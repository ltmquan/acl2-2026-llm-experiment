; Erlang in ACL2: the scheduler.
;
; The global state SYS of an Erlang program is a mapping from process
; identifiers (natural numbers; the Erlang pid of process n is (:pid n)) to
; processes.  A process is (status klist estate):
;   :ready        runnable: run eval-cont-list on klist
;   :blocked      klist = ((:receive2 clauses) . rest), waiting for a message
;   :done         exited normally; (estate->val estate) is the exit value
;   :crashed      exited with an uncaught exception
;   :out-of-fuel  ran out of fuel
; The inbox of a process lives in its estate but is only extended by the
; scheduler; the outbox (per-destination queues of sent messages) is
; emptied by the scheduler when it delivers messages.
;
; Scheduler actions:
;   (:run p)           run process p (ready, or blocked with a matching message)
;   (:deliver p dest)  move the oldest message from p's queue for DEST to the
;                      inbox of DEST (dropped if DEST does not exist)
;   (:stutter)         do nothing
;
; The scheduler itself is a constrained function ERL-SCHEDULER whose only
; constraint is the (weak) fairness condition: if a non-stuttering action is
; available, it chooses one.  An executable scheduler is attached with
; defattach.

(in-package "ACL2")

(include-book "evaluator")

(set-verify-guards-eagerness 0)

(defun make-proc (status klist estate) (list status klist estate))
(defun proc->status (p) (nth 0 p))
(defun proc->klist (p) (nth 1 p))
(defun proc->estate (p) (nth 2 p))

(defun sys-lookup (pid sys) (cdr (assoc-equal pid sys)))
(defun sys-update (pid proc sys) (put-assoc-equal pid proc sys))

(defun receive2-clauses (klist) (cadr (car klist)))

(defun proc-has-match-p (p)
  ; a blocked process with a message in its inbox matching its receive
  (let ((s (proc->estate p)))
    (mv-let (found body env inbox)
      (receive-match (estate->inbox s) (receive2-clauses (proc->klist p))
                     (estate->env s) (estate->self s))
      (declare (ignore body env inbox))
      found)))

(defun proc-runnable-p (p)
  (case (proc->status p)
    (:ready t)
    (:blocked (proc-has-match-p p))
    (otherwise nil)))

(defun outbox-actions (src outbox)
  (cond ((atom outbox) nil)
        ((and (consp (car outbox)) (consp (cdar outbox)))
         (cons (list :deliver src (caar outbox)) (outbox-actions src (cdr outbox))))
        (t (outbox-actions src (cdr outbox)))))

(defun sched-actions (sys)
  ; All non-stuttering actions available in SYS, in process order.
  (if (atom sys)
      nil
    (let* ((pid (caar sys)) (p (cdar sys)))
      (append (if (proc-runnable-p p) (list (list :run pid)) nil)
              (outbox-actions pid (estate->outbox (proc->estate p)))
              (sched-actions (cdr sys))))))

(defun sys-next-pid (sys)
  (if (atom sys) 0 (max (1+ (nfix (caar sys))) (sys-next-pid (cdr sys)))))

(defun spawned-proc (fun pid s)
  ; the child process created by spawn(FUN): it applies FUN to no arguments
  (make-proc :ready (list (list :call-fun2 fun))
             (make-estate nil nil (estate->module s) (estate->world s) (erl-pid pid) nil nil)))

(defun result-proc (s)
  ; Classify the estate returned by eval-cont-list as a process.
  (let ((v (estate->val s)))
    (cond ((and (consp v) (eq (car v) :receive))
           (make-proc :blocked (cons (list :receive2 (caddr v)) (cadr v))
                      (update-estate->val s :none)))
          ((erl-out-of-fuel-p v) (make-proc :out-of-fuel (cadr v) s))
          ((erl-exception-p v) (make-proc :crashed nil s))
          (t (make-proc :done nil s)))))

(defun sched-run (pid sys fuel)
  (let* ((p (sys-lookup pid sys))
         (s (eval-cont-list (proc->klist p) (proc->estate p) fuel))
         (v (estate->val s)))
    (if (and (consp v) (eq (car v) :spawn))
        ; (:spawn fun rest): allocate a fresh pid, resume the parent with it
        (let* ((child (sys-next-pid sys))
               (parent (make-proc :ready (caddr v) (update-estate->val s (erl-pid child)))))
          (append (sys-update pid parent sys)
                  (list (cons child (spawned-proc (cadr v) child s)))))
      (sys-update pid (result-proc s) sys))))

(defun sched-deliver (src dest sys)
  (let* ((p (sys-lookup src sys))
         (s (proc->estate p))
         (outbox (estate->outbox s))
         (queue (cdr (assoc-equal dest outbox)))
         (msg (car queue))
         (p2 (make-proc (proc->status p) (proc->klist p)
                        (update-estate->outbox s (put-assoc-equal dest (cdr queue) outbox))))
         (sys2 (sys-update src p2 sys))
         (dpid (cadr dest))
         (d (sys-lookup dpid sys2)))
    (if (and (erl-pid-p dest) (assoc-equal dpid sys2))
        (let ((ds (proc->estate d)))
          (sys-update dpid
                      (make-proc (proc->status d) (proc->klist d)
                                 (update-estate->inbox ds (append (estate->inbox ds) (list msg))))
                      sys2))
      sys2)))

(defun sched-apply (act sys fuel)
  (case (car act)
    (:run (sched-run (cadr act) sys fuel))
    (:deliver (sched-deliver (cadr act) (caddr act) sys))
    (otherwise sys)))

; ---------------------------------------------------------------------------
; The abstract scheduler.  N is the index of the step in the trace, so
; different choices may be made at different times in the same state.

(encapsulate
  (((erl-scheduler * *) => *))
  (local (defun erl-scheduler (n sys)
           (declare (ignore n))
           (let ((acts (sched-actions sys)))
             (if (consp acts) (car acts) '(:stutter)))))
  ; Fairness: if there is a non-stuttering action, a non-stuttering action
  ; is chosen.
  (defthm erl-scheduler-fair
    (implies (consp (sched-actions sys))
             (member-equal (erl-scheduler n sys) (sched-actions sys)))))

(defun sched-step (n sys fuel)
  ; One step of the trace.  An action that is not available stutters.
  (let ((act (erl-scheduler n sys)))
    (if (member-equal act (sched-actions sys))
        (sched-apply act sys fuel)
      sys)))

(defun erl-run-sched (sys n steps fuel)
  ; Run the scheduler for at most STEPS steps, stopping early when no
  ; non-stuttering action remains.  Each process run gets FUEL.
  (declare (xargs :measure (nfix steps)))
  (cond ((zp steps) sys)
        ((atom (sched-actions sys)) sys)
        (t (erl-run-sched (sched-step n sys fuel) (1+ n) (1- steps) fuel))))

; ---------------------------------------------------------------------------
; The executable scheduler: goes through the processes in order until it
; finds a runnable process or a pending message in an outbox, and prints
; the action taken (when the state global erl-verbose is not nil).

(defun erl-scheduler-exec (n sys)
  (declare (xargs :guard t :verify-guards t))
  (let ((acts (ec-call (sched-actions sys))))
    (if (consp acts)
        (prog2$ (cw "step ~x0: ~x1~%" n (car acts)) (car acts))
      '(:stutter))))

(defattach erl-scheduler erl-scheduler-exec)

; ---------------------------------------------------------------------------
; Creating processes before evaluation (the ACL2 "spawn"), running, and
; inspecting results.

(defun erl-spawn (sys pid klist estate)
  ; Add a ready process PID to SYS.
  (append sys (list (cons pid (make-proc :ready klist estate)))))

(defun erl-spawn-call (sys pid world mod fn args)
  ; Add process PID that will evaluate MOD:FN(ARGS...).
  (erl-spawn sys pid (list (list :call-remote mod fn))
             (make-estate args nil mod world (erl-pid pid) nil nil)))

(defun erl-exit-values (sys)
  ; alist from pid to (status . value) for all processes
  (if (atom sys) nil
    (cons (cons (caar sys)
                (cons (proc->status (cdar sys)) (estate->val (proc->estate (cdar sys)))))
          (erl-exit-values (cdr sys)))))

(defun erl-run-function-sys (world mod fn args fuel)
  ; Run MOD:FN(ARGS) as process 0 under the scheduler: at most FUEL
  ; scheduler steps, each process run with FUEL units of fuel.
  (erl-run-sched (erl-spawn-call nil 0 world mod fn args) 0 fuel fuel))

(defun erl-run-function (world mod fn args fuel)
  ; The exit value of MOD:FN(ARGS) if it terminates normally, otherwise
  ; (status value).
  (let* ((sys (erl-run-function-sys world mod fn args fuel))
         (p (sys-lookup 0 sys)))
    (if (eq (proc->status p) :done)
        (estate->val (proc->estate p))
      (list (proc->status p) (estate->val (proc->estate p))))))
