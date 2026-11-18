; Examples: running Erlang programs with the executable scheduler
; (Section 4.3).  Each module's AST was produced by the front end:
;     escript erl_to_acl2.erl erl/NAME.erl      (writes erl/NAME.lisp)
; As the executable scheduler runs it prints the actions it takes.

(in-package "ACL2")

(include-book "scheduler")
(include-book "reduce")            ; the simplified reduce of Section 4.2
(include-book "erl/add_pairs")
(include-book "erl/joe_robert")
(include-book "erl/reduce_v2")
(include-book "erl/features")

; ---------------------------------------------------------------------------
; The front end: "2 + 2." becomes (:binop + (:integer 2) (:integer 2))
;   $ escript erl_to_acl2.erl -e "2 + 2."
;   (:binop + (:integer 2) (:integer 2))

(assert-event
 (equal (estate->val
         (eval-cont-list (list (cont-expr :expr '(:binop + (:integer 2) (:integer 2))))
                         (erl-initial-estate nil '|shell| (erl-pid 0))
                         100))
        (make-erl-val-integer :val 4)))

; The example of Figure 4: (X + Y) * (receive Z -> Z end) blocks in the
; receive, yielding its continuation to the scheduler...
(defconst *fig4-ast*
  ; escript erl_to_acl2.erl -e "(X + Y) * (receive Z -> Z end)."
  '(:binop * (:binop + (:var |X|) (:var |Y|))
           (:receive ((:clause (:cons (:var |Z|) (:nil)) () ((:var |Z|)))))))

(defconst *fig4-estate*
  (make-estate :none (list (cons '|X| (erl-val-integer 2)) (cons '|Y| (erl-val-integer 3)))
               '|shell| nil (erl-pid 0) nil nil))

(assert-event
 (let ((s (eval-cont-list (list (cont-expr :expr *fig4-ast*)) *fig4-estate* 100)))
   (and (equal (eval-status s) :blocked)
        ; ... and when the scheduler resumes it with a message Z = 7 in its
        ; inbox, the continuation (:binop2 * 5) computes 5 * 7.
        (let* ((v (estate->val s))
               (klist (cons (cont-receive2 :clauses (caddr v)) (cadr v)))
               (s2 (eval-cont-list klist
                                   (update-estate->inbox s (list (erl-val-integer 7)))
                                   100)))
          (equal (estate->val s2) (make-erl-val-integer :val 35))))))

; ---------------------------------------------------------------------------
; Figure 1: add_pairs([1,2,3,4,5,6,7,8]) -> [3,7,11,15]
; (add_pairs spawns the server during evaluation.)

(defconst *add-pairs-world* (erl-make-world (list *add_pairs-module*)))

(assert-event
 (equal (erl-run-function *add-pairs-world* '|add_pairs| '|add_pairs|
                          (list (erl-ints '(1 2 3 4 5 6 7 8)))
                          1000)
        (erl-ints '(3 7 11 15))))

(assert-event
 (equal (erl-format (erl-run-function *add-pairs-world* '|add_pairs| '|add_pairs|
                                      (list (erl-ints '(1 2 3 4 5 6 7 8)))
                                      1000))
        "[3,7,11,15]"))

; ---------------------------------------------------------------------------
; Section 4.3, Joe-Robert: two processes send messages to each other,
; acknowledge that they have received them, and then exit.
;
; As in the paper, both processes are created by the ACL2 spawn function
; before evaluation begins: process 0 runs robert(), process 1 runs
; joe(<0.0.0>).

(defconst *joe-robert-world* (erl-make-world (list *joe_robert-module*)))

(defconst *joe-robert-sys*
  (erl-spawn-call (erl-spawn-call nil 0 *joe-robert-world* '|joe_robert| '|robert| nil)
                  1 *joe-robert-world* '|joe_robert| '|joe| (list (erl-pid 0))))

; (Attachments, hence the executable scheduler, are not used when
; evaluating defconst, so the runs are inside assert-event.)
(assert-event
 (let ((final (erl-run-sched *joe-robert-sys* 0 100 1000)))
   (and
    ; Helper: only the exit values of the processes
    (equal (erl-exit-values final)
           '((0 :done :tuple ((:atom |robert|) (:atom |done|)))
             (1 :done :tuple ((:atom |joe|) (:atom |done|)))))
    ; The scheduler ran to completion: no non-stuttering action is left.
    (atom (sched-actions final)))))

; The same exchange started from Erlang: start() spawns both processes.
(assert-event
 (equal (cdr (erl-exit-values (erl-run-function-sys *joe-robert-world* '|joe_robert|
                                                    '|start| nil 1000)))
        '((1 :done :tuple ((:atom |robert|) (:atom |done|)))
          (2 :done :tuple ((:atom |joe|) (:atom |done|))))))

; ---------------------------------------------------------------------------
; Section 4.3, reduce-v2: Schwartz's reduce with the grand total sent back
; to every worker, combining with a closure fun(A, B) -> A + B end.
; run(N) spawns N workers in a tree; worker I contributes I; every worker
; ends with 0 + 1 + ... + (N-1).

(defconst *reduce-v2-world* (erl-make-world (list *reduce_v2-module*)))

(assert-event
 (equal (erl-format (erl-run-function *reduce-v2-world* '|reduce_v2| '|run|
                                      (list (erl-val-integer 7)) 2000))
        "[21,21,21,21,21,21,21]"))

(assert-event
 (equal (erl-format (erl-run-function *reduce-v2-world* '|reduce_v2| '|run|
                                      (list (erl-val-integer 4)) 2000))
        "[6,6,6,6]"))

; with a different combine function, passed as an ACL2 closure value
(assert-event
 (equal (erl-format (erl-run-function *reduce-v2-world* '|reduce_v2| '|start|
                                      (list (erl-val-integer 5)
                                            '(:funref |erlang| |max| 2))
                                      2000))
        "[4,4,4,4,4]"))

; The simplified reduce of Figure 5 (the one verified in reduce.lisp) on
; the 7-node worker tree: the root ends with 21 and no worker is blocked.
(assert-event
 (let ((sys (reduce-run 7 1000)))
   (and (equal (worker-status 0 sys) :done)
        (equal (estate->val (proc->estate (sys-lookup 0 sys)))
               (make-erl-val-integer :val (sum-of-indices 7)))
        (no-blocked-workers 7 sys))))

; ---------------------------------------------------------------------------
; Coverage of the supported subset (erl/features.erl).  The expected strings
; are the output of io:format("~w", ...) in Erlang/OTP 25.

(defconst *features-world* (erl-make-world (list *features-module*)))

(assert-event
 (equal (erl-format (erl-run-function *features-world* '|features| '|all| nil 100000))
        "{3628800,negative,zero,positive,{ok,3},{error,divide_by_zero},11,81,10,3,{point,2,3},9,10,unknown,{thrown,zero},{exited,one},{value,20},zero,50,[1,2,3],[3,2,1],9,true,false,b,x,y,[{1,2},{2,1}],1,-3,true,true,true,true}"))

; receive / send with a spawned echo process
(assert-event
 (equal (erl-format (erl-run-function *features-world* '|features| '|ping| nil 1000))
        "{hello,[1,2,3]}"))

; closures capturing a pid, spawned in a loop
(assert-event
 (equal (erl-format (erl-run-function *features-world* '|features| '|counter|
                                      (list (erl-val-integer 4)) 1000))
        "30"))

; a function_clause exception crashes the process
(assert-event
 (equal (erl-run-function *features-world* '|features| '|fact|
                          (list (erl-val-integer -1)) 1000)
        '(:crashed (:exception |error| (:tuple ((:atom |function_clause|)
                                                 (:atom |fact|)))))))

; running out of fuel
(assert-event
 (equal (car (erl-run-function *features-world* '|features| '|fact|
                               (list (erl-val-integer 100)) 50))
        :out-of-fuel))
