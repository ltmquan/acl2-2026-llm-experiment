;;; solution-no-hints.lisp: reviewer variant of 04-binmonjil-chandy-lamport/exp1/solution.lisp
;;; with fewer :hints (21 -> 15). Every event of the original is kept unchanged except
;;; for its hints, in the same order. See reviews/04-binmonjil-chandy-lamport-exp1-hints.md.
;;;
; Chandy-Lamport snapshot algorithm: reordering of a checkpoint segment
; into prerecording events followed by postrecording events.

(in-package "ACL2")

(include-book "misc/records" :dir :system)
(include-book "misc/equal-by-g" :dir :system)

;;; ------------------------------------------------------------------
;;; Messages
;;; ------------------------------------------------------------------

(defun marker (sid) (cons :marker sid))
(defun markerp (m) (and (consp m) (eq (car m) :marker)))
(defun marker-sid (m) (cdr m))

;;; ------------------------------------------------------------------
;;; Abstract application, topology and initial states
;;; ------------------------------------------------------------------

(encapsulate
  (((app-compute * *) => *)          ; internal step: (p local-state) -> local-state
   ((app-receive * * * *) => *)      ; receive effect: (p from msg local-state)
   ((app-send-p * * *) => *)         ; send to outgoing neighbor? (p to local-state)
   ((app-make-msg * * *) => *)       ; the message constructed (p to local-state)
   ((in-nbrs *) => *)                ; incoming neighbors of a process
   ((out-nbrs *) => *)               ; outgoing neighbors of a process
   ((init-local *) => *)             ; initial local state of a process
   ((sys-procs) => *))               ; process identifiers
  (local (defun app-compute (p ls) (declare (ignore p)) ls))
  (local (defun app-receive (p j m ls) (declare (ignore p j m)) ls))
  (local (defun app-send-p (p k ls) (declare (ignore p k ls)) nil))
  (local (defun app-make-msg (p k ls) (declare (ignore p k ls)) nil))
  (local (defun in-nbrs (p) (declare (ignore p)) nil))
  (local (defun out-nbrs (p) (declare (ignore p)) nil))
  (local (defun init-local (p) (declare (ignore p)) nil))
  (local (defun sys-procs () nil))
  ;; the only constraint: constructed application messages are not markers
  (defthm app-make-msg-not-marker
    (not (markerp (app-make-msg p k ls)))))

;;; ------------------------------------------------------------------
;;; Global state.
;;;  A state is a record with fields
;;;    :procs   list of process identifiers
;;;    :pstates record  pid -> process state
;;;    :chans   record  (from . to) -> list of messages (FIFO, head first)
;;;  A process state is a record with fields
;;;    :app     application-visible local state
;;;    :in :out incoming / outgoing neighbors (topology)
;;;    :sids    list of snapshot identifiers
;;;    :counter checkpoint counter
;;;    :snaps   record sid -> snapshot entry
;;;  A snapshot entry is a record with fields
;;;    :state   saved local state
;;;    :chans   record in-neighbor -> recorded channel state
;;;    :expect  incoming neighbors from which markers are still expected
;;;    :status  :checkpointing or :done
;;; ------------------------------------------------------------------

(defun ps-of (p s) (g p (g :pstates s)))
(defun sids-of (p s) (g :sids (ps-of p s)))
(defun outs-of (p s) (g :out (ps-of p s)))
(defun ins-of (p s) (g :in (ps-of p s)))
(defun chan-of (a b s) (g (cons a b) (g :chans s)))

;;; Inputs: (proc type sender), type one of :compute :receive :checkpoint

(defun in-proc (x) (car x))
(defun in-type (x) (cadr x))
(defun in-sender (x) (caddr x))
(defun recv-p (x) (eq (in-type x) :receive))

;;; ------------------------------------------------------------------
;;; Local transitions
;;; ------------------------------------------------------------------

(defun marker-outbox (outs sid)
  (if (endp outs)
      nil
    (cons (cons (car outs) (marker sid))
          (marker-outbox (cdr outs) sid))))

(defun app-outbox (p outs ls)
  (if (endp outs)
      nil
    (if (app-send-p p (car outs) ls)
        (cons (cons (car outs) (app-make-msg p (car outs) ls))
              (app-outbox p (cdr outs) ls))
      (app-outbox p (cdr outs) ls))))

(defun new-entry (ls expect chans)
  (s :state ls
     (s :chans chans
        (s :expect expect
           (s :status (if (consp expect) :checkpointing :done) nil)))))

;; Chandy-Lamport channel recording rule for an ordinary message msg
;; arriving from j: record it in every snapshot that is still
;; checkpointing and still expects a marker from j.
(defun record-msg (sids snaps j msg)
  (if (endp sids)
      snaps
    (let ((e (g (car sids) snaps)))
      (record-msg (cdr sids)
                  (if (and (eq (g :status e) :checkpointing)
                           (member-equal j (g :expect e)))
                      (s (car sids)
                         (s :chans
                            (s j (append (g j (g :chans e)) (list msg))
                               (g :chans e))
                            e)
                         snaps)
                    snaps)
                  j msg))))

;; new process state; head is the received message (for a receive)
(defun local-ps (x pso head)
  (let ((p (in-proc x))
        (j (in-sender x))
        (app (g :app pso))
        (sids (g :sids pso))
        (snaps (g :snaps pso)))
    (case (in-type x)
      (:compute (s :app (app-compute p app) pso))
      (:checkpoint
       (let ((sid (cons p (nfix (g :counter pso)))))
         (s :counter (+ 1 (nfix (g :counter pso)))
            (s :sids (cons sid sids)
               (s :snaps (s sid (new-entry app (g :in pso) nil) snaps)
                  pso)))))
      (:receive
       (if (markerp head)
           (let ((sid (marker-sid head)))
             (if (member-equal sid sids)
                 ;; later marker: close the channel from j
                 (let* ((e (g sid snaps))
                        (ex (remove-equal j (g :expect e))))
                   (s :snaps
                      (s sid (s :expect ex
                                (s :status (if (consp ex) (g :status e) :done)
                                   e))
                         snaps)
                      pso))
               ;; first marker: record local state
               (s :sids (cons sid sids)
                  (s :snaps
                     (s sid (new-entry app (remove-equal j (g :in pso))
                                       (s j nil nil))
                        snaps)
                     pso))))
         (s :app (app-receive p j head app)
            (s :snaps (record-msg sids snaps j head) pso))))
      (otherwise pso))))

;; messages sent: list of (to . msg)
(defun local-out (x pso head)
  (let ((p (in-proc x))
        (sids (g :sids pso))
        (outs (g :out pso)))
    (case (in-type x)
      (:compute (app-outbox p outs (app-compute p (g :app pso))))
      (:checkpoint (marker-outbox outs (cons p (nfix (g :counter pso)))))
      (:receive (if (and (markerp head)
                         (not (member-equal (marker-sid head) sids)))
                    (marker-outbox outs (marker-sid head))
                  nil))
      (otherwise nil))))

;;; ------------------------------------------------------------------
;;; Global transitions
;;; ------------------------------------------------------------------

(defun head-of (s x)
  (if (recv-p x) (car (chan-of (in-sender x) (in-proc x) s)) nil))

(defun pop-chans (s x)
  (let ((c (g :chans s)))
    (if (recv-p x)
        (let ((k (cons (in-sender x) (in-proc x))))
          (s k (cdr (g k c)) c))
      c)))

(defun deliver (p ob c)
  (if (endp ob)
      c
    (deliver p (cdr ob)
             (let ((k (cons p (car (car ob)))))
               (s k (append (g k c) (list (cdr (car ob)))) c)))))

(defun cl-step (s x)
  (let ((p (in-proc x)))
    (s :pstates (s p (local-ps x (ps-of p s) (head-of s x)) (g :pstates s))
       (s :chans (deliver p (local-out x (ps-of p s) (head-of s x))
                          (pop-chans s x))
          s))))

(defun cl-run (s e)
  (declare (xargs :measure (len e)))
  (if (endp e) s (cl-run (cl-step s (car e)) (cdr e))))

;;; Legality

(defun legal-input (s x)
  (and (member-equal (in-proc x) (g :procs s))
       (member-equal (in-type x) '(:compute :checkpoint :receive))
       (if (recv-p x)
           (and (member-equal (in-sender x) (g :procs s))
                (member-equal (in-sender x) (ins-of (in-proc x) s))
                (consp (chan-of (in-sender x) (in-proc x) s)))
         t)))

(defun legal-exec (s e)
  (declare (xargs :measure (len e)))
  (if (endp e)
      t
    (and (legal-input s (car e))
         (legal-exec (cl-step s (car e)) (cdr e)))))

;;; Initial state

(defun init-pstates (ps)
  (if (endp ps)
      nil
    (s (car ps)
       (s :app (init-local (car ps))
          (s :in (in-nbrs (car ps))
             (s :out (out-nbrs (car ps))
                (s :sids nil (s :counter 0 (s :snaps nil nil))))))
       (init-pstates (cdr ps)))))

(defun init-state ()
  (s :procs (sys-procs)
     (s :pstates (init-pstates (sys-procs))
        (s :chans nil nil))))

;;; ------------------------------------------------------------------
;;; Snapshots, cut, segment
;;; ------------------------------------------------------------------

(defun recorded-p (sid p s) (member-equal sid (sids-of p s)))

(defun snapshot-done-all (sid ps s)
  (if (endp ps)
      t
    (and (member-equal sid (sids-of (car ps) s))
         (eq (g :status (g sid (g :snaps (ps-of (car ps) s)))) :done)
         (snapshot-done-all sid (cdr ps) s))))

(defun checkpoint-complete (sid s)
  (snapshot-done-all sid (g :procs s) s))

(defun segment-target (st e)
  (let ((i (in-proc (car e))))
    (cons i (nfix (g :counter (ps-of i st))))))

(defun incomplete-before-each (sid s e)
  (declare (xargs :measure (len e)))
  (if (endp e)
      t
    (and (not (checkpoint-complete sid s))
         (incomplete-before-each sid (cl-step s (car e)) (cdr e)))))

(defun complete-segment-p (st e)
  (and (consp e)
       (eq (in-type (car e)) :checkpoint)
       (legal-exec st e)
       (incomplete-before-each (segment-target st e) st e)
       (checkpoint-complete (segment-target st e) (cl-run st e))))

;; prerecording inputs: process has not yet taken its cut (before the
;; input's own effect); postrecording: it has.
(defun pre-inputs (sid s e)
  (declare (xargs :measure (len e)))
  (if (endp e)
      nil
    (if (recorded-p sid (in-proc (car e)) s)
        (pre-inputs sid (cl-step s (car e)) (cdr e))
      (cons (car e) (pre-inputs sid (cl-step s (car e)) (cdr e))))))

(defun post-inputs (sid s e)
  (declare (xargs :measure (len e)))
  (if (endp e)
      nil
    (if (recorded-p sid (in-proc (car e)) s)
        (cons (car e) (post-inputs sid (cl-step s (car e)) (cdr e)))
      (post-inputs sid (cl-step s (car e)) (cdr e)))))

;;; State equivalence

(defun pstates-equiv (ps s1 s2)
  (if (endp ps)
      t
    (let ((p (car ps)))
      (and (equal (g :app (ps-of p s1)) (g :app (ps-of p s2)))
           (equal (ins-of p s1) (ins-of p s2))
           (equal (outs-of p s1) (outs-of p s2))
           (equal (g :counter (ps-of p s1)) (g :counter (ps-of p s2)))
           (equal (sids-of p s1) (sids-of p s2))
           (pstates-equiv (cdr ps) s1 s2)))))

(defun state-equiv (s1 s2)
  (and (equal (g :procs s1) (g :procs s2))
       (equal (g :chans s1) (g :chans s2))
       (pstates-equiv (g :procs s1) s1 s2)))

;;; ==================================================================
;;; Proof
;;; ==================================================================

(defun msgs-for (b ob)
  (if (endp ob)
      nil
    (if (equal (car (car ob)) b)
        (cons (cdr (car ob)) (msgs-for b (cdr ob)))
      (msgs-for b (cdr ob)))))

(defthm append-assoc
  (equal (append (append a b) c) (append a (append b c))))

(defthm g-deliver
  (equal (g k (deliver p ob c))
         (if (and (consp k) (equal (car k) p)
                  (consp (msgs-for (cdr k) ob)))
             (append (g k c) (msgs-for (cdr k) ob))
           (g k c)))
  :hints (("Goal" :induct (deliver p ob c))))

(defthm g-pop-chans
  (equal (g k (pop-chans s x))
         (if (and (recv-p x) (equal k (cons (in-sender x) (in-proc x))))
             (cdr (g k (g :chans s)))
           (g k (g :chans s)))))

(defthm g-procs-step
  (equal (g :procs (cl-step s x)) (g :procs s)))

(defthm ps-of-step
  (equal (ps-of p (cl-step s x))
         (if (equal p (in-proc x))
             (local-ps x (ps-of p s) (head-of s x))
           (ps-of p s))))

(defthm chan-of-step
  (equal (chan-of a b (cl-step s x))
         (let ((base (if (and (recv-p x) (equal a (in-sender x))
                              (equal b (in-proc x)))
                         (cdr (chan-of a b s))
                       (chan-of a b s)))
               (msgs (msgs-for b (local-out x (ps-of a s) (head-of s x)))))
           (if (and (equal a (in-proc x)) (consp msgs))
               (append base msgs)
             base))))

(defthm g-other-step
  (implies (and (not (equal k :pstates)) (not (equal k :chans)))
           (equal (g k (cl-step s x)) (g k s))))

(defthm g-chans-step
  (equal (g :chans (cl-step s x))
         (deliver (in-proc x)
                  (local-out x (ps-of (in-proc x) s) (head-of s x))
                  (pop-chans s x))))

(defthm g-pstates-step
  (equal (g :pstates (cl-step s x))
         (s (in-proc x) (local-ps x (ps-of (in-proc x) s) (head-of s x))
            (g :pstates s))))

(in-theory (disable cl-step ps-of chan-of pop-chans))

;;; local facts

(defthm msgs-for-marker-outbox-nil
  (implies (not (member-equal b outs))
           (equal (msgs-for b (marker-outbox outs sid)) nil)))

(defthm msgs-for-app-outbox-nil
  (implies (not (member-equal b outs))
           (equal (msgs-for b (app-outbox p outs ls)) nil)))

(defthm member-marker-msgs-for-marker-outbox
  (implies (member-equal b outs)
           (member-equal (marker sid) (msgs-for b (marker-outbox outs sid)))))

(defthm consp-msgs-for-marker-outbox
  (implies (member-equal b outs)
           (consp (msgs-for b (marker-outbox outs sid)))))

(defthm local-out-keys
  (implies (not (member-equal b (g :out pso)))
           (equal (msgs-for b (local-out x pso head)) nil)))

(defthm local-ps-out
  (equal (g :out (local-ps x pso head)) (g :out pso)))

(defthm local-ps-in
  (equal (g :in (local-ps x pso head)) (g :in pso)))

(defthm local-ps-sids-mono
  (implies (member-equal sid (g :sids pso))
           (member-equal sid (g :sids (local-ps x pso head)))))

(defthm local-ps-new-sid
  (implies (and (not (member-equal sid (g :sids pso)))
                (member-equal sid (g :sids (local-ps x pso head))))
           (equal (local-out x pso head)
                  (marker-outbox (g :out pso) sid))))

(defthm local-ps-marker-records
  (implies (and (equal (in-type x) :receive)
                (equal head (marker sid)))
           (member-equal sid (g :sids (local-ps x pso head)))))

(in-theory (disable local-ps local-out marker))

;;; state-level facts

(defthm sids-mono-step
  (implies (member-equal sid (sids-of q s))
           (member-equal sid (sids-of q (cl-step s x)))))

(defthm sids-step-other
  (implies (not (equal q (in-proc x)))
           (equal (sids-of q (cl-step s x)) (sids-of q s))))

(defthm outs-step
  (equal (outs-of q (cl-step s x)) (outs-of q s)))

(defthm ins-step
  (equal (ins-of q (cl-step s x)) (ins-of q s)))

(defthm member-append
  (iff (member-equal a (append x y))
       (or (member-equal a x) (member-equal a y))))

(defthm newly-recorded-sends-marker
  (implies (and (not (member-equal sid (sids-of q s)))
                (member-equal sid (sids-of q (cl-step s x)))
                (member-equal k (outs-of q s)))
           (member-equal (marker sid) (chan-of q k (cl-step s x)))))

(defthm marker-retained
  (implies (and (member-equal (marker sid) (chan-of q p s))
                (not (member-equal sid (sids-of p (cl-step s x)))))
           (member-equal (marker sid) (chan-of q p (cl-step s x)))))

(in-theory (disable sids-of outs-of ins-of))

(defthm g-procs-run
  (equal (g :procs (cl-run s e)) (g :procs s)))

(defthm cl-run-append
  (equal (cl-run s (append a b)) (cl-run (cl-run s a) b)))

;;; ------------------------------------------------------------------
;;; The marker invariant: if q has recorded sid and its outgoing
;;; neighbor p has not, then a marker for sid is in channel q->p.
;;; ------------------------------------------------------------------

(defun-sk cl-inv (s)
  (forall (sid q p)
    (implies (and (member-equal sid (sids-of q s))
                  (not (member-equal sid (sids-of p s)))
                  (member-equal p (outs-of q s)))
             (member-equal (marker sid) (chan-of q p s)))))

(defthm cl-inv-step-point
  (implies (and (cl-inv s)
                (member-equal sid (sids-of q (cl-step s x)))
                (not (member-equal sid (sids-of p (cl-step s x))))
                (member-equal p (outs-of q s)))
           (member-equal (marker sid) (chan-of q p (cl-step s x))))
  :hints (("Goal"
           :use ((:instance cl-inv-necc)
                 (:instance newly-recorded-sends-marker (k p))
                 (:instance marker-retained)))))

(defthm cl-inv-step
  (implies (cl-inv s) (cl-inv (cl-step s x)))
  :hints (("Goal" :expand ((cl-inv (cl-step s x)))
           :use ((:instance cl-inv-step-point
                            (sid (mv-nth 0 (cl-inv-witness (cl-step s x))))
                            (q (mv-nth 1 (cl-inv-witness (cl-step s x))))
                            (p (mv-nth 2 (cl-inv-witness (cl-step s x)))))))))

(in-theory (disable cl-inv))

(defthm cl-inv-run
  (implies (cl-inv s) (cl-inv (cl-run s e))))

(defthm sids-init-pstates
  (equal (g :sids (g q (init-pstates ps))) nil)
  :hints (("Goal" :in-theory (enable g-of-s-redux))))

(defthm cl-inv-init
  (cl-inv (init-state))
  :hints (("Goal" :in-theory (enable cl-inv sids-of ps-of))))

;;; ------------------------------------------------------------------
;;; Commutation of steps of distinct processes
;;; ------------------------------------------------------------------

(defun ne-cond (s x)
  (if (recv-p x) (consp (chan-of (in-sender x) (in-proc x) s)) t))

(defthm car-append-consp
  (implies (consp a) (equal (car (append a b)) (car a))))

(defthm cdr-append-consp
  (implies (consp a) (equal (cdr (append a b)) (append (cdr a) b))))

(defthm head-of-step-other
  (implies (and (not (equal (in-proc x) (in-proc y)))
                (ne-cond s x))
           (equal (head-of (cl-step s y) x) (head-of s x))))

(defthm chans-commute
  (implies (and (not (equal (in-proc x) (in-proc y)))
                (ne-cond s x) (ne-cond s y))
           (equal (g :chans (cl-step (cl-step s y) x))
                  (g :chans (cl-step (cl-step s x) y))))
  :hints (("Goal"
           :use ((:functional-instance
                  equal-by-g
                  (equal-by-g-hyp
                   (lambda () (and (not (equal (in-proc x) (in-proc y)))
                                   (ne-cond s x) (ne-cond s y))))
                  (equal-by-g-lhs
                   (lambda () (g :chans (cl-step (cl-step s y) x))))
                  (equal-by-g-rhs
                   (lambda () (g :chans (cl-step (cl-step s x) y)))))))
          (and stable-under-simplificationp
               '(:in-theory (enable chan-of)))))

(defthm g-step-commute
  (implies (and (not (equal (in-proc x) (in-proc y)))
                (ne-cond s x) (ne-cond s y))
           (equal (g k (cl-step (cl-step s y) x))
                  (g k (cl-step (cl-step s x) y))))
  :hints (("Goal"
           :cases ((equal k :pstates) (equal k :chans)))))

(defthm step-commute
  (implies (and (not (equal (in-proc x) (in-proc y)))
                (ne-cond s x) (ne-cond s y))
           (equal (cl-step (cl-step s y) x)
                  (cl-step (cl-step s x) y)))
  :hints (("Goal"
           :use ((:functional-instance
                  equal-by-g
                  (equal-by-g-hyp
                   (lambda () (and (not (equal (in-proc x) (in-proc y)))
                                   (ne-cond s x) (ne-cond s y))))
                  (equal-by-g-lhs
                   (lambda () (cl-step (cl-step s y) x)))
                  (equal-by-g-rhs
                   (lambda () (cl-step (cl-step s x) y)))))))
  :rule-classes nil)

;;; ------------------------------------------------------------------
;;; Moving a prerecording event leftward past postrecording events
;;; ------------------------------------------------------------------

(defun all-recorded (sid u qs)
  (if (endp qs)
      t
    (and (recorded-p sid (in-proc (car qs)) u)
         (all-recorded sid u (cdr qs)))))

(defun feasible (u qs)
  (declare (xargs :measure (len qs)))
  (if (endp qs)
      t
    (and (ne-cond u (car qs))
         (feasible (cl-step u (car qs)) (cdr qs)))))

(defun no-events-of (p qs)
  (if (endp qs)
      t
    (and (not (equal (in-proc (car qs)) p))
         (no-events-of p (cdr qs)))))

(defthm all-recorded-step
  (implies (all-recorded sid u qs)
           (all-recorded sid (cl-step u x) qs)))

(defthm all-recorded-no-events
  (implies (and (all-recorded sid u qs)
                (not (member-equal sid (sids-of p u))))
           (no-events-of p qs)))

(defthm sids-run-no-events
  (implies (no-events-of p qs)
           (equal (sids-of p (cl-run u qs)) (sids-of p u))))

(defthm outs-run
  (equal (outs-of p (cl-run u qs)) (outs-of p u)))

(defthm sids-mono-run
  (implies (member-equal sid (sids-of p u))
           (member-equal sid (sids-of p (cl-run u qs)))))

(defthm recorded-before-run
  (implies (and (all-recorded sid u qs)
                (member-equal sid (sids-of p (cl-run u qs))))
           (member-equal sid (sids-of p u))))

(defthm chan-run-unchanged
  (implies (and (no-events-of p qs)
                (or (no-events-of j qs)
                    (not (member-equal p (outs-of j u)))))
           (equal (chan-of j p (cl-run u qs)) (chan-of j p u)))
  :hints (("Goal"
           :in-theory (enable outs-of))))

(defthm ne-cond-step-other
  (implies (and (ne-cond u y)
                (not (equal (in-proc x) (in-proc y))))
           (ne-cond (cl-step u x) y)))

(defthm ne-cond-before
  (implies (and (cl-inv u)
                (all-recorded sid u qs)
                (not (member-equal sid (sids-of (in-proc x) (cl-run u qs))))
                (ne-cond (cl-run u qs) x))
           (ne-cond u x))
  :hints (("Goal"
           :use ((:instance cl-inv-necc (s u) (q (in-sender x)) (p (in-proc x)))
                 (:instance all-recorded-no-events (p (in-proc x)))))))

(defthm all-recorded-proc-differs
  (implies (and (all-recorded sid u qs)
                (consp qs)
                (not (member-equal sid (sids-of p u))))
           (not (equal (in-proc (car qs)) p))))

(defthm commute-past-post
  (implies (and (cl-inv u)
                (all-recorded sid u qs)
                (feasible u qs)
                (not (member-equal sid (sids-of (in-proc x) (cl-run u qs))))
                (ne-cond (cl-run u qs) x))
           (and (equal (cl-step (cl-run u qs) x)
                       (cl-run (cl-step u x) qs))
                (feasible (cl-step u x) qs)))
  :hints (("Goal" :induct (cl-run u qs))
          ("Subgoal *1/2"
           :use ((:instance step-commute (s u) (y (car qs)))
                 (:instance ne-cond-before)))))

;;; ------------------------------------------------------------------
;;; Generalized reordering: u is the state after the prerecording
;;; events seen so far, qs the postrecording events seen so far, and
;;; (cl-run u qs) the state of the original execution.
;;; ------------------------------------------------------------------

(defthm all-recorded-append
  (iff (all-recorded sid u (append qs (list x)))
         (and (all-recorded sid u qs)
              (recorded-p sid (in-proc x) u))))

(defthm feasible-append
  (equal (feasible u (append qs (list x)))
         (and (feasible u qs)
              (ne-cond (cl-run u qs) x))))

(defthm legal-input-ne-cond
  (implies (legal-input s x) (ne-cond s x)))

(defun reorder-ind (sid u qs e)
  (declare (xargs :measure (len e)))
  (if (endp e)
      (list u qs)
    (if (recorded-p sid (in-proc (car e)) (cl-run u qs))
        (reorder-ind sid u (append qs (list (car e))) (cdr e))
      (reorder-ind sid (cl-step u (car e)) qs (cdr e)))))

(defthm reorder-general
  (implies (and (cl-inv u)
                (all-recorded sid u qs)
                (feasible u qs)
                (legal-exec (cl-run u qs) e))
           (equal (cl-run (cl-run u (pre-inputs sid (cl-run u qs) e))
                          (append qs (post-inputs sid (cl-run u qs) e)))
                  (cl-run (cl-run u qs) e)))
  :hints (("Goal" :induct (reorder-ind sid u qs e))))

(defthm pstates-equiv-refl
  (pstates-equiv ps s s))

(defthm state-equiv-refl
  (state-equiv s s))

(in-theory (disable state-equiv))

;;; ------------------------------------------------------------------
;;; Main theorem
;;; ------------------------------------------------------------------

(defthm reorder-from-state
  (implies (and (cl-inv st)
                (legal-exec st e))
           (equal (cl-run st (append (pre-inputs sid st e)
                                     (post-inputs sid st e)))
                  (cl-run st e)))
  :hints (("Goal"
           :use ((:instance reorder-general (u st) (qs nil))))))

(defthm cl-inv-reachable
  (cl-inv (cl-run (init-state) prefix))
  :hints (("Goal" :in-theory (disable init-state (:e init-state)))))

(defthm main
  (implies (and (legal-exec (init-state) prefix)
                (equal st (cl-run (init-state) prefix))
                (complete-segment-p st e))
           (state-equiv
            (cl-run st (append (pre-inputs (segment-target st e) st e)
                               (post-inputs (segment-target st e) st e)))
            (cl-run st e)))
  :hints (("Goal"
           :use ((:instance reorder-from-state (sid (segment-target st e)))
                 (:instance cl-inv-reachable)))))
