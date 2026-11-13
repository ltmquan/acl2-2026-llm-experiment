(in-package "ACL2")

(include-book "defs")

;;; ---------------- part 1 ----------------
(defmacro send-all (msg i nbrs ch) `(send-msg-all-outgoing-channels ,msg ,i ,nbrs ,ch))
(in-theory (disable send-msg-all-outgoing-channels))

(defthm send-all-nil
  (implies (endp nbrs) (equal (send-all msg i nbrs ch) ch))
  :hints (("Goal" :in-theory (enable send-msg-all-outgoing-channels))))

(defthm send-all-cons
  (equal (send-all msg i (cons n nbrs) ch)
         (let ((y (send-all msg i nbrs ch)))
           (s n (s i (snoc (g i (g n y)) msg) (g n y)) y)))
  :hints (("Goal" :in-theory (enable send-msg-all-outgoing-channels))))

(defun sa-ind (nbrs) (if (endp nbrs) nil (sa-ind (cdr nbrs))))

(defthm sa-cell-other
  (implies (not (and (equal a i) (memberp b nbrs)))
           (equal (g a (g b (send-all msg i nbrs ch)))
                  (g a (g b ch))))
  :hints (("Goal" :induct (sa-ind nbrs) :in-theory (enable g-of-s-redux))))

(defthm consp-snoc (consp (snoc x e)))
(defthm car-snoc (implies (consp x) (equal (car (snoc x e)) (car x))))
(defthm cdr-snoc (implies (consp x) (equal (cdr (snoc x e)) (snoc (cdr x) e))))

(defthm sa-cell-consp
  (implies (consp (g a (g b ch)))
           (and (consp (g a (g b (send-all msg i nbrs ch))))
                (equal (car (g a (g b (send-all msg i nbrs ch))))
                       (car (g a (g b ch))))))
  :hints (("Goal" :induct (sa-ind nbrs) :in-theory (enable g-of-s-redux))))

(defthm sc-cell-other
  (implies (not (and (equal a i) (memberp b nbrs)))
           (equal (g a (g b (send-compute-message ls i nbrs ch)))
                  (g a (g b ch))))
  :hints (("Goal" :in-theory (enable g-of-s-redux))))

(defthm sc-cell-consp
  (implies (consp (g a (g b ch)))
           (and (consp (g a (g b (send-compute-message ls i nbrs ch))))
                (equal (car (g a (g b (send-compute-message ls i nbrs ch))))
                       (car (g a (g b ch))))))
  :hints (("Goal" :in-theory (enable g-of-s-redux))))

;; commuting with a single cell update
(defthm sa-cell-commute
  (implies (or (not (equal a i)) (not (memberp b nbrs)))
           (equal (send-all msg i nbrs (s b (s a v (g b ch)) ch))
                  (s b (s a v (g b (send-all msg i nbrs ch)))
                     (send-all msg i nbrs ch))))
  :hints (("Goal" :induct (sa-ind nbrs) :in-theory (enable g-of-s-redux))))

(defthm sc-cell-commute
  (implies (or (not (equal a i)) (not (memberp b nbrs)))
           (equal (send-compute-message ls i nbrs (s b (s a v (g b ch)) ch))
                  (s b (s a v (g b (send-compute-message ls i nbrs ch)))
                     (send-compute-message ls i nbrs ch))))
  :hints (("Goal" :induct (send-compute-message ls i nbrs ch)
           :in-theory (enable g-of-s-redux))))

;;; ---------------- part 2 ----------------
(defthm rm-of-cell
  (equal (remove-message-from-channel j k (s b (s a v (g b ch)) ch))
         (if (and (equal a j) (equal b k))
             (s k (s j (if v (cdr v) nil) (g k ch)) ch)
           (s b (s a v (g b (remove-message-from-channel j k ch)))
              (remove-message-from-channel j k ch))))
  :hints (("Goal" :in-theory (enable g-of-s-redux))))

(defthm rm-cell-same
  (equal (g j (g k (remove-message-from-channel j k ch)))
         (if (g j (g k ch)) (cdr (g j (g k ch))) nil)))

(defthm rm-cell-other
  (implies (not (and (equal a j) (equal b k)))
           (equal (g a (g b (remove-message-from-channel j k ch)))
                  (g a (g b ch))))
  :hints (("Goal" :in-theory (enable g-of-s-redux))))

(defthm sa-rm-commute-1
  (implies (or (not (equal i j)) (not (memberp k nbrs)))
           (equal (send-all m i nbrs (remove-message-from-channel j k ch))
                  (remove-message-from-channel j k (send-all m i nbrs ch)))))

(defthm sc-rm-commute-1
  (implies (or (not (equal i j)) (not (memberp k nbrs)))
           (equal (send-compute-message ls i nbrs (remove-message-from-channel j k ch))
                  (remove-message-from-channel j k (send-compute-message ls i nbrs ch)))))

(defthm cell-set-over-rm
  (equal (s k (s j v (g k (remove-message-from-channel j k ch)))
            (remove-message-from-channel j k ch))
         (s k (s j v (g k ch)) ch)))

(in-theory (disable remove-message-from-channel))

(defthm sa-rm-commute-2
  (implies (consp (g j (g k ch)))
           (equal (send-all m i nbrs (remove-message-from-channel j k ch))
                  (remove-message-from-channel j k (send-all m i nbrs ch))))
  :hints (("Goal" :induct (sa-ind nbrs)
           :expand ((send-all m i nbrs (remove-message-from-channel j k ch))
                    (send-all m i nbrs ch)))))

(defthm sc-rm-commute-2
  (implies (consp (g j (g k ch)))
           (equal (send-compute-message ls i nbrs (remove-message-from-channel j k ch))
                  (remove-message-from-channel j k (send-compute-message ls i nbrs ch))))
  :hints (("Goal" :induct (send-compute-message ls i nbrs ch)
           :in-theory (enable g-of-s-redux))))

(defthm sa-sa-commute
  (implies (not (equal i k))
           (equal (send-all m i n1 (send-all m2 k n2 ch))
                  (send-all m2 k n2 (send-all m i n1 ch))))
  :hints (("Goal" :induct (sa-ind n2)
     :expand ((:free (x) (send-all m2 k n2 x))))))

(defthm sc-sa-commute
  (implies (not (equal i k))
           (equal (send-compute-message ls i n1 (send-all m2 k n2 ch))
                  (send-all m2 k n2 (send-compute-message ls i n1 ch))))
  :hints (("Goal" :induct (sa-ind n2)
     :expand ((:free (x) (send-all m2 k n2 x))))))

(defthm sc-sc-commute
  (implies (not (equal i k))
           (equal (send-compute-message ls i n1 (send-compute-message ls2 k n2 ch))
                  (send-compute-message ls2 k n2 (send-compute-message ls i n1 ch))))
  :hints (("Goal" :induct (send-compute-message ls2 k n2 ch))))

(defthm rm-rm-commute
  (implies (not (equal i k))
           (equal (remove-message-from-channel j i (remove-message-from-channel j2 k ch))
                  (remove-message-from-channel j2 k (remove-message-from-channel j i ch))))
  :hints (("Goal" :in-theory (enable g-of-s-redux remove-message-from-channel))))

;;; ---------------- part 3 ----------------
(defun acting-msg-p (msg)
  (and msg
       (or (equal (msg-type msg) :normal)
           (equal (msg-type msg) :marker)
           (equal (msg-type msg) :recovery))))

(defun in-msg (in ch)
  (if (equal (ttype in) :receive)
      (get-msg-from-channel (sender in) (pid in) ch)
    nil))

(defun rm-part (in msg ch)
  (if (and (equal (ttype in) :receive) (acting-msg-p msg))
      (remove-message-from-channel (sender in) (pid in) ch)
    ch))

(defun send-part (in p msg ch)
  (let ((i (pid in)))
    (cond ((equal (ttype in) :normal)
           (send-compute-message (local-state p) i (nbrs-to p) ch))
          ((equal (ttype in) :start-checkpoint)
           (send-all (create-marker-message (local-state p) (list i (counter p)))
                     i (nbrs-to p) ch))
          ((and (equal (ttype in) :receive) msg
                (equal (msg-type msg) :marker)
                (not (memberp (sid msg) (snapshot-ids p))))
           (send-all msg i (nbrs-to p) ch))
          ((and (equal (ttype in) :receive) msg
                (equal (msg-type msg) :recovery)
                (equal (proc-status p) :normal))
           (send-all msg i (nbrs-to p) ch))
          (t ch))))

(defun pnew (in p msg)
  (let ((i (pid in)) (j (sender in)))
    (cond ((equal (ttype in) :normal)
           (s :local-state (update-local-state-normal (local-state p)) p))
          ((equal (ttype in) :start-checkpoint)
           (s :counter (+ 1 (counter p))
              (install-snapshot-entry (list i (counter p))
                                      (make-snapshot-entry (local-state p) (nbrs-from p) nil)
                                      p)))
          ((and (equal (ttype in) :receive) msg)
           (cond ((equal (msg-type msg) :normal)
                  (if (and (equal (proc-status p) :recovering)
                           (memberp j (waiting-recovery-from p)))
                      p
                    (update-proc-for-normal-msg-core p j msg)))
                 ((equal (msg-type msg) :marker)
                  (if (memberp (sid msg) (snapshot-ids p))
                      (update-proc-for-non-first-marker-msg p (sid msg) j)
                    (update-proc-for-first-marker-msg p (sid msg) j)))
                 ((equal (msg-type msg) :recovery)
                  (if (equal (proc-status p) :normal)
                      (update-proc-for-first-recovery-msg p (sid msg) j)
                    (update-proc-for-non-first-recovery-msg p j)))
                 (t p)))
          (t p))))

(defun step-canon (u in)
  (let* ((i (pid in))
         (procs (procs u))
         (ch (channels u))
         (p (g i procs))
         (msg (in-msg in ch)))
    (s :channels (send-part in p msg (rm-part in msg ch))
       (s :procs (s i (pnew in p msg) procs) u))))

(defthm s-same-g-over-s
  (implies (not (equal a b))
           (equal (s a (g a r) (s b v r)) (s b v r)))
  :hints (("Goal" :use ((:instance s-diff-s (a b) (b a) (x v) (y (g a r))))
           :in-theory (disable s-diff-s))))

(defthm system-step-canon
  (implies (cl-checkpoint-body-input-p in)
           (equal (system-step u in) (step-canon u in)))
  :hints (("Goal" :in-theory (disable update-proc-for-normal-msg-core
                                      update-proc-for-non-first-marker-msg
                                      update-proc-for-first-marker-msg
                                      update-proc-for-first-recovery-msg
                                      update-proc-for-non-first-recovery-msg
                                      install-snapshot-entry
                                      make-snapshot-entry
                                      create-marker-message))))

;;; ---------------- part 4 ----------------
(defthm g-msg-type-nil (equal (g k nil) nil))

(defthm send-part-commute
  (implies (not (equal (pid a) (pid b)))
           (equal (send-part a pa ma (send-part b pb mb ch))
                  (send-part b pb mb (send-part a pa ma ch)))))

(defthm rm-part-commute
  (implies (not (equal (pid a) (pid b)))
           (equal (rm-part a ma (rm-part b mb ch))
                  (rm-part b mb (rm-part a ma ch)))))

(defthm sa-rm-commute-3
  (implies (or (not (equal i j)) (not (memberp k nbrs)) (consp (g i (g k ch))))
           (equal (send-all m i nbrs (remove-message-from-channel j k ch))
                  (remove-message-from-channel j k (send-all m i nbrs ch))))
  :hints (("Goal" :cases ((equal i j)))))

(defthm sc-rm-commute-3
  (implies (or (not (equal i j)) (not (memberp k nbrs)) (consp (g i (g k ch))))
           (equal (send-compute-message ls i nbrs (remove-message-from-channel j k ch))
                  (remove-message-from-channel j k (send-compute-message ls i nbrs ch))))
  :hints (("Goal" :cases ((equal i j)))))

(defthm get-msg-sa
  (implies (or (not (equal j i)) (not (memberp k nbrs)) (consp (g j (g k ch))))
           (equal (get-msg-from-channel j k (send-all m i nbrs ch))
                  (get-msg-from-channel j k ch)))
  :hints (("Goal" :cases ((equal i j)))))

(defthm get-msg-sc
  (implies (or (not (equal j i)) (not (memberp k nbrs)) (consp (g j (g k ch))))
           (equal (get-msg-from-channel j k (send-compute-message ls i nbrs ch))
                  (get-msg-from-channel j k ch)))
  :hints (("Goal" :cases ((equal i j)))))

(defthm get-msg-rm
  (implies (not (equal k i))
           (equal (get-msg-from-channel j k (remove-message-from-channel j2 i ch))
                  (get-msg-from-channel j k ch))))

(in-theory (disable get-msg-from-channel))

(defun ok-cell (a pa b ch)
  (implies (and (equal (ttype b) :receive)
                (or (equal (ttype a) :normal)
                    (equal (ttype a) :start-checkpoint)
                    (equal (ttype a) :receive))
                (equal (sender b) (pid a))
                (memberp (pid b) (nbrs-to pa)))
           (consp (g (sender b) (g (pid b) ch)))))

(defthm rm-part-over-send-part
  (implies (ok-cell a pa b ch)
           (equal (rm-part b mb (send-part a pa ma ch))
                  (send-part a pa ma (rm-part b mb ch)))))

(defthm in-msg-send-part
  (implies (ok-cell a pa b ch)
           (equal (in-msg b (send-part a pa ma ch))
                  (in-msg b ch))))

(defthm in-msg-rm-part
  (implies (not (equal (pid a) (pid b)))
           (equal (in-msg b (rm-part a ma ch))
                  (in-msg b ch))))

(defthm ok-cell-rm-part
  (implies (not (equal (pid a) (pid b)))
           (equal (ok-cell a pa b (rm-part a ma ch))
                  (ok-cell a pa b ch))))

(in-theory (disable send-part rm-part in-msg ok-cell pnew))

(defthm step-canon-commute
  (implies (and (not (equal (pid a) (pid b)))
                (ok-cell a (g (pid a) (procs u)) b (channels u))
                (ok-cell b (g (pid b) (procs u)) a (channels u)))
           (equal (step-canon (step-canon u a) b)
                  (step-canon (step-canon u b) a))))

;;; ---------------- part 5 ----------------
(defthm memberp-remove1
  (implies (memberp x (remove1-equal y l)) (memberp x l)))

(defthm cnt-process-cut-step
  (implies (cm-cut-not-taken-p (process-cut-step in st m) k)
           (cm-cut-not-taken-p m k)))

(defthm marker-consp
  (implies (marker-for-sid-in-channel-p sid c) (consp c))
  :rule-classes :forward-chaining)

(defthm markers-outgoing-consp
  (implies (and (cut-marker-in-transit-for-outgoing-nbrs-p src nbrs sid m ch)
                (not (cm-cut-not-taken-p m src))
                (memberp dst nbrs)
                (cm-cut-not-taken-p m dst))
           (marker-for-sid-in-channel-p sid (g src (g dst ch))))
  :hints (("Goal" :in-theory (disable cm-cut-not-taken-p))))

(defthm markers-srcs-consp
  (implies (and (cut-markers-in-transit-for-srcs-p srcs sid m procs ch)
                (memberp src srcs)
                (not (cm-cut-not-taken-p m src))
                (memberp dst (nbrs-to (g src procs)))
                (cm-cut-not-taken-p m dst))
           (consp (g src (g dst ch))))
  :hints (("Goal" :in-theory (disable cm-cut-not-taken-p))))

(defthm procs-equivalent-refl (procs-equivalent-p ids p p))
(defthm cl-control-refl (cl-checkpoint-control-equivalent-p ids p p))
(defthm state-equivalent-refl (state-equivalent-p x x))
(in-theory (disable state-equivalent-p))

(defthm MAIN-2
  (implies
   (post-pre-swap-start-p st m input-1 input-2)
   (state-equivalent-p
    (run-imp st (list input-1 input-2))
    (run-imp st (list input-2 input-1))))
  :hints (("Goal" :in-theory (e/d (ok-cell) (cm-cut-not-taken-p process-cut-step step-canon
                                    cut-meta-imp-consistent-p good-cut-meta-p good-state-p
                                    recovery-free-state-p))
           :use ((:instance step-canon-commute (u st) (a input-1) (b input-2))
                 (:instance cnt-process-cut-step (in input-1) (k (pid input-2)))))))

;;; ---------------- part 6 ----------------
(defthm step-canon-nop
  (implies (equal (ttype a) :nop) (equal (step-canon u a) u))
  :hints (("Goal" :in-theory (enable pnew send-part rm-part))))

(defthm nbrs-to-pnew
  (equal (g :nbrs-to (pnew a p msg)) (g :nbrs-to p))
  :hints (("Goal" :in-theory (enable pnew g-of-s-redux))))

(defthm nbrs-to-step-canon
  (equal (g :nbrs-to (g j (procs (step-canon u a))))
         (g :nbrs-to (g j (procs u))))
  :hints (("Goal" :in-theory (enable g-of-s-redux))))

(defthm cell-rm-part
  (implies (not (equal k (pid a)))
           (equal (g j (g k (rm-part a ma ch))) (g j (g k ch))))
  :hints (("Goal" :in-theory (enable rm-part))))

(defthm cell-send-part-consp
  (implies (consp (g j (g k ch)))
           (and (consp (g j (g k (send-part a pa ma ch))))
                (equal (car (g j (g k (send-part a pa ma ch))))
                       (car (g j (g k ch))))))
  :hints (("Goal" :in-theory (enable send-part))))

(defthm cell-send-part-other
  (implies (or (not (equal j (pid a))) (not (memberp k (nbrs-to pa))))
           (equal (g j (g k (send-part a pa ma ch))) (g j (g k ch))))
  :hints (("Goal" :in-theory (enable send-part))))

(defthm cell-send-part-other-2
  (implies (and (equal j (pid a)) (not (memberp k (nbrs-to (g j procs)))))
           (equal (g j (g k (send-part a (g (pid a) procs) ma ch))) (g j (g k ch))))
  :hints (("Goal" :in-theory (enable send-part))))

(defthm cell-step-canon-consp
  (implies (and (consp (g j (g k (channels u))))
                (not (equal k (pid a))))
           (and (consp (g j (g k (channels (step-canon u a)))))
                (equal (car (g j (g k (channels (step-canon u a)))))
                       (car (g j (g k (channels u)))))))
  :hints (("Goal" :in-theory (disable cell-send-part-other))))

(defthm cell-step-canon-other-1
  (implies (and (not (equal k (pid a)))
                (not (equal j (pid a))))
           (equal (g j (g k (channels (step-canon u a))))
                  (g j (g k (channels u))))))

(defthm cell-step-canon-other-2
  (implies (and (not (equal k (pid a)))
                (not (memberp k (nbrs-to (g (pid a) (procs u))))))
           (equal (g j (g k (channels (step-canon u a))))
                  (g j (g k (channels u))))))

(in-theory (disable step-canon))

(defun apids (l)
  (if (endp l) nil
    (if (equal (ttype (car l)) :nop)
        (apids (cdr l))
      (cons (pid (car l)) (apids (cdr l))))))

(defun rcv-ok (u l)
  (declare (xargs :measure (len l)))
  (if (endp l) t
    (and (implies (equal (ttype (car l)) :receive)
                  (consp (g (sender (car l)) (g (pid (car l)) (channels u)))))
         (rcv-ok (system-step u (car l)) (cdr l)))))

(defun x-ok (u x l)
  (implies (and (equal (ttype x) :receive)
                (memberp (sender x) (apids l))
                (memberp (pid x) (nbrs-to (g (sender x) (procs u)))))
           (consp (g (sender x) (g (pid x) (channels u))))))

(defthm run-imp-cons
  (equal (run-imp u (cons a l)) (run-imp (system-step u a) l)))
(defthm run-imp-endp
  (implies (endp l) (equal (run-imp u l) u)))
(defthm rcv-ok-cons
  (equal (rcv-ok u (cons a l))
         (and (implies (equal (ttype a) :receive)
                       (consp (g (sender a) (g (pid a) (channels u)))))
              (rcv-ok (system-step u a) l))))
(defthm rcv-ok-endp
  (implies (endp l) (rcv-ok u l)))
(defthm body-cons
  (equal (cl-checkpoint-body-inputs-p (cons a l))
         (and (cl-checkpoint-body-input-p a) (cl-checkpoint-body-inputs-p l))))
(defthm apids-cons
  (equal (apids (cons a l))
         (if (equal (ttype a) :nop) (apids l) (cons (pid a) (apids l)))))
(in-theory (disable run-imp rcv-ok cl-checkpoint-body-inputs-p apids system-step
                    cl-checkpoint-body-input-p))

(defun lc-ind (u l)
  (declare (xargs :measure (len l)))
  (if (endp l) u (lc-ind (system-step u (car l)) (cdr l))))

(defthm x-ok-step
  (implies (and (x-ok u x l)
                (consp l)
                (cl-checkpoint-body-input-p (car l))
                (not (memberp (pid x) (apids l))))
           (x-ok (step-canon u (car l)) x (cdr l)))
  :hints (("Goal" :cases ((equal (ttype (car l)) :nop))
           :expand ((apids l)))))

(defthm x-ok-step-nop
  (implies (and (x-ok u x l)
                (consp l)
                (equal (ttype (car l)) :nop))
           (x-ok u x (cdr l)))
  :hints (("Goal" :expand ((apids l)))))

(defthm list-commute
  (implies (and (cl-checkpoint-body-input-p x)
                (cl-checkpoint-body-inputs-p l)
                (not (memberp (pid x) (apids l)))
                (rcv-ok u l)
                (x-ok u x l))
           (equal (run-imp (system-step u x) l)
                  (system-step (run-imp u l) x)))
  :hints (("Goal" :induct (lc-ind u l)
           :in-theory (disable x-ok))
          ("Subgoal *1/2" :cases ((equal (ttype (car l)) :nop))
           :expand ((run-imp u l) (run-imp (step-canon u x) l)
                    (rcv-ok u l) (apids l) (cl-checkpoint-body-inputs-p l)))
          ("Subgoal *1/2.2"
           :in-theory (e/d (ok-cell x-ok) (step-canon-commute))
           :use ((:instance step-canon-commute (u u) (a x) (b (car l)))))))

(defthm rcv-ok-shift
  (implies (and (cl-checkpoint-body-input-p x)
                (cl-checkpoint-body-inputs-p l)
                (not (memberp (pid x) (apids l)))
                (rcv-ok u l)
                (x-ok u x l))
           (rcv-ok (system-step u x) l))
  :hints (("Goal" :induct (lc-ind u l)
           :in-theory (disable x-ok))
          ("Subgoal *1/2" :cases ((equal (ttype (car l)) :nop))
           :expand ((rcv-ok (step-canon u x) l)
                    (rcv-ok u l) (apids l) (cl-checkpoint-body-inputs-p l)))
          ("Subgoal *1/2.2"
           :in-theory (e/d (ok-cell x-ok) (step-canon-commute))
           :use ((:instance step-canon-commute (u u) (a x) (b (car l)))))))

;;; ---------------- part 7 ----------------
;; step-canon accessors
(defthm step-canon-procs-other
  (implies (not (equal k (pid a)))
           (equal (g k (g :procs (step-canon u a))) (g k (g :procs u))))
  :hints (("Goal" :in-theory (enable step-canon))))
(defthm step-canon-procs-same
  (equal (g (pid a) (g :procs (step-canon u a)))
         (pnew a (g (pid a) (g :procs u)) (in-msg a (g :channels u))))
  :hints (("Goal" :in-theory (enable step-canon))))
(defthm step-canon-channels
  (equal (g :channels (step-canon u a))
         (send-part a (g (pid a) (g :procs u)) (in-msg a (g :channels u))
                    (rm-part a (in-msg a (g :channels u)) (g :channels u))))
  :hints (("Goal" :in-theory (enable step-canon))))
(defthm step-canon-proc-ids
  (equal (g :proc-ids (step-canon u a)) (g :proc-ids u))
  :hints (("Goal" :in-theory (enable step-canon))))

;; run lemmas
(defthm run-procs-other
  (implies (and (cl-checkpoint-body-inputs-p l)
                (not (memberp k (apids l))))
           (equal (g k (g :procs (run-imp u l))) (g k (g :procs u))))
  :hints (("Goal" :induct (lc-ind u l) :expand ((run-imp u l) (apids l) (cl-checkpoint-body-inputs-p l)))))

(defthm run-nbrs-to
  (implies (cl-checkpoint-body-inputs-p l)
           (equal (g :nbrs-to (g j (g :procs (run-imp u l))))
                  (g :nbrs-to (g j (g :procs u)))))
  :hints (("Goal" :induct (lc-ind u l) :expand ((run-imp u l) (cl-checkpoint-body-inputs-p l)))))

(defthm run-proc-ids
  (implies (cl-checkpoint-body-inputs-p l)
           (equal (g :proc-ids (run-imp u l)) (g :proc-ids u)))
  :hints (("Goal" :induct (lc-ind u l) :expand ((run-imp u l) (cl-checkpoint-body-inputs-p l)))))

(defthm run-cell-consp
  (implies (and (cl-checkpoint-body-inputs-p l)
                (not (memberp k (apids l)))
                (consp (g j (g k (g :channels u)))))
           (and (consp (g j (g k (g :channels (run-imp u l)))))
                (equal (car (g j (g k (g :channels (run-imp u l)))))
                       (car (g j (g k (g :channels u)))))))
  :hints (("Goal" :induct (lc-ind u l)
           :in-theory (disable step-canon-channels)
           :expand ((run-imp u l) (apids l) (cl-checkpoint-body-inputs-p l)))))

(defthm run-cell-other-1
  (implies (and (cl-checkpoint-body-inputs-p l)
                (not (memberp k (apids l)))
                (not (memberp j (apids l))))
           (equal (g j (g k (g :channels (run-imp u l))))
                  (g j (g k (g :channels u)))))
  :hints (("Goal" :induct (lc-ind u l)
           :in-theory (disable step-canon-channels)
           :expand ((run-imp u l) (apids l) (cl-checkpoint-body-inputs-p l)))))

(defthm run-cell-other-2
  (implies (and (cl-checkpoint-body-inputs-p l)
                (not (memberp k (apids l)))
                (not (memberp k (nbrs-to (g j (g :procs u))))))
           (equal (g j (g k (g :channels (run-imp u l))))
                  (g j (g k (g :channels u)))))
  :hints (("Goal" :induct (lc-ind u l)
           :in-theory (disable step-canon-channels)
           :expand ((run-imp u l) (apids l) (cl-checkpoint-body-inputs-p l)))
          ("Subgoal *1/2" :cases ((equal j (pid (car l)))))))

(defthm run-imp-append
  (equal (run-imp u (append a b)) (run-imp (run-imp u a) b))
  :hints (("Goal" :induct (lc-ind u a) :expand ((run-imp u a) (append a b)))))

(defthm rcv-ok-append
  (equal (rcv-ok u (append a b)) (and (rcv-ok u a) (rcv-ok (run-imp u a) b)))
  :hints (("Goal" :induct (lc-ind u a) :expand ((run-imp u a) (rcv-ok u a) (append a b)))))

(defthm apids-append
  (equal (apids (append a b)) (append (apids a) (apids b)))
  :hints (("Goal" :in-theory (enable apids))))

(defthm body-append
  (equal (cl-checkpoint-body-inputs-p (append a b))
         (and (cl-checkpoint-body-inputs-p a) (cl-checkpoint-body-inputs-p b)))
  :hints (("Goal" :in-theory (enable cl-checkpoint-body-inputs-p))))

(defthm memberp-append
  (equal (memberp x (append a b)) (or (memberp x a) (memberp x b))))

(defthm subset-append
  (equal (subset (append a b) c) (and (subset a c) (subset b c))))

;; markers
(defthm marker-snoc
  (implies (marker-for-sid-in-channel-p sid c)
           (marker-for-sid-in-channel-p sid (snoc c e))))

(defthm marker-snoc-last
  (implies (and (equal (msg-type e) :marker) (equal (sid e) sid))
           (marker-for-sid-in-channel-p sid (snoc c e))))

(defthm marker-sa
  (implies (marker-for-sid-in-channel-p sid (g a (g b ch)))
           (marker-for-sid-in-channel-p sid (g a (g b (send-all m i nbrs ch)))))
  :hints (("Goal" :induct (sa-ind nbrs) :in-theory (enable g-of-s-redux))))

(defthm marker-sc
  (implies (marker-for-sid-in-channel-p sid (g a (g b ch)))
           (marker-for-sid-in-channel-p sid (g a (g b (send-compute-message ls i nbrs ch)))))
  :hints (("Goal" :in-theory (enable g-of-s-redux))))

(defthm marker-send-part
  (implies (marker-for-sid-in-channel-p sid (g a (g b ch)))
           (marker-for-sid-in-channel-p sid (g a (g b (send-part x p msg ch)))))
  :hints (("Goal" :in-theory (enable send-part))))

(defthm marker-sa-member
  (implies (and (memberp out nbrs)
                (equal (msg-type m) :marker))
           (marker-for-sid-in-channel-p (sid m) (g i (g out (send-all m i nbrs ch)))))
  :hints (("Goal" :induct (sa-ind nbrs) :in-theory (enable g-of-s-redux))))

(defthm marker-rm-part
  (implies (and (marker-for-sid-in-channel-p sid (g a (g b ch)))
                (not (and (equal (ttype x) :receive)
                          (equal a (sender x))
                          (equal b (pid x))
                          (equal (msg-type (car (g a (g b ch)))) :marker)
                          (equal (sid (car (g a (g b ch)))) sid))))
           (marker-for-sid-in-channel-p sid (g a (g b (rm-part x msg ch)))))
  :hints (("Goal" :in-theory (enable rm-part remove-message-from-channel g-of-s-redux))))

;;; ---------------- part 8 ----------------
(defun takes-cut (x p msg sid)
  (or (and (equal (ttype x) :start-checkpoint)
           (equal (list (pid x) (counter p)) sid))
      (and (equal (ttype x) :receive)
           (equal (msg-type msg) :marker)
           (equal (sid msg) sid))))

(defun new-cnt (x p msg sid cnt)
  (if (takes-cut x p msg sid) (remove1-equal (pid x) cnt) cnt))

(defthm remove1-nonmember
  (implies (and (true-listp l) (not (memberp x l)))
           (equal (remove1-equal x l) l)))

(defthm memberp-remove1-unique
  (implies (uniquep l)
           (equal (memberp x (remove1-equal y l))
                  (and (memberp x l) (not (equal x y))))))

(defthm uniquep-remove1
  (implies (uniquep l) (uniquep (remove1-equal y l))))

(defthm true-listp-remove1
  (implies (true-listp l) (true-listp (remove1-equal y l))))

(defthm pcs-sid
  (equal (g :sid (process-cut-step x st m)) (g :sid m)))

(defthm pcs-cnt
  (implies (true-listp (cm-cut-not-taken m))
           (equal (cm-cut-not-taken (process-cut-step x st m))
                  (new-cnt x (g (pid x) (g :procs st))
                           (in-msg x (g :channels st))
                           (g :sid m)
                           (cm-cut-not-taken m))))
  :hints (("Goal" :in-theory (enable in-msg))))

(defthm pcs-before
  (equal (cm-before-cut-input-sequence (process-cut-step x st m))
         (if (memberp (pid x) (cm-cut-not-taken m))
             (append (cm-before-cut-input-sequence m) (list x))
           (cm-before-cut-input-sequence m))))

(defthm pcs-after
  (equal (cm-after-cut-input-sequence (process-cut-step x st m))
         (if (memberp (pid x) (cm-cut-not-taken m))
             (cm-after-cut-input-sequence m)
           (append (cm-after-cut-input-sequence m) (list x)))))

(in-theory (disable process-cut-step cm-cut-not-taken cm-before-cut-input-sequence
                    cm-after-cut-input-sequence))

;; no-target invariant
(defun no-target (ids sid cnt procs)
  (if (endp ids) t
    (and (implies (memberp (car ids) cnt)
                  (not (memberp sid (snapshot-ids (g (car ids) procs)))))
         (no-target (cdr ids) sid cnt procs))))

(defthm no-target-necc
  (implies (and (no-target ids sid cnt procs)
                (memberp k ids) (memberp k cnt))
           (not (memberp sid (snapshot-ids (g k procs))))))

(defthm sids-pnew
  (implies (and (memberp sid (snapshot-ids (pnew x p msg)))
                (not (memberp sid (snapshot-ids p))))
           (or (and (equal (ttype x) :start-checkpoint)
                    (equal sid (list (pid x) (counter p))))
               (and (equal (ttype x) :receive)
                    (equal (msg-type msg) :marker)
                    (equal sid (sid msg)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable pnew g-of-s-redux))))

(defthm no-target-step
  (implies (and (no-target ids sid cnt (g :procs u))
                (true-listp cnt) (uniquep cnt))
           (no-target ids sid
                      (new-cnt x (g (pid x) (g :procs u)) (in-msg x (g :channels u)) sid cnt)
                      (g :procs (step-canon u x))))
  :hints (("Goal" :induct (no-target ids sid cnt (g :procs u))
           :in-theory (disable step-canon-procs-same))
          ("Subgoal *1/2" :cases ((equal (car ids) (pid x))))
          ("Subgoal *1/2.1"
           :in-theory (enable step-canon-procs-same)
           :use ((:instance sids-pnew (p (g (pid x) (g :procs u)))
                            (msg (in-msg x (g :channels u))))))))

(defthm no-target-subset-cnt
  (implies (and (no-target ids sid cnt procs) (uniquep cnt))
           (no-target ids sid (remove1-equal y cnt) procs)))

;; markers invariant
(defun-sk mk-all (sid cnt procs ch ids)
  (forall (src out)
          (implies (and (memberp src ids)
                        (not (memberp src cnt))
                        (memberp out (nbrs-to (g src procs)))
                        (memberp out cnt))
                   (marker-for-sid-in-channel-p sid (g src (g out ch))))))

(defthm mk-all-consp
  (implies (and (mk-all sid cnt procs ch ids)
                (memberp src ids)
                (not (memberp src cnt))
                (memberp out (nbrs-to (g src procs)))
                (memberp out cnt))
           (consp (g src (g out ch))))
  :hints (("Goal" :use mk-all-necc)))

(defthm subset-memberp
  (implies (and (subset a b) (memberp x a)) (memberp x b)))

(defthm mk-all-init
  (implies (subset ids cnt)
           (mk-all sid cnt procs ch ids))
  :hints (("Goal" :in-theory (enable mk-all))))

(defthm marker-car
  (implies (and (marker-for-sid-in-channel-p sid c)
                (not (and (equal (msg-type (car c)) :marker)
                          (equal (sid (car c)) sid))))
           (marker-for-sid-in-channel-p sid (cdr c))))

(defthm marker-sa-member-2
  (implies (and (memberp out nbrs)
                (equal (msg-type m) :marker)
                (equal (sid m) sid))
           (marker-for-sid-in-channel-p sid (g i (g out (send-all m i nbrs ch))))))

(defthm takes-cut-nop-lemma
  (implies (equal (ttype x) :nop) (not (takes-cut x p msg sid))))

(in-theory (disable mk-all))

(defthm l-old-cell-other
  (implies (and (marker-for-sid-in-channel-p sid (g src (g out ch)))
                (not (and (equal src (sender x)) (equal out (pid x)))))
           (marker-for-sid-in-channel-p sid (g src (g out (send-part x p msg (rm-part x msg ch))))))
  :hints (("Goal" :in-theory (disable marker-rm-part)
           :use ((:instance marker-rm-part (a src) (b out))))))

(defthm l-old-cell-same
  (implies (and (marker-for-sid-in-channel-p sid (g (sender x) (g (pid x) ch)))
                (not (takes-cut x p (in-msg x ch) sid)))
           (marker-for-sid-in-channel-p sid (g (sender x) (g (pid x)
                     (send-part x p (in-msg x ch) (rm-part x (in-msg x ch) ch))))))
  :hints (("Goal" :in-theory (e/d (in-msg get-msg-from-channel) (marker-rm-part))
           :use ((:instance marker-rm-part (a (sender x)) (b (pid x)) (msg (in-msg x ch)))))))

(defthm l-new-cell
  (implies (and (takes-cut x p msg sid)
                (memberp out (nbrs-to p))
                (not (memberp sid (snapshot-ids p))))
           (marker-for-sid-in-channel-p sid (g (pid x) (g out (send-part x p msg ch2)))))
  :hints (("Goal" :in-theory (enable send-part))))

(in-theory (disable takes-cut))

(defthm mk-point-b
  (implies (and (mk-all sid cnt (g :procs u) (g :channels u) ids)
                (cl-checkpoint-body-input-p x)
                (memberp (pid x) cnt)
                (uniquep cnt)
                (implies (not (equal (ttype x) :nop))
                         (not (memberp sid (snapshot-ids (g (pid x) (g :procs u))))))
                (memberp src ids)
                (not (memberp src (new-cnt x (g (pid x) (g :procs u)) (in-msg x (g :channels u)) sid cnt)))
                (memberp out (nbrs-to (g src (g :procs u))))
                (memberp out (new-cnt x (g (pid x) (g :procs u)) (in-msg x (g :channels u)) sid cnt)))
           (marker-for-sid-in-channel-p sid (g src (g out (g :channels (step-canon u x))))))
  :hints (("Goal" :cases ((equal (ttype x) :nop)
                          (and (memberp src cnt))
                          (and (not (memberp src cnt))
                               (equal src (sender x)) (equal out (pid x)))
                          (and (not (memberp src cnt))
                               (not (and (equal src (sender x)) (equal out (pid x))))))
           :in-theory (e/d (takes-cut-nop-lemma) (mk-all-necc step-canon-channels))
           :use ((:instance mk-all-necc (procs (g :procs u)) (ch (g :channels u)))
                 (:instance step-canon-channels (a x))))))

(defthm mk-step-b
  (implies (and (mk-all sid cnt (g :procs u) (g :channels u) ids)
                (cl-checkpoint-body-input-p x)
                (memberp (pid x) cnt)
                (uniquep cnt)
                (implies (not (equal (ttype x) :nop))
                         (not (memberp sid (snapshot-ids (g (pid x) (g :procs u)))))))
           (mk-all sid
                   (new-cnt x (g (pid x) (g :procs u)) (in-msg x (g :channels u)) sid cnt)
                   (g :procs (step-canon u x))
                   (g :channels (step-canon u x))
                   ids))
  :hints (("Goal" :in-theory (e/d (mk-all) (mk-all-necc new-cnt mk-point-b
                                             step-canon-channels step-canon-procs-same
                                             step-canon-procs-other step-canon-nop))
           :use ((:instance mk-point-b
                            (src (mv-nth 0 (mk-all-witness sid
                   (new-cnt x (g (pid x) (g :procs u)) (in-msg x (g :channels u)) sid cnt)
                   (g :procs (step-canon u x))
                   (g :channels (step-canon u x))
                   ids)))
                            (out (mv-nth 1 (mk-all-witness sid
                   (new-cnt x (g (pid x) (g :procs u)) (in-msg x (g :channels u)) sid cnt)
                   (g :procs (step-canon u x))
                   (g :channels (step-canon u x))
                   ids))))))))

;;; ---------------- part 9 ----------------
(defun none-in (l cnt)
  (if (endp l) t
    (and (not (memberp (car l) cnt))
         (none-in (cdr l) cnt))))

(defthm none-in-memberp
  (implies (and (none-in l cnt) (memberp k cnt)) (not (memberp k l))))
(defthm none-in-memberp-2
  (implies (and (none-in l cnt) (memberp k l)) (not (memberp k cnt))))
(defthm none-in-remove1
  (implies (none-in l cnt) (none-in l (remove1-equal y cnt))))
(defthm none-in-append
  (equal (none-in (append a b) cnt) (and (none-in a cnt) (none-in b cnt))))

(defthm new-cnt-nonmember
  (implies (and (true-listp cnt) (not (memberp (pid x) cnt)))
           (equal (new-cnt x p msg sid cnt) cnt)))

(defthm new-cnt-props
  (and (implies (true-listp cnt) (true-listp (new-cnt x p msg sid cnt)))
       (implies (uniquep cnt) (uniquep (new-cnt x p msg sid cnt)))
       (implies (none-in l cnt) (none-in l (new-cnt x p msg sid cnt)))))

(defthm x-ok-from-mk
  (implies (and (mk-all sid cnt (g :procs tt) (g :channels tt) (g :proc-ids tt))
                (none-in (apids aft) cnt)
                (subset (apids aft) (g :proc-ids tt))
                (memberp (pid x) cnt))
           (x-ok tt x aft))
  :hints (("Goal" :in-theory (disable mk-all-consp)
           :use ((:instance mk-all-consp (procs (g :procs tt)) (ch (g :channels tt))
                            (ids (g :proc-ids tt))
                            (src (sender x)) (out (pid x)))))))

(defthm head-same
  (implies (and (cl-checkpoint-body-inputs-p aft)
                (not (memberp (pid x) (apids aft)))
                (x-ok tt x aft))
           (equal (in-msg x (g :channels (run-imp tt aft)))
                  (in-msg x (g :channels tt))))
  :hints (("Goal" :in-theory (enable in-msg get-msg-from-channel))))

(in-theory (disable x-ok new-cnt))

(defthm new-cnt-nop
  (implies (equal (ttype x) :nop) (equal (new-cnt x p msg sid cnt) cnt))
  :hints (("Goal" :in-theory (enable new-cnt))))

(defthm b1
  (implies (and (cl-checkpoint-body-inputs-p aft)
                (rcv-ok tt aft)
                (none-in (apids aft) cnt)
                (subset (apids aft) (g :proc-ids tt))
                (mk-all sid cnt (g :procs tt) (g :channels tt) (g :proc-ids tt))
                (cl-checkpoint-body-input-p x)
                (memberp (pid x) cnt))
           (and (equal (system-step (run-imp tt aft) x)
                       (run-imp (system-step tt x) aft))
                (rcv-ok (system-step tt x) aft)))
  :hints (("Goal" :in-theory (disable list-commute rcv-ok-shift system-step-canon)
           :use ((:instance list-commute (u tt) (l aft))
                 (:instance rcv-ok-shift (u tt) (l aft))))))

(defthm b5
  (implies (and (cl-checkpoint-body-inputs-p aft)
                (none-in (apids aft) cnt)
                (subset (apids aft) (g :proc-ids tt))
                (mk-all sid cnt (g :procs tt) (g :channels tt) (g :proc-ids tt))
                (no-target (g :proc-ids tt) sid cnt (g :procs (run-imp tt aft)))
                (uniquep cnt)
                (cl-checkpoint-body-input-p x)
                (legal-inputp (run-imp tt aft) x)
                (memberp (pid x) cnt))
           (mk-all sid (new-cnt x (g (pid x) (g :procs (run-imp tt aft)))
                                (in-msg x (g :channels (run-imp tt aft))) sid cnt)
                   (g :procs (system-step tt x)) (g :channels (system-step tt x))
                   (g :proc-ids (system-step tt x))))
  :hints (("Goal" :in-theory (disable mk-step-b no-target-necc)
           :use ((:instance mk-step-b (u tt) (ids (g :proc-ids tt)))
                 (:instance no-target-necc (ids (g :proc-ids tt)) (k (pid x))
                            (procs (g :procs (run-imp tt aft))))))))

(defthm b6
  (implies (and (no-target ids sid cnt (g :procs s))
                (true-listp cnt) (uniquep cnt)
                (cl-checkpoint-body-input-p x))
           (no-target ids sid
                      (new-cnt x (g (pid x) (g :procs s)) (in-msg x (g :channels s)) sid cnt)
                      (g :procs (system-step s x)))))

;;; ---------------- part 10 ----------------
(defun inv (st0 s m)
  (let* ((cnt (cm-cut-not-taken m))
         (sid (g :sid m))
         (tt (run-imp st0 (cm-before-cut-input-sequence m)))
         (aft (cm-after-cut-input-sequence m)))
    (and (equal s (run-imp tt aft))
         (cl-checkpoint-body-inputs-p aft)
         (rcv-ok tt aft)
         (none-in (apids aft) cnt)
         (subset (apids aft) (g :proc-ids tt))
         (mk-all sid cnt (g :procs tt) (g :channels tt) (g :proc-ids tt))
         (no-target (g :proc-ids s) sid cnt (g :procs s))
         (true-listp cnt)
         (uniquep cnt))))

(defthm run-imp-snoc
  (equal (run-imp u (append a (list x)))
         (system-step (run-imp u a) x)))

(defthm proc-ids-system-step
  (implies (cl-checkpoint-body-input-p x)
           (equal (g :proc-ids (system-step u x)) (g :proc-ids u))))

(defthm legal-receive-consp
  (implies (and (legal-inputp u x) (equal (ttype x) :receive))
           (consp (g (sender x) (g (pid x) (g :channels u))))))

(defthm legal-member-ids
  (implies (and (legal-inputp u x) (cl-checkpoint-body-input-p x)
                (not (equal (ttype x) :nop)))
           (memberp (pid x) (g :proc-ids u))))

(defthm legal-member-ids-run
  (implies (and (legal-inputp (run-imp u l) x) (cl-checkpoint-body-input-p x)
                (cl-checkpoint-body-inputs-p l)
                (not (equal (ttype x) :nop)))
           (memberp (pid x) (g :proc-ids u)))
  :hints (("Goal" :in-theory (disable legal-member-ids)
           :use ((:instance legal-member-ids (u (run-imp u l)))))))

(defthm inv-step
  (implies (and (inv st0 s m)
                (cl-checkpoint-body-input-p x)
                (legal-inputp s x))
           (inv st0 (system-step s x) (process-cut-step x s m)))
  :hints (("Goal" :cases ((memberp (pid x) (cm-cut-not-taken m)))
           :in-theory (disable b1 b5 b6 system-step-canon legal-inputp)
           :use ((:instance b1 (tt (run-imp st0 (cm-before-cut-input-sequence m)))
                            (aft (cm-after-cut-input-sequence m))
                            (cnt (cm-cut-not-taken m)) (sid (g :sid m)))
                 (:instance b5 (tt (run-imp st0 (cm-before-cut-input-sequence m)))
                            (aft (cm-after-cut-input-sequence m))
                            (cnt (cm-cut-not-taken m)) (sid (g :sid m)))
                 (:instance b6 (ids (g :proc-ids s))
                            (cnt (cm-cut-not-taken m)) (sid (g :sid m)))))))

;;; ---------------- part 11 ----------------
(in-theory (disable inv))

(defthm gen
  (implies (and (inv st0 s m)
                (cl-checkpoint-body-inputs-p l)
                (legal-input-sequencep s l)
                (checkpoint-completes-at-segment-end-p l s m))
           (equal (run-imp s l)
                  (run-imp (run-imp st0 (cm-before-cut-input-sequence
                                         (scan-until-checkpoint-done l s m)))
                           (cm-after-cut-input-sequence
                            (scan-until-checkpoint-done l s m)))))
  :hints (("Goal" :induct (scan-until-checkpoint-done l s m)
           :in-theory (disable system-step-canon legal-inputp checkpoint-collection-complete-p)
           :expand ((run-imp s l) (legal-input-sequencep s l)
                    (cl-checkpoint-body-inputs-p l)
                    (checkpoint-completes-at-segment-end-p l s m)))
          ("Subgoal *1/1" :in-theory (enable inv))))

;; initial invariant
(defthm stored-not-member
  (implies (stored-sids-for-initiator-have-smaller-counters-p i c sids)
           (not (memberp (list i c) sids))))

(defthm all-stored-no-target
  (implies (all-stored-sids-for-initiator-have-smaller-counters-p i ids procs)
           (no-target ids (list i (counter (g i procs))) cnt procs)))

(defthm all-init-member
  (implies (and (all-initiators-stored-sids-have-smaller-counters-p inits ids procs)
                (memberp i inits))
           (all-stored-sids-for-initiator-have-smaller-counters-p i ids procs)))

(defthm subset-cons-right
  (implies (subset a b) (subset a (cons x b))))
(defthm subset-refl (subset a a))

(defthm inv-init
  (implies (and (good-state-p st)
                (memberp i (g :proc-ids st)))
           (inv st st (make-cut-meta (list i (counter (g i (g :procs st)))) i st)))
  :hints (("Goal" :in-theory (enable inv cm-cut-not-taken cm-before-cut-input-sequence
                                     cm-after-cut-input-sequence))))

(defthm MAIN-1
  (implies
   (checkpoint-start-end-segment-p st input-seg)
   (state-equivalent-p
    (run-imp st input-seg)
    (run-imp
     st
     (append
      (checkpoint-segment-before-cut-inputs st input-seg)
      (checkpoint-segment-after-cut-inputs st input-seg)))))
  :hints (("Goal" :in-theory (e/d (cl-checkpoint-body-input-p)
                                  (gen inv-init make-cut-meta good-state-p
                                       legal-inputp scan-until-checkpoint-done
                                       checkpoint-completes-at-segment-end-p
                                       recovery-free-state-p))
           :expand ((cl-checkpoint-body-inputs-p input-seg)
                    (legal-input-sequencep st input-seg))
           :use ((:instance gen (st0 st) (s st) (l input-seg)
                            (m (checkpoint-segment-initial-meta st input-seg)))
                 (:instance inv-init (i (pid (car input-seg))))))))
