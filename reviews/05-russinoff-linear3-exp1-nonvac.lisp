; Non-vacuity checks for 05-russinoff-linear3/exp1/solution.lisp (reviewer addition, not part of the run).
; Certify next to a copy of solution.lisp: cert.pl --acl2 <ACL2 8.7 image> 05-russinoff-linear3-exp1-nonvac.lisp

(in-package "ACL2")
(include-book "solution")

;;; Field facts on the raw (unfixed) operations, from the constraints.
(defthm fadd-f0-right (implies (fp x) (equal (fadd x (f0)) x))
  :hints (("Goal" :use ((:instance fadd-comm (y (f0)))))))
(defthm fmul-f1-right (implies (fp x) (equal (fmul x (f1)) x))
  :hints (("Goal" :use ((:instance fmul-comm (y (f1)))))))
(defthm fmul-f0-left (implies (fp x) (equal (fmul (f0) x) (f0)))
  :hints (("Goal" :use ((:instance f*-f0-1))
           :in-theory (e/d (f* ffix) (f*-f0-1 f*-comm fmul-comm)))))
(defthm fmul-f0-right (implies (fp x) (equal (fmul x (f0)) (f0)))
  :hints (("Goal" :use ((:instance fmul-comm (x x) (y (f0))))
           :in-theory (disable fmul-comm))))
(defthm fadd-f0-f0 (equal (fadd (f0) (f0)) (f0)))

;;; V := F (dimension 1)
(defun vp1 (x) (fp x))
(defun v01 () (f0))
(defun vneg1 (x) (fneg x))
(defun vadd1 (x y) (fadd x y))
(defun vmul1 (c x) (fmul c x))
(defun vbasis1 () (list (f1)))
(defun vcoord1 (x) (list x))
(defun vp-listp1 (l) (if (consp l) (and (vp1 (car l)) (vp-listp1 (cdr l))) (null l)))
(defun vlc1 (cs xs) (if (endp xs) (v01) (vadd1 (vmul1 (car cs) (car xs)) (vlc1 (cdr cs) (cdr xs)))))

;;; W := F x F (dimension 2)
(defun wp2 (x) (and (consp x) (fp (car x)) (fp (cdr x))))
(defun w02 () (cons (f0) (f0)))
(defun wneg2 (x) (cons (fneg (car x)) (fneg (cdr x))))
(defun wadd2 (x y) (cons (fadd (car x) (car y)) (fadd (cdr x) (cdr y))))
(defun wmul2 (c x) (cons (fmul c (car x)) (fmul c (cdr x))))
(defun wbasis2 () (list (cons (f1) (f0)) (cons (f0) (f1))))
(defun wcoord2 (x) (list (car x) (cdr x)))
(defun wp-listp2 (l) (if (consp l) (and (wp2 (car l)) (wp-listp2 (cdr l))) (null l)))
(defun wlc2 (cs xs) (if (endp xs) (w02) (wadd2 (wmul2 (car cs) (car xs)) (wlc2 (cdr cs) (cdr xs)))))

;;; T(x) := (x, 0)
(defun lt12 (x) (cons x (f0)))

(defun-sk injective12 ()
  (forall x (implies (and (vp1 x) (equal (lt12 x) (w02))) (equal x (v01)))))
(defun-sk preimage12 (y) (exists x (and (vp1 x) (equal (lt12 x) y))))
(defun-sk surjective12 () (forall y (implies (wp2 y) (preimage12 y))))
(defun dim-v1 () (len (vbasis1)))
(defun dim-w2 () (len (wbasis2)))

(defthm len2-cases
  (implies (and (f-listp cs) (equal (len cs) 2))
           (equal cs (list (car cs) (cadr cs))))
  :hints (("Goal" :expand ((len cs) (len (cdr cs)) (len (cddr cs)))))
  :rule-classes nil)

(defthm len1-cases
  (implies (and (f-listp cs) (equal (len cs) 1))
           (equal cs (list (car cs))))
  :hints (("Goal" :expand ((len cs) (len (cdr cs)))))
  :rule-classes nil)

;; Hints for the constraint subgoals of the functional instance, keyed on content
;; (top-level subgoal numbers are not stable).
(defun constraint-hint (id clause)
  (declare (xargs :mode :program))
  (and (equal (len (access clause-id id :case-lst)) 1)
       (null (access clause-id id :pool-lst))
       (cond ((ffnnamep-lst 'surjective12-witness clause)
              '(:use ((:instance surjective12-necc (y y)))
                :in-theory (disable preimage12 lt12 surjective12-necc)))
             ((ffnnamep-lst 'preimage12-witness clause)
              '(:use ((:instance preimage12-suff (x x) (y (lt12 x))))
                :in-theory (disable preimage12-suff)))
             ((ffnnamep-lst 'preimage12 clause)
              '(:use ((:instance preimage12-suff (x x) (y y)))
                :in-theory (disable preimage12 preimage12-suff)))
             ((ffnnamep-lst 'all-f0 clause)
              '(:use ((:instance len1-cases (cs cs)) (:instance len2-cases (cs cs)))))
             (t nil))))

(defthm main-instance-1-to-2
  (implies (injective12)
           (and (<= (dim-v1) (dim-w2))
                (iff (surjective12) (equal (dim-v1) (dim-w2)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable (:e dim-v1) (:e dim-w2) (:e vbasis1) (:e wbasis2) (:e wlc2) (:e vlc1) (:e wp-listp2) (:e vp-listp1))
           :use ((:functional-instance main
                  (vp vp1) (v0 v01) (vneg vneg1) (vadd vadd1) (vmul vmul1)
                  (vbasis vbasis1) (vcoord vcoord1) (vp-listp vp-listp1) (vlc vlc1)
                  (wp wp2) (w0 w02) (wneg wneg2) (wadd wadd2) (wmul wmul2)
                  (wbasis wbasis2) (wcoord wcoord2) (wp-listp wp-listp2) (wlc wlc2)
                  (lt lt12)
                  (injective injective12) (injective-witness injective12-witness)
                  (preimage preimage12) (preimage-witness preimage12-witness)
                  (surjective surjective12) (surjective-witness surjective12-witness)
                  (dim-v dim-v1) (dim-w dim-w2))))
          (constraint-hint id clause)))

;; T(x) = (x, 0) is injective ...
(defthm injective12-holds (injective12))

;; ... so MAIN, instantiated, says it is not surjective (dim 1 /= dim 2).
(defthm not-surjective12
  (not (surjective12))
  :hints (("Goal" :use (main-instance-1-to-2 injective12-holds)
           :in-theory (disable injective12 surjective12))))

;; Direct check, independent of MAIN: (0, 1) has no preimage.
(defthm no-preimage-0-1
  (not (preimage12 (cons (f0) (f1))))
  :hints (("Goal" :use ((:instance f0-not-f1)))))

;;; Second model: V = W = F (both dimension 1), T = identity.
(defun lt11 (x) x)
(defun-sk injective11 ()
  (forall x (implies (and (vp1 x) (equal (lt11 x) (v01))) (equal x (v01)))))
(defun-sk preimage11 (y) (exists x (and (vp1 x) (equal (lt11 x) y))))
(defun-sk surjective11 () (forall y (implies (vp1 y) (preimage11 y))))

(defun constraint-hint-11 (id clause)
  (declare (xargs :mode :program))
  (and (equal (len (access clause-id id :case-lst)) 1)
       (null (access clause-id id :pool-lst))
       (cond ((ffnnamep-lst 'surjective11-witness clause)
              '(:use ((:instance surjective11-necc (y y)))
                :in-theory (disable preimage11 lt11 surjective11-necc)))
             ((ffnnamep-lst 'preimage11-witness clause)
              '(:use ((:instance preimage11-suff (x x) (y (lt11 x))))
                :in-theory (disable preimage11-suff)))
             ((ffnnamep-lst 'preimage11 clause)
              '(:use ((:instance preimage11-suff (x x) (y y)))
                :in-theory (disable preimage11 preimage11-suff)))
             ((ffnnamep-lst 'all-f0 clause)
              '(:use ((:instance len1-cases (cs cs)))))
             (t nil))))

(defthm main-instance-1-to-1
  (implies (injective11)
           (and (<= (dim-v1) (dim-v1))
                (iff (surjective11) (equal (dim-v1) (dim-v1)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable (:e dim-v1) (:e vbasis1) (:e vlc1) (:e vp-listp1))
           :use ((:functional-instance main
                  (vp vp1) (v0 v01) (vneg vneg1) (vadd vadd1) (vmul vmul1)
                  (vbasis vbasis1) (vcoord vcoord1) (vp-listp vp-listp1) (vlc vlc1)
                  (wp vp1) (w0 v01) (wneg vneg1) (wadd vadd1) (wmul vmul1)
                  (wbasis vbasis1) (wcoord vcoord1) (wp-listp vp-listp1) (wlc vlc1)
                  (lt lt11)
                  (injective injective11) (injective-witness injective11-witness)
                  (preimage preimage11) (preimage-witness preimage11-witness)
                  (surjective surjective11) (surjective-witness surjective11-witness)
                  (dim-v dim-v1) (dim-w dim-v1))))
          (constraint-hint-11 id clause)))

(defthm injective11-holds (injective11))

;; MAIN, instantiated: injective with equal dimensions, hence surjective.
(defthm surjective11-holds
  (surjective11)
  :hints (("Goal" :use (main-instance-1-to-1 injective11-holds)
           :in-theory (disable injective11 surjective11))))
