(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)

(include-book "nonstd/nsa/trig" :dir :system)

(skip-proofs
(defun cplxp (z)
  (declare (xargs :guard t))
  (and (consp z) (acl2-numberp (car z)) (acl2-numberp (cdr z)))))

(skip-proofs
(defun cplx (re im)
  (declare (xargs :guard (and (acl2-numberp re) (acl2-numberp im))))
  (cons re im)))

(skip-proofs
(defun re (z) (declare (xargs :guard (consp z))) (car z)))

(skip-proofs
(defun imz (z) (declare (xargs :guard (consp z))) (cdr z)))

(skip-proofs
(defun cconj (z)
  (declare (xargs :guard (cplxp z)))
  (cplx (re z) (- (imz z)))))

(skip-proofs
(defun cadd (z w)
  (declare (xargs :guard (and (cplxp z) (cplxp w))))
  (cplx (+ (re z) (re w)) (+ (imz z) (imz w)))))

(skip-proofs
(defun cscale (k z)
  (declare (xargs :guard (and (acl2-numberp k) (cplxp z))))
  (cplx (* k (re z)) (* k (imz z)))))

(skip-proofs
(defun cmul (z w)
  (declare (xargs :guard (and (cplxp z) (cplxp w))))
  (cplx (- (* (re z) (re w)) (* (imz z) (imz w)))
        (+ (* (re z) (imz w)) (* (imz z) (re w))))))

(skip-proofs
(defun dotp (z w)
  (declare (xargs :guard (and (cplxp z) (cplxp w))))
  (+ (* (re z) (re w)) (* (imz z) (imz w)))))

(skip-proofs
(defun crossp (z w)
  (declare (xargs :guard (and (cplxp z) (cplxp w))))
  (- (* (imz z) (re w)) (* (re z) (imz w)))))

(skip-proofs
(encapsulate
 (((cosine *) => *) ((sine *) => *))
 (local (defun cosine (x) (declare (ignore x)) 1))
 (local (defun sine (x) (declare (ignore x)) 0))
 (defthm pythagorean-cos-sin
   (equal (+ (* (cosine x) (cosine x)) (* (sine x) (sine x))) 1))
 (defthm cosine-even
   (equal (cosine (- x)) (cosine x)))
 (defthm sine-odd
   (equal (sine (- x)) (- (sine x))))
 (defthm cosine-difference
   (equal (cosine (- x y))
          (+ (* (cosine x) (cosine y)) (* (sine x) (sine y)))))
 (defthm sine-difference
   (equal (sine (- x y))
          (- (* (sine x) (cosine y)) (* (cosine x) (sine y)))))
 (defthm acl2-numberp-cosine (acl2-numberp (cosine x)))
 (defthm acl2-numberp-sine (acl2-numberp (sine x)))))

(skip-proofs
(defun eiz (theta)
  (declare (xargs :guard t))
  (cplx (cosine theta) (sine theta))))

(skip-proofs
(defun e0 () (declare (xargs :guard t)) (cplx 1 0)))

(skip-proofs
(defun e1 (s3)
  (declare (xargs :guard (acl2-numberp s3)))
  (cplx (- (/ 1 2)) (/ s3 2))))

(skip-proofs
(defun e2 (s3)
  (declare (xargs :guard (acl2-numberp s3)))
  (cplx (- (/ 1 2)) (- (/ s3 2)))))

(skip-proofs
(defun torque-W (i-s i-r eps)
  (declare (xargs :guard (and (cplxp i-s) (cplxp i-r))))
  (cmul i-s (cconj (cmul i-r (eiz eps))))))

(skip-proofs
(defun g-cplxp (u)
  (declare (xargs :guard t))
  (and (consp u) (acl2-numberp (car u)) (acl2-numberp (cdr u)))))

(skip-proofs
(defun g-re (u) (declare (xargs :guard (consp u))) (car u)))

(skip-proofs
(defun g-im (u) (declare (xargs :guard (consp u))) (cdr u)))

(skip-proofs
(defun g-cplx (a b)
  (declare (xargs :guard (and (acl2-numberp a) (acl2-numberp b))))
  (cons a b)))

(skip-proofs
(defun g-realpairp (u)
  (declare (xargs :guard t))
  (and (consp u) (realp (g-re u)) (realp (g-im u)))))

(skip-proofs
(defun g-c+ (u v)
  (declare (xargs :guard (and (g-cplxp u) (g-cplxp v))))
  (g-cplx (+ (g-re u) (g-re v)) (+ (g-im u) (g-im v)))))

(skip-proofs
(defun g-cscale (k u)
  (declare (xargs :guard (and (acl2-numberp k) (g-cplxp u))))
  (g-cplx (* k (g-re u)) (* k (g-im u)))))

(skip-proofs
(defun g-c* (u v)
  (declare (xargs :guard (and (g-cplxp u) (g-cplxp v))))
  (g-cplx (- (* (g-re u) (g-re v)) (* (g-im u) (g-im v)))
          (+ (* (g-re u) (g-im v)) (* (g-im u) (g-re v))))))

(skip-proofs
(defun g-vdot (u v)
  (declare (xargs :guard (and (g-cplxp u) (g-cplxp v))))
  (+ (* (g-re u) (g-re v)) (* (g-im u) (g-im v)))))

(skip-proofs
(defun g-omega-pow (omega n)
  (declare (xargs :guard (and (g-cplxp omega) (natp n))
                  :verify-guards nil))
  (if (zp n) (g-cplx 1 0) (g-c* omega (g-omega-pow omega (1- n))))))

(skip-proofs
(verify-guards g-omega-pow))

(skip-proofs
(defun g-collapse-sum (A omega)
  (declare (xargs :guard (and (g-cplxp A) (g-cplxp omega))))
  (g-c+ (g-cscale (* 2/3 (g-vdot A (g-omega-pow omega 0))) (g-omega-pow omega 0))
        (g-c+ (g-cscale (* 2/3 (g-vdot A (g-omega-pow omega 1))) (g-omega-pow omega 1))
              (g-cscale (* 2/3 (g-vdot A (g-omega-pow omega 2))) (g-omega-pow omega 2))))))

(skip-proofs
(defun g-gamma-val () (* 2/3 (acl2-pi))))

(skip-proofs
(defun g-omega-real () (g-cplx (acl2-cosine (g-gamma-val)) (acl2-sine (g-gamma-val)))))
