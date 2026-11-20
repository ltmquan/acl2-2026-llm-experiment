(in-package "ACL2")
(include-book "defs")
(local (include-book "nonstd/integrals/ftc-2" :dir :system))
(local (include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/sin-cos-minimal" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (defun cosr (x) (acl2-cosine (realfix x))))
(local (defun sinr (x) (acl2-sine (realfix x))))
(local (defun map-cosr (p) (if (consp p) (cons (cosr (car p)) (map-cosr (cdr p))) nil)))
(local (defun riemann-cosr (p) (dotprod (deltas p) (map-cosr (cdr p)))))

(local
 (defthm map-cosr-is-map-cos
   (implies (real-listp p) (equal (map-cosr p) (map-cos p)))))

(local
 (defthm partitionp-real-listp
   (implies (partitionp p) (real-listp p))))

(local
 (defthm riemann-cosr-is-riemann-cos
   (implies (partitionp p) (equal (riemann-cosr p) (riemann-cos p)))
   :hints (("Goal" :use ((:instance partitionp-real-listp))
            :in-theory (disable partitionp-real-listp)))))

(local
 (defthm inside-interval-univ
   (equal (inside-interval-p x (interval nil nil)) (realp x))
   :hints (("Goal" :in-theory (enable interval-definition-theory)))))

(local
 (defthm limited-riemann-cosr
   (implies (and (realp a) (standardp a)
                 (realp b) (standardp b)
                 (< a b))
            (i-limited (riemann-cosr (make-small-partition a b))))
   :hints (("Goal"
            :use ((:functional-instance limited-riemann-rcfn-small-partition
                                        (rcfn-domain (lambda () (interval nil nil)))
                                        (rcfn cosr)
                                        (map-rcfn map-cosr)
                                        (riemann-rcfn riemann-cosr)))
            :in-theory (disable riemann-cosr-is-riemann-cos)))))

(local
 (defthm limited-riemann-cos
   (implies (and (realp a) (standardp a)
                 (realp b) (standardp b)
                 (< a b))
            (i-limited (riemann-cos (make-small-partition a b))))
   :hints (("Goal" :use ((:instance limited-riemann-cosr)
                         (:instance riemann-cosr-is-riemann-cos (p (make-small-partition a b))))
            :in-theory (disable limited-riemann-cosr riemann-cosr-is-riemann-cos riemann-cos riemann-cosr)))))

(local (in-theory (disable riemann-cos)))

(defun-std strict-int-cos (a b)
  (if (and (realp a) (realp b) (< a b))
      (standard-part (riemann-cos (make-small-partition a b)))
    0))

(local (in-theory (enable riemann-cos)))

(defun int-cos (a b) (if (<= a b) (strict-int-cos a b) (- (strict-int-cos b a))))

(local
 (defthm sinr-derivative-1
   (implies (and (standardp x) (realp x) (realp x1) (i-close x x1) (not (equal x x1)))
            (i-close (/ (- (sinr x) (sinr x1)) (- x x1)) (cosr x)))
   :hints (("Goal" :use ((:instance acl2-sine-derivative (x x) (y x1)))
            :in-theory (disable acl2-sine-derivative)))
   :rule-classes nil))

(local
 (defthm sinr-derivative
   (implies (and (standardp x) (realp x) (realp x1) (i-close x x1) (not (equal x x1)))
            (i-close (+ (* (sinr x) (/ (+ x (- x1)))) (- (* (sinr x1) (/ (+ x (- x1))))))
                     (cosr x)))
   :hints (("Goal" :use ((:instance sinr-derivative-1))
            :in-theory (disable sinr cosr)))))

(local
 (defthm cosr-continuous
   (implies (and (standardp x) (realp x) (realp x1) (i-close x x1))
            (i-close (cosr x) (cosr x1)))
   :hints (("Goal" :use ((:instance cosine-continuous (x x) (y x1)))
            :in-theory (disable cosine-continuous)))))

(local (defthm realp-sinr (realp (sinr x)) :rule-classes (:rewrite :type-prescription)))
(local (defthm realp-cosr (realp (cosr x)) :rule-classes (:rewrite :type-prescription)))

(local (in-theory (disable sinr cosr)))

(local
 (defthm ftc-cos
   (implies (and (realp a) (realp b))
            (equal (int-cos a b) (- (sinr b) (sinr a))))
   :hints (("Goal"
            :use ((:functional-instance ftc-2
                                        (rcdfn-domain (lambda () (interval nil nil)))
                                        (rcdfn sinr)
                                        (rcdfn-prime cosr)
                                        (map-rcdfn-prime map-cosr)
                                        (riemann-rcdfn-prime riemann-cosr)
                                        (strict-int-rcdfn-prime strict-int-cos)
                                        (int-rcdfn-prime int-cos)))
            :in-theory (enable interval-definition-theory))
           )))

;;;; ---------------- cos^2 ----------------

(local (defun fsq (x) (+ (* 1/2 (realfix x)) (* 1/4 (acl2-sine (* 2 (realfix x)))))))
(local (defun cossqr (x) (expt (acl2-cosine (realfix x)) 2)))
(local (defun map-cossqr (p) (if (consp p) (cons (cossqr (car p)) (map-cossqr (cdr p))) nil)))
(local (defun riemann-cossqr (p) (dotprod (deltas p) (map-cossqr (cdr p)))))

(local
 (defthm map-cossqr-is-map-cos-sq
   (implies (real-listp p) (equal (map-cossqr p) (map-cos-sq p)))))

(local
 (defthm riemann-cossqr-is-riemann-cos-sq
   (implies (partitionp p) (equal (riemann-cossqr p) (riemann-cos-sq p)))
   :hints (("Goal" :use ((:instance partitionp-real-listp))
            :in-theory (disable partitionp-real-listp)))))

(local (defthm realp-fsq (realp (fsq x)) :rule-classes (:rewrite :type-prescription)))
(local (defthm realp-cossqr (realp (cossqr x)) :rule-classes (:rewrite :type-prescription)))

(local
 (defthm close-times-standard
   (implies (and (i-close c d) (standardp c) (acl2-numberp c) (acl2-numberp d))
            (i-close (* c c) (* d d)))
   :hints (("Goal"
            :use ((:instance i-close-limited (x c) (y d))
                  (:instance limited*small->small (x (+ c d)) (y (- c d))))
            :in-theory (e/d (i-close) (i-close-limited limited*small->small))))))

(local
 (defthm cossqr-continuous
   (implies (and (standardp x) (realp x) (realp x1) (i-close x x1))
            (i-close (cossqr x) (cossqr x1)))
   :hints (("Goal" :use ((:instance cosine-continuous (x x) (y x1))
                         (:instance close-times-standard (c (acl2-cosine x)) (d (acl2-cosine x1))))
            :in-theory (disable cosine-continuous close-times-standard)))))

(local
 (defthm close-affine-half
   (implies (and (i-close u v) (acl2-numberp u) (acl2-numberp v))
            (i-close (+ 1/2 (* 1/2 u)) (+ 1/2 (* 1/2 v))))
   :hints (("Goal" :use ((:instance limited*small->small (x 1/2) (y (- u v))))
            :in-theory (e/d (i-close) (limited*small->small))))))

(local
 (defthm i-close-2x
   (implies (i-close x x1) (i-close (* 2 x) (* 2 x1)))
   :hints (("Goal" :use ((:instance limited*small->small (x 2) (y (- x x1))))
            :in-theory (e/d (i-close) (limited*small->small))))))

(local
 (defthm alg-d
   (implies (and (realp d) (not (equal d 0)) (realp q))
            (equal (/ (+ (* 1/2 d) (* 1/4 q)) d) (+ 1/2 (* 1/2 (/ q (* 2 d))))))
   :rule-classes nil))

(local
 (defthmd alg-n1
  (equal (- (+ (* 1/2 x) (* 1/4 s1)) (+ (* 1/2 x1) (* 1/4 s2)))
         (+ (* 1/2 (- x x1)) (* 1/4 (- s1 s2))))))

(local
 (defthmd alg-n2
  (equal (- (* 2 x) (* 2 x1)) (* 2 (- x x1)))))

(local
 (defthm alg-n3
  (implies (and (realp x) (realp x1) (not (equal x x1)))
           (and (realp (- x x1)) (not (equal (- x x1) 0))))
  :rule-classes nil))

(local
 (defthm fsq-quotient-alg
   (implies (and (realp x) (realp x1) (not (equal x x1)) (realp s1) (realp s2))
            (equal (/ (- (+ (* 1/2 x) (* 1/4 s1)) (+ (* 1/2 x1) (* 1/4 s2))) (- x x1))
                   (+ 1/2 (* 1/2 (/ (- s1 s2) (- (* 2 x) (* 2 x1)))))))
   :hints (("Goal" :use ((:instance alg-d (d (- x x1)) (q (- s1 s2))) alg-n3)
                   :in-theory (union-theories '(alg-n1 alg-n2) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fsq-quotient
   (implies (and (realp x) (realp x1) (not (equal x x1)))
            (equal (/ (- (fsq x) (fsq x1)) (- x x1))
                   (+ 1/2 (* 1/2 (/ (- (acl2-sine (* 2 x)) (acl2-sine (* 2 x1)))
                                    (- (* 2 x) (* 2 x1)))))))
   :hints (("Goal" :use ((:instance fsq-quotient-alg (s1 (acl2-sine (* 2 x))) (s2 (acl2-sine (* 2 x1)))))
            :in-theory (disable sine-2x cosine-2x)))))

(local
 (defthm cossqr-half
   (implies (realp x)
            (equal (cossqr x) (+ 1/2 (* 1/2 (acl2-cosine (* 2 x))))))
   :hints (("Goal" :use ((:instance sin**2+cos**2 (x x)))
            :in-theory (disable sin**2+cos**2 sine-2x)))))

(local
 (defthm fsq-derivative-1
   (implies (and (standardp x) (realp x) (realp x1) (i-close x x1) (not (equal x x1)))
            (i-close (/ (- (fsq x) (fsq x1)) (- x x1)) (cossqr x)))
   :hints (("Goal" :use ((:instance acl2-sine-derivative (x (* 2 x)) (y (* 2 x1)))
                         (:instance close-affine-half
                                    (u (/ (- (acl2-sine (* 2 x)) (acl2-sine (* 2 x1))) (- (* 2 x) (* 2 x1))))
                                    (v (acl2-cosine (* 2 x)))))
            :in-theory (disable acl2-sine-derivative close-affine-half fsq cossqr sine-2x cosine-2x
                                distributivity)))
   :rule-classes nil))

(local (in-theory (disable fsq cossqr cossqr-half fsq-quotient)))

(local
 (defthm fsq-derivative
   (implies (and (standardp x) (realp x) (realp x1) (i-close x x1) (not (equal x x1)))
            (i-close (+ (* (fsq x) (/ (+ x (- x1)))) (- (* (fsq x1) (/ (+ x (- x1))))))
                     (cossqr x)))
   :hints (("Goal" :use ((:instance fsq-derivative-1))))))

(local
 (defthm limited-riemann-cossqr
   (implies (and (realp a) (standardp a)
                 (realp b) (standardp b)
                 (< a b))
            (i-limited (riemann-cossqr (make-small-partition a b))))
   :hints (("Goal"
            :use ((:functional-instance limited-riemann-rcfn-small-partition
                                        (rcfn-domain (lambda () (interval nil nil)))
                                        (rcfn cossqr)
                                        (map-rcfn map-cossqr)
                                        (riemann-rcfn riemann-cossqr)))
            :in-theory (disable riemann-cossqr-is-riemann-cos-sq cossqr-half)))))

(local
 (defthm limited-riemann-cos-sq
   (implies (and (realp a) (standardp a)
                 (realp b) (standardp b)
                 (< a b))
            (i-limited (riemann-cos-sq (make-small-partition a b))))
   :hints (("Goal" :use ((:instance limited-riemann-cossqr)
                         (:instance riemann-cossqr-is-riemann-cos-sq (p (make-small-partition a b))))
            :in-theory (disable limited-riemann-cossqr riemann-cossqr-is-riemann-cos-sq
                                riemann-cos-sq riemann-cossqr)))))

(local (in-theory (disable riemann-cos-sq)))

(defun-std strict-int-cos-sq (a b)
  (if (and (realp a) (realp b) (< a b))
      (standard-part (riemann-cos-sq (make-small-partition a b)))
    0))

(local (in-theory (enable riemann-cos-sq)))

(defun int-cos-sq (a b) (if (<= a b) (strict-int-cos-sq a b) (- (strict-int-cos-sq b a))))

(local
 (defthm ftc-cos-sq
   (implies (and (realp a) (realp b))
            (equal (int-cos-sq a b) (- (fsq b) (fsq a))))
   :hints (("Goal"
            :use ((:functional-instance ftc-2
                                        (rcdfn-domain (lambda () (interval nil nil)))
                                        (rcdfn fsq)
                                        (rcdfn-prime cossqr)
                                        (map-rcdfn-prime map-cossqr)
                                        (riemann-rcdfn-prime riemann-cossqr)
                                        (strict-int-rcdfn-prime strict-int-cos-sq)
                                        (int-rcdfn-prime int-cos-sq)))
            :in-theory (enable interval-definition-theory)))))

;;;; ---------------- algebra ----------------

(local (in-theory (disable sine-2x cosine-2x)))

(local
 (defthm sin-sum-diff
  (implies (and (realp a) (realp h))
           (equal (- (acl2-sine (+ a h)) (acl2-sine (+ a (- h))))
                  (* 2 (acl2-cosine a) (acl2-sine h))))
  :hints (("Goal" :use ((:instance sine-of-sums (x a) (y h))
                        (:instance sine-of-sums (x a) (y (- h))))
           :in-theory (disable sine-of-sums)))))

(local
 (defthm-std sqrt-negative
  (implies (and (realp x) (< x 0))
           (equal (acl2-sqrt x) 0))
  :hints (("Goal" :in-theory (enable acl2-sqrt sqrt-iter)))))

(local
 (defthm sqrt-*-general
  (implies (and (realp x) (<= 0 x) (realp y))
           (equal (acl2-sqrt (* x y)) (* (acl2-sqrt x) (acl2-sqrt y))))
  :hints (("Goal" :cases ((<= 0 y) (equal x 0)))
          ("Subgoal 2" :use ((:instance sqrt-negative (x (* x y)))
                             (:instance sqrt-negative (x y)))))))

(defun vdc-integral (vm tt alpha)
  (* vm (/ tt) (int-cos (- alpha (/ tt 2)) (+ alpha (/ tt 2)))))

(defun vrms-integral (vm tt alpha)
  (acl2-sqrt (* (expt vm 2) (/ tt) (int-cos-sq (- alpha (/ tt 2)) (+ alpha (/ tt 2))))))

(local
 (defthm int-cos-window
   (implies (and (realp alpha) (realp h))
            (equal (int-cos (- alpha h) (+ alpha h))
                   (* 2 (acl2-cosine alpha) (acl2-sine h))))
   :hints (("Goal" :use ((:instance ftc-cos (a (- alpha h)) (b (+ alpha h)))
                         (:instance sin-sum-diff (a alpha) (h h)))
            :in-theory (e/d (sinr) (ftc-cos sin-sum-diff int-cos))))))

(local
 (defthm int-cos-sq-window
   (implies (and (realp alpha) (realp h))
            (equal (int-cos-sq (- alpha h) (+ alpha h))
                   (+ h (* 1/2 (acl2-cosine (* 2 alpha)) (acl2-sine (* 2 h))))))
   :hints (("Goal" :use ((:instance ftc-cos-sq (a (- alpha h)) (b (+ alpha h)))
                         (:instance sin-sum-diff (a (* 2 alpha)) (h (* 2 h))))
            :in-theory (e/d (fsq) (ftc-cos-sq sin-sum-diff int-cos-sq))))))

(local (in-theory (disable int-cos int-cos-sq)))

(defthm master-theorem-vdc
  (implies (and (realp vm) (realp tt) (< 0 tt) (realp alpha))
           (equal (vdc-integral vm tt alpha) (* vm (sa (/ tt 2)) (acl2-cosine alpha))))
  :hints (("Goal" :use ((:instance int-cos-window (h (/ tt 2))))
           :in-theory (disable int-cos-window))))

(local
 (defthm vrms-arg
   (implies (and (realp vm) (realp tt) (< 0 tt) (realp alpha))
            (equal (* (expt vm 2) (/ tt) (int-cos-sq (- alpha (/ tt 2)) (+ alpha (/ tt 2))))
                   (* (* vm vm (/ 2)) (+ 1 (* (sa tt) (acl2-cosine (* 2 alpha)))))))
   :hints (("Goal" :use ((:instance int-cos-sq-window (h (/ tt 2))))
            :in-theory (disable int-cos-sq-window)))))

(local
 (defthm sqrt-vm-half-aux
   (implies (and (realp r) (< 0 r) (equal (* r r) 2) (realp vm))
            (equal (* (/ vm r) (/ vm r)) (* vm vm (/ 2))))
   :rule-classes nil))

(local
 (defthm sqrt-vm-half
   (implies (and (realp vm) (<= 0 vm))
            (equal (acl2-sqrt (* vm vm (/ 2))) (/ vm (acl2-sqrt 2))))
   :hints (("Goal" :use ((:instance y*y=x->y=sqrt-x (x (* vm vm (/ 2))) (y (/ vm (acl2-sqrt 2))))
                         (:instance sqrt-sqrt (x 2))
                         (:instance y-<-sqrt (x 2) (y 1))
                         (:instance sqrt-vm-half-aux (r (acl2-sqrt 2))))
            :in-theory (disable y*y=x->y=sqrt-x sqrt-sqrt y-<-sqrt sqrt-*-general sqrt-* y-=-sqrt sqrt-=-y)))))

(local
 (defthm realp-sa
   (implies (realp x) (realp (sa x)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm vm-half-nonneg
   (implies (and (realp vm) (<= 0 vm))
            (and (realp (* vm vm (/ 2))) (<= 0 (* vm vm (/ 2)))))))

(local
 (defthm vrms-step-1
   (implies (and (realp vm) (realp tt) (< 0 tt) (realp alpha))
            (equal (vrms-integral vm tt alpha)
                   (acl2-sqrt (* (* vm vm (/ 2)) (+ 1 (* (sa tt) (acl2-cosine (* 2 alpha))))))))
   :hints (("Goal" :in-theory (union-theories '(vrms-integral vrms-arg) (theory 'minimal-theory))))))

(local
 (defthm realp-y-term
   (implies (and (realp tt) (realp alpha))
            (realp (+ 1 (* (sa tt) (acl2-cosine (* 2 alpha))))))
   :hints (("Goal" :in-theory (disable sa)))))

(defthm master-theorem-vrms
  (implies (and (realp vm) (<= 0 vm) (realp tt) (< 0 tt) (realp alpha))
           (equal (vrms-integral vm tt alpha)
                  (* (/ vm (acl2-sqrt 2))
                     (acl2-sqrt (+ 1 (* (sa tt) (acl2-cosine (* 2 alpha))))))))
  :hints (("Goal" :use ((:instance vrms-step-1)
                        (:instance sqrt-*-general (x (* vm vm (/ 2)))
                                   (y (+ 1 (* (sa tt) (acl2-cosine (* 2 alpha))))))
                        (:instance sqrt-vm-half)
                        (:instance vm-half-nonneg)
                        (:instance realp-y-term))
           :in-theory (theory 'minimal-theory))))

;;;; ---------------- special values ----------------

(local
 (defthm sin-pi-x-gen
   (implies (equal y (+ (acl2-pi) (- x)))
            (equal (acl2-sine y) (acl2-sine x)))
   :rule-classes nil))

(local
 (defthm sin-2pi/3
   (equal (acl2-sine (* 2/3 (acl2-pi))) (* 1/2 (acl2-sqrt 3)))
   :hints (("Goal" :use ((:instance sin-pi-x-gen (y (* 2/3 (acl2-pi))) (x (* 1/3 (acl2-pi)))))))))

(local
 (defthm sa-pi/3
   (equal (sa (* 1/3 (acl2-pi))) (/ (* 3 (acl2-sqrt 3)) (* 2 (acl2-pi))))))

(local
 (defthm sa-2pi/3
   (equal (sa (* 2/3 (acl2-pi))) (/ (* 3 (acl2-sqrt 3)) (* 4 (acl2-pi))))))

(local
 (defthm sa-pi/6
   (equal (sa (* 1/6 (acl2-pi))) (/ 3 (acl2-pi)))))

(local (in-theory (disable sa vdc-integral vrms-integral)))

(defthm three-phase-midpoint-row
  (implies (and (realp vmax) (<= 0 vmax) (realp alpha))
           (and (equal (vdc-integral vmax (* 2/3 (acl2-pi)) alpha)
                       (* (/ (* 3 (acl2-sqrt 3)) (* 2 (acl2-pi))) vmax (acl2-cosine alpha)))
                (equal (vrms-integral vmax (* 2/3 (acl2-pi)) alpha)
                       (* (/ vmax (acl2-sqrt 2))
                          (acl2-sqrt (+ 1 (* (/ (* 3 (acl2-sqrt 3)) (* 4 (acl2-pi)))
                                             (acl2-cosine (* 2 alpha)))))))))
  :hints (("Goal" :use ((:instance master-theorem-vdc (vm vmax) (tt (* 2/3 (acl2-pi))))
                        (:instance master-theorem-vrms (vm vmax) (tt (* 2/3 (acl2-pi)))))
           :in-theory (disable master-theorem-vdc master-theorem-vrms))))

(defthm three-phase-bridge-row
  (implies (and (realp vmax) (<= 0 vmax) (realp alpha))
           (and (equal (vdc-integral (* (acl2-sqrt 3) vmax) (* 1/3 (acl2-pi)) alpha)
                       (* (/ (* 3 (acl2-sqrt 3)) (acl2-pi)) vmax (acl2-cosine alpha)))
                (equal (vrms-integral (* (acl2-sqrt 3) vmax) (* 1/3 (acl2-pi)) alpha)
                       (* (/ (* (acl2-sqrt 3) vmax) (acl2-sqrt 2))
                          (acl2-sqrt (+ 1 (* (/ (* 3 (acl2-sqrt 3)) (* 2 (acl2-pi)))
                                             (acl2-cosine (* 2 alpha)))))))))
  :hints (("Goal" :use ((:instance master-theorem-vdc (vm (* (acl2-sqrt 3) vmax)) (tt (* 1/3 (acl2-pi))))
                        (:instance master-theorem-vrms (vm (* (acl2-sqrt 3) vmax)) (tt (* 1/3 (acl2-pi))))
                        (:instance y-<-sqrt (x 3) (y 0)))
           :in-theory (disable master-theorem-vdc master-theorem-vrms y-<-sqrt))))
