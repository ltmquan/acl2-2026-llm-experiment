(in-package "ACL2")

;; Integral of cos(x - m*gamma) * cos(x - n*gamma) over [0, 2*pi], gamma = 2*pi/3.
;;
;; Proof outline:
;;   cos(x-a)cos(x-b) = 1/2 cos(a-b) + 1/2 cos(a+b) cos(2x) + 1/2 sin(a+b) sin(2x).
;;   The Riemann sums of cos(2x) and sin(2x) over [0,2pi] with infinitesimal
;;   mesh are infinitesimal, by the fundamental theorem of calculus (ftc-2)
;;   applied to the antiderivatives sin(2x)/2 and -cos(2x)/2.  The coefficients
;;   cos(a+b), sin(a+b) are bounded, hence limited, so the Riemann sum of the
;;   integrand is infinitely close to 1/2 cos(a-b) * 2pi = pi cos((m-n) gamma).
;;   The definite integral follows by transfer (defthm-std).
(include-book "defs")
(include-book "nonstd/integrals/ftc-2" :dir :system)
(local (include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/sin-cos-minimal" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(defun trig-domain () (interval nil nil))

(defthmd inside-trig-domain
  (equal (inside-interval-p x (trig-domain)) (realp x))
  :hints (("Goal" :in-theory (enable inside-interval-p))))

(defthmd inside-trig-domain-literal
  (equal (inside-interval-p x '(nil)) (realp x))
  :hints (("Goal" :in-theory (enable inside-interval-p))))

(defun cos2 (x) (if (realp x) (acl2-cosine (* 2 x)) 0))
(defun sin2 (x) (if (realp x) (acl2-sine (* 2 x)) 0))
(defun half-sin2 (x) (* 1/2 (sin2 x)))
(defun neg-half-cos2 (x) (* -1/2 (cos2 x)))

(defthm realp-cos2 (realp (cos2 x)) :rule-classes (:rewrite :type-prescription))
(defthm realp-sin2 (realp (sin2 x)) :rule-classes (:rewrite :type-prescription))

(defun map-cos2 (p)
  (if (consp p) (cons (cos2 (car p)) (map-cos2 (cdr p))) nil))
(defun riemann-cos2 (p) (dotprod (deltas p) (map-cos2 (cdr p))))
(defun map-sin2 (p)
  (if (consp p) (cons (sin2 (car p)) (map-sin2 (cdr p))) nil))
(defun riemann-sin2 (p) (dotprod (deltas p) (map-sin2 (cdr p))))

(defthm-std standardp-acl2-pi (standardp (acl2-pi)))

(local (in-theory (disable sine-2x cosine-2x sine-of-sums cosine-of-sums)))
;; continuity
(defthm i-close-times-2
  (implies (and (acl2-numberp x) (acl2-numberp y) (i-close x y))
           (i-close (* 2 x) (* 2 y)))
  :hints (("Goal" :in-theory (enable i-close)
           :use ((:instance limited*small->small (x 2) (y (- x y)))))))

(defthm cos2-continuous
  (implies (and (standardp x) (realp x) (i-close x y) (realp y))
           (i-close (cos2 x) (cos2 y)))
  :hints (("Goal" :use ((:instance cosine-continuous (x (* 2 x)) (y (* 2 y)))
                        (:instance i-close-times-2))
           :in-theory (disable cosine-continuous))))

(defthm sin2-continuous
  (implies (and (standardp x) (realp x) (i-close x y) (realp y))
           (i-close (sin2 x) (sin2 y)))
  :hints (("Goal" :use ((:instance sine-continuous (x (* 2 x)) (y (* 2 y)))
                        (:instance i-close-times-2))
           :in-theory (disable sine-continuous))))

(defthm i-close-times-half
  (implies (and (acl2-numberp x) (acl2-numberp y) (i-close x y))
           (i-close (* 1/2 x) (* 1/2 y)))
  :hints (("Goal" :in-theory (enable i-close)
           :use ((:instance limited*small->small (x 1/2) (y (- x y)))))))

(defthm i-close-negate
  (implies (and (acl2-numberp x) (acl2-numberp y) (i-close x y))
           (i-close (- x) (- y)))
  :hints (("Goal" :in-theory (enable i-close)
           :use ((:instance i-small-uminus (x (- x y)))))))

(defthmd q-half
  (implies (and (acl2-numberp d) (not (equal d 0)))
           (equal (/ (- (* 1/2 a) (* 1/2 b)) d) (* (- a b) (/ (* 2 d))))))

(defthmd q-neg-half
  (implies (and (acl2-numberp d) (not (equal d 0)))
           (equal (/ (- (* -1/2 a) (* -1/2 b)) d) (- (* (- a b) (/ (* 2 d)))))))

(defthmd two-diff (equal (+ (* 2 x) (- (* 2 y))) (* 2 (+ x (- y)))))

(defthmd quotient-scale-half
  (implies (and (acl2-numberp x) (acl2-numberp y) (not (equal x y)))
           (equal (/ (- (* 1/2 a) (* 1/2 b)) (- x y))
                  (/ (- a b) (- (* 2 x) (* 2 y)))))
  :hints (("Goal" :use ((:instance q-half (d (- x y)))
                        (:instance two-diff))
           :in-theory (disable distributivity))))

(defthmd quotient-scale-neg-half
  (implies (and (acl2-numberp x) (acl2-numberp y) (not (equal x y)))
           (equal (/ (- (* -1/2 a) (* -1/2 b)) (- x y))
                  (- (/ (- a b) (- (* 2 x) (* 2 y))))))
  :hints (("Goal" :use ((:instance q-neg-half (d (- x y)))
                        (:instance two-diff))
           :in-theory (disable distributivity))))

(defthm half-sin2-derivative
  (implies (and (standardp x) (realp x) (realp x1)
                (i-close x x1) (not (= x x1)))
           (i-close (/ (- (half-sin2 x) (half-sin2 x1)) (- x x1))
                    (cos2 x)))
  :hints (("Goal" :use ((:instance acl2-sine-derivative (x (* 2 x)) (y (* 2 x1)))
                        (:instance i-close-times-2 (x x) (y x1))
                        (:instance quotient-scale-half (y x1)
                                   (a (acl2-sine (* 2 x))) (b (acl2-sine (* 2 x1)))))
           :in-theory (disable acl2-sine-derivative i-close-times-2))))

(defthm neg-half-cos2-derivative
  (implies (and (standardp x) (realp x) (realp x1)
                (i-close x x1) (not (= x x1)))
           (i-close (/ (- (neg-half-cos2 x) (neg-half-cos2 x1)) (- x x1))
                    (sin2 x)))
  :hints (("Goal" :use ((:instance acl2-cosine-derivative (x (* 2 x)) (y (* 2 x1)))
                        (:instance i-close-times-2 (x x) (y x1))
                        (:instance quotient-scale-neg-half (y x1)
                                   (a (acl2-cosine (* 2 x))) (b (acl2-cosine (* 2 x1))))
                        (:instance i-close-negate
                                   (x (/ (- (acl2-cosine (* 2 x)) (acl2-cosine (* 2 x1)))
                                         (- (* 2 x) (* 2 x1))))
                                   (y (- (acl2-sine (* 2 x))))))
           :in-theory (disable acl2-cosine-derivative i-close-times-2 i-close-negate))))

;;; ---------------- FTC instance for cos2 ----------------

(encapsulate
 nil
(local
 (defthm limited-riemann-cos2-small-partition
   (implies (and (realp a) (standardp a)
                 (realp b) (standardp b)
                 (inside-interval-p a (trig-domain))
                 (inside-interval-p b (trig-domain))
                 (< a b))
            (i-limited (riemann-cos2 (make-small-partition a b))))
   :hints (("Goal"
            :by (:functional-instance limited-riemann-rcfn-small-partition
                                      (rcfn-domain trig-domain)
                                      (rcfn cos2)
                                      (map-rcfn map-cos2)
                                      (riemann-rcfn riemann-cos2))))))

(local (in-theory (disable riemann-cos2)))
(defun-std strict-int-cos2 (a b)
  (if (and (realp a)
           (realp b)
           (inside-interval-p a (trig-domain))
           (inside-interval-p b (trig-domain))
           (< a b))
      (standard-part (riemann-cos2 (make-small-partition a b)))
    0))
)

(defun int-cos2 (a b)
  (if (<= a b)
      (strict-int-cos2 a b)
    (- (strict-int-cos2 b a))))

(defthm cos2-riemann-close-to-strict-int
  (implies (and (standardp a)
                (standardp b)
                (<= a b)
                (inside-interval-p a (trig-domain))
                (inside-interval-p b (trig-domain))
                (partitionp p)
                (equal (car p) a)
                (equal (car (last p)) b)
                (i-small (mesh p)))
           (i-close (riemann-cos2 p)
                    (strict-int-cos2 a b)))
  :hints (("Goal"
           :by (:functional-instance strict-int-rcdfn-prime-is-integral-of-rcdfn-prime
                                      (rcdfn-domain trig-domain)
                                      (rcdfn half-sin2)
                                      (rcdfn-prime cos2)
                                      (map-rcdfn-prime map-cos2)
                                      (riemann-rcdfn-prime riemann-cos2)
                                      (strict-int-rcdfn-prime strict-int-cos2)))
          ("Subgoal 2" :use ((:instance half-sin2-derivative))
           :in-theory (disable half-sin2-derivative))
          ("Subgoal 1" :use ((:instance cos2-continuous (y x1)))
           :in-theory (disable cos2-continuous))))

(defthm cos2-ftc-2
  (implies (and (inside-interval-p a (trig-domain))
                (inside-interval-p b (trig-domain)))
           (equal (int-cos2 a b)
                  (- (half-sin2 b) (half-sin2 a))))
  :hints (("Goal"
           :by (:functional-instance ftc-2
                                      (rcdfn-domain trig-domain)
                                      (rcdfn half-sin2)
                                      (rcdfn-prime cos2)
                                      (map-rcdfn-prime map-cos2)
                                      (riemann-rcdfn-prime riemann-cos2)
                                      (strict-int-rcdfn-prime strict-int-cos2)
                                      (int-rcdfn-prime int-cos2)))))

;;; ---------------- FTC instance for sin2 ----------------

(encapsulate
 nil
(local
 (defthm limited-riemann-sin2-small-partition
   (implies (and (realp a) (standardp a)
                 (realp b) (standardp b)
                 (inside-interval-p a (trig-domain))
                 (inside-interval-p b (trig-domain))
                 (< a b))
            (i-limited (riemann-sin2 (make-small-partition a b))))
   :hints (("Goal"
            :by (:functional-instance limited-riemann-rcfn-small-partition
                                      (rcfn-domain trig-domain)
                                      (rcfn sin2)
                                      (map-rcfn map-sin2)
                                      (riemann-rcfn riemann-sin2))))))

(local (in-theory (disable riemann-sin2)))
(defun-std strict-int-sin2 (a b)
  (if (and (realp a)
           (realp b)
           (inside-interval-p a (trig-domain))
           (inside-interval-p b (trig-domain))
           (< a b))
      (standard-part (riemann-sin2 (make-small-partition a b)))
    0))
)

(defun int-sin2 (a b)
  (if (<= a b)
      (strict-int-sin2 a b)
    (- (strict-int-sin2 b a))))

(defthm sin2-riemann-close-to-strict-int
  (implies (and (standardp a)
                (standardp b)
                (<= a b)
                (inside-interval-p a (trig-domain))
                (inside-interval-p b (trig-domain))
                (partitionp p)
                (equal (car p) a)
                (equal (car (last p)) b)
                (i-small (mesh p)))
           (i-close (riemann-sin2 p)
                    (strict-int-sin2 a b)))
  :hints (("Goal"
           :by (:functional-instance strict-int-rcdfn-prime-is-integral-of-rcdfn-prime
                                      (rcdfn-domain trig-domain)
                                      (rcdfn neg-half-cos2)
                                      (rcdfn-prime sin2)
                                      (map-rcdfn-prime map-sin2)
                                      (riemann-rcdfn-prime riemann-sin2)
                                      (strict-int-rcdfn-prime strict-int-sin2)))
          ("Subgoal 2" :use ((:instance neg-half-cos2-derivative))
           :in-theory (disable neg-half-cos2-derivative))
          ("Subgoal 1" :use ((:instance sin2-continuous (y x1)))
           :in-theory (disable sin2-continuous))))

(defthm sin2-ftc-2
  (implies (and (inside-interval-p a (trig-domain))
                (inside-interval-p b (trig-domain)))
           (equal (int-sin2 a b)
                  (- (neg-half-cos2 b) (neg-half-cos2 a))))
  :hints (("Goal"
           :by (:functional-instance ftc-2
                                      (rcdfn-domain trig-domain)
                                      (rcdfn neg-half-cos2)
                                      (rcdfn-prime sin2)
                                      (map-rcdfn-prime map-sin2)
                                      (riemann-rcdfn-prime riemann-sin2)
                                      (strict-int-rcdfn-prime strict-int-sin2)
                                      (int-rcdfn-prime int-sin2)))))

;;; ---------------- values at endpoints ----------------
(defthm sine-0 (equal (acl2-sine 0) 0)
  :hints (("Goal" :use ((:instance sin-uminus (x 0))) :in-theory (disable sin-uminus))))

(defthm sine-4pi (equal (acl2-sine (* 4 (acl2-pi))) 0)
  :hints (("Goal" :use ((:instance sine-2x (x (* 2 (acl2-pi))))))))

(defthm cosine-4pi (equal (acl2-cosine (* 4 (acl2-pi))) 1)
  :hints (("Goal" :use ((:instance cosine-2x (x (* 2 (acl2-pi))))))))


(defthm two-pi-facts
  (and (standardp (* 2 (acl2-pi)))
       (realp (* 2 (acl2-pi)))
       (<= 0 (* 2 (acl2-pi)))
       (inside-interval-p (* 2 (acl2-pi)) (trig-domain))
       )
  :hints (("Goal" :in-theory (enable inside-trig-domain-literal))))

(defthm strict-int-cos2-full-period
  (equal (strict-int-cos2 0 (* 2 (acl2-pi))) 0)
  :hints (("Goal" :use ((:instance cos2-ftc-2 (a 0) (b (* 2 (acl2-pi)))))
           :in-theory (e/d (inside-trig-domain-literal) (cos2-ftc-2 strict-int-cos2)))))

(defthm riemann-cos2-small
  (implies (and (partitionp p)
                (equal (car p) 0)
                (equal (car (last p)) (* 2 (acl2-pi)))
                (i-small (mesh p)))
           (i-small (riemann-cos2 p)))
  :hints (("Goal" :use ((:instance cos2-riemann-close-to-strict-int (a 0) (b (* 2 (acl2-pi)))))
           :in-theory (union-theories (theory (quote minimal-theory)) (quote (i-close strict-int-cos2-full-period i-small-uminus fix two-pi-facts (:executable-counterpart trig-domain) (:executable-counterpart inside-interval-p) inside-trig-domain-literal unicity-of-0 commutativity-of-+))))))

(defthm strict-int-sin2-full-period
  (equal (strict-int-sin2 0 (* 2 (acl2-pi))) 0)
  :hints (("Goal" :use ((:instance sin2-ftc-2 (a 0) (b (* 2 (acl2-pi)))))
           :in-theory (e/d (inside-trig-domain-literal) (sin2-ftc-2 strict-int-sin2)))))

(defthm riemann-sin2-small
  (implies (and (partitionp p)
                (equal (car p) 0)
                (equal (car (last p)) (* 2 (acl2-pi)))
                (i-small (mesh p)))
           (i-small (riemann-sin2 p)))
  :hints (("Goal" :use ((:instance sin2-riemann-close-to-strict-int (a 0) (b (* 2 (acl2-pi)))))
           :in-theory (union-theories (theory (quote minimal-theory)) (quote (i-close strict-int-sin2-full-period i-small-uminus fix two-pi-facts (:executable-counterpart trig-domain) (:executable-counterpart inside-interval-p) inside-trig-domain-literal unicity-of-0 commutativity-of-+))))))

;;; ================= Part 2: the inductance integrand =================

(defthmd cos-product
  (implies (and (acl2-numberp u) (acl2-numberp v))
           (equal (* (acl2-cosine u) (acl2-cosine v))
                  (+ (* 1/2 (acl2-cosine (- u v)))
                     (* 1/2 (acl2-cosine (+ u v))))))
  :hints (("Goal" :use ((:instance cosine-of-sums (x u) (y v))
                        (:instance cosine-of-sums (x u) (y (- v)))))))

(defthmd cos-shift
  (implies (and (acl2-numberp y) (acl2-numberp c))
           (equal (acl2-cosine (- y c))
                  (+ (* (acl2-cosine y) (acl2-cosine c))
                     (* (acl2-sine y) (acl2-sine c)))))
  :hints (("Goal" :use ((:instance cosine-of-sums (x y) (y (- c)))))))

(defthmd plus-x-x (equal (+ x x) (* 2 x)))

(defthmd decomp-generic
  (implies (and (realp x) (acl2-numberp a) (acl2-numberp b))
           (equal (* (acl2-cosine (- x a)) (acl2-cosine (- x b)))
                  (+ (* 1/2 (acl2-cosine (- a b)))
                     (* 1/2 (acl2-cosine (+ a b)) (acl2-cosine (* 2 x)))
                     (* 1/2 (acl2-sine (+ a b)) (acl2-sine (* 2 x))))))
  :hints (("Goal" :use ((:instance cos-product (u (- x a)) (v (- x b)))
                        (:instance cos-shift (y (* 2 x)) (c (+ a b)))
                        (:instance cos-uminus (x (- a b))))
           :in-theory (e/d (plus-x-x) (cos-uminus)))))

(defun kk (m n) (acl2-cosine (* (- m n) (winding-gamma))))
(defun cc (m n) (acl2-cosine (* (+ m n) (winding-gamma))))
(defun ss (m n) (acl2-sine (* (+ m n) (winding-gamma))))

(defthmd integrand-decomp
  (implies (and (realp x) (acl2-numberp m) (acl2-numberp n))
           (equal (inductance-integrand x m n)
                  (+ (* 1/2 (kk m n))
                     (* 1/2 (cc m n) (cos2 x))
                     (* 1/2 (ss m n) (sin2 x)))))
  :hints (("Goal" :use ((:instance decomp-generic
                                   (a (* m (winding-gamma)))
                                   (b (* n (winding-gamma)))))
           :in-theory (disable winding-gamma))))

(defthm sumlist-deltas
  (implies (partitionp p)
           (equal (sumlist (deltas p)) (- (car (last p)) (car p)))))

(defthm riemann-decomp-lemma
  (implies (and (partitionp p) (acl2-numberp m) (acl2-numberp n))
           (equal (dotprod (deltas p) (map-inductance-integrand (cdr p) m n))
                  (+ (* 1/2 (kk m n) (sumlist (deltas p)))
                     (* 1/2 (cc m n) (dotprod (deltas p) (map-cos2 (cdr p))))
                     (* 1/2 (ss m n) (dotprod (deltas p) (map-sin2 (cdr p)))))))
  :hints (("Goal" :in-theory (e/d (integrand-decomp)
                                  (kk cc ss cos2 sin2 inductance-integrand sumlist-deltas)))))

(defthm riemann-decomp
  (implies (and (partitionp p) (acl2-numberp m) (acl2-numberp n))
           (equal (riemann-inductance-integrand p m n)
                  (+ (* 1/2 (kk m n) (- (car (last p)) (car p)))
                     (* 1/2 (cc m n) (riemann-cos2 p))
                     (* 1/2 (ss m n) (riemann-sin2 p)))))
  :hints (("Goal" :in-theory (disable kk cc ss cos2 sin2 inductance-integrand))))

;; bounds on sine and cosine
(defthm cosine-bounds
  (implies (realp x)
           (and (<= -1 (acl2-cosine x)) (<= (acl2-cosine x) 1)))
  :rule-classes ((:linear) (:rewrite))
  :hints (("Goal" :use ((:instance sin**2+cos**2))
           :nonlinearp t
           :in-theory (disable sin**2+cos**2))))

(defthm sine-bounds
  (implies (realp x)
           (and (<= -1 (acl2-sine x)) (<= (acl2-sine x) 1)))
  :rule-classes ((:linear) (:rewrite))
  :hints (("Goal" :use ((:instance sin**2+cos**2))
           :nonlinearp t
           :in-theory (disable sin**2+cos**2))))

(defthm limited-if-bounded-by-1
  (implies (and (realp x) (<= -1 x) (<= x 1))
           (i-limited x))
  :hints (("Goal" :use ((:instance limited-squeeze (a -1) (b 1))))))

(defthm i-limited-cc
  (implies (and (realp m) (realp n)) (i-limited (cc m n))))
(defthm i-limited-ss
  (implies (and (realp m) (realp n)) (i-limited (ss m n))))

;;; ---------------- bounds, for admitting the defun-std ----------------

(defthm realp-winding-gamma (realp (winding-gamma))
  :rule-classes (:rewrite :type-prescription))
(local (in-theory (disable (:executable-counterpart winding-gamma))))
(local (in-theory (disable riemann-decomp riemann-decomp-lemma)))

(defthmd product-bounds
  (implies (and (realp c) (realp d) (<= -1 c) (<= c 1) (<= -1 d) (<= d 1))
           (and (<= -1 (* c d)) (<= (* c d) 1)))
  :hints (("Goal" :nonlinearp t)))

(defthm integrand-bounds
  (implies (and (realp x) (realp m) (realp n))
           (and (<= -1 (inductance-integrand x m n))
                (<= (inductance-integrand x m n) 1)))
  :rule-classes ((:linear) (:rewrite))
  :hints (("Goal" :use ((:instance product-bounds
                                   (c (acl2-cosine (- x (* m (winding-gamma)))))
                                   (d (acl2-cosine (- x (* n (winding-gamma)))))))
           :in-theory (disable winding-gamma))))

(defthm realp-inductance-integrand
  (implies (and (realp x) (realp m) (realp n))
           (realp (inductance-integrand x m n))))

(defthmd scaled-bounds
  (implies (and (realp d) (< 0 d) (realp f) (<= -1 f) (<= f 1))
           (and (<= (- d) (* d f)) (<= (* d f) d)))
  :hints (("Goal" :nonlinearp t)))

(defthm step-bounds
  (implies (and (realp d) (< 0 d) (realp y) (realp m) (realp n))
           (and (<= (- d) (* d (inductance-integrand y m n)))
                (<= (* d (inductance-integrand y m n)) d)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance scaled-bounds (f (inductance-integrand y m n))))
           :in-theory (disable inductance-integrand))))

(defthm riemann-integrand-bounds-lemma
  (implies (and (partitionp p) (realp m) (realp n))
           (and (<= (- (sumlist (deltas p)))
                    (dotprod (deltas p) (map-inductance-integrand (cdr p) m n)))
                (<= (dotprod (deltas p) (map-inductance-integrand (cdr p) m n))
                    (sumlist (deltas p)))))
  :hints (("Goal" :induct (deltas p)
           :expand ((map-inductance-integrand (cdr p) m n))
           :in-theory (disable inductance-integrand sumlist-deltas riemann-decomp-lemma))))

(defthm realp-car-last-partition
  (implies (partitionp p) (realp (car (last p)))))

(defthm realp-riemann-inductance-integrand-dotprod
  (implies (and (partitionp p) (realp m) (realp n))
           (realp (dotprod (deltas p) (map-inductance-integrand (cdr p) m n))))
  :hints (("Goal" :induct (deltas p)
           :expand ((map-inductance-integrand (cdr p) m n))
           :in-theory (disable inductance-integrand riemann-decomp-lemma))))

(defthm realp-riemann-inductance-integrand
  (implies (and (partitionp p) (realp m) (realp n))
           (realp (riemann-inductance-integrand p m n)))
  :hints (("Goal" :use ((:instance realp-riemann-inductance-integrand-dotprod))
           :in-theory (disable riemann-decomp riemann-decomp-lemma
                               realp-riemann-inductance-integrand-dotprod))))

(defthm riemann-integrand-bounds
  (implies (and (partitionp p) (realp m) (realp n))
           (and (<= (- (car p) (car (last p)))
                    (riemann-inductance-integrand p m n))
                (<= (riemann-inductance-integrand p m n)
                    (- (car (last p)) (car p)))))
  :hints (("Goal" :use ((:instance riemann-integrand-bounds-lemma)
                        (:instance sumlist-deltas))
           :in-theory (disable riemann-integrand-bounds-lemma riemann-decomp riemann-decomp-lemma
                               sumlist-deltas))))

(defthm limited-riemann-inductance-integrand-generic
  (implies (and (partitionp p) (standardp (car p)) (standardp (car (last p)))
                (realp m) (realp n))
           (i-limited (riemann-inductance-integrand p m n)))
  :hints (("Goal" :use ((:instance riemann-integrand-bounds)
                        (:instance standards-are-limited (x (- (car p) (car (last p)))))
                        (:instance standards-are-limited (x (- (car (last p)) (car p))))
                        (:instance limited-squeeze
                                   (a (- (car p) (car (last p))))
                                   (b (- (car (last p)) (car p)))
                                   (x (riemann-inductance-integrand p m n))))
           :in-theory (disable riemann-integrand-bounds riemann-decomp riemann-decomp-lemma
                               limited-squeeze sumlist-deltas riemann-inductance-integrand
                               dotprod deltas map-inductance-integrand sumlist partitionp last))))

(defthm limited-riemann-inductance-integrand-small-partition
  (implies (and (realp a) (standardp a)
                (realp b) (standardp b)
                (< a b) (realp m) (realp n))
           (i-limited (riemann-inductance-integrand (make-small-partition a b) m n)))
  :hints (("Goal" :use ((:instance limited-riemann-inductance-integrand-generic
                                   (p (make-small-partition a b))))
           :in-theory (disable limited-riemann-inductance-integrand-generic
                               riemann-inductance-integrand riemann-decomp))))

(local (in-theory (disable riemann-inductance-integrand)))

(defun-std int-inductance-integrand (a b m n)
  (if (and (realp a) (realp b) (< a b) (realp m) (realp n))
      (standard-part (riemann-inductance-integrand (make-small-partition a b) m n))
    0))

(local (in-theory (enable riemann-decomp)))

(defthm inductance-integral-riemann-form
  (implies (and (integerp m) (integerp n)
                (partitionp p)
                (equal (car p) 0)
                (equal (car (last p)) (* 2 (acl2-pi)))
                (i-small (mesh p)))
           (i-close (riemann-inductance-integrand p m n)
                    (* (acl2-pi) (acl2-cosine (* (- m n) (winding-gamma))))))
  :hints (("Goal" :use ((:instance riemann-cos2-small)
                        (:instance riemann-sin2-small)
                        (:instance limited*small->small (x (* 1/2 (cc m n))) (y (riemann-cos2 p)))
                        (:instance limited*small->small (x (* 1/2 (ss m n))) (y (riemann-sin2 p)))
                        (:instance i-small-plus
                                   (x (* 1/2 (cc m n) (riemann-cos2 p)))
                                   (y (* 1/2 (ss m n) (riemann-sin2 p)))))
           :in-theory (e/d (i-close kk)
                           (riemann-inductance-integrand riemann-cos2 riemann-sin2
                            cc ss winding-gamma riemann-cos2-small riemann-sin2-small
                            limited*small->small i-small-plus)))))

(defthm-std standardp-winding-gamma (standardp (winding-gamma)))

(local (in-theory (disable riemann-decomp riemann-decomp-lemma)))

(defthm-std inductance-integral-value-std
  (implies (and (integerp m) (integerp n))
           (equal (int-inductance-integrand 0 (* 2 (acl2-pi)) m n)
                  (* (acl2-pi) (acl2-cosine (* (- m n) (winding-gamma))))))
  :hints (("Goal" :use ((:instance inductance-integral-riemann-form
                                   (p (make-small-partition 0 (* 2 (acl2-pi)))))
                        (:instance close-x-y->same-standard-part
                                   (x (riemann-inductance-integrand (make-small-partition 0 (* 2 (acl2-pi))) m n))
                                   (y (* (acl2-pi) (acl2-cosine (* (- m n) (winding-gamma))))))
                        (:instance small-mesh-make-small-partition (a 0) (b (* 2 (acl2-pi)))))
           :in-theory (disable inductance-integral-riemann-form mesh small-mesh-make-small-partition close-x-y->same-standard-part
                               riemann-inductance-integrand winding-gamma))))

(defthm inductance-integral-value
  (implies (and (integerp m) (integerp n))
           (equal (int-inductance-integrand 0 (* 2 (acl2-pi)) m n)
                  (* (acl2-pi) (acl2-cosine (* (- m n) (winding-gamma))))))
  :hints (("Goal" :use ((:instance inductance-integral-value-std))
           :in-theory nil)))
