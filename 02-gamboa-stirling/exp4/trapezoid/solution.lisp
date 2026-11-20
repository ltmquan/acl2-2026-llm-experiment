(in-package "ACL2")

(include-book "defs")

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "nonstd/nsa/nsa" :dir :system))
(local (include-book "nonstd/integrals/continuous-function" :dir :system))
(local (include-book "nonstd/integrals/ftc-1" :dir :system))
(local (include-book "nonstd/nsa/derivatives" :dir :system))

;;; ------------------------------------------------------------------
;;; Basic nonstandard facts
;;; ------------------------------------------------------------------

(local
 (defthm-std tf-standard
   (implies (standardp x) (standardp (tf x)))))
(local
 (defthm-std tf1-standard
   (implies (standardp x) (standardp (tf1 x)))))
(local
 (defthm-std tf2-standard
   (implies (standardp x) (standardp (tf2 x)))))
(local
 (defthm-std tf2-bound-standard
   (standardp (tf2-bound))))
(local
 (defthm-std tf-domain-standard
   (standardp (tf-domain))))

(local
 (defthm lemma-small-from-limited-quotient
   (implies (and (realp x)
                 (realp y)
                 (i-small y)
                 (not (= y 0))
                 (i-limited (/ x y)))
            (i-small x))
   :hints (("Goal"
            :use ((:instance small*limited->small (x y) (y (/ x y))))
            :in-theory (disable small*limited->small)))))

(local
 (defthm tf-continuous
   (implies (and (standardp x)
                 (inside-interval-p x (tf-domain))
                 (i-close x y)
                 (inside-interval-p y (tf-domain)))
            (i-close (tf x) (tf y)))
   :hints (("Goal"
            :cases ((equal x y)))
           ("Subgoal 2"
            :use ((:instance tf1-is-derivative-of-tf (x1 y))
                  (:instance standards-are-limited (x (tf1 x)))
                  (:instance i-close-limited
                             (x (tf1 x))
                             (y (/ (- (tf x) (tf y)) (- x y))))
                  (:instance lemma-small-from-limited-quotient
                             (x (- (tf x) (tf y)))
                             (y (- x y))))
            :in-theory (e/d (i-close)
                            (tf1-is-derivative-of-tf i-close-limited
                                                     lemma-small-from-limited-quotient))))))

(local
 (defthm tf1-continuous
   (implies (and (standardp x)
                 (inside-interval-p x (tf-domain))
                 (i-close x y)
                 (inside-interval-p y (tf-domain)))
            (i-close (tf1 x) (tf1 y)))
   :hints (("Goal"
            :cases ((equal x y)))
           ("Subgoal 2"
            :use ((:instance tf2-is-derivative-of-tf1 (x1 y))
                  (:instance standards-are-limited (x (tf2 x)))
                  (:instance i-close-limited
                             (x (tf2 x))
                             (y (/ (- (tf1 x) (tf1 y)) (- x y))))
                  (:instance lemma-small-from-limited-quotient
                             (x (- (tf1 x) (tf1 y)))
                             (y (- x y))))
            :in-theory (e/d (i-close)
                            (tf2-is-derivative-of-tf1 i-close-limited
                                                      lemma-small-from-limited-quotient))))))

;;; ------------------------------------------------------------------
;;; The integral
;;; ------------------------------------------------------------------

(local
 (defthm limited-riemann-tf-small-partition
   (implies (and (realp a) (standardp a)
                 (realp b) (standardp b)
                 (inside-interval-p a (tf-domain))
                 (inside-interval-p b (tf-domain))
                 (< a b))
            (i-limited (riemann-tf (make-small-partition a b))))
   :hints (("Goal"
            :by (:functional-instance limited-riemann-rcfn-small-partition
                                      (rcfn-domain tf-domain)
                                      (rcfn tf)
                                      (map-rcfn map-tf)
                                      (riemann-rcfn riemann-tf)))
           ("Subgoal 2"
            :use ((:instance tf-domain-non-trivial))))))

(encapsulate
  nil
  (local (in-theory (disable riemann-tf)))
  (defun-std strict-int-tf (a b)
    (if (and (realp a) (realp b)
             (inside-interval-p a (tf-domain)) (inside-interval-p b (tf-domain))
             (< a b))
        (standard-part (riemann-tf (make-small-partition a b)))
      0)))

(defun int-tf (a b) (if (<= a b) (strict-int-tf a b) (- (strict-int-tf b a))))

(local
 (defthm ftc-1-tf
   (implies (and (inside-interval-p a (tf-domain))
                 (inside-interval-p b (tf-domain))
                 (inside-interval-p c (tf-domain))
                 (standardp b)
                 (i-close b c)
                 (not (equal b c)))
            (i-close (/ (- (int-tf a b) (int-tf a c))
                        (- b c))
                     (tf b)))
   :hints (("Goal"
            :by (:functional-instance ftc-1
                                      (rcfn-domain tf-domain)
                                      (int-rcfn int-tf)
                                      (rcfn tf)
                                      (map-rcfn map-tf)
                                      (riemann-rcfn riemann-tf)
                                      (strict-int-rcfn strict-int-tf))))))

(local
 (defthm split-int-tf
   (implies (and (inside-interval-p a (tf-domain))
                 (inside-interval-p b (tf-domain))
                 (inside-interval-p c (tf-domain)))
            (equal (+ (int-tf a c)
                      (int-tf c b))
                   (int-tf a b)))
   :hints (("Goal"
            :by (:functional-instance split-rcfn-integral-by-subintervals
                                      (rcfn-domain tf-domain)
                                      (int-rcfn int-tf)
                                      (rcfn tf)
                                      (map-rcfn map-tf)
                                      (riemann-rcfn riemann-tf)
                                      (strict-int-rcfn strict-int-tf))))))

(local
 (defthm realp-strict-int-tf
   (implies (and (realp a)
                 (realp b))
            (realp (strict-int-tf a b)))
   :hints (("Goal"
            :by (:functional-instance realp-strict-int-rcfn
                                      (strict-int-rcfn strict-int-tf)
                                      (rcfn-domain tf-domain)
                                      (rcfn tf)
                                      (riemann-rcfn riemann-tf)
                                      (map-rcfn map-tf))))))

(local
 (defthm-std realp-strict-int-tf-stronger
   (realp (strict-int-tf a b))
   :hints (("Goal"
            :cases ((not (realp a))
                    (not (realp b))))
           ("Subgoal 3"
            :use ((:instance realp-strict-int-tf))))))

(local
 (defthm realp-int-tf
   (realp (int-tf a b))))

(local
 (defthm-std strict-int-tf-a-a
   (equal (strict-int-tf a a) 0)))

(local
 (defthm int-tf-a-a
   (equal (int-tf a a) 0)))

(local (in-theory (disable int-tf)))

;;; ------------------------------------------------------------------
;;; Generic lemma: a function with nonnegative derivative is
;;; nondecreasing.  The function takes a parameter p.
;;; ------------------------------------------------------------------

(encapsulate
  (((mf * *) => *) ((mf1 * *) => *))
  (local (defun mf (p x) (declare (ignore p x)) 0))
  (local (defun mf1 (p x) (declare (ignore p x)) 0))
  (defthm mf-real (realp (mf p x)) :rule-classes (:rewrite :type-prescription))
  (defthm mf1-real (realp (mf1 p x)) :rule-classes (:rewrite :type-prescription))
  (defthm mf1-is-derivative
    (implies (and (standardp p)
                  (standardp x)
                  (inside-interval-p p (tf-domain))
                  (inside-interval-p x (tf-domain))
                  (inside-interval-p y (tf-domain))
                  (i-close x y) (not (= x y)))
             (i-close (/ (- (mf p x) (mf p y)) (- x y)) (mf1 p x))))
  (defthm mf1-nonneg
    (implies (and (inside-interval-p p (tf-domain))
                  (inside-interval-p x (tf-domain))
                  (<= p x))
             (<= 0 (mf1 p x)))))

(local
 (encapsulate
   ((mf-sub () t))
   (local
    (defun mf-sub ()
      (let ((left (interval-left-endpoint (tf-domain)))
            (right (interval-right-endpoint (tf-domain))))
        (if (null left)
            (if (null right)
                (interval 0 1)
              (interval (- right 2) (- right 1)))
          (if (null right)
              (interval (+ left 1) (+ left 2))
            (interval (+ left (* 1/3 (- right left)))
                      (+ left (* 2/3 (- right left)))))))))

   (defthm mf-sub-is-subdomain
     (subinterval-p (mf-sub) (tf-domain))
     :hints (("Goal"
              :use ((:instance interval-p (interval (tf-domain)))
                    (:instance tf-domain-non-trivial))
              :in-theory (enable interval-definition-theory))))

   (defthm mf-sub-closed-bounded
     (and (interval-left-inclusive-p (mf-sub))
          (interval-right-inclusive-p (mf-sub))))

   (defthm mf-sub-real-left
     (realp (interval-left-endpoint (mf-sub)))
     :rule-classes (:rewrite :type-prescription))

   (defthm mf-sub-real-right
     (realp (interval-right-endpoint (mf-sub)))
     :rule-classes (:rewrite :type-prescription))

   (defthm mf-sub-non-trivial
     (< (interval-left-endpoint (mf-sub))
        (interval-right-endpoint (mf-sub)))
     :hints (("Goal"
              :use (:instance tf-domain-non-trivial))))))

(local
 (defun-sk exists-mvt-point-mf ()
   (exists (x)
           (and (inside-interval-p x (mf-sub))
                (not (equal x (interval-left-endpoint (mf-sub))))
                (not (equal x (interval-right-endpoint (mf-sub))))
                (equal (mf1 (interval-left-endpoint (mf-sub)) x)
                       (/ (- (mf (interval-left-endpoint (mf-sub))
                                 (interval-right-endpoint (mf-sub)))
                             (mf (interval-left-endpoint (mf-sub))
                                 (interval-left-endpoint (mf-sub))))
                          (- (interval-right-endpoint (mf-sub))
                             (interval-left-endpoint (mf-sub)))))))))

(local
 (defthm-std standard-left-endpoint-mf-sub
   (standardp (interval-left-endpoint (mf-sub)))))

(local
 (defthm left-endpoint-mf-sub-in-domain
   (inside-interval-p (interval-left-endpoint (mf-sub)) (tf-domain))
   :hints (("Goal"
            :use ((:instance mf-sub-is-subdomain)
                  (:instance mf-sub-closed-bounded)
                  (:instance mf-sub-real-left))
            :in-theory (e/d (interval-definition-theory)
                            (mf-sub-is-subdomain
                             mf-sub-closed-bounded
                             mf-sub-real-left))))))

(local
 (defthm-std mf1-standard
   (implies (and (standardp p) (standardp x))
            (standardp (mf1 p x)))))

(local
 (defthm mf-differentiable
   (implies (and (standardp p)
                 (inside-interval-p p (tf-domain))
                 (standardp x)
                 (inside-interval-p x (tf-domain))
                 (inside-interval-p y1 (tf-domain))
                 (inside-interval-p y2 (tf-domain))
                 (i-close x y1) (not (= x y1))
                 (i-close x y2) (not (= x y2)))
            (and (i-limited (/ (- (mf p x) (mf p y1)) (- x y1)))
                 (i-close (/ (- (mf p x) (mf p y1)) (- x y1))
                          (/ (- (mf p x) (mf p y2)) (- x y2)))))
   :hints (("Goal"
            :use ((:instance mf1-is-derivative (y y1))
                  (:instance mf1-is-derivative (y y2))
                  (:instance standards-are-limited (x (mf1 p x)))
                  (:instance i-close-limited
                             (x (mf1 p x))
                             (y (/ (- (mf p x) (mf p y1)) (- x y1))))
                  (:instance i-close-symmetric
                             (x (/ (- (mf p x) (mf p y2)) (- x y2)))
                             (y (mf1 p x)))
                  (:instance i-close-symmetric
                             (x (/ (- (mf p x) (mf p y1)) (- x y1)))
                             (y (mf1 p x)))
                  (:instance i-close-transitive
                             (x (/ (- (mf p x) (mf p y1)) (- x y1)))
                             (y (mf1 p x))
                             (z (/ (- (mf p x) (mf p y2)) (- x y2)))))
            :in-theory (union-theories '(mf1-real mf-real mf1-standard) (theory 'minimal-theory))))))

(local
 (defthm mf-derivative-standard-part
   (implies (and (standardp p)
                 (inside-interval-p p (tf-domain))
                 (standardp x)
                 (inside-interval-p x (tf-domain))
                 (inside-interval-p (+ x eps) (tf-domain))
                 (realp eps)
                 (i-small eps)
                 (not (equal eps 0)))
            (equal (standard-part (/ (- (mf p (+ x eps)) (mf p x)) eps))
                   (mf1 p x)))
   :hints (("Goal"
            :use ((:instance mf1-is-derivative (y (+ x eps)))
                  (:instance i-close-to-small-sum)
                  (:instance standards-are-limited (x (mf1 p x)))
                  (:instance close-x-y->same-standard-part
                             (x (mf1 p x))
                             (y (/ (- (mf p x) (mf p (+ x eps))) (- x (+ x eps))))))
            :in-theory (disable mf1-is-derivative i-close-to-small-sum
                                standards-are-limited close-x-y->same-standard-part)))))

(local
 (defthm tf-domain-not-both-endpoints
   (implies (inside-interval-p x (tf-domain))
            (or (not (equal (interval-left-endpoint (tf-domain)) x))
                (not (equal (interval-right-endpoint (tf-domain)) x))))
   :hints (("Goal"
            :use ((:instance tf-domain-non-trivial))))
   :rule-classes nil))

(local
 (defthm tf-domain-eps-or-minus-eps
   (implies (and (inside-interval-p x (tf-domain))
                 (standardp x)
                 (realp eps)
                 (i-small eps))
            (or (inside-interval-p (+ x eps) (tf-domain))
                (inside-interval-p (- x eps) (tf-domain))))
   :hints (("Goal"
            :use ((:instance tf-domain-not-both-endpoints)
                  (:instance inside-interval-x+eps
                             (x x) (eps eps) (interval (tf-domain)))
                  (:instance inside-interval-x+eps
                             (x x) (eps (- eps)) (interval (tf-domain)))
                  (:instance inside-interval-x-eps
                             (x x) (eps eps) (interval (tf-domain)))
                  (:instance inside-interval-x-eps
                             (x x) (eps (- eps)) (interval (tf-domain))))))
   :rule-classes nil))

(local
 (defthm small-inverse-large-integer
   (and (realp (/ (i-large-integer)))
        (realp (- (/ (i-large-integer))))
        (i-small (/ (i-large-integer)))
        (i-small (- (/ (i-large-integer))))
        (not (equal (/ (i-large-integer)) 0))
        (not (equal (- (/ (i-large-integer))) 0)))
   :rule-classes nil))

(local
 (defthm mvt-theorem-sk-for-mf
   (exists-mvt-point-mf)
   :hints (("Goal"
            :by (:functional-instance
                 mvt-theorem-sk
                 (exists-mvt-point exists-mvt-point-mf)
                 (exists-mvt-point-witness exists-mvt-point-mf-witness)
                 (rdfn-domain tf-domain)
                 (rdfn-subdomain mf-sub)
                 (rdfn (lambda (x) (mf (interval-left-endpoint (mf-sub)) x)))
                 (derivative-rdfn (lambda (x) (mf1 (interval-left-endpoint (mf-sub)) x)))
                 (differential-rdfn
                  (lambda (x eps)
                    (/ (- (mf (interval-left-endpoint (mf-sub)) (+ x eps))
                          (mf (interval-left-endpoint (mf-sub)) x))
                       eps)))))
           ("Subgoal 6"
            :use ((:instance exists-mvt-point-mf-suff))
            :in-theory (disable exists-mvt-point-mf-suff))
           ("Subgoal 4"
            :use ((:instance mf-differentiable
                             (p (interval-left-endpoint (mf-sub)))))
            :in-theory (disable mf-differentiable))
           ("Subgoal 3"
            :use ((:instance tf-domain-non-trivial)))
           ("Subgoal 1"
            :use ((:instance mf-derivative-standard-part
                             (p (interval-left-endpoint (mf-sub)))
                             (eps (/ (i-large-integer))))
                  (:instance mf-derivative-standard-part
                             (p (interval-left-endpoint (mf-sub)))
                             (eps (- (/ (i-large-integer)))))
                  (:instance tf-domain-eps-or-minus-eps
                             (eps (/ (i-large-integer))))
                  (:instance small-inverse-large-integer)
                  (:instance standard-left-endpoint-mf-sub)
                  (:instance left-endpoint-mf-sub-in-domain))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm mf-sub-mono-lemma
   (implies (and (realp q) (realp l) (realp r) (< l r)
                 (<= 0 q)
                 (equal q (/ (- a b) (- r l))))
            (<= b a))
   :rule-classes nil))

(local
 (defthm mf-sub-mono
   (<= (mf (interval-left-endpoint (mf-sub))
           (interval-left-endpoint (mf-sub)))
       (mf (interval-left-endpoint (mf-sub))
           (interval-right-endpoint (mf-sub))))
   :hints (("Goal"
            :use ((:instance mvt-theorem-sk-for-mf)
                  (:instance exists-mvt-point-mf)
                  (:instance mf1-nonneg
                             (p (interval-left-endpoint (mf-sub)))
                             (x (exists-mvt-point-mf-witness)))
                  (:instance inside-subinterval
                             (x (exists-mvt-point-mf-witness))
                             (subinterval (mf-sub))
                             (interval (tf-domain)))
                  (:instance inside-interval-p->=-left-endpoint
                             (x (exists-mvt-point-mf-witness))
                             (interval (mf-sub)))
                  (:instance mf-sub-mono-lemma
                             (q (mf1 (interval-left-endpoint (mf-sub))
                                     (exists-mvt-point-mf-witness)))
                             (l (interval-left-endpoint (mf-sub)))
                             (r (interval-right-endpoint (mf-sub)))
                             (a (mf (interval-left-endpoint (mf-sub))
                                    (interval-right-endpoint (mf-sub))))
                             (b (mf (interval-left-endpoint (mf-sub))
                                    (interval-left-endpoint (mf-sub))))))
            :in-theory (disable mvt-theorem-sk-for-mf exists-mvt-point-mf
                                mf1-nonneg inside-subinterval
                                inside-interval-p->=-left-endpoint)))))

(defthm mf-mono
  (implies (and (inside-interval-p p (tf-domain))
                (inside-interval-p b (tf-domain))
                (<= p b))
           (<= (mf p p) (mf p b)))
  :hints (("Goal"
           :cases ((equal p b)))
          ("Subgoal 2"
           :use ((:functional-instance
                  mf-sub-mono
                  (mf-sub (lambda ()
                            (if (and (inside-interval-p p (tf-domain))
                                     (inside-interval-p b (tf-domain))
                                     (< p b))
                                (interval p b)
                              (mf-sub)))))))))

;;; ------------------------------------------------------------------
;;; Closeness algebra
;;; ------------------------------------------------------------------

(local
 (defthmd close-plus
   (implies (and (i-close x1 x2)
                 (i-close y1 y2))
            (i-close (+ x1 y1) (+ x2 y2)))
   :hints (("Goal"
            :use ((:instance i-small-plus
                             (x (- x1 x2))
                             (y (- y1 y2))))
            :in-theory (e/d (i-close)
                            (i-small-plus))))))

(local
 (defthmd close-times
   (implies (and (i-close x1 x2)
                 (i-close y1 y2)
                 (i-limited x2)
                 (i-limited y2)
                 (acl2-numberp x1) (acl2-numberp x2)
                 (acl2-numberp y1) (acl2-numberp y2))
            (i-close (* x1 y1) (* x2 y2)))
   :hints (("Goal"
            :use ((:instance i-close-limited-2 (x x1) (y x2))
                  (:instance limited*small->small (x x1) (y (- y1 y2)))
                  (:instance limited*small->small (x y2) (y (- x1 x2)))
                  (:instance i-small-plus
                             (x (* x1 (- y1 y2)))
                             (y (* y2 (- x1 x2)))))
            :in-theory (e/d (i-close)
                            (i-close-limited-2 limited*small->small i-small-plus))))))

(local
 (defthmd close-scale
   (implies (and (i-close x1 x2)
                 (standardp c)
                 (acl2-numberp c)
                 (acl2-numberp x1) (acl2-numberp x2))
            (i-close (* c x1) (* c x2)))
   :hints (("Goal"
            :use ((:instance standards-are-limited (x c))
                  (:instance limited*small->small (x c) (y (- x1 x2))))
            :in-theory (e/d (i-close)
                            (standards-are-limited limited*small->small))))))

(local
 (defthm close-subst
   (implies (and (equal u v) (i-close v w))
            (i-close u w))
   :rule-classes nil))

(local
 (defthm dq-linear-alg
   (implies (and (acl2-numberp x) (acl2-numberp y)
                 (not (equal x y)))
            (equal (/ (- (+ (* c fx) (* d gx)) (+ (* c fy) (* d gy))) (- x y))
                   (+ (* c (/ (- fx fy) (- x y)))
                      (* d (/ (- gx gy) (- x y))))))
   :rule-classes nil))

(local
 (defthm dq-linear
   (implies (and (i-close (/ (- fx fy) (- x y)) f1)
                 (i-close (/ (- gx gy) (- x y)) g1v)
                 (standardp c) (standardp d)
                 (realp c) (realp d)
                 (realp fx) (realp fy) (realp gx) (realp gy)
                 (realp f1) (realp g1v)
                 (realp x) (realp y)
                 (not (equal x y)))
            (i-close (/ (- (+ (* c fx) (* d gx)) (+ (* c fy) (* d gy))) (- x y))
                     (+ (* c f1) (* d g1v))))
   :hints (("Goal"
            :use ((:instance close-scale
                             (x1 (/ (- fx fy) (- x y))) (x2 f1))
                  (:instance close-scale (c d)
                             (x1 (/ (- gx gy) (- x y))) (x2 g1v))
                  (:instance close-plus
                             (x1 (* c (/ (- fx fy) (- x y))))
                             (x2 (* c f1))
                             (y1 (* d (/ (- gx gy) (- x y))))
                             (y2 (* d g1v)))
                  (:instance dq-linear-alg)
                  (:instance close-subst
                             (u (/ (- (+ (* c fx) (* d gx)) (+ (* c fy) (* d gy))) (- x y)))
                             (v (+ (* c (/ (- fx fy) (- x y)))
                                   (* d (/ (- gx gy) (- x y)))))
                             (w (+ (* c f1) (* d g1v)))))
            :in-theory (union-theories '(realp-implies-acl2-numberp)
                                       (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm close-subst-2
   (implies (and (equal w w2) (i-close v w))
            (i-close v w2))
   :rule-classes nil))

;;; generic: 1/2 q1 - 1/2 f1 - 1/2 (y-a) q2  ~  -1/2 (x-a) f2
(local
 (defthm dg1-gen
   (implies (and (i-close q1 f1) (i-close q2 f2) (i-close x y)
                 (standardp x) (standardp a) (standardp f1) (standardp f2)
                 (realp q1) (realp q2) (realp f1) (realp f2)
                 (realp x) (realp y) (realp a))
            (i-close (- (- (* 1/2 q1) (* 1/2 f1)) (* 1/2 (- y a) q2))
                     (- (* 1/2 (- x a) f2))))
   :hints (("Goal"
            :use ((:instance i-close-symmetric (x x) (y y))
                  (:instance close-plus (x1 y) (x2 x) (y1 (- a)) (y2 (- a)))
                  (:instance close-times (x1 (- y a)) (x2 (- x a)) (y1 q2) (y2 f2))
                  (:instance close-plus (x1 (* 1/2 q1)) (x2 (* 1/2 f1))
                             (y1 (- (* 1/2 f1))) (y2 (- (* 1/2 f1))))
                  (:instance close-scale (c 1/2) (x1 q1) (x2 f1))
                  (:instance close-scale (c -1/2) (x1 (* (- y a) q2)) (x2 (* (- x a) f2)))
                  (:instance close-plus
                             (x1 (+ (* 1/2 q1) (- (* 1/2 f1))))
                             (x2 (+ (* 1/2 f1) (- (* 1/2 f1))))
                             (y1 (* -1/2 (* (- y a) q2)))
                             (y2 (* -1/2 (* (- x a) f2))))
                  (:instance close-subst
                             (u (- (- (* 1/2 q1) (* 1/2 f1)) (* 1/2 (- y a) q2)))
                             (v (+ (+ (* 1/2 q1) (- (* 1/2 f1)))
                                   (* -1/2 (* (- y a) q2))))
                             (w (+ (+ (* 1/2 f1) (- (* 1/2 f1)))
                                   (* -1/2 (* (- x a) f2)))))
                  (:instance close-subst-2
                             (v (- (- (* 1/2 q1) (* 1/2 f1)) (* 1/2 (- y a) q2)))
                             (w (+ (+ (* 1/2 f1) (- (* 1/2 f1)))
                                   (* -1/2 (* (- x a) f2))))
                             (w2 (- (* 1/2 (- x a) f2)))))
            :in-theory (disable close-plus close-times close-scale
                                i-close-symmetric)))
   :rule-classes nil))

;;; generic: q1 - 1/2 (fa + fx) - 1/2 (y-a) q2  ~  1/2 (fx - fa) - 1/2 (x-a) f1
(local
 (defthm dgg-gen
   (implies (and (i-close q1 fx) (i-close q2 f1) (i-close x y)
                 (standardp x) (standardp a) (standardp fx) (standardp f1)
                 (realp q1) (realp q2) (realp fx) (realp f1) (realp fa)
                 (realp x) (realp y) (realp a))
            (i-close (- (- q1 (* 1/2 (+ fa fx))) (* 1/2 (- y a) q2))
                     (- (* 1/2 (- fx fa)) (* 1/2 (- x a) f1))))
   :hints (("Goal"
            :use ((:instance i-close-symmetric (x x) (y y))
                  (:instance close-plus (x1 y) (x2 x) (y1 (- a)) (y2 (- a)))
                  (:instance close-times (x1 (- y a)) (x2 (- x a)) (y1 q2) (y2 f1))
                  (:instance close-plus (x1 q1) (x2 fx)
                             (y1 (- (* 1/2 (+ fa fx)))) (y2 (- (* 1/2 (+ fa fx)))))
                  (:instance close-scale (c -1/2) (x1 (* (- y a) q2)) (x2 (* (- x a) f1)))
                  (:instance close-plus
                             (x1 (+ q1 (- (* 1/2 (+ fa fx)))))
                             (x2 (+ fx (- (* 1/2 (+ fa fx)))))
                             (y1 (* -1/2 (* (- y a) q2)))
                             (y2 (* -1/2 (* (- x a) f1))))
                  (:instance close-subst
                             (u (- (- q1 (* 1/2 (+ fa fx))) (* 1/2 (- y a) q2)))
                             (v (+ (+ q1 (- (* 1/2 (+ fa fx))))
                                   (* -1/2 (* (- y a) q2))))
                             (w (+ (+ fx (- (* 1/2 (+ fa fx))))
                                   (* -1/2 (* (- x a) f1)))))
                  (:instance close-subst-2
                             (v (- (- q1 (* 1/2 (+ fa fx))) (* 1/2 (- y a) q2)))
                             (w (+ (+ fx (- (* 1/2 (+ fa fx))))
                                   (* -1/2 (* (- x a) f1))))
                             (w2 (- (* 1/2 (- fx fa)) (* 1/2 (- x a) f1)))))
            :in-theory (disable close-plus close-times close-scale
                                i-close-symmetric)))
   :rule-classes nil))

(local
 (defthm dsq-gen
   (implies (and (i-close x y)
                 (standardp x) (standardp a)
                 (realp x) (realp y) (realp a))
            (i-close (+ (- x a) (- y a))
                     (* 2 (- x a))))
   :hints (("Goal"
            :use ((:instance i-close-symmetric (x x) (y y))
                  (:instance close-plus (x1 y) (x2 x) (y1 (- a)) (y2 (- a)))
                  (:instance close-plus (x1 (- x a)) (x2 (- x a))
                             (y1 (- y a)) (y2 (- x a)))
                  (:instance close-subst-2
                             (v (+ (- x a) (- y a)))
                             (w (+ (- x a) (- x a)))
                             (w2 (* 2 (- x a)))))
            :in-theory (disable close-plus i-close-symmetric)))
   :rule-classes nil))

(local
 (defthm dcube-gen
   (implies (and (i-close x y)
                 (standardp x) (standardp a)
                 (realp x) (realp y) (realp a))
            (i-close (+ (* (- x a) (- x a)) (* (- x a) (- y a)) (* (- y a) (- y a)))
                     (* 3 (- x a) (- x a))))
   :hints (("Goal"
            :use ((:instance i-close-symmetric (x x) (y y))
                  (:instance close-plus (x1 y) (x2 x) (y1 (- a)) (y2 (- a)))
                  (:instance close-times (x1 (- x a)) (x2 (- x a))
                             (y1 (- y a)) (y2 (- x a)))
                  (:instance close-times (x1 (- y a)) (x2 (- x a))
                             (y1 (- y a)) (y2 (- x a)))
                  (:instance close-plus
                             (x1 (* (- x a) (- y a))) (x2 (* (- x a) (- x a)))
                             (y1 (* (- y a) (- y a))) (y2 (* (- x a) (- x a))))
                  (:instance close-plus
                             (x1 (* (- x a) (- x a))) (x2 (* (- x a) (- x a)))
                             (y1 (+ (* (- x a) (- y a)) (* (- y a) (- y a))))
                             (y2 (+ (* (- x a) (- x a)) (* (- x a) (- x a)))))
                  (:instance close-subst-2
                             (v (+ (* (- x a) (- x a)) (* (- x a) (- y a)) (* (- y a) (- y a))))
                             (w (+ (* (- x a) (- x a))
                                   (+ (* (- x a) (- x a)) (* (- x a) (- x a)))))
                             (w2 (* 3 (- x a) (- x a)))))
            :in-theory (disable close-plus close-times i-close-symmetric)))
   :rule-classes nil))

;;; ------------------------------------------------------------------
;;; Auxiliary functions and their derivatives
;;; ------------------------------------------------------------------

(defun g1 (a x)
  (- (* 1/2 (- (tf x) (tf a))) (* 1/2 (- (realfix x) (realfix a)) (tf1 x))))

(defun gg (a x)
  (- (int-tf a x) (* 1/2 (- (realfix x) (realfix a)) (+ (tf a) (tf x)))))

(local
 (defthm div-intro
   (implies (and (acl2-numberp d) (not (equal d 0))
                 (acl2-numberp r)
                 (equal n (* r d)))
            (equal (/ n d) r))
   :rule-classes nil))

(local
 (defthm g1-real (realp (g1 a x)) :rule-classes (:rewrite :type-prescription)))
(local
 (defthm gg-real (realp (gg a x)) :rule-classes (:rewrite :type-prescription)))

(local
 (defthm dg1-alg
   (implies (and (realp x) (realp y) (realp a) (not (equal x y)))
            (equal (/ (- (g1 a x) (g1 a y)) (- x y))
                   (- (- (* 1/2 (/ (- (tf x) (tf y)) (- x y))) (* 1/2 (tf1 x)))
                      (* 1/2 (- y a) (/ (- (tf1 x) (tf1 y)) (- x y))))))
   :hints (("Goal" :use ((:instance div-intro (n (- (g1 a x) (g1 a y))) (d (- x y)) (r (- (- (* 1/2 (/ (- (tf x) (tf y)) (- x y))) (* 1/2 (tf1 x)))
                      (* 1/2 (- y a) (/ (- (tf1 x) (tf1 y)) (- x y)))))))))
   :rule-classes nil))

(local
 (defthm dgg-alg
   (implies (and (realp x) (realp y) (realp a) (not (equal x y)))
            (equal (/ (- (gg a x) (gg a y)) (- x y))
                   (- (- (/ (- (int-tf a x) (int-tf a y)) (- x y))
                         (* 1/2 (+ (tf a) (tf x))))
                      (* 1/2 (- y a) (/ (- (tf x) (tf y)) (- x y))))))
   :hints (("Goal" :use ((:instance div-intro (n (- (gg a x) (gg a y))) (d (- x y)) (r (- (- (/ (- (int-tf a x) (int-tf a y)) (- x y))
                         (* 1/2 (+ (tf a) (tf x))))
                      (* 1/2 (- y a) (/ (- (tf x) (tf y)) (- x y)))))))))
   :rule-classes nil))

(local
 (defthm dsq-alg
   (implies (and (realp x) (realp y) (realp a) (not (equal x y)))
            (equal (/ (- (* (- x a) (- x a)) (* (- y a) (- y a))) (- x y))
                   (+ (- x a) (- y a))))
   :hints (("Goal" :use ((:instance div-intro (n (- (* (- x a) (- x a)) (* (- y a) (- y a)))) (d (- x y)) (r (+ (- x a) (- y a)))))))
   :rule-classes nil))

(local
 (defthm dcube-alg
   (implies (and (realp x) (realp y) (realp a) (not (equal x y)))
            (equal (/ (- (* (- x a) (- x a) (- x a)) (* (- y a) (- y a) (- y a))) (- x y))
                   (+ (* (- x a) (- x a)) (* (- x a) (- y a)) (* (- y a) (- y a)))))
   :hints (("Goal" :use ((:instance div-intro (n (- (* (- x a) (- x a) (- x a)) (* (- y a) (- y a) (- y a)))) (d (- x y)) (r (+ (* (- x a) (- x a)) (* (- x a) (- y a)) (* (- y a) (- y a))))))))
   :rule-classes nil))

(local
 (defthm dg1
   (implies (and (standardp a) (standardp x)
                 (inside-interval-p a (tf-domain))
                 (inside-interval-p x (tf-domain))
                 (inside-interval-p y (tf-domain))
                 (i-close x y) (not (= x y)))
            (i-close (/ (- (g1 a x) (g1 a y)) (- x y))
                     (- (* 1/2 (- x a) (tf2 x)))))
   :hints (("Goal"
            :use ((:instance dg1-alg)
                  (:instance tf1-is-derivative-of-tf (x1 y))
                  (:instance tf2-is-derivative-of-tf1 (x1 y))
                  (:instance dg1-gen
                             (q1 (/ (- (tf x) (tf y)) (- x y)))
                             (f1 (tf1 x))
                             (q2 (/ (- (tf1 x) (tf1 y)) (- x y)))
                             (f2 (tf2 x)))
                  (:instance close-subst
                             (u (/ (- (g1 a x) (g1 a y)) (- x y)))
                             (v (- (- (* 1/2 (/ (- (tf x) (tf y)) (- x y))) (* 1/2 (tf1 x)))
                                   (* 1/2 (- y a) (/ (- (tf1 x) (tf1 y)) (- x y)))))
                             (w (- (* 1/2 (- x a) (tf2 x))))))
            :in-theory (disable tf1-is-derivative-of-tf tf2-is-derivative-of-tf1
                                g1 i-close)))))

(local
 (defthm dgg
   (implies (and (standardp a) (standardp x)
                 (inside-interval-p a (tf-domain))
                 (inside-interval-p x (tf-domain))
                 (inside-interval-p y (tf-domain))
                 (i-close x y) (not (= x y)))
            (i-close (/ (- (gg a x) (gg a y)) (- x y))
                     (g1 a x)))
   :hints (("Goal"
            :use ((:instance dgg-alg)
                  (:instance tf1-is-derivative-of-tf (x1 y))
                  (:instance ftc-1-tf (a a) (b x) (c y))
                  (:instance dgg-gen
                             (q1 (/ (- (int-tf a x) (int-tf a y)) (- x y)))
                             (fx (tf x))
                             (fa (tf a))
                             (q2 (/ (- (tf x) (tf y)) (- x y)))
                             (f1 (tf1 x)))
                  (:instance close-subst
                             (u (/ (- (gg a x) (gg a y)) (- x y)))
                             (v (- (- (/ (- (int-tf a x) (int-tf a y)) (- x y))
                                      (* 1/2 (+ (tf a) (tf x))))
                                   (* 1/2 (- y a) (/ (- (tf x) (tf y)) (- x y)))))
                             (w (- (* 1/2 (- (tf x) (tf a))) (* 1/2 (- x a) (tf1 x))))))
            :in-theory (disable tf1-is-derivative-of-tf ftc-1-tf
                                gg i-close)))))

(local
 (defthm dsq
   (implies (and (standardp a) (standardp x)
                 (inside-interval-p a (tf-domain))
                 (inside-interval-p x (tf-domain))
                 (inside-interval-p y (tf-domain))
                 (i-close x y) (not (= x y)))
            (i-close (/ (- (* (- x a) (- x a)) (* (- y a) (- y a))) (- x y))
                     (* 2 (- x a))))
   :hints (("Goal"
            :use ((:instance dsq-alg)
                  (:instance dsq-gen)
                  (:instance close-subst
                             (u (/ (- (* (- x a) (- x a)) (* (- y a) (- y a))) (- x y)))
                             (v (+ (- x a) (- y a)))
                             (w (* 2 (- x a)))))
            :in-theory (disable i-close)))))

(local
 (defthm dcube
   (implies (and (standardp a) (standardp x)
                 (inside-interval-p a (tf-domain))
                 (inside-interval-p x (tf-domain))
                 (inside-interval-p y (tf-domain))
                 (i-close x y) (not (= x y)))
            (i-close (/ (- (* (- x a) (- x a) (- x a)) (* (- y a) (- y a) (- y a))) (- x y))
                     (* 3 (- x a) (- x a))))
   :hints (("Goal"
            :use ((:instance dcube-alg)
                  (:instance dcube-gen)
                  (:instance close-subst
                             (u (/ (- (* (- x a) (- x a) (- x a)) (* (- y a) (- y a) (- y a))) (- x y)))
                             (v (+ (* (- x a) (- x a)) (* (- x a) (- y a)) (* (- y a) (- y a))))
                             (w (* 3 (- x a) (- x a)))))
            :in-theory (disable i-close)))))

;;; ------------------------------------------------------------------
;;; First comparison: |g1(p,x)| <= M/4 (x-p)^2
;;; ------------------------------------------------------------------

(local
 (defthm product-nonneg
   (implies (and (realp u) (realp v) (<= 0 u) (<= 0 v))
            (<= 0 (* u v)))
   :rule-classes nil))

(local
 (defthm tf2-bound-facts
   (implies (inside-interval-p x (tf-domain))
            (and (<= 0 (+ (tf2-bound) (tf2 x)))
                 (<= 0 (- (tf2-bound) (tf2 x)))))
   :hints (("Goal" :use ((:instance tf2-bounded))
            :in-theory (disable tf2-bounded)))
   :rule-classes nil))

(local
 (defun mfa (p x)
   (realfix (+ (* (* 1/4 (tf2-bound)) (* (- x p) (- x p)))
               (* -1 (g1 p x))))))
(local
 (defun mfa1 (p x)
   (realfix (+ (* (* 1/4 (tf2-bound)) (* 2 (- x p)))
               (* -1 (- (* 1/2 (- x p) (tf2 x))))))))
(local
 (defun mfb (p x)
   (realfix (+ (* (* 1/4 (tf2-bound)) (* (- x p) (- x p)))
               (* 1 (g1 p x))))))
(local
 (defun mfb1 (p x)
   (realfix (+ (* (* 1/4 (tf2-bound)) (* 2 (- x p)))
               (* 1 (- (* 1/2 (- x p) (tf2 x))))))))

(local
 (defthm mfa-deriv
   (implies (and (standardp p)
                 (standardp x)
                 (inside-interval-p p (tf-domain))
                 (inside-interval-p x (tf-domain))
                 (inside-interval-p y (tf-domain))
                 (i-close x y) (not (= x y)))
            (i-close (/ (- (mfa p x) (mfa p y)) (- x y)) (mfa1 p x)))
   :hints (("Goal"
            :use ((:instance dsq (a p))
                  (:instance dg1 (a p))
                  (:instance dq-linear
                             (c (* 1/4 (tf2-bound))) (d -1)
                             (fx (* (- x p) (- x p))) (fy (* (- y p) (- y p)))
                             (f1 (* 2 (- x p)))
                             (gx (g1 p x)) (gy (g1 p y))
                             (g1v (- (* 1/2 (- x p) (tf2 x))))))
            :in-theory (disable dsq dg1 g1 i-close)))))

(local
 (defthm mfb-deriv
   (implies (and (standardp p)
                 (standardp x)
                 (inside-interval-p p (tf-domain))
                 (inside-interval-p x (tf-domain))
                 (inside-interval-p y (tf-domain))
                 (i-close x y) (not (= x y)))
            (i-close (/ (- (mfb p x) (mfb p y)) (- x y)) (mfb1 p x)))
   :hints (("Goal"
            :use ((:instance dsq (a p))
                  (:instance dg1 (a p))
                  (:instance dq-linear
                             (c (* 1/4 (tf2-bound))) (d 1)
                             (fx (* (- x p) (- x p))) (fy (* (- y p) (- y p)))
                             (f1 (* 2 (- x p)))
                             (gx (g1 p x)) (gy (g1 p y))
                             (g1v (- (* 1/2 (- x p) (tf2 x))))))
            :in-theory (disable dsq dg1 g1 i-close)))))

(local
 (defthm mfa1-nonneg
   (implies (and (inside-interval-p p (tf-domain))
                 (inside-interval-p x (tf-domain))
                 (<= p x))
            (<= 0 (mfa1 p x)))
   :hints (("Goal"
            :use ((:instance tf2-bound-facts)
                  (:instance product-nonneg
                             (u (- x p)) (v (+ (tf2-bound) (tf2 x)))))))))

(local
 (defthm mfb1-nonneg
   (implies (and (inside-interval-p p (tf-domain))
                 (inside-interval-p x (tf-domain))
                 (<= p x))
            (<= 0 (mfb1 p x)))
   :hints (("Goal"
            :use ((:instance tf2-bound-facts)
                  (:instance product-nonneg
                             (u (- x p)) (v (- (tf2-bound) (tf2 x)))))))))

(local (in-theory (disable mfa mfa1 mfb mfb1)))

(local
 (defthm mfa-mono
   (implies (and (inside-interval-p p (tf-domain))
                 (inside-interval-p b (tf-domain))
                 (<= p b))
            (<= (mfa p p) (mfa p b)))
   :hints (("Goal"
            :by (:functional-instance mf-mono (mf mfa) (mf1 mfa1))
            :in-theory (union-theories '(mfa-deriv mfa1-nonneg
                                         (:type-prescription mfa)
                                         (:type-prescription mfa1))
                                       (theory 'minimal-theory))))))

(local
 (defthm mfb-mono
   (implies (and (inside-interval-p p (tf-domain))
                 (inside-interval-p b (tf-domain))
                 (<= p b))
            (<= (mfb p p) (mfb p b)))
   :hints (("Goal"
            :by (:functional-instance mf-mono (mf mfb) (mf1 mfb1))
            :in-theory (union-theories '(mfb-deriv mfb1-nonneg
                                         (:type-prescription mfb)
                                         (:type-prescription mfb1))
                                       (theory 'minimal-theory))))))

(local
 (defthm g1-bound
   (implies (and (inside-interval-p p (tf-domain))
                 (inside-interval-p b (tf-domain))
                 (<= p b))
            (and (<= (g1 p b) (* 1/4 (tf2-bound) (- b p) (- b p)))
                 (<= (- (g1 p b)) (* 1/4 (tf2-bound) (- b p) (- b p)))))
   :hints (("Goal"
            :use ((:instance mfa-mono)
                  (:instance mfb-mono))
            :in-theory (enable mfa mfb)))
   :rule-classes nil))

;;; ------------------------------------------------------------------
;;; Second comparison: |gg(p,x)| <= M/12 (x-p)^3
;;; ------------------------------------------------------------------

(local
 (defun mfc (p x)
   (realfix (+ (* (* 1/12 (tf2-bound)) (* (- x p) (- x p) (- x p)))
               (* -1 (gg p x))))))
(local
 (defun mfc1 (p x)
   (realfix (+ (* (* 1/12 (tf2-bound)) (* 3 (- x p) (- x p)))
               (* -1 (g1 p x))))))
(local
 (defun mfd (p x)
   (realfix (+ (* (* 1/12 (tf2-bound)) (* (- x p) (- x p) (- x p)))
               (* 1 (gg p x))))))
(local
 (defun mfd1 (p x)
   (realfix (+ (* (* 1/12 (tf2-bound)) (* 3 (- x p) (- x p)))
               (* 1 (g1 p x))))))

(local
 (defthm mfc-deriv
   (implies (and (standardp p)
                 (standardp x)
                 (inside-interval-p p (tf-domain))
                 (inside-interval-p x (tf-domain))
                 (inside-interval-p y (tf-domain))
                 (i-close x y) (not (= x y)))
            (i-close (/ (- (mfc p x) (mfc p y)) (- x y)) (mfc1 p x)))
   :hints (("Goal"
            :use ((:instance dcube (a p))
                  (:instance dgg (a p))
                  (:instance dq-linear
                             (c (* 1/12 (tf2-bound))) (d -1)
                             (fx (* (- x p) (- x p) (- x p)))
                             (fy (* (- y p) (- y p) (- y p)))
                             (f1 (* 3 (- x p) (- x p)))
                             (gx (gg p x)) (gy (gg p y))
                             (g1v (g1 p x))))
            :in-theory (disable dcube dgg g1 gg i-close)))))

(local
 (defthm mfd-deriv
   (implies (and (standardp p)
                 (standardp x)
                 (inside-interval-p p (tf-domain))
                 (inside-interval-p x (tf-domain))
                 (inside-interval-p y (tf-domain))
                 (i-close x y) (not (= x y)))
            (i-close (/ (- (mfd p x) (mfd p y)) (- x y)) (mfd1 p x)))
   :hints (("Goal"
            :use ((:instance dcube (a p))
                  (:instance dgg (a p))
                  (:instance dq-linear
                             (c (* 1/12 (tf2-bound))) (d 1)
                             (fx (* (- x p) (- x p) (- x p)))
                             (fy (* (- y p) (- y p) (- y p)))
                             (f1 (* 3 (- x p) (- x p)))
                             (gx (gg p x)) (gy (gg p y))
                             (g1v (g1 p x))))
            :in-theory (disable dcube dgg g1 gg i-close)))))

(local
 (defthm mfc1-nonneg
   (implies (and (inside-interval-p p (tf-domain))
                 (inside-interval-p x (tf-domain))
                 (<= p x))
            (<= 0 (mfc1 p x)))
   :hints (("Goal"
            :use ((:instance g1-bound (b x)))
            :in-theory (disable g1)))))

(local
 (defthm mfd1-nonneg
   (implies (and (inside-interval-p p (tf-domain))
                 (inside-interval-p x (tf-domain))
                 (<= p x))
            (<= 0 (mfd1 p x)))
   :hints (("Goal"
            :use ((:instance g1-bound (b x)))
            :in-theory (disable g1)))))

(local (in-theory (disable mfc mfc1 mfd mfd1)))

(local
 (defthm mfc-mono
   (implies (and (inside-interval-p p (tf-domain))
                 (inside-interval-p b (tf-domain))
                 (<= p b))
            (<= (mfc p p) (mfc p b)))
   :hints (("Goal"
            :by (:functional-instance mf-mono (mf mfc) (mf1 mfc1))
            :in-theory (union-theories '(mfc-deriv mfc1-nonneg
                                         (:type-prescription mfc)
                                         (:type-prescription mfc1))
                                       (theory 'minimal-theory))))))

(local
 (defthm mfd-mono
   (implies (and (inside-interval-p p (tf-domain))
                 (inside-interval-p b (tf-domain))
                 (<= p b))
            (<= (mfd p p) (mfd p b)))
   :hints (("Goal"
            :by (:functional-instance mf-mono (mf mfd) (mf1 mfd1))
            :in-theory (union-theories '(mfd-deriv mfd1-nonneg
                                         (:type-prescription mfd)
                                         (:type-prescription mfd1))
                                       (theory 'minimal-theory))))))

(local
 (defthm gg-p-p
   (equal (gg p p) 0)))

(local
 (defthm mfc-mfd-p-p
   (and (equal (mfc p p) 0)
        (equal (mfd p p) 0))
   :hints (("Goal" :in-theory (e/d (mfc mfd) (gg))))))

(local
 (defthm mfc-mfd-expand
   (implies (and (realp p) (realp b))
            (and (equal (mfc p b)
                        (- (* 1/12 (tf2-bound) (- b p) (- b p) (- b p)) (gg p b)))
                 (equal (mfd p b)
                        (+ (* 1/12 (tf2-bound) (- b p) (- b p) (- b p)) (gg p b)))))
   :hints (("Goal" :in-theory (e/d (mfc mfd) (gg))))
   :rule-classes nil))

(local
 (defthm gg-bound
   (implies (and (inside-interval-p p (tf-domain))
                 (inside-interval-p b (tf-domain))
                 (<= p b))
            (<= (abs (gg p b)) (* 1/12 (tf2-bound) (- b p) (- b p) (- b p))))
   :hints (("Goal"
            :use ((:instance mfc-mono)
                  (:instance mfd-mono)
                  (:instance mfc-mfd-expand))
            :in-theory (e/d () (gg (:executable-counterpart gg)
                                   mfc-mono mfd-mono
                                   (:executable-counterpart mfc)
                                   (:executable-counterpart mfd)))))))

;;; ------------------------------------------------------------------
;;; Summing over the partition
;;; ------------------------------------------------------------------

(local
 (defthm partition-car-<=-last
   (implies (partitionp p)
            (<= (car p) (car (last p))))
   :rule-classes (:rewrite :linear)))

(local
 (defthm partition-cadr-inside
   (implies (and (partitionp p)
                 (consp (cdr p))
                 (inside-interval-p (car p) (tf-domain))
                 (inside-interval-p (car (last p)) (tf-domain)))
            (inside-interval-p (cadr p) (tf-domain)))
   :hints (("Goal"
            :use ((:instance partition-car-<=-last (p (cdr p)))
                  (:instance inside-interval-p-squeeze
                             (a (car p)) (b (car (last p))) (c (cadr p))
                             (interval (tf-domain))))
            :in-theory (disable partition-car-<=-last inside-interval-p-squeeze)))))

(local
 (defthm trapezoid-step
   (implies (and (inside-interval-p a (tf-domain))
                 (inside-interval-p b (tf-domain))
                 (inside-interval-p l (tf-domain))
                 (<= a b)
                 (realp s) (realp tr)
                 (<= (abs (- (int-tf b l) tr)) (* (/ (tf2-bound) 12) s)))
            (<= (abs (- (int-tf a l)
                        (+ (* (- b a) (/ (+ (tf a) (tf b)) 2)) tr)))
                (* (/ (tf2-bound) 12)
                   (+ (expt (- b a) 3) s))))
   :hints (("Goal"
            :use ((:instance gg-bound (p a) (b b))
                  (:instance split-int-tf (a a) (c b) (b l)))
            :in-theory (disable gg-bound split-int-tf)))
   :rule-classes nil))

(local
 (defthm last-cdr-partition
   (implies (consp (cdr p))
            (equal (last p) (last (cdr p))))))

(local
 (defthm realp-trapezoid-tf
   (implies (partitionp p)
            (realp (trapezoid-tf p)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm realp-sum-cubed-deltas
   (implies (partitionp p)
            (realp (sum-cubed-deltas p)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm trapezoid-tf-open
   (implies (and (consp p) (consp (cdr p)))
            (equal (trapezoid-tf p)
                   (+ (* (- (cadr p) (car p)) (/ (+ (tf (car p)) (tf (cadr p))) 2))
                      (trapezoid-tf (cdr p)))))))

(local
 (defthm sum-cubed-deltas-open
   (implies (and (consp p) (consp (cdr p)))
            (equal (sum-cubed-deltas p)
                   (+ (expt (- (cadr p) (car p)) 3) (sum-cubed-deltas (cdr p)))))))

(local
 (defthm partitionp-open
   (implies (and (partitionp p) (consp (cdr p)))
            (and (partitionp (cdr p))
                 (< (car p) (cadr p))))))

(defthm trapezoid-rule-error
  (implies (and (partitionp p)
                (inside-interval-p (car p) (tf-domain))
                (inside-interval-p (car (last p)) (tf-domain)))
           (<= (abs (- (int-tf (car p) (car (last p))) (trapezoid-tf p)))
               (* (/ (tf2-bound) 12) (sum-cubed-deltas p))))
  :hints (("Goal"
           :induct (sum-cubed-deltas p))
          ("Subgoal *1/1"
           :use ((:instance trapezoid-step
                            (a (car p)) (b (cadr p)) (l (car (last p)))
                            (tr (trapezoid-tf (cdr p)))
                            (s (sum-cubed-deltas (cdr p))))
                 (:instance partition-cadr-inside)
                 (:instance partitionp-open))
           :in-theory (union-theories '(last-cdr-partition realp-trapezoid-tf realp-sum-cubed-deltas
                                        trapezoid-tf-open sum-cubed-deltas-open)
                                      (theory 'minimal-theory)))))

(local
 (defthm cube-le
   (implies (and (realp h) (realp m) (< 0 h) (<= h m))
            (<= (expt h 3) (* h m m)))
   :hints (("Goal"
            :use ((:instance product-nonneg (u h) (v (- (* m m) (* h h))))
                  (:instance product-nonneg (u (- m h)) (v (+ m h))))))
   :rule-classes nil))

(local
 (defthm sum-cubed-deltas-bound
   (implies (and (partitionp p)
                 (realp m)
                 (<= (mesh p) m))
            (<= (sum-cubed-deltas p)
                (* (- (car (last p)) (car p)) m m)))
   :hints (("Goal"
            :induct (sum-cubed-deltas p))
           ("Subgoal *1/1"
            :use ((:instance cube-le (h (- (cadr p) (car p)))))))))

(local
 (defthm realp-mesh-partition
   (implies (partitionp p)
            (realp (mesh p)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm realp-last-partition
   (implies (partitionp p)
            (realp (car (last p))))
   :rule-classes nil))

(local
 (defthm final-mesh-lemma
   (implies (and (realp e) (realp s) (realp d) (realp m)
                 (<= (abs e) (* (/ (tf2-bound) 12) s))
                 (<= s (* d m m)))
            (<= (abs e) (* (/ (tf2-bound) 12) d (expt m 2))))
   :hints (("Goal"
            :use ((:instance product-nonneg
                             (u (/ (tf2-bound) 12))
                             (v (- (* d m m) s))))))
   :rule-classes nil))

(defthm trapezoid-rule-error-mesh
  (implies (and (partitionp p)
                (inside-interval-p (car p) (tf-domain))
                (inside-interval-p (car (last p)) (tf-domain)))
           (<= (abs (- (int-tf (car p) (car (last p))) (trapezoid-tf p)))
               (* (/ (tf2-bound) 12) (- (car (last p)) (car p)) (expt (mesh p) 2))))
  :hints (("Goal"
           :use ((:instance trapezoid-rule-error)
                 (:instance sum-cubed-deltas-bound (m (mesh p)))
                 (:instance final-mesh-lemma
                            (e (- (int-tf (car p) (car (last p))) (trapezoid-tf p)))
                            (s (sum-cubed-deltas p))
                            (d (- (car (last p)) (car p)))
                            (m (mesh p)))
                 (:instance realp-mesh-partition)
                 (:instance realp-trapezoid-tf)
                 (:instance realp-sum-cubed-deltas)
                 (:instance realp-int-tf (a (car p)) (b (car (last p))))
                 (:instance partitionp-forward-to-realp-car)
                 (:instance realp-last-partition))
           :in-theory (theory 'minimal-theory))))
