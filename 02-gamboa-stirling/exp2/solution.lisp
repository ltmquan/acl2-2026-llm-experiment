(in-package "ACL2")

(include-book "defs")

;;; ---------------- generic monotonicity (MVT) ----------------


(include-book "nonstd/nsa/derivatives" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))

(encapsulate
 ((mf (x) t)
  (mf-prime (x) t)
  (mf-domain () t))
 (local (defun mf (x) (declare (ignore x)) 0))
 (local (defun mf-prime (x) (declare (ignore x)) 0))
 (local (defun mf-domain () (interval 0 1)))
 (defthm intervalp-mf-domain
   (interval-p (mf-domain))
   :rule-classes (:type-prescription :rewrite))
 (defthm mf-domain-real
   (implies (inside-interval-p x (mf-domain))
            (realp x))
   :rule-classes (:forward-chaining))
 (defthm mf-domain-non-trivial
   (or (null (interval-left-endpoint (mf-domain)))
       (null (interval-right-endpoint (mf-domain)))
       (< (interval-left-endpoint (mf-domain))
          (interval-right-endpoint (mf-domain))))
   :rule-classes nil)
 (defthm mf-real
   (realp (mf x))
   :rule-classes (:rewrite :type-prescription))
 (defthm mf-prime-real
   (realp (mf-prime x))
   :rule-classes (:rewrite :type-prescription))
 (defthm mf-deriv
   (implies (and (standardp x)
                 (inside-interval-p x (mf-domain))
                 (inside-interval-p y (mf-domain))
                 (i-close x y) (not (= x y)))
            (i-close (/ (- (mf x) (mf y)) (- x y))
                     (mf-prime x))))
 (defthm mf-prime-nonneg
   (implies (inside-interval-p x (mf-domain))
            (<= 0 (mf-prime x)))))

(defthm-std mf-prime-standard
  (implies (standardp x) (standardp (mf-prime x))))

(defthm mf-differentiable
  (implies (and (standardp x)
                (inside-interval-p x (mf-domain))
                (inside-interval-p y1 (mf-domain))
                (inside-interval-p y2 (mf-domain))
                (i-close x y1) (not (= x y1))
                (i-close x y2) (not (= x y2)))
           (and (i-limited (/ (- (mf x) (mf y1)) (- x y1)))
                (i-close (/ (- (mf x) (mf y1)) (- x y1))
                         (/ (- (mf x) (mf y2)) (- x y2)))))
  :hints (("Goal" :use ((:instance mf-deriv (y y1))
                        (:instance mf-prime-standard)
                        (:instance standards-are-limited (x (mf-prime x)))
                        (:instance mf-deriv (y y2))
                        (:instance i-close-limited
                                   (x (mf-prime x))
                                   (y (/ (- (mf x) (mf y1)) (- x y1))))
                        (:instance i-close-symmetric
                                   (x (/ (- (mf x) (mf y2)) (- x y2)))
                                   (y (mf-prime x)))
                        (:instance i-close-transitive
                                   (x (/ (- (mf x) (mf y1)) (- x y1)))
                                   (y (mf-prime x))
                                   (z (/ (- (mf x) (mf y2)) (- x y2)))))
           :in-theory (disable mf-deriv i-close-limited i-close-symmetric mf-prime-standard standards-are-limited
                               i-close-transitive))))

(defun mf-default-subdomain ()
  (let ((left (interval-left-endpoint (mf-domain)))
        (right (interval-right-endpoint (mf-domain))))
    (if (null left)
        (if (null right)
            (interval 0 1)
          (interval (- right 2) (- right 1)))
      (if (null right)
          (interval (+ left 1) (+ left 2))
        (interval (+ left (* 1/3 (- right left)))
                  (+ left (* 2/3 (- right left))))))))

(defun mf-subdomain (a b)
  (if (and (inside-interval-p a (mf-domain))
           (inside-interval-p b (mf-domain))
           (< a b))
      (interval a b)
    (mf-default-subdomain)))

(defthm mf-default-subdomain-is-subdomain
  (subinterval-p (mf-default-subdomain) (mf-domain))
  :hints (("Goal"
           :use ((:instance interval-p (interval (mf-domain))))
           :in-theory (enable interval-definition-theory))))

(defthm mf-default-subdomain-props
  (and (interval-left-inclusive-p (mf-default-subdomain))
       (interval-right-inclusive-p (mf-default-subdomain))
       (realp (interval-left-endpoint (mf-default-subdomain)))
       (realp (interval-right-endpoint (mf-default-subdomain)))
       (< (interval-left-endpoint (mf-default-subdomain))
          (interval-right-endpoint (mf-default-subdomain))))
  :hints (("Goal" :use (:instance mf-domain-non-trivial))))

(defthm subinterval-a-b
  (implies (and (interval-p i)
                (inside-interval-p a i) (inside-interval-p b i) (< a b))
           (subinterval-p (interval a b) i))
  :hints (("Goal" :in-theory (enable interval-definition-theory))))

(in-theory (disable mf-default-subdomain (:executable-counterpart mf-default-subdomain)))

(defthm mf-subdomain-is-subdomain
  (subinterval-p (mf-subdomain a b) (mf-domain)))

(defthm mf-subdomain-props
  (and (interval-left-inclusive-p (mf-subdomain a b))
       (interval-right-inclusive-p (mf-subdomain a b))
       (realp (interval-left-endpoint (mf-subdomain a b)))
       (realp (interval-right-endpoint (mf-subdomain a b)))
       (< (interval-left-endpoint (mf-subdomain a b))
          (interval-right-endpoint (mf-subdomain a b)))))

(in-theory (disable mf-subdomain (:executable-counterpart mf-subdomain)))

(defun differential-mf (x eps)
  (/ (- (mf (+ x eps)) (mf x)) eps))

(defthm differential-mf-limited
  (implies (and (standardp x)
                (inside-interval-p x (mf-domain))
                (inside-interval-p (+ x eps) (mf-domain))
                (i-small eps)
                (not (equal eps 0)))
           (i-limited (differential-mf x eps)))
  :hints (("Goal" :use ((:instance mf-differentiable (y1 (+ x eps)) (y2 (+ x eps)))
                        (:instance i-close-to-small-sum (x x) (eps eps)))
           :in-theory (disable mf-differentiable i-close-to-small-sum))))
(in-theory (disable differential-mf))

(defun-std derivative-mf (x)
  (if (inside-interval-p x (mf-domain))
      (if (inside-interval-p (+ x (/ (i-large-integer))) (mf-domain))
          (standard-part (differential-mf x (/ (i-large-integer))))
        (if (inside-interval-p (- x (/ (i-large-integer))) (mf-domain))
            (standard-part (differential-mf x (- (/ (i-large-integer)))))
          'error))
    'error))

(defun-sk exists-mvt-point-mf (a b)
  (exists (x)
          (and (inside-interval-p x (mf-subdomain a b))
               (not (equal x (interval-left-endpoint (mf-subdomain a b))))
               (not (equal x (interval-right-endpoint (mf-subdomain a b))))
               (equal (derivative-mf x)
                      (/ (- (mf (interval-right-endpoint (mf-subdomain a b)))
                            (mf (interval-left-endpoint (mf-subdomain a b))))
                         (- (interval-right-endpoint (mf-subdomain a b))
                            (interval-left-endpoint (mf-subdomain a b))))))))

(defthm mvt-mf
  (exists-mvt-point-mf a b)
  :hints (("Goal"
           :by (:functional-instance mvt-theorem-sk
                                       (rdfn mf)
                                       (rdfn-domain mf-domain)
                                       (rdfn-subdomain (lambda () (mf-subdomain a b)))
                                       (differential-rdfn differential-mf)
                                       (derivative-rdfn derivative-mf)
                                       (exists-mvt-point (lambda () (exists-mvt-point-mf a b)))
                                       (exists-mvt-point-witness
                                        (lambda () (exists-mvt-point-mf-witness a b)))))
          ("Subgoal 4" :use ((:instance mf-domain-non-trivial)))
          ("Subgoal 1" :in-theory (enable differential-mf))
          ("Subgoal 5" :use ((:instance mf-differentiable))
           :in-theory (disable mf-differentiable mf-deriv))))

(defthm small-lt-standard-gap
  (implies (and (realp x) (realp b) (standardp x) (standardp b) (< x b)
                (realp eps) (i-small eps))
           (< (+ x eps) b))
  :hints (("Goal" :use ((:instance standard-small-is-zero (x (- b x)))
                        (:instance small-<-non-small (x eps) (y (- b x)))))))

(defthm small-gt-standard-gap
  (implies (and (realp x) (realp a) (standardp x) (standardp a) (< a x)
                (realp eps) (i-small eps))
           (< a (- x eps)))
  :hints (("Goal" :use ((:instance standard-small-is-zero (x (- x a)))
                        (:instance small-<-non-small (x eps) (y (- x a)))))))

(defthm differential-mf-alt
  (implies (and (acl2-numberp x) (acl2-numberp eps))
           (equal (/ (- (mf x) (mf (+ x eps))) (- x (+ x eps)))
                  (differential-mf x eps)))
  :hints (("Goal" :in-theory (enable differential-mf))))

(defthm i-close-x-x+eps
  (implies (and (acl2-numberp x) (standardp x) (i-small eps))
           (i-close x (+ x eps)))
  :hints (("Goal" :use i-close-to-small-sum)))

(defthm std-part-differential-mf
  (implies (and (standardp x)
                (inside-interval-p x (mf-domain))
                (inside-interval-p (+ x eps) (mf-domain))
                (i-small eps) (realp eps)
                (not (equal eps 0)))
           (equal (standard-part (differential-mf x eps))
                  (mf-prime x)))
  :hints (("Goal"
           :use ((:instance mf-deriv (x x) (y (+ x eps)))
                 (:instance mf-prime-standard)
                 (:instance differential-mf-alt)
                 (:instance i-close-x-x+eps)
                 (:instance close-x-y->same-standard-part
                            (y (differential-mf x eps))
                            (x (mf-prime x))))
           :in-theory (disable mf-deriv differential-mf-alt mf-prime-standard i-close-x-x+eps
                               close-x-y->same-standard-part))))

(defthm-std derivative-mf-is-prime
  (implies (and (inside-interval-p a (mf-domain))
                (inside-interval-p b (mf-domain))
                (realp x) (< a x) (< x b))
           (equal (derivative-mf x) (mf-prime x)))
  :hints (("Goal"
           :use ((:instance small-lt-standard-gap (eps (/ (i-large-integer))))
                 (:instance inside-interval-p-squeeze (a a) (b b) (c (+ x (/ (i-large-integer))))
                            (interval (mf-domain)))
                 (:instance inside-interval-p-squeeze (a a) (b b) (c x)
                            (interval (mf-domain)))
                 (:instance std-part-differential-mf (eps (/ (i-large-integer)))))
           :in-theory (disable inside-interval-p-squeeze std-part-differential-mf
                               small-lt-standard-gap))))

(defthm slope-nonneg-lemma
  (implies (and (realp a) (realp b) (realp fa) (realp fb) (< a b)
                (<= 0 (+ (- (* fa (/ (+ (- a) b)))) (* fb (/ (+ (- a) b))))))
           (<= fa fb))
  :hints (("Goal" :use ((:instance (:theorem (implies (and (realp x) (realp y) (< 0 y) (<= 0 (* x (/ y)))) (<= 0 x)))
                                   (x (- fb fa)) (y (- b a))))))
  :rule-classes nil)

(defthm mf-monotone
  (implies (and (inside-interval-p a (mf-domain))
                (inside-interval-p b (mf-domain))
                (<= a b))
           (<= (mf a) (mf b)))
  :hints (("Goal" :cases ((= a b) (< a b)))
          ("Subgoal 1"
           :use ((:instance mvt-mf)
                 (:instance derivative-mf-is-prime (x (exists-mvt-point-mf-witness a b)))
                 (:instance mf-prime-nonneg (x (exists-mvt-point-mf-witness a b)))
                 (:instance slope-nonneg-lemma (fa (mf a)) (fb (mf b))))
           :in-theory (e/d (mf-subdomain inside-interval-p) (mvt-mf derivative-mf-is-prime mf-prime-nonneg)))))

(deftheory th-mono (current-theory :here))
;;; ---------------- Wallis integrals ----------------


(include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/sin-cos-minimal" :dir :system)

(deftheory th-sincos (set-difference-theories (current-theory :here) (theory 'th-mono)))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(defthm close-plus-gen
  (implies (and (i-close a b) (i-close c d) (acl2-numberp a) (acl2-numberp b) (acl2-numberp c) (acl2-numberp d))
           (i-close (+ a c) (+ b d)))
  :hints (("Goal" :in-theory (enable i-close)
           :use ((:instance i-small-plus (x (- a b)) (y (- c d)))))))

(defthm close-times-limited
  (implies (and (i-close a b) (i-limited c) (acl2-numberp a) (acl2-numberp b) (acl2-numberp c))
           (i-close (* c a) (* c b)))
  :hints (("Goal" :in-theory (enable i-close)
           :use ((:instance limited*small->small (x c) (y (- a b)))))))

(defthm prod-small
  (implies (and (acl2-numberp a1) (acl2-numberp b1) (acl2-numberp qa) (acl2-numberp qb)
                (acl2-numberp e1) (acl2-numberp e2) (acl2-numberp h)
                (i-limited a1) (i-limited b1) (i-limited qa) (i-limited qb)
                (i-small h) (i-small e1) (i-small e2))
           (i-small (+ (* a1 e2) (* b1 e1) (- (* qb qa h)))))
  :hints (("Goal" :in-theory (disable distributivity limited*small->small)
           :use ((:instance limited*small->small (x a1) (y e2))
                 (:instance limited*small->small (x b1) (y e1))
                 (:instance limited*small->small (x (* qb qa)) (y h))
                 (:instance i-limited-times (x qb) (y qa))
                 (:instance i-small-plus (x (* a1 e2)) (y (* b1 e1)))
                 (:instance i-small-plus (x (+ (* a1 e2) (* b1 e1))) (y (- (* qb qa h))))
                 (:instance i-small-uminus (x (* qb qa h)))))))

(defthm prod-id (equal (- (+ (* a1 qb) (* (- b1 (* qb h)) qa)) (+ (* a1 bb) (* b1 aa)))
                        (+ (* a1 (- qb bb)) (* b1 (- qa aa)) (- (* qb qa h))))
  :rule-classes nil)

(defthm prod-core
  (implies (and (acl2-numberp a1) (acl2-numberp b1) (acl2-numberp qa) (acl2-numberp qb)
                (acl2-numberp aa) (acl2-numberp bb) (acl2-numberp h)
                (i-limited a1) (i-limited b1) (i-limited aa) (i-limited bb) (i-small h)
                (i-close qa aa) (i-close qb bb))
           (i-close (+ (* a1 qb) (* (- b1 (* qb h)) qa)) (+ (* a1 bb) (* b1 aa))))
  :hints (("Goal"
           :use ((:instance i-close-limited (x bb) (y qb))
                 (:instance i-close-limited (x aa) (y qa))
                 (:instance i-close-symmetric (x qb) (y bb))
                 (:instance i-close-symmetric (x qa) (y aa))
                 (:instance prod-small (e1 (- qa aa)) (e2 (- qb bb)))
                 (:instance prod-id))
           :in-theory (e/d (i-close) (i-close-limited i-close-symmetric prod-small distributivity)))))

(defthm quot-id-1
  (implies (and (acl2-numberp h) (not (equal h 0)) (acl2-numberp b1) (acl2-numberp b2))
           (equal (- b1 (* (/ (- b1 b2) h) h)) b2))
  :rule-classes nil)

(defthm quot-id-2
  (implies (and (acl2-numberp h) (not (equal h 0)) (acl2-numberp a1) (acl2-numberp a2)
                (acl2-numberp b1) (acl2-numberp b2))
           (equal (/ (- (* a1 b1) (* a2 b2)) h)
                  (+ (* a1 (/ (- b1 b2) h)) (* b2 (/ (- a1 a2) h)))))
  :rule-classes nil)

(defthm prod-rule
  (implies (and (acl2-numberp a1) (acl2-numberp a2) (acl2-numberp b1) (acl2-numberp b2)
                (acl2-numberp aa) (acl2-numberp bb) (acl2-numberp h) (not (equal h 0))
                (i-limited a1) (i-limited b1) (i-limited aa) (i-limited bb) (i-small h)
                (i-close (/ (- a1 a2) h) aa) (i-close (/ (- b1 b2) h) bb))
           (i-close (/ (- (* a1 b1) (* a2 b2)) h) (+ (* a1 bb) (* b1 aa))))
  :hints (("Goal" :use ((:instance prod-core (qa (/ (- a1 a2) h)) (qb (/ (- b1 b2) h)))
                        (:instance quot-id-1)
                        (:instance quot-id-2))
           :in-theory nil))
  :rule-classes nil)

(defthm-std expt-standard-2
  (implies (and (standardp x) (standardp n))
           (standardp (expt x n))))

(defthm sin-real (implies (realp x) (realp (acl2-sine x))))
(defthm cos-real (implies (realp x) (realp (acl2-cosine x))))

(defun nat-ind (k) (if (zp k) 0 (nat-ind (- k 1))))

(defthm mult-eq (implies (equal x y) (equal (* c x) (* c y))) :rule-classes nil)

(defthm pow-alg
  (implies (and (acl2-numberp k) (acl2-numberp a1) (acl2-numberp p) (acl2-numberp b1) (acl2-numberp aa)
                (equal (* (- k 1) (* a1 p)) (* (- k 1) b1)))
           (equal (+ (* a1 (* (- k 1) p aa)) (* b1 aa)) (* k b1 aa)))
  :hints (("Goal" :use ((:instance mult-eq (c aa) (x (* (- k 1) (* a1 p))) (y (* (- k 1) b1))))))
  :rule-classes nil)

(defthm pow-step-abs
  (implies (and (acl2-numberp a1) (acl2-numberp a2) (acl2-numberp b1) (acl2-numberp b2)
                (acl2-numberp aa) (acl2-numberp p) (acl2-numberp k) (acl2-numberp h) (not (equal h 0))
                (i-limited a1) (i-limited b1) (i-limited aa) (i-limited (* (- k 1) p aa)) (i-small h)
                (i-close (/ (- a1 a2) h) aa)
                (i-close (/ (- b1 b2) h) (* (- k 1) p aa))
                (equal (* (- k 1) (* a1 p)) (* (- k 1) b1)))
           (i-close (/ (- (* a1 b1) (* a2 b2)) h) (* k b1 aa)))
  :hints (("Goal" :use ((:instance prod-rule (bb (* (- k 1) p aa)))
                        (:instance pow-alg))
           :in-theory (disable i-close)))
  :rule-classes nil)

(defthm expt-split-1
  (implies (and (integerp k) (<= 1 k) (acl2-numberp s))
           (equal (expt s k) (* s (expt s (- k 1)))))
  :rule-classes nil)

(defthm expt-split-2
  (implies (and (integerp k) (<= 1 k) (acl2-numberp s))
           (equal (* (- k 1) (* s (expt s (- k 2)))) (* (- k 1) (expt s (- k 1)))))
  :hints (("Goal" :cases ((<= 2 k)))
          ("Subgoal 1" :use ((:instance expt-split-1 (k (- k 1))))))
  :rule-classes nil)

(defthm std-k-minus
  (implies (and (standardp k) (acl2-numberp k))
           (and (standardp (- k 1)) (standardp (- k 2)))))

(defthm close-diff-small
  (implies (i-close x y) (i-small (- x y)))
  :hints (("Goal" :in-theory (enable i-close))))

(defthm std-times-3
  (implies (and (standardp a) (standardp b) (standardp c))
           (standardp (* a b c))))

(defthm sin-pow-step
  (implies (and (integerp k) (<= 1 k) (standardp k) (realp x) (standardp x) (realp y)
                (i-close x y) (not (= x y))
                (i-close (/ (- (expt (acl2-sine x) (- k 1)) (expt (acl2-sine y) (- k 1))) (- x y))
                         (* (- k 1) (expt (acl2-sine x) (- k 2)) (acl2-cosine x))))
           (i-close (/ (- (expt (acl2-sine x) k) (expt (acl2-sine y) k)) (- x y))
                    (* k (expt (acl2-sine x) (- k 1)) (acl2-cosine x))))
  :hints (("Goal"
           :use ((:instance pow-step-abs
                            (a1 (acl2-sine x)) (a2 (acl2-sine y))
                            (b1 (expt (acl2-sine x) (- k 1))) (b2 (expt (acl2-sine y) (- k 1)))
                            (aa (acl2-cosine x))
                            (p (expt (acl2-sine x) (- k 2)))
                            (h (- x y)))
                 (:instance expt-split-1 (s (acl2-sine x)))
                 (:instance expt-split-1 (s (acl2-sine y)))
                 (:instance expt-split-2 (s (acl2-sine x)))
                 (:instance acl2-sine-derivative)
                 (:instance standards-are-limited (x (acl2-sine x)))
                 (:instance standards-are-limited (x (acl2-cosine x)))
                 (:instance standards-are-limited (x (expt (acl2-sine x) (- k 1))))
                 (:instance standards-are-limited (x (* (- k 1) (expt (acl2-sine x) (- k 2)) (acl2-cosine x))))
                 (:instance expt-standard-2 (x (acl2-sine x)) (n (- k 1)))
                 (:instance expt-standard-2 (x (acl2-sine x)) (n (- k 2)))
                 (:instance std-times-3 (a (- k 1)) (b (expt (acl2-sine x) (- k 2))) (c (acl2-cosine x)))
                 (:instance close-diff-small))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(std-k-minus sin-real cos-real acl2-sine-standard acl2-cosine-standard
                                        (:type-prescription expt) (:type-prescription acl2-sine)
                                        (:type-prescription acl2-cosine)))))
  :rule-classes nil)

(defthm sin-pow-deriv
  (implies (and (natp k) (standardp k) (realp x) (standardp x) (realp y)
                (i-close x y) (not (= x y)))
           (i-close (/ (- (expt (acl2-sine x) k) (expt (acl2-sine y) k)) (- x y))
                    (* k (expt (acl2-sine x) (- k 1)) (acl2-cosine x))))
  :hints (("Goal" :induct (nat-ind k)
           :in-theory (disable i-close expt acl2-sine acl2-cosine))
          ("Subgoal *1/2" :use ((:instance sin-pow-step)))
          ("Subgoal *1/1" :in-theory (enable expt))))

(defthm std-times-2
  (implies (and (standardp a) (standardp b))
           (standardp (* a b))))

(defthm sin-pow-deriv-m1
  (implies (and (integerp n) (<= 1 n) (standardp n) (realp x) (standardp x) (realp y)
                (i-close x y) (not (= x y)))
           (i-close (/ (- (expt (acl2-sine x) (- n 1)) (expt (acl2-sine y) (- n 1))) (- x y))
                    (* (- n 1) (expt (acl2-sine x) (- n 2)) (acl2-cosine x))))
  :hints (("Goal" :use ((:instance sin-pow-deriv (k (- n 1))))
           :in-theory (disable sin-pow-deriv i-close expt acl2-sine acl2-cosine))))

(defthm std-uminus (implies (standardp a) (standardp (- a))))

(defthm p-deriv
  (implies (and (integerp n) (<= 1 n) (standardp n) (realp x) (standardp x) (realp y)
                (i-close x y) (not (= x y)))
           (i-close (/ (- (* (expt (acl2-sine x) (- n 1)) (acl2-cosine x))
                          (* (expt (acl2-sine y) (- n 1)) (acl2-cosine y)))
                       (- x y))
                    (+ (* (expt (acl2-sine x) (- n 1)) (- (acl2-sine x)))
                       (* (acl2-cosine x) (* (- n 1) (expt (acl2-sine x) (- n 2)) (acl2-cosine x))))))
  :hints (("Goal"
           :use ((:instance prod-rule
                            (a1 (expt (acl2-sine x) (- n 1))) (a2 (expt (acl2-sine y) (- n 1)))
                            (b1 (acl2-cosine x)) (b2 (acl2-cosine y))
                            (aa (* (- n 1) (expt (acl2-sine x) (- n 2)) (acl2-cosine x)))
                            (bb (- (acl2-sine x)))
                            (h (- x y)))
                 (:instance sin-pow-deriv-m1)
                 (:instance acl2-cosine-derivative)
                 (:instance standards-are-limited (x (acl2-sine x)))
                 (:instance standards-are-limited (x (- (acl2-sine x))))
                 (:instance standards-are-limited (x (acl2-cosine x)))
                 (:instance standards-are-limited (x (expt (acl2-sine x) (- n 1))))
                 (:instance standards-are-limited (x (* (- n 1) (expt (acl2-sine x) (- n 2)) (acl2-cosine x))))
                 (:instance expt-standard-2 (x (acl2-sine x)) (n (- n 1)))
                 (:instance expt-standard-2 (x (acl2-sine x)) (n (- n 2)))
                 (:instance std-times-3 (a (- n 1)) (b (expt (acl2-sine x) (- n 2))) (c (acl2-cosine x)))
                 (:instance std-uminus (a (acl2-sine x)))
                 (:instance close-diff-small))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(std-k-minus sin-real cos-real acl2-sine-standard acl2-cosine-standard
                                        natp (:type-prescription expt) (:type-prescription acl2-sine)
                                        (:type-prescription acl2-cosine))))))

(defun wf (n x)
  (declare (xargs :measure (nfix n)))
  (if (zp n) (realfix x)
    (if (equal n 1) (- (acl2-cosine x))
      (+ (- (* (/ n) (* (expt (acl2-sine x) (- n 1)) (acl2-cosine x))))
         (* (/ (- n 1) n) (wf (- n 2) x))))))

(defthm c2-gen
  (implies (equal cc (- 1 (* s s)))
           (equal (* cc e) (- e (* s s e))))
  :rule-classes nil)

(defthm c2-lemma
  (implies (equal (* c c) (- 1 (* s s)))
           (equal (* (* c c) e) (- e (* s s e))))
  :hints (("Goal" :by (:instance c2-gen (cc (* c c)))))
  :rule-classes nil)

(defthm f-alg
  (implies (and (acl2-numberp n) (not (equal n 0)) (acl2-numberp s) (acl2-numberp c)
                (acl2-numberp e0) (acl2-numberp e1) (acl2-numberp en)
                (equal (* s e0) e1) (equal (* s e1) en)
                (equal (* (* c c) e0) (- e0 (* s s e0)))
                (equal (* (* c c) (* e0 (/ n))) (- (* e0 (/ n)) (* s s (* e0 (/ n))))))
           (equal (+ (- (* (/ n) (+ (* e1 (- s)) (* c (* (- n 1) e0 c)))))
                     (* (/ (- n 1) n) e0))
                  en))
  :rule-classes nil)

(defthm quot-lin
  (implies (and (acl2-numberp h) (not (equal h 0)))
           (equal (/ (- (+ (- (* a px)) (* b fx)) (+ (- (* a py)) (* b fy))) h)
                  (+ (- (* a (/ (- px py) h))) (* b (/ (- fx fy) h)))))
  :rule-classes nil)

(defthm lin-close
  (implies (and (acl2-numberp a) (acl2-numberp b) (acl2-numberp q1) (acl2-numberp q2)
                (acl2-numberp t1) (acl2-numberp t2)
                (i-limited a) (i-limited b) (i-close q1 t1) (i-close q2 t2))
           (i-close (+ (- (* a q1)) (* b q2)) (+ (- (* a t1)) (* b t2))))
  :hints (("Goal" :use ((:instance close-times-limited (a q1) (b t1) (c (- a)))
                        (:instance close-times-limited (a q2) (b t2) (c b))
                        (:instance close-plus-gen (a (* (- a) q1)) (b (* (- a) t1)) (c (* b q2)) (d (* b t2))))
           :in-theory (disable close-times-limited close-plus-gen)))
  :rule-classes nil)

(defthm expt-split-3
  (implies (and (integerp n) (<= 2 n) (acl2-numberp s))
           (equal (* s (expt s (- n 2))) (expt s (- n 1))))
  :hints (("Goal" :use ((:instance expt-split-1 (k (- n 1))))))
  :rule-classes nil)

(defthm std-recip (implies (standardp a) (standardp (/ a))))

(defthm f-step
  (implies (and (integerp n) (<= 2 n) (standardp n) (realp x) (standardp x) (realp y)
                (i-close x y) (not (= x y))
                (i-close (/ (- (wf (- n 2) x) (wf (- n 2) y)) (- x y))
                         (expt (acl2-sine x) (- n 2))))
           (i-close (/ (- (wf n x) (wf n y)) (- x y))
                    (expt (acl2-sine x) n)))
  :hints (("Goal"
           :expand ((wf n x) (wf n y))
           :use ((:instance quot-lin (a (/ n)) (b (/ (- n 1) n)) (h (- x y))
                            (px (* (expt (acl2-sine x) (- n 1)) (acl2-cosine x)))
                            (py (* (expt (acl2-sine y) (- n 1)) (acl2-cosine y)))
                            (fx (wf (- n 2) x)) (fy (wf (- n 2) y)))
                 (:instance p-deriv)
                 (:instance lin-close (a (/ n)) (b (/ (- n 1) n))
                            (q1 (/ (- (* (expt (acl2-sine x) (- n 1)) (acl2-cosine x))
                                      (* (expt (acl2-sine y) (- n 1)) (acl2-cosine y)))
                                   (- x y)))
                            (t1 (+ (* (expt (acl2-sine x) (- n 1)) (- (acl2-sine x)))
                                   (* (acl2-cosine x) (* (- n 1) (expt (acl2-sine x) (- n 2)) (acl2-cosine x)))))
                            (q2 (/ (- (wf (- n 2) x) (wf (- n 2) y)) (- x y)))
                            (t2 (expt (acl2-sine x) (- n 2))))
                 (:instance f-alg (s (acl2-sine x)) (c (acl2-cosine x))
                            (e0 (expt (acl2-sine x) (- n 2)))
                            (e1 (expt (acl2-sine x) (- n 1)))
                            (en (expt (acl2-sine x) n)))
                 (:instance expt-split-3 (s (acl2-sine x)))
                 (:instance expt-split-1 (k n) (s (acl2-sine x)))
                 (:instance c2-lemma (c (acl2-cosine x)) (s (acl2-sine x)) (e (expt (acl2-sine x) (- n 2))))
                 (:instance c2-lemma (c (acl2-cosine x)) (s (acl2-sine x)) (e (* (expt (acl2-sine x) (- n 2)) (/ n))))
                 (:instance cos**2->1-sin**2 (x x))
                 (:instance standards-are-limited (x (/ n)))
                 (:instance standards-are-limited (x (/ (- n 1) n)))
                 (:instance std-recip (a n))
                 (:instance std-times-2 (a (- n 1)) (b (/ n))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(std-k-minus sin-real cos-real acl2-sine-standard acl2-cosine-standard
                                        natp zp (:type-prescription expt) (:type-prescription acl2-sine)
                                        (:type-prescription acl2-cosine) (:type-prescription wf))))))

(defthm i-close-uminus
  (implies (i-close x y) (i-close (- x) (- y)))
  :hints (("Goal" :in-theory (enable i-close))))

(defthm f-deriv
  (implies (and (natp n) (standardp n) (realp x) (standardp x) (realp y)
                (i-close x y) (not (= x y)))
           (i-close (/ (- (wf n x) (wf n y)) (- x y))
                    (expt (acl2-sine x) n)))
  :hints (("Goal" :induct (wf n x) :in-theory (disable i-close acl2-sine acl2-cosine))
          ("Subgoal *1/3" :use ((:instance f-step)) :in-theory (disable wf i-close acl2-sine acl2-cosine))
          ("Subgoal *1/2" :use ((:instance acl2-cosine-derivative)
                                (:instance i-close-uminus (x (/ (- (acl2-cosine x) (acl2-cosine y)) (- x y)))
                                           (y (- (acl2-sine x)))))
           :in-theory (disable i-close acl2-sine acl2-cosine acl2-cosine-derivative))
          ("Subgoal *1/1" :in-theory (enable i-close))))


(defthm dist-l (equal (* (+ x y) z) (+ (* x z) (* y z))) :rule-classes nil)

(defthm wf-real (implies (realp x) (realp (wf n x))))

(defun wi (n) (- (wf n (* 1/2 (acl2-pi))) (wf n 0)))

(defthm wi-0 (equal (wi 0) (* 1/2 (acl2-pi))))
(defthm wi-1 (equal (wi 1) 1))

(defthm expt-0-pos (implies (and (integerp k) (<= 1 k)) (equal (expt 0 k) 0)))

(defthm nm1-n
  (implies (and (acl2-numberp n) (not (equal n 0)) (acl2-numberp w))
           (equal (* (/ n) (+ -1 n) w) (- w (* (/ n) w))))
  :hints (("Goal" :use ((:instance dist-l (x -1) (y n) (z (* (/ n) w))))))
  :rule-classes nil)

(defthm wi-rec
  (implies (and (integerp n) (<= 2 n))
           (equal (wi n) (* (/ (- n 1) n) (wi (- n 2)))))
  :hints (("Goal" :expand ((wf n (* 1/2 (acl2-pi))) (wf n 0))
           :use ((:instance nm1-n (w (wf (+ -2 n) 0)))
                 (:instance nm1-n (w (wf (+ -2 n) (* 1/2 (acl2-pi))))))
           :in-theory (disable wf))))

(defthm pi-lt-4-linear (< (acl2-pi) 4) :rule-classes :linear)

(defthm sin-range
  (implies (and (realp x) (<= 0 x) (<= x (* 1/2 (acl2-pi))))
           (and (<= 0 (acl2-sine x)) (<= (acl2-sine x) 1)))
  :hints (("Goal" :use ((:instance acl2-sin-x-positive)
                        (:instance acl2-pi-gross-upper-bound)
                        (:instance sin**2->1-cos**2)
                        (:instance (:theorem (implies (and (realp c)) (<= 0 (* c c)))) (c (acl2-cosine x)))
                        (:instance (:theorem (implies (and (realp s) (< 1 s)) (< 1 (* s s)))) (s (acl2-sine x))))
           :in-theory (disable acl2-sin-x-positive acl2-pi-gross-upper-bound)
           :cases ((= x 0))))
  :rule-classes nil)

(encapsulate (((nn) => *))
  (local (defun nn () 0))
  (defthm natp-nn (natp (nn)) :rule-classes :type-prescription))

(defthm-std nn-standard (standardp (nn)))

(defun gfn (x) (realfix (- (wf (nn) x) (wf (+ 1 (nn)) x))))
(defun gprime (x) (realfix (- (expt (acl2-sine x) (nn)) (expt (acl2-sine x) (+ 1 (nn))))))

(defthm inside-0-pi/2
  (equal (inside-interval-p x (interval 0 (* 1/2 (acl2-pi))))
         (and (realp x) (<= 0 x) (<= x (* 1/2 (acl2-pi)))))
  :hints (("Goal" :in-theory (enable inside-interval-p))))

(defthm mult-le-pos
  (implies (and (realp a) (realp b) (realp c) (<= 0 c) (<= a b))
           (<= (* c a) (* c b)))
  :rule-classes nil)

(defthm expt-nonneg (implies (and (realp s) (<= 0 s) (natp n)) (<= 0 (expt s n))))

(defthm gprime-nonneg
  (implies (inside-interval-p x (interval 0 (* 1/2 (acl2-pi))))
           (<= 0 (gprime x)))
  :hints (("Goal" :use ((:instance sin-range)
                        (:instance expt-split-1 (k (+ 1 (nn))) (s (acl2-sine x)))
                        (:instance mult-le-pos (c (expt (acl2-sine x) (nn))) (a (acl2-sine x)) (b 1))))))

(defthm g-deriv
  (implies (and (standardp x)
                (inside-interval-p x (interval 0 (* 1/2 (acl2-pi))))
                (inside-interval-p y (interval 0 (* 1/2 (acl2-pi))))
                (i-close x y) (not (= x y)))
           (i-close (/ (- (gfn x) (gfn y)) (- x y)) (gprime x)))
  :hints (("Goal" :use ((:instance f-deriv (n (nn)))
                        (:instance f-deriv (n (+ 1 (nn))))
                        (:instance lin-close (a -1) (b -1)
                                   (q1 (/ (- (wf (nn) x) (wf (nn) y)) (- x y)))
                                   (t1 (expt (acl2-sine x) (nn)))
                                   (q2 (/ (- (wf (+ 1 (nn)) x) (wf (+ 1 (nn)) y)) (- x y)))
                                   (t2 (expt (acl2-sine x) (+ 1 (nn))))))
           :in-theory (disable f-deriv i-close wf))))

(in-theory (disable gfn gprime (:executable-counterpart gfn) (:executable-counterpart gprime)))

(defthm g-monotone
  (<= (gfn 0) (gfn (* 1/2 (acl2-pi))))
  :hints (("Goal" :use ((:instance (:functional-instance mf-monotone
                                              (mf gfn) (mf-prime gprime)
                                              (mf-domain (lambda () (interval 0 (* 1/2 (acl2-pi))))))
                                   (a 0) (b (* 1/2 (acl2-pi))))))
          ("Subgoal 2" :use ((:instance g-deriv)) :in-theory (disable g-deriv))))

(defthm wi-mono-nn
  (<= (wi (+ 1 (nn))) (wi (nn)))
  :hints (("Goal" :use ((:instance g-monotone))
           :in-theory (e/d (gfn) (g-monotone wf)))))

(defthm wi-mono
  (implies (natp n) (<= (wi (+ 1 n)) (wi n)))
  :hints (("Goal" :use ((:functional-instance wi-mono-nn (nn (lambda () (nfix n))))))))

(defthm pos-ratio
  (implies (and (integerp n) (<= 2 n) (realp w) (< 0 w)) (< 0 (* (/ (- n 1) n) w)))
  :rule-classes nil)

(defthm wi-real (realp (wi n))
  :hints (("Goal" :use ((:instance wf-real (x (* 1/2 (acl2-pi)))) (:instance wf-real (x 0)))
           :in-theory (union-theories (theory 'minimal-theory) '(wi realp-+ realp-uminus (:type-prescription acl2-pi))))))

(in-theory (disable (:executable-counterpart wi)))

(defthm wi-pos
  (implies (natp n) (< 0 (wi n)))
  :hints (("Goal" :induct (wf n x) :in-theory (disable wi))
          ("Subgoal *1/3" :use ((:instance wi-rec) (:instance pos-ratio (w (wi (- n 2)))))
           :in-theory (disable wi wi-rec)))
  :rule-classes (:rewrite :linear))

(defthm wp-alg
  (implies (and (acl2-numberp a) (acl2-numberp b) (acl2-numberp r) (acl2-numberp w1)
                (acl2-numberp j2) (acl2-numberp j1) (acl2-numberp p)
                (equal (* a r) 1) (equal (* w1 j2) (* p j1)))
           (equal (* (* a b w1) (* r j2)) (* p (* b j1))))
  :hints (("Goal" :use ((:instance (:theorem (equal (* (* a b w1) (* r j2)) (* (* a r) b (* w1 j2))))))))
  :rule-classes nil)

(defthm split-one-w
  (implies (and (acl2-numberp a) (acl2-numberp b) (not (equal (+ a b) 0)))
           (equal (+ (* a (/ (+ a b))) (* b (/ (+ a b)))) 1))
  :hints (("Goal" :use ((:instance distributivity (x (/ (+ a b))) (y a) (z b)))
           :in-theory (disable distributivity)))
  :rule-classes nil)

(defthm ar-one
  (implies (and (integerp n) (<= 1 n))
           (equal (* (/ (* 2 n) (1- (* 2 n))) (/ (- (* 2 n) 1) (* 2 n))) 1))
  :hints (("Goal" :use ((:instance split-one-w (a -1) (b (* 2 n))))))
  :rule-classes nil)

(defthm wp-wi
  (implies (natp n)
           (equal (* (wallis-product n) (wi (* 2 n)))
                  (* (* 1/2 (acl2-pi)) (wi (+ 1 (* 2 n))))))
  :hints (("Goal" :induct (nat-ind n) :in-theory (disable wi wallis-product))
          ("Subgoal *1/2"
           :expand ((wallis-product n))
           :use ((:instance wi-rec (n (* 2 n)))
                 (:instance wi-rec (n (+ 1 (* 2 n))))
                 (:instance ar-one)
                 (:instance wp-alg (a (/ (* 2 n) (1- (* 2 n))))
                            (b (/ (* 2 n) (1+ (* 2 n))))
                            (r (/ (- (* 2 n) 1) (* 2 n)))
                            (w1 (wallis-product (- n 1)))
                            (j2 (wi (- (* 2 n) 2)))
                            (j1 (wi (- (+ 1 (* 2 n)) 2)))
                            (p (* 1/2 (acl2-pi)))))
           :in-theory (disable wi wallis-product wi-rec))))

(defthm cancel-le
  (implies (and (realp a) (realp b) (realp c) (< 0 c) (<= (* a c) (* b c))) (<= a b))
  :hints (("Goal" :cases ((< b a)))
          ("Subgoal 1" :use ((:instance (:theorem (implies (and (realp a) (realp b) (realp c) (< 0 c) (< b a)) (< (* b c) (* a c))))))))
  :rule-classes nil)

(defthm assoc-fact (equal (* (* p r) i0) (* p (* r i0))) :rule-classes nil)

(defthm bounds-gen
  (implies (and (realp w) (realp p) (realp i0) (realp i1) (realp i2) (realp r)
                (< 0 i0) (< 0 p)
                (equal (* w i0) (* p i1)) (<= i2 i1) (<= i1 i0) (equal i2 (* r i0)))
           (and (<= w p) (<= (* p r) w)))
  :hints (("Goal" :use ((:instance mult-le-pos (a i1) (b i0) (c p))
                        (:instance mult-le-pos (a i2) (b i1) (c p))
                        (:instance cancel-le (a w) (b p) (c i0))
                        (:instance cancel-le (a (* p r)) (b w) (c i0))
                        (:instance assoc-fact))
           :in-theory (theory 'minimal-theory)))
  :rule-classes nil)

(defthm wallis-bounds
  (implies (natp n)
           (and (<= (wallis-product n) (* 1/2 (acl2-pi)))
                (<= (* (* 1/2 (acl2-pi)) (/ (+ 1 (* 2 n)) (+ 2 (* 2 n)))) (wallis-product n))))
  :hints (("Goal" :use ((:instance bounds-gen (w (wallis-product n)) (p (* 1/2 (acl2-pi)))
                                   (i0 (wi (* 2 n))) (i1 (wi (+ 1 (* 2 n)))) (i2 (wi (+ 2 (* 2 n))))
                                   (r (/ (+ 1 (* 2 n)) (+ 2 (* 2 n)))))
                        (:instance wp-wi)
                        (:instance wi-mono (n (* 2 n)))
                        (:instance wi-mono (n (+ 1 (* 2 n))))
                        (:instance wi-rec (n (+ 2 (* 2 n)))))
           :in-theory (disable wi wallis-product wi-rec wi-mono wp-wi))))

(defthm-std pi-std (standardp (acl2-pi)))

(defthm fold-2 (equal (+ 1 (+ 1 x)) (+ 2 x)))

(defthm omr-gen
  (implies (and (acl2-numberp p) (acl2-numberp u) (acl2-numberp v) (equal u (- 1 v))) (equal (- p (* p v)) (* p u)))
  :rule-classes nil)

(defthm one-minus-r
  (implies (and (natp n) (acl2-numberp p))
           (equal (- p (* p (/ (+ 1 (* 2 n)) (+ 2 (* 2 n))))) (* p (/ (+ 2 (* 2 n))))))
  :hints (("Goal" :use ((:instance split-one-w (a 1) (b (+ 1 (* 2 n))))
                        (:instance omr-gen (v (* (+ 1 (* 2 n)) (/ (+ 2 (* 2 n))))) (u (/ (+ 2 (* 2 n))))))
           :in-theory (union-theories (theory 'minimal-theory) '(natp fold-2 unicity-of-1 fix))))
  :rule-classes nil)

(defthm large-2n+2
  (implies (and (natp n) (i-large n)) (i-small (/ (+ 2 (* 2 n)))))
  :hints (("Goal" :use ((:instance i-large-udivide (x (+ 2 (* 2 n))))
                        (:instance large-if->-large (x n) (y (+ 2 (* 2 n)))))
           :in-theory (disable i-large-udivide large-if->-large))))

(defthm close-gen
  (implies (and (realp w) (realp p) (realp e) (<= (- p e) w) (<= w p) (i-small e))
           (i-close w p))
  :hints (("Goal" :use ((:instance small-if-<-small (x e) (y (- w p))))
           :in-theory (enable i-close))))

(defthm u-pos (implies (natp n) (<= 0 (/ (+ 2 (* 2 n))))) :rule-classes nil)

(defthm wallis-close
  (implies (and (natp n) (i-large n))
           (i-close (wallis-product n) (* 1/2 (acl2-pi))))
  :hints (("Goal" :use ((:instance wallis-bounds)
                        (:instance one-minus-r (p (* 1/2 (acl2-pi))))
                        (:instance large-2n+2)
                        (:instance standards-are-limited (x (* 1/2 (acl2-pi))))
                        (:instance std-times-2 (a 1/2) (b (acl2-pi)))
                        (:instance pi-std)
                        (:instance limited*small->small (x (* 1/2 (acl2-pi))) (y (/ (+ 2 (* 2 n)))))
                        (:instance close-gen (w (wallis-product n)) (p (* 1/2 (acl2-pi)))
                                   (e (* (* 1/2 (acl2-pi)) (/ (+ 2 (* 2 n)))))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(natp (:type-prescription wallis-product) (:type-prescription acl2-pi))))))

(defthm main-3-lemma
  (implies (and (natp n) (i-large n))
           (equal (standard-part (wallis-product n)) (/ (acl2-pi) 2)))
  :hints (("Goal" :use ((:instance wallis-close)
                        (:instance close-x-y->same-standard-part (x (* 1/2 (acl2-pi))) (y (wallis-product n)))
                        (:instance i-close-symmetric (x (wallis-product n)) (y (* 1/2 (acl2-pi))))
                        (:instance standards-are-limited (x (* 1/2 (acl2-pi))))
                        (:instance std-times-2 (a 1/2) (b (acl2-pi))))
           :in-theory (disable wallis-product wallis-close close-x-y->same-standard-part
                               i-close-symmetric standards-are-limited))))

(deftheory th-wal-end (current-theory :here))
(in-theory (union-theories (theory 'th-mono) (theory 'th-sincos)))
;;; ---------------- log inequalities ----------------


(include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/ln-derivative-real" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))

(defderivative phi-deriv-raw (+ (acl2-ln (+ 1 x)) (- (acl2-ln (+ 1 (- x)))) (* -2 x)))

(defderivative psi-deriv-raw (+ (* 2 x) (* x x x) (- (acl2-ln (+ 1 x))) (acl2-ln (+ 1 (- x)))))

(defthm recip-le
  (implies (and (realp d) (< 0 d) (realp p) (<= 1 (* p d)))
           (<= (/ d) p))
  :hints (("Goal" :use ((:instance (:theorem (implies (and (realp a) (realp b) (realp c) (< 0 c) (<= a b)) (<= (* a c) (* b c))))
                                   (a 1) (b (* p d)) (c (/ d))))))
  :rule-classes nil)

(defthm recip-ge
  (implies (and (realp d) (< 0 d) (realp p) (<= (* p d) 1))
           (<= p (/ d)))
  :hints (("Goal" :use ((:instance (:theorem (implies (and (realp a) (realp b) (realp c) (< 0 c) (<= a b)) (<= (* a c) (* b c))))
                                   (b 1) (a (* p d)) (c (/ d))))))
  :rule-classes nil)

(defthm sq-nonneg (implies (realp x) (<= 0 (* x x))) :rule-classes nil)

(defthm r-lower-1
  (implies (and (realp x) (<= 0 x) (<= x 1/2))
           (<= (- 1 x) (/ (+ 1 x))))
  :hints (("Goal" :use ((:instance recip-ge (d (+ 1 x)) (p (- 1 x)))
                        (:instance sq-nonneg)))))

(defthm r-lower-2
  (implies (and (realp x) (<= 0 x) (<= x 1/2))
           (<= (+ 1 x) (/ (+ 1 (- x)))))
  :hints (("Goal" :use ((:instance recip-ge (d (- 1 x)) (p (+ 1 x)))
                        (:instance sq-nonneg)))))

(defthm add-le (implies (and (<= a u) (<= b v)) (<= (+ a b) (+ u v))) :rule-classes nil)

(defthm r-lower
  (implies (and (realp x) (<= 0 x) (<= x 1/2))
           (<= 2 (+ (/ (+ 1 x)) (/ (+ 1 (- x))))))
  :hints (("Goal" :use (r-lower-1 r-lower-2
                         (:instance add-le (a (- 1 x)) (b (+ 1 x)) (u (/ (+ 1 x))) (v (/ (+ 1 (- x))))))
           :in-theory (disable r-lower-1 r-lower-2))))

(defthm cube-nonneg (implies (and (realp x) (<= 0 x)) (<= 0 (* x x x)))
  :rule-classes nil)

(defthm r-upper-1
  (implies (and (realp x) (<= 0 x) (<= x 1/2))
           (<= (/ (+ 1 x)) (+ 1 (- x) (* x x))))
  :hints (("Goal" :use ((:instance recip-le (d (+ 1 x)) (p (+ 1 (- x) (* x x))))
                        (:instance cube-nonneg)))))

(defthm r-upper-2a
  (implies (and (realp x) (<= 0 x) (<= x 1/2))
           (<= 0 (* x x (- 1 (* 2 x)))))
  :hints (("Goal" :use ((:instance (:theorem (implies (and (realp a) (realp b) (<= 0 a) (<= 0 b)) (<= 0 (* a b))))
                                   (a (* x x)) (b (- 1 (* 2 x))))
                        (:instance sq-nonneg))))
  :rule-classes nil)

(defthm r-upper-2
  (implies (and (realp x) (<= 0 x) (<= x 1/2))
           (<= (/ (+ 1 (- x))) (+ 1 x (* 2 x x))))
  :hints (("Goal" :use ((:instance recip-le (d (- 1 x)) (p (+ 1 x (* 2 x x))))
                        (:instance r-upper-2a)))))

(defthm r-upper
  (implies (and (realp x) (<= 0 x) (<= x 1/2))
           (<= (+ (/ (+ 1 x)) (/ (+ 1 (- x)))) (+ 2 (* 3 x x))))
  :hints (("Goal" :use (r-upper-1 r-upper-2
                         (:instance add-le (u (+ 1 (- x) (* x x))) (v (+ 1 x (* 2 x x))) (a (/ (+ 1 x))) (b (/ (+ 1 (- x))))))
           :in-theory (disable r-upper-1 r-upper-2))))

(defun phi-fn (x)
  (realfix (+ (acl2-ln (+ 1 x)) (- (acl2-ln (+ 1 (- x)))) (* -2 x))))

(defun phi-prime (x)
  (realfix (+ -2 (/ (+ 1 x)) (/ (+ 1 (- x))))))

(defun psi-fn (x)
  (realfix (+ (* 2 x) (* x x x) (- (acl2-ln (+ 1 x))) (acl2-ln (+ 1 (- x))))))

(defun psi-prime (x)
  (realfix (- (+ 2 (* 3 x x)) (+ (/ (+ 1 x)) (/ (+ 1 (- x)))))))

(defthm phi-deriv
  (implies (and (standardp x)
                (inside-interval-p x (interval 0 1/2))
                (inside-interval-p y (interval 0 1/2))
                (i-close x y) (not (= x y)))
           (i-close (/ (- (phi-fn x) (phi-fn y)) (- x y)) (phi-prime x)))
  :hints (("Goal" :use ((:instance phi-deriv-raw))
           :in-theory (e/d (inside-interval-p) (phi-deriv-raw)))))

(defthm psi-raw-prime
  (implies (realp x)
           (equal (+ (+ (* 2 1) (* X 0))
                     (+ (+ (* X (+ (* X 1) (* X 1)))
                           (* (* X X) 1))
                        (+ (* -1 (* (/ (+ 1 X)) (+ 0 1)))
                           (* (/ (+ 1 (- X))) (+ 0 (* -1 1))))))
                  (psi-prime x))))

(defthm psi-deriv
  (implies (and (standardp x)
                (inside-interval-p x (interval 0 1/2))
                (inside-interval-p y (interval 0 1/2))
                (i-close x y) (not (= x y)))
           (i-close (/ (- (psi-fn x) (psi-fn y)) (- x y)) (psi-prime x)))
  :hints (("Goal" :use ((:instance psi-deriv-raw) (:instance psi-raw-prime))
           :in-theory (e/d (inside-interval-p) (psi-deriv-raw psi-raw-prime psi-prime)))))

(defthm phi-prime-nonneg
  (implies (inside-interval-p x (interval 0 1/2))
           (<= 0 (phi-prime x)))
  :hints (("Goal" :in-theory (enable inside-interval-p) :use ((:instance r-lower)))))

(defthm psi-prime-nonneg
  (implies (inside-interval-p x (interval 0 1/2))
           (<= 0 (psi-prime x)))
  :hints (("Goal" :in-theory (enable inside-interval-p) :use ((:instance r-upper)))))

(defthm inside-0-1/2
  (equal (inside-interval-p x (interval 0 1/2))
         (and (realp x) (<= 0 x) (<= x 1/2)))
  :hints (("Goal" :in-theory (enable inside-interval-p))))

(in-theory (disable phi-fn phi-prime psi-fn psi-prime
                    (:executable-counterpart phi-fn) (:executable-counterpart psi-fn)
                    (:executable-counterpart phi-prime) (:executable-counterpart psi-prime)))

(defthm phi-monotone
  (implies (and (realp x) (<= 0 x) (<= x 1/2))
           (<= (phi-fn 0) (phi-fn x)))
  :hints (("Goal" :use ((:instance (:functional-instance mf-monotone
                                              (mf phi-fn) (mf-prime phi-prime)
                                              (mf-domain (lambda () (interval 0 1/2))))
                                   (a 0) (b x))))
          ("Subgoal 2" :use ((:instance phi-deriv)) :in-theory (disable phi-deriv))))

(defthm psi-monotone
  (implies (and (realp x) (<= 0 x) (<= x 1/2))
           (<= (psi-fn 0) (psi-fn x)))
  :hints (("Goal" :use ((:instance (:functional-instance mf-monotone
                                              (mf psi-fn) (mf-prime psi-prime)
                                              (mf-domain (lambda () (interval 0 1/2))))
                                   (a 0) (b x))))
          ("Subgoal 2" :use ((:instance psi-deriv)) :in-theory (disable psi-deriv))))

(defthm acl2-ln-1
  (equal (acl2-ln 1) 0)
  :hints (("Goal" :use ((:instance uniqueness-of-ln (x 0) (y 1))))))

(defthm ln-lower
  (implies (and (realp x) (<= 0 x) (<= x 1/2))
           (<= (* 2 x) (- (acl2-ln (+ 1 x)) (acl2-ln (- 1 x)))))
  :hints (("Goal" :use ((:instance phi-monotone))
           :in-theory (e/d (phi-fn) (phi-monotone)))))

(defthm ln-upper
  (implies (and (realp x) (<= 0 x) (<= x 1/2))
           (<= (- (acl2-ln (+ 1 x)) (acl2-ln (- 1 x))) (+ (* 2 x) (* x x x))))
  :hints (("Goal" :use ((:instance psi-monotone))
           :in-theory (e/d (psi-fn) (psi-monotone)))))

;;; ---------------- Stirling sequence ----------------


(local (include-book "arithmetic/top-with-meta" :dir :system))

(defthm ln-positive-real
  (implies (and (realp x) (< 0 x))
           (equal (acl2-ln x) (acl2-ln-for-positive x)))
  :hints (("Goal" :in-theory (enable acl2-ln radiuspart anglepart))))

(defthm ln-product
  (implies (and (realp x) (< 0 x) (realp y) (< 0 y))
           (equal (acl2-ln (* x y)) (+ (acl2-ln x) (acl2-ln y)))))

(defthm ln-inverse
  (implies (and (realp x) (< 0 x))
           (equal (acl2-ln (/ x)) (- (acl2-ln x))))
  :hints (("Goal" :use ((:instance ln-product (y (/ x))))
           :in-theory (disable ln-product ln-positive-real))))

(defthm factorial-positive
  (< 0 (factorial n))
  :rule-classes (:rewrite :linear))

(defthm split-one
  (implies (and (acl2-numberp a) (acl2-numberp b) (not (equal (+ a b) 0)))
           (equal (+ (* a (/ (+ a b))) (* b (/ (+ a b)))) 1))
  :hints (("Goal" :use ((:instance distributivity (x (/ (+ a b))) (y a) (z b)))
           :in-theory (disable distributivity)))
  :rule-classes nil)

(defthm e1-gen
  (implies (and (acl2-numberp u) (acl2-numberp k) (equal (+ u (* 2 k u)) 1))
           (equal (+ 1 u) (* 2 (+ 1 k) u)))
  :rule-classes nil)

(defthm e2-gen
  (implies (and (acl2-numberp u) (acl2-numberp k) (equal (+ u (* 2 k u)) 1))
           (equal (- 1 u) (* 2 k u)))
  :rule-classes nil)

(defthm e1-lemma
  (implies (and (integerp k) (<= 1 k))
           (equal (+ 1 (/ (+ 1 (* 2 k)))) (* (* 2 (+ 1 k)) (/ (+ 1 (* 2 k))))))
  :hints (("Goal" :use ((:instance split-one (a 1) (b (* 2 k)))
                        (:instance e1-gen (u (/ (+ 1 (* 2 k))))))))
  :rule-classes nil)

(defthm e2-lemma
  (implies (and (integerp k) (<= 1 k))
           (equal (- 1 (/ (+ 1 (* 2 k)))) (* (* 2 k) (/ (+ 1 (* 2 k))))))
  :hints (("Goal" :use ((:instance split-one (a 1) (b (* 2 k)))
                        (:instance e2-gen (u (/ (+ 1 (* 2 k))))))))
  :rule-classes nil)

(defthm ln-sum-to-diff
  (implies (and (integerp k) (<= 1 k))
           (equal (- (acl2-ln (+ 1 (/ (+ 1 (* 2 k)))))
                     (acl2-ln (- 1 (/ (+ 1 (* 2 k))))))
                  (- (acl2-ln (+ 1 k)) (acl2-ln k))))
  :hints (("Goal"
           :use ((:instance ln-product (x (* 2 (+ 1 k))) (y (/ (+ 1 (* 2 k)))))
                 (:instance ln-product (x (* 2 k)) (y (/ (+ 1 (* 2 k)))))
                 (:instance ln-product (x 2) (y (+ 1 k)))
                 (:instance ln-product (x 2) (y k))
                 e1-lemma e2-lemma)
           :in-theory (disable ln-product ln-positive-real))))

(defun ell (n)
  (+ (acl2-ln (factorial n)) n (- (* n (acl2-ln n))) (- (* 1/2 (acl2-ln n)))))

(defthm dist-left (equal (* (+ x y) z) (+ (* x z) (* y z))) :rule-classes nil)

(defthm ell-step
  (implies (and (integerp k) (<= 1 k))
           (equal (- (ell k) (ell (+ 1 k)))
                  (- (* (+ k 1/2) (- (acl2-ln (+ 1 k)) (acl2-ln k))) 1)))
  :hints (("Goal" :use ((:instance ln-product (x (+ 1 k)) (y (factorial k)))
                        (:instance dist-left (x 1) (y k) (z (acl2-ln (+ 1 k))))
                        (:instance dist-left (x 1/2) (y k) (z (acl2-ln (+ 1 k)))))
           :expand ((factorial (+ 1 k)))
           :in-theory (disable ln-product ln-positive-real))))

(defthm mult-both
  (implies (equal a b) (equal (* c a) (* c b)))
  :rule-classes nil)



(defthm cu-cube
  (implies (and (realp u) (realp c) (equal (* 2 c u) 1))
           (equal (* c u u u) (* 1/2 u u)))
  :hints (("Goal" :use ((:instance (:theorem (equal (* 2 c (* u (* u u))) (* (* 2 c u) (* u u)))))))))

(defthm step-algebra-gen
  (implies (and (realp u) (realp c) (realp d) (< 0 c)
                (equal (* 2 c u) 1)
                (<= (* 2 u) d) (<= d (+ (* 2 u) (* u u u))))
           (and (<= 0 (- (* c d) 1))
                (<= (- (* c d) 1) (* 1/2 u u))))
  :hints (("Goal" :use ((:instance mult-le-pos (a (* 2 u)) (b d))
                        (:instance mult-le-pos (b (+ (* 2 u) (* u u u))) (a d)))))
  :rule-classes nil)

(defthm two-c-u-gen
  (implies (and (acl2-numberp u) (acl2-numberp k) (equal (+ u (* 2 k u)) 1))
           (equal (* 2 (+ k 1/2) u) 1))
  :rule-classes nil)

(defthm two-c-u
  (implies (and (integerp k) (<= 1 k))
           (equal (* 2 (+ k 1/2) (/ (+ 1 (* 2 k)))) 1))
  :hints (("Goal" :use ((:instance split-one (a 1) (b (* 2 k)))
                        (:instance two-c-u-gen (u (/ (+ 1 (* 2 k))))))
           :in-theory (disable distributivity)))
  :rule-classes nil)

(defthm u-range
  (implies (and (integerp k) (<= 1 k))
           (and (realp (/ (+ 1 (* 2 k))))
                (<= 0 (/ (+ 1 (* 2 k))))
                (<= (/ (+ 1 (* 2 k))) 1/2)))
  :hints (("Goal" :use ((:instance recip-le (d (+ 1 (* 2 k))) (p 1/2)))))
  :rule-classes nil)

(defthm d-bounds
  (implies (and (integerp k) (<= 1 k))
           (and (<= (* 2 (/ (+ 1 (* 2 k)))) (- (acl2-ln (+ 1 k)) (acl2-ln k)))
                (<= (- (acl2-ln (+ 1 k)) (acl2-ln k))
                    (+ (* 2 (/ (+ 1 (* 2 k))))
                       (* (/ (+ 1 (* 2 k))) (/ (+ 1 (* 2 k))) (/ (+ 1 (* 2 k))))))))
  :hints (("Goal" :use ((:instance u-range)
                        (:instance ln-sum-to-diff)
                        (:instance ln-lower (x (/ (+ 1 (* 2 k)))))
                        (:instance ln-upper (x (/ (+ 1 (* 2 k))))))
           :in-theory '(realfix fix))))

(defthm ell-step-bounds-1
  (implies (and (integerp k) (<= 1 k))
           (and (<= 0 (- (ell k) (ell (+ 1 k))))
                (<= (- (ell k) (ell (+ 1 k)))
                    (* 1/2 (/ (+ 1 (* 2 k))) (/ (+ 1 (* 2 k)))))))
  :hints (("Goal" :use ((:instance ell-step)
                        (:instance two-c-u)
                        (:instance d-bounds)
                        (:instance step-algebra-gen
                                   (u (/ (+ 1 (* 2 k))))
                                   (c (+ k 1/2))
                                   (d (- (acl2-ln (+ 1 k)) (acl2-ln k))))
                        (:instance realp-ln (y (+ 1 k)))
                        (:instance realp-ln (y k)))
           :in-theory '(realfix fix))))

(defthm recip-mono
  (implies (and (realp a) (realp b) (< 0 a) (<= a b))
           (<= (/ b) (/ a)))
  :rule-classes nil)

(defthm ring-id-1 (equal (* a (+ b (* b k))) (+ (* a b) (* b (* a k)))) :rule-classes nil)

(defthm ab-gen
  (implies (and (acl2-numberp a) (acl2-numberp b) (acl2-numberp k)
                (equal (* a k) 1) (equal (+ b (* b k)) 1))
           (equal (- a b) (* a b)))
  :hints (("Goal" :use ((:instance ring-id-1))
           :in-theory (disable distributivity)))
  :rule-classes nil)

(defthm u2-poly
  (implies (realp k) (<= (* 4 k (+ 1 k)) (* (+ 1 (* 2 k)) (+ 1 (* 2 k)))))
  :rule-classes nil)

(defthm u2-recip
  (implies (and (integerp k) (<= 1 k))
           (<= (/ (* (+ 1 (* 2 k)) (+ 1 (* 2 k)))) (/ (* 4 k (+ 1 k)))))
  :hints (("Goal" :use ((:instance recip-mono (a (* 4 k (+ 1 k)))
                                   (b (* (+ 1 (* 2 k)) (+ 1 (* 2 k)))))
                        (:instance u2-poly))
           :in-theory (disable distributivity inverse-of-* )))
  :rule-classes nil)

(defthm u2-recip-2
  (implies (and (integerp k) (<= 1 k))
           (<= (* (/ (+ 1 (* 2 k))) (/ (+ 1 (* 2 k)))) (* 1/4 (* (/ k) (/ (+ 1 k))))))
  :hints (("Goal" :use ((:instance u2-recip))))
  :rule-classes nil)

(defthm ab-k
  (implies (and (integerp k) (<= 1 k))
           (equal (- (/ k) (/ (+ 1 k))) (* (/ k) (/ (+ 1 k)))))
  :hints (("Goal" :use ((:instance ab-gen (a (/ k)) (b (/ (+ 1 k))))
                        (:instance split-one (a 1) (b k)))))
  :rule-classes nil)

(defthm u2-gen
  (implies (and (realp u) (realp a) (realp b) (<= (* u u) (* 1/4 (* a b))) (equal (- a b) (* a b)))
           (<= (* 1/2 (* u u)) (* 1/8 (- a b))))
  :rule-classes nil)

(defthm u2-bound
  (implies (and (integerp k) (<= 1 k))
           (<= (* 1/2 (* (/ (+ 1 (* 2 k))) (/ (+ 1 (* 2 k)))))
               (* 1/8 (- (/ k) (/ (+ 1 k))))))
  :hints (("Goal" :use ((:instance u2-recip-2)
                        (:instance ab-k)
                        (:instance u2-gen (u (/ (+ 1 (* 2 k)))) (a (/ k)) (b (/ (+ 1 k)))))
           :in-theory nil)))

(defthm le-trans (implies (and (<= x y) (<= y z)) (<= x z)) :rule-classes nil)

(defthm ell-step-bounds
  (implies (and (integerp k) (<= 1 k))
           (and (<= 0 (- (ell k) (ell (+ 1 k))))
                (<= (- (ell k) (ell (+ 1 k)))
                    (* 1/8 (- (/ k) (/ (+ 1 k)))))))
  :hints (("Goal" :use ((:instance ell-step-bounds-1)
                        (:instance u2-bound)
                        (:instance le-trans (x (- (ell k) (ell (+ 1 k))))
                                   (y (* 1/2 (* (/ (+ 1 (* 2 k))) (/ (+ 1 (* 2 k))))))
                                   (z (* 1/8 (- (/ k) (/ (+ 1 k)))))))
           :in-theory nil))
  :rule-classes nil)

(defun tele-ind (m n)
  (declare (xargs :measure (nfix n)))
  (if (or (not (integerp n)) (<= n m) (zp n)) t (tele-ind m (- n 1))))

(defthm ell-tele
  (implies (and (integerp m) (integerp n) (<= 1 m) (<= m n))
           (and (<= 0 (- (ell m) (ell n)))
                (<= (- (ell m) (ell n)) (* 1/8 (- (/ m) (/ n))))))
  :hints (("Goal" :induct (tele-ind m n) :in-theory (disable ell))
          ("Subgoal *1/2" :use ((:instance ell-step-bounds (k (- n 1))))))
  :rule-classes nil)

(defthm ell-1 (equal (ell 1) 1)
  :hints (("Goal" :in-theory (enable factorial))))

(defthm ell-bounds
  (implies (and (integerp n) (<= 1 n))
           (and (<= 7/8 (ell n)) (<= (ell n) 1)))
  :hints (("Goal" :use ((:instance ell-tele (m 1) (n n))
                        (:instance (:theorem (implies (and (integerp n) (<= 1 n)) (< 0 (/ n))))))
           :in-theory (disable ell)))
  :rule-classes nil)

(defthm ell-realp (implies (and (integerp n) (<= 1 n)) (realp (ell n)))
  :hints (("Goal" :in-theory (enable ell))))

(defthm ell-limited
  (implies (and (integerp n) (<= 1 n))
           (i-limited (ell n)))
  :hints (("Goal" :use ((:instance ell-bounds)
                        (:instance limited-squeeze (a 7/8) (b 1) (x (ell n))))
           :in-theory (disable ell limited-squeeze))))

(defthm pos-recip (implies (and (integerp n) (<= 1 n)) (and (< 0 (/ n)) (<= (/ n) 1))) :rule-classes nil)

(defthm small-gen
  (implies (and (realp d) (realp a) (realp b) (<= 0 d) (<= d (* 1/8 (- a b))) (< 0 b) (i-small a))
           (i-small d))
  :hints (("Goal" :use ((:instance small-if-<-small (x a) (y d))))))

(defthm ell-close-ordered
  (implies (and (integerp m) (integerp n) (<= 1 m) (<= m n) (i-large m))
           (i-close (ell m) (ell n)))
  :hints (("Goal" :use ((:instance ell-tele)
                        (:instance i-large-udivide (x m))
                        (:instance small-gen (a (/ m)) (b (/ n)) (d (- (ell m) (ell n))))
                        (:instance ell-realp (n m))
                        (:instance ell-realp (n n))
                        (:instance pos-recip (n n)))
           :in-theory '(i-close realfix fix))))

(defthm ell-close
  (implies (and (integerp m) (integerp n) (<= 1 m) (<= 1 n) (i-large m) (i-large n))
           (i-close (ell m) (ell n)))
  :hints (("Goal" :cases ((<= m n))
           :in-theory (disable ell))
          ("Subgoal 2" :use ((:instance ell-close-ordered (m n) (n m))
                             (:instance i-close-symmetric (x (ell n)) (y (ell m))))
           :in-theory (disable ell ell-close-ordered i-close-symmetric))))

(in-theory (disable ell))

(defun-std ell-lim ()
  (standard-part (ell (i-large-integer))))

(defthm ell-to-lim
  (implies (and (integerp n) (<= 1 n) (i-large n))
           (i-close (ell n) (ell-lim)))
  :hints (("Goal" :use ((:instance ell-close (m n) (n (i-large-integer)))
                        (:instance standard-part-close (x (ell (i-large-integer))))
                        (:instance ell-limited (n (i-large-integer)))
                        (:instance i-close-symmetric (x (standard-part (ell (i-large-integer))))
                                   (y (ell (i-large-integer))))
                        (:instance i-close-transitive (x (ell n)) (y (ell (i-large-integer)))
                                   (z (standard-part (ell (i-large-integer))))))
           :in-theory (disable ell ell-close standard-part-close ell-limited i-close-symmetric
                               i-close-transitive))))

(in-theory (union-theories (current-theory :here) (theory 'th-wal-end)))
;;; ---------------- final assembly ----------------



(local (include-book "arithmetic/top-with-meta" :dir :system))

(in-theory (disable ln-positive-real))

(defthm wp-pos
  (implies (natp n) (and (realp (wallis-product n)) (< 0 (wallis-product n))))
  :rule-classes (:rewrite :type-prescription))

(defthm ln-quot
  (implies (and (realp x) (< 0 x) (realp y) (< 0 y))
           (equal (acl2-ln (* x (/ y))) (- (acl2-ln x) (acl2-ln y))))
  :hints (("Goal" :use ((:instance ln-product (y (/ y))) (:instance ln-inverse (x y)))
           :in-theory (disable ln-product ln-inverse))))

(defthm ln-2n
  (implies (and (realp n) (< 0 n))
           (equal (acl2-ln (* 2 n)) (+ (acl2-ln 2) (acl2-ln n))))
  :hints (("Goal" :use ((:instance ln-product (x 2) (y n))))))

(defthm ln-wp
  (implies (natp n)
           (equal (acl2-ln (wallis-product n))
                  (+ (* 4 (acl2-ln (factorial n))) (* 4 n (acl2-ln 2))
                     (- (* 2 (acl2-ln (factorial (* 2 n)))))
                     (- (acl2-ln (+ 1 (* 2 n)))))))
  :hints (("Goal" :induct (nat-ind n) :in-theory (disable wallis-product factorial ln-2n))
          ("Subgoal *1/2"
           :expand ((wallis-product n) (factorial n) (factorial (* 2 n)) (factorial (+ -1 (* 2 n))))
           :use ((:instance ln-product (x (/ (* 2 n) (1- (* 2 n))))
                            (y (* (/ (* 2 n) (1+ (* 2 n))) (wallis-product (- n 1)))))
                 (:instance ln-product (x (/ (* 2 n) (1+ (* 2 n)))) (y (wallis-product (- n 1))))
                 (:instance ln-quot (x (* 2 n)) (y (1- (* 2 n))))
                 (:instance ln-quot (x (* 2 n)) (y (1+ (* 2 n))))
                 (:instance ln-product (x n) (y (factorial (- n 1))))
                 (:instance ln-product (x (* 2 n)) (y (* (+ -1 (* 2 n)) (factorial (+ -2 (* 2 n))))))
                 (:instance ln-product (x (+ -1 (* 2 n))) (y (factorial (+ -2 (* 2 n)))))
                 (:instance ln-2n))
           :in-theory (disable wallis-product factorial ln-product ln-quot ln-2n))))

(defthm four-alg
  (implies (and (acl2-numberp n) (acl2-numberp u) (equal (* n u) 1))
           (equal (* 2 (* (+ 1 (* 2 n)) u)) (+ 4 (* 2 u))))
  :hints (("Goal" :use ((:instance dist-left (x 1) (y (* 2 n)) (z u)))))
  :rule-classes nil)

(defthm four-alg-n
  (implies (and (integerp n) (<= 1 n))
           (equal (* 2 (* (+ 1 (* 2 n)) (/ n))) (+ 4 (* 2 (/ n)))))
  :hints (("Goal" :use ((:instance four-alg (u (/ n))))
           :in-theory (disable distributivity)))
  :rule-classes nil)

(defthm pos-fact-n
  (implies (and (integerp n) (<= 1 n))
           (and (realp (* (+ 1 (* 2 n)) (/ n))) (< 0 (* (+ 1 (* 2 n)) (/ n)))
                (realp (+ 1 (* 2 n))) (< 0 (+ 1 (* 2 n))) (realp n) (< 0 n) (realp 2) (< 0 2)))
  :rule-classes nil)

(defthm four-plus
  (implies (and (integerp n) (<= 1 n))
           (equal (acl2-ln (+ 4 (* 2 (/ n))))
                  (- (+ (acl2-ln 2) (acl2-ln (+ 1 (* 2 n)))) (acl2-ln n))))
  :hints (("Goal" :use ((:instance ln-product (x 2) (y (* (+ 1 (* 2 n)) (/ n))))
                        (:instance ln-quot (x (+ 1 (* 2 n))) (y n))
                        (:instance four-alg-n)
                        (:instance pos-fact-n))
           :in-theory (theory 'minimal-theory))))

(defthm ln-wp-ell
  (implies (and (integerp n) (<= 1 n))
           (equal (acl2-ln (wallis-product n))
                  (- (- (* 4 (ell n)) (* 2 (ell (* 2 n)))) (acl2-ln (+ 4 (* 2 (/ n)))))))
  :hints (("Goal" :use ((:instance ln-wp) (:instance four-plus) (:instance ln-2n))
           :in-theory (e/d (ell) (ln-wp four-plus ln-2n wallis-product factorial)))))

(defthm close-std-equal
  (implies (and (standardp x) (standardp y) (acl2-numberp x) (acl2-numberp y) (i-close x y))
           (equal x y))
  :hints (("Goal" :use ((:instance standard-small-is-zero (x (- x y))))
           :in-theory (enable i-close)))
  :rule-classes nil)

(defthm comb-close
  (implies (and (acl2-numberp a1) (acl2-numberp a2) (acl2-numberp a3)
                (acl2-numberp c1) (acl2-numberp c2) (acl2-numberp c3)
                (i-close a1 c1) (i-close a2 c2) (i-close a3 c3))
           (i-close (- (- (* 4 a1) (* 2 a2)) a3) (- (- (* 4 c1) (* 2 c2)) c3)))
  :hints (("Goal" :in-theory (enable i-close)
           :use ((:instance limited*small->small (x 4) (y (- a1 c1)))
                 (:instance limited*small->small (x 2) (y (- a2 c2)))
                 (:instance i-small-plus (x (* 4 (- a1 c1))) (y (- (* 2 (- a2 c2)))))
                 (:instance i-small-plus (x (+ (* 4 (- a1 c1)) (- (* 2 (- a2 c2))))) (y (- (- a3 c3))))))))

(defthm-std ell-lim-real (realp (ell-lim)))
(defthm-std ell-lim-std (standardp (ell-lim)))

(defthm two-limited (and (i-limited 2) (standardp 4) (acl2-numberp 4)) :rule-classes nil)

(defthm small-2/n
  (implies (and (natp n) (i-large n)) (i-close 4 (+ 4 (* 2 (/ n)))))
  :hints (("Goal" :use ((:instance i-large-udivide (x n))
                        (:instance limited*small->small (x 2) (y (/ n)))
                        (:instance i-close-to-small-sum (x 4) (eps (* 2 (/ n))))
                        (:instance two-limited))
           :in-theory (theory 'minimal-theory))))

(defthm large-2n
  (implies (and (natp n) (i-large n)) (i-large (* 2 n)))
  :hints (("Goal" :use ((:instance large-if->-large (x n) (y (* 2 n)))))))

(defthm natp-large-pos
  (implies (and (natp n) (i-large n)) (<= 1 n))
  :hints (("Goal" :cases ((= n 0))))
  :rule-classes :forward-chaining)

(defthm misc-facts-n
  (implies (and (natp n) (i-large n))
           (and (integerp n) (<= 1 n) (integerp (* 2 n)) (<= 1 (* 2 n))
                (realp (+ 4 (* 2 (/ n)))) (< 0 (+ 4 (* 2 (/ n))))
                (realp (wallis-product n)) (< 0 (wallis-product n))
                (realp 4) (< 0 4) (standardp 4)))
  :rule-classes nil)

(defthm half-pi-facts
  (and (realp (* 1/2 (acl2-pi))) (< 0 (* 1/2 (acl2-pi))) (standardp (* 1/2 (acl2-pi)))
       (acl2-numberp (* 1/2 (acl2-pi))))
  :rule-classes nil)

(defthm ln-num (acl2-numberp (acl2-ln x)))

(defthm std-comb
  (implies (and (standardp c) (standardp d))
           (standardp (- (- (* 4 c) (* 2 c)) d)))
  :rule-classes nil)

(defthm comb-simp
  (equal (- (- (* 4 c) (* 2 c)) d) (- (* 2 c) d))
  :rule-classes nil)

(defthm ell-num (implies (and (integerp n) (<= 1 n)) (acl2-numberp (ell n))))

(defthm ell-lim-eqn-n
  (implies (and (natp n) (i-large n))
           (equal (- (* 2 (ell-lim)) (acl2-ln 4)) (acl2-ln (* 1/2 (acl2-pi)))))
  :hints (("Goal"
           :use ((:instance misc-facts-n)
                 (:instance half-pi-facts)
                 (:instance ln-wp-ell)
                 (:instance ell-to-lim)
                 (:instance ell-to-lim (n (* 2 n)))
                 (:instance ell-num)
                 (:instance ell-num (n (* 2 n)))
                 (:instance small-2/n)
                 (:instance large-2n)
                 (:instance acl2-ln-real-continuous (x 4) (y (+ 4 (* 2 (/ n)))))
                 (:instance wallis-close)
                 (:instance i-close-symmetric (x (wallis-product n)) (y (* 1/2 (acl2-pi))))
                 (:instance i-close-symmetric (x (acl2-ln 4)) (y (acl2-ln (+ 4 (* 2 (/ n))))))
                 (:instance acl2-ln-real-continuous (x (* 1/2 (acl2-pi))) (y (wallis-product n)))
                 (:instance comb-close (a1 (ell n)) (a2 (ell (* 2 n))) (a3 (acl2-ln (+ 4 (* 2 (/ n)))))
                            (c1 (ell-lim)) (c2 (ell-lim)) (c3 (acl2-ln 4)))
                 (:instance i-close-transitive (x (acl2-ln (* 1/2 (acl2-pi))))
                            (y (acl2-ln (wallis-product n)))
                            (z (- (- (* 4 (ell-lim)) (* 2 (ell-lim))) (acl2-ln 4))))
                 (:instance close-std-equal (x (acl2-ln (* 1/2 (acl2-pi))))
                            (y (- (- (* 4 (ell-lim)) (* 2 (ell-lim))) (acl2-ln 4))))
                 (:instance std-comb (c (ell-lim)) (d (acl2-ln 4)))
                 (:instance comb-simp (c (ell-lim)) (d (acl2-ln 4)))
                 (:instance acl2-ln-standard (x 4))
                 (:instance acl2-ln-standard (x (* 1/2 (acl2-pi))))
                 (:instance ln-num (x 4))
                 (:instance ln-num (x (* 1/2 (acl2-pi))))
                 (:instance ln-num (x (wallis-product n)))
                 (:instance ln-num (x (+ 4 (* 2 (/ n)))))
                 (:instance ell-lim-real)
                 (:instance ell-lim-std))
           :in-theory (theory 'minimal-theory))))

(defthm ln-sqrt
  (implies (and (realp x) (< 0 x))
           (equal (acl2-ln (acl2-sqrt x)) (* 1/2 (acl2-ln x))))
  :hints (("Goal" :use ((:instance ln-product (x (acl2-sqrt x)) (y (acl2-sqrt x)))
                        (:instance sqrt-sqrt)
                        (:instance sqrt->-0))
           :in-theory (disable ln-product sqrt-sqrt sqrt->-0))))

(defthm c-gen
  (implies (and (acl2-numberp c) (acl2-numberp l4) (acl2-numberp lh)
                (equal (- (* 2 c) l4) lh) (equal ll (+ l4 lh)) (equal ss (* 1/2 ll)))
           (equal c ss))
  :rule-classes nil)

(defthm four-half (equal (* 4 (* 1/2 x)) (* 2 x)))

(defthm ilg-facts (and (natp (i-large-integer)) (i-large (i-large-integer))) :rule-classes nil)

(defthm two-pi-facts
  (and (realp (* 2 (acl2-pi))) (< 0 (* 2 (acl2-pi))) (realp 4) (< 0 4))
  :rule-classes nil)

(defthm ell-lim-value
  (equal (ell-lim) (acl2-ln (acl2-sqrt (* 2 (acl2-pi)))))
  :hints (("Goal" :use ((:instance ell-lim-eqn-n (n (i-large-integer)))
                        (:instance ilg-facts)
                        (:instance half-pi-facts)
                        (:instance two-pi-facts)
                        (:instance ln-product (x 4) (y (* 1/2 (acl2-pi))))
                        (:instance four-half (x (acl2-pi)))
                        (:instance ln-sqrt (x (* 2 (acl2-pi))))
                        (:instance ell-lim-real)
                        (:instance ln-num (x 4))
                        (:instance ln-num (x (* 1/2 (acl2-pi))))
                        (:instance c-gen (c (ell-lim)) (l4 (acl2-ln 4)) (lh (acl2-ln (* 1/2 (acl2-pi))))
                                   (ll (acl2-ln (* 2 (acl2-pi))))
                                   (ss (acl2-ln (acl2-sqrt (* 2 (acl2-pi)))))))
           :in-theory (theory 'minimal-theory)))
  :rule-classes nil)

(defthm ln-expt
  (implies (and (realp x) (< 0 x) (natp k))
           (equal (acl2-ln (expt x k)) (* k (acl2-ln x))))
  :hints (("Goal" :induct (nat-ind k))
          ("Subgoal *1/2" :use ((:instance ln-product (y (expt x (- k 1)))))
           :in-theory (disable ln-product))))

(defthm sqrt-facts
  (implies (and (realp x) (< 0 x))
           (and (realp (acl2-sqrt x)) (< 0 (acl2-sqrt x)) (<= 0 x)))
  :rule-classes nil)

(defthm assoc-2pin (equal (* 2 (acl2-pi) n) (* (* 2 (acl2-pi)) n)) :rule-classes nil)

(defthm ln-sqrt-2pin
  (implies (and (integerp n) (<= 1 n))
           (equal (acl2-ln (acl2-sqrt (* 2 (acl2-pi) n)))
                  (+ (ell-lim) (* 1/2 (acl2-ln n)))))
  :hints (("Goal" :use ((:instance sqrt-* (x (* 2 (acl2-pi))) (y n))
                        (:instance ln-product (x (acl2-sqrt (* 2 (acl2-pi)))) (y (acl2-sqrt n)))
                        (:instance sqrt-facts (x (* 2 (acl2-pi))))
                        (:instance sqrt-facts (x n))
                        (:instance two-pi-facts)
                        (:instance assoc-2pin)
                        (:instance ln-sqrt (x n))
                        (:instance ell-lim-value))
           :in-theory (theory 'minimal-theory))))

(defthm ell-def
  (equal (ell n) (+ (acl2-ln (factorial n)) n (- (* n (acl2-ln n))) (- (* 1/2 (acl2-ln n)))))
  :hints (("Goal" :in-theory (enable ell)))
  :rule-classes nil)

(defthm rhs-gen
  (implies (and (acl2-numberp n) (acl2-numberp l) (acl2-numberp c) (acl2-numberp f)
                (equal aa (* n l)) (equal bb (+ c (* 1/2 l)))
                (equal e (+ f n (- (* n l)) (- (* 1/2 l)))))
           (equal (+ aa (- n) bb) (- f (- e c))))
  :rule-classes nil)

(defthm rhs-2
  (implies (and (integerp n) (<= 1 n))
           (equal (+ (acl2-ln (expt n n)) (- n) (acl2-ln (acl2-sqrt (* 2 (acl2-pi) n))))
                  (- (acl2-ln (factorial n)) (- (ell n) (ell-lim)))))
  :hints (("Goal" :use ((:instance ln-sqrt-2pin) (:instance ln-expt (x n) (k n))
                        (:instance ell-def)
                        (:instance rhs-gen (aa (acl2-ln (expt n n))) (l (acl2-ln n))
                                   (bb (acl2-ln (acl2-sqrt (* 2 (acl2-pi) n))))
                                   (c (ell-lim)) (f (acl2-ln (factorial n))) (e (ell n))))
           :in-theory (union-theories (theory 'minimal-theory) '(natp posp)))))

(defthm close-minus-small
  (implies (and (acl2-numberp a) (acl2-numberp d) (i-small d))
           (i-close a (- a d)))
  :hints (("Goal" :in-theory (enable i-close))))

(defthm MAIN-2
  (implies (and (posp n)
                (i-large n))
           (i-close (acl2-ln (factorial n))
                    (+ (acl2-ln (expt n n))
                       (- n)
                       (acl2-ln (acl2-sqrt (* 2 (acl2-pi) n))))))
  :hints (("Goal" :use ((:instance rhs-2)
                        (:instance ell-to-lim)
                        (:instance close-diff-small (x (ell n)) (y (ell-lim)))
                        (:instance close-minus-small (a (acl2-ln (factorial n))) (d (- (ell n) (ell-lim))))
                        (:instance ln-num (x (factorial n)))
                        (:instance ell-num)
                        (:instance ell-lim-real))
           :in-theory (union-theories (theory 'minimal-theory) '(posp)))))

(defthm exp-ln-pos
  (implies (and (realp y) (< 0 y))
           (equal (acl2-exp (acl2-ln y)) y))
  :hints (("Goal" :in-theory (enable ln-positive-real))))

(defthm exp-0 (equal (acl2-exp 0) 1)
  :hints (("Goal" :use ((:instance exp-ln-pos (y 1))) :in-theory (disable exp-ln-pos))))

(defthm ln-exp-real
  (implies (realp x) (equal (acl2-ln (acl2-exp x)) x))
  :hints (("Goal" :use ((:instance ln-exp)))))

(defthm exp-pos-real
  (implies (realp x) (and (realp (acl2-exp x)) (< 0 (acl2-exp x)))))

(defthm expt-pos-n
  (implies (and (integerp n) (<= 1 n))
           (and (realp (expt n n)) (< 0 (expt n n))
                (realp (/ (acl2-exp n))) (< 0 (/ (acl2-exp n)))
                (realp (* (/ (acl2-exp n)) (acl2-sqrt n))) (< 0 (* (/ (acl2-exp n)) (acl2-sqrt n)))
                (realp (* (expt n n) (* (/ (acl2-exp n)) (acl2-sqrt n))))
                (< 0 (* (expt n n) (* (/ (acl2-exp n)) (acl2-sqrt n))))
                (realp n) (< 0 n)))
  :rule-classes nil)

(defthm ln-denom
  (implies (and (integerp n) (<= 1 n))
           (equal (acl2-ln (* (acl2-sqrt (* 2 (acl2-pi))) (expt n n) (/ (acl2-exp n)) (acl2-sqrt n)))
                  (+ (ell-lim) (* n (acl2-ln n)) (- n) (* 1/2 (acl2-ln n)))))
  :hints (("Goal" :use ((:instance ell-lim-value)
                        (:instance ln-product (x (acl2-sqrt (* 2 (acl2-pi))))
                                   (y (* (expt n n) (/ (acl2-exp n)) (acl2-sqrt n))))
                        (:instance ln-product (x (expt n n)) (y (* (/ (acl2-exp n)) (acl2-sqrt n))))
                        (:instance ln-product (x (/ (acl2-exp n))) (y (acl2-sqrt n)))
                        (:instance ln-inverse (x (acl2-exp n)))
                        (:instance ln-exp-real (x n))
                        (:instance ln-expt (x n) (k n))
                        (:instance ln-sqrt (x n))
                        (:instance sqrt-facts (x (* 2 (acl2-pi))))
                        (:instance sqrt-facts (x n))
                        (:instance two-pi-facts)
                        (:instance exp-pos-real (x n))
                        (:instance expt-pos-n))
           :in-theory (union-theories (theory 'minimal-theory) '(natp)))))

(defthm fact-pos-real (and (realp (factorial n)) (< 0 (factorial n))) :rule-classes nil)

(defthm minus-0 (implies (acl2-numberp x) (and (equal (- x 0) x) (equal (+ x 0) x))) :rule-classes nil)

(defthm small-close-0
  (implies (and (acl2-numberp d) (i-small d)) (i-close d 0))
  :hints (("Goal" :use ((:instance minus-0 (x d)))
           :in-theory (union-theories (theory 'minimal-theory) '(i-close))))
  :rule-classes nil)

(defthm zero-std (standard-numberp 0) :rule-classes nil)

(defthm pos4
  (implies (and (realp a) (realp b) (realp c) (realp d) (< 0 a) (< 0 b) (< 0 c) (< 0 d))
           (and (realp (* a b c d)) (< 0 (* a b c d))))
  :rule-classes nil)

(defthm denom-pos
  (implies (and (integerp n) (<= 1 n))
           (and (realp (* (acl2-sqrt (* 2 (acl2-pi))) (expt n n) (/ (acl2-exp n)) (acl2-sqrt n)))
                (< 0 (* (acl2-sqrt (* 2 (acl2-pi))) (expt n n) (/ (acl2-exp n)) (acl2-sqrt n)))))
  :hints (("Goal" :use ((:instance expt-pos-n) (:instance sqrt-facts (x (* 2 (acl2-pi))))
                        (:instance sqrt-facts (x n))
                        (:instance two-pi-facts)
                        (:instance pos4 (a (acl2-sqrt (* 2 (acl2-pi)))) (b (expt n n)) (c (/ (acl2-exp n)))
                                   (d (acl2-sqrt n))))
           :in-theory (theory 'minimal-theory)))
  :rule-classes nil)

(defthm ln-ratio
  (implies (and (integerp n) (<= 1 n))
           (equal (acl2-ln (/ (factorial n)
                              (* (acl2-sqrt (* 2 (acl2-pi))) (expt n n) (/ (acl2-exp n)) (acl2-sqrt n))))
                  (- (ell n) (ell-lim))))
  :hints (("Goal" :use ((:instance ln-quot (x (factorial n))
                                   (y (* (acl2-sqrt (* 2 (acl2-pi))) (expt n n) (/ (acl2-exp n)) (acl2-sqrt n))))
                        (:instance denom-pos)
                        (:instance ln-denom)
                        (:instance ell-def)
                        (:instance fact-pos-real))
           :in-theory (theory 'minimal-theory))))

(defthm ratio-pos
  (implies (and (integerp n) (<= 1 n))
           (and (realp (/ (factorial n)
                          (* (acl2-sqrt (* 2 (acl2-pi))) (expt n n) (/ (acl2-exp n)) (acl2-sqrt n))))
                (< 0 (/ (factorial n)
                        (* (acl2-sqrt (* 2 (acl2-pi))) (expt n n) (/ (acl2-exp n)) (acl2-sqrt n))))))
  :hints (("Goal" :use ((:instance denom-pos))))
  :rule-classes nil)

(defthm MAIN-1
  (implies (and (natp n)
                (i-large n))
           (i-close (/ (factorial n)
                       (* (acl2-sqrt (* 2 (acl2-pi)))
                          (expt n n)
                          (/ (acl2-exp n))
                          (acl2-sqrt n)))
                    1))
  :hints (("Goal" :use ((:instance ln-ratio)
                        (:instance ratio-pos)
                        (:instance exp-ln-pos
                                   (y (/ (factorial n)
                                         (* (acl2-sqrt (* 2 (acl2-pi))) (expt n n) (/ (acl2-exp n)) (acl2-sqrt n)))))
                        (:instance ell-to-lim)
                        (:instance close-diff-small (x (ell n)) (y (ell-lim)))
                        (:instance small-close-0 (d (- (ell n) (ell-lim))))
                        (:instance exp-continuous (x 0) (y (- (ell n) (ell-lim))))
                        (:instance exp-0)
                        (:instance zero-std)
                        (:instance i-close-symmetric (x 1)
                                   (y (/ (factorial n)
                                         (* (acl2-sqrt (* 2 (acl2-pi))) (expt n n) (/ (acl2-exp n)) (acl2-sqrt n)))))
                        (:instance natp-large-pos))
           :in-theory (union-theories (theory 'minimal-theory) '(natp)))))


(defthm MAIN-3
  (implies (and (natp n)
                (i-large n))
           (equal (standard-part (wallis-product n))
                  (/ (acl2-pi) 2)))
  :hints (("Goal" :use ((:instance main-3-lemma)) :in-theory (disable main-3-lemma wallis-product))))
