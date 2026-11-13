(in-package "ACL2")

;; Stirling's formula in ACL2(r):  n! ~ sqrt(2 pi n) (n/e)^n
;;
;; Proof outline:
;;  1. Series bounds for exp give monotonicity of A(n) = (n!)^2 e^(2n) / n^(2n+1)
;;     (decreasing) and A(n) e^(-2/n) (increasing), so A(n) ~ A(m) for all
;;     infinite n, m and 1 <= A(n) <= e^2.
;;  2. Wallis integrals I_n = st( h * sum_{j<N} sin(jh)^n ), h = pi/(2N), N
;;     infinite (defun-std), satisfy I_0 = pi/2, I_1 = 1, (n+1) I_(n+1) = n I_(n-1),
;;     I_(n+1) <= I_n  (via a discrete integration-by-parts with infinitesimal error),
;;     giving Wallis' inequalities 2/(2k+1) <= pi p_k^2 <= 1/k, p_k = prod (2j-1)/(2j).
;;  3. A(m)^2 m p_m^2 = 2 A(2m) forces A(m) ~ 2 pi, hence the ratio
;;     n! / (sqrt(2 pi n) (n/e)^n) = sqrt(A(n)/(2 pi)) is infinitely close to 1
;;     for infinite n, which is transferred to the classical epsilon-N limit.

(include-book "nonstd/nsa/trig" :dir :system)
(include-book "nonstd/nsa/ln" :dir :system)
(include-book "nonstd/nsa/sqrt" :dir :system)
(local (include-book "arithmetic-5/top" :dir :system))

;;; ---------------- part p1 ----------------
(in-theory (disable binomial-theorem))

(defun tm (k y)
  (if (zp k) 1 (* (tm (1- k) y) y (/ k))))

(defun ep (n x)
  (if (zp n) 0
    (+ (ep (1- n) x) (tm (1- n) x))))

(local
 (defthm tm-is-term
   (implies (natp k)
            (equal (taylor-exp-term x k) (tm k x)))
   :hints (("Goal" :in-theory (enable taylor-exp-term) :induct (tm k x) :expand ((factorial k))))))

(local
 (defthm ep-is-sumlist
   (implies (natp n)
            (equal (sumlist (taylor-exp-list n 0 x)) (ep n x)))
   :hints (("Goal" :induct (ep n x))
           ("Subgoal *1/2" :use ((:instance taylor-exp-list-split (n1 (1- n)) (n2 1) (counter 0)))))))

(defthm realp-tm (implies (realp x) (realp (tm n x))) :rule-classes :type-prescription)
(defthm realp-ep (implies (realp x) (realp (ep n x))) :rule-classes :type-prescription)
(defthm tm-nonneg (implies (and (realp x) (<= 0 x)) (<= 0 (tm n x))) :rule-classes (:rewrite :linear))
(defthm ep-nonneg (implies (and (realp x) (<= 0 x)) (<= 0 (ep n x))) :rule-classes (:rewrite :linear)
  :hints (("Goal" :induct (ep n x) :in-theory (disable tm))))

(local
 (defthm ep-q-step
   (implies (and (realp e) (realp a) (realp x) (<= 0 a) (<= 0 x) (natp n) (<= 2 n))
            (<= (+ (* (+ e (* a 2 x (/ n))) (- 1 x)) (* (* a 2 x (/ n)) x))
                (+ (* e (- 1 x)) (* a x))))
   :hints (("Goal" :use ((:instance (:theorem (implies (and (realp z) (<= 0 z) (realp n) (<= 2 n))
                                                       (<= (* z 2 (/ n)) z)))
                                    (z (* a x))))))))

(local
 (defthm ep-q
   (implies (and (natp n) (<= 2 n) (realp x) (<= 0 x))
            (<= (+ (* (ep n (* 2 x)) (- 1 x))
                   (* (tm (1- n) (* 2 x)) x))
                (+ 1 x)))
   :hints (("Goal" :induct (ep n x))
           ("Subgoal *1/2" :cases ((= n 2)))
           ("Subgoal *1/2.2" :use ((:instance ep-q-step (e (ep (- n 2) (* 2 x)))
                                              (a (tm (- n 2) (* 2 x))) (n (1- n))))
            :expand ((ep n (* 2 x)) (ep (1- n) (* 2 x)) (tm (1- n) (* 2 x)))))))

(local
 (defthm ep-upper
   (implies (and (natp n) (<= 2 n) (realp x) (<= 0 x))
            (<= (* (ep n (* 2 x)) (- 1 x)) (+ 1 x)))
   :hints (("Goal" :use (ep-q (:instance tm-nonneg (n (1- n)) (x (* 2 x)))
                         (:instance (:theorem (implies (and (realp a) (realp b) (<= 0 a) (<= 0 b)) (<= 0 (* a b))))
                                    (a x) (b (tm (1- n) (* 2 x)))))
            :in-theory (disable ep-q ep tm tm-nonneg)))))

(local
 (defthm ep-mono
   (implies (and (natp n) (natp m) (<= m n) (realp x) (<= 0 x))
            (<= (ep m x) (ep n x)))
   :hints (("Goal" :induct (ep n x) :in-theory (disable tm)))))

(local
 (defthm ep-lower
   (implies (and (natp n) (<= 3 n) (realp x) (<= 0 x))
            (<= (+ 1 x (* 1/2 x x)) (ep n x)))
   :hints (("Goal" :use ((:instance ep-mono (m 3)))
            :in-theory (disable ep-mono)))))

(local
 (defthm large-integer-facts
   (and (natp (i-large-integer)) (<= 3 (i-large-integer)))
   :hints (("Goal" :use (i-large-integer-is-large
                         (:instance large->-non-large (x (i-large-integer)) (y 3)))
            :in-theory (disable large->-non-large)))))

(local
 (defthm st-le-lemma
   (implies (and (realp a) (i-limited a) (realp b) (standardp b) (realp c) (standardp c)
                 (<= (* a b) c))
            (<= (* (standard-part a) b) c))
   :hints (("Goal" :use ((:instance standard-part-<= (x (* a b)) (y c)))
            :in-theory (disable standard-part-<=)))))

(local
 (defthm st-ge-lemma
   (implies (and (realp a) (i-limited a) (realp c) (standardp c)
                 (<= c a))
            (<= c (standard-part a)))
   :hints (("Goal" :use ((:instance standard-part-<= (x c) (y a)))
            :in-theory (disable standard-part-<=)))))

(defthm-std exp-upper-bound
  (implies (and (realp x) (<= 0 x))
           (<= (* (acl2-exp (* 2 x)) (- 1 x)) (+ 1 x)))
  :hints (("Goal" :in-theory (e/d (acl2-exp) (ep tm))
           :use ((:instance ep-upper (n (i-large-integer)))
                 (:instance taylor-exp-list-limited (x (* 2 x)))
                 (:instance st-le-lemma (a (ep (i-large-integer) (* 2 x))) (b (- 1 x)) (c (+ 1 x)))))))

(defthm-std exp-lower-bound
  (implies (and (realp x) (<= 0 x))
           (<= (+ 1 x (* 1/2 x x)) (acl2-exp x)))
  :hints (("Goal" :in-theory (e/d (acl2-exp) (ep tm))
           :use ((:instance ep-lower (n (i-large-integer)))
                 (:instance taylor-exp-list-limited)
                 (:instance st-ge-lemma (a (ep (i-large-integer) x)) (c (+ 1 x (* 1/2 x x))))))))

(defthm le-div-intro
  (implies (and (realp a) (realp b) (realp c) (< 0 c) (<= (* a c) b))
           (<= a (/ b c)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil)
(defthm div-le-intro
  (implies (and (realp a) (realp b) (realp c) (< 0 c) (<= b (* a c)))
           (<= (/ b c) a))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil)
(defthm mult-le-mono
  (implies (and (realp a) (realp b) (realp c) (<= 0 c) (<= a b))
           (<= (* a c) (* b c)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil)
(defthm realp-expt-tp (implies (realp x) (realp (expt x k))) :rule-classes :type-prescription)

(defthm sq-gt-1-a (implies (and (realp a) (< 1 a)) (< 1 (* a a)))
  :hints (("Goal" :use ((:instance mult-le-mono (a 1) (b a) (c a)))))
  :rule-classes nil)
(defthm sq-gt-1-b (implies (and (realp a) (< a -1)) (< 1 (* a a)))
  :hints (("Goal" :use ((:instance sq-gt-1-a (a (- a))))))
  :rule-classes nil)
(defthm sq-nonneg (implies (realp b) (<= 0 (* b b)))
  :hints (("Goal" :cases ((<= 0 b)))
          ("Subgoal 2" :use ((:instance mult-le-mono (a b) (b 0) (c (- b)))))
          ("Subgoal 1" :use ((:instance mult-le-mono (a 0) (b b) (c b)))))
  :rule-classes nil)
(defthm sq-le-1-abs
  (implies (and (realp a) (realp b) (equal (+ (* a a) (* b b)) 1))
           (and (<= a 1) (<= -1 a)))
  :hints (("Goal" :use (sq-gt-1-a sq-gt-1-b sq-nonneg)))
  :rule-classes nil)

(defthm sq-pos-strict (implies (and (realp b) (not (equal b 0))) (< 0 (* b b)))
  :hints (("Goal" :cases ((< 0 b)))
          ("Subgoal 2" :use ((:instance (:theorem (implies (and (realp x) (realp y) (< 0 x) (< 0 y)) (< 0 (* x y)))) (x (- b)) (y (- b)))))
          ("Subgoal 1" :use ((:instance (:theorem (implies (and (realp x) (realp y) (< 0 x) (< 0 y)) (< 0 (* x y)))) (x b) (y b)))))
  :rule-classes nil)
(defthm expt2-nonneg (implies (realp b) (<= 0 (expt b 2)))
  :hints (("Goal" :use sq-nonneg))
  :rule-classes (:linear :type-prescription))
(defthm expt2-pos (implies (and (realp b) (not (equal b 0))) (< 0 (expt b 2)))
  :hints (("Goal" :use sq-pos-strict))
  :rule-classes (:linear :type-prescription))

;;; ---------------- part p7 ----------------

(defun sa (n)
  (/ (* (factorial n) (factorial n) (expt (acl2-exp 1) (* 2 n)))
     (expt n (+ (* 2 n) 1))))

(defthm exp-expt
  (implies (and (natp k) (realp x))
           (equal (expt (acl2-exp x) k) (acl2-exp (* k x))))
  :hints (("Goal" :induct (expt (acl2-exp x) k) :in-theory (enable expt))
          ("Subgoal *1/2" :use ((:instance exp-sum (x x) (y (* (1- k) x)))))))

(defthm realp-exp-x (implies (realp x) (realp (acl2-exp x))) :rule-classes :type-prescription)
(defthm pos-exp-x (implies (realp x) (< 0 (acl2-exp x))) :rule-classes :linear)

(local (defthm alg1
  (implies (and (acl2-numberp m) (not (equal m 0)) (acl2-numberp f) (acl2-numberp a) (acl2-numberp b)
                (acl2-numberp c) (not (equal c 0)) (acl2-numberp d) (not (equal d 0)))
           (equal (/ (* (* m f) (* m f) (* a b)) (* c (* m m)))
                  (* (/ (* f f a) d) b (* d (/ c)))))
  :rule-classes nil))

(local (defthm expt-split
  (implies (and (acl2-numberp x) (not (equal x 0)) (integerp i) (integerp j))
           (equal (expt x (+ i j)) (* (expt x i) (expt x j))))
  :rule-classes nil))

(local (defthm g1 (implies (and (acl2-numberp w) (acl2-numberp n) (equal (* w (+ 1 n) (+ 1 n)) 1))
                            (equal (+ w (* (expt n 2) w) (* 2 n w)) 1))
  :rule-classes nil))
(local (defthm g2a (implies (and (acl2-numberp m) (not (equal m 0))) (equal (* (expt m -2) m m) 1)) :rule-classes nil))
(local (defthm g2 (implies (and (integerp n) (<= 0 n)) (equal (* (expt (+ 1 n) -2) (+ 1 n) (+ 1 n)) 1))
  :hints (("Goal" :use ((:instance g2a (m (+ 1 n)))) :in-theory (theory 'minimal-theory)))))
(local (defthm ugly-1
  (implies (and (integerp n) (<= 0 n))
           (equal (+ (expt (+ 1 n) -2) (* (expt n 2) (expt (+ 1 n) -2)) (* 2 n (expt (+ 1 n) -2))) 1))
  :hints (("Goal" :use ((:instance g1 (w (expt (+ 1 n) -2))) g2) :in-theory (theory 'minimal-theory)))))
(defthm sa-step
  (implies (and (natp n) (< 0 n))
           (equal (sa (+ 1 n))
                  (* (sa n) (expt (acl2-exp 1) 2) (expt (/ n (+ 1 n)) (+ 1 (* 2 n))))))
  :hints (("Goal" :expand ((factorial (+ 1 n)))
           :in-theory (e/d (sa) (exp-expt factorial expt))
           :use ((:instance alg1 (m (+ 1 n)) (f (factorial n)) (a (expt (acl2-exp 1) (* 2 n)))
                            (b (expt (acl2-exp 1) 2)) (c (expt (+ 1 n) (+ 1 (* 2 n))))
                            (d (expt n (+ 1 (* 2 n)))))
                 (:instance expt-split (x (acl2-exp 1)) (i (* 2 n)) (j 2))
                 (:instance expt-split (x (+ 1 n)) (i (+ 1 (* 2 n))) (j 2))
                 (:instance (:theorem (implies (and (acl2-numberp x) (acl2-numberp y) (not (equal y 0)) (natp k))
                                               (equal (expt (/ x y) k) (/ (expt x k) (expt y k)))))
                            (x n) (y (+ 1 n)) (k (+ 1 (* 2 n))))))))

(defthm sa-nonneg (implies (natp n) (<= 0 (sa n))) :rule-classes (:rewrite :linear))
(defthm realp-sa (implies (natp n) (realp (sa n))) :rule-classes (:rewrite :type-prescription))

(local
 (defthm c1
   (implies (and (natp n) (< 0 n))
            (<= (acl2-exp (* 2 (/ (+ 1 (* 2 n))))) (/ (+ 1 n) n)))
   :hints (("Goal" :use ((:instance exp-upper-bound (x (/ (+ 1 (* 2 n)))))
                         (:instance mult-le-mono (a (* (acl2-exp (* 2 (/ (+ 1 (* 2 n))))) (- 1 (/ (+ 1 (* 2 n))))))
                                    (b (+ 1 (/ (+ 1 (* 2 n))))) (c (+ 1 (* 2 n))))
                         (:instance le-div-intro (a (acl2-exp (* 2 (/ (+ 1 (* 2 n)))))) (b (+ 2 (* 2 n))) (c (* 2 n))))
            :in-theory (disable exp-upper-bound)))))

(local
 (defthm c2
   (implies (and (natp n) (< 0 n))
            (<= (expt (acl2-exp 1) 2) (expt (/ (+ 1 n) n) (+ 1 (* 2 n)))))
   :hints (("Goal" :use (c1 (:instance expt-is-non-decreasing-for-non-negatives
                                       (x (acl2-exp (* 2 (/ (+ 1 (* 2 n)))))) (y (/ (+ 1 n) n)) (n (+ 1 (* 2 n))))
                            (:instance exp-expt (x (* 2 (/ (+ 1 (* 2 n))))) (k (+ 1 (* 2 n))))
                            (:instance exp-expt (x 1) (k 2)))
            :in-theory (disable c1 expt-is-non-decreasing-for-non-negatives exp-expt)))))

(local
 (defthm c3
   (implies (and (realp s) (<= 0 s) (realp e) (realp p) (< 0 p) (realp q) (<= e q) (equal (* p q) 1))
            (<= (* s e p) s))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(defthm pq-gen
  (implies (and (acl2-numberp a) (acl2-numberp b) (not (equal a 0)) (not (equal b 0)) (integerp k))
           (equal (* (expt (/ a b) k) (expt (/ b a) k)) 1))
  :rule-classes nil)
(defthm pq-1
  (implies (and (natp n) (< 0 n) (integerp k))
           (equal (* (expt (/ n (+ 1 n)) k) (expt (/ (+ 1 n) n) k)) 1))
  :hints (("Goal" :use ((:instance pq-gen (a n) (b (+ 1 n)))) :in-theory (theory 'minimal-theory))))

(defthm pq-pos
  (implies (and (natp n) (< 0 n) (integerp k))
           (< 0 (expt (/ n (+ 1 n)) k)))
  :rule-classes (:rewrite :linear))

(defthm sa-decreasing
  (implies (and (natp n) (< 0 n))
           (<= (sa (+ 1 n)) (sa n)))
  :hints (("Goal" :use (c2 (:instance pq-1 (k (+ 1 (* 2 n)))) (:instance pq-pos (k (+ 1 (* 2 n))))
                        (:instance c3 (s (sa n)) (e (expt (acl2-exp 1) 2))
                                   (p (expt (/ n (+ 1 n)) (+ 1 (* 2 n))))
                                   (q (expt (/ (+ 1 n) n) (+ 1 (* 2 n))))))
           :in-theory (union-theories '(sa-step sa-nonneg realp-sa realp-exp-x natp-compound-recognizer realp-expt-tp (:type-prescription expt)) (theory 'minimal-theory)))))

(defun sb (n) (* (sa n) (acl2-exp (- (/ 2 n)))))

(defmacro ym (n) `(* 2 (+ (* ,n ,n) ,n 1)))
(defmacro yd (n) `(* (+ 1 (* 2 ,n)) (* ,n (+ 1 ,n))))
(defmacro yy (n) `(* (ym ,n) (/ (yd ,n))))

(local (defthm s-a (implies (and (natp n) (< 0 n))
   (let ((m (ym n)) (d (yd n)))
     (equal (- (+ (* n m d) (* 1/2 n m m)) (* d d)) (* n (+ n 2) (+ (* 3 n n) (* 2 n) 1)))))))
(local (defthm s-b (implies (and (acl2-numberp m) (acl2-numberp d) (acl2-numberp n) (not (equal d 0)))
   (equal (* (+ (* m (/ d)) (* 1/2 (* m (/ d)) (* m (/ d)))) (* n d d)) (+ (* n m d) (* 1/2 n m m))))
   :rule-classes nil))
(local (defthm s-d (implies (and (realp x) (realp d) (realp n) (< 0 n) (< 0 d) (<= (* d d) (* x (* n d d))))
   (<= (/ n) x))
  :hints (("Goal" :use ((:instance div-le-intro (a x) (b (* d d)) (c (* n d d))))))
  :rule-classes nil))

(local (defthm d-pos (implies (and (natp n) (< 0 n)) (and (< 0 (yd n)) (rationalp (yd n)) (rationalp (ym n))))
   :rule-classes nil))
(local (defthm p-pos (implies (and (natp n) (< 0 n)) (<= 0 (* n (+ n 2) (+ (* 3 n n) (* 2 n) 1))))
   :rule-classes nil))
(local
 (defthm d1
   (implies (and (natp n) (< 0 n))
            (<= (+ 1 (/ n)) (+ 1 (yy n) (* 1/2 (yy n) (yy n)))))
   :hints (("Goal" :use (s-a (:instance s-b (m (ym n)) (d (yd n)))
                         (:instance s-d (x (+ (yy n) (* 1/2 (yy n) (yy n)))) (d (yd n)))
                         d-pos p-pos)
            :in-theory (union-theories '(natp-compound-recognizer) (theory 'minimal-theory))))))

(local
 (defthm d1b
   (implies (and (natp n) (< 0 n))
            (<= (/ (+ 1 n) n) (acl2-exp (yy n))))
   :hints (("Goal" :use (d1 (:instance exp-lower-bound (x (yy n))))
            :in-theory (disable d1 exp-lower-bound)))))

(local
 (defthm d2
   (implies (and (natp n) (< 0 n))
            (<= (expt (/ (+ 1 n) n) (+ 1 (* 2 n))) (acl2-exp (* (+ 1 (* 2 n)) (yy n)))))
   :hints (("Goal" :use (d1b (:instance expt-is-non-decreasing-for-non-negatives
                                       (y (acl2-exp (yy n))) (x (/ (+ 1 n) n)) (n (+ 1 (* 2 n))))
                            (:instance exp-expt (x (yy n)) (k (+ 1 (* 2 n)))))
            :in-theory (disable d1b expt-is-non-decreasing-for-non-negatives exp-expt)))))

(local (defthm s-c (implies (and (natp n) (< 0 n))
   (equal (* (+ 2 (- (/ 2 (+ 1 n))) (/ 2 n)) (* n (+ 1 n))) (ym n)))))
(local (defthm s-e (implies (and (acl2-numberp a) (acl2-numberp b) (acl2-numberp m) (not (equal a 0)) (not (equal b 0)))
   (equal (* a (* m (/ (* a b)))) (* m (/ b))))
   :rule-classes nil))
(local (defthm s-f (implies (and (acl2-numberp s) (acl2-numberp b) (acl2-numberp m) (not (equal b 0)) (equal (* s b) m))
   (equal (* m (/ b)) s))
   :rule-classes nil))

(local
 (defthm d3
   (implies (and (natp n) (< 0 n))
            (equal (* (+ 1 (* 2 n)) (yy n)) (+ 2 (- (/ 2 (+ 1 n))) (/ 2 n))))
   :hints (("Goal" :use (s-c (:instance s-e (a (+ 1 (* 2 n))) (b (* n (+ 1 n))) (m (ym n)))
                         (:instance s-f (s (+ 2 (- (/ 2 (+ 1 n))) (/ 2 n))) (b (* n (+ 1 n))) (m (ym n))))
            :in-theory (union-theories '(natp-compound-recognizer) (theory 'minimal-theory))))))

(local
 (defthm d4
   (implies (and (natp n) (< 0 n))
            (equal (acl2-exp (+ 2 (- (/ 2 (+ 1 n))) (/ 2 n)))
                   (* (expt (acl2-exp 1) 2) (acl2-exp (- (/ 2 (+ 1 n)))) (acl2-exp (/ 2 n)))))
   :hints (("Goal" :use ((:instance exp-sum (x 2) (y (+ (- (/ 2 (+ 1 n))) (/ 2 n))))
                         (:instance exp-sum (x (- (/ 2 (+ 1 n)))) (y (/ 2 n)))
                         (:instance exp-expt (x 1) (k 2)))
            :in-theory (disable exp-sum exp-expt)))))

(local
 (defthm d5
   (implies (realp x)
            (equal (* (acl2-exp x) (acl2-exp (- x))) 1))
   :hints (("Goal" :use ((:instance exp-sum (y (- x))))
            :in-theory (disable exp-sum)))))

(local
 (defthm d6a
   (implies (and (realp s) (<= 0 s) (realp e2) (realp p) (< 0 p)
                 (realp x) (realp w) (< 0 w)
                 (<= (/ p) (* e2 x w)))
            (<= (* s (/ w)) (* (* s e2 p) x)))
   :hints (("Goal" :use ((:instance mult-le-mono (a (/ p)) (b (* e2 x w)) (c (* p (/ w))))
                         (:instance mult-le-mono (a (/ w)) (b (* e2 x p)) (c s)))))
   :rule-classes nil))

(local (defthm inv-unique (implies (and (acl2-numberp p) (equal (* p q) 1)) (equal q (/ p))) :rule-classes nil))

(local
 (defthm d6
   (implies (and (realp s) (<= 0 s) (realp e2) (realp p) (< 0 p) (realp q) (equal (* p q) 1)
                 (realp x) (realp w) (< 0 w) (realp z) (equal (* w z) 1)
                 (<= q (* e2 x w)))
            (<= (* s z) (* (* s e2 p) x)))
   :hints (("Goal" :use (d6a inv-unique (:instance inv-unique (p w) (q z)))
            :in-theory (theory 'minimal-theory)))
   :rule-classes nil))

(defthm sb-increasing
  (implies (and (natp n) (< 0 n))
           (<= (sb n) (sb (+ 1 n))))
  :hints (("Goal" :use (d2 d3 d4 (:instance d5 (x (/ 2 n)))
                        (:instance pq-1 (k (+ 1 (* 2 n)))) (:instance pq-pos (k (+ 1 (* 2 n))))
                        (:instance d6 (s (sa n)) (e2 (expt (acl2-exp 1) 2))
                                   (p (expt (/ n (+ 1 n)) (+ 1 (* 2 n))))
                                   (q (expt (/ (+ 1 n) n) (+ 1 (* 2 n))))
                                   (x (acl2-exp (- (/ 2 (+ 1 n)))))
                                   (w (acl2-exp (/ 2 n)))
                                   (z (acl2-exp (- (/ 2 n))))))
           :in-theory (union-theories '(sb sa-step sa-nonneg realp-sa realp-exp-x pos-exp-x natp-compound-recognizer realp-expt-tp (:type-prescription expt)) (theory 'minimal-theory)))))


;;; ---------------- part p8 ----------------

(defun ind-up (m n) (if (or (zp m) (<= m n)) t (ind-up (1- m) n)))


(defthm sa-mono
  (implies (and (natp n) (natp m) (< 0 n) (<= n m))
           (<= (sa m) (sa n)))
  :hints (("Goal" :induct (ind-up m n) :in-theory (disable sa))
          ("Subgoal *1/2" :use ((:instance sa-decreasing (n (1- m)))))))

(defthm sb-mono
  (implies (and (natp n) (natp m) (< 0 n) (<= n m))
           (<= (sb n) (sb m)))
  :hints (("Goal" :induct (ind-up m n) :in-theory (disable sb))
          ("Subgoal *1/2" :use ((:instance sb-increasing (n (1- m)))))))

(defthm exp-neg-le-1
  (implies (and (natp n) (< 0 n)) (<= (acl2-exp (- (/ 2 n))) 1))
  :hints (("Goal" :use ((:instance acl2-exp-is-non-decreasing (x (- (/ 2 n))) (y 0))))))

(defthm sb-le-sa
  (implies (and (natp n) (< 0 n))
           (<= (sb n) (sa n)))
  :hints (("Goal" :use (exp-neg-le-1
                        (:instance mult-le-mono (a (acl2-exp (- (/ 2 n)))) (b 1) (c (sa n))))
           :in-theory (disable exp-neg-le-1 sa acl2-exp---x))))

(defthm sa-1 (equal (sa 1) (expt (acl2-exp 1) 2))
  :hints (("Goal" :expand ((factorial 1)) :in-theory (disable exp-expt))))

(defthm sb-1 (equal (sb 1) 1)
  :hints (("Goal" :in-theory (disable sa)
           :use ((:instance d5 (x 2)) (:instance exp-expt (x 1) (k 2))))))

(defthm sa-lower
  (implies (and (natp n) (< 0 n)) (<= 1 (sa n)))
  :hints (("Goal" :use (sb-le-sa (:instance sb-mono (n 1) (m n))) :in-theory (disable sb sa sb-le-sa sb-mono))))

(defthm sa-upper
  (implies (and (natp n) (< 0 n)) (<= (sa n) (expt (acl2-exp 1) 2)))
  :hints (("Goal" :use ((:instance sa-mono (n 1) (m n))) :in-theory (disable sa sa-mono))))

;;; ---------------- part p9 ----------------

(defthm standardp-e (standardp (acl2-exp 1))
  :hints (("Goal" :use ((:instance standard-exp (x 1))))))

(local (defthm ns1
  (implies (and (natp n) (i-large n)) (i-small (- (/ 2 n))))
  :hints (("Goal" :use ((:instance limited*small->small (x -2) (y (/ n))))
           :in-theory (disable limited*small->small)))))

(local (defthm ns2
  (implies (and (natp n) (i-large n)) (i-small (- 1 (acl2-exp (- (/ 2 n))))))
  :hints (("Goal" :use ((:instance exp-of-infinitesimal (x (- (/ 2 n)))))
           :in-theory (e/d (i-close) (exp-of-infinitesimal ns1 acl2-exp---x))))))

(defthm sa-limited
  (implies (and (natp n) (< 0 n)) (i-limited (sa n)))
  :hints (("Goal" :use ((:instance limited-squeeze (a 1) (b (acl2-exp 2)) (x (sa n)))
                        sa-upper sa-lower (:instance standard-exp (x 2)))
           :in-theory (disable limited-squeeze sa sa-upper sa-lower))))

(local (defthm large-pos (implies (and (natp n) (i-large n)) (< 0 n)) :rule-classes :forward-chaining))

(local (defthm ns4
  (implies (and (natp n) (natp m) (<= n m) (i-large n))
           (i-small (- (sa n) (sa m))))
  :hints (("Goal" :use ((:instance small-if-<-small (x (* (sa n) (- 1 (acl2-exp (- (/ 2 n))))))
                                   (y (- (sa n) (sa m))))
                        (:instance limited*small->small (x (sa n)) (y (- 1 (acl2-exp (- (/ 2 n))))))
                        sa-limited ns2 sa-mono (:instance sb-mono (m m)) (:instance sb-le-sa (n m)))
           :in-theory (disable small-if-<-small limited*small->small sa-limited ns2 sa sa-mono sb-mono sb-le-sa acl2-exp---x)))))

(defthm sa-close
  (implies (and (natp n) (natp m) (i-large n) (i-large m))
           (i-close (sa n) (sa m)))
  :hints (("Goal" :cases ((<= n m)))
          ("Subgoal 2" :use ((:instance ns4 (n m) (m n))) :in-theory (e/d (i-close) (sa)))
          ("Subgoal 1" :use ((:instance ns4)) :in-theory (e/d (i-close) (sa)))))

;;; ---------------- part p10 ----------------

(defun wp (m) (if (zp m) 1 (* (wp (1- m)) (/ (- (* 2 m) 1) (* 2 m)))))

(defthm wp-pos (< 0 (wp m)) :rule-classes (:rewrite :linear))
(defthm realp-wp (rationalp (wp m)) :rule-classes :type-prescription)

(defun pow4 (m) (if (zp m) 1 (* 4 (pow4 (1- m)))))
(defthm pow4-pos (< 0 (pow4 m)) :rule-classes (:rewrite :linear))
(defthm pow4-type (integerp (pow4 m)) :rule-classes :type-prescription)

(defthm wp-factorial
  (implies (natp m)
           (equal (* (wp m) (pow4 m) (factorial m) (factorial m)) (factorial (* 2 m))))
  :hints (("Goal" :induct (wp m))
          ("Subgoal *1/2" :expand ((factorial (* 2 m)) (factorial (+ -1 (* 2 m))) (factorial m) (pow4 m) (wp m)))))

(defthm factorial-pos (< 0 (factorial n)) :rule-classes (:rewrite :linear :type-prescription)
  :hints (("Goal" :in-theory (enable factorial))))
(defthm pow4-expt (implies (natp m) (equal (pow4 m) (expt 4 m))))

(local (defthm alg2
  (implies (and (acl2-numberp f) (not (equal f 0)) (acl2-numberp w) (acl2-numberp p) (not (equal p 0))
                (acl2-numberp e) (not (equal e 0)) (acl2-numberp k) (not (equal k 0))
                (acl2-numberp m) (not (equal m 0))
                (equal bigf (* w (* p (* f f))))
                (equal e2 (* e e))
                (equal k2 (* 2 (* p (* p (* k (* k (/ m))))))))
           (equal (* (* (/ (* f (* f e)) k) (/ (* f (* f e)) k)) (* m (* w w)))
                  (* 2 (/ (* bigf (* bigf e2)) k2))))
  :rule-classes nil))

(local (defthm ef1
  (implies (natp m)
           (equal (expt (acl2-exp 1) (* 2 (* 2 m))) (* (expt (acl2-exp 1) (* 2 m)) (expt (acl2-exp 1) (* 2 m)))))
  :hints (("Goal" :in-theory (disable exp-expt)))))

(local (defthm ef2
  (implies (and (natp m) (< 0 m))
           (equal (expt (* 2 m) (+ (* 2 (* 2 m)) 1))
                  (* 2 (* (pow4 m) (* (pow4 m) (* (expt m (+ (* 2 m) 1)) (* (expt m (+ (* 2 m) 1)) (/ m))))))))))

(local (defthm wpf2
  (implies (natp m)
           (equal (factorial (* 2 m)) (* (wp m) (* (pow4 m) (* (factorial m) (factorial m))))))
  :hints (("Goal" :use wp-factorial :in-theory (disable wp-factorial pow4-expt)))))

(defthm sa-wallis-relation
  (implies (and (natp m) (< 0 m))
           (equal (* (* (sa m) (sa m)) (* m (* (wp m) (wp m))))
                  (* 2 (sa (* 2 m)))))
  :hints (("Goal" :use (ef1 ef2 wpf2
                        (:instance alg2 (f (factorial m)) (w (wp m)) (p (pow4 m)) (e (expt (acl2-exp 1) (* 2 m)))
                                   (k (expt m (+ (* 2 m) 1)))
                                   (bigf (factorial (* 2 m))) (e2 (expt (acl2-exp 1) (* 2 (* 2 m))))
                                   (k2 (expt (* 2 m) (+ (* 2 (* 2 m)) 1)))))
           :in-theory (union-theories '(sa natp-compound-recognizer factorial-pos pow4-pos wp-pos pos-exp-x realp-exp-x
                                         (:type-prescription expt) realp-expt-tp (:type-prescription factorial)
                                         (:type-prescription wp) (:type-prescription pow4))
                                       (theory 'minimal-theory)))))

;;; ---------------- part p2 ----------------
(encapsulate ()
(local (include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/sin-cos-minimal" :dir :system))
(local (in-theory (disable expt-minus)))


(defthm sine-bounds
  (implies (realp x)
           (and (<= (acl2-sine x) 1) (<= -1 (acl2-sine x))))
  :hints (("Goal" :use ((:instance sq-le-1-abs (a (acl2-sine x)) (b (acl2-cosine x)))
                        (:instance sin**2+cos**2))
           :in-theory (disable sin**2+cos**2)))
  :rule-classes (:rewrite :linear))

(defthm cosine-bounds
  (implies (realp x)
           (and (<= (acl2-cosine x) 1) (<= -1 (acl2-cosine x))))
  :hints (("Goal" :use ((:instance sq-le-1-abs (b (acl2-sine x)) (a (acl2-cosine x)))
                        (:instance sin**2+cos**2))
           :in-theory (disable sin**2+cos**2)))
  :rule-classes (:rewrite :linear))

(defthm sine-limited (implies (realp x) (i-limited (acl2-sine x)))
  :hints (("Goal" :use ((:instance limited-squeeze (a -1) (b 1) (x (acl2-sine x))))
           :in-theory (disable limited-squeeze))))
(defthm cosine-limited (implies (realp x) (i-limited (acl2-cosine x)))
  :hints (("Goal" :use ((:instance limited-squeeze (a -1) (b 1) (x (acl2-cosine x))))
           :in-theory (disable limited-squeeze))))

(defthm sin-aux-1 (implies (acl2-numberp h) (equal (/ (- 0 s) (- 0 h)) (/ s h)))
  :rule-classes nil)

(defthm sin-small-angle
  (implies (and (realp h) (i-small h) (not (equal h 0)))
           (i-small (- (/ (acl2-sine h) h) 1)))
  :hints (("Goal" :use ((:instance acl2-sine-derivative (x 0) (y h))
                        (:instance sin-aux-1 (s (acl2-sine h))))
           :in-theory (union-theories '(i-close cosine-0 sine-0 realp-sine (:executable-counterpart unary--) unicity-of-0 i-small-uminus fix commutativity-of-+) (theory 'minimal-theory)))))

(defthm cos-aux-1 (implies (acl2-numberp h) (equal (/ (- 1 c) (- 0 h)) (- (/ (- c 1) h) 0)))
  :rule-classes nil)

(defthm cos-small-angle
  (implies (and (realp h) (i-small h) (not (equal h 0)))
           (i-small (/ (- (acl2-cosine h) 1) h)))
  :hints (("Goal" :use ((:instance acl2-cosine-derivative (x 0) (y h))
                        (:instance cos-aux-1 (c (acl2-cosine h))))
           :in-theory (union-theories '(i-close cosine-0 sine-0 realp-cosine (:executable-counterpart unary--) unicity-of-0 i-small-uminus fix commutativity-of-+) (theory 'minimal-theory)))))

(defthm small-by-equal
  (implies (and (equal x y) (i-small y)) (i-small x))
  :rule-classes nil)

(defthm small-comb2
  (implies (and (i-limited a) (i-small u) (i-limited b) (i-small v))
           (i-small (+ (* a u) (* b v))))
  :rule-classes nil)

(local (defthm u1-alg
  (implies (and (realp x) (realp h) (not (equal h 0)))
           (equal (- (/ (- (acl2-sine (+ x h)) (acl2-sine x)) h) (acl2-cosine x))
                  (+ (* (acl2-sine x) (/ (- (acl2-cosine h) 1) h))
                     (* (acl2-cosine x) (- (/ (acl2-sine h) h) 1)))))))

(defthm sine-uniform-derivative
  (implies (and (realp x) (realp h) (i-small h) (not (equal h 0)))
           (i-small (- (/ (- (acl2-sine (+ x h)) (acl2-sine x)) h) (acl2-cosine x))))
  :hints (("Goal" :use (u1-alg sin-small-angle cos-small-angle
                        (:instance small-comb2 (a (acl2-sine x)) (u (/ (- (acl2-cosine h) 1) h))
                                   (b (acl2-cosine x)) (v (- (/ (acl2-sine h) h) 1)))
                        (:instance small-by-equal (x (- (/ (- (acl2-sine (+ x h)) (acl2-sine x)) h) (acl2-cosine x)))
                                   (y (+ (* (acl2-sine x) (/ (- (acl2-cosine h) 1) h))
                                         (* (acl2-cosine x) (- (/ (acl2-sine h) h) 1))))))
           :in-theory (union-theories '(sine-limited cosine-limited) (theory 'minimal-theory)))))

(defthm i-limited-uminus (implies (i-limited x) (i-limited (- x))))

(local (defthm u2-alg
  (implies (and (realp x) (realp h) (not (equal h 0)))
           (equal (+ (/ (- (acl2-cosine (+ x h)) (acl2-cosine x)) h) (acl2-sine x))
                  (+ (* (acl2-cosine x) (/ (- (acl2-cosine h) 1) h))
                     (* (- (acl2-sine x)) (- (/ (acl2-sine h) h) 1)))))))

(defthm cosine-uniform-derivative
  (implies (and (realp x) (realp h) (i-small h) (not (equal h 0)))
           (i-small (+ (/ (- (acl2-cosine (+ x h)) (acl2-cosine x)) h) (acl2-sine x))))
  :hints (("Goal" :use (u2-alg sin-small-angle cos-small-angle
                        (:instance i-limited-uminus (x (acl2-sine x)))
                        (:instance small-comb2 (a (acl2-cosine x)) (u (/ (- (acl2-cosine h) 1) h))
                                   (b (- (acl2-sine x))) (v (- (/ (acl2-sine h) h) 1)))
                        (:instance small-by-equal (x (+ (/ (- (acl2-cosine (+ x h)) (acl2-cosine x)) h) (acl2-sine x)))
                                   (y (+ (* (acl2-cosine x) (/ (- (acl2-cosine h) 1) h))
                                         (* (- (acl2-sine x)) (- (/ (acl2-sine h) h) 1))))))
           :in-theory (union-theories '(sine-limited cosine-limited) (theory 'minimal-theory)))))

) ; end encapsulate (sin-cos-minimal is local here)

;;; ---------------- part p3 ----------------


(defun rterm (m u v)
  (- (- (expt u m) (expt v m)) (* m (expt v (- m 1)) (- u v))))

(defthm abs-expt
  (implies (and (realp v) (natp k))
           (equal (abs (expt v k)) (expt (abs v) k)))
  :hints (("Goal" :induct (expt v k) :in-theory (enable expt))))

(defthm abs-expt-le-1
  (implies (and (realp v) (<= (abs v) 1) (natp k))
           (<= (abs (expt v k)) 1))
  :hints (("Goal" :use ((:instance expt-is-non-decreasing-for-non-negatives (x (abs v)) (y 1) (n k)))
           :in-theory (disable expt-is-non-decreasing-for-non-negatives))))

(local (defthm rterm-step
  (implies (and (natp m) (< 0 m) (realp u) (realp v))
           (equal (rterm (+ 1 m) u v)
                  (+ (* u (rterm m u v)) (* m (expt v (- m 1)) (* (- u v) (- u v))))))
  :hints (("Goal" :use ((:instance (:theorem (implies (and (natp m) (< 0 m) (realp v)) (equal (expt v m) (* v (expt v (- m 1))))))))
           :in-theory (disable expt)))))

(local (defthm abs-prod-le
  (implies (and (realp a) (realp b) (<= (abs a) 1))
           (<= (abs (* a b)) (abs b)))
  :hints (("Goal" :use ((:instance mult-le-mono (a (abs a)) (b 1) (c (abs b))))
           :cases ((<= 0 a)) ) ("Subgoal 2" :cases ((<= 0 b))) ("Subgoal 1" :cases ((<= 0 b))))
  :rule-classes nil))

(defthm realp-abs (implies (realp x) (realp (abs x))) :rule-classes :type-prescription)
(defthm abs-nonneg (<= 0 (abs x)) :rule-classes :linear)
(defthm abs-tri (implies (and (realp a) (realp b)) (<= (abs (+ a b)) (+ (abs a) (abs b))))
  :rule-classes nil)
(local (defthm abs-of-nonneg (implies (and (realp a) (<= 0 a)) (equal (abs a) a))))

(local (defthm abs-step
  (implies (and (realp u) (realp r) (realp w) (realp d) (natp k) (<= 0 d) (equal m (+ 1 k))
                (<= (abs u) 1) (<= (abs w) 1) (<= (abs r) (* k k d)))
           (<= (abs (+ (* u r) (* k (* w d)))) (* m m d)))
  :hints (("Goal" :use ((:instance abs-prod-le (a u) (b r))
                        (:instance abs-prod-le (a w) (b (* k d)))
                        (:instance abs-tri (a (* u r)) (b (* k (* w d))))
                        (:instance mult-le-mono (a 0) (b k) (c d)))
           :in-theory (disable abs)))
  :rule-classes nil))

(defun nat-ind (m) (if (zp m) 0 (nat-ind (1- m))))

(defthm realp-rterm (implies (and (realp u) (realp v) (integerp m)) (realp (rterm m u v))) :rule-classes :type-prescription)
(local (defthm m-1+1 (implies (acl2-numberp m) (equal (+ 1 (+ -1 m)) m))))
(local (defthm rterm-base (implies (and (realp u) (realp v) (natp m) (<= m 1)) (equal (rterm m u v) 0)) :hints (("Goal" :cases ((= m 0) (= m 1))))))

(defthm rterm-bound
  (implies (and (natp m) (realp u) (realp v) (<= (abs u) 1) (<= (abs v) 1))
           (<= (abs (rterm m u v)) (* m m (- u v) (- u v))))
  :hints (("Goal" :induct (nat-ind m))
          ("Subgoal *1/2" :cases ((<= m 1)))
          ("Subgoal *1/2.1" :use ((:instance sq-nonneg (b (- u v)))
                                  (:instance mult-le-mono (a 0) (b (* m m)) (c (* (- u v) (- u v))))))
          ("Subgoal *1/2.2" :use ((:instance rterm-step (m (1- m)))
                                  (:instance abs-step (k (1- m)) (r (rterm (1- m) u v)) (w (expt v (- (1- m) 1)))
                                             (d (* (- u v) (- u v))))
                                  (:instance abs-expt-le-1 (k (- (1- m) 1)))
                                  (:instance sq-nonneg (b (- u v))))
           :in-theory (union-theories '(m-1+1 realp-rterm realp-expt-tp natp-compound-recognizer zp natp
                                        (:type-prescription abs) realp-abs)
                                      (theory 'minimal-theory)))))

(local (defthm rh-1 (implies (and (realp k) (realp d) (realp h) (not (equal h 0)))
                             (equal (abs (* k k d (/ d h))) (* (* k k d d) (/ (abs h)))))
  :hints (("Goal" :cases ((< 0 h)))) ))
(local (defthm rh-2 (implies (and (realp r) (realp h) (not (equal h 0)))
                             (equal (abs (/ r h)) (* (abs r) (/ (abs h)))))
  :hints (("Goal" :cases ((< 0 h)))) ))
(local (defthm abs-h-pos (implies (and (realp h) (not (equal h 0))) (and (< 0 (abs h)) (realp (/ (abs h))) (<= 0 (/ (abs h)))))
  :rule-classes nil))
(defthm rh-bound
  (implies (and (realp r) (realp h) (not (equal h 0)) (realp d) (realp k)
                (<= (abs r) (* k k d d)))
           (<= (abs (/ r h)) (abs (* k k d (/ d h)))))
  :hints (("Goal" :use ((:instance mult-le-mono (a (abs r)) (b (* k k d d)) (c (/ (abs h))))
                        rh-1 rh-2 abs-h-pos)
           :in-theory (union-theories '(realp-abs (:type-prescription abs)) (theory 'minimal-theory))))
  :rule-classes nil)

(defthm expt-facts-2
  (implies (and (natp m) (realp v))
           (and (equal (expt v (+ m 1)) (* (expt v m) v))
                (equal (* m (expt v (+ m 1))) (* m (* (expt v (- m 1)) (* v v))))))
  :hints (("Goal" :cases ((= m 0))))
  :rule-classes nil)


;;; ---------------- part p4 ----------------

(local (defthm alg3
  (implies (and (realp u) (realp v) (realp c) (realp h) (not (equal h 0)) (natp m))
           (equal (- (/ (- (expt u m) (expt v m)) h) (* m (expt v (- m 1)) c))
                  (+ (/ (rterm m u v) h) (* (* m (expt v (- m 1))) (- (/ (- u v) h) c)))))
  :rule-classes nil))

(local (defthm alg3b
  (implies (and (realp u) (realp v) (realp h) (not (equal h 0)))
           (equal (- u v) (* h (/ (- u v) h))))
  :rule-classes nil))

(local (defthm lim-plus-small
  (implies (and (i-limited c) (i-small (- q c)) (acl2-numberp q)) (i-limited q))
  :hints (("Goal" :use ((:instance i-limited-plus (x c) (y (- q c))) (:instance small-are-limited (x (- q c))))
           :in-theory (disable i-limited-plus small-are-limited)))
  :rule-classes nil))

(defthm lim-coef
  (implies (and (natp m) (standardp m) (realp v) (<= (abs v) 1))
           (i-limited (* m (expt v (- m 1)))))
  :hints (("Goal" :cases ((= m 0)))
          ("Subgoal 2" :use ((:instance abs-expt-le-1 (k (- m 1)))
                             (:instance limited-squeeze (a -1) (b 1) (x (expt v (- m 1))))
                             (:instance i-limited-times (x m) (y (expt v (- m 1)))))
           :in-theory (union-theories '(abs natp standards-are-limited realp-expt-tp) (theory 'minimal-theory)))))

(defthm sine-abs-le-1 (implies (realp x) (<= (abs (acl2-sine x)) 1)))

(defthm spow-uniform-derivative
  (implies (and (natp m) (standardp m) (realp x) (realp h) (i-small h) (not (equal h 0)))
           (i-small (- (/ (- (expt (acl2-sine (+ x h)) m) (expt (acl2-sine x) m)) h)
                       (* m (expt (acl2-sine x) (- m 1)) (acl2-cosine x)))))
  :hints (("Goal"
           :use ((:instance alg3 (u (acl2-sine (+ x h))) (v (acl2-sine x)) (c (acl2-cosine x)))
                 (:instance alg3b (u (acl2-sine (+ x h))) (v (acl2-sine x)))
                 sine-uniform-derivative
                 (:instance lim-plus-small (c (acl2-cosine x))
                            (q (/ (- (acl2-sine (+ x h)) (acl2-sine x)) h)))
                 (:instance small*limited->small (x h) (y (/ (- (acl2-sine (+ x h)) (acl2-sine x)) h)))
                 (:instance rh-bound (r (rterm m (acl2-sine (+ x h)) (acl2-sine x))) (k m)
                            (d (- (acl2-sine (+ x h)) (acl2-sine x))))
                 (:instance rterm-bound (u (acl2-sine (+ x h))) (v (acl2-sine x)))
                 (:instance small*limited->small (x (- (acl2-sine (+ x h)) (acl2-sine x)))
                            (y (/ (- (acl2-sine (+ x h)) (acl2-sine x)) h)))
                 (:instance limited*small->small (x m) (y (* (- (acl2-sine (+ x h)) (acl2-sine x))
                                                            (/ (- (acl2-sine (+ x h)) (acl2-sine x)) h))))
                 (:instance limited*small->small (x m) (y (* m (* (- (acl2-sine (+ x h)) (acl2-sine x))
                                                            (/ (- (acl2-sine (+ x h)) (acl2-sine x)) h)))))
                 (:instance small-if-<-small (x (* m m (- (acl2-sine (+ x h)) (acl2-sine x))
                                                   (/ (- (acl2-sine (+ x h)) (acl2-sine x)) h)))
                            (y (/ (rterm m (acl2-sine (+ x h)) (acl2-sine x)) h)))
                 (:instance lim-coef (v (acl2-sine x)))
                 (:instance limited*small->small (x (* m (expt (acl2-sine x) (- m 1))))
                            (y (- (/ (- (acl2-sine (+ x h)) (acl2-sine x)) h) (acl2-cosine x))))
                 (:instance i-small-plus (x (/ (rterm m (acl2-sine (+ x h)) (acl2-sine x)) h))
                            (y (* (* m (expt (acl2-sine x) (- m 1)))
                                  (- (/ (- (acl2-sine (+ x h)) (acl2-sine x)) h) (acl2-cosine x)))))
                 (:instance small-by-equal (x (- (/ (- (expt (acl2-sine (+ x h)) m) (expt (acl2-sine x) m)) h)
                                                 (* m (expt (acl2-sine x) (- m 1)) (acl2-cosine x))))
                            (y (+ (/ (rterm m (acl2-sine (+ x h)) (acl2-sine x)) h)
                                  (* (* m (expt (acl2-sine x) (- m 1)))
                                     (- (/ (- (acl2-sine (+ x h)) (acl2-sine x)) h) (acl2-cosine x)))))))
           :in-theory (union-theories '(sine-limited cosine-limited realp-sine realp-cosine sine-abs-le-1 standardp-times
                                        natp-compound-recognizer realp-rterm realp-expt-tp
                                        (:type-prescription abs) realp-abs standards-are-limited)
                                      (theory 'minimal-theory)))))

;;; ---------------- part p5 ----------------

(defun gfun (m x) (* (expt (acl2-sine x) m) (acl2-cosine x)))
(defun gder (m x) (- (* m (expt (acl2-sine x) (- m 1))) (* (+ m 1) (expt (acl2-sine x) (+ m 1)))))
(defun dterm (m x h) (- (- (gfun m (+ x h)) (gfun m x)) (* h (gder m x))))

(local (defthm alg4
  (implies (and (acl2-numberp p) (acl2-numberp q) (acl2-numberp w) (acl2-numberp z) (acl2-numberp c)
                (acl2-numberp c2) (acl2-numberp v) (acl2-numberp h) (not (equal h 0)) (acl2-numberp m)
                (equal (+ (* v v) (* c c)) 1) (equal z (* q v)) (equal (* m z) (* m (* w (* v v)))))
           (equal (/ (- (- (* p c2) (* q c)) (* h (- (* m w) (* (+ m 1) z)))) h)
                  (+ (* p (+ (/ (- c2 c) h) v)) (* c (- (/ (- p q) h) (* m (* w c)))) (- (* v (- p q))))))
  :rule-classes nil))

(local (defthm limited-prod (implies (and (i-limited a) (i-limited b)) (i-limited (* a b))) :rule-classes nil))

(local (defthm expt-limited-1 (implies (and (realp x) (natp m)) (i-limited (expt (acl2-sine x) m)))
  :hints (("Goal" :use ((:instance abs-expt-le-1 (v (acl2-sine x)) (k m))
                        (:instance limited-squeeze (a -1) (b 1) (x (expt (acl2-sine x) m))))
           :in-theory (union-theories '(abs realp-expt-tp realp-sine sine-abs-le-1 sine-bounds standard-constants-are-limited) (theory 'minimal-theory))))))

(local (defthm limited-from-close
  (implies (and (i-limited c) (i-small (- q c)) (acl2-numberp q)) (i-limited q))
  :hints (("Goal" :use ((:instance i-limited-plus (x c) (y (- q c))) (:instance small-are-limited (x (- q c))))
           :in-theory (disable i-limited-plus small-are-limited)))
  :rule-classes nil))

(local (defthm diff-from-ratio
  (implies (and (acl2-numberp a) (acl2-numberp h) (not (equal h 0))) (equal a (* h (/ a h))))
  :rule-classes nil))

(defthm dterm-small
  (implies (and (natp m) (standardp m) (realp x) (realp h) (i-small h) (not (equal h 0)))
           (i-small (/ (dterm m x h) h)))
  :hints (("Goal"
           :use ((:instance alg4 (p (expt (acl2-sine (+ x h)) m)) (q (expt (acl2-sine x) m))
                            (w (expt (acl2-sine x) (- m 1))) (z (expt (acl2-sine x) (+ m 1)))
                            (c (acl2-cosine x)) (c2 (acl2-cosine (+ x h))) (v (acl2-sine x)))
                 (:instance expt-facts-2 (v (acl2-sine x)))
                 (:instance sin**2+cos**2)
                 cosine-uniform-derivative spow-uniform-derivative
                 (:instance expt-limited-1 (x (+ x h)))
                 (:instance lim-coef (v (acl2-sine x)))
                 (:instance limited-prod (a (* m (expt (acl2-sine x) (- m 1)))) (b (acl2-cosine x)))
                 (:instance limited-from-close (c (* m (* (expt (acl2-sine x) (- m 1)) (acl2-cosine x))))
                            (q (/ (- (expt (acl2-sine (+ x h)) m) (expt (acl2-sine x) m)) h)))
                 (:instance diff-from-ratio (a (- (expt (acl2-sine (+ x h)) m) (expt (acl2-sine x) m))))
                 (:instance small*limited->small (x h) (y (/ (- (expt (acl2-sine (+ x h)) m) (expt (acl2-sine x) m)) h)))
                 (:instance limited*small->small (x (expt (acl2-sine (+ x h)) m))
                            (y (+ (/ (- (acl2-cosine (+ x h)) (acl2-cosine x)) h) (acl2-sine x))))
                 (:instance limited*small->small (x (acl2-cosine x))
                            (y (- (/ (- (expt (acl2-sine (+ x h)) m) (expt (acl2-sine x) m)) h)
                                  (* m (* (expt (acl2-sine x) (- m 1)) (acl2-cosine x))))))
                 (:instance limited*small->small (x (acl2-sine x))
                            (y (- (expt (acl2-sine (+ x h)) m) (expt (acl2-sine x) m))))
                 (:instance i-small-uminus (x (* (acl2-sine x) (- (expt (acl2-sine (+ x h)) m) (expt (acl2-sine x) m)))))
                 (:instance i-small-plus (x (* (acl2-cosine x) (- (/ (- (expt (acl2-sine (+ x h)) m) (expt (acl2-sine x) m)) h) (* m (* (expt (acl2-sine x) (- m 1)) (acl2-cosine x)))))) (y (- (* (acl2-sine x) (- (expt (acl2-sine (+ x h)) m) (expt (acl2-sine x) m))))))
                 (:instance i-small-plus (x (* (expt (acl2-sine (+ x h)) m) (+ (/ (- (acl2-cosine (+ x h)) (acl2-cosine x)) h) (acl2-sine x)))) (y (+ (* (acl2-cosine x) (- (/ (- (expt (acl2-sine (+ x h)) m) (expt (acl2-sine x) m)) h) (* m (* (expt (acl2-sine x) (- m 1)) (acl2-cosine x))))) (- (* (acl2-sine x) (- (expt (acl2-sine (+ x h)) m) (expt (acl2-sine x) m)))))))
                 (:instance small-by-equal (x (/ (dterm m x h) h)) (y (+ (* (expt (acl2-sine (+ x h)) m) (+ (/ (- (acl2-cosine (+ x h)) (acl2-cosine x)) h) (acl2-sine x))) (+ (* (acl2-cosine x) (- (/ (- (expt (acl2-sine (+ x h)) m) (expt (acl2-sine x) m)) h) (* m (* (expt (acl2-sine x) (- m 1)) (acl2-cosine x))))) (- (* (acl2-sine x) (- (expt (acl2-sine (+ x h)) m) (expt (acl2-sine x) m)))))))))
           :in-theory (union-theories '(dterm gfun gder sine-limited cosine-limited realp-sine realp-cosine sine-abs-le-1 sine-bounds
                                        natp-compound-recognizer realp-expt-tp associativity-of-+ associativity-of-* fix
                                        (:type-prescription abs) realp-abs standards-are-limited)
                                      (theory 'minimal-theory)))))

;;; ---------------- part p6 ----------------

(defun spsum (n k h) (if (zp k) 0 (+ (spsum n (1- k) h) (expt (acl2-sine (* (1- k) h)) n))))
(defun gsum (m k h) (if (zp k) 0 (+ (gsum m (1- k) h) (gder m (* (1- k) h)))))
(defun dsum (m k h) (if (zp k) 0 (+ (dsum m (1- k) h) (dterm m (* (1- k) h) h))))
(defun maxd (m k h) (if (zp k) 0 (max (maxd m (1- k) h) (abs (dterm m (* (1- k) h) h)))))
(defun argx (m k h) (if (zp k) 0
                      (if (<= (abs (dterm m (* (1- k) h) h)) (maxd m (1- k) h))
                          (argx m (1- k) h)
                        (* (1- k) h))))

(in-theory (disable gfun gder dterm))

(defthm dsum-telescope
  (implies (and (natp k) (realp h))
           (equal (dsum m k h) (- (- (gfun m (* k h)) (gfun m 0)) (* h (gsum m k h)))))
  :hints (("Goal" :induct (dsum m k h) :in-theory (enable dterm))))

(defthm gsum-spsum
  (implies (and (natp k) (natp m))
           (equal (gsum m k h) (- (* m (spsum (- m 1) k h)) (* (+ m 1) (spsum (+ m 1) k h)))))
  :hints (("Goal" :induct (gsum m k h) :in-theory (enable gder))))

(in-theory (disable dsum-telescope gsum-spsum))

(defthm realp-dterm (implies (and (realp x) (realp h) (integerp m)) (realp (dterm m x h)))
  :hints (("Goal" :in-theory (enable dterm gfun gder)))
  :rule-classes :type-prescription)

(defthm realp-dsum (implies (and (realp h) (integerp m)) (realp (dsum m k h))) :rule-classes :type-prescription)
(defthm maxd-real (implies (and (realp h) (integerp m)) (realp (maxd m k h))) :rule-classes :type-prescription)
(defthm maxd-nonneg (implies (and (realp h) (integerp m)) (<= 0 (maxd m k h))) :rule-classes :linear)

(defthm dsum-bound
  (implies (and (natp k) (realp h) (integerp m))
           (<= (abs (dsum m k h)) (* k (maxd m k h))))
  :hints (("Goal" :induct (dsum m k h) :in-theory (disable abs))
          ("Subgoal *1/2" :use ((:instance abs-tri (a (dsum m (1- k) h)) (b (dterm m (* (1- k) h) h)))
                                (:instance mult-le-mono (a (maxd m (1- k) h)) (b (maxd m k h)) (c (1- k)))))))

(defthm maxd-argx
  (implies (and (natp k) (realp h) (integerp m))
           (<= (maxd m k h) (abs (dterm m (argx m k h) h))))
  :hints (("Goal" :induct (argx m k h) :in-theory (disable abs))))

(defthm realp-argx (implies (realp h) (realp (argx m k h))) :rule-classes :type-prescription)

(defun hs (bign) (/ (acl2-pi) (* 2 bign)))
(defun ssum (n bign) (* (hs bign) (spsum n bign (hs bign))))

(defthm-std standardp-pi (standardp (acl2-pi)))

(defthm n-hs (implies (and (natp bign) (< 0 bign)) (equal (* bign (hs bign)) (* 1/2 (acl2-pi)))))

(defthm hs-props
  (implies (and (natp bign) (< 0 bign)) (and (realp (hs bign)) (< 0 (hs bign))))
  :rule-classes nil)

(defthm pi-half-standard (standardp (* 1/2 (acl2-pi))))
(defthm pi-half-limited (i-limited (* 1/2 (acl2-pi)))
  :hints (("Goal" :use ((:instance standards-are-limited (x (* 1/2 (acl2-pi))))))))

(defthm hs-small
  (implies (and (natp bign) (i-large bign)) (i-small (hs bign)))
  :hints (("Goal" :use ((:instance limited*small->small (x (* 1/2 (acl2-pi))) (y (/ bign)))
                        (:instance i-large-udivide (x bign)) pi-half-limited)
           :in-theory (disable limited*small->small i-large-udivide pi-half-limited))))

(local (defthm ns-alg
  (implies (and (realp d) (realp h) (< 0 h) (natp bign) (equal (* bign h) p))
           (equal (* bign (abs d)) (abs (* p (/ d h)))))
  :hints (("Goal" :cases ((<= 0 d))))
  :rule-classes nil))

(local (defthm large-pos-nat (implies (and (natp n) (i-large n)) (< 0 n)) :rule-classes nil))

(defthm dsum-small
  (implies (and (natp m) (standardp m) (natp bign) (i-large bign))
           (i-small (dsum m bign (hs bign))))
  :hints (("Goal" :use ((:instance large-pos-nat (n bign)) hs-small (:instance hs-props)
                        (:instance dsum-bound (k bign) (h (hs bign)))
                        (:instance maxd-argx (k bign) (h (hs bign)))
                        (:instance mult-le-mono (a (maxd m bign (hs bign))) (b (abs (dterm m (argx m bign (hs bign)) (hs bign))))
                                   (c bign))
                        (:instance dterm-small (x (argx m bign (hs bign))) (h (hs bign)))
                        (:instance ns-alg (d (dterm m (argx m bign (hs bign)) (hs bign))) (h (hs bign)) (p (* 1/2 (acl2-pi))))
                        (:instance limited*small->small (x (* 1/2 (acl2-pi)))
                                   (y (/ (dterm m (argx m bign (hs bign)) (hs bign)) (hs bign))))
                        (:instance small-if-<-small (x (* (* 1/2 (acl2-pi)) (/ (dterm m (argx m bign (hs bign)) (hs bign)) (hs bign))))
                                   (y (dsum m bign (hs bign)))))
           :in-theory (union-theories '(n-hs realp-dsum realp-dterm realp-argx maxd-real natp-compound-recognizer commutativity-of-*
                                        standardp-pi pi-half-limited standards-are-limited standardp-times realp-abs (:type-prescription abs)
                                        (:type-prescription acl2-pi) acl2-pi-type-prescription)
                                      (theory 'minimal-theory)))))

;;; ---------------- part p6b ----------------
(local (in-theory (disable sine-of-sums cosine-of-sums)))

(defthm realp-hs (implies (realp bign) (realp (hs bign))) :rule-classes :type-prescription)

(local (defthm grid-lt
  (implies (and (natp j) (natp bign) (< j bign))
           (and (<= 0 (* j (hs bign))) (< (* j (hs bign)) (* 1/2 (acl2-pi)))))
  :hints (("Goal" :use ((:instance mult-le-mono (a j) (b (- bign 1)) (c (hs bign))) hs-props)))))

(defthm sine-grid
  (implies (and (natp j) (natp bign) (< j bign))
           (and (<= 0 (acl2-sine (* j (hs bign)))) (<= (acl2-sine (* j (hs bign))) 1)))
  :hints (("Goal" :cases ((= j 0)))
          ("Subgoal 2" :use (grid-lt (:instance sine-positive-in-0-pi/2 (x (* j (hs bign)))))
           :in-theory (disable grid-lt sine-positive-in-0-pi/2 hs))))

(defthm pow-01
  (implies (and (realp s) (<= 0 s) (<= s 1) (natp n))
           (and (<= 0 (expt s n)) (<= (expt s n) 1) (<= (expt s (+ 1 n)) (expt s n))))
  :hints (("Goal" :use ((:instance expt-is-non-decreasing-for-non-negatives (x s) (y 1))
                        (:instance mult-le-mono (a s) (b 1) (c (expt s n)))))))


(defthm pow-mono-sin
  (implies (and (realp x) (<= 0 (acl2-sine x)) (natp n))
           (<= (expt (acl2-sine x) (+ 1 n)) (expt (acl2-sine x) n)))
  :hints (("Goal" :use ((:instance pow-01 (s (acl2-sine x))))
           :in-theory (disable pow-01)))
  :rule-classes nil)

(defthm spsum-mono
  (implies (and (natp n) (natp k) (natp bign) (<= k bign))
           (<= (spsum (+ 1 n) k (hs bign)) (spsum n k (hs bign))))
  :hints (("Goal" :induct (spsum n k (hs bign)) :in-theory (disable hs))
          ("Subgoal *1/2" :use ((:instance sine-grid (j (1- k)))
                                (:instance pow-mono-sin (x (* (1- k) (hs bign)))))
           :in-theory (union-theories '(spsum zp natp realp-hs (:type-prescription acl2-sine) realp-sine) (theory 'minimal-theory)))))

(defthm spsum-nonneg
  (implies (and (natp n) (natp k) (natp bign) (<= k bign))
           (<= 0 (spsum n k (hs bign))))
  :hints (("Goal" :induct (spsum n k (hs bign)) :in-theory (disable hs))
          ("Subgoal *1/2" :use ((:instance sine-grid (j (1- k)))
                                (:instance pow-01 (s (acl2-sine (* (1- k) (hs bign)))))))))

(defthm spsum-le-k
  (implies (and (natp n) (natp k) (natp bign) (<= k bign))
           (<= (spsum n k (hs bign)) k))
  :hints (("Goal" :induct (spsum n k (hs bign)) :in-theory (disable hs))
          ("Subgoal *1/2" :use ((:instance sine-grid (j (1- k)))
                                (:instance pow-01 (s (acl2-sine (* (1- k) (hs bign)))))))))

(defthm spsum-0 (implies (natp k) (equal (spsum 0 k h) k)))

;;; ---------------- part p6c ----------------
(local (in-theory (disable sine-of-sums cosine-of-sums)))

(defthm realp-spsum (implies (realp h) (realp (spsum n k h))) :rule-classes :type-prescription)
(defthm realp-ssum (implies (realp bign) (realp (ssum n bign))) :rule-classes :type-prescription)

(defthm dsum-0-identity
  (implies (and (natp bign) (< 0 bign))
           (equal (dsum 0 bign (hs bign)) (- (ssum 1 bign) 1)))
  :hints (("Goal" :use ((:instance dsum-telescope (m 0) (k bign) (h (hs bign)))
                        (:instance gsum-spsum (m 0) (k bign) (h (hs bign))))
           :in-theory (e/d (gfun) (hs)))))

(defthm dsum-m-identity
  (implies (and (natp bign) (< 0 bign) (natp m) (< 0 m))
           (equal (dsum m bign (hs bign))
                  (- (* (+ m 1) (ssum (+ m 1) bign)) (* m (ssum (- m 1) bign)))))
  :hints (("Goal" :use ((:instance dsum-telescope (k bign) (h (hs bign)))
                        (:instance gsum-spsum (k bign) (h (hs bign))))
           :in-theory (e/d (gfun) (hs)))))

(defthm ssum-bounds
  (implies (and (natp n) (natp bign) (< 0 bign))
           (and (<= 0 (ssum n bign)) (<= (ssum n bign) (* 1/2 (acl2-pi)))
                (<= (ssum (+ 1 n) bign) (ssum n bign))))
  :hints (("Goal" :use ((:instance spsum-nonneg (k bign)) (:instance spsum-le-k (k bign)) (:instance spsum-mono (k bign))
                        hs-props
                        (:instance mult-le-mono (a (spsum n bign (hs bign))) (b bign) (c (hs bign)))
                        (:instance mult-le-mono (a 0) (b (spsum n bign (hs bign))) (c (hs bign)))
                        (:instance mult-le-mono (a (spsum (+ 1 n) bign (hs bign))) (b (spsum n bign (hs bign))) (c (hs bign))))
           :in-theory (disable spsum-nonneg spsum-le-k spsum-mono hs))))

;;; ---------------- part p6d ----------------
(local (in-theory (disable sine-of-sums cosine-of-sums)))

(local (defthm lg-facts
  (and (natp (i-large-integer)) (< 0 (i-large-integer)) (i-large (i-large-integer)))
  :hints (("Goal" :use (i-large-integer-is-large
                        (:instance large->-non-large (x (i-large-integer)) (y 1)))
           :in-theory (disable large->-non-large)))))

(defthm ssum-limited
  (implies (and (natp n) (natp bign) (< 0 bign))
           (i-limited (ssum n bign)))
  :hints (("Goal" :use ((:instance limited-squeeze (a 0) (b (* 1/2 (acl2-pi))) (x (ssum n bign)))
                        ssum-bounds pi-half-limited)
           :in-theory (disable limited-squeeze ssum-bounds ssum pi-half-limited))))

(in-theory (disable ssum hs))
(defun-std wint (n)
  (standard-part (ssum (nfix n) (i-large-integer))))

(defthm-std wint-0 (equal (wint 0) (* 1/2 (acl2-pi)))
  :hints (("Goal" :in-theory (enable ssum)
           :use ((:instance n-hs (bign (i-large-integer)))))))

(local (defthm st-1-plus-small
  (implies (and (acl2-numberp a) (i-small (- a 1))) (equal (standard-part a) 1))
  :hints (("Goal" :in-theory (enable i-small)
           :use ((:instance standard-part-of-plus (x (- a 1)) (y 1)))))))

(defthm-std wint-1 (equal (wint 1) 1)
  :hints (("Goal" :use ((:instance dsum-small (m 0) (bign (i-large-integer)))
                        (:instance dsum-0-identity (bign (i-large-integer)))
                        (:instance st-1-plus-small (a (ssum 1 (i-large-integer)))))
           :in-theory (disable dsum-small dsum-0-identity st-1-plus-small))))

(local (defthm st-lin
  (implies (and (i-limited a) (i-limited b) (standardp p) (standardp q) (acl2-numberp p) (acl2-numberp q)
                (i-small (- (* p a) (* q b))))
           (equal (* p (standard-part a)) (* q (standard-part b))))
  :hints (("Goal" :in-theory (enable i-small)
           :use ((:instance standard-part-of-plus (x (* p a)) (y (- (* q b))))
                 (:instance standard-part-of-times (x p) (y a))
                 (:instance standard-part-of-times (x q) (y b)))))
  :rule-classes nil))

(defthm-std wint-rec
  (implies (and (natp m) (< 0 m))
           (equal (* (+ m 1) (wint (+ m 1))) (* m (wint (- m 1)))))
  :hints (("Goal" :use ((:instance dsum-small (bign (i-large-integer)))
                        (:instance dsum-m-identity (bign (i-large-integer)))
                        (:instance st-lin (p (+ m 1)) (q m) (a (ssum (+ m 1) (i-large-integer)))
                                   (b (ssum (- m 1) (i-large-integer)))))
           :in-theory (disable dsum-small dsum-m-identity))))

(defthm-std wint-mono
  (implies (natp n) (<= (wint (+ 1 n)) (wint n)))
  :hints (("Goal" :use ((:instance ssum-bounds (bign (i-large-integer)))
                        (:instance standard-part-<= (x (ssum (+ 1 n) (i-large-integer))) (y (ssum n (i-large-integer)))))
           :in-theory (disable ssum-bounds standard-part-<=))))

;;; ---------------- part p11 ----------------
(in-theory (disable wint-rec))

(defthm realp-wint (realp (wint n))
  :hints (("Goal" :use ((:instance wint-mono (n (nfix n)))) :in-theory (disable wint-mono)))
  :rule-classes :type-prescription)

(defthm solve-lin (implies (and (acl2-numberp a) (acl2-numberp w) (not (equal a 0)) (equal (* a w) x)) (equal w (/ x a)))
  :rule-classes nil)

(local (defthm we-step
  (implies (and (acl2-numberp w2) (acl2-numberp w0) (acl2-numberp p) (natp k) (< 0 k)
                (equal (* (+ (+ -1 (* 2 k)) 1) w2) (* (+ -1 (* 2 k)) w0))
                (equal w0 (* (* 1/2 pp) p)))
           (equal w2 (* (* 1/2 pp) (* p (/ (- (* 2 k) 1) (* 2 k))))))
  :hints (("Goal" :use ((:instance solve-lin (a (* 2 k)) (w w2) (x (* (+ -1 (* 2 k)) w0))))))
  :rule-classes nil))

(defthm wint-even
  (implies (natp k) (equal (wint (* 2 k)) (* (* 1/2 (acl2-pi)) (wp k))))
  :hints (("Goal" :induct (wp k))
          ("Subgoal *1/2" :use ((:instance wint-rec (m (- (* 2 k) 1)))
                                (:instance we-step (w2 (wint (* 2 k))) (w0 (wint (* 2 (1- k)))) (p (wp (1- k)))
                                           (pp (acl2-pi))))
           :in-theory (disable wint-rec))))

(defthm comm-3a (equal (* x (* a q)) (* q (* a x))) :rule-classes nil)
(defthm comm-3b (equal (* q (* b w)) (* w (* b q))) :rule-classes nil)
(defthm cong-* (implies (equal u v) (equal (* q u) (* q v))) :rule-classes nil)

(local (defthm wo-abs
  (implies (and (acl2-numberp x) (acl2-numberp w) (acl2-numberp p) (acl2-numberp q) (acl2-numberp a)
                (acl2-numberp b) (acl2-numberp c) (not (equal a 0)) (not (equal b 0))
                (equal (* a x) (* b w)) (equal (* b q) (* c p)) (equal (* w (* c p)) 1))
           (equal (* x (* a q)) 1))
  :hints (("Goal" :use ((:instance cong-* (q q) (u (* a x)) (v (* b w)))
                        (:instance cong-* (q w) (u (* b q)) (v (* c p)))
                        (:instance comm-3a) (:instance comm-3b))
           :in-theory (theory 'minimal-theory)))
  :rule-classes nil))

(defthm wp-rec-mult (implies (and (natp k) (< 0 k)) (equal (* (* 2 k) (wp k)) (* (+ -1 (* 2 k)) (wp (1- k))))))

(defthm wint-odd
  (implies (natp k) (equal (* (wint (+ 1 (* 2 k))) (* (+ 1 (* 2 k)) (wp k))) 1))
  :hints (("Goal" :induct (wp k))
          ("Subgoal *1/2" :use ((:instance wint-rec (m (* 2 k))) wp-rec-mult
                                (:instance wo-abs (x (wint (+ 1 (* 2 k)))) (a (+ 1 (* 2 k))) (b (* 2 k))
                                           (w (wint (+ -1 (* 2 k)))) (c (+ -1 (* 2 k))) (p (wp (1- k))) (q (wp k))))
           :in-theory (disable wint-rec wp wp-rec-mult))))

(local (defthm wl-abs
  (implies (and (realp x) (realp y) (realp a) (realp p) (realp pp) (< 0 a) (< 0 p)
                (equal (* x (* a p)) 1) (<= x y) (equal y (* (* 1/2 pp) p)))
           (<= 2 (* a (* pp (* p p)))))
  :hints (("Goal" :use ((:instance mult-le-mono (a x) (b y) (c (* a p))))))
  :rule-classes nil))

(defthm wallis-lower
  (implies (natp k)
           (<= 2 (* (+ 1 (* 2 k)) (* (acl2-pi) (* (wp k) (wp k))))))
  :hints (("Goal" :use (wint-odd wint-even (:instance wint-mono (n (* 2 k)))
                        (:instance wl-abs (x (wint (+ 1 (* 2 k)))) (y (wint (* 2 k))) (a (+ 1 (* 2 k)))
                                   (p (wp k)) (pp (acl2-pi))))
           :in-theory (disable wint-odd wint-even wint-mono wp))))

(local (defthm wu-abs
  (implies (and (realp x) (realp y) (realp k) (realp p) (realp pp) (< 0 k) (< 0 p)
                (equal (* x (* (* 2 k) p)) 1) (<= y x) (equal y (* (* 1/2 pp) p)))
           (<= (* k (* pp (* p p))) 1))
  :hints (("Goal" :use ((:instance mult-le-mono (a y) (b x) (c (* (* 2 k) p))))))
  :rule-classes nil))

(local (defthm wo2
  (implies (and (equal (* x (* c p)) 1) (equal (* b q) (* c p)))
           (equal (* x (* b q)) 1))
  :hints (("Goal" :use ((:instance cong-* (q x) (u (* b q)) (v (* c p))))
           :in-theory (theory 'minimal-theory)))
  :rule-classes nil))

(local (defthm wodd-shift
  (implies (and (natp k) (< 0 k))
           (equal (* (wint (+ -1 (* 2 k))) (* (* 2 k) (wp k))) 1))
  :hints (("Goal" :use ((:instance wint-odd (k (1- k))) wp-rec-mult
                        (:instance wo2 (x (wint (+ -1 (* 2 k)))) (c (+ -1 (* 2 k))) (p (wp (1- k))) (b (* 2 k)) (q (wp k))))
           :in-theory (disable wint-odd wp-rec-mult wp)))))

(defthm wallis-upper
  (implies (and (natp k) (< 0 k))
           (<= (* k (* (acl2-pi) (* (wp k) (wp k)))) 1))
  :hints (("Goal" :use (wodd-shift wint-even (:instance wint-mono (n (+ -1 (* 2 k))))
                        (:instance wu-abs (x (wint (+ -1 (* 2 k)))) (y (wint (* 2 k)))
                                   (p (wp k)) (pp (acl2-pi))))
           :in-theory (disable wodd-shift wint-even wint-mono wp))))

;;; ---------------- part p12 ----------------

(local (defthm f1-abs
  (implies (and (realp y) (natp m) (< 0 m) (<= 2 (* (+ 1 (* 2 m)) y)) (<= (* m y) 1))
           (and (<= 0 (- 1 (* m y))) (<= (- 1 (* m y)) (/ (+ 1 (* 2 m))))))
  :hints (("Goal" :use ((:instance le-div-intro (a (- 1 (* m y))) (b 1) (c (+ 1 (* 2 m)))))))
  :rule-classes nil))

(local (defthm large-nat-facts (implies (and (natp m) (i-large m)) (< 0 m)) :rule-classes :forward-chaining))

(defthm wallis-close
  (implies (and (natp m) (i-large m))
           (i-small (- 1 (* m (* (acl2-pi) (* (wp m) (wp m)))))))
  :hints (("Goal" :use ((:instance wallis-lower (k m)) (:instance wallis-upper (k m))
                        (:instance f1-abs (y (* (acl2-pi) (* (wp m) (wp m)))))
                        (:instance i-large-udivide (x (+ 1 (* 2 m))))
                        (:instance large-if->-large (x m) (y (+ 1 (* 2 m))))
                        (:instance small-if-<-small (x (/ (+ 1 (* 2 m)))) (y (- 1 (* m (* (acl2-pi) (* (wp m) (wp m))))))))
           :in-theory (disable wallis-lower wallis-upper i-large-udivide large-if->-large small-if-<-small wp))))

(local (defthm f2-alg
  (implies (and (acl2-numberp a) (not (equal a 0)) (acl2-numberp x) (acl2-numberp b) (acl2-numberp pp)
                (equal (* (* a a) x) (* (* 2 pp) b)))
           (equal (- a (* 2 pp)) (* (/ a) (+ (* (* a a) (- 1 x)) (* (* 2 pp) (- b a))))))
  :rule-classes nil))

(local (defthm f2-rel
  (implies (and (natp m) (< 0 m))
           (equal (* (* (sa m) (sa m)) (* m (* (acl2-pi) (* (wp m) (wp m)))))
                  (* (* 2 (acl2-pi)) (sa (* 2 m)))))
  :hints (("Goal" :use (sa-wallis-relation
                        (:instance cong-* (q (acl2-pi)) (u (* (* (sa m) (sa m)) (* m (* (wp m) (wp m)))))
                                   (v (* 2 (sa (* 2 m))))))
           :in-theory (disable sa-wallis-relation sa wp)))))

(local (defthm inv-limited
  (implies (and (realp a) (<= 1 a)) (i-limited (/ a)))
  :hints (("Goal" :use ((:instance limited-squeeze (a 0) (b 1) (x (/ a))))
           :in-theory (disable limited-squeeze)))))

(defthm two-pi-limited (i-limited (* 2 (acl2-pi)))
  :hints (("Goal" :use ((:instance standards-are-limited (x (* 2 (acl2-pi))))))))

(defthm sa-limit
  (implies (and (natp m) (i-large m))
           (i-close (sa m) (* 2 (acl2-pi))))
  :hints (("Goal"
           :use ((:instance f2-alg (a (sa m)) (x (* m (* (acl2-pi) (* (wp m) (wp m))))) (b (sa (* 2 m))) (pp (acl2-pi)))
                 f2-rel wallis-close
                 (:instance sa-close (n m) (m (* 2 m)))
                 (:instance large-if->-large (x m) (y (* 2 m)))
                 (:instance sa-lower (n m)) (:instance sa-limited (n m))
                 (:instance sa-limited (n (* 2 m)))
                 (:instance inv-limited (a (sa m)))
                 (:instance i-limited-times (x (sa m)) (y (sa m)))
                 (:instance limited*small->small (x (* (sa m) (sa m))) (y (- 1 (* m (* (acl2-pi) (* (wp m) (wp m)))))))
                 (:instance i-close-symmetric (x (sa m)) (y (sa (* 2 m))))
                 (:instance limited*small->small (x (* 2 (acl2-pi))) (y (- (sa (* 2 m)) (sa m))))
                 two-pi-limited
                 (:instance i-small-plus (x (* (* (sa m) (sa m)) (- 1 (* m (* (acl2-pi) (* (wp m) (wp m)))))))
                            (y (* (* 2 (acl2-pi)) (- (sa (* 2 m)) (sa m)))))
                 (:instance limited*small->small (x (/ (sa m)))
                            (y (+ (* (* (sa m) (sa m)) (- 1 (* m (* (acl2-pi) (* (wp m) (wp m))))))
                                  (* (* 2 (acl2-pi)) (- (sa (* 2 m)) (sa m))))))
                 (:instance small-by-equal (x (- (sa m) (* 2 (acl2-pi))))
                            (y (* (/ (sa m)) (+ (* (* (sa m) (sa m)) (- 1 (* m (* (acl2-pi) (* (wp m) (wp m))))))
                                                (* (* 2 (acl2-pi)) (- (sa (* 2 m)) (sa m))))))))
           :in-theory (union-theories '(i-close realp-sa natp-compound-recognizer natp large-nat-facts abs
                                        realp-wp (:type-prescription acl2-pi) acl2-pi-type-prescription)
                                      (theory 'minimal-theory)))))

;;; ---------------- part p13 ----------------

;; Stirling's approximation sqrt(2 pi n) (n/e)^n and the ratio n!/approximation
(defun stirling-approx (n)
  (* (acl2-sqrt (* 2 (acl2-pi) n)) (expt (/ n (acl2-exp 1)) n)))

(defun stirling-ratio (n)
  (/ (factorial n) (stirling-approx n)))

(local (defthm r-alg
  (implies (and (acl2-numberp f) (acl2-numberp s) (acl2-numberp e) (acl2-numberp p) (acl2-numberp n)
                (acl2-numberp pp) (not (equal s 0)) (not (equal e 0)) (not (equal p 0)) (not (equal n 0))
                (not (equal pp 0))
                (equal (* s s) (* 2 (* pp n))) (equal q (/ p e)) (equal e2 (* e e)) (equal p2 (* p (* p n))))
           (equal (* (/ f (* s q)) (/ f (* s q))) (/ (/ (* f (* f e2)) p2) (* 2 pp))))
  :rule-classes nil))

(local (defthm r-facts
  (implies (and (natp n) (< 0 n))
           (and (equal (expt (/ n (acl2-exp 1)) n) (/ (expt n n) (expt (acl2-exp 1) n)))
                (equal (expt (acl2-exp 1) (* 2 n)) (* (expt (acl2-exp 1) n) (expt (acl2-exp 1) n)))
                (equal (expt n (+ (* 2 n) 1)) (* (expt n n) (* (expt n n) n)))))
  :hints (("Goal" :in-theory (disable exp-expt)))))

(local (defthm pos-facts
  (implies (and (natp n) (< 0 n))
           (and (< 0 (acl2-sqrt (* 2 (acl2-pi) n))) (realp (acl2-sqrt (* 2 (acl2-pi) n)))
                (equal (* (acl2-sqrt (* 2 (acl2-pi) n)) (acl2-sqrt (* 2 (acl2-pi) n))) (* 2 (* (acl2-pi) n)))))
  :hints (("Goal" :use ((:instance sqrt->-0 (x (* 2 (acl2-pi) n))) (:instance sqrt-sqrt (x (* 2 (acl2-pi) n))))
           :in-theory (disable sqrt->-0 sqrt-sqrt)))))

(local (defthm e-facts (and (realp (acl2-exp 1)) (< 0 (acl2-exp 1)))))

(defthm ratio-sq
  (implies (and (natp n) (< 0 n))
           (equal (* (stirling-ratio n) (stirling-ratio n)) (/ (sa n) (* 2 (acl2-pi)))))
  :hints (("Goal" :use (r-facts pos-facts e-facts
                        (:instance r-alg (f (factorial n)) (s (acl2-sqrt (* 2 (acl2-pi) n)))
                                   (e (expt (acl2-exp 1) n)) (p (expt n n)) (pp (acl2-pi))
                                   (q (expt (/ n (acl2-exp 1)) n))
                                   (e2 (expt (acl2-exp 1) (* 2 n)))
                                   (p2 (expt n (+ (* 2 n) 1)))))
           :in-theory (union-theories '(stirling-ratio stirling-approx sa natp-compound-recognizer
                                        (:type-prescription expt) realp-expt-tp acl2-pi-type-prescription
                                        (:type-prescription factorial) factorial-pos)
                                      (theory 'minimal-theory)))))

(defthm ratio-pos
  (implies (and (natp n) (< 0 n)) (and (realp (stirling-ratio n)) (< 0 (stirling-ratio n))))
  :hints (("Goal" :use (pos-facts e-facts (:instance factorial-pos))
           :in-theory (disable pos-facts e-facts factorial-pos))))

(local (defthm root-close-abs
  (implies (and (realp r) (< 0 r))
           (<= (abs (- r 1)) (abs (- (* r r) 1))))
  :hints (("Goal" :use ((:instance mult-le-mono (a 1) (b (+ r 1)) (c (abs (- r 1)))))
           :cases ((<= 1 r))))
  :rule-classes nil))

(local (defthm large-pos-n (implies (and (natp m) (i-large m)) (< 0 m)) :rule-classes nil))

(defthm ratio-close
  (implies (and (natp n) (i-large n))
           (i-small (- (stirling-ratio n) 1)))
  :hints (("Goal" :use ((:instance root-close-abs (r (stirling-ratio n)))
                        (:instance ratio-pos) ratio-sq (:instance sa-limit (m n)) (:instance large-pos-n (m n))
                        (:instance limited*small->small (x (/ (* 2 (acl2-pi)))) (y (- (sa n) (* 2 (acl2-pi)))))
                        (:instance standards-are-limited (x (/ (* 2 (acl2-pi)))))
                        (:instance small-by-equal (x (- (/ (sa n) (* 2 (acl2-pi))) 1))
                                   (y (* (/ (* 2 (acl2-pi))) (- (sa n) (* 2 (acl2-pi))))))
                        (:instance small-if-<-small (x (- (* (stirling-ratio n) (stirling-ratio n)) 1))
                                   (y (- (stirling-ratio n) 1))))
           :in-theory (e/d (i-close) (ratio-pos ratio-sq sa-limit limited*small->small standards-are-limited
                                      small-if-<-small stirling-ratio sa abs)))))

;;; ---------------- part p14 ----------------

;; f(n) ~ g(n) means lim_{n->oo} f(n)/g(n) = 1, i.e. for every eps > 0 there is
;; an N such that |f(n)/g(n) - 1| < eps for all n >= N.

(defun-sk stirling-tail-within (eps bign)
  (forall n (implies (and (natp n) (<= bign n))
                     (< (abs (- (/ (factorial n) (stirling-approx n)) 1)) eps))))

(defun-sk stirling-ratio-limit-is-1 (eps)
  (exists bign (and (natp bign) (stirling-tail-within eps bign))))

(local (defthm lg-facts2
  (and (natp (i-large-integer)) (i-large (i-large-integer)))
  :hints (("Goal" :use (i-large-integer-is-large)))))

(local (defthm tail-body
  (implies (and (realp eps) (< 0 eps) (standardp eps) (natp n) (<= (i-large-integer) n))
           (< (abs (- (/ (factorial n) (stirling-approx n)) 1)) eps))
  :hints (("Goal" :use ((:instance large-if->-large (x (i-large-integer)) (y n))
                        (:instance ratio-close)
                        (:instance small-<-non-small (x (- (/ (factorial n) (stirling-approx n)) 1)) (y eps))
                        (:instance standard-small-is-zero (x eps))
                        (:instance ratio-pos))
           :in-theory (disable large-if->-large ratio-close small-<-non-small ratio-pos stirling-approx)))))

(local (defthm tail-std
  (implies (and (realp eps) (< 0 eps) (standardp eps))
           (stirling-tail-within eps (i-large-integer)))
  :hints (("Goal" :use ((:instance tail-body (n (stirling-tail-within-witness eps (i-large-integer)))))
           :in-theory (disable tail-body stirling-approx)))))

(defthm-std main
  (implies (and (realp eps) (< 0 eps))
           (stirling-ratio-limit-is-1 eps))
  :hints (("Goal" :use (tail-std (:instance stirling-ratio-limit-is-1-suff (bign (i-large-integer))))
           :in-theory (disable tail-std stirling-ratio-limit-is-1-suff stirling-tail-within))))
