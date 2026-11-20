(in-package "ACL2")

; Stirling ratio bounds.  stirling-ratio(n) = n! / (sqrt(n) n^n e^-n).
; r(n)/r(n+1) = sqrt(q) q^n / e with q = (n+1)/n.  With a = 1/(2n+1), q = (1+a)/(1-a), and
; both theorems reduce to  exp(2a) < (1+a)/(1-a) < exp(2a + 2a^3/(3(1-a^2))),
; which follow from Taylor bounds on acl2-exp proved below, raised to the power 2n+1.

(include-book "defs")

;; Part 1: Taylor lower/upper bounds for acl2-exp
(encapsulate ()
(local (encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
(defthm taylor-term-next
  (implies (natp c)
           (equal (taylor-exp-term x (+ 1 c))
                  (* (taylor-exp-term x c) x (/ (+ 1 c)))))
  :hints (("Goal" :in-theory (enable taylor-exp-term)
           :expand ((factorial (+ 1 c))))))
  (defthm frac-le
    (implies (and (realp p) (realp q) (realp r) (realp s) (< 0 q) (< 0 s)
                  (<= (* p s) (* r q)))
             (<= (* p (/ q)) (* r (/ s))))
    :hints (("Goal" :use ((:instance (:theorem (implies (and (realp a) (realp b) (realp c) (< 0 c) (<= a b))
                                                         (<= (* a c) (* b c))))
                                     (a (* p s)) (b (* r q)) (c (/ (* q s)))))))
    :rule-classes nil)
  (defthm alg1
    (implies (and (realp x) (realp a) (<= 0 x) (< x a))
             (<= (* (* x (+ a 1)) (/ (* a (+ a 1 (- x)))))
                 (* x (/ (- a x)))))
    :hints (("Goal" :use ((:instance frac-le (p (* x (+ a 1))) (q (* a (+ a 1 (- x))))
                                     (r x) (s (- a x))))
             ))
    :rule-classes nil)
  (defthm alg2
    (implies (and (realp x) (realp a) (< x a))
             (equal (+ 1 (* x (/ (- a x)))) (* a (/ (- a x)))))
    :hints (("Goal" :use ((:instance (:theorem (implies (and (realp d) (realp x) (not (equal d 0)))
                                                        (equal (+ 1 (* x (/ d))) (* (+ d x) (/ d)))))
                                     (d (- a x)))))))
  (defthm tail-step-alg
    (implies (and (realp x) (<= 0 x) (natp c) (< x (+ c 1))
                  (realp tt) (<= 0 tt) (realp s)
                  (<= s (* (* tt x (/ (+ 1 c))) (/ (+ c 2) (- (+ c 2) x)))))
             (<= (+ tt s) (* tt (/ (+ c 1) (- (+ c 1) x)))))
    :hints (("Goal" :use ((:instance alg1 (a (+ c 1)))
                          (:instance alg2 (a (+ c 1)))
                          (:instance (:theorem (implies (and (realp tt) (<= 0 tt) (realp u) (realp v) (<= u v))
                                                        (<= (* tt u) (* tt v))))
                                     (u (* (* x (+ c 2)) (/ (* (+ c 1) (+ c 2 (- x))))))
                                     (v (* x (/ (- (+ c 1) x))))))
             :in-theory (disable alg2))))))

(local (include-book "nonstd/nsa/ln" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (defthm taylor-term-nonneg
  (implies (and (realp x) (<= 0 x))
           (<= 0 (taylor-exp-term x c)))
  :rule-classes (:rewrite :linear)))

(local (in-theory (disable taylor-exp-term)))

(local (defthm sumlist-taylor-nonneg
  (implies (and (realp x) (<= 0 x))
           (<= 0 (sumlist (taylor-exp-list n c x))))
  :rule-classes (:rewrite :linear)))

(local (defthm taylor-mono
  (implies (and (realp x) (<= 0 x) (natp k) (natp n) (<= k n))
           (<= (sumlist (taylor-exp-list k 0 x))
               (sumlist (taylor-exp-list n 0 x))))
  :hints (("Goal" :use ((:instance taylor-exp-list-split (n1 k) (n2 (- n k)) (counter 0)))
           :in-theory (disable taylor-exp-list-split)))))

(local (defthm-std standard-sumlist-taylor
  (implies (and (standardp k) (standardp x))
           (standardp (sumlist (taylor-exp-list k 0 x))))))

(local (defthm k-<-large
  (implies (and (natp k) (standardp k))
           (< k (i-large-integer)))
  :hints (("Goal" :use ((:instance large->-non-large (x (i-large-integer)) (y k)))
           :in-theory (disable large->-non-large)))
  :rule-classes :linear))

(defthm-std exp-lower-bound
  (implies (and (realp x) (<= 0 x) (natp k))
           (<= (sumlist (taylor-exp-list k 0 x)) (acl2-exp x)))
  :hints (("Goal" :in-theory (enable acl2-exp)
           :use ((:instance standard-part-<=
                            (x (sumlist (taylor-exp-list k 0 x)))
                            (y (sumlist (taylor-exp-list (i-large-integer) 0 x))))
                 (:instance taylor-mono (n (i-large-integer)))
                 (:instance standard-sumlist-taylor))
           :do-not-induct t)))

(local (defthm realp-taylor-term
  (implies (realp x) (realp (taylor-exp-term x c)))
  :hints (("Goal" :in-theory (enable taylor-exp-term)))))

(local (defthm realp-sumlist-taylor
  (implies (realp x) (realp (sumlist (taylor-exp-list n c x))))))

(local (defun tail-b (x c)
  (* (taylor-exp-term x c) (/ (+ c 1) (- (+ c 1) x)))))

(local (defthm tail-b-step
  (implies (and (realp x) (<= 0 x) (natp c) (< x (+ c 1)))
           (<= (+ (taylor-exp-term x c) (tail-b x (+ 1 c)))
               (tail-b x c)))
  :hints (("Goal" :use ((:instance tail-step-alg
                                   (tt (taylor-exp-term x c))
                                   (s (tail-b x (+ 1 c)))))
           :in-theory (disable tail-step-alg)))
  :rule-classes :linear))

(local (defthm tail-b-nonneg
  (implies (and (realp x) (<= 0 x) (natp c) (< x (+ c 1)))
           (<= 0 (tail-b x c)))
  :rule-classes :linear))

(local (in-theory (disable tail-b)))

(local (defthm tail-bound-b
  (implies (and (realp x) (<= 0 x) (natp c) (< x (+ c 1)))
           (<= (sumlist (taylor-exp-list n c x)) (tail-b x c)))
  :hints (("Goal" :induct (taylor-exp-list n c x)))))

(local (defthm tail-bound
  (implies (and (realp x) (<= 0 x) (natp c) (< x (+ c 1)))
           (<= (sumlist (taylor-exp-list n c x))
               (* (taylor-exp-term x c) (/ (+ c 1) (- (+ c 1) x)))))
  :hints (("Goal" :use tail-bound-b :in-theory (e/d (tail-b) (tail-bound-b))))))

(defun exp-ub (x k)
  (+ (sumlist (taylor-exp-list k 0 x))
     (* (taylor-exp-term x k) (/ (+ k 1) (- (+ k 1) x)))))

(local (defthm-std standard-exp-ub
  (implies (and (standardp k) (standardp x))
           (standardp (exp-ub x k)))))

(local (defthm taylor-split-k
  (implies (and (realp x) (<= 0 x) (natp k) (natp n) (<= k n) (< x (+ k 1)))
           (<= (sumlist (taylor-exp-list n 0 x)) (exp-ub x k)))
  :hints (("Goal" :use ((:instance taylor-exp-list-split (n1 k) (n2 (- n k)) (counter 0))
                        (:instance tail-bound (c k) (n (- n k))))
           :in-theory (disable taylor-exp-list-split tail-bound)))))

(local (defthm realp-exp-ub
  (implies (and (realp x) (natp k)) (realp (exp-ub x k)))))

(local (in-theory (disable exp-ub)))

(defthm-std exp-upper-bound
  (implies (and (realp x) (<= 0 x) (natp k) (< x (+ k 1)))
           (<= (acl2-exp x) (exp-ub x k)))
  :hints (("Goal" :in-theory (enable acl2-exp)
           :use ((:instance standard-part-<=
                            (y (exp-ub x k))
                            (x (sumlist (taylor-exp-list (i-large-integer) 0 x))))
                 (:instance taylor-split-k (n (i-large-integer)))
                 (:instance standard-exp-ub))
           :do-not-induct t)))
)

;; Part 2: per-factor inequalities in a
(encapsulate ()
(local (include-book "nonstd/nsa/ln" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm lt-div
  (implies (and (realp x) (realp y) (realp d) (< 0 d) (< (* x d) y))
           (< x (* y (/ d))))
  :hints (("Goal" :use ((:instance (:theorem (implies (and (realp u) (realp v) (realp c) (< 0 c) (< u v))
                                                       (< (* u c) (* v c))))
                                   (u (* x d)) (v y) (c (/ d))))))
  :rule-classes nil))

(local (defthm div-lt
  (implies (and (realp x) (realp y) (realp d) (< 0 d) (< y (* x d)))
           (< (* y (/ d)) x))
  :hints (("Goal" :use ((:instance (:theorem (implies (and (realp u) (realp v) (realp c) (< 0 c) (< u v))
                                                       (< (* u c) (* v c))))
                                   (v (* x d)) (u y) (c (/ d))))))
  :rule-classes nil))

(local (defthm div-le
  (implies (and (realp x) (realp y) (realp d) (< 0 d) (<= y (* x d)))
           (<= (* y (/ d)) x))
  :hints (("Goal" :use ((:instance (:theorem (implies (and (realp u) (realp v) (realp c) (< 0 c) (<= u v))
                                                       (<= (* u c) (* v c))))
                                   (v (* x d)) (u y) (c (/ d))))))
  :rule-classes nil))

(local (defthm a1
  (implies (and (rationalp a) (< 0 a) (<= a 1/3))
           (< (+ 1 (* 2 a) (* 2 a a) (* 8/5 a a a))
              (* (+ 1 a) (/ (- 1 a)))))
  :hints (("Goal" :use ((:instance lt-div (x (+ 1 (* 2 a) (* 2 a a) (* 8/5 a a a)))
                                   (y (+ 1 a)) (d (- 1 a))))))))

(local (defun s5 (a) (+ 1 (* 2 a) (* 2 a a) (* 4/3 a a a) (* 2/3 a a a a))))
(defun ww (a) (* (* 2 a a a) (/ (* 3 (- 1 a) (+ 1 a)))))

(local (defthm a2-poly
  (implies (and (rationalp a) (< 0 a) (<= a 1/3))
           (< (* 3 (+ 1 a) (+ 1 a))
              (* (s5 a) (+ (* 3 (- 1 a) (+ 1 a)) (* 2 a a a)))))))

(local (defthm gen-e1
  (implies (and (realp u) (realp v) (not (equal u 0)) (not (equal v 0)))
           (equal (* v (/ u)) (* (* 3 v v) (/ (* 3 u v)))))
  :rule-classes nil))

(local (defthm gen-e2
  (implies (and (realp u) (realp v) (realp s) (realp c) (not (equal u 0)) (not (equal v 0)))
           (equal (* (* s (+ 1 (* c (/ (* 3 u v))))) (* 3 u v))
                  (* s (+ (* 3 u v) c))))
  :rule-classes nil))

(local (defthm realp-s5 (implies (rationalp a) (realp (s5 a)))))
(local (defthm realp-ww (implies (rationalp a) (realp (ww a)))))

(local (defthm a2-facts
  (implies (and (rationalp a) (< 0 a) (<= a 1/3))
           (and (realp (- 1 a)) (realp (+ 1 a))
                (not (equal (- 1 a) 0)) (not (equal (+ 1 a) 0))
                (realp (* 2 a a a))
                (realp (* 3 (+ 1 a) (+ 1 a)))
                (realp (* 3 (- 1 a) (+ 1 a)))
                (< 0 (* 3 (- 1 a) (+ 1 a)))))
  :rule-classes nil))

(local (defthm real-prod-1+ (implies (and (realp s) (realp w)) (realp (* s (+ 1 w)))) :rule-classes nil))

(local (defthm a2
  (implies (and (rationalp a) (< 0 a) (<= a 1/3))
           (< (* (+ 1 a) (/ (- 1 a)))
              (* (s5 a) (+ 1 (ww a)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance div-lt (y (* 3 (+ 1 a) (+ 1 a)))
                            (d (* 3 (- 1 a) (+ 1 a)))
                            (x (* (s5 a) (+ 1 (ww a)))))
                 (:instance gen-e1 (u (- 1 a)) (v (+ 1 a)))
                 (:instance gen-e2 (u (- 1 a)) (v (+ 1 a)) (s (s5 a)) (c (* 2 a a a)))
                 a2-facts
                 (:instance real-prod-1+
                            (s (s5 a)) (w (ww a)))
                 (:instance ww)
                 realp-s5 realp-ww
                 a2-poly)))))

(local (defthm a3-frac
  (implies (and (rationalp a) (< 0 a) (<= a 1/3))
           (<= (* 4 (/ (+ 4 (* -2 a)))) 6/5))
  :hints (("Goal" :use ((:instance div-le
                                   (x 6/5) (y 4) (d (+ 4 (* -2 a)))))))))

(local (defthm a3
  (implies (and (rationalp a) (< 0 a) (<= a 1/3))
           (<= (exp-ub (* 2 a) 3) (+ 1 (* 2 a) (* 2 a a) (* 8/5 a a a))))
  :hints (("Goal" :use ((:instance (:theorem (implies (and (realp u) (realp v) (realp c) (<= 0 c) (<= u v))
                                                       (<= (* c u) (* c v))))
                                   (c (* 4/3 a a a)) (u (* 4 (/ (+ 4 (* -2 a))))) (v 6/5))
                        a3-frac)
           :in-theory (disable a3-frac)))))

(local (defthm a4
  (equal (sumlist (taylor-exp-list 5 0 (* 2 a))) (s5 a))))

(local (defthm a5
  (implies (acl2-numberp w)
           (equal (sumlist (taylor-exp-list 2 0 w)) (+ 1 w)))))

(local (in-theory (disable exp-ub)))

(defthm b1
  (implies (and (rationalp a) (< 0 a) (<= a 1/3))
           (< (acl2-exp (* 2 a)) (* (+ 1 a) (/ (- 1 a)))))
  :hints (("Goal" :use ((:instance exp-upper-bound (x (* 2 a)) (k 3))
                        a3 a1)
           :in-theory (disable exp-upper-bound a3 a1))))

(local (defthm ww-pos
  (implies (and (rationalp a) (< 0 a) (<= a 1/3))
           (< 0 (ww a)))
  :rule-classes nil))

(local (defthm s5-pos
  (implies (and (rationalp a) (< 0 a))
           (< 0 (s5 a)))
  :rule-classes nil))

(local (defthm prod-mono
  (implies (and (realp p1) (realp p2) (realp q1) (realp q2)
                (<= 0 p1) (<= p1 q1) (<= 0 p2) (<= p2 q2))
           (<= (* p1 p2) (* q1 q2)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil))


(defthm b2
  (implies (and (rationalp a) (< 0 a) (<= a 1/3))
           (< (* (+ 1 a) (/ (- 1 a))) (acl2-exp (+ (* 2 a) (ww a)))))
  :hints (("Goal" :use ((:instance exp-sum (x (* 2 a)) (y (ww a)))
                        (:instance exp-lower-bound (x (* 2 a)) (k 5))
                        (:instance exp-lower-bound (x (ww a)) (k 2))
                        (:instance a5 (w (ww a)))
                        a4 a2 ww-pos s5-pos
                        (:instance prod-mono (p1 (s5 a)) (q1 (acl2-exp (* 2 a)))
                                   (p2 (+ 1 (ww a))) (q2 (acl2-exp (ww a)))))
           :in-theory (e/d () (exp-sum exp-lower-bound a5 a4 a2 s5 ww)))))
)

;; Part 3: powers and the substitution a = 1/(2n+1)
(encapsulate ()
(local (include-book "nonstd/nsa/ln" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

(local (defun nat-ind (k) (if (zp k) 0 (nat-ind (1- k)))))

(local (defthm exp-power
  (implies (and (natp k) (acl2-numberp x))
           (equal (acl2-exp (* k x)) (expt (acl2-exp x) k)))
  :hints (("Goal" :induct (nat-ind k))
          ("Subgoal *1/2" :use ((:instance exp-sum (x (* (+ -1 k) x)) (y x)))
           :in-theory (disable exp-sum)))))

(local (defthm prod-strict
  (implies (and (realp u) (realp v) (realp p) (realp q)
                (< 0 u) (< u v) (< 0 p) (<= p q))
           (< (* u p) (* v q)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil))

(local (defthm expt-strict-mono
  (implies (and (realp u) (realp v) (< 0 u) (< u v) (posp k))
           (< (expt u k) (expt v k)))
    :hints (("Goal" :use ((:instance expt-is-non-decreasing-for-non-negatives (x u) (y v) (n (- k 1)))
                        (:instance prod-strict
                                   (p (expt u (- k 1))) (q (expt v (- k 1)))))
           :expand ((expt u k) (expt v k))
           :in-theory (disable expt-is-non-decreasing-for-non-negatives)))))

(local (defthm frac-eq
  (implies (and (acl2-numberp p) (acl2-numberp q) (acl2-numberp r) (acl2-numberp s)
                (not (equal q 0)) (not (equal s 0))
                (equal (* p s) (* r q)))
           (equal (* p (/ q)) (* r (/ s))))
  :hints (("Goal" :use ((:instance (:theorem (implies (equal u v) (equal (* u c) (* v c))))
                                   (u (* p s)) (v (* r q)) (c (/ (* q s)))))))
  :rule-classes nil))

(local (defthm g1
  (implies (and (realp m) (< 1 m))
           (equal (* (+ 1 (/ m)) (/ (- 1 (/ m)))) (* (+ m 1) (/ (- m 1)))))
  :hints (("Goal" :use ((:instance frac-eq (p (+ 1 (/ m))) (q (- 1 (/ m))) (r (+ m 1)) (s (- m 1))))))
  :rule-classes nil))

(local (defthm g2
  (implies (posp n)
           (equal (* (+ (+ 1 (* 2 n)) 1) (/ (- (+ 1 (* 2 n)) 1))) (/ (+ n 1) n)))
  :rule-classes nil))

(local (defthm m-facts
  (implies (posp n) (and (realp (+ 1 (* 2 n))) (< 1 (+ 1 (* 2 n)))))
  :rule-classes nil))

(local (defthm c1
  (implies (posp n)
           (equal (* (+ 1 (/ (+ 1 (* 2 n)))) (/ (- 1 (/ (+ 1 (* 2 n))))))
                  (/ (+ n 1) n)))
  :hints (("Goal" :use (g2 m-facts (:instance g1 (m (+ 1 (* 2 n)))))
           :in-theory (theory 'minimal-theory)))))

(local (defthm c2
  (implies (posp n)
           (equal (* (+ 1 (* 2 n)) (* 2 (/ (+ 1 (* 2 n))))) 2))))

(local (defthm g3
  (implies (and (realp m) (< 1 m))
           (equal (* m (ww (/ m))) (* 2 (/ (* 3 (- m 1) (+ m 1))))))
  :hints (("Goal" :use ((:instance frac-eq (p (* m (* 2 (/ m) (/ m) (/ m))))
                                   (q (* 3 (- 1 (/ m)) (+ 1 (/ m))))
                                   (r 2) (s (* 3 (- m 1) (+ m 1)))))))
  :rule-classes nil))

(local (defthm g4a
  (implies (posp n)
           (equal (- (/ (* 12 n)) (/ (* 12 (1+ n)))) (/ (* 12 n (+ 1 n)))))
  :hints (("Goal" :use ((:instance (:theorem (implies (and (acl2-numberp u) (acl2-numberp v)
                                                            (not (equal u 0)) (not (equal v 0)))
                                                       (equal (- (/ u) (/ v)) (* (- v u) (/ u) (/ v)))))
                                   (u (* 12 n)) (v (* 12 (+ 1 n)))))))
  :rule-classes nil))

(local (defthm g4
  (implies (posp n)
           (equal (* 2 (/ (* 3 (- (+ 1 (* 2 n)) 1) (+ (+ 1 (* 2 n)) 1))))
                  (* 2 (- (/ (* 12 n)) (/ (* 12 (1+ n)))))))
  :hints (("Goal" :use g4a))
  :rule-classes nil))

(local (defthm c3
  (implies (posp n)
           (equal (* (+ 1 (* 2 n)) (+ (* 2 (/ (+ 1 (* 2 n)))) (ww (/ (+ 1 (* 2 n))))))
                  (+ 2 (* 2 (- (/ (* 12 n)) (/ (* 12 (1+ n))))))))
  :hints (("Goal" :use (g4 m-facts (:instance g3 (m (+ 1 (* 2 n)))))
           :in-theory (disable ww)))))

(local (defthm a-facts
  (implies (posp n)
           (and (rationalp (/ (+ 1 (* 2 n))))
                (< 0 (/ (+ 1 (* 2 n))))
                (<= (/ (+ 1 (* 2 n))) 1/3)
                (natp (+ 1 (* 2 n)))
                (posp (+ 1 (* 2 n)))
                (acl2-numberp (* 2 (/ (+ 1 (* 2 n)))))
                (acl2-numberp (+ (* 2 (/ (+ 1 (* 2 n)))) (ww (/ (+ 1 (* 2 n))))))
                (realp (* 2 (/ (+ 1 (* 2 n)))))
                (realp (+ (* 2 (/ (+ 1 (* 2 n)))) (ww (/ (+ 1 (* 2 n))))))
                (realp (/ (+ n 1) n))
                (< 0 (/ (+ n 1) n))))
  :rule-classes nil))

(defthm p1
  (implies (posp n)
           (< (acl2-exp 2) (expt (/ (+ n 1) n) (+ 1 (* 2 n)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (a-facts c1 c2
                 (:instance b1 (a (/ (+ 1 (* 2 n)))))
                 (:instance exp-power (k (+ 1 (* 2 n))) (x (* 2 (/ (+ 1 (* 2 n))))))
                 (:instance acl2-exp->-0-for-reals (x (* 2 (/ (+ 1 (* 2 n))))))
                 (:instance realp-exp (x (* 2 (/ (+ 1 (* 2 n))))))
                 (:instance expt-strict-mono (k (+ 1 (* 2 n)))
                            (u (acl2-exp (* 2 (/ (+ 1 (* 2 n))))))
                            (v (/ (+ n 1) n)))))))

(defthm p2
  (implies (posp n)
           (< (expt (/ (+ n 1) n) (+ 1 (* 2 n)))
              (acl2-exp (+ 2 (* 2 (- (/ (* 12 n)) (/ (* 12 (1+ n)))))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (a-facts c1 c3
                 (:instance b2 (a (/ (+ 1 (* 2 n)))))
                 (:instance realp-exp (x (+ (* 2 (/ (+ 1 (* 2 n)))) (ww (/ (+ 1 (* 2 n)))))))
                 (:instance exp-power (k (+ 1 (* 2 n)))
                            (x (+ (* 2 (/ (+ 1 (* 2 n)))) (ww (/ (+ 1 (* 2 n)))))))
                 (:instance expt-strict-mono (k (+ 1 (* 2 n)))
                            (v (acl2-exp (+ (* 2 (/ (+ 1 (* 2 n)))) (ww (/ (+ 1 (* 2 n)))))))
                            (u (/ (+ n 1) n)))))))
)

;; Part 4: generic algebra
(encapsulate ()
(local (include-book "nonstd/nsa/ln" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm sq-lt
  (implies (and (realp u) (realp v) (< 0 u) (< 0 v) (< (* u u) (* v v)))
           (< u v))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil))

(local (defthm lt-mult
  (implies (and (realp x) (realp y) (realp c) (< 0 c) (< x y))
           (< (* x c) (* y c)))
  :rule-classes nil))

;; Theorem 1 core
(defthm t1-s1
  (implies (and (realp e) (realp n) (realp p) (realp bp) (< 0 n) (< 0 p)
                (< (* e e) (* (+ 1 n) bp bp (/ (* n p p)))))
           (< (* e e n p p) (* (+ 1 n) bp bp)))
  :hints (("Goal" :use ((:instance lt-mult (x (* e e)) (y (* (+ 1 n) bp bp (/ (* n p p))))
                                   (c (* n p p))))))
  :rule-classes nil)

(defthm t1-s2
  (implies (and (realp e) (realp n) (realp p) (realp bp) (realp sa) (realp sb)
                (< 0 e) (< 0 n) (< 0 p) (< 0 bp) (< 0 sa) (< 0 sb)
                (equal (* sa sa) n) (equal (* sb sb) (+ 1 n))
                (< (* e e n p p) (* (+ 1 n) bp bp)))
           (< (* e sa p) (* sb bp)))
  :hints (("Goal" :use ((:instance sq-lt (u (* e sa p)) (v (* sb bp))))))
  :rule-classes nil)

(local (defthm e-lhs
  (implies (and (realp n) (realp bp) (realp sb) (realp f) (realp x) (realp e)
                (< 0 n) (< 0 bp) (< 0 sb) (< 0 x) (< 0 e))
           (equal (* (* (+ 1 n) f) (/ (* sb (* (+ 1 n) bp) (/ (* x e)))))
                  (* (* e (/ (* sb bp))) (* f x))))
  :rule-classes nil))

(local (defthm e-rhs
  (implies (and (realp sa) (realp p) (realp f) (realp x) (< 0 sa) (< 0 p) (< 0 x))
           (equal (* f (/ (* sa p (/ x)))) (* (/ (* sa p)) (* f x))))
  :rule-classes nil))

(local (defthm i1
  (implies (and (realp e) (realp u) (realp v) (< 0 u) (< 0 v) (< (* e u) v))
           (< (* e (/ v)) (/ u)))
  :hints (("Goal" :use ((:instance lt-mult (x (* e u)) (y v) (c (/ (* u v)))))))
  :rule-classes nil))

(local (defthm t1-facts
  (implies (and (realp e) (realp n) (realp p) (realp bp) (realp sa) (realp sb) (realp f) (realp x)
                (< 0 e) (< 0 n) (< 0 p) (< 0 bp) (< 0 sa) (< 0 sb) (< 0 f) (< 0 x))
           (and (realp (* e (/ (* sb bp)))) (realp (/ (* sa p))) (realp (* f x)) (< 0 (* f x))
                (realp (* sa p)) (realp (* sb bp)) (< 0 (* sa p)) (< 0 (* sb bp))))
  :rule-classes nil))

(defthm t1-s3
  (implies (and (realp e) (realp n) (realp p) (realp bp) (realp sa) (realp sb) (realp f) (realp x)
                (< 0 e) (< 0 n) (< 0 p) (< 0 bp) (< 0 sa) (< 0 sb) (< 0 f) (< 0 x)
                (< (* e sa p) (* sb bp)))
           (< (* (* (+ 1 n) f) (/ (* sb (* (+ 1 n) bp) (/ (* x e)))))
              (* f (/ (* sa p (/ x))))))
  :hints (("Goal" :use (e-lhs e-rhs
                        (:instance i1 (u (* sa p)) (v (* sb bp)))
                        (:instance lt-mult (x (* e (/ (* sb bp)))) (y (/ (* sa p))) (c (* f x)))
                        t1-facts)
           :in-theory (theory 'minimal-theory)))
  :rule-classes nil)

(defthm t2-s1
  (implies (and (realp e) (realp n) (realp p) (realp bp) (< 0 n) (< 0 p)
                (< (* (+ 1 n) bp bp (/ (* n p p))) (* e e)))
           (< (* (+ 1 n) bp bp) (* e e n p p)))
  :hints (("Goal" :use ((:instance lt-mult (y (* e e)) (x (* (+ 1 n) bp bp (/ (* n p p))))
                                   (c (* n p p))))))
  :rule-classes nil)

(defthm t2-s2
  (implies (and (realp e) (realp n) (realp p) (realp bp) (realp sa) (realp sb)
                (< 0 e) (< 0 n) (< 0 p) (< 0 bp) (< 0 sa) (< 0 sb)
                (equal (* sa sa) n) (equal (* sb sb) (+ 1 n))
                (< (* (+ 1 n) bp bp) (* e e n p p)))
           (< (* sb bp) (* e sa p)))
  :hints (("Goal" :use ((:instance sq-lt (v (* e sa p)) (u (* sb bp))))))
  :rule-classes nil)

(local (defthm i2
  (implies (and (realp e) (realp u) (realp v) (< 0 u) (< 0 v) (< v (* e u)))
           (< (/ u) (* e (/ v))))
  :hints (("Goal" :use ((:instance lt-mult (y (* e u)) (x v) (c (/ (* u v)))))))
  :rule-classes nil))

(local (defthm t2-facts
  (implies (and (realp e) (realp dd) (realp n) (realp p) (realp bp) (realp sa) (realp sb) (realp f) (realp x)
                (< 0 e) (< 0 dd) (< 0 n) (< 0 p) (< 0 bp) (< 0 sa) (< 0 sb) (< 0 f) (< 0 x))
           (and (realp (* (* e dd) (/ (* sb bp)))) (realp (/ (* sa p))) (realp (* f x)) (< 0 (* f x))
                (realp (* sa p)) (realp (* sb bp)) (< 0 (* sa p)) (< 0 (* sb bp))
                (realp (* e dd))))
  :rule-classes nil))

(local (defthm e-rhs2
  (implies (and (realp n) (realp bp) (realp sb) (realp f) (realp x) (realp e) (realp dd)
                (< 0 n) (< 0 bp) (< 0 sb) (< 0 x) (< 0 e))
           (equal (* (* (* (+ 1 n) f) (/ (* sb (* (+ 1 n) bp) (/ (* x e))))) dd)
                  (* (* (* e dd) (/ (* sb bp))) (* f x))))
  :hints (("Goal" :use e-lhs))
  :rule-classes nil))

(defthm t2-s3
  (implies (and (realp e) (realp dd) (realp n) (realp p) (realp bp) (realp sa) (realp sb) (realp f) (realp x)
                (< 0 e) (< 0 dd) (< 0 n) (< 0 p) (< 0 bp) (< 0 sa) (< 0 sb) (< 0 f) (< 0 x)
                (< (* sb bp) (* (* e dd) (* sa p))))
           (< (* f (/ (* sa p (/ x))))
              (* (* (* (+ 1 n) f) (/ (* sb (* (+ 1 n) bp) (/ (* x e))))) dd)))
  :hints (("Goal" :use (e-rhs2 e-rhs
                        (:instance i2 (e (* e dd)) (u (* sa p)) (v (* sb bp)))
                        (:instance lt-mult (y (* (* e dd) (/ (* sb bp)))) (x (/ (* sa p))) (c (* f x)))
                        t2-facts)
           :in-theory (theory 'minimal-theory)))
  :rule-classes nil)
)

;; Part 5: main theorems
(encapsulate ()
(local (include-book "nonstd/nsa/ln" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm-std realp-sqrt
  (implies (realp x) (realp (acl2-sqrt x)))
  :hints (("Goal" :in-theory (enable acl2-sqrt)))))

(local (defthm fact-step
  (implies (natp n) (equal (factorial (+ 1 n)) (* (+ 1 n) (factorial n))))
  :hints (("Goal" :expand ((factorial (+ 1 n)))))))

(local (defthm expt-step-gen
  (implies (and (acl2-numberp x) (natp k)) (equal (expt x (+ 1 k)) (* x (expt x k))))
  :rule-classes nil))

(local (defthm expt-step
  (implies (natp n) (equal (expt (+ 1 n) (+ 1 n)) (* (+ 1 n) (expt (+ 1 n) n))))
  :hints (("Goal" :use ((:instance expt-step-gen (x (+ 1 n)) (k n)))
           :in-theory (theory 'minimal-theory)))))

(local (defthm exp-step
  (implies (natp n) (equal (acl2-exp (+ 1 n)) (* (acl2-exp n) (acl2-exp 1))))
  :hints (("Goal" :use ((:instance exp-sum (x n) (y 1)))))))

(local (defthm exp-2
  (equal (acl2-exp 2) (* (acl2-exp 1) (acl2-exp 1)))
  :hints (("Goal" :use ((:instance exp-sum (x 1) (y 1)))))))

(local (defthm exp-2d
  (implies (realp d)
           (equal (acl2-exp (+ 2 (* 2 d)))
                  (* (* (acl2-exp 1) (acl2-exp d)) (* (acl2-exp 1) (acl2-exp d)))))
  :hints (("Goal" :use ((:instance exp-sum (x (+ 1 d)) (y (+ 1 d)))
                        (:instance exp-sum (x 1) (y d))
                        (:instance (:theorem (implies (realp d) (and (acl2-numberp (+ 1 d)) (acl2-numberp d)
                                                                     (equal (+ (+ 1 d) (+ 1 d)) (+ 2 (* 2 d))))))))
           :in-theory (theory 'minimal-theory)))))

(local (defthm q-expt-gen
  (implies (and (posp n) (acl2-numberp u) (not (equal u 0)))
           (equal (expt (/ u n) (+ 1 (* 2 n)))
                  (* u (expt u n) (expt u n) (/ (* n (expt n n) (expt n n))))))
  :rule-classes nil))

(local (defthm n1-facts
  (implies (posp n) (and (acl2-numberp (+ 1 n)) (not (equal (+ 1 n) 0))))
  :rule-classes nil))

(local (defthm q-expt
  (implies (posp n)
           (equal (expt (/ (+ 1 n) n) (+ 1 (* 2 n)))
                  (* (+ 1 n) (expt (+ 1 n) n) (expt (+ 1 n) n) (/ (* n (expt n n) (expt n n))))))
  :hints (("Goal" :use ((:instance q-expt-gen (u (+ 1 n))) n1-facts)
           :in-theory (theory 'minimal-theory)))))

(local (defthm sr-n
  (equal (stirling-ratio n) (* (factorial n) (/ (* (acl2-sqrt n) (expt n n) (/ (acl2-exp n))))))
  :rule-classes nil))

(local (defthm posp-natp (implies (posp n) (natp n)) :rule-classes nil))

(local (defthm sr-n1
  (implies (posp n)
           (equal (stirling-ratio (+ 1 n))
                  (* (* (+ 1 n) (factorial n))
                     (/ (* (acl2-sqrt (+ 1 n)) (* (+ 1 n) (expt (+ 1 n) n))
                           (/ (* (acl2-exp n) (acl2-exp 1))))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance sr-n (n (+ 1 n))) fact-step expt-step exp-step
                 posp-natp)))
  :rule-classes nil))

(local (defthm f-d (implies (posp n) (realp (- (/ (* 12 n)) (/ (* 12 (1+ n)))))) :rule-classes nil))
(local (defthm f-fact (implies (posp n) (and (realp (factorial n)) (< 0 (factorial n)))) :rule-classes nil))
(local (defthm f-exp (implies (realp y) (and (realp (acl2-exp y)) (< 0 (acl2-exp y)))) :rule-classes nil))
(local (defthm f-prod (implies (and (realp y) (realp z) (< 0 y) (< 0 z)) (and (realp (* y z)) (< 0 (* y z))))
  :rule-classes nil))
(local (in-theory (disable sqrt-sqrt)))
(local (defthm f-sqrt (implies (and (realp y) (< 0 y))
                               (and (realp (acl2-sqrt y)) (< 0 (acl2-sqrt y))
                                    (equal (* (acl2-sqrt y) (acl2-sqrt y)) y)))
  :hints (("Goal" :in-theory (disable acl2-sqrt) :use ((:instance sqrt-sqrt (x y)))))
  :rule-classes nil))
(local (defthm f-expt (implies (and (realp y) (< 0 y) (natp k)) (and (realp (expt y k)) (< 0 (expt y k))))
  :rule-classes nil))
(local (defthm f-n (implies (posp n) (and (realp n) (< 0 n) (realp (+ 1 n)) (< 0 (+ 1 n)) (natp n)
                                          (equal (+ n 1) (+ 1 n))))
  :rule-classes nil))

(local (defthm st-facts
  (implies (posp n)
           (let ((d (- (/ (* 12 n)) (/ (* 12 (1+ n))))))
             (and (realp n) (< 0 n)
                  (realp (factorial n)) (< 0 (factorial n))
                  (realp (acl2-exp n)) (< 0 (acl2-exp n))
                  (realp (acl2-exp 1)) (< 0 (acl2-exp 1))
                  (realp (acl2-exp d)) (< 0 (acl2-exp d))
                  (realp (* (acl2-exp 1) (acl2-exp d))) (< 0 (* (acl2-exp 1) (acl2-exp d)))
                  (realp (acl2-sqrt n)) (< 0 (acl2-sqrt n))
                  (realp (acl2-sqrt (+ 1 n))) (< 0 (acl2-sqrt (+ 1 n)))
                  (equal (* (acl2-sqrt n) (acl2-sqrt n)) n)
                  (equal (* (acl2-sqrt (+ 1 n)) (acl2-sqrt (+ 1 n))) (+ 1 n))
                  (realp (expt n n)) (< 0 (expt n n))
                  (realp (expt (+ 1 n) n)) (< 0 (expt (+ 1 n) n))
                  (equal (+ n 1) (+ 1 n)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (f-d f-fact f-n
                 (:instance f-exp (y n)) (:instance f-exp (y 1))
                 (:instance f-exp (y (- (/ (* 12 n)) (/ (* 12 (1+ n))))))
                 (:instance f-prod (y (acl2-exp 1)) (z (acl2-exp (- (/ (* 12 n)) (/ (* 12 (1+ n)))))))
                 (:instance f-sqrt (y n)) (:instance f-sqrt (y (+ 1 n)))
                 (:instance f-expt (y n) (k n)) (:instance f-expt (y (+ 1 n)) (k n)))))
  :rule-classes nil))

(defthm stirling-ratio-decreasing
  (implies (posp n) (< (stirling-ratio (1+ n)) (stirling-ratio n)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (sr-n sr-n1 p1 q-expt exp-2 st-facts
                 (:instance t1-s1 (e (acl2-exp 1)) (p (expt n n)) (bp (expt (+ 1 n) n)))
                 (:instance t1-s2 (e (acl2-exp 1)) (p (expt n n)) (bp (expt (+ 1 n) n))
                            (sa (acl2-sqrt n)) (sb (acl2-sqrt (+ 1 n))))
                 (:instance t1-s3 (e (acl2-exp 1)) (p (expt n n)) (bp (expt (+ 1 n) n))
                            (sa (acl2-sqrt n)) (sb (acl2-sqrt (+ 1 n)))
                            (f (factorial n)) (x (acl2-exp n)))))))

(defthm stirling-ratio-decrease-bounded
  (implies (posp n)
           (< (stirling-ratio n)
              (* (stirling-ratio (1+ n))
                 (acl2-exp (- (/ (* 12 n)) (/ (* 12 (1+ n))))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (sr-n sr-n1 p2 q-expt st-facts
                 (:instance exp-2d (d (- (/ (* 12 n)) (/ (* 12 (1+ n))))))
                 (:instance t2-s1 (e (* (acl2-exp 1) (acl2-exp (- (/ (* 12 n)) (/ (* 12 (1+ n)))))))
                            (p (expt n n)) (bp (expt (+ 1 n) n)))
                 (:instance t2-s2 (e (* (acl2-exp 1) (acl2-exp (- (/ (* 12 n)) (/ (* 12 (1+ n)))))))
                            (p (expt n n)) (bp (expt (+ 1 n) n))
                            (sa (acl2-sqrt n)) (sb (acl2-sqrt (+ 1 n))))
                 (:instance t2-s3 (e (acl2-exp 1)) (dd (acl2-exp (- (/ (* 12 n)) (/ (* 12 (1+ n))))))
                            (p (expt n n)) (bp (expt (+ 1 n) n))
                            (sa (acl2-sqrt n)) (sb (acl2-sqrt (+ 1 n)))
                            (f (factorial n)) (x (acl2-exp n)))))))
)
