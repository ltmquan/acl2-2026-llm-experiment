;; Basel problem in ACL2(r):  sum_{i>=1} 1/i^2 = pi^2/6.
;;
;; Certify with:  cert.pl --acl2 acl2r solution.lisp
;;
;; Formalization.  (basel-partial n) = sum_{i=1}^n 1/i^2, pi is ACL2(r)'s
;; (acl2-pi) from nonstd/nsa/trig, and MAIN says that the partial sums
;; converge to pi^2/6 in the usual epsilon-N sense:
;;   for every real eps > 0 there is a natural N such that for every
;;   natural n >= N, |basel-partial(n) - pi^2/6| < eps.
;;
;; Proof outline (elementary, no polynomial roots):
;;  1. Using alternating Taylor series bounds: sin x <= x and
;;     x cos x <= sin x for 0 < x <= 2.  So for 0 < x < pi/2,
;;     1/x^2 <= csc^2 x <= 1 + 1/x^2.
;;  2. csc^2(2y) = (csc^2 y + csc^2(pi/2 - y))/4.  Using it,
;;     U(M) = sum_{k=1}^{M-1} csc^2(k pi/(2M)) satisfies U(2M) = 4U(M) + 2,
;;     so U(2^n) = (2/3)(4^n - 1).
;;  3. Summing the bounds from step 1 at x = k pi/(2M) gives
;;     pi^2/6 - 4/M <= basel-partial(M-1) <= pi^2/6 for M = 2^n.
;;  4. The partial sums increase, so they converge to pi^2/6.

(in-package "ACL2")
(include-book "nonstd/nsa/trig-approx" :dir :system)

(encapsulate ()
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable taylor-sincos-list-split-limited-non-limited
                           taylor-sincos-list-split-for-n-for-taylor-sin-term
                           sumlist-taylor-sincos-list-split
                           sumlist-taylor-sincos-list-split-2
                           standard-part-sumlist-taylor-sincos-list-split
                           standard-part-sumlist-taylor-sincos-list-split-2)))

(defthm factorial-pos
  (< 0 (factorial n))
  :rule-classes :type-prescription)

(defthm taylor-sin-term-signs
  (implies (and (realp x) (< 0 x) (natp counter) (realp sign))
           (and (implies (< sign 0) (< (taylor-sin-term sign counter x) 0))
                (implies (< 0 sign) (< 0 (taylor-sin-term sign counter x)))))
  :hints (("Goal" :in-theory (enable taylor-sin-term))))

(defthm sumlist-taylor-tail-neg
  (implies (and (natp nterms) (natp counter) (<= 2 counter)
                (realp x) (< 0 x) (<= x 2) (realp sign) (< sign 0))
           (<= (sumlist (taylor-sincos-list nterms counter sign x)) 0))
  :hints (("Goal" :do-not-induct t
           :cases ((consp (taylor-sincos-list nterms counter sign x)))
           :use ((:instance sumlist-alternating-sequence-lemma
                            (x (taylor-sincos-list nterms counter sign x)))
                 (:instance alternating-sequence-2-p-taylor-sincos-2))
           :expand ((sumlist (taylor-sincos-list nterms counter sign x)))
           :in-theory (disable alternating-sequence-2-p-taylor-sincos-2 sumlist))))

(defthm sumlist-taylor-tail-pos
  (implies (and (natp nterms) (natp counter) (<= 2 counter)
                (realp x) (< 0 x) (<= x 2) (realp sign) (< 0 sign))
           (<= 0 (sumlist (taylor-sincos-list nterms counter sign x))))
  :hints (("Goal" :do-not-induct t
           :cases ((consp (taylor-sincos-list nterms counter sign x)))
           :use ((:instance sumlist-alternating-sequence-lemma
                            (x (taylor-sincos-list nterms counter sign x)))
                 (:instance alternating-sequence-2-p-taylor-sincos-2))
           :expand ((sumlist (taylor-sincos-list nterms counter sign x)))
           :in-theory (disable alternating-sequence-2-p-taylor-sincos-2 sumlist))))

(defthm sumlist-sin-le-x
  (implies (and (natp n) (realp x) (< 0 x) (<= x 2))
           (<= (sumlist (taylor-sincos-list n 1 1 x)) x))
  :hints (("Goal" :do-not-induct t
           :expand ((taylor-sincos-list n 1 1 x))
           :use ((:instance sumlist-taylor-tail-neg (nterms (nfix (- n 2)))
                            (counter 3) (sign -1)))
           :in-theory (e/d (taylor-sin-term) (sumlist-taylor-tail-neg)))))

(defthm sumlist-sin-ge
  (implies (and (natp n) (<= 4 n) (realp x) (< 0 x) (<= x 2))
           (<= (+ x (* -1/6 (expt x 3))) (sumlist (taylor-sincos-list n 1 1 x))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance sumlist-taylor-tail-pos (nterms (- n 4))
                            (counter 5) (sign 1))
                 (:instance taylor-sin-x-expansion (nterms n)))
           :in-theory (disable sumlist-taylor-tail-pos taylor-sin-x-expansion))))

(defthm sumlist-cos-le
  (implies (and (natp n) (<= 6 n) (realp x) (< 0 x) (<= x 2))
           (<= (sumlist (taylor-sincos-list n 0 1 x))
               (+ 1 (* -1/2 (expt x 2)) (* 1/24 (expt x 4)))))
  :hints (("Goal" :do-not-induct t
           :expand ((taylor-sincos-list n 0 1 x)
                    (taylor-sincos-list (+ -2 n) 2 -1 x)
                    (taylor-sincos-list (+ -4 n) 4 1 x))
           :use ((:instance sumlist-taylor-tail-neg (nterms (- n 6))
                            (counter 6) (sign -1)))
           :in-theory (e/d (taylor-sin-term) (sumlist-taylor-tail-neg)))))

(defthm six-<-large-integer
  (< 6 (i-large-integer))
  :hints (("Goal"
	   :use ((:instance large->-non-large
			    (x (i-large-integer))
			    (y 6)))
	   :in-theory (disable large->-non-large))))

(defthm-std sine-le-x
  (implies (and (realp x) (< 0 x) (<= x 2))
           (<= (acl2-sine x) x))
  :hints (("Goal"
           :use ((:instance taylor-sin-valid)
                 (:instance sumlist-sin-le-x (n (1- (i-large-integer))))
                 (:instance standard-part-<=
                            (x (sumlist (taylor-sincos-list (1- (i-large-integer)) 1 1 x)))
                            (y x)))
           :in-theory (disable taylor-sin-valid sumlist-sin-le-x standard-part-<=))))

(defthm-std sine-ge-cubic
  (implies (and (realp x) (< 0 x) (<= x 2))
           (<= (+ x (* -1/6 (expt x 3))) (acl2-sine x)))
  :hints (("Goal"
           :use ((:instance taylor-sin-valid)
                 (:instance sumlist-sin-ge (n (1- (i-large-integer))))
                 (:instance standard-part-<=
                            (y (sumlist (taylor-sincos-list (1- (i-large-integer)) 1 1 x)))
                            (x (+ x (* -1/6 (expt x 3))))))
           :in-theory (disable taylor-sin-valid sumlist-sin-ge standard-part-<=))
          ("Goal'" :use (4-<-large-integer) :in-theory (disable 4-<-large-integer))))

(defthm-std cosine-le-quartic
  (implies (and (realp x) (< 0 x) (<= x 2))
           (<= (acl2-cosine x) (+ 1 (* -1/2 (expt x 2)) (* 1/24 (expt x 4)))))
  :hints (("Goal"
           :use ((:instance taylor-cos-valid)
                 (:instance sumlist-cos-le (n (i-large-integer)))
                 (:instance standard-part-<=
                            (x (sumlist (taylor-sincos-list (i-large-integer) 0 1 x)))
                            (y (+ 1 (* -1/2 (expt x 2)) (* 1/24 (expt x 4))))))
           :in-theory (disable taylor-cos-valid sumlist-cos-le standard-part-<=))
          ("Goal'" :use (six-<-large-integer) :in-theory (disable six-<-large-integer))))

(defun csc2 (x) (/ (* (acl2-sine x) (acl2-sine x))))

(defthm acl2-pi-lt-4-linear (< (acl2-pi) 4) :rule-classes :linear)

(defthm alg-xcos
  (implies (and (realp x) (< 0 x) (<= x 2) (realp c)
                (<= c (+ 1 (* -1/2 (expt x 2)) (* 1/24 (expt x 4)))))
           (<= (* x c) (+ x (* -1/6 (expt x 3)))))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t)))

(defthm x-cos-le-sin
  (implies (and (realp x) (< 0 x) (<= x 2))
           (<= (* x (acl2-cosine x)) (acl2-sine x)))
  :hints (("Goal" :use (sine-ge-cubic cosine-le-quartic
                         (:instance alg-xcos (c (acl2-cosine x))))
           :in-theory (disable sine-ge-cubic cosine-le-quartic))))

(defthm alg-lower
  (implies (and (realp x) (realp s) (< 0 s) (<= s x))
           (<= (/ (* x x)) (/ (* s s))))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t)))

(defthm alg-u1
  (implies (and (realp x) (realp s) (realp c) (< 0 x) (< 0 c) (<= (* x c) s))
           (<= (* (* x c) (* x c)) (* s s)))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t)))

(defthm alg-u2
  (implies (and (realp xx) (realp ss) (realp cc)
                (<= (* xx cc) ss) (equal cc (- 1 ss)))
           (<= xx (+ (* xx ss) ss)))
  :rule-classes nil)

(defthm alg-u3
  (implies (and (realp x) (realp s) (< 0 s) (< 0 x)
                (<= (* x x) (+ (* x x s s) (* s s))))
           (<= (/ (* s s)) (+ 1 (/ (* x x)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance (:theorem (implies (and (realp a) (realp b) (realp p) (< 0 p) (<= a b))
                                                      (<= (* a p) (* b p))))
                                   (a (* x x)) (b (+ (* x x s s) (* s s))) (p (/ (* x x s s))))))))

(defthm alg-upper
  (implies (and (realp x) (realp s) (realp c) (< 0 s) (< 0 x) (< 0 c)
                (<= (* x c) s) (equal (+ (* s s) (* c c)) 1))
           (<= (/ (* s s)) (+ 1 (/ (* x x)))))
  :rule-classes nil
  :hints (("Goal" :use (alg-u1 alg-u3 (:instance alg-u2 (xx (* x x)) (ss (* s s)) (cc (* c c)))))))

(defthm csc2-lower
  (implies (and (realp x) (< 0 x) (< x (* 1/2 (acl2-pi))))
           (<= (/ (* x x)) (csc2 x)))
  :hints (("Goal" :use (sine-le-x sine-positive-in-0-pi/2
                         (:instance alg-lower (s (acl2-sine x))))
           :in-theory (union-theories '(csc2 realp-sine acl2-pi-lt-4-linear) (theory 'minimal-theory)))))

(defthm csc2-upper
  (implies (and (realp x) (< 0 x) (< x (* 1/2 (acl2-pi))))
           (<= (csc2 x) (+ 1 (/ (* x x)))))
  :hints (("Goal" :use (x-cos-le-sin sine-positive-in-0-pi/2 cosine-positive-in-0-pi/2
                         sin**2+cos**2
                         (:instance alg-upper (s (acl2-sine x)) (c (acl2-cosine x))))
           :in-theory (union-theories '(csc2 realp-sine realp-cosine acl2-pi-lt-4-linear) (theory 'minimal-theory)))))

) ; end trig encapsulate

(local (include-book "arithmetic-5/top" :dir :system))
(in-theory (disable csc2))

(defthm alg-double
  (implies (and (realp s) (realp c) (< 0 s) (< 0 c) (equal (+ (* s s) (* c c)) 1))
           (equal (/ (* (* 2 s c) (* 2 s c)))
                  (* 1/4 (+ (/ (* s s)) (/ (* c c))))))
  :rule-classes nil
  :hints (("Goal" :use ((:theorem (implies (and (realp s) (realp c) (< 0 s) (< 0 c)) (equal (+ (/ (* s s)) (/ (* c c)))
                                         (* (+ (* s s) (* c c)) (/ (* s s)) (/ (* c c))))))))))

(defthm csc2-double
  (implies (and (realp y) (< 0 y) (< y (* 1/2 (acl2-pi))))
           (equal (csc2 (* 2 y))
                  (* 1/4 (+ (csc2 y) (csc2 (+ (* 1/2 (acl2-pi)) (- y)))))))
  :hints (("Goal" :use ((:instance sine-positive-in-0-pi/2 (x y)) (:instance cosine-positive-in-0-pi/2 (x y)) (:instance sin**2+cos**2 (x y))
                        (:instance sin-pi/2-x (x y))
                        (:instance sine-2x (x y))
                        (:instance alg-double (s (acl2-sine y)) (c (acl2-cosine y))))
           :in-theory (union-theories '(csc2 realp-sine realp-cosine) (theory 'minimal-theory)))))

(in-theory (disable csc2))

(defun g (k d) (csc2 (/ (* k (acl2-pi)) d)))

(defthm ang-bound-lemma
  (implies (and (posp m) (realp i) (< i (* 2 m)) (realp p) (< 0 p))
           (< (* p i (/ m)) (* 2 p)))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t)))

(defthm g-double
  (implies (and (posp m) (posp i) (< i (* 2 m)))
           (equal (g i (* 2 m))
                  (* 1/4 (+ (g i (* 4 m)) (g (- (* 2 m) i) (* 4 m))))))
  :hints (("Goal" :use ((:instance csc2-double (y (/ (* i (acl2-pi)) (* 4 m))))
                        (:instance ang-bound-lemma (p (acl2-pi)))))))

(in-theory (disable g))

(defun ssum (k d)
  (if (zp k) 0 (+ (g k d) (ssum (1- k) d))))

(defun rsum (k c d)
  (if (zp k) 0 (+ (g (- c k) d) (rsum (1- k) c d))))

(defthm rsum-ssum
  (implies (and (natp k) (natp c) (< k c))
           (equal (rsum k c d)
                  (- (ssum (1- c) d) (ssum (- c (1+ k)) d))))
  :hints (("Goal" :induct (rsum k c d))
          ("Subgoal *1/2" :expand ((ssum (- c k) d)))))

(defthm ssum-half
  (implies (and (natp k) (posp m) (< k (* 2 m)))
           (equal (ssum k (* 2 m))
                  (* 1/4 (+ (ssum k (* 4 m)) (rsum k (* 2 m) (* 4 m))))))
  :hints (("Goal" :induct (ssum k m))))

(defthm sin-pi/4-squared-0
  (equal (* (acl2-sine (* 1/2 (* 1/2 (acl2-pi)))) (acl2-sine (* 1/2 (* 1/2 (acl2-pi))))) 1/2)
  :rule-classes nil
  :hints (("Goal" :use ((:instance sine**2-half-angle (x (* 1/2 (acl2-pi)))))
           :in-theory (union-theories '(cosine-pi/2) (theory 'minimal-theory)))))

(defthm sin-pi/4-squared
  (equal (* (acl2-sine (* 1/4 (acl2-pi))) (acl2-sine (* 1/4 (acl2-pi)))) 1/2)
  :hints (("Goal" :use (sin-pi/4-squared-0) :in-theory (disable sine-pi/4 sine**2-half-angle))))

(defthm quarter-angle
  (implies (posp m) (equal (/ (* m (acl2-pi)) (* 4 m)) (* 1/4 (acl2-pi))))
  :rule-classes nil)

(defthm g-quarter
  (implies (posp m) (equal (g m (* 4 m)) 2))
  :hints (("Goal" :in-theory (union-theories '(g csc2) (theory 'minimal-theory))
           :use (sin-pi/4-squared
                 quarter-angle))))

(defun usum (m) (ssum (1- m) (* 2 m)))

(defthm u-double
  (implies (posp m)
           (equal (usum (* 2 m)) (+ 2 (* 4 (usum m)))))
  :hints (("Goal" :use ((:instance ssum-half (k (1- m)))
                        (:instance rsum-ssum (k (1- m)) (c (* 2 m)) (d (* 4 m))))
           :expand ((ssum m (* 4 m)))
           :in-theory (disable ssum-half rsum-ssum))))

(defun pow2 (n) (if (zp n) 1 (* 2 (pow2 (1- n)))))

(defthm pow2-posp (posp (pow2 n)) :rule-classes :type-prescription)

(defthm u-pow2
  (implies (natp n)
           (equal (usum (pow2 n)) (* 2/3 (- (* (pow2 n) (pow2 n)) 1))))
  :hints (("Goal" :induct (pow2 n) :in-theory (disable usum))
          ("Subgoal *1/2" :use ((:instance u-double (m (pow2 (1- n))))))))

(defun basel-partial (n)
  (if (zp n) 0 (+ (/ (* n n)) (basel-partial (1- n)))))

(defthm angle-in-range
  (implies (and (posp m) (posp k) (< k m))
           (and (< 0 (/ (* k (acl2-pi)) (* 2 m)))
                (< (/ (* k (acl2-pi)) (* 2 m)) (* 1/2 (acl2-pi)))))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t)))

(defthm inv-sq-angle
  (implies (and (posp m) (posp k))
           (equal (/ (* (/ (* k (acl2-pi)) (* 2 m)) (/ (* k (acl2-pi)) (* 2 m))))
                  (* 4 m m (/ (* (acl2-pi) (acl2-pi))) (/ (* k k)))))
  :rule-classes nil)

(defthm g-bounds
  (implies (and (posp m) (posp k) (< k m))
           (and (<= (* 4 m m (/ (* (acl2-pi) (acl2-pi))) (/ (* k k))) (g k (* 2 m)))
                (<= (g k (* 2 m)) (+ 1 (* 4 m m (/ (* (acl2-pi) (acl2-pi))) (/ (* k k)))))))
  :rule-classes nil
  :hints (("Goal" :use (angle-in-range inv-sq-angle
                        (:instance csc2-lower (x (/ (* k (acl2-pi)) (* 2 m))))
                        (:instance csc2-upper (x (/ (* k (acl2-pi)) (* 2 m)))))
           :in-theory (e/d (g) (csc2-lower csc2-upper)))))

(defthm ssum-bounds
  (implies (and (posp m) (natp k) (< k m))
           (and (<= (* 4 m m (/ (* (acl2-pi) (acl2-pi))) (basel-partial k)) (ssum k (* 2 m)))
                (<= (ssum k (* 2 m)) (+ k (* 4 m m (/ (* (acl2-pi) (acl2-pi))) (basel-partial k))))))
  :rule-classes nil
  :hints (("Goal" :induct (basel-partial k))
          ("Subgoal *1/2" :use ((:instance g-bounds)))))

(defthm div-le
  (implies (and (realp a) (realp s) (realp b) (< 0 a) (<= (* a s) b))
           (<= s (/ b a)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance (:theorem (implies (and (realp a) (realp u) (realp v) (< 0 a) (<= u v))
                                                      (<= (* u (/ a)) (* v (/ a)))))
                                   (u (* a s)) (v b))))))

(defthm le-div
  (implies (and (realp a) (realp s) (realp b) (< 0 a) (<= b (* a s)))
           (<= (/ b a) s))
  :rule-classes nil
  :hints (("Goal" :use ((:instance (:theorem (implies (and (realp a) (realp u) (realp v) (< 0 a) (<= u v))
                                                      (<= (* u (/ a)) (* v (/ a)))))
                                   (v (* a s)) (u b))))))

(defthm alg-upper-final
  (implies (and (realp p) (< 0 p) (realp m) (<= 1 m) (realp s)
                (<= (* 4 m m (/ p) s) (* 2/3 (- (* m m) 1))))
           (<= s (/ p 6)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance div-le (a (* 4 m m (/ p))) (b (* 2/3 (- (* m m) 1))))
                        (:theorem (implies (and (realp p) (< 0 p) (realp m) (<= 1 m))
                                           (equal (/ (* 2/3 (- (* m m) 1)) (* 4 m m (/ p)))
                                                  (- (/ p 6) (/ p (* 6 m m))))))
                        (:theorem (implies (and (realp p) (< 0 p) (realp m) (<= 1 m))
                                           (<= 0 (/ p (* 6 m m)))))))))

(defthm alg-lf-1
  (implies (and (realp p) (< 0 p) (realp m) (<= 1 m))
           (equal (/ (- (* 2/3 (- (* m m) 1)) (- m 1)) (* 4 m m (/ p)))
                  (+ (/ p 6) (- (/ p (* 4 m))) (/ p (* 12 m m)))))
  :rule-classes nil)

(defthm alg-lf-2
  (implies (and (realp p) (< 0 p) (realp m) (<= 1 m))
           (<= 0 (/ p (* 12 m m))))
  :rule-classes nil)

(defthm alg-lf-3
  (implies (and (realp p) (< 0 p) (< p 16) (realp m) (<= 1 m))
           (<= (/ p (* 4 m)) (/ 4 m)))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t)))

(defthm alg-lf-4
  (implies (and (realp p) (realp q) (realp r) (realp s) (realp w)
                (<= (/ (- (* 2/3 (- (* m m) 1)) (- m 1)) (* 4 m m (/ p))) s)
                (equal (/ (- (* 2/3 (- (* m m) 1)) (- m 1)) (* 4 m m (/ p))) (+ (/ p 6) (- q) r))
                (<= 0 r) (<= q w))
           (<= (- (/ p 6) w) s))
  :rule-classes nil)

(defthm alg-lower-final
  (implies (and (realp p) (< 0 p) (< p 16) (realp m) (<= 1 m) (realp s)
                (<= (* 2/3 (- (* m m) 1)) (+ (- m 1) (* 4 m m (/ p) s))))
           (<= (- (/ p 6) (/ 4 m)) s))
  :rule-classes nil
  :hints (("Goal" :use ((:instance le-div (a (* 4 m m (/ p))) (b (- (* 2/3 (- (* m m) 1)) (- m 1))))
                        alg-lf-1 alg-lf-2 alg-lf-3
                        (:instance alg-lf-4 (q (/ p (* 4 m))) (r (/ p (* 12 m m))) (w (/ 4 m))))
           :in-theory (theory 'minimal-theory))
          ("Goal'" :in-theory (enable))))

(defthm pi-sq-lemma
  (implies (and (realp x) (< 0 x) (< x 4)) (< (* x x) 16))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t)))

(defthm pi-squared-lt-16
  (< (* (acl2-pi) (acl2-pi)) 16)
  :rule-classes nil
  :hints (("Goal" :use ((:instance pi-sq-lemma (x (acl2-pi)))))))

(defthm realp-basel-partial (realp (basel-partial n)) :rule-classes :type-prescription)

(defthm pow2-partial-bounds
  (implies (natp n)
           (and (<= (basel-partial (1- (pow2 n))) (/ (* (acl2-pi) (acl2-pi)) 6))
                (<= (- (/ (* (acl2-pi) (acl2-pi)) 6) (/ 4 (pow2 n)))
                    (basel-partial (1- (pow2 n))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance ssum-bounds (m (pow2 n)) (k (1- (pow2 n))))
                        u-pow2 pi-squared-lt-16 (:instance usum (m (pow2 n)))
                        (:instance alg-upper-final (p (* (acl2-pi) (acl2-pi))) (m (pow2 n))
                                   (s (basel-partial (1- (pow2 n)))))
                        (:instance alg-lower-final (p (* (acl2-pi) (acl2-pi))) (m (pow2 n))
                                   (s (basel-partial (1- (pow2 n))))))
           :in-theory (disable u-pow2 usum ssum basel-partial pow2 ssum-half rsum-ssum u-double))))

(defthm basel-partial-mono
  (implies (and (natp a) (natp b) (<= a b))
           (<= (basel-partial a) (basel-partial b)))
  :rule-classes nil
  :hints (("Goal" :induct (basel-partial b))))

(defthm pow2-gt-n
  (implies (natp n) (< n (pow2 n)))
  :rule-classes :linear)

(defthm basel-upper
  (implies (natp n)
           (<= (basel-partial n) (/ (* (acl2-pi) (acl2-pi)) 6)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance basel-partial-mono (a n) (b (1- (pow2 n))))
                        (:instance pow2-partial-bounds))
           :in-theory (disable pow2 basel-partial))))

(defun basel-k (eps) (nfix (ceiling (/ 4 eps) 1)))

(defthm recip-a
  (implies (and (realp q) (realp z) (< 0 q) (< q z))
           (< (/ 4 z) (/ 4 q)))
  :rule-classes nil)

(defthm mult-le
  (implies (and (realp a) (realp u) (realp v) (< 0 a) (<= u v))
           (<= (* u a) (* v a)))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t)))

(defthm recip-b
  (implies (and (realp eps) (< 0 eps) (realp q) (<= (/ 4 eps) q))
           (<= (/ 4 q) eps))
  :rule-classes nil
  :hints (("Goal" :use ((:instance mult-le (u (/ 4 eps)) (v q) (a eps))
                        (:instance le-div (a q) (b 4) (s eps))))))

(defthm recip-lemma
  (implies (and (realp eps) (< 0 eps) (realp q) (<= (/ 4 eps) q) (realp z) (< q z))
           (< (/ 4 z) eps))
  :rule-classes nil
  :hints (("Goal" :use (recip-b recip-a))))

(defthm basel-k-ge
  (implies (and (realp eps) (< 0 eps))
           (<= (/ 4 eps) (basel-k eps)))
  :rule-classes nil)

(defthm basel-k-big
  (implies (and (realp eps) (< 0 eps))
           (< (/ 4 (pow2 (basel-k eps))) eps))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable pow2 basel-k)
           :use (basel-k-ge
                 (:instance pow2-gt-n (n (basel-k eps)))
                 (:instance recip-lemma (q (basel-k eps)) (z (pow2 (basel-k eps))))))))

(defun basel-n (eps) (1- (pow2 (basel-k eps))))

;; ---------------------------------------------------------------------
;; The statement: the series sum 1/i^2 converges to l (epsilon-N form).

(defun-sk basel-tail-within (l eps n0)
  (forall n (implies (and (natp n) (<= n0 n))
                     (< (abs (- (basel-partial n) l)) eps))))

(defun-sk basel-eventually-within (l eps)
  (exists n0 (and (natp n0) (basel-tail-within l eps n0))))

(defun-sk basel-series-converges-to (l)
  (forall eps (implies (and (realp eps) (< 0 eps))
                       (basel-eventually-within l eps))))

(defthm basel-tail-lemma
  (implies (and (realp eps) (< 0 eps) (natp n) (<= (basel-n eps) n))
           (< (abs (- (basel-partial n) (/ (* (acl2-pi) (acl2-pi)) 6))) eps))
  :rule-classes nil
  :hints (("Goal" :use (basel-k-big basel-upper
                        (:instance pow2-partial-bounds (n (basel-k eps)))
                        (:instance basel-partial-mono (a (basel-n eps)) (b n)))
           :in-theory (disable pow2 basel-partial basel-k))))

(defthm basel-tail-within-holds
  (implies (and (realp eps) (< 0 eps))
           (basel-tail-within (/ (* (acl2-pi) (acl2-pi)) 6) eps (basel-n eps)))
  :hints (("Goal" :in-theory (disable basel-n)
           :use ((:instance basel-tail-lemma
                            (n (basel-tail-within-witness (/ (* (acl2-pi) (acl2-pi)) 6)
                                                          eps (basel-n eps))))))))

(defthm natp-basel-n (natp (basel-n eps)) :rule-classes (:rewrite :type-prescription))

(defthm basel-eventually-within-holds
  (implies (and (realp eps) (< 0 eps))
           (basel-eventually-within (/ (* (acl2-pi) (acl2-pi)) 6) eps))
  :hints (("Goal" :in-theory (union-theories '(natp-basel-n) (theory 'minimal-theory))
           :use (basel-tail-within-holds
                 (:instance basel-eventually-within-suff
                            (l (/ (* (acl2-pi) (acl2-pi)) 6)) (n0 (basel-n eps)))))))

(defthm main
  (basel-series-converges-to (/ (* (acl2-pi) (acl2-pi)) 6))
  :hints (("Goal" :in-theory (union-theories '(basel-series-converges-to) (theory 'minimal-theory))
           :use ((:instance basel-eventually-within-holds
                            (eps (basel-series-converges-to-witness (/ (* (acl2-pi) (acl2-pi)) 6))))))))