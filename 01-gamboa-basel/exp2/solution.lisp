(in-package "ACL2")

(include-book "defs")

;; ---------------- section a ----------------
(encapsulate
 ()
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local
 (defthm alt-sum-bounds
   (implies (and (alternating-sequence-p x)
                 (real-listp x)
                 (consp x)
                 (< 0 (car x)))
            (and (<= 0 (sumlist x))
                 (<= (sumlist x) (car x))))
   :hints (("Goal" :use ((:instance sumlist-alternating-sequence-lemma))
            :expand ((sumlist x))))))

(local
 (defthm tail5-bounds
   (implies (and (integerp nterms)
                 (<= 0 nterms)
                 (realp x)
                 (< 0 x)
                 (<= x 2))
            (and (<= 0 (sumlist (taylor-sincos-list nterms 5 1 x)))
                 (<= (sumlist (taylor-sincos-list nterms 5 1 x))
                     (* 1/120 (expt x 5)))))
   :hints (("Goal" :cases ((< 0 nterms)))
           ("Subgoal 1" :use ((:instance alt-sum-bounds
                                         (x (taylor-sincos-list nterms 5 1 x)))
                              (:instance alternating-sequence-p-taylor-sincos-x))
            :in-theory (disable alt-sum-bounds alternating-sequence-p-taylor-sincos-x))
           ("Subgoal 2" :expand ((taylor-sincos-list nterms 5 1 x))))))

(local
(defthm mono-*
  (implies (and (realp a) (realp b) (realp c) (<= a b) (<= 0 c))
           (<= (* a c) (* b c)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil))
(local
(defthm xx-le-4
   (implies (and (realp x) (<= 0 x) (<= x 2))
            (<= (* x x) 4))
   :hints (("Goal" :nonlinearp t))
   :rule-classes (:rewrite :linear)))
(local
(defthm x5-le-x3
   (implies (and (realp x) (< 0 x) (<= x 2))
            (<= (* 1/120 (expt x 5)) (* 1/6 (expt x 3))))
   :hints (("Goal" :use ((:instance xx-le-4)
                         (:instance mono-*
                                    (a (* x x)) (b 20) (c (* x x x))))
            :in-theory (disable xx-le-4)
            :expand ((expt x 5) (expt x 4) (expt x 3) (expt x 2))))))

(local
 (defthm taylor-sin-bounds
   (implies (and (integerp nterms)
                 (<= 4 nterms)
                 (realp x)
                 (< 0 x)
                 (<= x 2))
            (and (<= (+ x (* -1/6 (expt x 3)))
                     (sumlist (taylor-sincos-list nterms 1 1 x)))
                 (<= (sumlist (taylor-sincos-list nterms 1 1 x)) x)))
   :hints (("Goal" :use ((:instance tail5-bounds (nterms (- nterms 4)))
                         (:instance x5-le-x3))
            :in-theory (disable tail5-bounds x5-le-x3)))))

(encapsulate () (local (include-book "nonstd/nsa/trig-approx" :dir :system))
(defthm-std sine-bounds
  (implies (and (realp x)
                (< 0 x)
                (<= x 2))
           (and (<= (+ x (* -1/6 (expt x 3))) (acl2-sine x))
                (<= (acl2-sine x) x)))
  :hints (("Goal"
           :use ((:instance taylor-sin-bounds (nterms (+ -1 (i-large-integer))))
                 (:instance 4-<-large-integer)
                 (:instance taylor-sin-valid)
                 (:instance standard-part-<=
                            (x (+ x (* -1/6 (expt x 3))))
                            (y (sumlist (taylor-sincos-list (+ -1 (i-large-integer)) 1 1 x))))
                 (:instance standard-part-<=
                            (y x)
                            (x (sumlist (taylor-sincos-list (+ -1 (i-large-integer)) 1 1 x)))))
           :in-theory (disable taylor-sin-bounds 4-<-large-integer taylor-sin-valid standard-part-<=)))))
)

;; ---------------- section b ----------------
(encapsulate
 ()
(local (include-book "arithmetic-5/top" :dir :system))

(defun csc2 (x) (/ (* (acl2-sine x) (acl2-sine x))))

(defun ssum (a d m)
  (if (zp m) 0 (+ (csc2 a) (ssum (+ a d) d (1- m)))))

(defun inv2 (x) (/ (* x x)))

(defun isum (a d m)
  (if (zp m) 0 (+ (inv2 a) (isum (+ a d) d (1- m)))))

(defthm ssum-split
  (implies (and (natp m1) (natp m2) (realp a) (realp d))
           (equal (ssum a d (+ m1 m2))
                  (+ (ssum a d m1) (ssum (+ a (* m1 d)) d m2))))
  :hints (("Goal" :induct (ssum a d m1) :in-theory (disable csc2))))

(defthm isum-split
  (implies (and (natp m1) (natp m2) (realp a) (realp d))
           (equal (isum a d (+ m1 m2))
                  (+ (isum a d m1) (isum (+ a (* m1 d)) d m2))))
  :hints (("Goal" :induct (isum a d m1) :in-theory (disable inv2))))

(defthm csc2-pi-x
  (equal (csc2 (+ (acl2-pi) (- x))) (csc2 x))
  :hints (("Goal" :in-theory (disable sin-pi-x) :use ((:instance sin-pi-x)))))

(defthm ssum-reflect
  (implies (and (realp a) (realp d))
           (equal (ssum (+ (acl2-pi) (- a)) (- d) m)
                  (ssum a d m)))
  :hints (("Goal" :induct (ssum a d m) :in-theory (disable csc2))))

(defthm ssum-1
  (equal (ssum a d 1) (csc2 a))
  :hints (("Goal" :expand ((ssum a d 1)) :in-theory (disable csc2))))

(defthm isum-1
  (equal (isum a d 1) (inv2 a))
  :hints (("Goal" :expand ((isum a d 1)) :in-theory (disable inv2))))

(defthm ssum-snoc
  (implies (and (natp m) (realp a) (realp d))
           (equal (ssum a d (+ 1 m))
                  (+ (ssum a d m) (csc2 (+ a (* m d))))))
  :hints (("Goal" :use ((:instance ssum-split (m1 m) (m2 1)))
           :in-theory (disable ssum-split csc2))))

(defun nat-ind (m) (if (zp m) 0 (nat-ind (1- m))))

(defthm ssum-reverse
  (implies (and (natp m) (realp a) (realp d))
           (equal (ssum a d m)
                  (ssum (+ a (* (- m 1) d)) (- d) m)))
  :hints (("Goal" :induct (nat-ind m) :in-theory (disable csc2))
          ("Subgoal *1/2" :use ((:instance ssum-snoc (m (- m 1))))
           :expand ((ssum (+ a (* (- m 1) d)) (- d) m))
           :in-theory (disable ssum-snoc csc2)))
  :rule-classes nil)
)

;; ---------------- section c ----------------
(encapsulate
 ()
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable sine-of-sums cosine-of-sums)))

(local
 (defthm alg-0
   (implies (and (realp a) (realp b) (< 0 a) (< 0 b) (equal (+ a b) 1))
            (equal (+ (/ a) (/ b)) (/ (* a b))))
   :hints (("Goal" :use ((:instance (:theorem (implies (and (realp a) (realp b) (< 0 a) (< 0 b))
                                                        (equal (+ (/ a) (/ b)) (* (+ a b) (/ a) (/ b)))))))))))
(local
 (defthm alg-1
   (implies (and (realp s) (realp c) (< 0 s) (< 0 c)
                 (equal (+ (* s s) (* c c)) 1))
            (equal (+ (/ (* s s)) (/ (* c c)))
                   (* 4 (/ (* (* 2 s c) (* 2 s c))))))
   :hints (("Goal" :use ((:instance alg-0 (a (* s s)) (b (* c c))))
            :in-theory (disable alg-0)))
   :rule-classes nil))

(defthm sin-shift
  (equal (acl2-sine (+ y (* 1/2 (acl2-pi)))) (acl2-cosine y))
  :hints (("Goal" :use ((:instance sin-pi/2+x (x y)))
           :in-theory (union-theories '(commutativity-of-+) (theory 'minimal-theory)))))

(defthm csc2-double
  (implies (and (realp y) (< 0 y) (< y (* 1/2 (acl2-pi))))
           (equal (+ (csc2 y) (csc2 (+ y (* 1/2 (acl2-pi)))))
                  (* 4 (csc2 (* 2 y)))))
  :hints (("Goal" :use ((:instance alg-1 (s (acl2-sine y)) (c (acl2-cosine y)))
                        (:instance sine-2x (x y))
                        (:instance sin**2+cos**2 (x y))
                        (:instance sine-positive-in-0-pi/2 (x y))
                        (:instance cosine-positive-in-0-pi/2 (x y)))
           :in-theory (union-theories '(csc2 sin-shift realp-sine realp-cosine) (theory 'minimal-theory)))))
)

;; ---------------- section d ----------------
(encapsulate
 ()
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable sine-of-sums cosine-of-sums csc2)))

(local
 (defthm prod-nonneg
   (implies (and (integerp m) (< 0 m) (realp e) (<= 0 e))
            (<= 0 (* (+ -1 m) e)))
   :hints (("Goal" :nonlinearp t))))

(defthm ssum-double
  (implies (and (realp y) (realp e) (< 0 y) (<= 0 e) (natp m)
                (< (+ y (* (- m 1) e)) (* 1/2 (acl2-pi))))
           (equal (+ (ssum y e m) (ssum (+ y (* 1/2 (acl2-pi))) e m))
                  (* 4 (ssum (* 2 y) (* 2 e) m))))
  :hints (("Goal" :induct (ssum y e m))
          ("Subgoal *1/2" :use ((:instance prod-nonneg)
                                (:instance csc2-double))
           :in-theory (disable prod-nonneg csc2-double))))
)

;; ---------------- section e ----------------
(encapsulate
 ()
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable sine-of-sums cosine-of-sums csc2)))

(defun tt (m) (ssum (/ (acl2-pi) (* 2 m)) (/ (acl2-pi) m) m))
(defun hh (m) (ssum (/ (acl2-pi) (* 4 m)) (/ (acl2-pi) (* 2 m)) m))

(local
 (defthm pi-bounds-linear
   (and (<= 2 (acl2-pi)) (< (acl2-pi) 4))
   :hints (("Goal" :use pi-between-2-4))
   :rule-classes :linear))

(local (defthm x+x (equal (+ x x) (* 2 x))))

(defthm tt-split
  (implies (posp m)
           (equal (tt (* 2 m))
                  (+ (hh m)
                     (ssum (+ (/ (acl2-pi) (* 4 m)) (* 1/2 (acl2-pi))) (/ (acl2-pi) (* 2 m)) m))))
  :hints (("Goal" :use ((:instance ssum-split (a (/ (acl2-pi) (* 4 m))) (d (/ (acl2-pi) (* 2 m)))
                                   (m1 m) (m2 m)))
           :in-theory (disable ssum-split))))

(defthm tt-double
  (implies (posp m)
           (equal (tt (* 2 m)) (* 4 (tt m))))
  :hints (("Goal" :use ((:instance ssum-double (y (/ (acl2-pi) (* 4 m))) (e (/ (acl2-pi) (* 2 m)))))
           :expand ((tt m))
           :in-theory (disable ssum-double))))

(defthm ssum-cong
  (implies (equal a b) (equal (ssum a d m) (ssum b d m)))
  :rule-classes nil)

(defthm second-half
  (implies (posp m)
           (equal (ssum (+ (/ (acl2-pi) (* 4 m)) (* 1/2 (acl2-pi))) (/ (acl2-pi) (* 2 m)) m)
                  (hh m)))
  :hints (("Goal" :use ((:instance ssum-reverse (a (+ (/ (acl2-pi) (* 4 m)) (* 1/2 (acl2-pi))))
                                   (d (/ (acl2-pi) (* 2 m))))
                        (:instance ssum-reflect (a (/ (acl2-pi) (* 4 m))) (d (/ (acl2-pi) (* 2 m))))
                        (:instance ssum-cong
                                   (a (+ (* 1/2 (acl2-pi)) (* 1/2 (acl2-pi))
                                         (- (* 1/2 (acl2-pi) (/ m))) (* 1/4 (acl2-pi) (/ m))))
                                   (b (+ (acl2-pi) (- (* 1/4 (acl2-pi) (/ m)))))
                                   (d (- (* 1/2 (acl2-pi) (/ m))))))
           :in-theory (disable ssum-reflect))))

(defun pow2 (p) (if (zp p) 1 (* 2 (pow2 (1- p)))))

(defthm posp-pow2 (posp (pow2 p)) :rule-classes :type-prescription)

(defthm tt-1 (equal (tt 1) 1)
  :hints (("Goal" :in-theory (enable csc2))))

(defthm tt-pow2
  (equal (tt (pow2 p)) (* (pow2 p) (pow2 p)))
  :hints (("Goal" :in-theory (disable tt))))

(defthm hh-tt
  (implies (posp m) (equal (hh m) (* 1/2 (tt (* 2 m)))))
  :hints (("Goal" :use ((:instance tt-split) (:instance second-half))
           :in-theory (disable tt-split second-half tt-double tt hh (tt) (hh)))))

(defthm pow2-1+
  (implies (natp p) (equal (pow2 (+ 1 p)) (* 2 (pow2 p)))))

(defthm hh-pow2
  (implies (natp p) (equal (hh (pow2 p)) (* 2 (pow2 p) (pow2 p))))
  :hints (("Goal" :use ((:instance hh-tt (m (pow2 p)))
                        (:instance tt-pow2 (p (+ 1 (nfix p))))
                        (:instance pow2-1+ (p (nfix p))))
           :in-theory (disable tt hh hh-tt tt-split tt-pow2 tt-double pow2 pow2-1+ (tt) (hh)))))
)

;; ---------------- section f ----------------
(encapsulate
 ()
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable sine-of-sums cosine-of-sums csc2)))

(local
 (defthm mono-*
  (implies (and (realp a) (realp b) (realp c) (<= a b) (<= 0 c))
           (<= (* a c) (* b c)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil))

(local
 (defthm xx-le-4
   (implies (and (realp x) (<= 0 x) (<= x 2))
            (<= (* x x) 4))
   :hints (("Goal" :nonlinearp t))
   :rule-classes (:rewrite :linear)))

(local
 (defthm la
   (implies (and (realp x) (realp s) (< 0 x) (<= x 2) (<= (+ x (* -1/6 x x x)) s))
            (< 0 s))
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm lb
   (implies (and (realp x) (realp s) (< 0 s) (<= s x))
            (<= (/ (* x x)) (/ (* s s))))
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm lc1
   (implies (and (realp tt) (<= 0 tt) (<= tt 4))
            (<= 1 (* (+ 1 (* -1/6 tt)) (+ 1 (* -1/6 tt)) (+ 1 (* 3 tt)))))
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm lc2
   (implies (and (realp x) (realp s) (realp u) (<= 0 u) (< 0 x) (<= (* x u) s))
            (<= (* x x u u) (* s s)))
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm lc-abs
   (implies (and (realp xx) (realp ss) (realp v) (realp k) (< 0 xx) (<= (* xx v) ss)
                 (<= 1 (* v k)) (<= 0 k))
            (<= xx (* ss k)))
   :hints (("Goal" :use ((:instance mono-* (a 1) (b (* v k)) (c xx))
                         (:instance mono-* (a (* xx v)) (b ss) (c k)))
            :in-theory (disable <-*-right-cancel <-*-left-cancel)))))

(local
 (defthm lc
   (implies (and (realp x) (realp s) (< 0 x) (<= x 2) (<= (+ x (* -1/6 x x x)) s))
            (<= (* x x) (* s s (+ 1 (* 3 x x)))))
   :hints (("Goal" :use ((:instance lc1 (tt (* x x))) (:instance xx-le-4)
                         (:instance lc2 (u (+ 1 (* -1/6 x x))))
                         (:instance lc-abs (xx (* x x)) (ss (* s s)) (v (* (+ 1 (* -1/6 x x)) (+ 1 (* -1/6 x x))))
                                    (k (+ 1 (* 3 x x)))))
            :in-theory (disable lc1 lc2 xx-le-4 lc-abs)))))

(local
 (defthm lemd
   (implies (and (realp x) (realp s) (< 0 x) (< 0 s) (<= (* x x) (* s s (+ 1 (* 3 x x)))))
            (<= (/ (* s s)) (+ (/ (* x x)) 3)))
   :hints (("Goal" :use ((:instance mono-* (a (* x x)) (b (* s s (+ 1 (* 3 x x))))
                                    (c (/ (* x x s s)))))
            :in-theory (disable <-*-right-cancel <-*-left-cancel)))))

(defthm csc2-bounds
  (implies (and (realp x) (< 0 x) (<= x 2))
           (and (<= (inv2 x) (csc2 x))
                (<= (csc2 x) (+ (inv2 x) 3))))
  :hints (("Goal" :use ((:instance sine-bounds)
                        (:instance la (s (acl2-sine x)))
                        (:instance lb (s (acl2-sine x)))
                        (:instance lc (s (acl2-sine x)))
                        (:instance lemd (s (acl2-sine x))))
           :in-theory (e/d (csc2) (sine-bounds la lb lc lemd)))))
)

;; ---------------- section g ----------------
(encapsulate
 ()
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable sine-of-sums cosine-of-sums csc2)))

(local
 (defthm prod-nonneg
   (implies (and (integerp m) (< 0 m) (realp e) (<= 0 e))
            (<= 0 (* (+ -1 m) e)))
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm a-le-2
   (implies (and (integerp m) (< 0 m) (realp a) (realp d) (<= 0 d)
                 (<= (+ a (* (- m 1) d)) 2))
            (<= a 2))
   :hints (("Goal" :use ((:instance prod-nonneg (e d)))))
   :rule-classes nil))

(defthm ssum-isum-bounds
  (implies (and (realp a) (realp d) (< 0 a) (<= 0 d) (natp m)
                (<= (+ a (* (- m 1) d)) 2))
           (and (<= (isum a d m) (ssum a d m))
                (<= (ssum a d m) (+ (isum a d m) (* 3 m)))))
  :hints (("Goal" :induct (ssum a d m) :in-theory (disable inv2))
          ("Subgoal *1/2" :use ((:instance a-le-2)
                                (:instance csc2-bounds (x a)))
           :in-theory (disable prod-nonneg csc2-bounds inv2))))

(defthm isum-scale
  (implies (and (realp c) (not (equal c 0)) (realp a) (realp d))
           (equal (isum (* c a) (* c d) m)
                  (* (/ (* c c)) (isum a d m))))
  :hints (("Goal" :induct (isum a d m))))

(local
 (defthm pi-bounds-linear
   (and (<= 2 (acl2-pi)) (< (acl2-pi) 4))
   :hints (("Goal" :use pi-between-2-4))
   :rule-classes :linear))

(defthm hh-pow2-b
  (implies (natp p)
           (equal (ssum (* 1/4 (acl2-pi) (/ (pow2 p))) (* 1/2 (acl2-pi) (/ (pow2 p))) (pow2 p))
                  (* 2 (pow2 p) (pow2 p))))
  :hints (("Goal" :use hh-pow2 :in-theory (disable hh-pow2 pow2 hh-tt tt-pow2 tt-split second-half))))

(defthm hh-isum-bounds
  (implies (natp p)
           (and (<= (* 16 (pow2 p) (pow2 p) (/ (* (acl2-pi) (acl2-pi))) (isum 1 2 (pow2 p)))
                    (* 2 (pow2 p) (pow2 p)))
                (<= (* 2 (pow2 p) (pow2 p))
                    (+ (* 16 (pow2 p) (pow2 p) (/ (* (acl2-pi) (acl2-pi))) (isum 1 2 (pow2 p)))
                       (* 3 (pow2 p))))))
  :hints (("Goal" :use ((:instance hh-pow2-b)
                        (:instance ssum-isum-bounds (a (/ (acl2-pi) (* 4 (pow2 p))))
                                   (d (/ (acl2-pi) (* 2 (pow2 p)))) (m (pow2 p)))
                        (:instance isum-scale (c (/ (acl2-pi) (* 4 (pow2 p)))) (a 1) (d 2) (m (pow2 p))))
           :in-theory (disable hh-pow2-b hh-pow2 ssum-isum-bounds isum-scale isum ssum pow2))))
)

;; ---------------- section h ----------------
(encapsulate
 ()
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable sine-of-sums cosine-of-sums csc2)))

(local
 (defthm mono-*
  (implies (and (realp a) (realp b) (realp c) (<= a b) (<= 0 c))
           (<= (* a c) (* b c)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil))

(local
 (defthm pi-bounds-linear
   (and (<= 2 (acl2-pi)) (< (acl2-pi) 4))
   :hints (("Goal" :use pi-between-2-4))
   :rule-classes :linear))

(defthm realp-isum
  (implies (and (realp a) (realp d)) (realp (isum a d m)))
  :rule-classes (:rewrite :type-prescription))

(local
 (defthm alg-up
   (implies (and (realp k) (realp q) (realp x) (< 0 k) (< 0 q)
                 (<= (* 16 k k (/ q) x) (* 2 k k)))
            (<= x (* 1/8 q)))
   :hints (("Goal" :use ((:instance mono-* (a (* 16 k k (/ q) x)) (b (* 2 k k)) (c (* q (/ (* 16 k k))))))
            :in-theory (disable <-*-right-cancel <-*-left-cancel)))
   :rule-classes nil))

(local
 (defthm alg-lo
   (implies (and (realp k) (realp q) (realp x) (< 0 k) (< 0 q)
                 (<= (* 2 k k) (+ (* 16 k k (/ q) x) (* 3 k))))
            (<= (- (* 1/8 q) (* 3/16 q (/ k))) x))
   :hints (("Goal" :use ((:instance mono-* (b (+ (* 16 k k (/ q) x) (* 3 k))) (a (* 2 k k)) (c (* q (/ (* 16 k k))))))
            :in-theory (disable <-*-right-cancel <-*-left-cancel)))
   :rule-classes nil))

(defthm odd-bounds
  (implies (natp p)
           (and (<= (isum 1 2 (pow2 p)) (* 1/8 (acl2-pi) (acl2-pi)))
                (<= (- (* 1/8 (acl2-pi) (acl2-pi)) (* 3/16 (acl2-pi) (acl2-pi) (/ (pow2 p))))
                    (isum 1 2 (pow2 p)))))
  :hints (("Goal" :use ((:instance hh-isum-bounds)
                        (:instance alg-up (k (pow2 p)) (q (* (acl2-pi) (acl2-pi))) (x (isum 1 2 (pow2 p))))
                        (:instance alg-lo (k (pow2 p)) (q (* (acl2-pi) (acl2-pi))) (x (isum 1 2 (pow2 p)))))
           :in-theory (disable hh-isum-bounds isum pow2))))

(local (defthm x+x (equal (+ x x) (* 2 x))))
(local (defthm x+x+y (equal (+ x x y) (+ (* 2 x) y))))

(defthm isum-interleave
  (implies (and (natp m) (realp a) (realp d))
           (equal (isum a d (* 2 m))
                  (+ (isum a (* 2 d) m) (isum (+ a d) (* 2 d) m))))
  :hints (("Goal" :induct (isum a (* 2 d) m))
          ("Subgoal *1/2" :expand ((isum a d (* 2 m)) (isum (+ a d) d (+ -1 (* 2 m)))))))

(defthm even-odd
  (implies (natp m)
           (equal (isum 1 1 (* 2 m))
                  (+ (isum 1 2 m) (* 1/4 (isum 1 1 m)))))
  :hints (("Goal" :use ((:instance isum-interleave (a 1) (d 1))
                        (:instance isum-scale (c 2) (a 1) (d 1)))
           :in-theory (disable isum-interleave isum-scale isum))))

(defthm isum-nonneg
  (implies (and (realp a) (realp d)) (<= 0 (isum a d m)))
  :rule-classes (:rewrite :linear))

(local
 (defthm recip-mono
   (implies (and (realp x) (realp y) (< 0 x) (<= x y))
            (<= (/ y) (/ x)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm tele-gen
   (implies (and (realp b) (realp c) (< 0 b) (< 0 c))
            (equal (- (/ b) (/ c)) (* (- c b) (/ (* b c)))))
   :rule-classes nil))

(local
 (defthm tele-eq
   (implies (and (realp b) (< 0 b))
            (equal (- (/ b) (/ (+ 1 b))) (/ (* (+ 1 b) b))))
   :hints (("Goal" :use ((:instance tele-gen (c (+ 1 b))))))
   :rule-classes nil))

(local
 (defthm prod-le
   (implies (and (realp b) (< 0 b))
            (<= (* (+ 1 b) b) (* (+ 1 b) (+ 1 b))))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm inv2-tele-c
   (implies (and (realp b) (< 0 b))
            (<= (/ (* (+ 1 b) (+ 1 b))) (/ (* (+ 1 b) b))))
   :hints (("Goal" :use (prod-le (:instance recip-mono (x (* (+ 1 b) b)) (y (* (+ 1 b) (+ 1 b)))))
            :in-theory (disable distributivity)))
   :rule-classes nil))

(local
 (defthm inv2-tele-b
   (implies (and (realp b) (< 0 b))
            (<= (inv2 (+ 1 b)) (- (/ b) (/ (+ 1 b)))))
   :hints (("Goal" :use (tele-eq inv2-tele-c)
            :in-theory (union-theories '(inv2) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm inv2-tele
   (implies (and (realp a) (< 1 a))
            (<= (inv2 a) (- (/ (- a 1)) (/ a))))
   :hints (("Goal" :use ((:instance inv2-tele-b (b (- a 1))))))))

(defthm isum-tail
  (implies (and (realp a) (< 1 a) (natp k))
           (<= (isum a 1 k) (- (/ (- a 1)) (/ (+ a -1 k)))))
  :hints (("Goal" :induct (isum a 1 k) :in-theory (disable inv2))
          ("Subgoal *1/2" :use ((:instance inv2-tele)) :in-theory (disable inv2 inv2-tele))))
)

;; ---------------- section i ----------------
(encapsulate
 ()
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable sine-of-sums cosine-of-sums csc2)))

(local
 (defthm pi-bounds-linear
   (and (<= 2 (acl2-pi)) (< (acl2-pi) 4))
   :hints (("Goal" :use pi-between-2-4))
   :rule-classes :linear))

(defthm e-diff
  (implies (and (natp n) (< 0 n) (natp m) (<= n m))
           (and (<= (isum 1 1 n) (isum 1 1 m))
                (<= (isum 1 1 m) (+ (isum 1 1 n) (/ n)))))
  :hints (("Goal" :use ((:instance isum-split (a 1) (d 1) (m1 n) (m2 (- m n)))
                        (:instance isum-tail (a (+ 1 n)) (k (- m n))))
           :in-theory (disable isum-split isum-tail isum))))

(local
 (defthm qr-bound
   (implies (and (realp r) (< 0 r))
            (<= (* (acl2-pi) (acl2-pi) r) (* 16 r)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes :linear))

(defthm e-bounds
  (implies (and (natp p) (integerp n) (<= (pow2 p) n) (<= n (* 2 (pow2 p))))
           (and (<= (isum 1 1 n) (* 1/6 (acl2-pi) (acl2-pi)))
                (<= (- (* 1/6 (acl2-pi) (acl2-pi)) (* 6 (/ (pow2 p)))) (isum 1 1 n))))
  :hints (("Goal" :use ((:instance even-odd (m (pow2 p)))
                        (:instance odd-bounds)
                        (:instance e-diff (n (pow2 p)) (m n))
                        (:instance e-diff (n n) (m (* 2 (pow2 p))))
                        (:instance e-diff (n (pow2 p)) (m (* 2 (pow2 p))))
                        )
           :in-theory (disable even-odd odd-bounds e-diff isum pow2 isum-interleave))))
)

;; ---------------- section j ----------------
(encapsulate
 ()
(local (include-book "arithmetic-5/top" :dir :system))
(local (in-theory (disable (tau-system) sine-of-sums cosine-of-sums csc2)))

(defun pow2-floor (n)
  (if (or (zp n) (< n 2)) 0 (1+ (pow2-floor (floor n 2)))))

(defthm pf-bounds
  (implies (posp n)
           (and (<= (pow2 (pow2-floor n)) n)
                (< n (* 2 (pow2 (pow2-floor n))))))
  :rule-classes nil)

(defthm basel-isum
  (implies (and (posp i) (integerp n))
           (equal (basel-series i n) (isum i 1 (nfix (- n i)))))
  :hints (("Goal" :induct (basel-series i n))))
)

;; ---------------- section k ----------------
(encapsulate
 ()
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable sine-of-sums cosine-of-sums csc2)))

(local
 (defthm mono-*
  (implies (and (realp a) (realp b) (realp c) (<= a b) (<= 0 c))
           (<= (* a c) (* b c)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil))

(local
 (defthm k/m
   (implies (and (posp k) (posp m) (< k (* 2 m)))
            (< (* k (/ m)) 2))
   :hints (("Goal" :nonlinearp t))
   :rule-classes :linear))

(local
 (defthm recip-step
   (implies (and (posp k) (posp m) (< k (* 2 m)))
            (<= (* 6 (/ m)) (* 12 (/ k))))
   :rule-classes :linear))

(defthm e-close-classical
  (implies (posp k)
           (and (<= (isum 1 1 k) (* 1/6 (acl2-pi) (acl2-pi)))
                (<= (- (* 1/6 (acl2-pi) (acl2-pi)) (* 12 (/ k))) (isum 1 1 k))))
  :hints (("Goal" :use ((:instance pf-bounds (n k))
                        (:instance e-bounds (p (pow2-floor k)) (n k))
)
           :in-theory (disable e-bounds isum pow2 pow2-floor))))

(local
 (defthm large-gt-1
   (implies (and (i-large n) (realp n) (< 0 n))
            (< 1 n))
   :hints (("Goal" :use ((:instance large->-non-large (x n) (y 1)))
            :in-theory (disable large->-non-large)))))

(local
 (defthm small-12/k
   (implies (and (i-large n) (realp n))
            (i-small (* 12 (/ (+ -1 n)))))
   :hints (("Goal" :use ((:instance large+limited->large (x n) (y -1))
                         (:instance i-large-udivide (x (+ -1 n)))
                         (:instance limited*small->small (x 12) (y (/ (+ -1 n)))))
            :in-theory (disable large+limited->large i-large-udivide limited*small->small)))))

(local
 (defthm close-lemma
   (implies (and (realp b) (realp q) (realp e) (i-small e) (<= b q) (<= (- q e) b))
            (i-close b q))
   :hints (("Goal" :use ((:instance small-if-<-small (x e) (y (- b q))))
            :in-theory (e/d (i-close abs) (small-if-<-small))))
   :rule-classes nil))

(local
 (defthm expt-pi-2
   (equal (/ (expt (acl2-pi) 2) 6) (* 1/6 (acl2-pi) (acl2-pi)))))

(defthm MAIN-1
  (implies (and (posp n)
                (i-large n))
           (i-close (basel-series 1 n)
                    (/ (expt (acl2-pi) 2) 6)))
  :hints (("Goal" :use ((:instance basel-isum (i 1))
                        (:instance e-close-classical (k (- n 1)))
                        (:instance large-gt-1)
                        (:instance small-12/k)
                        (:instance close-lemma
                                   (b (basel-series 1 n))
                                   (q (* 1/6 (acl2-pi) (acl2-pi)))
                                   (e (* 12 (/ (+ -1 n))))))
           :in-theory (e/d (expt-pi-2) (basel-isum e-close-classical large-gt-1 small-12/k
                                      i-close isum basel-series)))))
)
