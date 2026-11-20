(in-package "ACL2")
(include-book "defs")
(local (include-book "projects/numbers/euclid" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system))
(local (include-book "nonstd/nsa/nsa" :dir :system))

;;; Bridge to DM

(local
 (defthm ldf-equal
   (implies (and (integerp k) (< 1 k))
            (equal (least-divisor-from k n) (dm::least-divisor k n)))
   :hints (("Goal" :induct (least-divisor-from k n)
            :in-theory (enable dm::divides)))))

(local
 (defthm primep-equiv
   (equal (primep n) (dm::primep n))
   :hints (("Goal" :in-theory (enable dm::primep)))))

(local (in-theory (disable primep)))

(local
 (defthm euclid-ours
   (implies (and (primep p) (integerp a) (integerp b)
                 (integerp (/ (* a b) p)))
            (or (integerp (/ a p)) (integerp (/ b p))))
   :rule-classes nil
   :hints (("Goal" :use (:instance dm::euclid)
            :in-theory (enable dm::divides)))))

(local
 (defthm primep-ld
   (implies (and (integerp m) (<= 2 m))
            (and (primep (least-divisor-from 2 m))
                 (integerp (least-divisor-from 2 m))
                 (<= 2 (least-divisor-from 2 m))
                 (<= (least-divisor-from 2 m) m)
                 (integerp (/ m (least-divisor-from 2 m)))))
   :hints (("Goal" :use ((:instance dm::primep-least-divisor (n m))
                         (:instance dm::least-divisor-divides (n m) (k 2)))
            :in-theory (enable dm::divides)))))

(local
 (defthm primep-fc
   (implies (primep p) (and (integerp p) (<= 2 p)))
   :rule-classes :forward-chaining
   :hints (("Goal" :use (:instance dm::primep-gt-1)))))

;;; No prime divisor in [d, m]
(local (in-theory (disable primep-equiv)))

(defun npd (d m)
  (declare (xargs :measure (nfix (- (1+ m) d))))
  (if (and (integerp d) (integerp m) (<= d m))
      (and (not (and (primep d) (integerp (/ m d))))
           (npd (1+ d) m))
    t))

(defun npd-wit (d m)
  (declare (xargs :measure (nfix (- (1+ m) d))))
  (if (and (integerp d) (integerp m) (<= d m))
      (if (and (primep d) (integerp (/ m d)))
          d
        (npd-wit (1+ d) m))
    nil))

(local
 (defthm npd-necc
   (implies (and (npd d m) (integerp d) (integerp m) (integerp e) (<= d e) (<= e m) (primep e))
            (not (integerp (/ m e))))
   :hints (("Goal" :induct (npd d m)))))

(local
 (defthm npd-wit-props
   (implies (not (npd d m))
            (and (integerp (npd-wit d m))
                 (<= d (npd-wit d m))
                 (<= (npd-wit d m) m)
                 (primep (npd-wit d m))
                 (integerp (/ m (npd-wit d m)))))
   :hints (("Goal" :induct (npd-wit d m)))))

(local
 (defthm npd-large-d
   (implies (< m d) (npd d m))))

(local
 (defthm npd-step-nonprime
   (implies (and (integerp q) (not (primep q)))
            (equal (npd q m) (npd (1+ q) m)))))

(local
 (defthm npd-step-prime
   (implies (and (primep p) (posp m))
            (equal (npd p m)
                   (and (not (integerp (/ m p))) (npd (1+ p) m))))
   :hints (("Goal" :cases ((<= p m))))))

(local
 (defthm npd-2
   (implies (and (integerp m) (<= 2 m))
            (not (npd 2 m)))
   :hints (("Goal" :use ((:instance npd-necc (d 2) (e (least-divisor-from 2 m)))
                         (:instance primep-ld))
            :in-theory (disable npd npd-necc primep-ld least-divisor-from)))))

(local
 (defthm divides-le
   (implies (and (posp k) (posp e) (integerp (/ k e)))
            (<= e k))
   :rule-classes :forward-chaining
   :hints (("Goal" :use (:instance dm::divides-leq (x e) (y k))
            :in-theory (enable dm::divides)))))

(local
 (defthm k-le-pk
   (implies (and (posp k) (integerp p) (<= 2 p))
            (<= k (* p k)))
   :rule-classes :linear
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm npd-times-p-1
   (implies (and (primep p) (posp k) (npd (1+ p) (* p k)))
            (npd (1+ p) k))
   :hints (("Goal" :use ((:instance npd-wit-props (d (1+ p)) (m k))
                         (:instance npd-necc (d (1+ p)) (m (* p k)) (e (npd-wit (1+ p) k)))
                         (:instance k-le-pk))
            :in-theory (disable npd-wit-props npd-necc npd k-le-pk))
           (and stable-under-simplificationp '(:nonlinearp t)))))

(local
 (defthm npd-times-p-2
   (implies (and (primep p) (posp k) (npd (1+ p) k))
            (npd (1+ p) (* p k)))
   :hints (("Goal" :use ((:instance npd-wit-props (d (1+ p)) (m (* p k)))
                         (:instance npd-necc (d (1+ p)) (m k) (e (npd-wit (1+ p) (* p k))))
                         (:instance euclid-ours (p (npd-wit (1+ p) (* p k))) (a p) (b k))
                         (:instance divides-le (k p) (e (npd-wit (1+ p) (* p k))))
                         (:instance divides-le (e (npd-wit (1+ p) (* p k)))))
            :in-theory (disable npd-wit-props npd-necc npd divides-le)))))

(local
 (defthm npd-times-p
   (implies (and (primep p) (posp k))
            (equal (npd (1+ p) (* p k)) (npd (1+ p) k)))
   :hints (("Goal" :use (npd-times-p-1 npd-times-p-2)
            :in-theory (disable npd-times-p-1 npd-times-p-2)))))

;;; Sums over smooth numbers

(defun ssum (q x)
  (if (zp x)
      0
    (+ (if (npd q x) (expt x -2) 0)
       (ssum q (1- x)))))

(defun dsum (q p x)
  (if (zp x)
      0
    (+ (if (and (integerp (/ x p)) (npd q x)) (expt x -2) 0)
       (dsum q p (1- x)))))

(defun ssum2 (q p k)
  (if (zp k)
      0
    (+ (if (npd q (* p k)) (expt k -2) 0)
       (ssum2 q p (1- k)))))

(local
 (defthm ssum-split
   (implies (primep p)
            (equal (ssum (1+ p) x)
                   (+ (ssum p x) (dsum (1+ p) p x))))))

(local
 (defthm floor-step-div
   (implies (and (posp x) (posp p) (integerp (/ x p)))
            (equal (floor x p) (+ 1 (floor (1- x) p))))))

(local
 (defthm floor-step-nondiv
   (implies (and (posp x) (posp p) (not (integerp (/ x p))))
            (equal (floor x p) (floor (1- x) p)))))

(local
 (defthm floor-div-exact
   (implies (and (posp x) (posp p) (integerp (/ x p)))
            (equal (floor x p) (/ x p)))))

(local (in-theory (disable floor-step-div floor-step-nondiv floor-div-exact)))

(local
 (defthm ssum2-open
   (implies (posp k)
            (equal (ssum2 q p k)
                   (+ (if (npd q (* p k)) (expt k -2) 0)
                      (ssum2 q p (1- k)))))
   :rule-classes nil))

(local
 (defthm floor-prev-div
   (implies (and (posp x) (posp p) (integerp (/ x p)))
            (equal (floor (1- x) p) (+ -1 (/ x p))))
   :hints (("Goal" :use (floor-step-div floor-div-exact)))))

(local
 (defthm ssum2-step-div
   (implies (and (posp x) (posp p) (integerp (/ x p)))
            (equal (ssum2 q p (floor x p))
                   (+ (if (npd q x) (expt (/ x p) -2) 0)
                      (ssum2 q p (floor (1- x) p)))))
   :hints (("Goal" :use (floor-div-exact floor-prev-div
                         (:instance ssum2-open (k (/ x p))))
            :in-theory (disable ssum2 floor-prev-div)))))

(local
 (defthm ssum2-step-nondiv
   (implies (and (posp x) (posp p) (not (integerp (/ x p))))
            (equal (ssum2 q p (floor x p))
                   (ssum2 q p (floor (1- x) p))))
   :hints (("Goal" :use (floor-step-nondiv)
            :in-theory (disable ssum2)))))

(local
 (defthm expt-div-lemma
   (implies (and (posp x) (posp p))
            (equal (* (expt p -2) (expt (/ x p) -2))
                   (expt x -2)))))

(defund fl (x p) (floor x p))

(local
 (defthm ssum2-fl-step
   (implies (and (posp x) (posp p))
            (equal (* (expt p -2) (ssum2 q p (fl x p)))
                   (+ (if (and (integerp (/ x p)) (npd q x)) (expt x -2) 0)
                      (* (expt p -2) (ssum2 q p (fl (1- x) p))))))
   :hints (("Goal" :cases ((integerp (/ x p)))
            :use ((:instance ssum2-open (k (/ x p)))
                  floor-div-exact floor-prev-div floor-step-nondiv)
            :in-theory (e/d (fl) (ssum2 npd floor-prev-div ssum2-step-div ssum2-step-nondiv))))))

(local
 (defthm ssum2-fl-0
   (equal (ssum2 q p (fl 0 p)) 0)
   :hints (("Goal" :in-theory (enable fl)))))

(local
 (defthm dsum-reindex-fl
   (implies (and (posp p) (natp x))
            (equal (dsum q p x)
                   (* (expt p -2) (ssum2 q p (fl x p)))))
   :hints (("Goal" :induct (dsum q p x)
            :in-theory (disable ssum2)))))

(local
 (defthm dsum-reindex
   (implies (and (posp p) (natp x))
            (equal (dsum q p x)
                   (* (expt p -2) (ssum2 q p (floor x p)))))
   :hints (("Goal" :use dsum-reindex-fl :in-theory (e/d (fl) (dsum-reindex-fl dsum ssum2))))))

(local
 (defthm ssum2-is-ssum
   (implies (primep p)
            (equal (ssum2 (1+ p) p k) (ssum (1+ p) k)))
   :hints (("Goal" :induct (ssum2 (1+ p) p k)
            :in-theory (disable npd ssum-split dsum-reindex dsum-reindex-fl npd-times-p))
           ("Subgoal *1/2" :use ((:instance npd-times-p))))))

(local
 (defthm ssum-recursion
   (implies (and (primep p) (natp x))
            (equal (ssum (1+ p) x)
                   (+ (ssum p x) (* (expt p -2) (ssum (1+ p) (floor x p))))))
   :hints (("Goal" :use ((:instance ssum-split)
                         (:instance dsum-reindex (q (1+ p)))
                         (:instance ssum2-is-ssum (k (floor x p))))
            :in-theory (disable ssum-split dsum-reindex ssum2-is-ssum ssum dsum ssum2
                                dsum-reindex-fl)))))

(local (in-theory (disable ssum-split dsum-reindex ssum2-is-ssum dsum-reindex-fl)))

(local
 (defthm ssum-nonprime
   (implies (and (integerp q) (not (primep q)))
            (equal (ssum (1+ q) x) (ssum q x)))))

(local
 (defthm ssum-nonneg
   (<= 0 (ssum q x))
   :rule-classes :linear))

;;; The Euler product

(defun eprod (q) (euler-zeta2-product 2 q))

(local
 (defthm prod-upper-end
   (implies (and (integerp i) (integerp n) (<= i n))
            (equal (euler-zeta2-product i (1+ n))
                   (* (euler-zeta2-product i n)
                      (if (primep n) (/ (- 1 (expt n -2))) 1))))
   :hints (("Goal" :induct (euler-zeta2-product i n)))))

(local
 (defthm factor-pos
   (implies (and (integerp n) (<= 2 n))
            (and (< 0 (/ (- 1 (expt n -2))))
                 (<= (/ (- 1 (expt n -2))) 2)))
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm prod-pos
   (< 0 (euler-zeta2-product i n))
   :rule-classes :linear
   :hints (("Goal" :induct (euler-zeta2-product i n))
           ("Subgoal *1/2" :use ((:instance factor-pos (n i)))
            :in-theory (disable factor-pos)))))

(local
 (defthm rationalp-prod
   (rationalp (euler-zeta2-product i n))
   :rule-classes :type-prescription))

(local
 (defthm eprod-step
   (implies (and (integerp q) (<= 2 q))
            (equal (eprod (1+ q))
                   (* (eprod q) (if (primep q) (/ (- 1 (expt q -2))) 1))))
   :hints (("Goal" :in-theory (disable euler-zeta2-product)))))

(local
 (defthm eprod-props
   (and (rationalp (eprod q)) (< 0 (eprod q)))
   :rule-classes ((:type-prescription :corollary (rationalp (eprod q)))
                  (:linear :corollary (< 0 (eprod q))))))

(local (in-theory (disable eprod)))

(local
 (defthm eprod-2 (equal (eprod 2) 1) :hints (("Goal" :in-theory (enable eprod)))))

(local
 (defun q-ind (q)
   (declare (xargs :measure (nfix q)))
   (if (and (integerp q) (< 2 q)) (q-ind (1- q)) t)))

(local
 (defthm arith-mul-le
   (implies (and (rationalp a) (rationalp f) (rationalp e)
                 (< 0 a) (< 0 f) (<= f 2) (<= a e))
            (<= (* a f) (* 2 e)))
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm eprod-le-step
   (implies (and (integerp q) (< 2 q)
                 (<= (eprod (1- q)) (expt 2 (1- q))))
            (<= (eprod q) (expt 2 q)))
   :hints (("Goal" :use ((:instance eprod-step (q (1- q)))
                         (:instance factor-pos (n (1- q)))
                         (:instance arith-mul-le (a (eprod (1- q)))
                                    (f (if (primep (1- q)) (/ (- 1 (expt (1- q) -2))) 1))
                                    (e (expt 2 (1- q)))))
            :in-theory (disable eprod-step factor-pos arith-mul-le)))))

(local
 (defthm eprod-le-expt
   (implies (and (integerp q) (<= 2 q))
            (<= (eprod q) (expt 2 q)))
   :hints (("Goal" :induct (q-ind q)))))

(local (in-theory (disable ssum-recursion ssum-nonprime npd-step-prime npd-step-nonprime)))

(local
 (defthm rationalp-ssum
   (rationalp (ssum q x))
   :rule-classes :type-prescription))

(local
 (defthm ssum-zp
   (implies (zp x) (equal (ssum q x) 0))))

(local
 (defthm ssum-2
   (implies (natp x)
            (equal (ssum 2 x) (if (zp x) 0 1)))
   :hints ((and stable-under-simplificationp '(:cases ((equal x 1)))))))

(local
 (defun ind2 (q x)
   (declare (xargs :measure (llist (nfix q) (nfix x))
                   :well-founded-relation l<))
   (cond ((or (not (integerp q)) (<= q 2) (zp x)) t)
         ((not (primep (1- q))) (ind2 (1- q) x))
         (t (list (ind2 (1- q) x) (ind2 q (floor x (1- q))))))))

;;; Lower bound: smooth sum <= product

(local
 (defthm arith-l3
   (implies (and (rationalp a) (rationalp b) (rationalp aa) (rationalp bb)
                 (rationalp c) (< 0 c)
                 (equal aa (- bb (* c bb)))
                 (<= a aa) (<= b bb))
            (<= (+ a (* c b)) bb))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm expt-m2-bounds
   (implies (and (integerp p) (<= 2 p))
            (and (< 0 (expt p -2)) (< (expt p -2) 1)))
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm div-mul-lemma0
   (implies (and (rationalp a) (rationalp d) (not (equal d 0)))
            (equal (* d (/ a d)) a))
   :rule-classes nil))

(local
 (defthm div-mul-lemma
   (implies (and (rationalp a) (rationalp c) (< c 1))
            (equal (- (/ a (- 1 c)) (* c (/ a (- 1 c)))) a))
   :rule-classes nil
   :hints (("Goal" :use ((:instance div-mul-lemma0 (d (- 1 c))))
            :in-theory (theory 'minimal-theory))
           (and stable-under-simplificationp
                '(:in-theory (current-theory :here))))))

(local
 (defthm eprod-step-mul
   (implies (primep p)
            (equal (eprod p)
                   (- (eprod (1+ p)) (* (expt p -2) (eprod (1+ p))))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance eprod-step (q p))
                         (:instance expt-m2-bounds)
                         (:instance div-mul-lemma (a (eprod p)) (c (expt p -2))))
            :in-theory (disable eprod-step expt-m2-bounds)))))

(local
 (defthm l3-prime-step
   (implies (and (primep p) (natp x)
                 (<= (ssum p x) (eprod p))
                 (<= (ssum (1+ p) (floor x p)) (eprod (1+ p))))
            (<= (ssum (1+ p) x) (eprod (1+ p))))
   :hints (("Goal" :use ((:instance ssum-recursion)
                         (:instance eprod-step-mul)
                         (:instance expt-m2-bounds)
                         (:instance arith-l3 (a (ssum p x)) (b (ssum (1+ p) (floor x p)))
                                    (aa (eprod p)) (bb (eprod (1+ p))) (c (expt p -2))))
            :in-theory (disable ssum-recursion eprod-step ssum expt-m2-bounds)))))

(local
 (defthm smooth-sum-le-product
   (implies (and (integerp q) (<= 2 q) (natp x))
            (<= (ssum q x) (eprod q)))
   :hints (("Goal" :induct (ind2 q x) :in-theory (disable ssum))
           ("Subgoal *1/3" :use ((:instance l3-prime-step (p (1- q))))
            :in-theory (disable l3-prime-step ssum))
           ("Subgoal *1/2" :use ((:instance ssum-nonprime (q (1- q)))
                                 (:instance eprod-step (q (1- q))))
            :in-theory (disable ssum-nonprime eprod-step ssum)))))

;;; Upper estimate: product <= smooth sum + 2^q/(x+1)

(local
 (defthm floor-bound
   (implies (and (natp x) (posp p))
            (<= (+ 1 x) (* p (+ 1 (floor x p)))))
   :rule-classes nil))

(local
 (defthm g2
   (implies (and (rationalp m) (rationalp n) (< 0 m) (<= m n) (rationalp e) (< 0 e))
            (<= (/ e n) (/ e m)))
   :rule-classes nil))

(local
 (defthm h1
   (implies (and (integerp p) (<= 2 p) (posp z) (natp x)
                 (<= (+ 1 x) (* p z)))
            (<= (* 2 (+ 1 x)) (* (expt p 2) z)))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm arith-l4-a
   (implies (and (rationalp e) (< 0 e) (integerp p) (<= 2 p) (posp z) (natp x)
                 (<= (+ 1 x) (* p z)))
            (<= (* (expt p -2) (/ (* 2 e) z)) (/ e (+ 1 x))))
   :rule-classes nil
   :hints (("Goal" :use (h1
                         (:instance g2 (e (* 2 e)) (m (* 2 (+ 1 x))) (n (* (expt p 2) z))))))))

(local
 (defthm arith-l4-b
   (implies (and (rationalp a) (rationalp b) (rationalp aa) (rationalp bb)
                 (rationalp c) (< 0 c) (rationalp u) (rationalp v)
                 (equal aa (- bb (* c bb)))
                 (<= aa (+ a u))
                 (<= bb (+ b v))
                 (<= (* c v) u))
            (<= bb (+ a (* c b) (* 2 u))))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm l4-prime-step
   (implies (and (primep p) (natp x)
                 (<= (eprod p) (+ (ssum p x) (/ (expt 2 p) (+ 1 x))))
                 (<= (eprod (1+ p))
                     (+ (ssum (1+ p) (floor x p))
                        (/ (expt 2 (1+ p)) (+ 1 (floor x p))))))
            (<= (eprod (1+ p)) (+ (ssum (1+ p) x) (/ (expt 2 (1+ p)) (+ 1 x)))))
   :hints (("Goal" :use ((:instance ssum-recursion)
                         (:instance eprod-step-mul)
                         (:instance expt-m2-bounds)
                         (:instance floor-bound)
                         (:instance arith-l4-a (e (expt 2 p)) (z (+ 1 (floor x p))))
                         (:instance arith-l4-b (a (ssum p x)) (b (ssum (1+ p) (floor x p)))
                                    (aa (eprod p)) (bb (eprod (1+ p))) (c (expt p -2))
                                    (u (/ (expt 2 p) (+ 1 x)))
                                    (v (/ (* 2 (expt 2 p)) (+ 1 (floor x p))))))
            :in-theory (disable ssum-recursion ssum expt-m2-bounds)))))

(local
 (defthm expt2-mono-div
   (implies (and (integerp q) (natp x))
            (<= (/ (expt 2 (+ -1 q)) (+ 1 x)) (/ (expt 2 q) (+ 1 x))))))

(local
 (defthm product-le-smooth-sum
   (implies (and (integerp q) (<= 2 q) (natp x))
            (<= (eprod q) (+ (ssum q x) (/ (expt 2 q) (+ 1 x)))))
   :hints (("Goal" :induct (ind2 q x) :in-theory (disable ssum))
           ("Subgoal *1/3" :use ((:instance l4-prime-step (p (1- q))))
            :in-theory (disable l4-prime-step ssum))
           ("Subgoal *1/2" :use ((:instance ssum-nonprime (q (1- q)))
                                 (:instance eprod-step (q (1- q)))
                                 (:instance expt2-mono-div))
            :in-theory (disable ssum-nonprime eprod-step ssum expt2-mono-div))
           (and stable-under-simplificationp '(:nonlinearp t)))))

;;; Basel series facts

(local
 (defthm basel-upper-end
   (implies (and (integerp i) (integerp n) (<= i n))
            (equal (basel-series i (1+ n))
                   (+ (basel-series i n) (expt n -2))))))

(local
 (defthm rationalp-basel
   (implies (rationalp i) (rationalp (basel-series i n)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm ssum-is-basel
   (implies (and (natp x) (integerp q) (< x q))
            (equal (ssum q x) (basel-series 1 (1+ x))))
   :hints (("Goal" :induct (ssum q x)))))

(local
 (defthm ssum-diff
   (implies (and (natp x) (natp y) (<= x y))
            (<= (ssum q y) (+ (ssum q x) (basel-series (1+ x) (1+ y)))))
   :hints (("Goal" :induct (ssum q y))
           (and stable-under-simplificationp '(:cases ((equal x y)))))))

(local
 (defthm tele-step
   (implies (and (integerp i) (<= 2 i))
            (<= (+ (expt i -2) (/ i)) (/ (- i 1))))
   :hints (("Goal" :nonlinearp t))))

(local
 (defthm tele-gen
   (implies (and (integerp i) (<= 2 i) (rationalp s) (<= s (/ i)))
            (<= (+ (expt i -2) s) (/ (+ -1 i))))
   :rule-classes nil
   :hints (("Goal" :use tele-step :in-theory (theory 'minimal-theory)))))

(local
 (defthm basel-tail
   (implies (and (integerp i) (integerp n) (<= 2 i) (<= i n))
            (<= (basel-series i n) (- (/ (- i 1)) (/ (- n 1)))))
   :hints (("Goal" :induct (basel-series i n))
           (and stable-under-simplificationp
                '(:use ((:instance tele-gen
                                   (s (+ (/ (+ -1 n)) (basel-series (+ 1 i) n)))))
                  :in-theory (union-theories (theory 'minimal-theory) '(rationalp-basel)))))))

(local
 (defthm basel-tail-2
   (implies (and (integerp i) (integerp n) (<= 2 i) (<= i n))
            (<= (basel-series i n) (/ (- i 1))))
   :hints (("Goal" :use basel-tail :in-theory (disable basel-tail)))))

;;; Main theorems

(defthm euler-zeta2-product-lower
  (implies (and (integerp n) (<= 2 n))
           (<= (basel-series 1 n) (euler-zeta2-product 2 n)))
  :hints (("Goal" :use ((:instance smooth-sum-le-product (q n) (x (1- n)))
                        (:instance ssum-is-basel (q n) (x (1- n))))
           :in-theory (e/d (eprod) (smooth-sum-le-product ssum-is-basel ssum)))))

(local
 (defthm upper-y
   (implies (and (integerp n) (<= 2 n) (natp y) (<= (1- n) y))
            (<= (eprod n)
                (+ (basel-series 1 n) (/ (- n 1)) (/ (expt 2 n) (1+ y)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance product-le-smooth-sum (q n) (x y))
                         (:instance ssum-diff (q n) (x (1- n)))
                         (:instance ssum-is-basel (q n) (x (1- n)))
                         (:instance basel-tail-2 (i n) (n (1+ y))))
           :in-theory (disable product-le-smooth-sum ssum-diff ssum-is-basel
                               basel-tail-2 basel-tail ssum basel-series)))))

(local (defthm ceil-ge (implies (rationalp r) (<= r (ceiling r 1))) :rule-classes nil))

(local
 (defthm g3a
   (implies (and (rationalp g) (< 0 g) (rationalp k) (rationalp z) (< (/ k g) z))
            (< k (* g z)))
   :rule-classes nil :hints (("Goal" :nonlinearp t))))

(local
 (defthm g3b
   (implies (and (rationalp g) (rationalp k) (rationalp z) (< 0 z) (< k (* g z)))
            (< (/ k z) g))
   :rule-classes nil :hints (("Goal" :nonlinearp t))))

(local
 (defthm small-choice
   (implies (and (rationalp g) (< 0 g) (rationalp k) (< 0 k) (natp y)
                 (<= (ceiling (/ k g) 1) y))
            (< (/ k (1+ y)) g))
   :rule-classes nil
   :hints (("Goal" :use ((:instance ceil-ge (r (/ k g)))
                         (:instance g3a (z (1+ y)))
                         (:instance g3b (z (1+ y))))))))

(local
 (defun wy (a b n)
   (+ (nfix n) (nfix (ceiling (/ (expt 2 n) (- a b)) 1)))))

(local
 (defthm wy-props
   (implies (natp n)
            (and (natp (wy a b n)) (<= n (wy a b n))))
   :rule-classes ((:rewrite)
                  (:linear :corollary (implies (natp n) (<= n (wy a b n)))))))

(local
 (defthm final-gen
   (implies (and (rationalp a) (rationalp b) (natp n)
                 (<= a (+ b (/ (expt 2 n) (1+ (wy a b n))))))
            (<= a b))
   :rule-classes nil
   :hints (("Goal" :use ((:instance small-choice (g (- a b)) (k (expt 2 n))
                                    (y (wy a b n)))))
           (and stable-under-simplificationp '(:nonlinearp t)))))

(local (in-theory (disable wy)))

(defthm euler-zeta2-product-upper
  (implies (and (integerp n) (<= 2 n))
           (<= (euler-zeta2-product 2 n)
               (+ (basel-series 1 n) (/ (- n 1)))))
  :hints (("Goal"
           :use ((:instance upper-y
                            (y (wy (euler-zeta2-product 2 n)
                                   (+ (basel-series 1 n) (/ (- n 1))) n)))
                 (:instance final-gen
                            (a (euler-zeta2-product 2 n))
                            (b (+ (basel-series 1 n) (/ (- n 1))))))
           :in-theory (e/d (eprod) (euler-zeta2-product basel-series)))))

;;; Nonstandard corollary

(local
 (defthm not-large-1
   (not (i-large 1))
   :hints (("Goal" :in-theory (enable i-large)))))

(local
 (defthm large-minus-1
   (implies (i-large n) (i-large (+ -1 n)))
   :hints (("Goal" :use ((:instance large+limited->large (x n) (y -1)))
            :in-theory (disable large+limited->large)))))

(defthm euler-product-close-to-basel-series
  (implies (and (posp n) (i-large n))
           (i-close (euler-zeta2-product 2 n) (basel-series 1 n)))
  :hints (("Goal"
           :cases ((equal n 1))
           :use (euler-zeta2-product-lower
                 euler-zeta2-product-upper
                 (:instance i-large-udivide (x (+ -1 n)))
                 (:instance small-if-<-small
                            (x (/ (+ -1 n)))
                            (y (- (euler-zeta2-product 2 n) (basel-series 1 n)))))
           :in-theory (e/d (i-close)
                           (euler-zeta2-product-lower euler-zeta2-product-upper
                            i-large-udivide small-if-<-small
                            euler-zeta2-product basel-series)))))
