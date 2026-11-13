(in-package "DM")

(include-book "defs")

;;;=====================================================================
;;; Part 1: Row-vector times matrix (fcomb) and matrix-level facts
;;;=====================================================================

(defthmd flistnp-nth-diff
  (implies (and (flistnp x n) (flistnp y n) (natp n) (not (equal x y)))
           (let ((k (nth-diff x y)))
             (and (natp k) (< k n) (not (equal (nth k x) (nth k y))))))
  :hints (("Goal" :use ((:instance nth-diff-diff)))))

(defthm flistnp-flist0p-equal
  (implies (and (flistnp x n) (natp n) (flist0p x))
           (equal (flistn0 n) x))
  :rule-classes ()
  :hints (("Goal" :use ((:instance flist0p-flistn0-len)))))

(defun fcomb (d a n)
  (if (consp d)
      (flist-add (flist-scalar-mul (car d) (car a))
                 (fcomb (cdr d) (cdr a) n))
    (flistn0 n)))

(defthm flistnp-fcomb
  (implies (and (flistnp d m) (fmatp a m n))
           (flistnp (fcomb d a n) n)))

(defthm nth-fcomb
  (implies (and (flistnp d m) (fmatp a m n) (natp n) (natp j) (< j n))
           (equal (nth j (fcomb d a n))
                  (fdot d (col j a))))
  :hints (("Subgoal *1/3" :use ((:instance nth-flist-add (x (flist-scalar-mul (car d) (car a)))
                                           (y (fcomb (cdr d) (cdr a) n)) (i j))
                                (:instance nth-flist-scalar-mul (c (car d)) (x (car a)) (i j))))))

(defthm fcomb-flistn0
  (implies (fmatp a m n)
           (equal (fcomb (flistn0 m) a n)
                  (flistn0 n))))

(defthm flistnp-fdot-list-transpose
  (implies (and (fmatp a m n) (posp m) (posp n) (flistnp d m))
           (flistnp (fdot-list d (transpose-mat a)) n))
  :hints (("Goal" :use ((:instance fmatp-transpose)))))

(defthmd fdot-list-transpose-fcomb
  (implies (and (fmatp a m n) (posp m) (posp n) (flistnp d m))
           (equal (fdot-list d (transpose-mat a))
                  (fcomb d a n)))
  :hints (("Goal" :use ((:instance flistnp-nth-diff
                                   (x (fdot-list d (transpose-mat a)))
                                   (y (fcomb d a n)))
                        (:instance fmatp-transpose))
                  :in-theory (disable flistnp-nth-diff))))

(defthmd fmat*-row-mat
  (implies (and (fmatp a m n) (posp m) (posp n) (flistnp d m))
           (equal (fmat* (list d) a)
                  (list (fcomb d a n))))
  :hints (("Goal" :expand ((fmat* (list d) a) (fmat* nil a))
                  :in-theory (enable fdot-list-transpose-fcomb))))

(defthmd nth-fmat*-fcomb
  (implies (and (fmatp a m k) (fmatp b k n) (posp m) (posp k) (posp n)
                (natp i) (< i m))
           (equal (nth i (fmat* a b))
                  (fcomb (nth i a) b n)))
  :hints (("Goal" :in-theory (enable nth-fmat* fdot-list-transpose-fcomb))))

(defthmd fcomb-fmat*
  (implies (and (fmatp a m k) (fmatp b k n) (posp m) (posp k) (posp n)
                (flistnp d m))
           (equal (fcomb d (fmat* a b) n)
                  (fcomb (fcomb d a k) b n)))
  :hints (("Goal" :use ((:instance fmat*-assoc (a (list d)) (b a) (c b) (m 1) (n m) (p k) (q n))
                        (:instance fmat*-row-mat (a (fmat* a b)) (m m) (n n))
                        (:instance fmat*-row-mat (a a) (m m) (n k))
                        (:instance fmat*-row-mat (a b) (d (fcomb d a k)) (m k) (n n))))))

(defthmd fcomb-id-fmat
  (implies (and (posp m) (flistnp d m))
           (equal (fcomb d (id-fmat m) m) d))
  :hints (("Goal" :use ((:instance id-fmat-right (a (list d)) (m 1) (n m))
                        (:instance fmat*-row-mat (a (id-fmat m)) (n m))))))

;; If a has rank less than m, the last row of (row-reduce-mat a) is a nontrivial
;; dependence relation:

(defthm funit-not-flistn0
  (implies (and (natp j) (natp n) (< j n))
           (not (equal (funit j n) (flistn0 n))))
  :hints (("Goal" :use ((:instance nth-funit (i j))
                        (:instance nth-flistn0 (i j))))))

(defthmd fcomb-funit-nonzero
  (implies (and (fmatp q m m) (natp i) (< i m) (natp m)
                (equal (fcomb d q m) (funit i m)))
           (not (equal d (flistn0 m))))
  :hints (("Goal" :use ((:instance funit-not-flistn0 (j i) (n m))
                        (:instance fcomb-flistn0 (a q) (n m)))
                  :in-theory (disable funit flistn0 fcomb funit-not-flistn0 fcomb-flistn0))))

(defthmd rdd-1
  (implies (and (fmatp a m n) (posp m) (posp n))
           (flistnp (nth (1- m) (row-reduce-mat a)) m))
  :hints (("Goal" :use ((:instance fmatp-row-reduce-mat)
                        (:instance flistnp-row (a (row-reduce-mat a)) (n m) (i (1- m))))
                  :in-theory (disable flistnp-row))))

(defthmd rdd-2
  (implies (and (fmatp a m n) (posp m) (posp n) (< (row-rank a) m))
           (equal (fcomb (nth (1- m) (row-reduce-mat a)) a n) (flistn0 n)))
  :hints (("Goal" :use ((:instance fmatp-row-reduce-mat)
                        (:instance row-ops-mat-row-reduce)
                        (:instance nth-fmat*-fcomb (a (row-reduce-mat a)) (b a) (k m) (i (1- m)))
                        (:instance fmatp-row-reduce)
                        (:instance row-echelon-p-row-reduce)
                        (:instance num-nonzero-rows-nonzero (a (row-reduce a)) (i (1- m)))
                        (:instance flistnp-flist0p-equal (x (nth (1- m) (row-reduce a))))
                        (:instance flistnp-row (a (row-reduce a)) (i (1- m))))
                  :in-theory (disable nth-fcomb flistnp-row))))

(defthmd rdd-3
  (implies (and (fmatp a m n) (posp m) (posp n))
           (not (equal (nth (1- m) (row-reduce-mat a)) (flistn0 m))))
  :hints (("Goal" :use ((:instance fmatp-row-reduce-mat)
                        (:instance invertiblep-row-reduce-mat)
                        (:instance invertiblep-sufficient (a (row-reduce-mat a)) (n m))
                        (:instance nth-fmat*-fcomb (a (row-reduce-mat a))
                                   (b (inverse-mat (row-reduce-mat a))) (k m) (n m) (i (1- m)))
                        (:instance nth-id-fmat (n m) (i (1- m)))
                        (:instance fcomb-funit-nonzero (q (inverse-mat (row-reduce-mat a)))
                                   (i (1- m)) (d (nth (1- m) (row-reduce-mat a)))))
                  :in-theory (disable nth-fcomb nth-id-fmat funit flistn0))))

(defthmd rank-deficient-dep
  (implies (and (fmatp a m n) (posp m) (posp n) (< (row-rank a) m))
           (let ((d (nth (1- m) (row-reduce-mat a))))
             (and (flistnp d m)
                  (not (equal d (flistn0 m)))
                  (equal (fcomb d a n) (flistn0 n)))))
  :hints (("Goal" :use (rdd-1 rdd-2 rdd-3)
                  :in-theory (disable row-rank))))

;; Columns of a matrix that are unit vectors:

(defthmd fcomb-unit-col
  (implies (and (flistnp d m) (fmatp a m n) (posp m) (natp n) (natp k) (< k n)
                (natp i) (< i m)
                (equal (col k a) (funit i m)))
           (equal (nth k (fcomb d a n))
                  (nth i d)))
  :hints (("Goal" :in-theory (enable fdot-comm)
                  :use ((:instance fdot-funit-comm (x d) (n m) (j i))))))

(defthmd flistnp-not-zero
  (implies (and (flistnp d m) (natp m) (not (equal d (flistn0 m))))
           (let ((i (nth-diff d (flistn0 m))))
             (and (natp i) (< i m) (not (equal (nth i d) (f0))))))
  :hints (("Goal" :use ((:instance flistnp-nth-diff (x d) (y (flistn0 m)) (n m))))))

;; In a row-echelon matrix with all rows nonzero, the lead columns are unit vectors:

(defthmd col-lead-inds-funit
  (implies (and (fmatp r m n) (posp m) (posp n) (row-echelon-p r)
                (= (num-nonzero-rows r) m)
                (natp i) (< i m))
           (equal (col (nth i (lead-inds r)) r)
                  (funit i m)))
  :hints (("Goal" :use ((:instance flistnp-nth-diff (x (col (nth i (lead-inds r)) r))
                                   (y (funit i m)) (n m))
                        (:instance nth-col-lead-inds (a r)
                                   (k (nth-diff (col (nth i (lead-inds r)) r) (funit i m))))
                        (:instance row-reduce-row-echelon-p (a r))
                        (:instance nth-lead-inds-bound (a r) (k i))
                        (:instance len-lead-inds-num-nonzero-rows (a r)))
                  :in-theory (disable nth-col-lead-inds))))

(defthmd nth-lead-fcomb
  (implies (and (fmatp r m n) (posp m) (posp n) (row-echelon-p r)
                (= (num-nonzero-rows r) m)
                (flistnp e m)
                (natp i) (< i m))
           (equal (nth (nth i (lead-inds r)) (fcomb e r n))
                  (nth i e)))
  :hints (("Goal" :use ((:instance col-lead-inds-funit)
                        (:instance nth-lead-inds-bound (a r) (k i))
                        (:instance len-lead-inds-num-nonzero-rows (a r))
                        (:instance fcomb-unit-col (d e) (a r) (k (nth i (lead-inds r))))))))

(defthm echelon-indep
  (implies (and (fmatp r m n) (posp m) (posp n) (row-echelon-p r)
                (= (num-nonzero-rows r) m)
                (flistnp e m)
                (equal (fcomb e r n) (flistn0 n)))
           (equal e (flistn0 m)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance flistnp-not-zero (d e))
                        (:instance nth-lead-fcomb (i (nth-diff e (flistn0 m))))
                        (:instance nth-lead-inds-bound (a r) (k (nth-diff e (flistn0 m))))
                        (:instance len-lead-inds-num-nonzero-rows (a r))))))

;; Factorization a = q r, where r = (row-reduce a), q = (inverse-mat (row-reduce-mat a)):

(defthmd row-reduce-factor
  (implies (and (fmatp a m n) (posp m) (posp n))
           (let ((p (row-reduce-mat a))
                 (q (inverse-mat (row-reduce-mat a))))
             (and (fmatp q m m)
                  (equal (fmat* q p) (id-fmat m))
                  (equal (fmat* p q) (id-fmat m))
                  (equal (fmat* q (row-reduce a)) a))))
  :hints (("Goal" :use ((:instance fmatp-row-reduce-mat)
                        (:instance row-ops-mat-row-reduce)
                        (:instance invertiblep-row-reduce-mat)
                        (:instance invertiblep-sufficient (a (row-reduce-mat a)) (n m))
                        (:instance fmat*-assoc (a (inverse-mat (row-reduce-mat a)))
                                   (b (row-reduce-mat a)) (c a) (n m) (p m) (q n))
                        (:instance id-fmat-left)))))

(defthm full-rank-indep
  (implies (and (fmatp a m n) (posp m) (posp n) (= (row-rank a) m)
                (flistnp d m) (equal (fcomb d a n) (flistn0 n)))
           (equal d (flistn0 m)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance row-reduce-factor)
                        (:instance fmatp-row-reduce)
                        (:instance row-echelon-p-row-reduce)
                        (:instance fcomb-fmat* (a (inverse-mat (row-reduce-mat a)))
                                   (b (row-reduce a)) (k m))
                        (:instance echelon-indep (r (row-reduce a))
                                   (e (fcomb d (inverse-mat (row-reduce-mat a)) m)))
                        (:instance fcomb-fmat* (a (inverse-mat (row-reduce-mat a)))
                                   (b (row-reduce-mat a)) (k m) (n m))
                        (:instance fmatp-row-reduce-mat)
                        (:instance fcomb-id-fmat)
                        (:instance fcomb-flistn0 (a (row-reduce-mat a)) (n m))))))

;; A unit vector at a non-lead index is not in the row space of a full-rank matrix:

(defthmd not-in-row-space
  (implies (and (fmatp a m n) (posp m) (posp n) (= (row-rank a) m)
                (natp j) (< j n)
                (not (member j (lead-inds (row-reduce a))))
                (flistnp c m))
           (not (equal (fcomb c a n) (funit j n))))
  :hints (("Goal" :use ((:instance row-reduce-factor)
                        (:instance fmatp-row-reduce)
                        (:instance row-echelon-p-row-reduce)
                        (:instance fcomb-fmat* (d c) (a (inverse-mat (row-reduce-mat a)))
                                   (b (row-reduce a)) (k m))
                        (:instance flistnp-not-zero (d (fcomb c (inverse-mat (row-reduce-mat a)) m)))
                        (:instance nth-lead-fcomb (r (row-reduce a))
                                   (e (fcomb c (inverse-mat (row-reduce-mat a)) m))
                                   (i (nth-diff (fcomb c (inverse-mat (row-reduce-mat a)) m) (flistn0 m))))
                        (:instance nth-lead-inds-bound (a (row-reduce a))
                                   (k (nth-diff (fcomb c (inverse-mat (row-reduce-mat a)) m) (flistn0 m))))
                        (:instance member-nth (n (nth-diff (fcomb c (inverse-mat (row-reduce-mat a)) m) (flistn0 m)))
                                   (l (lead-inds (row-reduce a))))
                        (:instance len-lead-inds-num-nonzero-rows (a (row-reduce a)))
                        (:instance nth-funit (n n) (j j)
                                   (i (nth (nth-diff (fcomb c (inverse-mat (row-reduce-mat a)) m) (flistn0 m))
                                           (lead-inds (row-reduce a)))))
                        (:instance funit-not-flistn0))
                  :in-theory (disable nth-funit member-nth funit-not-flistn0))))

(defthmd fs-neg-neg
  (implies (and (fp x) (fp y))
           (equal (f* (f- x) (f- y)) (f* x y)))
  :hints (("Goal" :use ((:instance f-f* (x (f- x)) (y y))
                        (:instance f-f* (x y) (y x))
                        (:instance f*comm (x (f- x)) (y y))
                        (:instance f*comm (x x) (y y))
                        (:instance f-f- (x (f* x y))))
                  :in-theory (disable f-f-))))


(defthm fs-neg1
  (implies (fp c) (equal (f* (f- (f1)) c) (f- c)))
  :hints (("Goal" :use ((:instance f-f* (x c) (y (f1)))
                        (:instance f*comm (x c) (y (f- (f1))))))))

(defthm fs-neg-cancel
  (implies (and (fp e) (fp c) (equal (f+ e (f- c)) (f0)))
           (equal e c))
  :rule-classes ()
  :hints (("Goal" :use ((:instance f-unique (x e) (y (f- c)))
                        (:instance f-f- (x e))
                        (:instance f-f- (x c)))
                  :in-theory (disable f-f-))))

(defun fs-ind2 (a b n)
  (if (zp n)
      (list a b)
    (fs-ind2 (cdr a) (cdr b) (1- n))))

(defthm fs-flist-neg-cancel
  (implies (and (flistnp e n) (flistnp c n)
                (equal (flist-add e (flist-scalar-mul (f- (f1)) c)) (flistn0 n)))
           (equal e c))
  :rule-classes ()
  :hints (("Goal" :induct (fs-ind2 e c n))
          ("Subgoal *1/2" :use ((:instance fs-neg-cancel (e (car e)) (c (car c)))))))

(defthm fs-ks-step
  (implies (and (fp a) (fp b) (fp s))
           (equal (f+ (f* a (f- b)) (f- s))
                  (f- (f+ (f* b a) s))))
  :hints (("Goal" :use ((:instance f-f+ (x (f* b a)) (y s))
                        (:instance f-f* (x a) (y b))
                        (:instance f*comm (x a) (y b))))))

;;;=====================================================================
;;; Part 2 (V): Basic vector space algebra and coordinates
;;;=====================================================================

(defthm vs-v0-left
  (implies (vp x) (equal (v+ (v0) x) x))
  :hints (("Goal" :use ((:instance v+comm (x x) (y (v0)))))))

(defthm vs-inv-left
  (implies (vp x) (equal (v+ (v- x) x) (v0)))
  :hints (("Goal" :use ((:instance v+comm (x x) (y (v- x)))))))

(defthm vs-idem-zero
  (implies (and (vp y) (equal (v+ y y) y))
           (equal y (v0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance v+assoc (x y) (y y) (z (v- y)))))))

(defthm vs-v*-f0
  (implies (vp x) (equal (v* (f0) x) (v0)))
  :hints (("Goal" :use ((:instance vdistf (c (f0)) (d (f0)))
                        (:instance vs-idem-zero (y (v* (f0) x)))))))

(defthm vs-v*-v0
  (implies (fp c) (equal (v* c (v0)) (v0)))
  :hints (("Goal" :use ((:instance vdistv (x (v0)) (y (v0)))
                        (:instance vs-idem-zero (y (v* c (v0))))))))

(defthm vs-inv-unique
  (implies (and (vp x) (vp z) (equal (v+ x z) (v0)))
           (equal z (v- x)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance v+assoc (x (v- x)) (y x) (z z))))))

(defthm vs-v*-neg
  (implies (and (fp c) (vp x))
           (equal (v* (f- c) x) (v- (v* c x))))
  :hints (("Goal" :use ((:instance vdistf (d (f- c)))
                        (:instance vs-inv-unique (x (v* c x)) (z (v* (f- c) x)))))))

(defthmd vs-swap4
  (implies (and (vp a) (vp b) (vp c) (vp d))
           (equal (v+ (v+ a b) (v+ c d))
                  (v+ (v+ a c) (v+ b d))))
  :hints (("Goal" :use ((:instance v+assoc (x (v+ a b)) (y c) (z d))
                        (:instance v+assoc (x a) (y b) (z c))
                        (:instance v+assoc (x a) (y c) (z b))
                        (:instance v+comm (x b) (y c))
                        (:instance v+assoc (x (v+ a c)) (y b) (z d))))))

;; Linear combinations:

(defun vs-ind (l n)
  (if (zp n)
      l
    (vs-ind (cdr l) (1- n))))

(defun vs-ind2 (j l n)
  (if (zp n)
      (list j l)
    (vs-ind2 (1- j) (cdr l) (1- n))))

(defun vs-ind3 (a b l n)
  (if (zp n)
      (list a b l)
    (vs-ind3 (cdr a) (cdr b) (cdr l) (1- n))))

(defthm vs-vp-vcomb
  (implies (and (vlistnp l n) (flistnp d n))
           (vp (vcomb d l))))

(defthm vs-vcomb-flistn0
  (implies (vlistnp l n)
           (equal (vcomb (flistn0 n) l) (v0)))
  :hints (("Goal" :induct (vs-ind l n))))

(defthm vs-step-add
  (implies (and (fp a0) (fp b0) (vp x) (vp ra) (vp rb))
           (equal (v+ (v+ (v* a0 x) ra) (v+ (v* b0 x) rb))
                  (v+ (v* (f+ a0 b0) x) (v+ ra rb))))
  :hints (("Goal" :use ((:instance vdistf (c a0) (d b0))
                        (:instance vs-swap4 (a (v* a0 x)) (b ra) (c (v* b0 x)) (d rb))))))

(defthm vs-step-scalar
  (implies (and (fp c) (fp a0) (vp x) (vp r))
           (equal (v* c (v+ (v* a0 x) r))
                  (v+ (v* (f* c a0) x) (v* c r))))
  :hints (("Goal" :use ((:instance v*assoc (d a0))
                        (:instance vdistv (x (v* a0 x)) (y r))))))

(defthm vs-vcomb-flist-add
  (implies (and (vlistnp l n) (flistnp a n) (flistnp b n))
           (equal (vcomb (flist-add a b) l)
                  (v+ (vcomb a l) (vcomb b l))))
  :hints (("Goal" :induct (vs-ind3 a b l n))))

(defthm vs-vcomb-scalar-mul
  (implies (and (vlistnp l n) (flistnp a n) (fp c))
           (equal (vcomb (flist-scalar-mul c a) l)
                  (v* c (vcomb a l))))
  :hints (("Goal" :induct (vs-ind3 a a l n))))

(defthm vs-vp-nth
  (implies (and (vlistnp l n) (natp n) (natp j) (< j n))
           (vp (nth j l)))
  :hints (("Goal" :induct (vs-ind2 j l n))))

(defthm vs-vcomb-funit
  (implies (and (vlistnp l n) (natp n) (natp j) (< j n))
           (equal (vcomb (funit j n) l) (nth j l)))
  :hints (("Goal" :induct (vs-ind2 j l n))))

;; Coordinates relative to the canonical basis:

(defthm vs-vcoords0-vcomb
  (implies (flistnp c (vdim))
           (equal (vcoords0 (vcomb c (vbasis0))) c))
  :hints (("Goal" :use ((:instance fs-flist-neg-cancel (n (vdim))
                                   (e (vcoords0 (vcomb c (vbasis0)))))
                        (:instance vbasis0-lin-indep
                                   (c (flist-add (vcoords0 (vcomb c (vbasis0)))
                                                 (flist-scalar-mul (f- (f1)) c))))))))

(defthm vs-vcoords0-v0
  (equal (vcoords0 (v0)) (flistn0 (vdim)))
  :hints (("Goal" :use ((:instance vs-vcoords0-vcomb (c (flistn0 (vdim))))))))

(defthm vs-vcoords0-v+
  (implies (and (vp x) (vp y))
           (equal (vcoords0 (v+ x y))
                  (flist-add (vcoords0 x) (vcoords0 y))))
  :hints (("Goal" :use ((:instance vs-vcoords0-vcomb (c (flist-add (vcoords0 x) (vcoords0 y))))
                        (:instance vs-vcomb-flist-add (l (vbasis0)) (n (vdim))
                                   (a (vcoords0 x)) (b (vcoords0 y))))
                  :in-theory (disable vs-vcoords0-vcomb vs-vcomb-flist-add))))

(defthm vs-vcoords0-v*
  (implies (and (fp c) (vp x))
           (equal (vcoords0 (v* c x))
                  (flist-scalar-mul c (vcoords0 x))))
  :hints (("Goal" :use ((:instance vs-vcoords0-vcomb (c (flist-scalar-mul c (vcoords0 x))))
                        (:instance vs-vcomb-scalar-mul (l (vbasis0)) (n (vdim))
                                   (a (vcoords0 x))))
                  :in-theory (disable vs-vcoords0-vcomb vs-vcomb-scalar-mul))))

(defthm vs-vcoords0-inj
  (implies (and (vp x) (vp y) (equal (vcoords0 x) (vcoords0 y)))
           (equal x y))
  :rule-classes ()
  :hints (("Goal" :use ((:instance vbasis0-spans (x x))
                        (:instance vbasis0-spans (x y)))
                  :in-theory (disable vbasis0-spans))))

(defthm vs-vcoords0-zero
  (implies (and (vp x) (equal (vcoords0 x) (flistn0 (vdim))))
           (equal x (v0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance vs-vcoords0-inj (y (v0)))))))

(defthm vs-fmatp-vcoord-mat
  (implies (vlistnp l n)
           (fmatp (vcoord-mat l) n (vdim)))
  :hints (("Goal" :induct (vs-ind l n))))

(defthm vs-len-vcoord-mat
  (equal (len (vcoord-mat l)) (len l)))

(defthm vs-vcoords0-vcomb-gen
  (implies (and (vlistnp l n) (flistnp d n))
           (equal (vcoords0 (vcomb d l))
                  (fcomb d (vcoord-mat l) (vdim))))
  :hints (("Goal" :induct (vs-ind3 d d l n))))

(defthmd vs-vcomb-zero-iff
  (implies (and (vlistnp l n) (flistnp d n))
           (iff (equal (vcomb d l) (v0))
                (equal (fcomb d (vcoord-mat l) (vdim)) (flistn0 (vdim)))))
  :hints (("Goal" :use ((:instance vs-vcoords0-zero (x (vcomb d l)))
                        (:instance vs-vcoords0-vcomb-gen))
                  :in-theory (disable vcomb vs-vcoords0-vcomb-gen))))

(defthm vs-vlistnp-len
  (implies (and (vlistnp l n) (natp n))
           (equal (len l) n))
  :rule-classes ()
  :hints (("Goal" :induct (vs-ind l n))))

(defthm vs-vlistnp-true-listp
  (implies (vlistnp l n) (true-listp l))
  :rule-classes ()
  :hints (("Goal" :induct (vs-ind l n))))

(defthm vs-nth-basis
  (implies (and (natp j) (< j (vdim)))
           (and (vp (nth j (vbasis0)))
                (equal (vcoords0 (nth j (vbasis0))) (funit j (vdim)))))
  :hints (("Goal" :use ((:instance vs-vcomb-funit (l (vbasis0)) (n (vdim)))
                        (:instance vs-vcoords0-vcomb (c (funit j (vdim)))))
                  :in-theory (disable vs-vcomb-funit vs-vcoords0-vcomb))))

(defthmd vs-solve
  (implies (and (vp u) (vp w) (fp a) (not (equal a (f0)))
                (equal (v+ (v* a u) w) (v0)))
           (equal (v* (f- (f/ a)) w) u))
  :hints (("Goal" :use ((:instance vs-inv-unique (x (v* a u)) (z w))
                        (:instance v*assoc (c (f- (f/ a))) (d (f- a)) (x u))
                        (:instance fs-neg-neg (x (f/ a)) (y a))))))

(defthm vs-fcomb-vcoord-mat-basis
  (implies (flistnp c (vdim))
           (equal (fcomb c (vcoord-mat (vbasis0)) (vdim)) c))
  :hints (("Goal" :use ((:instance vs-vcoords0-vcomb)
                        (:instance vs-vcoords0-vcomb-gen (d c) (l (vbasis0)) (n (vdim))))
                  :in-theory (disable vs-vcoords0-vcomb vs-vcoords0-vcomb-gen))))

(defthm vs-fp-nth-vcoords0
  (implies (and (vp x) (natp i) (< i (vdim)))
           (fp (nth i (vcoords0 x))))
  :hints (("Goal" :use ((:instance fp-flistnp (x (vcoords0 x)) (n (vdim)))
                        (:instance posp-vdim)))))

(defthmd vs-dep-exists
  (implies (and (vlistnp l n) (posp n) (not (vindepp l)))
           (let ((d (nth (1- n) (row-reduce-mat (vcoord-mat l)))))
             (and (flistnp d n)
                  (not (equal d (flistn0 n)))
                  (equal (vcomb d l) (v0)))))
  :hints (("Goal" :use ((:instance rank-deficient-dep (a (vcoord-mat l)) (m n) (n (vdim)))
                        (:instance row-rank<=m (a (vcoord-mat l)) (m n) (n (vdim)))
                        (:instance vs-vcomb-zero-iff (d (nth (1- n) (row-reduce-mat (vcoord-mat l)))))
                        (:instance vs-vlistnp-len)
                        (:instance posp-vdim))
                  :in-theory (e/d (vindepp) (row-rank)))))

;;;=====================================================================
;;; Part 2 (V): Basic vector space algebra and coordinates
;;;=====================================================================

(defthm ws-v0-left
  (implies (wp x) (equal (w+ (w0) x) x))
  :hints (("Goal" :use ((:instance w+comm (x x) (y (w0)))))))

(defthm ws-inv-left
  (implies (wp x) (equal (w+ (w- x) x) (w0)))
  :hints (("Goal" :use ((:instance w+comm (x x) (y (w- x)))))))

(defthm ws-idem-zero
  (implies (and (wp y) (equal (w+ y y) y))
           (equal y (w0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance w+assoc (x y) (y y) (z (w- y)))))))

(defthm ws-v*-f0
  (implies (wp x) (equal (w* (f0) x) (w0)))
  :hints (("Goal" :use ((:instance wdistf (c (f0)) (d (f0)))
                        (:instance ws-idem-zero (y (w* (f0) x)))))))

(defthm ws-v*-v0
  (implies (fp c) (equal (w* c (w0)) (w0)))
  :hints (("Goal" :use ((:instance wdistw (x (w0)) (y (w0)))
                        (:instance ws-idem-zero (y (w* c (w0))))))))

(defthm ws-inv-unique
  (implies (and (wp x) (wp z) (equal (w+ x z) (w0)))
           (equal z (w- x)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance w+assoc (x (w- x)) (y x) (z z))))))

(defthm ws-v*-neg
  (implies (and (fp c) (wp x))
           (equal (w* (f- c) x) (w- (w* c x))))
  :hints (("Goal" :use ((:instance wdistf (d (f- c)))
                        (:instance ws-inv-unique (x (w* c x)) (z (w* (f- c) x)))))))

(defthmd ws-swap4
  (implies (and (wp a) (wp b) (wp c) (wp d))
           (equal (w+ (w+ a b) (w+ c d))
                  (w+ (w+ a c) (w+ b d))))
  :hints (("Goal" :use ((:instance w+assoc (x (w+ a b)) (y c) (z d))
                        (:instance w+assoc (x a) (y b) (z c))
                        (:instance w+assoc (x a) (y c) (z b))
                        (:instance w+comm (x b) (y c))
                        (:instance w+assoc (x (w+ a c)) (y b) (z d))))))

;; Linear combinations:

(defun ws-ind (l n)
  (if (zp n)
      l
    (ws-ind (cdr l) (1- n))))

(defun ws-ind2 (j l n)
  (if (zp n)
      (list j l)
    (ws-ind2 (1- j) (cdr l) (1- n))))

(defun ws-ind3 (a b l n)
  (if (zp n)
      (list a b l)
    (ws-ind3 (cdr a) (cdr b) (cdr l) (1- n))))

(defthm ws-vp-vcomb
  (implies (and (wlistnp l n) (flistnp d n))
           (wp (wcomb d l))))

(defthm ws-vcomb-flistn0
  (implies (wlistnp l n)
           (equal (wcomb (flistn0 n) l) (w0)))
  :hints (("Goal" :induct (ws-ind l n))))

(defthm ws-step-add
  (implies (and (fp a0) (fp b0) (wp x) (wp ra) (wp rb))
           (equal (w+ (w+ (w* a0 x) ra) (w+ (w* b0 x) rb))
                  (w+ (w* (f+ a0 b0) x) (w+ ra rb))))
  :hints (("Goal" :use ((:instance wdistf (c a0) (d b0))
                        (:instance ws-swap4 (a (w* a0 x)) (b ra) (c (w* b0 x)) (d rb))))))

(defthm ws-step-scalar
  (implies (and (fp c) (fp a0) (wp x) (wp r))
           (equal (w* c (w+ (w* a0 x) r))
                  (w+ (w* (f* c a0) x) (w* c r))))
  :hints (("Goal" :use ((:instance w*assoc (d a0))
                        (:instance wdistw (x (w* a0 x)) (y r))))))

(defthm ws-vcomb-flist-add
  (implies (and (wlistnp l n) (flistnp a n) (flistnp b n))
           (equal (wcomb (flist-add a b) l)
                  (w+ (wcomb a l) (wcomb b l))))
  :hints (("Goal" :induct (ws-ind3 a b l n))))

(defthm ws-vcomb-scalar-mul
  (implies (and (wlistnp l n) (flistnp a n) (fp c))
           (equal (wcomb (flist-scalar-mul c a) l)
                  (w* c (wcomb a l))))
  :hints (("Goal" :induct (ws-ind3 a a l n))))

(defthm ws-vp-nth
  (implies (and (wlistnp l n) (natp n) (natp j) (< j n))
           (wp (nth j l)))
  :hints (("Goal" :induct (ws-ind2 j l n))))

(defthm ws-vcomb-funit
  (implies (and (wlistnp l n) (natp n) (natp j) (< j n))
           (equal (wcomb (funit j n) l) (nth j l)))
  :hints (("Goal" :induct (ws-ind2 j l n))))

;; Coordinates relative to the canonical basis:

(defthm ws-vcoords0-vcomb
  (implies (flistnp c (wdim))
           (equal (wcoords0 (wcomb c (wbasis0))) c))
  :hints (("Goal" :use ((:instance fs-flist-neg-cancel (n (wdim))
                                   (e (wcoords0 (wcomb c (wbasis0)))))
                        (:instance wbasis0-lin-indep
                                   (c (flist-add (wcoords0 (wcomb c (wbasis0)))
                                                 (flist-scalar-mul (f- (f1)) c))))))))

(defthm ws-vcoords0-v0
  (equal (wcoords0 (w0)) (flistn0 (wdim)))
  :hints (("Goal" :use ((:instance ws-vcoords0-vcomb (c (flistn0 (wdim))))))))

(defthm ws-vcoords0-v+
  (implies (and (wp x) (wp y))
           (equal (wcoords0 (w+ x y))
                  (flist-add (wcoords0 x) (wcoords0 y))))
  :hints (("Goal" :use ((:instance ws-vcoords0-vcomb (c (flist-add (wcoords0 x) (wcoords0 y))))
                        (:instance ws-vcomb-flist-add (l (wbasis0)) (n (wdim))
                                   (a (wcoords0 x)) (b (wcoords0 y))))
                  :in-theory (disable ws-vcoords0-vcomb ws-vcomb-flist-add))))

(defthm ws-vcoords0-v*
  (implies (and (fp c) (wp x))
           (equal (wcoords0 (w* c x))
                  (flist-scalar-mul c (wcoords0 x))))
  :hints (("Goal" :use ((:instance ws-vcoords0-vcomb (c (flist-scalar-mul c (wcoords0 x))))
                        (:instance ws-vcomb-scalar-mul (l (wbasis0)) (n (wdim))
                                   (a (wcoords0 x))))
                  :in-theory (disable ws-vcoords0-vcomb ws-vcomb-scalar-mul))))

(defthm ws-vcoords0-inj
  (implies (and (wp x) (wp y) (equal (wcoords0 x) (wcoords0 y)))
           (equal x y))
  :rule-classes ()
  :hints (("Goal" :use ((:instance wbasis0-spans (x x))
                        (:instance wbasis0-spans (x y)))
                  :in-theory (disable wbasis0-spans))))

(defthm ws-vcoords0-zero
  (implies (and (wp x) (equal (wcoords0 x) (flistn0 (wdim))))
           (equal x (w0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance ws-vcoords0-inj (y (w0)))))))

(defthm ws-fmatp-vcoord-mat
  (implies (wlistnp l n)
           (fmatp (wcoord-mat l) n (wdim)))
  :hints (("Goal" :induct (ws-ind l n))))

(defthm ws-len-vcoord-mat
  (equal (len (wcoord-mat l)) (len l)))

(defthm ws-vcoords0-vcomb-gen
  (implies (and (wlistnp l n) (flistnp d n))
           (equal (wcoords0 (wcomb d l))
                  (fcomb d (wcoord-mat l) (wdim))))
  :hints (("Goal" :induct (ws-ind3 d d l n))))

(defthmd ws-vcomb-zero-iff
  (implies (and (wlistnp l n) (flistnp d n))
           (iff (equal (wcomb d l) (w0))
                (equal (fcomb d (wcoord-mat l) (wdim)) (flistn0 (wdim)))))
  :hints (("Goal" :use ((:instance ws-vcoords0-zero (x (wcomb d l)))
                        (:instance ws-vcoords0-vcomb-gen))
                  :in-theory (disable wcomb ws-vcoords0-vcomb-gen))))

(defthm ws-vlistnp-len
  (implies (and (wlistnp l n) (natp n))
           (equal (len l) n))
  :rule-classes ()
  :hints (("Goal" :induct (ws-ind l n))))

(defthm ws-vlistnp-true-listp
  (implies (wlistnp l n) (true-listp l))
  :rule-classes ()
  :hints (("Goal" :induct (ws-ind l n))))

(defthm ws-nth-basis
  (implies (and (natp j) (< j (wdim)))
           (and (wp (nth j (wbasis0)))
                (equal (wcoords0 (nth j (wbasis0))) (funit j (wdim)))))
  :hints (("Goal" :use ((:instance ws-vcomb-funit (l (wbasis0)) (n (wdim)))
                        (:instance ws-vcoords0-vcomb (c (funit j (wdim)))))
                  :in-theory (disable ws-vcomb-funit ws-vcoords0-vcomb))))

(defthmd ws-solve
  (implies (and (wp u) (wp w) (fp a) (not (equal a (f0)))
                (equal (w+ (w* a u) w) (w0)))
           (equal (w* (f- (f/ a)) w) u))
  :hints (("Goal" :use ((:instance ws-inv-unique (x (w* a u)) (z w))
                        (:instance w*assoc (c (f- (f/ a))) (d (f- a)) (x u))
                        (:instance fs-neg-neg (x (f/ a)) (y a))))))

(defthm ws-fcomb-vcoord-mat-basis
  (implies (flistnp c (wdim))
           (equal (fcomb c (wcoord-mat (wbasis0)) (wdim)) c))
  :hints (("Goal" :use ((:instance ws-vcoords0-vcomb)
                        (:instance ws-vcoords0-vcomb-gen (d c) (l (wbasis0)) (n (wdim))))
                  :in-theory (disable ws-vcoords0-vcomb ws-vcoords0-vcomb-gen))))

(defthm ws-fp-nth-vcoords0
  (implies (and (wp x) (natp i) (< i (wdim)))
           (fp (nth i (wcoords0 x))))
  :hints (("Goal" :use ((:instance fp-flistnp (x (wcoords0 x)) (n (wdim)))
                        (:instance posp-wdim)))))

(defthmd ws-dep-exists
  (implies (and (wlistnp l n) (posp n) (not (windepp l)))
           (let ((d (nth (1- n) (row-reduce-mat (wcoord-mat l)))))
             (and (flistnp d n)
                  (not (equal d (flistn0 n)))
                  (equal (wcomb d l) (w0)))))
  :hints (("Goal" :use ((:instance rank-deficient-dep (a (wcoord-mat l)) (m n) (n (wdim)))
                        (:instance row-rank<=m (a (wcoord-mat l)) (m n) (n (wdim)))
                        (:instance ws-vcomb-zero-iff (d (nth (1- n) (row-reduce-mat (wcoord-mat l)))))
                        (:instance ws-vlistnp-len)
                        (:instance posp-wdim))
                  :in-theory (e/d (windepp) (row-rank)))))

;;;=====================================================================
;;; Part 3: Independence, dependence coefficients, vcoords, MAIN-3
;;;=====================================================================

(defthm vindepp-indep
  (implies (and (vlistnp l n) (vindepp l) (flistnp d n) (equal (vcomb d l) (v0)))
           (equal d (flistn0 n)))
  :rule-classes ()
  :hints (("Goal" :cases ((zp n)))
          ("Subgoal 2" :use ((:instance full-rank-indep (a (vcoord-mat l)) (m n) (n (vdim)))
                             (:instance vs-vcomb-zero-iff)
                             (:instance vs-vlistnp-len)
                             (:instance posp-vdim))
                       :in-theory (enable vindepp))))

(defthmd vdep-coeffs-dep
  (implies (and (vlistnp l n) (posp n) (not (vindepp l)))
           (let ((d (vdep-coeffs l)))
             (and (flistnp d n)
                  (not (equal d (flistn0 n)))
                  (equal (vcomb d l) (v0)))))
  :hints (("Goal" :use ((:instance rank-deficient-dep (a (vcoord-mat l)) (m n) (n (vdim)))
                        (:instance row-rank<=m (a (vcoord-mat l)) (m n) (n (vdim)))
                        (:instance vs-vcomb-zero-iff (d (vdep-coeffs l)))
                        (:instance vs-vlistnp-len)
                        (:instance posp-vdim))
                  :in-theory (e/d (vindepp) (row-rank)))))

(defthm vcoords-spans
  (implies (and (vlistnp l n) (posp n) (vindepp l) (vp x) (not (vindepp (cons x l))))
           (and (flistnp (vcoords x l) n)
                (equal (vcomb (vcoords x l) l) x)))
  :hints (("Goal" :use ((:instance vdep-coeffs-dep (l (cons x l)) (n (1+ n)))
                        (:instance vindepp-indep (d (cdr (vdep-coeffs (cons x l)))))
                        (:instance vs-solve (u x) (a (car (vdep-coeffs (cons x l))))
                                   (w (vcomb (cdr (vdep-coeffs (cons x l))) l))))
                  :cases ((equal (car (vdep-coeffs (cons x l))) (f0)))
                  :in-theory (e/d (vcoords) (vdep-coeffs)))))

;; A non-lead index exists when the rank is less than the number of columns:

(defthm sublistp-set-difference-nil
  (implies (not (consp (set-difference-equal l m)))
           (sublistp l m)))

(defthm member-car-consp
  (implies (consp x) (member (car x) x)))

(defthmd consp-free-inds
  (implies (and (fmatp a m n) (posp m) (posp n) (< (row-rank a) n))
           (consp (free-inds (row-reduce a) n)))
  :hints (("Goal" :use ((:instance sublistp-<=-len (l (ninit n)) (m (lead-inds (row-reduce a))))
                        (:instance sublistp-set-difference-nil (l (ninit n)) (m (lead-inds (row-reduce a))))
                        (:instance len-lead-inds-num-nonzero-rows (a (row-reduce a))))
                  :in-theory (enable free-inds))))

(defthmd free-ind-exists
  (implies (and (fmatp a m n) (posp m) (posp n) (< (row-rank a) n))
           (let ((j (car (free-inds (row-reduce a) n))))
             (and (natp j) (< j n)
                  (not (member j (lead-inds (row-reduce a)))))))
  :hints (("Goal" :use ((:instance consp-free-inds)
                        (:instance fmatp-row-reduce)
                        (:instance row-echelon-p-row-reduce)
                        (:instance member-free-inds (a (row-reduce a)) (x (car (free-inds (row-reduce a) n))))
                        (:instance member-ninit (x (car (free-inds (row-reduce a) n)))))
                  :in-theory (disable row-rank))))

(defthmd vunspanned-props
  (implies (and (vlistnp l m) (posp m) (vindepp l) (< m (vdim)))
           (let ((u (vunspanned l)))
             (and (vp u) (vindepp (cons u l)))))
  :hints (("Goal" :use ((:instance free-ind-exists (a (vcoord-mat l)) (n (vdim)))
                        (:instance vs-nth-basis (j (car (free-inds (row-reduce (vcoord-mat l)) (vdim)))))
                        (:instance vcoords-spans (x (vunspanned l)) (n m))
                        (:instance vs-vcoords0-vcomb-gen (d (vcoords (vunspanned l) l)) (n m))
                        (:instance not-in-row-space (a (vcoord-mat l)) (n (vdim))
                                   (j (car (free-inds (row-reduce (vcoord-mat l)) (vdim))))
                                   (c (vcoords (vunspanned l) l)))
                        (:instance vs-vlistnp-len (n m))
                        (:instance posp-vdim))
                  :in-theory (e/d (vindepp vunspanned) (row-rank vs-nth-basis vcoords-spans vs-vcoords0-vcomb-gen)))))

(defthm ext-step
  (implies (and (vlistnp l (len l)) (consp l) (vindepp l) (< (len l) (vdim)))
           (and (vp (vunspanned l))
                (vindepp (cons (vunspanned l) l))))
  :hints (("Goal" :use ((:instance vunspanned-props (m (len l)))))))

(defthm ext-base
  (implies (and (vlistnp l (len l)) (consp l) (vindepp l) (not (< (len l) (vdim))))
           (vbasisp l))
  :hints (("Goal" :use ((:instance row-rank<=n (a (vcoord-mat l)) (m (len l)) (n (vdim)))
                        (:instance posp-vdim))
                  :in-theory (e/d (vindepp vbasisp) (row-rank)))))

(defthm extend-to-basis-basisp
  (implies (and (vlistnp l (len l)) (consp l) (vindepp l))
           (vbasisp (extend-to-basis l)))
  :hints (("Goal" :induct (extend-to-basis l))))

(defthm main-3
  (implies (and (vlistnp l n) (posp n) (vindepp l))
           (vbasisp (extend-to-basis l)))
  :hints (("Goal" :use ((:instance vs-vlistnp-len)
                        (:instance extend-to-basis-basisp)))))

;;;=====================================================================
;;; Part 4: Linear transformation, MAIN-1, MAIN-2
;;;=====================================================================

(defthm wlistnp-lin-list
  (implies (vlistnp l n) (wlistnp (lin-list l) n))
  :hints (("Goal" :induct (vs-ind l n))))

(defthm len-lin-list
  (equal (len (lin-list l)) (len l)))

(defthm lin-vcomb
  (implies (and (vlistnp l n) (flistnp d n))
           (equal (lin (vcomb d l)) (wcomb d (lin-list l))))
  :hints (("Goal" :induct (vs-ind3 d d l n))))

(defthm fmatp-lin-mat
  (fmatp (lin-mat) (vdim) (wdim))
  :hints (("Goal" :in-theory (enable lin-mat))))

(defthm wcoords0-lin-vcomb
  (implies (and (vlistnp l n) (flistnp d n))
           (equal (wcoords0 (lin (vcomb d l)))
                  (fcomb d (wcoord-mat (lin-list l)) (wdim))))
  :hints (("Goal" :use ((:instance ws-vcoords0-vcomb-gen (l (lin-list l))))
                  :in-theory (disable ws-vcoords0-vcomb-gen))))

(defthmd wcoords0-lin
  (implies (vp x)
           (equal (wcoords0 (lin x))
                  (fcomb (vcoords0 x) (lin-mat) (wdim))))
  :hints (("Goal" :use ((:instance wcoords0-lin-vcomb (l (vbasis0)) (n (vdim)) (d (vcoords0 x))))
                  :in-theory (e/d (lin-mat) (wcoords0-lin-vcomb lin-vcomb)))))

(defthmd wcoords0-lin-basis
  (implies (flistnp c (vdim))
           (equal (wcoords0 (lin (vcomb c (vbasis0))))
                  (fcomb c (lin-mat) (wdim))))
  :hints (("Goal" :use ((:instance wcoords0-lin-vcomb (l (vbasis0)) (n (vdim)) (d c)))
                  :in-theory (e/d (lin-mat) (wcoords0-lin-vcomb lin-vcomb vcomb)))))

(defthmd injective-rank
  (implies (lin-injective-p)
           (equal (row-rank (lin-mat)) (vdim)))
  :hints (("Goal" :use ((:instance row-rank<=m (a (lin-mat)) (m (vdim)) (n (wdim)))
                        (:instance rank-deficient-dep (a (lin-mat)) (m (vdim)) (n (wdim)))
                        (:instance wcoords0-lin-basis
                                   (c (nth (1- (vdim)) (row-reduce-mat (lin-mat)))))
                        (:instance ws-vcoords0-zero
                                   (x (lin (vcomb (nth (1- (vdim)) (row-reduce-mat (lin-mat))) (vbasis0)))))
                        (:instance lin-injective-p-necc
                                   (x (vcomb (nth (1- (vdim)) (row-reduce-mat (lin-mat))) (vbasis0))))
                        (:instance vs-vcoords0-vcomb (c (nth (1- (vdim)) (row-reduce-mat (lin-mat)))))
                        (:instance posp-vdim)
                        (:instance posp-wdim))
                  :in-theory (disable row-rank lin-vcomb wcoords0-lin-vcomb vs-vcoords0-vcomb))))

(defthmd injective-dims
  (implies (lin-injective-p)
           (<= (vdim) (wdim)))
  :hints (("Goal" :use ((:instance injective-rank)
                        (:instance row-rank<=n (a (lin-mat)) (m (vdim)) (n (wdim)))
                        (:instance posp-vdim)
                        (:instance posp-wdim))
                  :in-theory (disable row-rank))))

(defthmd surjective-dims
  (implies (and (lin-injective-p) (lin-surjective-p))
           (equal (vdim) (wdim)))
  :hints (("Goal" :cases ((< (vdim) (wdim))))
          ("Subgoal 1"
           :use ((:instance injective-rank)
                 (:instance free-ind-exists (a (lin-mat)) (m (vdim)) (n (wdim)))
                 (:instance ws-nth-basis (j (car (free-inds (row-reduce (lin-mat)) (wdim)))))
                 (:instance lin-surjective-p-necc
                            (y (nth (car (free-inds (row-reduce (lin-mat)) (wdim))) (wbasis0))))
                 (:instance wcoords0-lin
                            (x (lin-preimage (nth (car (free-inds (row-reduce (lin-mat)) (wdim))) (wbasis0)))))
                 (:instance not-in-row-space (a (lin-mat)) (m (vdim)) (n (wdim))
                            (j (car (free-inds (row-reduce (lin-mat)) (wdim))))
                            (c (vcoords0 (lin-preimage (nth (car (free-inds (row-reduce (lin-mat)) (wdim)))
                                                            (wbasis0))))))
                 (:instance posp-vdim)
                 (:instance posp-wdim))
           :in-theory (disable row-rank ws-nth-basis))
          ("Subgoal 2" :use ((:instance injective-dims)))))

(defthmd sq-1
  (implies (equal (vdim) (wdim))
           (fmatp (lin-mat) (vdim) (vdim)))
  :hints (("Goal" :use fmatp-lin-mat :in-theory (disable fmatp-lin-mat))))

(defthmd sq-2
  (implies (and (equal (vdim) (wdim)) (wp y))
           (flistnp (wcoords0 y) (vdim)))
  :hints (("Goal" :use ((:instance flistnp-wcoords0 (x y))) :in-theory (disable flistnp-wcoords0))))

(defthmd sq-3
  (implies (equal (vdim) (wdim))
           (equal (fcomb c a (wdim)) (fcomb c a (vdim)))))

(defthmd lin-inv-rewrite
  (implies (and (lin-injective-p) (equal (vdim) (wdim)) (wp y))
           (equal (lin-inv y)
                  (vcomb (fcomb (wcoords0 y) (inverse-mat (lin-mat)) (vdim)) (vbasis0))))
  :hints (("Goal" :use ((:instance injective-rank)
                        (:instance invertiblep-sufficient (a (lin-mat)) (n (vdim)))
                        (:instance fmat*-row-mat (a (inverse-mat (lin-mat))) (m (vdim)) (n (vdim))
                                   (d (wcoords0 y)))
                        (:instance sq-1) (:instance sq-2)
                        (:instance posp-vdim))
                  :in-theory (e/d (lin-inv invertiblep) (row-rank)))))

(defthmd lin-inv-coords
  (implies (and (lin-injective-p) (equal (vdim) (wdim)) (wp y))
           (equal (fcomb (fcomb (wcoords0 y) (inverse-mat (lin-mat)) (vdim)) (lin-mat) (vdim))
                  (wcoords0 y)))
  :hints (("Goal" :use ((:instance injective-rank)
                        (:instance invertiblep-sufficient (a (lin-mat)) (n (vdim)))
                        (:instance fcomb-fmat* (d (wcoords0 y)) (a (inverse-mat (lin-mat)))
                                   (b (lin-mat)) (m (vdim)) (k (vdim)) (n (vdim)))
                        (:instance fcomb-id-fmat (d (wcoords0 y)) (m (vdim)))
                        (:instance sq-1) (:instance sq-2)
                        (:instance posp-vdim))
                  :in-theory (e/d (invertiblep) (row-rank)))))

(defthmd lin-inv-works
  (implies (and (lin-injective-p) (equal (vdim) (wdim)) (wp y))
           (and (vp (lin-inv y))
                (equal (lin (lin-inv y)) y)))
  :hints (("Goal" :use ((:instance lin-inv-rewrite)
                        (:instance lin-inv-coords)
                        (:instance injective-rank)
                        (:instance invertiblep-sufficient (a (lin-mat)) (n (vdim)))
                        (:instance wcoords0-lin-basis
                                   (c (fcomb (wcoords0 y) (inverse-mat (lin-mat)) (vdim))))
                        (:instance ws-vcoords0-inj (x (lin (lin-inv y))))
                        (:instance sq-1) (:instance sq-2)
                        (:instance sq-3 (c (fcomb (wcoords0 y) (inverse-mat (lin-mat)) (vdim))) (a (lin-mat)))
                        (:instance flistnp-fcomb (d (wcoords0 y)) (a (inverse-mat (lin-mat)))
                                   (m (vdim)) (n (vdim)))
                        (:instance vs-vp-vcomb (d (fcomb (wcoords0 y) (inverse-mat (lin-mat)) (vdim)))
                                   (l (vbasis0)) (n (vdim)))
                        (:instance posp-vdim))
                  :in-theory (e/d (invertiblep)
                                  (row-rank lin-vcomb wcoords0-lin-vcomb vs-vcoords0-vcomb lin-inv
                                            vs-vp-vcomb flistnp-fcomb fcomb)))))

(defthmd equal-dims-surjective
  (implies (and (lin-injective-p) (equal (vdim) (wdim)))
           (lin-surjective-p))
  :hints (("Goal" :use ((:instance lin-inv-works (y (lin-surjective-p-witness)))
                        (:instance lin-preimage (y (lin-surjective-p-witness))
                                   (x (lin-inv (lin-surjective-p-witness)))))
                  :in-theory (enable lin-surjective-p))))

(defthm main-1
  (and (implies (lin-injective-p)
                (<= (vdim) (wdim)))
       (implies (lin-injective-p)
                (iff (lin-surjective-p)
                     (equal (vdim) (wdim)))))
  :hints (("Goal" :use ((:instance injective-dims)
                        (:instance surjective-dims)
                        (:instance equal-dims-surjective)))))

(defthm main-2
  (implies (and (lin-injective-p)
                (lin-surjective-p)
                (wp y))
           (let ((x (lin-inv y)))
             (and (vp x)
                  (equal (lin x) y))))
  :hints (("Goal" :use ((:instance surjective-dims)
                        (:instance lin-inv-works)))))

;;;=====================================================================
;;; Part 5: Subspace dimension, MAIN-4
;;;=====================================================================

(defthm slistnp-vlistnp
  (implies (slistnp l n) (vlistnp l n)))

(defthm slistnp-len
  (implies (and (slistnp l n) (natp n))
           (equal (len l) n))
  :rule-classes ())

(defthm sbasis0-aux-props
  (implies (and (slistnp l (len l)) (vindepp l))
           (let ((r (sbasis0-aux l)))
             (and (slistnp r (len r))
                  (vindepp r)
                  (not (and (sp (sunspanned r))
                            (vindepp (cons (sunspanned r) r)))))))
  :hints (("Goal" :induct (sbasis0-aux l))))

(defthm sbasis0-props
  (and (slistnp (sbasis0) (sdim))
       (vindepp (sbasis0)))
  :hints (("Goal" :use ((:instance sbasis0-aux-props (l nil)))
                  :in-theory (enable sbasis0 vindepp))))

(defthmd sbasis0-maximal
  (implies (sp x)
           (not (vindepp (cons x (sbasis0)))))
  :hints (("Goal" :use ((:instance sbasis0-aux-props (l nil))
                        (:instance sunspanned (l (sbasis0))))
                  :in-theory (enable sbasis0 vindepp))))

(in-theory (disable sdim sdim1 (sdim1)))

;; Linear combinations of a list, one for each row of a coefficient matrix:

(defun vcomb-list (c l)
  (if (consp c)
      (cons (vcomb (car c) l)
            (vcomb-list (cdr c) l))
    ()))

(defthm vlistnp-vcomb-list
  (implies (and (fmatp c m k) (vlistnp l k))
           (vlistnp (vcomb-list c l) m)))

(defthm fmat*-nil
  (equal (fmat* nil b) nil)
  :hints (("Goal" :expand ((fmat* nil b)))))

(defthm fmat*-cons
  (equal (fmat* (cons r c) b)
         (cons (fdot-list r (transpose-mat b)) (fmat* c b)))
  :hints (("Goal" :expand ((fmat* (cons r c) b)))))

(defthm fdot-list-transpose-vcoord-mat
  (implies (and (vlistnp l k) (posp k) (flistnp d k))
           (equal (fdot-list d (transpose-mat (vcoord-mat l)))
                  (fcomb d (vcoord-mat l) (vdim))))
  :hints (("Goal" :use ((:instance posp-vdim)
                        (:instance fdot-list-transpose-fcomb (a (vcoord-mat l)) (m k)
                                   (n (vdim)))))))

(defthm vcoord-mat-vcomb-list
  (implies (and (fmatp c m k) (vlistnp l k) (posp k))
           (equal (vcoord-mat (vcomb-list c l))
                  (fmat* c (vcoord-mat l))))
  :hints (("Goal" :induct (fmatp c m k)
                  :expand ((fmat* c (vcoord-mat l))))))

(defthmd span-dim-bound
  (implies (and (vlistnp l k) (posp k) (fmatp c m k) (posp m)
                (vindepp (vcomb-list c l)))
           (<= m k))
  :hints (("Goal" :use ((:instance row-rank<=n (a c) (m m) (n k))
                        (:instance rank-deficient-dep (a c) (m m) (n k))
                        (:instance vs-vcomb-zero-iff (l (vcomb-list c l)) (n m)
                                   (d (nth (1- m) (row-reduce-mat c))))
                        (:instance fcomb-fmat* (d (nth (1- m) (row-reduce-mat c)))
                                   (a c) (b (vcoord-mat l)) (k k) (n (vdim)))
                        (:instance vindepp-indep (l (vcomb-list c l)) (n m)
                                   (d (nth (1- m) (row-reduce-mat c))))
                        (:instance posp-vdim))
                  :in-theory (disable row-rank))))

(defthm not-vindepp-cons-v0
  (implies (vlistnp l n)
           (not (vindepp (cons (v0) l))))
  :hints (("Goal" :use ((:instance vindepp-indep (l (cons (v0) l)) (n (1+ (nfix n)))
                                   (d (cons (f1) (flistn0 (nfix n)))))))))

(defthm flistnp-1-form
  (implies (flistnp d 1) (equal (list (car d)) d))
  :rule-classes ())

(defthmd vindepp-car
  (implies (and (vlistnp (cons x l) n) (vindepp (cons x l)))
           (vindepp (list x)))
  :hints (("Goal" :use ((:instance vdep-coeffs-dep (l (list x)) (n 1))
                        (:instance vindepp-indep (l (cons x l))
                                   (d (cons (car (vdep-coeffs (list x))) (flistn0 (1- n)))))
                        (:instance flistnp-1-form (d (vdep-coeffs (list x)))))
                  :in-theory (disable vdep-coeffs))))

;; Coefficient matrices:

(defun scoords1-list (l)
  (if (consp l)
      (cons (scoords1 (car l)) (scoords1-list (cdr l)))
    ()))

(defthm scoords1-list-props
  (implies (and (slistnp l n) (posp (sdim)))
           (and (fmatp (scoords1-list l) n (sdim1))
                (equal (vcomb-list (scoords1-list l) (sbasis1)) l)))
  :hints (("Goal" :in-theory (enable flistnp-scoords1 sbasis1-spans))))

(defun vcoords-list (l b)
  (if (consp l)
      (cons (vcoords (car l) b) (vcoords-list (cdr l) b))
    ()))

(defthm sbasis0-coords
  (implies (and (sp x) (posp (sdim)))
           (and (flistnp (vcoords x (sbasis0)) (sdim))
                (equal (vcomb (vcoords x (sbasis0)) (sbasis0)) x)))
  :hints (("Goal" :use ((:instance vcoords-spans (l (sbasis0)) (n (sdim)))
                        (:instance sbasis0-maximal)
                        (:instance sbasis0-props))
                  :in-theory (disable vcoords-spans sbasis0-props))))

(defthm vcoords-list-props
  (implies (and (slistnp l n) (posp (sdim)))
           (and (fmatp (vcoords-list l (sbasis0)) n (sdim))
                (equal (vcomb-list (vcoords-list l (sbasis0)) (sbasis0)) l))))

(defthm sdim1-<=-sdim
  (<= (sdim1) (sdim))
  :rule-classes ()
  :hints (("Goal" :cases ((posp (sdim))))
          ("Subgoal 2" :use ((:instance slistnp-sbasis1)
                             (:instance vindepp-sbasis1)
                             (:instance vindepp-car (x (car (sbasis1))) (l (cdr (sbasis1))) (n (sdim1)))
                             (:instance sbasis0-maximal (x (car (sbasis1))))
                             (:instance sbasis0-props)
                             (:instance slistnp-len (l (sbasis0)) (n (sdim))))
                       :in-theory (disable sbasis0-props sdim))
          ("Subgoal 1" :use ((:instance slistnp-sbasis1)
                             (:instance vindepp-sbasis1)
                             (:instance sbasis0-props)
                             (:instance vcoords-list-props (l (sbasis1)) (n (sdim1)))
                             (:instance span-dim-bound (l (sbasis0)) (k (sdim))
                                        (c (vcoords-list (sbasis1) (sbasis0))) (m (sdim1))))
                       :in-theory (disable sbasis0-props vcoords-list-props sdim))))

(defthm sdim-<=-sdim1
  (<= (sdim) (sdim1))
  :rule-classes ()
  :hints (("Goal" :cases ((posp (sdim1))))
          ("Subgoal 2" :use ((:instance slistnp-sbasis1)
                             (:instance sbasis0-props)
                             (:instance sbasis1-spans (x (car (sbasis0))))
                             (:instance flistnp-scoords1 (x (car (sbasis0))))
                             (:instance not-vindepp-cons-v0 (l (cdr (sbasis0))) (n (1- (sdim)))))
                       :in-theory (disable sbasis0-props sdim))
          ("Subgoal 1" :use ((:instance slistnp-sbasis1)
                             (:instance sbasis0-props)
                             (:instance scoords1-list-props (l (sbasis0)) (n (sdim)))
                             (:instance span-dim-bound (l (sbasis1)) (k (sdim1))
                                        (c (scoords1-list (sbasis0))) (m (sdim))))
                       :in-theory (disable sbasis0-props scoords1-list-props sdim))))

(defthm main-4
  (= (sdim1) (sdim))
  :hints (("Goal" :use ((:instance sdim1-<=-sdim)
                        (:instance sdim-<=-sdim1)))))

;;;=====================================================================
;;; Part 6: Kernel, MAIN-5
;;;=====================================================================

(defmacro kR () '(row-reduce (transpose-mat (lin-mat))))
(defmacro kP () '(row-reduce-mat (transpose-mat (lin-mat))))
(defmacro kL () '(lead-inds (row-reduce (transpose-mat (lin-mat)))))
(defmacro kF () '(free-inds (row-reduce (transpose-mat (lin-mat))) (vdim)))
(defmacro kr# () '(num-nonzero-rows (row-reduce (transpose-mat (lin-mat)))))

(defthm fdot-step
  (implies (and (fp q0) (flistnp y0 n) (flistnp r n) (flistnp c n))
           (equal (fdot (flist-add (flist-scalar-mul q0 y0) r) c)
                  (f+ (f* q0 (fdot c y0)) (fdot r c))))
  :hints (("Goal" :use ((:instance fdot-flist-add (x (flist-scalar-mul q0 y0)) (y r) (z c))
                        (:instance fdot-flist-scalar-mul (c q0) (x y0) (y c))
                        (:instance fdot-comm (x c) (y y0))))))

(defthm fdot-fcomb
  (implies (and (flistnp q p) (fmatp y p n) (flistnp c n) (natp n))
           (equal (fdot (fcomb q y n) c)
                  (fdot q (fdot-list c y)))))

(defthm nth-fdot-list-fmat*
  (implies (and (fmatp x p p) (fmatp y p n) (posp p) (posp n) (flistnp c n)
                (natp s) (< s p))
           (equal (nth s (fdot-list c (fmat* x y)))
                  (fdot (nth s x) (fdot-list c y))))
  :hints (("Goal" :use ((:instance nth-fmat*-fcomb (a x) (b y) (m p) (k p) (i s))
                        (:instance fdot-comm (x c) (y (fcomb (nth s x) y n)))
                        (:instance flistnp-row (a x) (m p) (n p) (i s))
                        (:instance fmatp-fmat* (a x) (b y) (m p) (n p) (p n))
                        (:instance len-fmatp (a (fmat* x y)) (m p) (n n))
                        (:instance nth-fdot-list (j s) (x c) (l (fmat* x y))))
                  :in-theory (disable flistnp-row fmatp-fmat* len-fmatp nth-fdot-list fdot-list fdot fcomb))))

(defthmd fdot-list-fmat*-zero
  (implies (and (fmatp x p p) (fmatp y p n) (posp p) (posp n) (flistnp c n)
                (equal (fdot-list c y) (flistn0 p)))
           (equal (fdot-list c (fmat* x y)) (flistn0 p)))
  :hints (("Goal" :use ((:instance flistnp-nth-diff (x (fdot-list c (fmat* x y))) (y (flistn0 p)) (n p))
                        (:instance flistnp-row (a x) (m p) (n p) (i (nth-diff (fdot-list c (fmat* x y)) (flistn0 p))))
                        (:instance fdot-comm (x (nth (nth-diff (fdot-list c (fmat* x y)) (flistn0 p)) x))
                                   (y (flistn0 p)) (n p))
                        (:instance fmatp-fmat* (a x) (b y) (m p) (n p) (p n))
                        (:instance flistnp-fdot-list (l (fmat* x y)) (m p) (n n) (x c))
                        (:instance nth-fdot-list-fmat* (s (nth-diff (fdot-list c (fmat* x y)) (flistn0 p)))))
                  :in-theory (disable flistnp-row fmatp-fmat* flistnp-fdot-list nth-fdot-list-fmat*
                                      fdot-list fmat* fdot))))

(defthm fmatp-kat
  (and (fmatp (transpose-mat (lin-mat)) (wdim) (vdim))
       (fmatp (kR) (wdim) (vdim))
       (row-echelon-p (kR)))
  :hints (("Goal" :use ((:instance fmatp-transpose (a (lin-mat)) (m (vdim)) (n (wdim)))
                        (:instance fmatp-row-reduce (a (transpose-mat (lin-mat))) (m (wdim)) (n (vdim)))
                        (:instance row-echelon-p-row-reduce (a (transpose-mat (lin-mat))) (m (wdim)) (n (vdim)))
                        (:instance posp-vdim) (:instance posp-wdim)))))

(defthmd kernel-coords-iff
  (implies (flistnp c (vdim))
           (iff (equal (fcomb c (lin-mat) (wdim)) (flistn0 (wdim)))
                (equal (fdot-list c (kR)) (flistn0 (wdim)))))
  :hints (("Goal" :use ((:instance fdot-list-transpose-fcomb (a (lin-mat)) (m (vdim)) (n (wdim)) (d c))
                        (:instance row-ops-mat-row-reduce (a (transpose-mat (lin-mat))) (m (wdim)) (n (vdim)))
                        (:instance row-reduce-factor (a (transpose-mat (lin-mat))) (m (wdim)) (n (vdim)))
                        (:instance fmatp-row-reduce-mat (a (transpose-mat (lin-mat))) (m (wdim)) (n (vdim)))
                        (:instance fdot-list-fmat*-zero (x (kP)) (y (transpose-mat (lin-mat)))
                                   (p (wdim)) (n (vdim)))
                        (:instance fdot-list-fmat*-zero (x (inverse-mat (kP))) (y (kR))
                                   (p (wdim)) (n (vdim)))
                        (:instance fmatp-kat)
                        (:instance posp-vdim) (:instance posp-wdim))
                  :in-theory (disable fmatp-kat fcomb fdot-list))))

;; Splitting a row of a reduced row-echelon matrix:

(defthmd fdot-row-split
  (implies (and (fmatp r m n) (posp m) (posp n) (row-echelon-p r) (flistnp c n)
                (natp s) (< s (num-nonzero-rows r)))
           (equal (fdot (nth s r) c)
                  (f+ (nth (nth s (lead-inds r)) c)
                      (fdot-select (free-inds r n) (nth s r) c))))
  :hints (("Goal" :use ((:instance num-nonzero-rows<=m (a r))
                        (:instance fmatp-first-rows (a r) (q (num-nonzero-rows r)))
                        (:instance row-echelon-p-first-rows (a r) (q (num-nonzero-rows r)))
                        (:instance num-nonzero-rows-first-rows (a r) (q (num-nonzero-rows r)))
                        (:instance lead-inds-first-nonzero-rows (a r))
                        (:instance nth-first-rows (a r) (q (num-nonzero-rows r)) (i s))
                        (:instance fdot-lead-free (aq (first-rows (num-nonzero-rows r) r))
                                   (q (num-nonzero-rows r)) (x c) (i s))
                        (:instance fdot-select-lead-inds (aq (first-rows (num-nonzero-rows r) r))
                                   (q (num-nonzero-rows r)) (x c) (i s)))
                  :in-theory (enable free-inds))))

(defthm kr#-bound
  (<= (kr#) (wdim))
  :rule-classes (:linear :rewrite)
  :hints (("Goal" :use ((:instance num-nonzero-rows<=m (a (kR)) (m (wdim)) (n (vdim)))
                        (:instance posp-vdim) (:instance posp-wdim)))))

(defthm len-kL
  (equal (len (kL)) (kr#))
  :hints (("Goal" :use ((:instance len-lead-inds-num-nonzero-rows (a (kR)))))))

(defthm dlistp-kL
  (dlistp (kL))
  :hints (("Goal" :use ((:instance dlistp-lead-inds (a (kR)) (m (wdim)) (n (vdim)))
                        (:instance posp-vdim) (:instance posp-wdim)))))

(defthm dlistp-kF
  (dlistp (kF))
  :hints (("Goal" :use ((:instance dlistp-free-inds (a (kR)) (m (wdim)) (n (vdim)))
                        (:instance posp-vdim) (:instance posp-wdim)))))

(defthmd member-kF
  (iff (member i (kF))
       (and (natp i) (< i (vdim)) (not (member i (kL)))))
  :hints (("Goal" :use ((:instance member-free-inds (a (kR)) (m (wdim)) (n (vdim)) (x i))
                        (:instance member-ninit (x i) (n (vdim)))
                        (:instance posp-vdim) (:instance posp-wdim)))))

(defthm kF-props
  (implies (member i (kF))
           (and (natp i) (< i (vdim)) (not (member i (kL)))))
  :hints (("Goal" :use member-kF)))

(defthmd kL-nth-props
  (implies (and (natp s) (< s (kr#)))
           (and (natp (nth s (kL)))
                (< (nth s (kL)) (vdim))
                (member (nth s (kL)) (kL))
                (equal (index (nth s (kL)) (kL)) s)))
  :hints (("Goal" :use ((:instance nth-lead-inds-bound (a (kR)) (m (wdim)) (n (vdim)) (k s))
                        (:instance posp-vdim) (:instance posp-wdim)))))

;; Coordinates of the kernel basis vectors:

(defthm fp-kbasis-coord
  (implies (and (natp i) (< i (vdim)) (natp j) (< j (vdim)))
           (fp (kbasis-coord i j)))
  :hints (("Goal" :use ((:instance fp-entry (a (kR)) (m (wdim)) (n (vdim))
                                   (i (index i (kL))) (j j))
                        (:instance ind<len (x i) (l (kL)))
                        (:instance posp-vdim) (:instance posp-wdim))
                  :in-theory (e/d (kbasis-coord) (ind<len)))))

(defthm kbasis-coord-free
  (implies (member i (kF))
           (equal (kbasis-coord i j) (if (= i j) (f1) (f0))))
  :hints (("Goal" :in-theory (enable kbasis-coord))))

(defthm kbasis-coord-lead
  (implies (and (natp s) (< s (kr#)))
           (equal (kbasis-coord (nth s (kL)) j)
                  (f- (entry s j (kR)))))
  :hints (("Goal" :use ((:instance kL-nth-props))
                  :in-theory (e/d (kbasis-coord) (entry)))))

(defthm nth-append-gen
  (implies (natp i)
           (equal (nth i (append x y))
                  (if (< i (len x)) (nth i x) (nth (- i (len x)) y)))))

(defthm flistnp-append-1-aux
  (implies (and (flistnp x k) (fp a) (natp k))
           (flistnp (append x (list a)) (1+ k))))

(defthm flistnp-append-1
  (implies (and (flistnp x (1- k)) (fp a) (posp k))
           (flistnp (append x (list a)) k))
  :hints (("Goal" :use ((:instance flistnp-append-1-aux (k (1- k)))))))

(defthm flistnp-kbasis-coords-aux
  (implies (and (natp k) (<= k (vdim)) (natp j) (< j (vdim)))
           (flistnp (kbasis-coords-aux k j) k)))

(defthm len-append-gen
  (equal (len (append x y)) (+ (len x) (len y))))

(defthm len-kbasis-coords-aux
  (equal (len (kbasis-coords-aux k j)) (nfix k)))

(defthm nth-kbasis-coords-aux
  (implies (and (natp k) (<= k (vdim)) (natp j) (< j (vdim))
                (natp i) (< i k))
           (equal (nth i (kbasis-coords-aux k j))
                  (kbasis-coord i j)))
  :hints (("Goal" :induct (kbasis-coords-aux k j))))

(defthm kbasis-coords-aux-props
  (implies (and (natp k) (<= k (vdim)) (natp j) (< j (vdim)))
           (and (flistnp (kbasis-coords-aux k j) k)
                (implies (and (natp i) (< i k))
                         (equal (nth i (kbasis-coords-aux k j))
                                (kbasis-coord i j))))))

(defthm kbasis-coords-props
  (implies (and (natp j) (< j (vdim)))
           (and (flistnp (kbasis-coords j) (vdim))
                (implies (and (natp i) (< i (vdim)))
                         (equal (nth i (kbasis-coords j))
                                (kbasis-coord i j)))))
  :hints (("Goal" :use ((:instance kbasis-coords-aux-props (k (vdim)))
                        (:instance posp-vdim))
                  :in-theory (enable kbasis-coords))))

;; Sum over a sublist of the free indices with kbasis coordinates:

(defthm fdot-select-kbasis-coords
  (implies (and (sublistp g (kF)) (dlistp g) (flistnp r (vdim)) (natp j) (< j (vdim)))
           (equal (fdot-select g r (kbasis-coords j))
                  (if (member j g) (nth j r) (f0))))
  :hints (("Goal" :induct (sublistp g (kF)))))

(defthm kbasis-coords-kernel-row
  (implies (and (member j (kF)) (natp s) (< s (wdim)))
           (equal (fdot (nth s (kR)) (kbasis-coords j)) (f0)))
  :hints (("Goal" :cases ((< s (kr#))))
          ("Subgoal 2" :use ((:instance num-nonzero-rows-nonzero (a (kR)) (m (wdim)) (n (vdim)) (i s))
                             (:instance flistnp-flist0p-equal (x (nth s (kR))) (n (vdim)))
                             (:instance flistnp-row (a (kR)) (m (wdim)) (n (vdim)) (i s))
                             (:instance posp-vdim) (:instance posp-wdim))
                       :in-theory (disable flistnp-row))
          ("Subgoal 1" :use ((:instance fdot-row-split (r (kR)) (m (wdim)) (n (vdim))
                                        (c (kbasis-coords j)))
                             (:instance kL-nth-props)
                             (:instance flistnp-row (a (kR)) (m (wdim)) (n (vdim)) (i s))
                             (:instance fp-entry (a (kR)) (m (wdim)) (n (vdim)) (i s) (j j))
                             (:instance posp-vdim) (:instance posp-wdim))
                       :in-theory (disable flistnp-row))))

(defthm kbasis-coords-kernel
  (implies (member j (kF))
           (equal (fcomb (kbasis-coords j) (lin-mat) (wdim)) (flistn0 (wdim))))
  :hints (("Goal" :use ((:instance kernel-coords-iff (c (kbasis-coords j)))
                        (:instance flistnp-nth-diff (x (fdot-list (kbasis-coords j) (kR)))
                                   (y (flistn0 (wdim))) (n (wdim)))
                        (:instance fdot-comm (x (kbasis-coords j))
                                   (y (nth (nth-diff (fdot-list (kbasis-coords j) (kR)) (flistn0 (wdim))) (kR)))
                                   (n (vdim)))
                        (:instance flistnp-row (a (kR)) (m (wdim)) (n (vdim))
                                   (i (nth-diff (fdot-list (kbasis-coords j) (kR)) (flistn0 (wdim)))))
                        (:instance posp-vdim) (:instance posp-wdim))
                  :in-theory (disable flistnp-row))))

(defthm in-kernel-p-kbasis-elt
  (implies (member j (kF))
           (in-kernel-p (vcomb (kbasis-coords j) (vbasis0))))
  :hints (("Goal" :use ((:instance wcoords0-lin-basis (c (kbasis-coords j)))
                        (:instance ws-vcoords0-zero (x (lin (vcomb (kbasis-coords j) (vbasis0))))))
                  :in-theory (e/d (in-kernel-p) (lin-vcomb wcoords0-lin-vcomb)))))

(defthm klistnp-kbasis-aux
  (implies (sublistp g (kF))
           (klistnp (kbasis-aux g) (len g))))

(defthm klistnp-vlistnp
  (implies (klistnp l n) (vlistnp l n))
  :hints (("Goal" :in-theory (enable in-kernel-p))))

(defthm len-kbasis-aux
  (equal (len (kbasis-aux g)) (len g)))

(defthm kdim-len
  (equal (kdim) (len (kF)))
  :hints (("Goal" :in-theory (enable kdim kbasis))))

(defthm klistnp-kbasis
  (klistnp (kbasis) (kdim))
  :hints (("Goal" :in-theory (enable kbasis))))

;; Independence of the kernel basis:

(defun kc-list (g)
  (if (consp g)
      (cons (kbasis-coords (car g)) (kc-list (cdr g)))
    ()))

(defthm kc-list-props
  (implies (sublistp g (kF))
           (and (fmatp (kc-list g) (len g) (vdim))
                (equal (vcoord-mat (kbasis-aux g)) (kc-list g)))))

(defthm nth-kc-list
  (implies (and (natp t0) (< t0 (len g)))
           (equal (nth t0 (kc-list g)) (kbasis-coords (nth t0 g)))))

(defthm member-nth-kF
  (implies (and (natp i) (< i (len (kF))))
           (member (nth i (kF)) (kF))))

(defthm nth-col-kc-list
  (implies (and (natp i) (< i (len (kF))) (natp t0) (< t0 (len (kF))))
           (equal (nth t0 (col (nth i (kF)) (kc-list (kF))))
                  (fdelta t0 i)))
  :hints (("Goal" :use ((:instance nth-col (i t0) (j (nth i (kF))) (a (kc-list (kF))))
                        (:instance nth-kc-list (g (kF)))
                        (:instance member-nth-kF (i i))
                        (:instance member-nth-kF (i t0))
                        (:instance kF-props (i (nth i (kF))))
                        (:instance kF-props (i (nth t0 (kF))))
                        (:instance kbasis-coords-props (j (nth t0 (kF))) (i (nth i (kF))))
                        (:instance kbasis-coord-free (i (nth i (kF))) (j (nth t0 (kF))))
                        (:instance nth-dlist-distinct (l (kF)) (i i) (j t0)))
                  :in-theory (disable col kc-list nth-dlist-distinct member-nth-kF kF-props
                                      kbasis-coords-props kbasis-coord-free nth-kc-list))))

(defthmd col-kc-list
  (implies (and (natp i) (< i (len (kF))))
           (equal (col (nth i (kF)) (kc-list (kF)))
                  (funit i (len (kF)))))
  :hints (("Goal" :use ((:instance flistnp-nth-diff (x (col (nth i (kF)) (kc-list (kF))))
                                   (y (funit i (len (kF)))) (n (len (kF))))
                        (:instance nth-col-kc-list
                                   (t0 (nth-diff (col (nth i (kF)) (kc-list (kF))) (funit i (len (kF))))))
                        (:instance flistnp-col (a (kc-list (kF))) (m (len (kF))) (n (vdim)) (j (nth i (kF))))
                        (:instance kc-list-props (g (kF)))
                        (:instance member-nth-kF (i i))
                        (:instance kF-props (i (nth i (kF))))
                        (:instance nth-funit (n (len (kF))) (j i)
                                   (i (nth-diff (col (nth i (kF)) (kc-list (kF))) (funit i (len (kF))))))
                        (:instance posp-vdim))
                  :in-theory (disable col kc-list nth-col-kc-list flistnp-col kc-list-props member-nth-kF
                                      kF-props nth-funit funit))))

(defthm vk-1
  (implies (and (flistnp d (len (kF)))
                (equal (fcomb d (kc-list (kF)) (vdim)) (flistn0 (vdim))))
           (equal d (flistn0 (len (kF)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance flistnp-not-zero (m (len (kF))))
                        (:instance col-kc-list (i (nth-diff d (flistn0 (len (kF))))))
                        (:instance fcomb-unit-col (a (kc-list (kF))) (m (len (kF))) (n (vdim))
                                   (i (nth-diff d (flistn0 (len (kF)))))
                                   (k (nth (nth-diff d (flistn0 (len (kF)))) (kF))))
                        (:instance member-nth-kF (i (nth-diff d (flistn0 (len (kF))))))
                        (:instance kF-props (i (nth (nth-diff d (flistn0 (len (kF)))) (kF))))
                        (:instance kc-list-props (g (kF)))
                        (:instance posp-vdim))
                  :in-theory (disable member-nth-kF kF-props kc-list-props fcomb kc-list))))

(defthm vindepp-kbasis-aux
  (vindepp (kbasis-aux (kF)))
  :hints (("Goal" :cases ((consp (kF))))
          ("Subgoal 2" :in-theory (enable vindepp))
          ("Subgoal 1" :use ((:instance vdep-coeffs-dep (l (kbasis-aux (kF))) (n (len (kF))))
                             (:instance vs-vcomb-zero-iff (l (kbasis-aux (kF))) (n (len (kF)))
                                        (d (vdep-coeffs (kbasis-aux (kF)))))
                             (:instance kc-list-props (g (kF)))
                             (:instance vk-1 (d (vdep-coeffs (kbasis-aux (kF)))))
                             (:instance klistnp-kbasis-aux (g (kF))))
                       :in-theory (disable vdep-coeffs kc-list-props klistnp-kbasis-aux kbasis-aux))))

(defthm vindepp-kbasis
  (vindepp (kbasis))
  :hints (("Goal" :in-theory (enable kbasis))))

;; Kernel coordinates:

(defthm flistnp-kcoords-aux
  (implies (and (vp x) (sublistp g (kF)))
           (flistnp (kcoords-aux x g) (len g))))

(defthm flistnp-kcoords
  (implies (in-kernel-p x)
           (flistnp (kcoords x) (kdim)))
  :hints (("Goal" :in-theory (enable kcoords in-kernel-p))))

(defun ksum (c g i)
  (if (consp g)
      (f+ (f* (nth (car g) c) (kbasis-coord i (car g)))
          (ksum c (cdr g) i))
    (f0)))

(defthm nth-kstep
  (implies (and (fp a) (flistnp r (vdim)) (flistnp s (vdim)) (natp i) (< i (vdim)))
           (equal (nth i (flist-add (flist-scalar-mul a r) s))
                  (f+ (f* a (nth i r)) (nth i s))))
  :hints (("Goal" :use ((:instance nth-flist-add (x (flist-scalar-mul a r)) (y s) (n (vdim)))
                        (:instance nth-flist-scalar-mul (c a) (x r) (n (vdim)))))))

(defthm flistnp-fcomb-kcoords
  (implies (and (vp x) (sublistp g (kF)))
           (flistnp (fcomb (kcoords-aux x g) (kc-list g) (vdim)) (vdim)))
  :hints (("Goal" :use ((:instance flistnp-fcomb (d (kcoords-aux x g)) (a (kc-list g))
                                   (m (len g)) (n (vdim)))))))

(defthm nth-fcomb-kcoords
  (implies (and (vp x) (sublistp g (kF)) (natp i) (< i (vdim)))
           (equal (nth i (fcomb (kcoords-aux x g) (kc-list g) (vdim)))
                  (ksum (vcoords0 x) g i))))

(defthm fp-ksum
  (implies (and (sublistp g (kF)) (flistnp c (vdim)) (natp i) (< i (vdim)))
           (fp (ksum c g i))))

(defthm ksum-free-0
  (implies (and (sublistp g (kF)) (member i (kF)) (flistnp c (vdim))
                (not (member i g)))
           (equal (ksum c g i) (f0))))

(defthm ksum-free
  (implies (and (sublistp g (kF)) (dlistp g) (member i (kF)) (flistnp c (vdim)))
           (equal (ksum c g i)
                  (if (member i g) (nth i c) (f0))))
  :hints (("Goal" :induct (ksum c g i))))

(defthm flistnp-kR-row
  (implies (and (natp s) (< s (wdim)))
           (flistnp (nth s (kR)) (vdim)))
  :hints (("Goal" :use ((:instance flistnp-row (a (kR)) (m (wdim)) (n (vdim)) (i s))
                        (:instance posp-vdim) (:instance posp-wdim))
                  :in-theory (disable flistnp-row))))

(defthm fp-fdot-select-kF
  (implies (and (sublistp g (kF)) (flistnp r (vdim)) (flistnp c (vdim)))
           (fp (fdot-select g r c))))

(defthm ksum-lead-step
  (implies (and (member g0 (kF)) (flistnp c (vdim)) (natp s) (< s (kr#)) (sublistp g1 (kF)))
           (equal (f+ (f* (nth g0 c) (f- (nth g0 (nth s (kR)))))
                      (f- (fdot-select g1 (nth s (kR)) c)))
                  (f- (f+ (f* (nth g0 (nth s (kR))) (nth g0 c))
                          (fdot-select g1 (nth s (kR)) c)))))
  :hints (("Goal" :use ((:instance fs-ks-step (a (nth g0 c)) (b (nth g0 (nth s (kR))))
                                   (s (fdot-select g1 (nth s (kR)) c)))
                        (:instance kF-props (i g0))
                        (:instance flistnp-kR-row)
                        (:instance fp-flistnp (x c) (n (vdim)) (i g0))
                        (:instance fp-flistnp (x (nth s (kR))) (n (vdim)) (i g0))
                        (:instance fp-fdot-select-kF (g g1) (r (nth s (kR)))))
                  :in-theory (disable fs-ks-step kF-props flistnp-kR-row fp-flistnp fp-fdot-select-kF))))

(defthm ksum-lead
  (implies (and (sublistp g (kF)) (flistnp c (vdim)) (natp s) (< s (kr#)))
           (equal (ksum c g (nth s (kL)))
                  (f- (fdot-select g (nth s (kR)) c))))
  :hints (("Goal" :induct (ksum c g (nth s (kL))))))

(defthmd kernel-lead-coord
  (implies (and (in-kernel-p x) (natp s) (< s (kr#)))
           (equal (nth (nth s (kL)) (vcoords0 x))
                  (f- (fdot-select (kF) (nth s (kR)) (vcoords0 x)))))
  :hints (("Goal" :use ((:instance wcoords0-lin)
                        (:instance kernel-coords-iff (c (vcoords0 x)))
                        (:instance nth-fdot-list (j s) (x (vcoords0 x)) (l (kR)))
                        (:instance fdot-comm (x (vcoords0 x)) (y (nth s (kR))) (n (vdim)))
                        (:instance fdot-row-split (r (kR)) (m (wdim)) (n (vdim)) (c (vcoords0 x)))
                        (:instance f-unique (x (nth (nth s (kL)) (vcoords0 x)))
                                   (y (fdot-select (kF) (nth s (kR)) (vcoords0 x))))
                        (:instance kL-nth-props)
                        (:instance flistnp-row (a (kR)) (m (wdim)) (n (vdim)) (i s))
                        (:instance posp-vdim) (:instance posp-wdim))
                  :in-theory (e/d (in-kernel-p) (nth-fdot-list flistnp-row)))))

(defthmd kernel-coord-recover
  (implies (and (in-kernel-p x) (natp i) (< i (vdim)))
           (equal (nth i (fcomb (kcoords x) (vcoord-mat (kbasis)) (vdim)))
                  (nth i (vcoords0 x))))
  :hints (("Goal" :cases ((member i (kL))))
          ("Subgoal 2" :use ((:instance member-kF))
                       :in-theory (enable kcoords kbasis in-kernel-p))
          ("Subgoal 1" :use ((:instance kernel-lead-coord (s (index i (kL))))
                             (:instance ksum-lead (c (vcoords0 x)) (g (kF)) (s (index i (kL))))
                             (:instance nth-ind (x i) (l (kL)))
                             (:instance ind<len (x i) (l (kL))))
                       :in-theory (e/d (kcoords kbasis in-kernel-p) (ksum-lead nth-ind ind<len)))))

(defthm kernel-spans
  (implies (in-kernel-p x)
           (equal (vcomb (kcoords x) (kbasis)) x))
  :hints (("Goal" :use ((:instance flistnp-nth-diff (x (fcomb (kcoords x) (vcoord-mat (kbasis)) (vdim)))
                                   (y (vcoords0 x)) (n (vdim)))
                        (:instance kernel-coord-recover
                                   (i (nth-diff (fcomb (kcoords x) (vcoord-mat (kbasis)) (vdim)) (vcoords0 x))))
                        (:instance vs-vcoords0-vcomb-gen (d (kcoords x)) (l (kbasis)) (n (kdim)))
                        (:instance vs-vcoords0-inj (x (vcomb (kcoords x) (kbasis))) (y x))
                        (:instance flistnp-kcoords)
                        (:instance vs-vp-vcomb (d (kcoords x)) (l (kbasis)) (n (kdim)))
                        (:instance posp-vdim))
                  :in-theory (e/d (in-kernel-p) (vs-vcoords0-vcomb-gen flistnp-kcoords kdim-len vs-vp-vcomb)))))

(defthm main-5
  (and (klistnp (kbasis) (kdim))
       (vindepp (kbasis))
       (implies (in-kernel-p x)
                (flistnp (kcoords x) (kdim)))
       (implies (in-kernel-p x)
                (equal (vcomb (kcoords x) (kbasis)) x)))
  :hints (("Goal" :in-theory (disable kdim-len))))

;;;=====================================================================
;;; Part 7: Image, MAIN-6
;;;=====================================================================

(in-theory (disable kdim-len (idim)))

(defthm kdim-natp
  (natp (kdim))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable kdim))))

(defthm cdr-nthcdr
  (equal (cdr (nthcdr k x)) (nthcdr k (cdr x))))

(defun ext-prefix (l)
  (declare (xargs :measure (nfix (- (vdim) (len l)))
                  :hints (("Goal" :use posp-vdim))))
  (if (and (vlistnp l (len l)) (vindepp l) (< (len l) (vdim)))
      (append (ext-prefix (cons (vunspanned l) l)) (list (vunspanned l)))
    ()))

(defthm append-assoc-gen
  (equal (append (append x y) z) (append x (append y z))))

(defthm true-listp-ext-prefix
  (true-listp (ext-prefix l)))

(defthm extend-to-basis-prefix
  (equal (extend-to-basis l) (append (ext-prefix l) l))
  :hints (("Goal" :induct (extend-to-basis l))))

(defthm nthcdr-append-len
  (equal (nthcdr (len p) (append p l)) l))

(defthm nthcdr-append-k
  (implies (equal (len p) k)
           (equal (nthcdr k (append p l)) l)))

(defthm nthcdr-len-true-listp
  (implies (and (true-listp x) (equal (len x) k))
           (equal (nthcdr k x) nil)))

(defthm vindepp-vbasis0
  (vindepp (vbasis0))
  :hints (("Goal" :use ((:instance vdep-coeffs-dep (l (vbasis0)) (n (vdim)))
                        (:instance vbasis0-lin-indep (c (vdep-coeffs (vbasis0))))
                        (:instance posp-vdim))
                  :in-theory (disable vdep-coeffs))))

(defthm true-listp-kbasis-aux
  (true-listp (kbasis-aux g)))

(defthm kbasis-aux-len0
  (implies (equal (len g) 0) (equal (kbasis-aux g) nil))
  :hints (("Goal" :expand ((len g) (kbasis-aux g)))))

(defthmd kbasis-nil
  (implies (not (posp (kdim)))
           (equal (kbasis) nil))
  :hints (("Goal" :in-theory (enable kdim kbasis))))

(defthm vlistnp-kbasis
  (vlistnp (kbasis) (kdim))
  :hints (("Goal" :use ((:instance klistnp-vlistnp (l (kbasis)) (n (kdim))))
                  :in-theory (disable klistnp-vlistnp))))

(defthm len-kbasis
  (equal (len (kbasis)) (kdim))
  :hints (("Goal" :in-theory (enable kdim))))

(defthm extend-kbasis-props
  (and (vlistnp (extend-kbasis) (vdim))
       (vindepp (extend-kbasis))
       (equal (len (extend-kbasis)) (vdim))
       (<= (kdim) (vdim))
       (equal (nthcdr (idim) (extend-kbasis)) (kbasis)))
  :hints (("Goal" :cases ((posp (kdim))))
          ("Subgoal 2" :use ((:instance kbasis-nil)
                             (:instance vs-vlistnp-len (l (vbasis0)) (n (vdim)))
                             (:instance vs-vlistnp-true-listp (l (vbasis0)) (n (vdim)))
                             (:instance posp-vdim))
                       :in-theory (enable extend-kbasis))
          ("Subgoal 1" :use ((:instance main-3 (l (kbasis)) (n (kdim)))
                             (:instance vs-vlistnp-len (l (extend-kbasis)) (n (vdim)))
                             (:instance posp-vdim))
                       :in-theory (e/d (extend-kbasis vbasisp) (main-3)))))

(defthm idim-facts
  (and (natp (idim))
       (<= (idim) (vdim))
       (equal (+ (idim) (kdim)) (vdim))
       (equal (+ (kdim) (idim)) (vdim))
       (equal (- (vdim) (idim)) (kdim)))
  :hints (("Goal" :use ((:instance extend-kbasis-props)
                        (:instance posp-vdim))
                  :in-theory (disable extend-kbasis-props))))

(in-theory (disable idim))

(defthm append-firstn-nthcdr
  (implies (and (natp k) (<= k (len x)))
           (equal (append (firstn k x) (nthcdr k x)) x)))

(defthm extend-kbasis-split
  (equal (append (firstn (idim) (extend-kbasis)) (kbasis))
         (extend-kbasis))
  :hints (("Goal" :use ((:instance extend-kbasis-props)
                        (:instance append-firstn-nthcdr (k (idim)) (x (extend-kbasis))))
                  :in-theory (disable extend-kbasis-props append-firstn-nthcdr))))

(defthm vlistnp-firstn
  (implies (and (vlistnp x n) (natp n) (natp k) (<= k n))
           (vlistnp (firstn k x) k))
  :hints (("Goal" :induct (vs-ind2 k x n))))

(defthm flistnp-firstn
  (implies (and (flistnp x n) (natp n) (natp k) (<= k n))
           (flistnp (firstn k x) k))
  :hints (("Goal" :induct (vs-ind2 k x n))))

(defthm flistnp-nthcdr
  (implies (and (flistnp x n) (natp k) (<= k n) (natp n))
           (flistnp (nthcdr k x) (- n k)))
  :hints (("Goal" :induct (vs-ind2 k x n))))

(defthm vlistnp-ifirst
  (vlistnp (firstn (idim) (extend-kbasis)) (idim))
  :hints (("Goal" :use ((:instance extend-kbasis-props))
                  :in-theory (disable extend-kbasis-props))))

(defthmd vs-v+assoc-r
  (implies (and (vp x) (vp y) (vp z))
           (equal (v+ (v+ x y) z) (v+ x (v+ y z))))
  :hints (("Goal" :use v+assoc)))

(defthm vcomb-append
  (implies (and (vlistnp l1 k) (flistnp a k) (vlistnp l2 j) (flistnp b j))
           (equal (vcomb (append a b) (append l1 l2))
                  (v+ (vcomb a l1) (vcomb b l2))))
  :hints (("Goal" :induct (vs-ind3 a a l1 k)
                  :in-theory (enable vs-v+assoc-r))))

(defthm vp-vcomb-klistnp
  (implies (and (klistnp l n) (flistnp e n))
           (vp (vcomb e l)))
  :hints (("Goal" :use ((:instance klistnp-vlistnp)
                        (:instance vs-vp-vcomb (d e)))
                  :in-theory (disable klistnp-vlistnp vs-vp-vcomb vcomb))))

(defthm lin-vcomb-kernel
  (implies (and (klistnp l n) (flistnp e n))
           (equal (lin (vcomb e l)) (w0)))
  :hints (("Goal" :in-theory (enable in-kernel-p))))

(defthm in-image-p-lin
  (implies (vp v) (in-image-p (lin v)))
  :hints (("Goal" :use ((:instance lin-preimage (y (lin v)) (x v)))
                  :in-theory (enable in-image-p))))

(defthm ilistnp-lin-list
  (implies (vlistnp l n)
           (ilistnp (lin-list l) n))
  :hints (("Goal" :induct (vs-ind l n))))

(defthm firstn-append
  (implies (and (true-listp d) (equal (len d) k))
           (equal (firstn k (append d e)) d)))

(defthm firstn-flistn0
  (implies (and (natp k) (<= k n) (natp n))
           (equal (firstn k (flistn0 n)) (flistn0 k)))
  :hints (("Goal" :induct (vs-ind2 k nil n))))

(defthm not-vindepp-cons-basis
  (implies (and (vlistnp l (vdim)) (vp x))
           (not (vindepp (cons x l))))
  :hints (("Goal" :use ((:instance row-rank<=n (a (vcoord-mat (cons x l))) (m (1+ (vdim))) (n (vdim)))
                        (:instance vs-vlistnp-len (n (vdim)))
                        (:instance posp-vdim))
                  :in-theory (e/d (vindepp) (row-rank)))))

(defthm flistnp-append-gen
  (implies (and (flistnp a i) (flistnp b j) (natp i) (natp j))
           (flistnp (append a b) (+ i j)))
  :hints (("Goal" :induct (vs-ind2 i a i))))

(defmacro kF1 () '(firstn (idim) (extend-kbasis)))

(defthm vp-vcomb-kF1
  (implies (flistnp d (idim))
           (vp (vcomb d (kF1))))
  :hints (("Goal" :use ((:instance vs-vp-vcomb (l (kF1)) (n (idim))))
                  :in-theory (disable vs-vp-vcomb))))

(defthmd ib-a
  (implies (and (flistnp d (idim)) (in-kernel-p (vcomb d (kF1))))
           (equal (vcomb (append d (flist-scalar-mul (f- (f1)) (kcoords (vcomb d (kF1)))))
                         (extend-kbasis))
                  (v0)))
  :hints (("Goal" :use ((:instance kernel-spans (x (vcomb d (kF1))))
                        (:instance flistnp-kcoords (x (vcomb d (kF1))))
                        (:instance extend-kbasis-split)
                        (:instance vcomb-append (l1 (kF1)) (k (idim)) (l2 (kbasis)) (j (kdim))
                                   (a d) (b (flist-scalar-mul (f- (f1)) (kcoords (vcomb d (kF1)))))))
                  :in-theory (disable kernel-spans flistnp-kcoords extend-kbasis-split vcomb-append
                                      extend-to-basis-prefix))))

(defthmd ib-b
  (implies (and (flistnp d (idim)) (in-kernel-p (vcomb d (kF1))))
           (flistnp (append d (flist-scalar-mul (f- (f1)) (kcoords (vcomb d (kF1)))))
                    (vdim)))
  :hints (("Goal" :use ((:instance flistnp-kcoords (x (vcomb d (kF1))))
                        (:instance extend-kbasis-props)
                        (:instance flistnp-append-gen (a d)
                                   (b (flist-scalar-mul (f- (f1)) (kcoords (vcomb d (kF1)))))
                                   (i (idim)) (j (kdim))))
                  :in-theory (disable flistnp-kcoords extend-kbasis-props flistnp-append-gen))))

(defthm ib-1
  (implies (and (flistnp d (idim))
                (equal (lin (vcomb d (kF1))) (w0)))
           (equal d (flistn0 (idim))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance ib-a) (:instance ib-b)
                        (:instance vindepp-indep (l (extend-kbasis)) (n (vdim))
                                   (d (append d (flist-scalar-mul (f- (f1)) (kcoords (vcomb d (kF1)))))))
                        (:instance firstn-append (k (idim))
                                   (e (flist-scalar-mul (f- (f1)) (kcoords (vcomb d (kF1))))))
                        (:instance firstn-flistn0 (k (idim)) (n (vdim)))
                        (:instance extend-kbasis-props))
                  :in-theory (e/d (in-kernel-p)
                                  (firstn-append firstn-flistn0 extend-kbasis-props firstn extend-to-basis-prefix)))))

(defthm windepp-ibasis
  (windepp (ibasis))
  :hints (("Goal" :cases ((posp (idim))))
          ("Subgoal 2" :in-theory (enable ibasis windepp))
          ("Subgoal 1"
           :use ((:instance ws-dep-exists (l (lin-list (kF1))) (n (idim)))
                 (:instance ib-1 (d (nth (1- (idim)) (row-reduce-mat (wcoord-mat (lin-list (kF1)))))))
                 (:instance lin-vcomb (l (kF1)) (n (idim))
                            (d (nth (1- (idim)) (row-reduce-mat (wcoord-mat (lin-list (kF1))))))))
           :in-theory (e/d (ibasis) (lin-vcomb extend-to-basis-prefix)))))

(defthm flistnp-icoords
  (implies (in-image-p x)
           (flistnp (icoords x) (idim)))
  :hints (("Goal" :use ((:instance vcoords-spans (x (lin-preimage x)) (l (extend-kbasis)) (n (vdim)))
                        (:instance extend-kbasis-props)
                        (:instance posp-vdim))
                  :in-theory (e/d (icoords in-image-p) (vcoords-spans extend-kbasis-props)))))

(defthm is-1
  (implies (and (flistnp c1 (idim)) (flistnp c2 (kdim)))
           (equal (lin (v+ (vcomb c1 (kF1)) (vcomb c2 (kbasis))))
                  (wcomb c1 (lin-list (kF1)))))
  :hints (("Goal" :use ((:instance lin-v+ (x (vcomb c1 (kF1))) (y (vcomb c2 (kbasis))))
                        (:instance lin-vcomb (l (kF1)) (n (idim)) (d c1))
                        (:instance lin-vcomb-kernel (l (kbasis)) (n (kdim)) (e c2))
                        (:instance vs-vp-vcomb (l (kbasis)) (n (kdim)) (d c2))
                        (:instance ws-vp-vcomb (l (lin-list (kF1))) (n (idim)) (d c1)))
                  :in-theory (disable lin-v+ lin-vcomb lin-vcomb-kernel vs-vp-vcomb ws-vp-vcomb))))

(defthm image-spans
  (implies (in-image-p x)
           (equal (wcomb (icoords x) (ibasis)) x))
  :hints (("Goal" :use ((:instance vcoords-spans (x (lin-preimage x)) (l (extend-kbasis)) (n (vdim)))
                        (:instance extend-kbasis-props)
                        (:instance append-firstn-nthcdr (k (idim))
                                   (x (vcoords (lin-preimage x) (extend-kbasis))))
                        (:instance vcomb-append (l1 (firstn (idim) (extend-kbasis))) (k (idim))
                                   (l2 (kbasis)) (j (kdim))
                                   (a (firstn (idim) (vcoords (lin-preimage x) (extend-kbasis))))
                                   (b (nthcdr (idim) (vcoords (lin-preimage x) (extend-kbasis)))))
                        (:instance lin-vcomb (l (firstn (idim) (extend-kbasis))) (n (idim))
                                   (d (firstn (idim) (vcoords (lin-preimage x) (extend-kbasis)))))
                        (:instance lin-vcomb-kernel (l (kbasis)) (n (kdim))
                                   (e (nthcdr (idim) (vcoords (lin-preimage x) (extend-kbasis)))))
                        (:instance is-1 (c1 (firstn (idim) (vcoords (lin-preimage x) (extend-kbasis))))
                                   (c2 (nthcdr (idim) (vcoords (lin-preimage x) (extend-kbasis)))))
                        (:instance flistnp-nthcdr (x (vcoords (lin-preimage x) (extend-kbasis)))
                                   (n (vdim)) (k (idim)))
                        (:instance flistnp-firstn (x (vcoords (lin-preimage x) (extend-kbasis)))
                                   (n (vdim)) (k (idim)))
                        (:instance posp-vdim))
                  :in-theory (e/d (icoords in-image-p ibasis)
                                  (vcoords-spans extend-kbasis-props append-firstn-nthcdr vcomb-append
                                                 lin-vcomb lin-vcomb-kernel flistnp-nthcdr flistnp-firstn is-1)))))

(defthm ilistnp-ibasis
  (ilistnp (ibasis) (idim))
  :hints (("Goal" :in-theory (enable ibasis))))

(defthm main-6
  (and (ilistnp (ibasis) (idim))
       (windepp (ibasis))
       (implies (in-image-p x)
                (flistnp (icoords x) (idim)))
       (implies (in-image-p x)
                (equal (wcomb (icoords x) (ibasis)) x))))

