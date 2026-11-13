; Syntax/admissibility check of candidate task statements.  Theorems are
; wrapped in skip-proofs ONLY to check that they translate; this is not a
; solution.

(in-package "ACL2")
(include-book "projects/set-theory/top" :dir :system)
(include-book "projects/set-theory/topology/compact" :dir :system)
(include-book "projects/set-theory/topology/normal" :dir :system)
(include-book "projects/set-theory/topology/subspace" :dir :system)
(include-book "projects/set-theory/algebra/groups" :dir :system)
(include-book "projects/set-theory/reals/sum" :dir :system)
(in-package "ZF")

(defmacro chk (&rest x) `(skip-proofs (defthmz ,@x :rule-classes nil)))

;;; ---------------- A. Equivalence relations
(defun-sk refl-on (r s)
  (forall x (implies (in x s) (in (cons x x) r))))
(defun-sk sym-rel (r)
  (forall (x y) (implies (in (cons x y) r) (in (cons y x) r))))
(defun-sk trans-rel (r)
  (forall (x y z) (implies (and (in (cons x y) r) (in (cons y z) r))
                           (in (cons x z) r))))
(defun equivalence-on (r s)
  (and (subset r (prod2 s s)) (refl-on r s) (sym-rel r) (trans-rel r)))
(zsub eqv-class (a r s) y s (in (cons a y) r))
(defun-sk is-eqv-class (c r s)
  (exists a (and (in a s) (equal c (eqv-class a r s)))))
(zsub quotient (r s) c (powerset s) (is-eqv-class c r s))
(defun-sk pairwise-disjoint (p)
  (forall (c d) (implies (and (in c p) (in d p) (not (equal c d)))
                         (equal (int2 c d) 0))))
(defun partition-p (p s)
  (and (equal (union p) s) (not (in 0 p)) (pairwise-disjoint p)))
(defun-sk same-block (x y p)
  (exists c (and (in c p) (in x c) (in y c))))
(zsub partition-rel (p s) q (prod2 s s) (same-block (car q) (cdr q) p))
(defun-sk maps-to-classes (f r s)
  (forall a (implies (in a s) (equal (apply f a) (eqv-class a r s)))))
(defun-sk exists-quotient-map (r s)
  (exists f (and (funp f) (equal (domain f) s)
                 (equal (image f) (quotient r s))
                 (maps-to-classes f r s))))

(chk eqv-class-equal
  (implies (and (equivalence-on r s) (in a s) (in b s))
           (equal (equal (eqv-class a r s) (eqv-class b r s))
                  (in (cons a b) r)))
  :props (zfc prod2$prop eqv-class$prop))
(chk quotient-is-partition
  (implies (equivalence-on r s) (partition-p (quotient r s) s))
  :props (zfc prod2$prop diff$prop eqv-class$prop quotient$prop))
(chk partition-rel-is-equivalence
  (implies (partition-p p s) (equivalence-on (partition-rel p s) s))
  :props (zfc prod2$prop diff$prop partition-rel$prop))
(chk quotient-of-partition-rel
  (implies (partition-p p s) (equal (quotient (partition-rel p s) s) p))
  :props (zfc prod2$prop diff$prop eqv-class$prop quotient$prop partition-rel$prop))
(chk partition-rel-of-quotient
  (implies (equivalence-on r s) (equal (partition-rel (quotient r s) s) r))
  :props (zfc prod2$prop diff$prop eqv-class$prop quotient$prop partition-rel$prop))
(chk quotient-map-exists
  (implies (equivalence-on r s) (exists-quotient-map r s))
  :props (zfc prod2$prop domain$prop inverse$prop eqv-class$prop quotient$prop))

;;; ---------------- B. Cartesian product of a family
(defun-sk choice-fn-p (f fam)
  (forall i (implies (in i (domain fam)) (in (apply f i) (apply fam i)))))
(zsub prod-family (fam) f (fun-space (domain fam) (union (image fam)))
      (choice-fn-p f fam))
(defun-sk nonempty-values (fam)
  (forall i (implies (in i (domain fam)) (not (equal (apply fam i) 0)))))
(defun-sk has-coordinate (fam i y)
  (exists f (and (in f (prod-family fam)) (equal (apply f i) y))))

(chk in-prod-family
  (implies (funp fam)
           (equal (in f (prod-family fam))
                  (and (funp f) (equal (domain f) (domain fam))
                       (choice-fn-p f fam))))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop))
(chk prod-family-empty-iff
  (implies (funp fam)
           (iff (equal (prod-family fam) 0)
                (not (nonempty-values fam))))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop))
(chk projection-surjective
  (implies (and (funp fam) (nonempty-values fam)
                (in i (domain fam)) (in y (apply fam i)))
           (has-coordinate fam i y))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop))
(chk prod-family-binary
  (exists-bijection (prod-family (pair (cons 0 a) (cons 1 b)))
                    (prod2 a b))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop))

;;; ---------------- C. Filters and ultrafilters
(defun-sk upward-closed (u s)
  (forall (x y) (implies (and (in x u) (subset x y) (subset y s)) (in y u))))
(defun-sk int2-closed (u)
  (forall (x y) (implies (and (in x u) (in y u)) (in (int2 x y) u))))
(defun filter-on (u s)
  (and (subset u (powerset s)) (in s u) (not (in 0 u))
       (upward-closed u s) (int2-closed u)))
(defun-sk ultra-p (u s)
  (forall x (implies (subset x s) (or (in x u) (in (diff s x) u)))))
(defun ultrafilter-on (u s)
  (and (filter-on u s) (ultra-p u s)))
(zsub principal-filter (a s) x (powerset s) (in a x))
(defun-sk principal-p (u s)
  (exists a (and (in a s) (equal u (principal-filter a s)))))
(defun-sk maximal-filter-p (u s)
  (forall v (implies (and (filter-on v s) (subset u v)) (equal u v))))
(defun-sk exists-nonprincipal-ultrafilter (s)
  (exists u (and (ultrafilter-on u s) (not (principal-p u s)))))

(chk principal-filter-is-ultrafilter
  (implies (in a s) (ultrafilter-on (principal-filter a s) s))
  :props (zfc diff$prop principal-filter$prop))
(chk ultra-iff-maximal
  (implies (filter-on u s) (iff (ultra-p u s) (maximal-filter-p u s)))
  :props (zfc diff$prop))
(chk ultrafilter-prime
  (implies (and (ultrafilter-on u s) (subset x s) (subset y s)
                (in (union2 x y) u))
           (or (in x u) (in y u)))
  :props (zfc diff$prop))
(chk ultrafilter-with-finite-member-is-principal
  (implies (and (ultrafilter-on u s) (in x u) (finite x))
           (principal-p u s))
  :props (zfc diff$prop principal-filter$prop))
(chk ultrafilter-on-finite-set-is-principal
  (implies (and (ultrafilter-on u s) (finite s))
           (principal-p u s))
  :props (zfc diff$prop principal-filter$prop))
(chk nonprincipal-ultrafilter-exists
  (exists-nonprincipal-ultrafilter (omega))
  :props (zfc diff$prop principal-filter$prop))

;;; ---------------- D. Cardinality basics
(defun-sk injects-into (a b)
  (exists f (and (injective-funp f) (equal (domain f) a) (subset (image f) b))))
(defun-sk eqnum-to-nat (s)
  (exists n (and (natp n) (exists-bijection n s))))

(chk eqnum-reflexive (exists-bijection s s))
(chk eqnum-symmetric
  (implies (exists-bijection a b) (exists-bijection b a))
  :props (zfc prod2$prop domain$prop inverse$prop))
(chk eqnum-transitive
  (implies (and (exists-bijection a b) (exists-bijection b c))
           (exists-bijection a c))
  :props (zfc prod2$prop domain$prop inverse$prop compose$prop))
(chk injects-both-ways-implies-eqnum
  (implies (and (injects-into a b) (injects-into b a))
           (exists-bijection a b))
  :props (sbt-prop))
(chk set-injects-into-powerset (injects-into s (powerset s)))
(chk powerset-does-not-inject (not (injects-into (powerset s) s))
  :props (zfc prod2$prop domain$prop inverse$prop))
(chk pigeonhole
  (implies (natp n) (not (injects-into (+ 1 n) n)))
  :props (zfc prod2$prop domain$prop inverse$prop))
(chk eqnum-naturals-equal
  (implies (and (natp m) (natp n) (exists-bijection m n)) (equal m n))
  :props (zfc prod2$prop domain$prop inverse$prop))
(chk omega-not-finite (not (finite (omega))))
(chk finite-iff-eqnum-to-nat (iff (finite s) (eqnum-to-nat s))
  :props (zfc prod2$prop domain$prop inverse$prop))

;;; ---------------- E. Transfinite recursion
(defstub tr-g (x) t)
(defun-sk tr-step-ok (f)
  (forall b (implies (in b (domain f))
                     (equal (apply f b) (tr-g (restrict f b))))))
(defun tr-fn-p (f a)
  (and (funp f) (equal (domain f) a) (tr-step-ok f)))
(defun-sk tr-exists (a) (exists f (tr-fn-p f a)))
(chk tr-unique
  (implies (and (ordinal-p a) (tr-fn-p f1 a) (tr-fn-p f2 a)) (equal f1 f2))
  :props (zfc domain$prop restrict$prop diff$prop))
(chk tr-existence
  (implies (ordinal-p a) (tr-exists a))
  :props (zfc domain$prop restrict$prop diff$prop))

;;; ---------------- F. Infinite Ramsey
(defun-sk homogeneous (h c k)
  (forall (m n) (implies (and (in m h) (in n h) (< m n))
                         (equal (apply c (cons m n)) k))))
(defun-sk exists-infinite-homogeneous (c)
  (exists (h k) (and (subset h (omega)) (not (finite h)) (homogeneous h c k))))
(chk infinite-ramsey-2
  (implies (and (funp c) (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) 2))
           (exists-infinite-homogeneous c))
  :props (zfc prod2$prop domain$prop inverse$prop))
(chk infinite-ramsey
  (implies (and (natp r) (funp c) (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) r))
           (exists-infinite-homogeneous c))
  :props (zfc prod2$prop domain$prop inverse$prop))

;;; ---------------- G. Topology
(zsub preimage (f v) x (domain f) (in (apply f x) v))
(defun-sk preimages-open (f tp1 tp2)
  (forall v (implies (in v tp2) (in (preimage f v) tp1))))
(defun continuous (f tp1 tp2)
  (and (funp f) (equal (domain f) (union tp1))
       (subset (image f) (union tp2)) (preimages-open f tp1 tp2)))
(chk continuous-compose
  (implies (and (continuous f tp1 tp2) (continuous g tp2 tp3))
           (continuous (compose g f) tp1 tp3))
  :props (zfc prod2$prop domain$prop inverse$prop compose$prop preimage$prop))
(chk continuous-image-of-compact
  (implies (and (tpp tp1) (tpp tp2) (compact tp1) (continuous f tp1 tp2)
                (equal (image f) (union tp2)))
           (compact tp2))
  :props (zfc prod2$prop domain$prop inverse$prop preimage$prop))
(chk hausdorff-singleton-closed
  (implies (and (tpp tp) (hausdorff tp) (in x (union tp)))
           (closed (singleton x) tp))
  :props (zfc diff$prop))
(chk compact-subset-of-hausdorff-is-closed
  (implies (and (tpp tp) (hausdorff tp) (subset s (union tp))
                (compact (subspace s tp)))
           (closed s tp))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop subspace-fn$prop))

;;; ---------------- H. Groups
(defun-sk closed-under-op (h op)
  (forall (x y) (implies (and (in x h) (in y h)) (in (apply2 op x y) h))))
(defun-sk closed-under-inv (h inv)
  (forall x (implies (in x h) (in (apply inv x) h))))
(defun subgroup-p (h s op e inv)
  (and (subset h s) (in e h) (closed-under-op h op) (closed-under-inv h inv)))
(defun-sk all-subgroups (hs s op e inv)
  (forall h (implies (in h hs) (subgroup-p h s op e inv))))
(defun-sk preserves-op (f s1 op1 op2)
  (forall (x y) (implies (and (in x s1) (in y s1))
                         (equal (apply f (apply2 op1 x y))
                                (apply2 op2 (apply f x) (apply f y))))))
(defun group-hom-p (f s1 op1 s2 op2)
  (and (funp f) (equal (domain f) s1) (subset (image f) s2)
       (preserves-op f s1 op1 op2)))
(zsub kernel (f s1 e2) x s1 (equal (apply f x) e2))
(defun-sk normal-in (h s op inv)
  (forall (g x) (implies (and (in g s) (in x h))
                         (in (apply2 op (apply2 op g x) (apply inv g)) h))))
(chk group-identity-unique
  (implies (and (groupp s op e inv) (in e2 s) (group-identity-p s op e2))
           (equal e2 e))
  :props (zfc prod2$prop domain$prop inverse$prop))
(chk group-inverse-unique
  (implies (and (groupp s op e inv) (in x s) (in y s)
                (equal (apply2 op x y) e))
           (equal y (apply inv x)))
  :props (zfc prod2$prop domain$prop inverse$prop))
(chk subgroup-is-group
  (implies (and (groupp s op e inv) (subgroup-p h s op e inv))
           (groupp h (restrict op (prod2 h h)) e (restrict inv h)))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))
(chk intersection-of-subgroups
  (implies (and (groupp s op e inv) (not (equal hs 0))
                (all-subgroups hs s op e inv))
           (subgroup-p (intersection hs) s op e inv))
  :props (zfc prod2$prop domain$prop inverse$prop intersection$prop))
(chk hom-preserves-identity-and-inverse
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (and (equal (apply f e1) e2)
                (implies (in x s1)
                         (equal (apply f (apply inv1 x))
                                (apply inv2 (apply f x))))))
  :props (zfc prod2$prop domain$prop inverse$prop))
(chk kernel-is-normal-subgroup
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (and (subgroup-p (kernel f s1 e2) s1 op1 e1 inv1)
                (normal-in (kernel f s1 e2) s1 op1 inv1)))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))
(chk image-is-subgroup
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (subgroup-p (image f) s2 op2 e2 inv2))
  :props (zfc prod2$prop domain$prop inverse$prop))
(chk injective-iff-trivial-kernel
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (iff (injective-funp f)
                (equal (kernel f s1 e2) (singleton e1))))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

;;; ---------------- I. Fields; complex numbers as pairs
(defun-sk distributive-p (s add mul)
  (forall (x y z)
    (implies (and (in x s) (in y s) (in z s))
             (equal (apply2 mul x (apply2 add y z))
                    (apply2 add (apply2 mul x y) (apply2 mul x z))))))
(defun nonzeros (s zero) (diff s (singleton zero)))
(defun fieldp (s add mul zero one neg recip)
  (and (abelian-group-p s add zero neg)
       (not (equal zero one))
       (equal (domain mul) (prod2 s s))
       (subset (image mul) s)
       (abelian-group-p (nonzeros s zero)
                        (restrict mul (prod2 (nonzeros s zero)
                                             (nonzeros s zero)))
                        one recip)
       (distributive-p s add mul)))
(defun-sk minus-one-not-square (s mul neg one)
  (forall x (implies (in x s)
                     (not (equal (apply2 mul x x) (apply neg one))))))
(defun cx-a (p) (car (car (car p))))  ; p = ((a . b) . (c . d)) . w
(defun cx-b (p) (cdr (car (car p))))
(defun cx-c (p) (car (cdr (car p))))
(defun cx-d (p) (cdr (cdr (car p))))
(zsub c-add (s add) p (prod2 (prod2 (prod2 s s) (prod2 s s)) (prod2 s s))
      (equal (cdr p) (cons (apply2 add (cx-a p) (cx-c p))
                           (apply2 add (cx-b p) (cx-d p)))))
(zsub c-mul (s add mul neg) p
      (prod2 (prod2 (prod2 s s) (prod2 s s)) (prod2 s s))
      (equal (cdr p)
             (cons (apply2 add (apply2 mul (cx-a p) (cx-c p))
                           (apply neg (apply2 mul (cx-b p) (cx-d p))))
                   (apply2 add (apply2 mul (cx-a p) (cx-d p))
                           (apply2 mul (cx-b p) (cx-c p))))))
(zsub c-neg (s neg) p (prod2 (prod2 s s) (prod2 s s))
      (equal (cdr p) (cons (apply neg (car (car p)))
                           (apply neg (cdr (car p))))))
(defun c-norm2 (u add mul)
  (apply2 add (apply2 mul (car u) (car u)) (apply2 mul (cdr u) (cdr u))))
(zsub c-recip (s add mul zero neg recip) p
      (prod2 (diff (prod2 s s) (singleton (cons zero zero))) (prod2 s s))
      (equal (cdr p)
             (cons (apply2 mul (car (car p))
                           (apply recip (c-norm2 (car p) add mul)))
                   (apply2 mul (apply neg (cdr (car p)))
                           (apply recip (c-norm2 (car p) add mul))))))
(chk complex-construction-is-field
  (implies (and (fieldp s add mul zero one neg recip)
                (minus-one-not-square s mul neg one))
           (fieldp (prod2 s s) (c-add s add) (c-mul s add mul neg)
                   (cons zero zero) (cons one zero) (c-neg s neg)
                   (c-recip s add mul zero neg recip)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop restrict$prop
              c-add$prop c-mul$prop c-neg$prop c-recip$prop))
(chk complex-i-squared
  (implies (fieldp s add mul zero one neg recip)
           (equal (apply2 (c-mul s add mul neg) (cons zero one) (cons zero one))
                  (apply (c-neg s neg) (cons one zero))))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop restrict$prop
              c-mul$prop c-neg$prop))
(defun-sk rational-ops-standard (add mul)
  (forall (x y) (implies (and (rationalp x) (rationalp y))
                         (and (equal (apply2 add x y) (+ x y))
                              (equal (apply2 mul x y) (* x y))))))
(defun-sk rationals-field-witness ()
  (exists (add mul neg recip)
    (and (fieldp (rationals) add mul 0 1 neg recip)
         (minus-one-not-square (rationals) mul neg 1)
         (rational-ops-standard add mul))))
(chk rationals-form-field (rationals-field-witness)
  :props (zfc rationals$prop v$prop prod2$prop domain$prop inverse$prop))

;;; ---------------- J. Metric spaces with Dedekind-real distances
(defun-sk dr-valued (d x)
  (forall (a b) (implies (and (in a x) (in b x)) (drp (apply d (cons a b))))))
(defun-sk metric-axioms (d x)
  (forall (a b c)
    (implies (and (in a x) (in b x) (in c x))
             (and (subset (r2dr 0) (apply d (cons a b)))
                  (iff (equal (apply d (cons a b)) (r2dr 0)) (equal a b))
                  (equal (apply d (cons a b)) (apply d (cons b a)))
                  (subset (apply d (cons a c))
                          (dr+ (apply d (cons a b)) (apply d (cons b c))))))))
(defun metric-p (d x)
  (and (funp d) (equal (domain d) (prod2 x x)) (dr-valued d x)
       (metric-axioms d x)))
(defun-sk ball-inside (u a eps d x)
  (forall b (implies (and (in b x) (not (in eps (apply d (cons a b)))))
                     (in b u))))
(defun-sk has-ball (u a d x)
  (exists eps (and (rationalp eps) (< 0 eps) (ball-inside u a eps d x))))
(defun-sk metric-open-p (u d x)
  (forall a (implies (in a u) (has-ball u a d x))))
(zsub metric-topology (d x) u (powerset x) (metric-open-p u d x))
(chk metric-topology-is-topology
  (implies (metric-p d x)
           (and (tpp (metric-topology d x))
                (equal (union (metric-topology d x)) x)))
  :props (zfc prod2$prop diff$prop metric-topology$prop))
(chk metric-topology-is-hausdorff
  (implies (metric-p d x) (hausdorff (metric-topology d x)))
  :props (dr-sum-prop diff$prop metric-topology$prop))
(zsub q-dist () p (prod2 (prod2 (rationals) (rationals)) (powerset (rationals)))
      (equal (cdr p) (r2dr (abs (- (car (car p)) (cdr (car p)))))))
(chk rationals-metric
  (metric-p (q-dist) (rationals))
  :props (dr-sum-prop q-dist$prop))

;;; ---------------- K. Reduced products / ultraproducts (needs A, B, C)
(zsub agree-set (f g i) x i (equal (apply f x) (apply g x)))
(zsub ultra-rel (fam u) q (prod2 (prod-family fam) (prod-family fam))
      (in (agree-set (car q) (cdr q) (domain fam)) u))
(defun ultraproduct (fam u) (quotient (ultra-rel fam u) (prod-family fam)))
(chk reduced-product-relation-is-equivalence
  (implies (and (funp fam) (filter-on u (domain fam)))
           (equivalence-on (ultra-rel fam u) (prod-family fam)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop))
(chk principal-ultraproduct
  (implies (and (funp fam) (nonempty-values fam) (in i0 (domain fam)))
           (exists-bijection
            (ultraproduct fam (principal-filter i0 (domain fam)))
            (apply fam i0)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop
              principal-filter$prop eqv-class$prop quotient$prop))
