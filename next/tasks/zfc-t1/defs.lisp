(in-package "ZF")

(include-book "projects/set-theory/top" :dir :system)
(include-book "projects/set-theory/topology/compact" :dir :system)
(include-book "projects/set-theory/topology/normal" :dir :system)
(include-book "projects/set-theory/topology/subspace" :dir :system)
(include-book "projects/set-theory/algebra/groups" :dir :system)
(include-book "projects/set-theory/reals/sum" :dir :system)

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
