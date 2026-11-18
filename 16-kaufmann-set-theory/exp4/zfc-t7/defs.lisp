(in-package "ZF")

(include-book "projects/set-theory/top" :dir :system)
(include-book "projects/set-theory/topology/compact" :dir :system)
(include-book "projects/set-theory/topology/normal" :dir :system)
(include-book "projects/set-theory/topology/subspace" :dir :system)
(include-book "projects/set-theory/algebra/groups" :dir :system)
(include-book "projects/set-theory/reals/sum" :dir :system)

(zsub preimage (f v) x (domain f) (in (apply f x) v))

(defun-sk preimages-open (f tp1 tp2)
  (forall v (implies (in v tp2) (in (preimage f v) tp1))))

(defun continuous (f tp1 tp2)
  (and (funp f) (equal (domain f) (union tp1))
       (subset (image f) (union tp2)) (preimages-open f tp1 tp2)))
