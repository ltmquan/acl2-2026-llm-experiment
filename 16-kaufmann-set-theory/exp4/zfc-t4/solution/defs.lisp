(in-package "ZF")

(include-book "projects/set-theory/top" :dir :system)
(include-book "projects/set-theory/topology/compact" :dir :system)
(include-book "projects/set-theory/topology/normal" :dir :system)
(include-book "projects/set-theory/topology/subspace" :dir :system)
(include-book "projects/set-theory/algebra/groups" :dir :system)
(include-book "projects/set-theory/reals/sum" :dir :system)

(defun-sk injects-into (a b)
  (exists f (and (injective-funp f) (equal (domain f) a) (subset (image f) b))))

(defun-sk eqnum-to-nat (s)
  (exists n (and (natp n) (exists-bijection n s))))
