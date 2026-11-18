(in-package "ZF")

(include-book "projects/set-theory/top" :dir :system)
(include-book "projects/set-theory/topology/compact" :dir :system)
(include-book "projects/set-theory/topology/normal" :dir :system)
(include-book "projects/set-theory/topology/subspace" :dir :system)
(include-book "projects/set-theory/algebra/groups" :dir :system)
(include-book "projects/set-theory/reals/sum" :dir :system)

(defun-sk homogeneous (h c k)
  (forall (m n) (implies (and (in m h) (in n h) (< m n))
                         (equal (apply c (cons m n)) k))))

(defun-sk exists-infinite-homogeneous (c)
  (exists (h k) (and (subset h (omega)) (not (finite h)) (homogeneous h c k))))
