(in-package "ZF")

(include-book "projects/set-theory/top" :dir :system)
(include-book "projects/set-theory/topology/compact" :dir :system)
(include-book "projects/set-theory/topology/normal" :dir :system)
(include-book "projects/set-theory/topology/subspace" :dir :system)
(include-book "projects/set-theory/algebra/groups" :dir :system)
(include-book "projects/set-theory/reals/sum" :dir :system)

(defun-sk choice-fn-p (f fam)
  (forall i (implies (in i (domain fam)) (in (apply f i) (apply fam i)))))

(zsub prod-family (fam) f (fun-space (domain fam) (union (image fam)))
      (choice-fn-p f fam))

(defun-sk nonempty-values (fam)
  (forall i (implies (in i (domain fam)) (not (equal (apply fam i) 0)))))

(defun-sk has-coordinate (fam i y)
  (exists f (and (in f (prod-family fam)) (equal (apply f i) y))))
