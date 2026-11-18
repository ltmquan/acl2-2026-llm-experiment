(in-package "ZF")

(include-book "projects/set-theory/top" :dir :system)
(include-book "projects/set-theory/topology/compact" :dir :system)
(include-book "projects/set-theory/topology/normal" :dir :system)
(include-book "projects/set-theory/topology/subspace" :dir :system)
(include-book "projects/set-theory/algebra/groups" :dir :system)
(include-book "projects/set-theory/reals/sum" :dir :system)

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
