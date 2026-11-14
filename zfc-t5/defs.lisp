(in-package "ZF")

(include-book "projects/set-theory/top" :dir :system)
(include-book "projects/set-theory/topology/compact" :dir :system)
(include-book "projects/set-theory/topology/normal" :dir :system)
(include-book "projects/set-theory/topology/subspace" :dir :system)
(include-book "projects/set-theory/algebra/groups" :dir :system)
(include-book "projects/set-theory/reals/sum" :dir :system)

(defstub tr-g (x) t)

(defun-sk tr-step-ok (f)
  (forall b (implies (in b (domain f))
                     (equal (apply f b) (tr-g (restrict f b))))))

(defun tr-fn-p (f a)
  (and (funp f) (equal (domain f) a) (tr-step-ok f)))

(defun-sk tr-exists (a) (exists f (tr-fn-p f a)))
