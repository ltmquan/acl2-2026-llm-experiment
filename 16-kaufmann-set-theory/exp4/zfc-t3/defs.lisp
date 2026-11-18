(in-package "ZF")

(include-book "projects/set-theory/top" :dir :system)
(include-book "projects/set-theory/topology/compact" :dir :system)
(include-book "projects/set-theory/topology/normal" :dir :system)
(include-book "projects/set-theory/topology/subspace" :dir :system)
(include-book "projects/set-theory/algebra/groups" :dir :system)
(include-book "projects/set-theory/reals/sum" :dir :system)

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
