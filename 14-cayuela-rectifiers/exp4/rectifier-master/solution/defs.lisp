(in-package "ACL2")

(include-book "nonstd/nsa/trig" :dir :system)
(include-book "nonstd/nsa/sqrt" :dir :system)
(include-book "nonstd/integrals/integrable-functions" :dir :system)
(include-book "nonstd/integrals/make-partition" :dir :system)

(defun sa (x) (if (equal x 0) 1 (/ (acl2-sine x) x)))

(defun map-cos (p) (if (consp p) (cons (acl2-cosine (car p)) (map-cos (cdr p))) nil))
(defun riemann-cos (p) (dotprod (deltas p) (map-cos (cdr p))))

(defun map-cos-sq (p)
  (if (consp p) (cons (expt (acl2-cosine (car p)) 2) (map-cos-sq (cdr p))) nil))
(defun riemann-cos-sq (p) (dotprod (deltas p) (map-cos-sq (cdr p))))
