(in-package "ACL2")

(include-book "nonstd/nsa/trig" :dir :system)
(include-book "nonstd/integrals/integrable-functions" :dir :system)
(include-book "nonstd/integrals/make-partition" :dir :system)

(defun winding-gamma () (* 2/3 (acl2-pi)))

(defun inductance-integrand (x m n)
  (* (acl2-cosine (- x (* m (winding-gamma))))
     (acl2-cosine (- x (* n (winding-gamma))))))

(defun map-inductance-integrand (p m n)
  (if (consp p)
      (cons (inductance-integrand (car p) m n)
            (map-inductance-integrand (cdr p) m n))
    nil))

(defun riemann-inductance-integrand (p m n)
  (dotprod (deltas p) (map-inductance-integrand (cdr p) m n)))
