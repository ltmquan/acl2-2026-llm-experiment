(defun-std int-inductance-integrand (a b m n)
  (if (and (realp a) (realp b) (< a b) (realp m) (realp n))
      (standard-part (riemann-inductance-integrand (make-small-partition a b) m n))
    0))
