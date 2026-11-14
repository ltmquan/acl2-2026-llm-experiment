(defun-std strict-int-tf (a b)
  (if (and (realp a) (realp b)
           (inside-interval-p a (tf-domain)) (inside-interval-p b (tf-domain))
           (< a b))
      (standard-part (riemann-tf (make-small-partition a b)))
    0))

(defun int-tf (a b) (if (<= a b) (strict-int-tf a b) (- (strict-int-tf b a))))
