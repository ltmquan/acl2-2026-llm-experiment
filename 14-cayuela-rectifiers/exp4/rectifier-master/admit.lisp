(defun-std strict-int-cos (a b)
  (if (and (realp a) (realp b) (< a b))
      (standard-part (riemann-cos (make-small-partition a b)))
    0))

(defun int-cos (a b) (if (<= a b) (strict-int-cos a b) (- (strict-int-cos b a))))

(defun-std strict-int-cos-sq (a b)
  (if (and (realp a) (realp b) (< a b))
      (standard-part (riemann-cos-sq (make-small-partition a b)))
    0))

(defun int-cos-sq (a b) (if (<= a b) (strict-int-cos-sq a b) (- (strict-int-cos-sq b a))))

(defun vdc-integral (vm tt alpha)
  (* vm (/ tt) (int-cos (- alpha (/ tt 2)) (+ alpha (/ tt 2)))))

(defun vrms-integral (vm tt alpha)
  (acl2-sqrt (* (expt vm 2) (/ tt) (int-cos-sq (- alpha (/ tt 2)) (+ alpha (/ tt 2))))))
