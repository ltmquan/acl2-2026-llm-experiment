(in-package "ACL2")

(defun basel-series (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      0
    (+ (expt i -2)
       (basel-series (1+ i) n))))

(defun least-divisor-from (k n)
  (declare (xargs :measure (nfix (- (1+ n) k))))
  (if (and (integerp k) (integerp n) (< 1 k) (<= k n))
      (if (integerp (/ n k)) k (least-divisor-from (1+ k) n))
    nil))

(defun primep (n)
  (and (integerp n) (<= 2 n) (equal (least-divisor-from 2 n) n)))

(defun euler-zeta2-product (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      1
    (* (if (primep i) (/ (- 1 (expt i -2))) 1)
       (euler-zeta2-product (1+ i) n))))
