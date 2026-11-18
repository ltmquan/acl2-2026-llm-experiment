(skip-proofs (progn
(defun basel-series (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      0
    (+ (expt i -2)
       (basel-series (1+ i) n))))

(defun least-divisor-from (k n)
  (declare (xargs :measure (nfix (- (1+ n) k))))
  (if (and (integerp k) (integerp n) (< 1 k) (<= k n))
      (if (integerp (/ n k))
          k
        (least-divisor-from (1+ k) n))
    nil))

(defun primep (n)
  (and (integerp n)
       (<= 2 n)
       (equal (least-divisor-from 2 n) n)))

;; product, over the primes p with i <= p < n, of 1/(1 - p^-2)
(defun euler-zeta2-product (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      1
    (* (if (primep i) (/ (- 1 (expt i -2))) 1)
       (euler-zeta2-product (1+ i) n))))

(defthm euler-zeta2-product-lower        ; plain-ACL2 content
  (implies (and (integerp n) (<= 2 n))
           (<= (basel-series 1 n) (euler-zeta2-product 2 n))))

(defthm euler-zeta2-product-upper        ; plain-ACL2 content
  (implies (and (integerp n) (<= 2 n))
           (<= (euler-zeta2-product 2 n)
               (+ (basel-series 1 n) (/ (- n 1))))))

))
(defun chk (n) (declare (xargs :measure (nfix (- 80 n)))) (if (or (not (natp n)) (>= n 80)) t (and (<= (basel-series 1 n) (euler-zeta2-product 2 n)) (<= (euler-zeta2-product 2 n) (+ (basel-series 1 n) (/ (- n 1)))) (chk (1+ n)))))
(assert-event (chk 2))
(cw "ALL-OK~%")
