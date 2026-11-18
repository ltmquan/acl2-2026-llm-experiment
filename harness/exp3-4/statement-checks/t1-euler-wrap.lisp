(include-book "nonstd/nsa/trig" :dir :system)
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

(defthm euler-product-close-to-basel-series
  (implies (and (posp n) (i-large n))
           (i-close (euler-zeta2-product 2 n)
                    (basel-series 1 n))))

;; variant, assuming the series value as a given
(defthm basel-series-closed-form-close    ; GIVEN (would be supplied)
  (implies (and (posp n) (i-large n))
           (i-close (basel-series 1 n) (/ (expt (acl2-pi) 2) 6))))

(defthm euler-product-zeta-2
  (implies (and (posp n) (i-large n))
           (i-close (euler-zeta2-product 2 n)
                    (/ (expt (acl2-pi) 2) 6))))
))
(assert-event (equal (euler-zeta2-product 2 10) (* 4/3 9/8 25/24 49/48)))
(assert-event (and (<= (basel-series 1 30) (euler-zeta2-product 2 30)) (<= (euler-zeta2-product 2 30) (+ (basel-series 1 30) 1/29))))
(cw "ALL-OK~%")
