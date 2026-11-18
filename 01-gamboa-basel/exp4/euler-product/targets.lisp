(defthm euler-zeta2-product-lower
  (implies (and (integerp n) (<= 2 n))
           (<= (basel-series 1 n) (euler-zeta2-product 2 n))))

(defthm euler-zeta2-product-upper
  (implies (and (integerp n) (<= 2 n))
           (<= (euler-zeta2-product 2 n)
               (+ (basel-series 1 n) (/ (- n 1))))))

(defthm euler-product-close-to-basel-series
  (implies (and (posp n) (i-large n))
           (i-close (euler-zeta2-product 2 n) (basel-series 1 n))))
