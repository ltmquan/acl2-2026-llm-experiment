(defthm stirling-ratio-decreasing
  (implies (posp n) (< (stirling-ratio (1+ n)) (stirling-ratio n))))

(defthm stirling-ratio-decrease-bounded
  (implies (posp n)
           (< (stirling-ratio n)
              (* (stirling-ratio (1+ n))
                 (acl2-exp (- (/ (* 12 n)) (/ (* 12 (1+ n)))))))))
