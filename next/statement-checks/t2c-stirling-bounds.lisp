(include-book "arithmetic/factorial" :dir :system)
(include-book "nonstd/nsa/exp" :dir :system)
(include-book "nonstd/nsa/sqrt" :dir :system)
(include-book "nonstd/nsa/trig" :dir :system)

;; r(n) = n! / ( sqrt(n) * n^n * e^(-n) )
(defun stirling-ratio (n)
  (/ (factorial n)
     (* (acl2-sqrt n) (expt n n) (/ (acl2-exp n)))))

(skip-proofs
(defthm stirling-ratio-decreasing
  (implies (posp n)
           (< (stirling-ratio (1+ n)) (stirling-ratio n)))))

(skip-proofs
(defthm stirling-ratio-decrease-bounded
  (implies (posp n)
           (< (stirling-ratio n)
              (* (stirling-ratio (1+ n))
                 (acl2-exp (- (/ (* 12 n)) (/ (* 12 (1+ n))))))))))

;; stretch (uses the asymptotic theorem as a given)
(skip-proofs
(defthm stirling-approximation-to-factorial   ; GIVEN
  (implies (and (natp n) (i-large n))
           (i-close (/ (factorial n)
                       (* (acl2-sqrt (* 2 (acl2-pi))) (expt n n)
                          (/ (acl2-exp n)) (acl2-sqrt n)))
                    1))))
(skip-proofs
(defthm stirling-explicit-bounds
  (implies (posp n)
           (let ((s (* (acl2-sqrt (* 2 (acl2-pi) n)) (expt n n) (/ (acl2-exp n)))))
             (and (< s (factorial n))
                  (< (factorial n) (* s (acl2-exp (/ (* 12 n))))))))))
(cw "ALL-OK~%")
