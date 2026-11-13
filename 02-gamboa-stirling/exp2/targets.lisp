; Targets for gamboa-stirling (ACL2(r)).  Statements transcribed from the paper
; (no authors' books exist); line numbers refer to papers/gamboa-stirling.txt.

; stirling-approximation-to-factorial (paper Sec. 5, txt l.814-822):
; n! / (sqrt(2 pi) n^n e^-n sqrt(n)) is infinitely close to 1 for every i-large natural n.
(defthm MAIN-1
  (implies (and (natp n)
                (i-large n))
           (i-close (/ (factorial n)
                       (* (acl2-sqrt (* 2 (acl2-pi)))
                          (expt n n)
                          (/ (acl2-exp n))
                          (acl2-sqrt n)))
                    1)))

; stirling-approximation-to-ln-factorial (paper Sec. 5, txt l.826-832):
; ln n! is infinitely close to ln(n^n) - n + ln sqrt(2 pi n) for every i-large positive n.
(defthm MAIN-2
  (implies (and (posp n)
                (i-large n))
           (i-close (acl2-ln (factorial n))
                    (+ (acl2-ln (expt n n))
                       (- n)
                       (acl2-ln (acl2-sqrt (* 2 (acl2-pi) n)))))))

; wallis-product-convergence (paper Sec. 4, txt l.678-682):
; the standard part of the n-th partial Wallis product is pi/2 for every i-large natural n.
(defthm MAIN-3
  (implies (and (natp n)
                (i-large n))
           (equal (standard-part (wallis-product n))
                  (/ (acl2-pi) 2))))
