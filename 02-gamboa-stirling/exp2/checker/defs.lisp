; Given definitions for gamboa-stirling (ACL2(r) 8.7).
; Paper: "A Mechanical Proof of Stirling's Approximation in ACL2(r)", R. Gamboa.
; The authors' books are not available; the only author definition needed by the
; targets is wallis-product, copied verbatim from the paper (Sec. 4).
; Library functions used by the targets:
;   factorial            arithmetic/factorial (via nonstd/nsa/factorial)
;   acl2-exp             nonstd/nsa/exp
;   acl2-ln              nonstd/nsa/ln
;   acl2-sqrt            nonstd/nsa/sqrt
;   acl2-pi              nonstd/nsa/trig
;   i-close, i-large, standard-part   ACL2(r) primitives

(in-package "ACL2")

(include-book "arithmetic/factorial" :dir :system)
(include-book "nonstd/nsa/factorial" :dir :system)
(include-book "nonstd/nsa/sqrt" :dir :system)
(include-book "nonstd/nsa/exp" :dir :system)
(include-book "nonstd/nsa/ln" :dir :system)
(include-book "nonstd/nsa/trig" :dir :system)

(defun wallis-product (n)
  (if (zp n)
      1
      (* (/ (* 2 n) (1- (* 2 n)))
         (/ (* 2 n) (1+ (* 2 n)))
         (wallis-product (1- n)))))
