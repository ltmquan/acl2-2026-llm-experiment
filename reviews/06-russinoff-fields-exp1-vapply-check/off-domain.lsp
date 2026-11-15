(include-book "solution")
(set-guard-checking :none)
; non-monic p = 2x^2 + 1 over Q. True: x^2 mod p = -1/2; and (x * x) mod p = -1/2
(cw "~%NONMONIC-pmod ~x0~%" (pmod (quote (:q)) (quote (0 0 1)) (quote (1 0 2))))
(cw "~%NONMONIC-mul ~x0~%" (vapply (quote (:q)) (quote (1 0 2)) (quote (0 1)) (quote (0 1))))
; v of the wrong length (3 coefficients) with deg p = 2 over Q, p = x^2 - 2: (1)*(1 0 1) should be 1 + x^2 = 3
(cw "~%WRONGLEN ~x0~%" (vapply (quote (:q)) (quote (-2 0 1)) (quote (1)) (quote (1 0 1))))
