; Grader book for tool-definductive, requirement 3 (model's examples.lisp):
; the Section 5 theorems exist in examples.lisp, non-locally, with the paper's
; exact statements.  (check-examples.py checks the hints the paper shows;
; grade-r3-paper.lisp proves the theorems with the paper's hints on the
; model's tool.)

(in-package "ACL2")

(include-book "examples")
(include-book "grader-utils")

; Section 5.1
(grader-formula r3-trans-base-right trans-base-right
  (implies (and (r* x y) (r y z)) (r* x z)))
(grader-formula r3-trans-base-left trans-base-left
  (implies (and (r x y) (r* y z)) (r* x z)))
(grader-formula r3-even-add-2 even-add-2
  (implies (even n) (even (+ 2 n))))
(grader-formula r3-even-add-double even-add-double
  (implies (and (natp m) (even n)) (even (+ (* 2 m) n))))

; Section 5.2
(grader-formula r3-even-when-evenp even-when-evenp
  (implies (and (natp n) (evenp n)) (even n)))
(grader-formula r3-odd-when-oddp odd-when-oddp
  (implies (and (natp n) (oddp n)) (odd n)))
(grader-formula r3-even-of-pred-when-odd even-of-pred-when-odd
  (implies (odd n) (even (1- n))))

; Section 5.3
(grader-formula r3-natp-when-even-proof-validp natp-when-even-proof-validp
  (implies (even-proof-validp proof n) (natp n)))
(grader-formula r3-natp-when-odd-proof-validp natp-when-odd-proof-validp
  (implies (odd-proof-validp proof n) (natp n)))
(grader-formula r3-natp-when-even/odd natp-when-even/odd
  (implies (or (even n) (odd n)) (natp n)))

; Section 5.4: f preserves r, and nothing more is assumed about f.
(grader-formula r3-r-of-f r-of-f
  (implies (r x y) (r (f x) (f y))))
(grader-assert r3-f-constrained
  (and (equal (len (grader-formals 'f (w state))) 1)
       (not (getpropc 'f 'unnormalized-body nil (w state)))
       (grader-set-equal (grader-constraints 'f (w state))
                         (grader-translate-list '((implies (r x y) (r (f x) (f y))))
                                                (w state))))
  "f is not a unary function constrained only by r-of-f (Section 5.4: \"a function f that preserves r\")")
(grader-formula r3-r*-of-f r*-of-f
  (implies (r* a b) (r* (f a) (f b))))

(grader-final)
