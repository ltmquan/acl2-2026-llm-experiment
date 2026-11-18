; Grader book for tool-definductive, requirement 2 (and base of R1, R3).
; The paper's four definductive calls, verbatim (Sections 3/4, 4.2, footnote 4),
; on the model's /work/definductive.lisp.  The deflabels only delimit the events
; of each call for the R1 checks.

(in-package "ACL2")

(include-book "definductive")
(include-book "grader-utils")

; Section 3
(defstub r (* *) => *) ; uninterpreted, for abstraction

; Section 4
(deflabel grader-before-rtc)
(definductive refl-trans-closure
  :preds ((r* a b))
  :irules ((base ((r x y)) (r* x y))
           (refl () (r* x x))
           (trans ((r* x y) (r* y z)) (r* x z))))
(deflabel grader-after-rtc)

; Section 4.2
(deflabel grader-before-nt)
(definductive nat-trees
  :preds ((nat n) (tree tr) (trees trs))
  :irules (;; natural numbers:
           (zero () (nat 0))
           (succ ((nat n)) (nat (1+ n)))
           ;; trees of natural numbers:
           (leaf ((nat n)) (tree n))
           (branch ((nat n) (trees trs)) (tree (cons n trs)))
           ;; lists of trees of natural numbers:
           (empty () (trees nil))
           (cons ((tree tr) (trees trs)) (trees (cons tr trs)))))
(deflabel grader-after-nt)

; Section 4.2
(deflabel grader-before-eo)
(definductive even-and-odd
  :preds ((even n) (odd n))
  :irules ((zero () (even 0))
           (from-even ((even n)) (odd (1+ n)))
           (from-odd ((odd n)) (even (1+ n)))))
(deflabel grader-after-eo)

; Footnote 4
(deflabel grader-before-j0)
(definductive just-0 :preds ((p x)) :irules ((zero () (p 0))))
(deflabel grader-after-j0)
