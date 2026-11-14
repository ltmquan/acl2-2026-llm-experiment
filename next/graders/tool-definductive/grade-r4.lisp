; Grader book for tool-definductive, requirement 4: invalid definitions are
; rejected.  (grade.sh also runs each bad call at the top level, outside
; must-fail, to check that the error is an ACL2 error, not a raw Lisp error.)
; Each negative test has a positive control that differs only in the premise,
; so that a must-fail does not pass for an unrelated reason.

(in-package "ACL2")

(include-book "definductive")
(include-book "grader-utils")

; Section 4.8, verbatim.
(grader-try r4-no-proof-trees
  (must-fail
   (definductive no-proof-trees
     :preds ((p x))
     :irules ((recurse ((p x)) (p x))))))

; Section 4.8: "Conjunctions like (and (p ...) (q ...)), where p and q are
; predicates being defined, or disjunctions like (or (p ...) (q ...)) ... are
; currently rejected by definductive."
(grader-try r4-and
  (must-fail
   (definductive bad-and
     :preds ((pa x) (qa x))
     :irules ((pa0 () (pa 0))
              (qa0 () (qa 0))
              (both ((and (pa x) (qa x))) (pa (cons x x)))))))

(grader-try r4-or
  (must-fail
   (definductive bad-or
     :preds ((po x) (qo x))
     :irules ((po0 () (po 0))
              (qo0 () (qo 0))
              (either ((or (po x) (qo x))) (po (cons x x)))))))

; "Negations like (not (p ...)) and implications like (implies (p ...) ...)
; violate general positivity and are not expressible in definductive."
(grader-try r4-not
  (must-fail
   (definductive bad-not
     :preds ((pn x))
     :irules ((pn0 () (pn 0))
              (neg ((not (pn x))) (pn (cons x x)))))))

(grader-try r4-implies
  (must-fail
   (definductive bad-implies
     :preds ((pm x) (qm x))
     :irules ((pm0 () (pm 0))
              (qm0 () (qm 0))
              (imp ((implies (pm x) (qm x))) (pm (cons x x)))))))

; Positive controls (same predicates and base rules; the conjunction split
; into two premises, the disjunction into two rules; the not/implies rule
; dropped).
(grader-try r4-controls
  (definductive ctl-and
    :preds ((pa x) (qa x))
    :irules ((pa0 () (pa 0))
             (qa0 () (qa 0))
             (both ((pa x) (qa x)) (pa (cons x x)))))
  (definductive ctl-or
    :preds ((po x) (qo x))
    :irules ((po0 () (po 0))
             (qo0 () (qo 0))
             (either1 ((po x)) (po (cons x x)))
             (either2 ((qo x)) (po (cons x x)))))
  (definductive ctl-not
    :preds ((pn x))
    :irules ((pn0 () (pn 0))))
  (definductive ctl-implies
    :preds ((pm x) (qm x))
    :irules ((pm0 () (pm 0))
             (qm0 () (qm 0))
             (imp ((qm x)) (pm (cons x x))))))

(grader-final)
