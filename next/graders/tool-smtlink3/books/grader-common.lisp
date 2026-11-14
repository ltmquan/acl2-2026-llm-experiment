; tool-smtlink3 grader: common prelude for the grader books (not a requirement by itself).
(in-package "ACL2")
(include-book "../smtlink" :ttags :all)
(include-book "../examples" :ttags :all)
(include-book "std/testing/must-fail" :dir :system)

; The paper uses x^2-y^2 (Sections 5 and 5.4) without defining it; it is the function of the
; Smtlink 2.0 example, (- (* x x) (* y y)).  Define it only if the model's books did not.
(make-event
 (if (function-symbolp 'x^2-y^2 (w state))
     '(value-triple :x^2-y^2-defined-by-model)
   '(defun x^2-y^2 (x y) (- (* x x) (* y y)))))

; The paper's :smtlink hint (Section 5.4, line 19 of the hint) names the rule
; smt::specialize-unary-rational- (PDF shows exactly that; the encapsulate elides it with "...").
; It is presumably the unary-minus rule, which a model may call specialize-unary-rational--.
; If only the latter exists, introduce the paper's name as a copy so the paper's hint can be used
; verbatim.  If neither exists the paper's hint is ill-formed and the proofs below fail.
(make-event
 (let ((w (w state)))
   (cond ((getpropc 'smt::specialize-unary-rational- 'theorem nil w)
          '(value-triple :paper-name-present))
         ((getpropc 'smt::specialize-unary-rational-- 'theorem nil w)
          `(defthmd smt::specialize-unary-rational-
             ,(getpropc 'smt::specialize-unary-rational-- 'theorem nil w)
             :hints (("Goal" :by smt::specialize-unary-rational--))))
         (t '(value-triple :no-unary-minus-specialization-rule)))))
