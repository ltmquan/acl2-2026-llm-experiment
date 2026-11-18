; tool-smtlink3 grader, requirement 4: the paper's poly-ineq-example (Section 5.4, PDF page 10),
; statement and :smtlink hint verbatim (only the theorem name changed, so that it is not redundant
; with the model's own poly-ineq-example), proved by the model's tool; and the same goal with its
; hypotheses permuted (reversed), same hint.  grade.py also checks that Z3 was called and answered
; unsat while this book was certified, and that /work/examples.lisp itself contains both proofs.
(in-package "ACL2")
(include-book "grader-common" :ttags :all)

; The Section 5.4 encapsulate: the five SMT real-theory functions are constrained (not defined)
; functions of the paper's arities.
(assert-event
 (let ((w (w state)))
   (and (equal (arity 'smt::rational-+ w) 2)
        (equal (arity 'smt::rational-- w) 1)
        (equal (arity 'smt::rational-* w) 2)
        (equal (arity 'smt::rational-/ w) 1)
        (equal (arity 'smt::rational-< w) 2)
        (getpropc 'smt::rational-+ 'constrainedp nil w)
        (getpropc 'smt::rational-- 'constrainedp nil w)
        (getpropc 'smt::rational-* 'constrainedp nil w)
        (getpropc 'smt::rational-/ 'constrainedp nil w)
        (getpropc 'smt::rational-< 'constrainedp nil w))))

(defthm grader-poly-ineq-example
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (<= (+ (* (/ 9 8) x x) (* y y)) 1)
                (<= (x^2-y^2 x y) 1))
           (< y
              (- (* 3 (- x (/ 17 8)) (- x (/ 17 8)))
                 3)))
  :hints (("Goal''" :smtlink
           (:translation-theory
            (union-theories
             (theory 'minimal-theory)
             '(smt::return-of-rational-+
               smt::return-of-rational--
               smt::return-of-rational-*
               smt::return-of-rational-/
               smt::return-of-rational-<
               smt::specialize-binary-rational-operators
               smt::specialize-unary-rational-
               smt::specialize-unary-rational-/))))))

(defthm grader-poly-ineq-example-permuted
  (implies (and (<= (x^2-y^2 x y) 1)
                (<= (+ (* (/ 9 8) x x) (* y y)) 1)
                (real/rationalp y)
                (real/rationalp x))
           (< y
              (- (* 3 (- x (/ 17 8)) (- x (/ 17 8)))
                 3)))
  :hints (("Goal''" :smtlink
           (:translation-theory
            (union-theories
             (theory 'minimal-theory)
             '(smt::return-of-rational-+
               smt::return-of-rational--
               smt::return-of-rational-*
               smt::return-of-rational-/
               smt::return-of-rational-<
               smt::specialize-binary-rational-operators
               smt::specialize-unary-rational-
               smt::specialize-unary-rational-/))))))
