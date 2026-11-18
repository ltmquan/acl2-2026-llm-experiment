; tool-smtlink3 grader, requirement 3 (part 2): certified by grade.py with a fake z3 first on PATH
; that answers with an (error ...) line and exit status 1.
; The paper's true goal must then FAIL to prove.
(in-package "ACL2")
(include-book "grader-common" :ttags :all)

(must-fail
 (defthm grader-r3-poly-ineq-example-error
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
                smt::specialize-unary-rational-/)))))))
