; tool-smtlink3 grader, requirement 3 (part 1, real Z3): a true goal proves, a false goal
; (Z3 answers sat) must fail.  The true goal is the paper's poly-ineq-example (Section 5.4), verbatim
; except for the name; the false goal replaces the constant 3 subtracted in the conclusion by 5
; (counterexample x = 9/10, y = 0).
(in-package "ACL2")
(include-book "grader-common" :ttags :all)

(defthm grader-r3-poly-ineq-example
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

(must-fail
 (defthm grader-r3-poly-ineq-false
   (implies (and (real/rationalp x)
                 (real/rationalp y)
                 (<= (+ (* (/ 9 8) x x) (* y y)) 1)
                 (<= (x^2-y^2 x y) 1))
            (< y
               (- (* 3 (- x (/ 17 8)) (- x (/ 17 8)))
                  5)))
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
