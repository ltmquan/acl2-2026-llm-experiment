; tool-smtlink3 grader, requirement 6 (supplementary check; grade.py also checks examples.lisp).
; The type-terse goal of Section 4.1, (implies (and (integerp y) (= x (* 2 y))) (foo x y)), with no
; type hypothesis on x.  The paper leaves foo unspecified; we use grader-foo, a nonlinear fact true
; for x = 2y over the reals (y^4 < 1 + 4y^4), and the paper's rational translation theory.  The hint
; goal is not given in the paper; we accept "Goal" or "Goal''".
(in-package "ACL2")
(include-book "grader-common" :ttags :all)

(defun grader-foo (x y)
  (< (* y y y y) (+ 1 (* x x y y))))

(make-event
 '(:or
   (defthm grader-type-terse
     (implies (and (integerp y)
                   (= x (* 2 y)))
              (grader-foo x y))
     :hints (("Goal" :smtlink
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
   (defthm grader-type-terse
     (implies (and (integerp y)
                   (= x (* 2 y)))
              (grader-foo x y))
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
                  smt::specialize-unary-rational-/))))))))
