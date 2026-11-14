; Grader (R1, hidden test): calls that must be rejected (all three have a wrong
; antiderivative; the third also supplies a derivative theorem about other
; functions).
(in-package "ACL2")
(include-book "nonstd/integrals/ftc-2" :dir :system)
(include-book "def-ftc-integral")
(include-book "std/testing/must-fail" :dir :system)

; wrong antiderivative (x^3 is not an antiderivative of 2x), no theorems supplied
(must-fail
 (def-ftc-integral gr-bad1
   :integrand (lambda (x) (* 2 x))
   :antiderivative (lambda (x) (* x x x))
   :domain (interval nil nil)))

; wrong antiderivative for a symbol integrand
(must-fail
 (def-ftc-integral gr-bad2
   :integrand acl2-cosine
   :antiderivative acl2-cosine
   :domain (interval nil nil)))

; a supplied derivative theorem about other functions (F = 5, f = 0)
(encapsulate
  ()
  (local (include-book "arithmetic/top" :dir :system))
  (local (include-book "nonstd/nsa/nsa" :dir :system))
  (defthm gr-unrelated-thm
  (implies (and (standardp x)
                (inside-interval-p x (interval nil nil))
                (inside-interval-p x1 (interval nil nil))
                (i-close x x1)
                (not (= x x1)))
           (i-close (/ (- 5 5) (- x x1))
                    0))
  :rule-classes nil
  :hints (("Goal" :use ((:instance i-close-reflexive (x 0)))))))

(must-fail
 (def-ftc-integral gr-bad3
   :integrand (lambda (x) (* 3 x))
   :antiderivative (lambda (x) (* x x))
   :domain (interval nil nil)
   :derivative-thm gr-unrelated-thm))
