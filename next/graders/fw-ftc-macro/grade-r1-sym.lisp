; Grader (R1, hidden test): symbol integrand and antiderivative (user
; functions), f(x) = 3x^2, F(x) = x^3, on (interval 0 nil), no theorems supplied.
(in-package "ACL2")
(include-book "nonstd/integrals/ftc-2" :dir :system)
(include-book "def-ftc-integral")
(include-book "grader-ftc-lib")

(defun gr-sq3 (x) (* 3 (* x x)))
(defun gr-cube (x) (* x (* x x)))

(def-ftc-integral gr-sym
  :integrand gr-sq3
  :antiderivative gr-cube
  :domain (interval 0 nil))

(gr-check-ftc gr-sym
  :integrand gr-sq3
  :antiderivative gr-cube
  :domain (interval 0 nil))

(defthm grader-gr-sym-value
  (equal (int-gr-sym 0 2) 8)
  :hints (("Goal" :use ((:instance int-gr-sym-ftc (a 0) (b 2)))
           :in-theory (e/d (inside-interval-p interval (:e inside-interval-p) (:e interval))
                           (int-gr-sym (:e int-gr-sym) strict-int-gr-sym (:e strict-int-gr-sym))))))
