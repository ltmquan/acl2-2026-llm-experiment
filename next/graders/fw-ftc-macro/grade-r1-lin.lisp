; Grader (R1, hidden test): a lambda integrand, f(x) = 2x, F(x) = x^2 on the
; whole line, no theorems supplied.
(in-package "ACL2")
(include-book "nonstd/integrals/ftc-2" :dir :system)
(include-book "def-ftc-integral")
(include-book "grader-ftc-lib")

(def-ftc-integral gr-lin
  :integrand (lambda (x) (* 2 x))
  :antiderivative (lambda (x) (* x x))
  :domain (interval nil nil))

(gr-check-ftc gr-lin
  :integrand (lambda (x) (* 2 x))
  :antiderivative (lambda (x) (* x x))
  :domain (interval nil nil))

; closed form at concrete endpoints, from int-gr-lin-ftc
(defthm grader-gr-lin-value
  (equal (int-gr-lin 1 3) 8)
  :hints (("Goal" :use ((:instance int-gr-lin-ftc (a 1) (b 3)))
           :in-theory (e/d (inside-interval-p interval (:e inside-interval-p) (:e interval))
                           (int-gr-lin (:e int-gr-lin) strict-int-gr-lin (:e strict-int-gr-lin))))))

(defthm grader-gr-lin-value-reversed
  (equal (int-gr-lin 3 -2) -5)
  :hints (("Goal" :use ((:instance int-gr-lin-ftc (a 3) (b -2)))
           :in-theory (e/d (inside-interval-p interval (:e inside-interval-p) (:e interval))
                           (int-gr-lin (:e int-gr-lin) strict-int-gr-lin (:e strict-int-gr-lin))))))
