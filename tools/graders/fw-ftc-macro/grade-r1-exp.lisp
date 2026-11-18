; Grader (R1, hidden test): f = F = acl2-exp on the whole line, with the
; derivative and continuity theorems supplied (proved here from library lemmas).
(in-package "ACL2")
(include-book "nonstd/integrals/ftc-2" :dir :system)
(include-book "def-ftc-integral")
(include-book "grader-ftc-lib")

(include-book "nonstd/nsa/exp" :dir :system) ; defines acl2-exp

; The other library lemmas are included locally, so that only the theorems
; below are added to the world the model's macro runs in.
(encapsulate
  ()
  (local (include-book "nonstd/nsa/derivative-raise" :dir :system)) ; acl2-exp-derivative
  (local (include-book "nonstd/nsa/exp-continuous" :dir :system))   ; exp-continuous-2
  (local (include-book "nonstd/nsa/ln" :dir :system))               ; realp-exp

; realness of the integrand and antiderivative on the domain
(defthm gr-realp-acl2-exp
  (implies (realp x) (realp (acl2-exp x)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use ((:instance realp-exp)))))

; The derivative theorem, in the prompt's form.
(defthm gr-exp-derivative
  (implies (and (standardp x)
                (inside-interval-p x (interval nil nil))
                (inside-interval-p x1 (interval nil nil))
                (i-close x x1)
                (not (= x x1)))
           (i-close (/ (- (acl2-exp x) (acl2-exp x1)) (- x x1))
                    (acl2-exp x)))
  :hints (("Goal" :use ((:instance acl2-exp-derivative (y x1))))))

; The continuity theorem, in the form of rcdfn-prime-continuous in ftc-2.lisp.
(defthm gr-exp-continuous
  (implies (and (standardp x)
                (inside-interval-p x (interval nil nil))
                (i-close x x1)
                (inside-interval-p x1 (interval nil nil)))
           (i-close (acl2-exp x) (acl2-exp x1)))
  :hints (("Goal" :use ((:instance exp-continuous-2 (y x1)))))))

(def-ftc-integral gr-exp
  :integrand acl2-exp
  :antiderivative acl2-exp
  :domain (interval nil nil)
  :derivative-thm gr-exp-derivative
  :continuity-thm gr-exp-continuous)

(gr-check-ftc gr-exp
  :integrand acl2-exp
  :antiderivative acl2-exp
  :domain (interval nil nil))

(defthm grader-gr-exp-value
  (equal (int-gr-exp 0 1) (- (acl2-exp 1) (acl2-exp 0)))
  :hints (("Goal" :use ((:instance int-gr-exp-ftc (a 0) (b 1)))
           :in-theory (e/d (inside-interval-p interval (:e inside-interval-p) (:e interval))
                           (int-gr-exp (:e int-gr-exp) strict-int-gr-exp (:e strict-int-gr-exp))))))
