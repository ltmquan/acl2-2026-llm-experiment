; tool-erlang grader, requirement 5 (mechanical part): the names the paper fixes for the
; sum_of_nats proof exist after including /work/sum-of-nats.lisp, and the Lisp function sum-of-nats
; computes N(N+1)/2 on 0..30.  The main theorem (evaluation of the Erlang sum_of_nats with a linear
; fuel bound equals the closed form) is checked by hand (CHECKLIST.md R5).
(in-package "ACL2")
(include-book "grader-util")
(include-book "../sum-of-nats")
(grader-require-fns ("SUM-OF-NATS" "SUM-TEST-WORLD-P" "ERL-VAL-INTEGER->VAL" "EVAL-CONT-LIST"))
(assert-event (or (grader-macros "MAKE-ERL-VAL-INTEGER" (w state))
                  (grader-fns "MAKE-ERL-VAL-INTEGER" (w state)))
              :msg "make-erl-val-integer is not defined")

(defun grader-sum-checks (fn k)
  (declare (xargs :mode :program))
  (if (zp k) `((equal (,fn 0) 0))
    (cons `(equal (,fn ,k) ,(/ (+ (* k k) k) 2)) (grader-sum-checks fn (1- k)))))

(make-event
 `(assert-event (and ,@(grader-sum-checks (grader-logic-fn "SUM-OF-NATS" (w state)) 30))
                :msg "sum-of-nats does not compute N(N+1)/2"))
