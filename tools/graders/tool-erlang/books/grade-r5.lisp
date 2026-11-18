; tool-erlang grader, requirement 5 (mechanical part).  After including /work/sum-of-nats.lisp:
;  - the paper's names exist: sum-of-nats, sum-test-world-p, erl-val-integer->val, eval-cont-list
;    (logic-mode functions), make-erl-val-integer (macro or function);
;  - a theorem named sum-of-nats-correct exists (its statement is printed; its shape and the linear
;    fuel bound are checked by hand, CHECKLIST.md R5);
;  - the closed form, exactly as the prompt states it, follows by :by from one of the model's
;    theorems: first sum-of-nats-correct, then any theorem of the world mentioning only sum-of-nats
;    and arithmetic.
(in-package "ACL2")
(include-book "grader-util")
(include-book "../sum-of-nats")
(grader-require-fns ("SUM-OF-NATS" "SUM-TEST-WORLD-P" "ERL-VAL-INTEGER->VAL" "EVAL-CONT-LIST"))
(assert-event (or (grader-macros "MAKE-ERL-VAL-INTEGER" (w state))
                  (grader-fns "MAKE-ERL-VAL-INTEGER" (w state)))
              :msg "make-erl-val-integer is not defined")
(grader-require-thms ("SUM-OF-NATS-CORRECT"))
(value-triple (grader-print-thms '("SUM-OF-NATS-CORRECT") (w state)))

(defun grader-closed-form-candidates (wrld fn acc)
  ;; names of theorems whose function symbols are FN plus arithmetic/propositional primitives
  (declare (xargs :mode :program))
  (cond ((endp wrld) acc)
        ((and (eq (cadar wrld) 'theorem)
              (not (eq (cddar wrld) *acl2-property-unbound*))
              (member-eq fn (all-fnnames (cddar wrld)))
              (subsetp-eq (all-fnnames (cddar wrld))
                          (list* fn '(implies if not natp integerp equal binary-* binary-+ unary-/
                                      unary-- < acl2-numberp rationalp zp nfix))))
         (grader-closed-form-candidates (cdr wrld) fn (add-to-set-eq (caar wrld) acc)))
        (t (grader-closed-form-candidates (cdr wrld) fn acc))))

(defun grader-closed-form-attempts (cands fn)
  (declare (xargs :mode :program))
  (if (endp cands) nil
    (cons `(defthm grader-sum-of-nats-closed-form
             (implies (natp n)
                      (equal (,fn n) (/ (+ (* n n) n) 2)))
             :hints (("Goal" :by ,(car cands)))
             :rule-classes nil)
          (grader-closed-form-attempts (cdr cands) fn))))

(make-event
 (let* ((w (w state))
        (fn (grader-logic-fn "SUM-OF-NATS" w))
        (main (grader-thms "SUM-OF-NATS-CORRECT" w))
        (cands (append main (set-difference-eq (grader-closed-form-candidates w fn nil) main))))
   `(:or ,@(grader-closed-form-attempts cands fn)
         (value-triple (er hard 'grader-r5
                           "No theorem of the model gives the closed form of sum-of-nats by :by.")))))
