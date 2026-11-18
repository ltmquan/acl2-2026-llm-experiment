; tool-erlang grader, requirement 2 (mechanical part): eval-cont-list (the paper's name) exists as a
; unique logic-mode function (in any package) once the model's examples are loaded.  Fuel, out-of-fuel
; status and yielding on receive are checked by hand (CHECKLIST.md R2).
(in-package "ACL2")
(include-book "grader-util")
(include-book "../examples")
(grader-require-fns ("EVAL-CONT-LIST"))
(assert-event (getpropc (grader-logic-fn "EVAL-CONT-LIST" (w state)) 'recursivep nil (w state))
              :msg "eval-cont-list is not recursive")
