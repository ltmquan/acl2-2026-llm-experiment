; tool-erlang grader, requirement 6 (mechanical part): wtree-p and create-wtree are logic-mode
; functions, and the three theorems the prompt names exist after including /work/reduce.lisp.
; Their statements are printed; that they state the three properties of Section 4.2 for the
; constrained scheduler is checked by hand (CHECKLIST.md R6).
(in-package "ACL2")
(include-book "grader-util")
(include-book "../reduce")
(grader-require-fns ("WTREE-P" "CREATE-WTREE"))
(grader-require-thms ("REDUCE-INVARIANT-PRESERVED" "REDUCE-NO-BLOCKED-WORKER" "REDUCE-ROOT-VALUE"))
(value-triple (grader-print-thms '("REDUCE-INVARIANT-PRESERVED" "REDUCE-NO-BLOCKED-WORKER"
                                   "REDUCE-ROOT-VALUE")
                                 (w state)))
