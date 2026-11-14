; tool-erlang grader, requirement 6 (mechanical part): the names the paper fixes for the reduce
; proof (wtree-p, create-wtree) exist as logic-mode functions after including /work/reduce.lisp.
; The three properties are checked by hand (CHECKLIST.md R6).
(in-package "ACL2")
(include-book "grader-util")
(include-book "../reduce")
(grader-require-fns ("WTREE-P" "CREATE-WTREE"))
