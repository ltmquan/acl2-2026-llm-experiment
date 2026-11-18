; Grader book for fw-definductive-exec, requirement 1: /work/definductive.lisp
; is a book defining the event macro definductive.  (check-exec.py checks that
; it is a modified copy of the books' file.)
(in-package "ACL2")
(include-book "definductive")
(include-book "grader-utils")
(grader-assert r1-macro
  (getpropc 'definductive 'macro-body nil (w state))
  "definductive.lisp does not define the macro definductive")
(grader-final)
