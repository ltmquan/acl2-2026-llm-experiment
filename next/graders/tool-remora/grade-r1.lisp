;; Grader for tool-remora, R1: the seven helper functions of the paper are defined (not merely constrained),
;; with the arity the paper's statements use (pairwise-curry-binary-x-fn appears in no statement: any arity).
(in-package "REMORA")
(include-book "kestrel/remora/expression-evaluation" :dir :system)
(include-book "grader-model")

(defun grader-defined-p (fn arity wrld)
  (declare (xargs :mode :program))
  (and (acl2::function-symbolp fn wrld)
       (or (null arity) (equal (acl2::arity fn wrld) arity))
       (not (acl2::getpropc fn 'acl2::constrainedp nil wrld))
       (acl2::getpropc fn 'acl2::unnormalized-body nil wrld)
       t))

(assert-event (grader-defined-p 'pairwise-curry-binary-fn 2 (w state)))
(assert-event (grader-defined-p 'pairwise-curry-binary-x-fn nil (w state)))
(assert-event (grader-defined-p 'pairwise-binary-args-fn 3 (w state)))
(assert-event (grader-defined-p 'get-cells-from-expr-value 1 (w state)))
(assert-event (grader-defined-p 'expr-is-nested-vectors-of-base-values 1 (w state)))
(assert-event (grader-defined-p 'list-of-primop-int-binary 1 (w state)))
(assert-event (grader-defined-p 'list-of-base-values 1 (w state)))
