;; Grader for tool-remora, R2 (4/5): undo-expr-value-with-nonempty-dims-3 (gamboa-remora, Sec. 3).
;; THEOREM: undo-expr-value-with-nonempty-dims-3
;; The paper's statement, transcribed verbatim (arg2l read as arg2); it must follow :by from the model's
;; theorem of the same name.  The interpreter is included first, so the model's books must use its
;; functions (a model redefinition of eval-app etc. would make the include fail).
;; Variant a: pos-listp read as ACL2::POS-LISTP (the built-in; "REMORA" does not import it, see
;; NOTES.md).  grade.sh accepts variant a or variant b (grade-r2-4b.lisp).
(in-package "REMORA")
(include-book "kestrel/remora/expression-evaluation" :dir :system)
(include-book "grader-model")

(defthm grader-undo-expr-value-with-nonempty-dims-3
  (implies (and (expr-value-listp cells)
                (expr-value-list-wfp cells)
                (acl2::pos-listp frame)
                (equal (len cells)
                       (nat-list-product frame))
                (prefixp frame pframe)
                (not (reserrp
                      (cells-at-depth-in-expr-value
                       (expr-value-with-nonempty-dims frame cells)
                       (len frame)))))
           (equal (lift-expr-value-to-frame
                   (expr-value-with-nonempty-dims frame cells)
                   frame
                   pframe)
                  (repeat-each (nat-list-product
                                (nthcdr (len frame) pframe))
                               cells)))
  :hints (("Goal" :by undo-expr-value-with-nonempty-dims-3))
  :rule-classes nil)
