;; Grader for tool-remora, R2 (5/5): eval-app-when-funval-is-binary-op-fully (gamboa-remora, Sec. 3).
;; THEOREM: eval-app-when-funval-is-binary-op-fully
;; The paper's statement, transcribed verbatim (arg2l read as arg2); it must follow :by from the model's
;; theorem of the same name.  The interpreter is included first, so the model's books must use its
;; functions (a model redefinition of eval-app etc. would make the include fail).
(in-package "REMORA")
(include-book "kestrel/remora/expression-evaluation" :dir :system)
(include-book "grader-model")

(defthm grader-eval-app-when-funval-is-binary-op-fully
  (implies (and (expr-valuep funval)
                (expr-value-case funval :primop)
                (primop-value-case (expr-value-primop->val funval)
                                   :int-binary)
                (expr-value-wfp arg1)
                (expr-valuep arg1)
                (expr-value-wfp arg2)
                (expr-valuep arg2)
                (expr-is-nested-vectors-of-base-values arg1)
                (expr-is-nested-vectors-of-base-values arg2)
                (equal arg1-frame (dims-of-expr-value arg1))
                (equal arg2-frame (dims-of-expr-value arg2))
                (equal (list-prefix-join (list arg1-frame arg2-frame))
                       (mv t pframe))
                (not
                 (reserrp (eval-app funval (list arg1 arg2) limit))))
           (equal (eval-app funval (list arg1 arg2) limit)
                  (expr-value-with-nonempty-dims
                   pframe
                   (pairwise-binary-args-fn
                    (repeat-each (nat-list-product pframe)
                                 (get-cells-from-expr-value funval))
                    (repeat-each (nat-list-product
                                  (nthcdr (len arg1-frame) pframe))
                                 (get-cells-from-expr-value arg1))
                    (repeat-each (nat-list-product
                                  (nthcdr (len arg2-frame) pframe))
                                 (get-cells-from-expr-value arg2))))))
  :hints (("Goal" :by eval-app-when-funval-is-binary-op-fully))
  :rule-classes nil)
