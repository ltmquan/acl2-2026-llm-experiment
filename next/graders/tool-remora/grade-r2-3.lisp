;; Grader for tool-remora, R2 (3/5): eval-app-when-funval-is-binary-op (gamboa-remora, Sec. 3).
;; THEOREM: eval-app-when-funval-is-binary-op
;; The paper's statement, transcribed verbatim (arg2l read as arg2); it must follow :by from the model's
;; theorem of the same name.  The interpreter is included first, so the model's books must use its
;; functions (a model redefinition of eval-app etc. would make the include fail).
(in-package "REMORA")
(include-book "kestrel/remora/expression-evaluation" :dir :system)
(include-book "grader-model")

(defthm grader-eval-app-when-funval-is-binary-op
  (implies (and (equal fun-frame (dims-of-expr-value funval))
                (expr-valuep funval)
                (expr-value-case funval :primop)
                (primop-value-case (expr-value-primop->val funval)
                                   :int-binary)
                (equal argval (car argvals))
                (expr-value-wfp argval)
                (expr-valuep argval)
                (expr-is-nested-vectors-of-base-values argval)
                (equal arg-frame (dims-of-expr-value argval))
                (equal pframe arg-frame)
                (equal funcells (lift-expr-value-to-frame
                                 funval fun-frame pframe))
                (equal argcells (lift-expr-value-to-frame
                                 argval arg-frame pframe))
                (not (reserrp (eval-app funval argvals limit))))
           (equal (eval-app funval argvals limit)
                  (eval-app (expr-value-with-nonempty-dims
                             pframe
                             (pairwise-curry-binary-fn funcells
                                                       argcells))
                            (cdr argvals)
                            (1- limit))))
  :hints (("Goal" :by eval-app-when-funval-is-binary-op))
  :rule-classes nil)
