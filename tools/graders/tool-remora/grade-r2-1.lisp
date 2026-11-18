;; Grader for tool-remora, R2 (1/5): propagate-not-reserrp-cells-at-depth-in-expr-value-list-when-vector (gamboa-remora, Sec. 3).
;; THEOREM: propagate-not-reserrp-cells-at-depth-in-expr-value-list-when-vector
;; The paper's statement, transcribed verbatim (arg2l read as arg2); it must follow :by from the model's
;; theorem of the same name.  The interpreter is included first, so the model's books must use its
;; functions (a model redefinition of eval-app etc. would make the include fail).
(in-package "REMORA")
(include-book "kestrel/remora/expression-evaluation" :dir :system)
(include-book "grader-model")

(defthm grader-propagate-not-reserrp-cells-at-depth-in-expr-value-list-when-vector
  (implies (and (equal (expr-value-kind val) :vector)
                (expr-value-wfp val)
                (not
                 (reserrp (cells-at-depth-in-expr-value val depth)))
                (equal depth (len (dims-of-expr-value val))))
           (not
            (reserrp
             (cells-at-depth-in-expr-value-list
              (expr-value-vector->elems val)
              (+ -1 depth)))))
  :hints (("Goal" :by propagate-not-reserrp-cells-at-depth-in-expr-value-list-when-vector))
  :rule-classes nil)
