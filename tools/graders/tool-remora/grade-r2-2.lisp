;; Grader for tool-remora, R2 (2/5): eval-app-list-when-primop-binary-and-bases (gamboa-remora, Sec. 3).
;; THEOREM: eval-app-list-when-primop-binary-and-bases
;; The paper's statement, transcribed verbatim (arg2l read as arg2); it must follow :by from the model's
;; theorem of the same name.  The interpreter is included first, so the model's books must use its
;; functions (a model redefinition of eval-app etc. would make the include fail).
(in-package "REMORA")
(include-book "kestrel/remora/expression-evaluation" :dir :system)
(include-book "grader-model")

(defthm grader-eval-app-list-when-primop-binary-and-bases
  (implies (and (list-of-primop-int-binary funcells)
                (list-of-base-values argcells)
                (equal (len funcells) (len argcells))
                (not (reserrp (eval-app-list funcells argcells limit))))
           (equal (eval-app-list funcells argcells limit)
                  (pairwise-curry-binary-fn funcells argcells)))
  :hints (("Goal" :by eval-app-list-when-primop-binary-and-bases))
  :rule-classes nil)
