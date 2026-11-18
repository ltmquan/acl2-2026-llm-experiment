;; Grader for tool-remora, R1 (meaning of the helpers, so that the R2 theorems are not vacuous): on the
;; Section 2 example [1 2] + [[1 2] [3 4]], the helper predicates hold where the paper's theorems need them,
;; and the helpers compute what the paper says (Sec. 3):
;;  - expr-is-nested-vectors-of-base-values holds of both arguments;
;;  - list-of-primop-int-binary holds of the lifted function cells, list-of-base-values of the argument cells;
;;  - pairwise-curry-binary-fn agrees with eval-app-list on the first Curried step, and
;;    the right-hand side of eval-app-when-funval-is-binary-op-fully (get-cells-from-expr-value,
;;    pairwise-binary-args-fn) gives [[2 3] [5 6]]  (the paper does not fix the representation returned by
;;    get-cells-from-expr-value, so it is checked only through this composition);
;;  - all hypotheses of eval-app-when-funval-is-binary-op-fully hold on the example.
(in-package "REMORA")
(include-book "kestrel/remora/expression-evaluation" :dir :system)
(include-book "grader-model")

(defmacro grader-int (i) `(expr-value-base (base-value-int (int-value ,i))))
(defconst *grader-plus*
  (expr-value-primop (primop-value-int-binary (int-binary-primop-add))))
(defconst *grader-v12* (expr-value-vector (list (grader-int 1) (grader-int 2))))
(defconst *grader-m1234*
  (expr-value-vector (list (expr-value-vector (list (grader-int 1) (grader-int 2)))
                           (expr-value-vector (list (grader-int 3) (grader-int 4))))))
(defconst *grader-m2356*
  (expr-value-vector (list (expr-value-vector (list (grader-int 2) (grader-int 3)))
                           (expr-value-vector (list (grader-int 5) (grader-int 6))))))

(assert-event (expr-is-nested-vectors-of-base-values *grader-v12*))
(assert-event (expr-is-nested-vectors-of-base-values *grader-m1234*))

;; first step of eval-app on [1 2]: function cells (plus plus), argument cells (1 2)
(defconst *grader-funcells* (lift-expr-value-to-frame *grader-plus* nil '(2)))
(defconst *grader-argcells* (lift-expr-value-to-frame *grader-v12* '(2) '(2)))
(assert-event (list-of-primop-int-binary *grader-funcells*))
(assert-event (list-of-base-values *grader-argcells*))
(assert-event (not (reserrp (eval-app-list *grader-funcells* *grader-argcells* 1000))))
(assert-event (equal (pairwise-curry-binary-fn *grader-funcells* *grader-argcells*)
                     (eval-app-list *grader-funcells* *grader-argcells* 1000)))

;; hypotheses of eval-app-when-funval-is-binary-op-fully, with arg1 = [1 2], arg2 = [[1 2] [3 4]]
(assert-event (b* ((funval *grader-plus*) (arg1 *grader-v12*) (arg2 *grader-m1234*) (limit 1000)
                   (arg1-frame (dims-of-expr-value arg1))
                   (arg2-frame (dims-of-expr-value arg2))
                   ((mv ok pframe) (list-prefix-join (list arg1-frame arg2-frame))))
                (and ok
                     (equal pframe '(2 2))
                     (expr-valuep funval) (expr-value-case funval :primop)
                     (primop-value-case (expr-value-primop->val funval) :int-binary)
                     (expr-value-wfp arg1) (expr-valuep arg1) (expr-value-wfp arg2) (expr-valuep arg2)
                     (expr-is-nested-vectors-of-base-values arg1)
                     (expr-is-nested-vectors-of-base-values arg2)
                     (not (reserrp (eval-app funval (list arg1 arg2) limit)))
                     ;; and its right-hand side gives [[2 3] [5 6]]
                     (equal (expr-value-with-nonempty-dims
                             pframe
                             (pairwise-binary-args-fn
                              (repeat-each (nat-list-product pframe)
                                           (get-cells-from-expr-value funval))
                              (repeat-each (nat-list-product (nthcdr (len arg1-frame) pframe))
                                           (get-cells-from-expr-value arg1))
                              (repeat-each (nat-list-product (nthcdr (len arg2-frame) pframe))
                                           (get-cells-from-expr-value arg2))))
                            *grader-m2356*))))
