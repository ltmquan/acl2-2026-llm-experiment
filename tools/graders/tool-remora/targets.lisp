; The five theorems of gamboa-remora (Sec. 3), transcribed verbatim from the PDF, read in package "REMORA".
; Only change: arg2l -> arg2 in eval-app-when-funval-is-binary-op-fully (as the prompt says).
; (pos-listp is discussed in NOTES.md: read in "REMORA" it is not the ACL2 built-in.)
; Data file for grade.sh (diff report); the checks are the :by proofs in grade-r2-*.lisp.
(defthm propagate-not-reserrp-cells-at-depth-in-expr-value-list-when-vector
  (implies (and (equal (expr-value-kind val) :vector)
                (expr-value-wfp val)
                (not
                 (reserrp (cells-at-depth-in-expr-value val depth)))
                (equal depth (len (dims-of-expr-value val))))
           (not
            (reserrp
             (cells-at-depth-in-expr-value-list
              (expr-value-vector->elems val)
              (+ -1 depth))))))

(defthm eval-app-list-when-primop-binary-and-bases
  (implies (and (list-of-primop-int-binary funcells)
                (list-of-base-values argcells)
                (equal (len funcells) (len argcells))
                (not (reserrp (eval-app-list funcells argcells limit))))
           (equal (eval-app-list funcells argcells limit)
                  (pairwise-curry-binary-fn funcells argcells))))

(defthm eval-app-when-funval-is-binary-op
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
                            (1- limit)))))

(defthm undo-expr-value-with-nonempty-dims-3
  (implies (and (expr-value-listp cells)
                (expr-value-list-wfp cells)
                (pos-listp frame)
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
                               cells))))

(defthm eval-app-when-funval-is-binary-op-fully
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
                                 (get-cells-from-expr-value arg2)))))))
