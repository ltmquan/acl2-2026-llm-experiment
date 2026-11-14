; Reasoning about lifting of integer binary primitive operations
; in the Kestrel ACL2 Remora interpreter.
;
; Formalization of "Towards Formalizing the Semantics of Lifting Argument
; Frames When Evaluating Remora Expressions" (Gamboa, ACL2-2026).

(in-package "REMORA")

(include-book "helpers")

(include-book "std/lists/prefixp" :dir :system)
(local (include-book "std/lists/top" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (in-theory (enable not-reserrp-when-expr-value-listp
                          not-reserrp-when-expr-valuep
                          expr-valuep-when-result-not-error
                          expr-value-listp-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Pure list lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule repeat-each-of-append
  (equal (repeat-each n (append x y))
         (append (repeat-each n x) (repeat-each n y)))
  :induct (len x)
  :enable repeat-each)

(defrule repeat-each-of-1
  (equal (repeat-each 1 x)
         (true-list-fix x))
  :induct (len x)
  :enable (repeat-each repeat))

(defrule repeat-each-of-repeat
  (equal (repeat-each n (repeat m x))
         (repeat (* (nfix n) (nfix m)) x))
  :induct (repeat m x)
  :enable (repeat-each repeat)
  :prep-lemmas
  ((defrule append-of-repeat-repeat
     (equal (append (repeat n x) (repeat m x))
            (repeat (+ (nfix n) (nfix m)) x))
     :induct (repeat n x)
     :enable repeat)))

(defrule repeat-each-of-repeat-each
  (equal (repeat-each n (repeat-each m x))
         (repeat-each (* (nfix n) (nfix m)) x))
  :induct (len x)
  :enable repeat-each)

(defrule repeat-each-of-list
  (equal (repeat-each n (list x))
         (repeat n x))
  :enable repeat-each)

(defruled append-take-nthcdr-tlf
  (implies (<= (nfix n) (len x))
           (equal (append (take n x) (true-list-fix (nthcdr n x)))
                  (true-list-fix x)))
  :induct (nthcdr n x)
  :enable (take nthcdr))

(defruled chunk-<=-len-when-divides
  (implies (and (posp n)
                (consp x)
                (integerp (/ (len x) n)))
           (<= n (len x)))
  :prep-lemmas
  ((defrule lemma
     (implies (and (posp n) (posp k) (integerp (/ k n)))
              (<= n k))
     :use (:instance acl2::<-*-left-cancel (z n) (x (/ k n)) (y 1))
     :prep-books ((include-book "arithmetic-5/top" :dir :system)))))

(defrule append-all-of-list-split
  (implies (and (posp n)
                (integerp (/ (len x) n)))
           (equal (append-all (list-split x n))
                  (true-list-fix x)))
  :induct (list-split x n)
  :enable (list-split append-all append-take-nthcdr-tlf)
  :hints ('(:use ((:instance chunk-<=-len-when-divides)))))

(defrule nat-list-product-of-prefix
  (implies (and (prefixp a b)
                (nat-listp b))
           (equal (* (nat-list-product a)
                     (nat-list-product (nthcdr (len a) b)))
                  (nat-list-product b)))
  :induct (two-cdrs-induct a b)
  :enable (prefixp nat-list-product nthcdr len)
  :prep-lemmas
  ((defun two-cdrs-induct (a b)
     (if (or (endp a) (endp b))
         nil
       (two-cdrs-induct (cdr a) (cdr b))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Application of a single cell
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled eval-app-cell-when-int-binary
  (implies (and (expr-value-case funcell :primop)
                (primop-value-case (expr-value-primop->val funcell)
                                   :int-binary))
           (equal (eval-app-cell funcell argcell limit)
                  (if (and (integerp limit) (>= limit 2))
                      (expr-value-primop
                       (make-primop-value-int-binary-x
                        :op (primop-value-int-binary->op
                             (expr-value-primop->val funcell))
                        :xval argcell))
                    (reserr :limit))))
  :expand ((eval-app-cell funcell argcell limit)
           (:free (op) (eval-primop-fun op argcell (+ -1 limit))))
  :enable (eval-primop-fun-fo
           primop-value-funp
           primop-value-fun-fo-p))

(defruled eval-app-cell-when-int-binary-x
  (implies (and (expr-value-case funcell :primop)
                (primop-value-case (expr-value-primop->val funcell)
                                   :int-binary-x))
           (equal (eval-app-cell funcell argcell limit)
                  (if (and (integerp limit) (>= limit 2))
                      (int-binary-op-apply
                       (primop-value-int-binary-x->op
                        (expr-value-primop->val funcell))
                       (primop-value-int-binary-x->xval
                        (expr-value-primop->val funcell))
                       argcell)
                    (reserr :limit))))
  :expand ((eval-app-cell funcell argcell limit)
           (:free (op) (eval-primop-fun op argcell (+ -1 limit))))
  :enable (eval-primop-fun-fo
           primop-value-funp
           primop-value-fun-fo-p
           int-binary-op-apply))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; One round trip of eval-app-list
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun eval-app-list-induct (funcells argcells limit)
   (if (or (zp limit) (endp funcells))
       (list argcells)
     (eval-app-list-induct (cdr funcells) (cdr argcells) (1- limit)))))

(defthm eval-app-list-when-primop-binary-and-bases
  (implies (and (list-of-primop-int-binary funcells)
                (list-of-base-values argcells)
                (equal (len funcells) (len argcells))
                (not (reserrp (eval-app-list funcells argcells limit))))
           (equal (eval-app-list funcells argcells limit)
                  (pairwise-curry-binary-fn funcells argcells)))
  :hints (("Goal"
           :induct (eval-app-list-induct funcells argcells limit)
           :expand ((eval-app-list funcells argcells limit))
           :in-theory (enable list-of-primop-int-binary
                              list-of-base-values
                              pairwise-curry-binary-fn
                              eval-app-cell-when-int-binary
                              len))))

(defthm eval-app-list-when-primop-binary-x
  (implies (and (list-of-primop-int-binary-x funcells)
                (equal (len funcells) (len argcells))
                (not (reserrp (eval-app-list funcells argcells limit))))
           (equal (eval-app-list funcells argcells limit)
                  (pairwise-curry-binary-x-fn funcells argcells)))
  :hints (("Goal"
           :induct (eval-app-list-induct funcells argcells limit)
           :expand ((eval-app-list funcells argcells limit))
           :in-theory (enable list-of-primop-int-binary-x
                              pairwise-curry-binary-x-fn
                              eval-app-cell-when-int-binary-x
                              len))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Cells of nested vectors of base values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule list-of-base-values-of-append
  (equal (list-of-base-values (append x y))
         (and (list-of-base-values x)
              (list-of-base-values y)))
  :induct (len x)
  :enable list-of-base-values)

(defruled dims-of-expr-value-when-vector
  (implies (and (expr-value-case val :vector)
                (expr-value-wfp val))
           (equal (dims-of-expr-value val)
                  (cons (len (expr-value-vector->elems val))
                        (dims-of-expr-value
                         (car (expr-value-vector->elems val))))))
  :enable (dims-of-expr-value expr-value-wfp
                              expr-value-list-wfp-alt-def)
  :expand ((check-dims-of-expr-value val)
           (check-dims-of-expr-value-list (expr-value-vector->elems val))))

(defruled wfp-facts-when-vector
  (implies (and (expr-value-case val :vector)
                (expr-value-wfp val))
           (and (expr-value-list-wfp (expr-value-vector->elems val))
                (consp (expr-value-vector->elems val))
                (list-repeatp (dims-of-expr-value-list
                               (expr-value-vector->elems val)))))
  :enable (expr-value-wfp
           dims-of-expr-value-list-when-expr-value-list-wfp
           expr-value-list-wfp-alt-def)
  :expand ((check-dims-of-expr-value val)))

(defruled dims-of-expr-value-when-base-kind
  (implies (expr-value-case val :base)
           (equal (dims-of-expr-value val) nil))
  :enable (dims-of-expr-value check-dims-of-expr-value))

(defruled kind-when-nested
  (implies (expr-is-nested-vectors-of-base-values val)
           (or (equal (expr-value-kind val) :base)
               (equal (expr-value-kind val) :vector)))
  :enable expr-is-nested-vectors-of-base-values
  :rule-classes :forward-chaining)

(defruled dims-of-cadr-when-list-repeatp
  (implies (list-repeatp (dims-of-expr-value-list vals))
           (equal (dims-of-expr-value (cadr vals))
                  (if (consp (cdr vals))
                      (dims-of-expr-value (car vals))
                    (dims-of-expr-value nil))))
  :enable (list-repeatp dims-of-expr-value-list))

(defruled list-repeatp-of-dims-of-cdr
  (implies (list-repeatp (dims-of-expr-value-list vals))
           (list-repeatp (dims-of-expr-value-list (cdr vals))))
  :enable (list-repeatp dims-of-expr-value-list))

(defruled cells-at-depth-in-expr-value-list-when-not-consp
  (implies (not (consp vals))
           (equal (cells-at-depth-in-expr-value-list vals d) nil))
  :enable cells-at-depth-in-expr-value-list)

(defret-mutual cells-at-depth-when-nested
  (defret cells-at-depth-in-expr-value-when-nested
    (implies (and (expr-value-wfp val)
                  (expr-is-nested-vectors-of-base-values val)
                  (equal depth (len (dims-of-expr-value val))))
             (and (not (reserrp cells))
                  (list-of-base-values cells)
                  (equal (len cells)
                         (nat-list-product (dims-of-expr-value val)))))
    :fn cells-at-depth-in-expr-value)
  (defret cells-at-depth-in-expr-value-list-when-nested
    (implies (and (expr-value-list-wfp vals)
                  (expr-list-is-nested-vectors-of-base-values vals)
                  (list-repeatp (dims-of-expr-value-list vals))
                  (equal depth (len (dims-of-expr-value (car vals)))))
             (and (not (reserrp cells))
                  (list-of-base-values cells)
                  (equal (len cells)
                         (* (len vals)
                            (nat-list-product
                             (dims-of-expr-value (car vals)))))))
    :fn cells-at-depth-in-expr-value-list)
  :mutual-recursion cells-at-depth-in-expr-values
  :hints (("Goal"
           :in-theory (enable cells-at-depth-in-expr-value
                              cells-at-depth-in-expr-value-list
                              expr-is-nested-vectors-of-base-values
                              expr-list-is-nested-vectors-of-base-values
                              dims-of-expr-value-when-vector
                              dims-of-expr-value-when-base-kind
                              wfp-facts-when-vector
                              list-of-base-values
                              nat-list-product
                              kind-when-nested
                              dims-of-cadr-when-list-repeatp
                              list-repeatp-of-dims-of-cdr
                              cells-at-depth-in-expr-value-list-when-not-consp
                              not-reserrp-when-expr-value-listp
                              expr-value-listp-when-result-not-error
                              len))))

(defret-mutual pos-listp-dims-when-nested
  (defret pos-listp-of-dims-when-nested
    (implies (and (expr-value-wfp val)
                  yes/no)
             (acl2::pos-listp (dims-of-expr-value val)))
    :fn expr-is-nested-vectors-of-base-values)
  (defret pos-listp-of-car-dims-when-nested-list
    (implies (and (expr-value-list-wfp vals)
                  yes/no)
             (acl2::pos-listp (dims-of-expr-value (car vals))))
    :fn expr-list-is-nested-vectors-of-base-values)
  :mutual-recursion expr-is-nested-vectors-of-base-values
  :hints (("Goal"
           :in-theory (enable expr-is-nested-vectors-of-base-values
                              expr-list-is-nested-vectors-of-base-values
                              dims-of-expr-value-when-vector
                              dims-of-expr-value-when-base-kind
                              wfp-facts-when-vector))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Error propagation (paper, Section 3)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
              (+ -1 depth)))))
  :hints (("Goal"
           :in-theory (enable dims-of-expr-value-when-vector)
           :expand ((:free (d) (cells-at-depth-in-expr-value val d))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Lifting values to frames
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule get-cells-from-expr-value-when-nested
  (implies (and (expr-value-wfp val)
                (expr-is-nested-vectors-of-base-values val))
           (and (not (reserrp (get-cells-from-expr-value val)))
                (expr-value-listp (get-cells-from-expr-value val))
                (list-of-base-values (get-cells-from-expr-value val))
                (equal (len (get-cells-from-expr-value val))
                       (nat-list-product (dims-of-expr-value val)))
                (expr-value-list-wfp (get-cells-from-expr-value val))))
  :enable (get-cells-from-expr-value
           expr-value-listp-when-result-not-error))

(defrule get-cells-from-expr-value-when-primop
  (implies (expr-value-case val :primop)
           (equal (get-cells-from-expr-value val)
                  (list (expr-value-fix val))))
  :enable (get-cells-from-expr-value
           dims-of-expr-value-when-primop
           cells-at-depth-in-expr-value))

(defruled lift-expr-value-to-frame-when-nested
  (implies (and (expr-value-wfp val)
                (expr-is-nested-vectors-of-base-values val)
                (equal frame (dims-of-expr-value val)))
           (equal (lift-expr-value-to-frame val frame pframe)
                  (repeat-each (nat-list-product (nthcdr (len frame) pframe))
                               (get-cells-from-expr-value val))))
  :enable (lift-expr-value-to-frame get-cells-from-expr-value))

(defruled lift-expr-value-to-frame-when-scalar
  (equal (lift-expr-value-to-frame val nil pframe)
         (repeat (nat-list-product pframe) (expr-value-fix val)))
  :enable (lift-expr-value-to-frame cells-at-depth-in-expr-value))

(defrule list-of-primop-int-binary-of-repeat
  (implies (and (expr-value-case f :primop)
                (primop-value-case (expr-value-primop->val f) :int-binary))
           (list-of-primop-int-binary (repeat n f)))
  :induct (repeat n f)
  :enable (repeat list-of-primop-int-binary))

(defruled check-list-suffix-of-nil
  (equal (check-list-suffix x nil)
         (mv t (true-list-fix x)))
  :induct (len x)
  :enable check-list-suffix)

(defruled list-prefix-join-of-nil-and
  (equal (list-prefix-join (list nil x))
         (mv t (true-list-fix x)))
  :enable list-prefix-join)

(defrule nthcdr-of-len-same
  (implies (true-listp x)
           (equal (nthcdr (len x) x) nil))
  :induct (len x)
  :enable (nthcdr len)
  :disable (acl2::nthcdr-of-cdr))

(defrule nthcdr-of-len-same-when-nat-listp
  (implies (nat-listp x)
           (equal (nthcdr (len x) x) nil))
  :enable true-listp-when-nat-listp)

(defrule not-member-0-when-pos-listp
  (implies (acl2::pos-listp x)
           (not (member-equal 0 x)))
  :induct (len x))

(defrule nat-listp-when-pos-listp-local
  (implies (acl2::pos-listp x)
           (nat-listp x))
  :induct (len x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; A single step of eval-app with a binary operator (paper, Section 3)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
                            (1- limit))))
  :hints (("Goal"
           :expand ((eval-app funval argvals limit))
           :in-theory (enable fun-value-param-dims-of-int-binary
                              dims-of-expr-value-when-primop
                              check-list-suffix-of-nil
                              list-prefix-join-of-nil-and
                              lift-expr-value-to-frame-when-scalar
                              lift-expr-value-to-frame-when-nested
                              not-reserrp-when-expr-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Glue: packing cells into an array and taking them apart again
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled chunk-facts-for-list-split
  (implies (and (acl2::pos-listp dims)
                (consp dims)
                (equal (len vals) (nat-list-product dims)))
           (and (posp (* (/ (car dims)) (len vals)))
                (integerp (/ (len vals) (* (/ (car dims)) (len vals))))
                (equal (* (/ (car dims)) (len vals))
                       (nat-list-product (cdr dims)))))
  :enable (nat-list-product posp))

(defrule posp-of-nat-list-product-when-pos-listp
  (implies (acl2::pos-listp x)
           (posp (nat-list-product x)))
  :induct (len x)
  :enable nat-list-product
  :rule-classes (:rewrite :type-prescription))

(defrule expr-value-list-listp-of-list-split-when-divides
  (implies (and (expr-value-listp vals)
                (posp n)
                (integerp (/ (len vals) n)))
           (expr-value-list-listp (list-split vals n)))
  :induct (list-split vals n)
  :enable list-split
  :hints ('(:use ((:instance chunk-<=-len-when-divides (x vals))))))

(defrule divides-len-by-product-of-cdr
  (implies (and (acl2::pos-listp dims)
                (consp dims)
                (equal (len vals) (nat-list-product dims)))
           (integerp (/ (len vals) (nat-list-product (cdr dims)))))
  :enable nat-list-product)

(defret-mutual cells-at-depth-of-expr-value-with-nonempty-dims
  (defret cells-at-depth-of-expr-value-with-nonempty-dims
    (implies (and (acl2::pos-listp dims)
                  (expr-value-listp vals)
                  (equal (len vals) (nat-list-product dims)))
             (equal (cells-at-depth-in-expr-value val (len dims))
                    vals))
    :fn expr-value-with-nonempty-dims)
  (defret cells-at-depth-of-expr-value-list-with-nonempty-dims
    (implies (and (acl2::pos-listp dims)
                  (expr-value-list-listp valss)
                  (all-of-len-p valss (nat-list-product dims)))
             (equal (cells-at-depth-in-expr-value-list vals (len dims))
                    (append-all valss)))
    :fn expr-value-list-with-nonempty-dims)
  :mutual-recursion expr-values-with-nonempty-dims
  :hints (("Goal"
           :in-theory (enable expr-value-with-nonempty-dims
                              expr-value-list-with-nonempty-dims
                              cells-at-depth-in-expr-value
                              cells-at-depth-in-expr-value-list
                              chunk-facts-for-list-split
                              expr-value-list-listp-of-list-split-by-len-over-car-of-dims
                              append-all
                              all-of-len-p
                              list-of-car-when-len-1
                              len))))

(defthm undo-expr-value-with-nonempty-dims-3
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
  :hints (("Goal" :in-theory (enable lift-expr-value-to-frame))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Facts about arrays of curried binary operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule list-split-under-iff
  (iff (list-split vals n)
       (consp vals))
  :use (:instance consp-of-list-split (list vals) (chunk n))
  :disable consp-of-list-split)

(defret-mutual expr-value-first-fun-of-expr-value-with-nonempty-dims
  (defret expr-value-first-fun-of-expr-value-with-nonempty-dims
    (implies (and (acl2::pos-listp dims)
                  (expr-value-listp vals)
                  (equal (len vals) (nat-list-product dims)))
             (equal (expr-value-first-fun val)
                    (expr-value-first-fun (car vals))))
    :fn expr-value-with-nonempty-dims)
  (defret expr-value-first-fun-of-car-expr-value-list-with-nonempty-dims
    (implies (and (acl2::pos-listp dims)
                  (expr-value-list-listp valss)
                  (all-of-len-p valss (nat-list-product dims))
                  (consp valss))
             (equal (expr-value-first-fun (car vals))
                    (expr-value-first-fun (car (car valss)))))
    :fn expr-value-list-with-nonempty-dims)
  :mutual-recursion expr-values-with-nonempty-dims
  :hints (("Goal"
           :in-theory (enable expr-value-with-nonempty-dims
                              expr-value-list-with-nonempty-dims
                              chunk-facts-for-list-split
                              car-of-car-of-list-split
                              consp-when-positive-len
                              all-of-len-p
                              len))
          '(:expand ((:free (x) (expr-value-first-fun (expr-value-vector x)))))))

(defruled fun-value-param-dims-when-first-fun-int-binary-x
  (implies (and (equal (expr-value-first-fun v)
                       (expr-value-first-fun c))
                (expr-value-case c :primop)
                (primop-value-case (expr-value-primop->val c)
                                   :int-binary-x))
           (equal (fun-value-param-dims v)
                  (list nil)))
  :enable (fun-value-param-dims
           expr-value-first-fun
           type-of-primop-value-fun
           primop-value-funp))

(defrule fun-value-param-dims-of-curried-binary-op-vector
  (implies (and (acl2::pos-listp dims)
                (expr-value-listp cells)
                (equal (len cells) (nat-list-product dims))
                (list-of-primop-int-binary-x cells))
           (equal (fun-value-param-dims
                   (expr-value-with-nonempty-dims dims cells))
                  (list nil)))
  :use ((:instance fun-value-param-dims-when-first-fun-int-binary-x
                   (v (expr-value-with-nonempty-dims dims cells))
                   (c (car cells))))
  :enable (list-of-primop-int-binary-x consp-when-positive-len))

(defrule dims-of-expr-value-list-when-list-of-primop-int-binary-x
  (implies (list-of-primop-int-binary-x cells)
           (equal (dims-of-expr-value-list cells)
                  (repeat (len cells) nil)))
  :induct (len cells)
  :enable (list-of-primop-int-binary-x
           dims-of-expr-value-when-primop
           repeat))

(defrule list-of-primop-int-binary-x-of-append
  (equal (list-of-primop-int-binary-x (append x y))
         (and (list-of-primop-int-binary-x x)
              (list-of-primop-int-binary-x y)))
  :induct (len x)
  :enable list-of-primop-int-binary-x)

(defrule list-of-primop-int-binary-x-of-repeat
  (implies (and (expr-value-case f :primop)
                (primop-value-case (expr-value-primop->val f) :int-binary-x))
           (list-of-primop-int-binary-x (repeat n f)))
  :induct (repeat n f)
  :enable (repeat list-of-primop-int-binary-x))

(defrule list-of-primop-int-binary-x-of-repeat-each
  (implies (list-of-primop-int-binary-x x)
           (list-of-primop-int-binary-x (repeat-each n x)))
  :induct (len x)
  :enable (repeat-each list-of-primop-int-binary-x))

(defrule list-of-primop-int-binary-x-of-pairwise-curry-binary-fn
  (list-of-primop-int-binary-x (pairwise-curry-binary-fn funcells argcells))
  :enable (pairwise-curry-binary-fn list-of-primop-int-binary-x))

(defrule expr-value-list-wfp-of-pairwise-curry-binary-fn
  (implies (expr-value-list-wfp argcells)
           (expr-value-list-wfp (pairwise-curry-binary-fn funcells argcells)))
  :enable (pairwise-curry-binary-fn expr-value-list-wfp)
  :prep-lemmas
  ((defrule wfp-of-int-binary-x
     (equal (expr-value-wfp
             (expr-value-primop
              (primop-value-int-binary-x op x)))
            (expr-value-wfp x))
     :enable (expr-value-wfp)
     :expand ((check-dims-of-expr-value
               (expr-value-primop (primop-value-int-binary-x op x)))
              (check-dims-of-primop-value (primop-value-int-binary-x op x))))))

(defrule len-of-pairwise-curry-binary-fn
  (equal (len (pairwise-curry-binary-fn funcells argcells))
         (min (len funcells) (len argcells)))
  :enable (pairwise-curry-binary-fn len))

(defruled pos-listp-of-list-prefix-join-of-two
  (implies (and (mv-nth 0 (list-prefix-join (list a b)))
                (acl2::pos-listp a)
                (acl2::pos-listp b))
           (acl2::pos-listp (mv-nth 1 (list-prefix-join (list a b)))))
  :enable list-prefix-join)

(defruled prefixp-of-list-prefix-join-of-two
  (implies (mv-nth 0 (list-prefix-join (list a b)))
           (and (prefixp a (mv-nth 1 (list-prefix-join (list a b))))
                (prefixp b (mv-nth 1 (list-prefix-join (list a b))))))
  :enable list-prefix-join)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; A single step of eval-app with a vector of curried binary operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled eval-app-when-funval-is-curried-binary-op-vector-raw
  (implies (and (expr-value-listp cells)
                (expr-value-list-wfp cells)
                (list-of-primop-int-binary-x cells)
                (acl2::pos-listp fun-frame)
                (equal (len cells) (nat-list-product fun-frame))
                (equal argval (car argvals))
                (expr-value-wfp argval)
                (expr-valuep argval)
                (expr-is-nested-vectors-of-base-values argval)
                (equal arg-frame (dims-of-expr-value argval))
                (mv-nth 0 (list-prefix-join (list fun-frame arg-frame)))
                (equal pframe
                       (mv-nth 1 (list-prefix-join (list fun-frame arg-frame))))
                (not (reserrp
                      (eval-app (expr-value-with-nonempty-dims fun-frame cells)
                                argvals limit))))
           (b* ((result-cells
                 (eval-app-list
                  (repeat-each (nat-list-product
                                (nthcdr (len fun-frame) pframe))
                               cells)
                  (repeat-each (nat-list-product
                                (nthcdr (len arg-frame) pframe))
                               (get-cells-from-expr-value argval))
                  (1- limit))))
             (and (not (reserrp result-cells))
                  (equal (eval-app (expr-value-with-nonempty-dims fun-frame cells)
                                   argvals limit)
                         (eval-app (expr-value-with-nonempty-dims
                                    pframe result-cells)
                                   (cdr argvals)
                                   (1- limit))))))
  :hints (("Goal"
           :expand ((eval-app (expr-value-with-nonempty-dims fun-frame cells)
                              argvals limit))
           :use ((:instance pos-listp-of-list-prefix-join-of-two
                            (a fun-frame) (b (dims-of-expr-value (car argvals))))
                 (:instance prefixp-of-list-prefix-join-of-two
                            (a fun-frame) (b (dims-of-expr-value (car argvals)))))
           :do-not-induct t
           :in-theory (e/d (check-list-suffix-of-nil
                            true-listp-when-nat-listp
                            lift-expr-value-to-frame-when-nested
                            list-of-primop-int-binary-x
                            car-of-repeat)
                           (eval-app-list-when-primop-binary-x)))))

(defthm eval-app-when-funval-is-curried-binary-op-vector
  (implies (and (expr-value-listp cells)
                (expr-value-list-wfp cells)
                (list-of-primop-int-binary-x cells)
                (acl2::pos-listp fun-frame)
                (equal (len cells) (nat-list-product fun-frame))
                (equal argval (car argvals))
                (expr-value-wfp argval)
                (expr-valuep argval)
                (expr-is-nested-vectors-of-base-values argval)
                (equal arg-frame (dims-of-expr-value argval))
                (mv-nth 0 (list-prefix-join (list fun-frame arg-frame)))
                (equal pframe
                       (mv-nth 1 (list-prefix-join (list fun-frame arg-frame))))
                (not (reserrp
                      (eval-app (expr-value-with-nonempty-dims fun-frame cells)
                                argvals limit))))
           (equal (eval-app (expr-value-with-nonempty-dims fun-frame cells)
                            argvals limit)
                  (eval-app (expr-value-with-nonempty-dims
                             pframe
                             (pairwise-curry-binary-x-fn
                              (repeat-each (nat-list-product
                                            (nthcdr (len fun-frame) pframe))
                                           cells)
                              (repeat-each (nat-list-product
                                            (nthcdr (len arg-frame) pframe))
                                           (get-cells-from-expr-value argval))))
                            (cdr argvals)
                            (1- limit))))
  :hints (("Goal"
           :use ((:instance eval-app-when-funval-is-curried-binary-op-vector-raw)
                 (:instance prefixp-of-list-prefix-join-of-two
                            (a fun-frame) (b (dims-of-expr-value (car argvals))))
                 (:instance nat-list-product-of-prefix
                            (a fun-frame)
                            (b (mv-nth 1 (list-prefix-join
                                          (list fun-frame
                                                (dims-of-expr-value
                                                 (car argvals)))))))
                 (:instance nat-list-product-of-prefix
                            (a (dims-of-expr-value (car argvals)))
                            (b (mv-nth 1 (list-prefix-join
                                          (list fun-frame
                                                (dims-of-expr-value
                                                 (car argvals))))))))
           :do-not-induct t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Pure list reasoning about the pairwise functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pairwise-curry-binary-fn-of-append
  (implies (equal (len a) (len c))
           (equal (pairwise-curry-binary-fn (append a b) (append c d))
                  (append (pairwise-curry-binary-fn a c)
                          (pairwise-curry-binary-fn b d))))
  :induct (two-cdrs a c)
  :enable (pairwise-curry-binary-fn len)
  :prep-lemmas
  ((defun two-cdrs (a b)
     (if (or (endp a) (endp b))
         nil
       (two-cdrs (cdr a) (cdr b))))))

(defrule pairwise-curry-binary-fn-of-repeat-repeat
  (equal (pairwise-curry-binary-fn (repeat n f) (repeat n x))
         (repeat n (expr-value-primop
                    (make-primop-value-int-binary-x
                     :op (primop-value-int-binary->op
                          (expr-value-primop->val f))
                     :xval x))))
  :induct (repeat n f)
  :enable (pairwise-curry-binary-fn repeat))

(defrule repeat-each-of-pairwise-curry-binary-fn
  (implies (equal (len funcells) (len argcells))
           (equal (repeat-each n (pairwise-curry-binary-fn funcells argcells))
                  (pairwise-curry-binary-fn (repeat-each n funcells)
                                            (repeat-each n argcells))))
  :induct (two-cdrs funcells argcells)
  :enable (pairwise-curry-binary-fn repeat-each len)
  :prep-lemmas
  ((defun two-cdrs (a b)
     (if (or (endp a) (endp b))
         nil
       (two-cdrs (cdr a) (cdr b))))))

(defrule pairwise-curry-binary-x-fn-of-pairwise-curry-binary-fn
  (implies (and (expr-value-listp args1)
                (equal (len funcells) (len args1)))
           (equal (pairwise-curry-binary-x-fn
                   (pairwise-curry-binary-fn funcells args1)
                   args2)
                  (pairwise-binary-args-fn funcells args1 args2)))
  :induct (three-cdrs-induct funcells args1 args2)
  :enable (pairwise-curry-binary-fn
           pairwise-curry-binary-x-fn
           pairwise-binary-args-fn
           three-cdrs-induct
           len))

(defruled eval-app-of-nil-args
  (equal (eval-app funval nil limit)
         (if (zp limit)
             (reserr :limit)
           (expr-value-fix funval)))
  :expand ((eval-app funval nil limit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The whole application of a binary operation (paper, Section 3)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled eval-app-when-funval-is-binary-op-and-not-reserrp
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
           (b* ((next (eval-app (expr-value-with-nonempty-dims
                                 pframe
                                 (pairwise-curry-binary-fn funcells
                                                           argcells))
                                (cdr argvals)
                                (1- limit))))
             (and (not (reserrp next))
                  (equal (eval-app funval argvals limit) next))))
  :use eval-app-when-funval-is-binary-op
  :disable eval-app-when-funval-is-binary-op)

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
                                 (get-cells-from-expr-value arg2))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance eval-app-when-funval-is-binary-op-and-not-reserrp
                            (fun-frame nil)
                            (argvals (list arg1 arg2))
                            (argval arg1)
                            (arg-frame (dims-of-expr-value arg1))
                            (pframe (dims-of-expr-value arg1))
                            (funcells (repeat (nat-list-product
                                               (dims-of-expr-value arg1))
                                              funval))
                            (argcells (get-cells-from-expr-value arg1)))
                 (:instance eval-app-when-funval-is-curried-binary-op-vector
                            (fun-frame (dims-of-expr-value arg1))
                            (cells (pairwise-curry-binary-fn
                                    (repeat (nat-list-product
                                             (dims-of-expr-value arg1))
                                            funval)
                                    (get-cells-from-expr-value arg1)))
                            (argvals (list arg2))
                            (argval arg2)
                            (arg-frame (dims-of-expr-value arg2))
                            (pframe pframe)
                            (limit (1- limit)))
                 (:instance nat-list-product-of-prefix
                            (a (dims-of-expr-value arg1))
                            (b pframe))
                 (:instance prefixp-of-list-prefix-join-of-two
                            (a (dims-of-expr-value arg1))
                            (b (dims-of-expr-value arg2)))
                 (:instance nat-listp-of-mv-nth-1-of-list-prefix-join
                            (lists (list (dims-of-expr-value arg1)
                                         (dims-of-expr-value arg2)))))
           :in-theory (e/d (dims-of-expr-value-when-primop
                            lift-expr-value-to-frame-when-scalar
                            lift-expr-value-to-frame-when-nested
                            eval-app-of-nil-args)
                           (eval-app-when-funval-is-binary-op
                            eval-app-when-funval-is-curried-binary-op-vector)))))
