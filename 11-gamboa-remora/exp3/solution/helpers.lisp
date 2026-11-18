; Helper functions for reasoning about lifting of primitive binary operations
; in the Kestrel ACL2 Remora interpreter.
;
; These are the ACL2 functions used in the statements of the theorems of
; "Towards Formalizing the Semantics of Lifting Argument Frames When
; Evaluating Remora Expressions" (Gamboa, ACL2-2026).

(in-package "REMORA")

(include-book "kestrel/remora/evaluation-rules" :dir :system)

(local (in-theory (enable expr-valuep-when-result-not-error
                          expr-value-listp-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Recognizers for lists of cells
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define list-of-primop-int-binary ((funcells expr-value-listp))
  :returns (yes/no booleanp)
  :short "Check if every cell is a (first-stage) integer binary primitive
          operation, e.g. integer addition before any argument is supplied."
  (or (endp funcells)
      (and (expr-value-case (car funcells) :primop)
           (primop-value-case (expr-value-primop->val (car funcells))
                              :int-binary)
           (list-of-primop-int-binary (cdr funcells)))))

(define list-of-primop-int-binary-x ((funcells expr-value-listp))
  :returns (yes/no booleanp)
  :short "Check if every cell is a curried (second-stage) integer binary
          primitive operation, i.e. one that has received its first argument."
  (or (endp funcells)
      (and (expr-value-case (car funcells) :primop)
           (primop-value-case (expr-value-primop->val (car funcells))
                              :int-binary-x)
           (list-of-primop-int-binary-x (cdr funcells)))))

(define list-of-base-values ((argcells expr-value-listp))
  :returns (yes/no booleanp)
  :short "Check if every cell is a base (scalar) value."
  (or (endp argcells)
      (and (expr-value-case (car argcells) :base)
           (list-of-base-values (cdr argcells)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Nested vectors of base values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines expr-is-nested-vectors-of-base-values
  :short "Check if an expression value is a base value
          or a (non-empty) vector of nested vectors of base values."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the ``data'' arrays: scalars, vectors, matrices, etc.
     whose atoms are all base values.  Empty vectors are excluded."))

  (define expr-is-nested-vectors-of-base-values ((val expr-valuep))
    :returns (yes/no booleanp)
    :measure (expr-value-count val)
    (expr-value-case
     val
     :base t
     :vector (expr-list-is-nested-vectors-of-base-values val.elems)
     :otherwise nil))

  (define expr-list-is-nested-vectors-of-base-values ((vals expr-value-listp))
    :returns (yes/no booleanp)
    :measure (expr-value-list-count vals)
    (or (endp vals)
        (and (expr-is-nested-vectors-of-base-values (car vals))
             (expr-list-is-nested-vectors-of-base-values (cdr vals)))))

  :flag-local nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Getting the cells of an expression value
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-cells-from-expr-value ((val expr-valuep))
  :guard (expr-value-wfp val)
  :returns (cells expr-value-list-resultp)
  :short "All the atoms (rank-0 cells) of an expression value,
          in row-major order."
  (cells-at-depth-in-expr-value val (len (dims-of-expr-value val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Integer binary operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-binary-op-apply ((op int-binary-primop)
                             (x expr-valuep)
                             (y expr-valuep))
  :returns (val expr-value-resultp)
  :short "Apply an integer binary primitive operation to two values,
          as the interpreter does in its last (curried) stage."
  (b* ((y (expr-value-fix y)))
    (int-binary-primop-case
     op
     :add (prim-int-add x y)
     :sub (prim-int-sub x y)
     :mul (prim-int-mul x y)
     :div (prim-int-div x y)
     :expt (prim-int-expt x y)
     :mod (prim-int-mod x y)
     :max (prim-int-max x y)
     :min (prim-int-min x y)
     :bit-and (prim-int-bit-and x y)
     :bit-or (prim-int-bit-or x y)
     :bit-xor (prim-int-bit-xor x y)
     :shl (prim-int-shl x y)
     :shr (prim-int-shr x y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Pairwise (map-like) application of binary operations over lists of cells
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pairwise-curry-binary-fn ((funcells expr-value-listp)
                                  (argcells expr-value-listp))
  :guard (list-of-primop-int-binary funcells)
  :returns (vals expr-value-listp)
  :short "Apply each integer binary operation to its first argument,
          producing the list of curried operations."
  (if (or (endp funcells) (endp argcells))
      nil
    (cons (expr-value-primop
           (make-primop-value-int-binary-x
            :op (primop-value-int-binary->op
                 (expr-value-primop->val (car funcells)))
            :xval (car argcells)))
          (pairwise-curry-binary-fn (cdr funcells) (cdr argcells))))
  :guard-hints (("Goal" :in-theory (enable list-of-primop-int-binary))))

(define pairwise-curry-binary-x-fn ((funcells expr-value-listp)
                                    (argcells expr-value-listp))
  :guard (list-of-primop-int-binary-x funcells)
  :returns (vals expr-value-list-resultp)
  :short "Apply each curried integer binary operation to its second argument,
          producing the list of results (or an error)."
  (b* (((when (or (endp funcells) (endp argcells))) nil)
       (op (expr-value-primop->val (car funcells)))
       ((ok val) (int-binary-op-apply (primop-value-int-binary-x->op op)
                                      (primop-value-int-binary-x->xval op)
                                      (car argcells)))
       ((ok vals) (pairwise-curry-binary-x-fn (cdr funcells) (cdr argcells))))
    (cons val vals))
  :guard-hints (("Goal" :in-theory (enable list-of-primop-int-binary-x))))

(define pairwise-binary-args-fn ((funcells expr-value-listp)
                                 (args1 expr-value-listp)
                                 (args2 expr-value-listp))
  :guard (list-of-primop-int-binary funcells)
  :returns (vals expr-value-list-resultp)
  :short "Apply each integer binary operation to both of its arguments
          at once, producing the list of results (or an error)."
  (b* (((when (or (endp funcells) (endp args1) (endp args2))) nil)
       (op (expr-value-primop->val (car funcells)))
       ((ok val) (int-binary-op-apply (primop-value-int-binary->op op)
                                      (car args1)
                                      (car args2)))
       ((ok vals) (pairwise-binary-args-fn (cdr funcells)
                                           (cdr args1)
                                           (cdr args2))))
    (cons val vals))
  :guard-hints (("Goal" :in-theory (enable list-of-primop-int-binary))))
