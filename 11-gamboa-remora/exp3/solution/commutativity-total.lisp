; A stronger form of the commutativity corollary:
; if (+ a b) evaluates without error, so does (+ b a), with the same value.

(in-package "REMORA")

(include-book "commutativity")

(local (include-book "std/lists/top" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (in-theory (enable not-reserrp-when-expr-value-listp
                          not-reserrp-when-expr-valuep
                          expr-valuep-when-result-not-error
                          expr-value-listp-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define list-of-int-values ((cells expr-value-listp))
  :returns (yes/no booleanp)
  :short "Check if every cell is an integer base value."
  (or (endp cells)
      (and (expr-value-case (car cells) :base)
           (base-value-case (expr-value-base->val (car cells)) :int)
           (list-of-int-values (cdr cells)))))

(local
 (defun eval-app-list-induct2 (funcells argcells limit)
   (if (or (zp limit) (endp funcells))
       (list argcells)
     (eval-app-list-induct2 (cdr funcells) (cdr argcells) (1- limit)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; How much limit eval-app-list needs

(defruled limit-when-eval-app-list-of-int-binary-x-not-reserrp
  (implies (and (list-of-primop-int-binary-x funcells)
                (consp funcells)
                (not (reserrp (eval-app-list funcells argcells limit))))
           (and (integerp limit)
                (<= (+ 2 (len funcells)) limit)))
  :induct (eval-app-list-induct2 funcells argcells limit)
  :expand ((eval-app-list funcells argcells limit))
  :enable (list-of-primop-int-binary-x
           eval-app-cell-when-int-binary-x
           len))

(defrule eval-app-list-of-int-binary-not-reserrp
  (implies (and (list-of-primop-int-binary funcells)
                (expr-value-list-wfp argcells)
                (<= (len funcells) (len argcells))
                (integerp limit)
                (<= (+ 2 (len funcells)) limit))
           (not (reserrp (eval-app-list funcells argcells limit))))
  :induct (eval-app-list-induct2 funcells argcells limit)
  :expand ((eval-app-list funcells argcells limit))
  :enable (list-of-primop-int-binary
           eval-app-cell-when-int-binary
           len))

(define list-of-int-add-x-cells ((funcells expr-value-listp))
  :returns (yes/no booleanp)
  :short "Check if every cell is a curried integer addition
          whose stored first argument is an integer."
  (or (endp funcells)
      (and (expr-value-case (car funcells) :primop)
           (primop-value-case (expr-value-primop->val (car funcells))
                              :int-binary-x)
           (int-binary-primop-case
            (primop-value-int-binary-x->op
             (expr-value-primop->val (car funcells)))
            :add)
           (b* ((x (primop-value-int-binary-x->xval
                    (expr-value-primop->val (car funcells)))))
             (and (expr-value-case x :base)
                  (base-value-case (expr-value-base->val x) :int)))
           (list-of-int-add-x-cells (cdr funcells)))))

(defrule eval-app-list-of-int-add-x-not-reserrp
  (implies (and (list-of-int-add-x-cells funcells)
                (expr-value-list-wfp argcells)
                (list-of-int-values argcells)
                (<= (len funcells) (len argcells))
                (integerp limit)
                (<= (+ 2 (len funcells)) limit))
           (not (reserrp (eval-app-list funcells argcells limit))))
  :induct (eval-app-list-induct2 funcells argcells limit)
  :expand ((eval-app-list funcells argcells limit))
  :enable (list-of-int-add-x-cells
           list-of-int-values
           eval-app-cell-when-int-binary-x
           int-binary-op-apply
           prim-int-add
           check-expr-value-int
           len))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; List facts

(defrule list-of-int-values-of-append
  (equal (list-of-int-values (append x y))
         (and (list-of-int-values x)
              (list-of-int-values y)))
  :induct (len x)
  :enable list-of-int-values)

(defrule list-of-int-values-of-repeat
  (implies (and (expr-value-case x :base)
                (base-value-case (expr-value-base->val x) :int))
           (list-of-int-values (repeat n x)))
  :induct (repeat n x)
  :enable (repeat list-of-int-values))

(defrule list-of-int-values-of-repeat-each
  (implies (posp n)
           (equal (list-of-int-values (repeat-each n x))
                  (list-of-int-values x)))
  :induct (len x)
  :enable (repeat-each list-of-int-values repeat))

(defrule int-values-when-pairwise-binary-args-fn-of-add-not-reserrp
  (implies (and (list-of-primop-int-add funcells)
                (expr-value-listp args1)
                (expr-value-listp args2)
                (equal (len funcells) (len args1))
                (equal (len funcells) (len args2))
                (not (reserrp (pairwise-binary-args-fn funcells args1 args2))))
           (and (list-of-int-values args1)
                (list-of-int-values args2)))
  :induct (three-cdrs-induct funcells args1 args2)
  :enable (three-cdrs-induct
           pairwise-binary-args-fn
           list-of-primop-int-add
           list-of-int-values
           int-binary-op-apply
           prim-int-add
           check-expr-value-int
           len))

(defrule pairwise-binary-args-fn-of-add-when-int-values
  (implies (and (list-of-primop-int-add funcells)
                (list-of-int-values args1)
                (list-of-int-values args2))
           (b* ((vals (pairwise-binary-args-fn funcells args1 args2)))
             (and (not (reserrp vals))
                  (list-of-int-values vals)
                  (expr-value-list-wfp vals)
                  (equal (len vals)
                         (min (len funcells) (min (len args1) (len args2)))))))
  :induct (three-cdrs-induct funcells args1 args2)
  :enable (three-cdrs-induct
           pairwise-binary-args-fn
           list-of-primop-int-add
           list-of-int-values
           int-binary-op-apply
           prim-int-add
           check-expr-value-int
           len))

(defrule dims-of-expr-value-list-when-list-of-int-values
  (implies (list-of-int-values cells)
           (equal (dims-of-expr-value-list cells)
                  (repeat (len cells) nil)))
  :induct (len cells)
  :enable (list-of-int-values
           dims-of-expr-value-when-base-kind
           repeat))

(defrule list-of-int-add-x-cells-of-pairwise-curry-binary-fn
  (implies (and (list-of-primop-int-add funcells)
                (list-of-int-values argcells))
           (list-of-int-add-x-cells
            (pairwise-curry-binary-fn funcells argcells)))
  :induct (three-cdrs-induct funcells argcells argcells)
  :enable (three-cdrs-induct
           pairwise-curry-binary-fn
           list-of-primop-int-add
           list-of-int-values
           list-of-int-add-x-cells))

(defrule list-of-primop-int-binary-when-list-of-primop-int-add
  (implies (list-of-primop-int-add funcells)
           (list-of-primop-int-binary funcells))
  :induct (len funcells)
  :enable (list-of-primop-int-add list-of-primop-int-binary))

(defrule posp-of-nat-list-product-of-nthcdr-when-pos-listp
  (implies (acl2::pos-listp x)
           (posp (nat-list-product (nthcdr n x))))
  :induct (nthcdr n x)
  :enable nthcdr)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pairwise-curry-binary-fn-under-iff
  (iff (pairwise-curry-binary-fn funcells argcells)
       (and (consp funcells) (consp argcells)))
  :enable pairwise-curry-binary-fn)

(defrule consp-of-repeat-each
  (equal (consp (repeat-each n x))
         (and (posp n) (consp x)))
  :enable (repeat-each repeat))

(defrule consp-of-get-cells-when-nested
  (implies (and (expr-value-wfp val)
                (expr-is-nested-vectors-of-base-values val))
           (consp (get-cells-from-expr-value val)))
  :use ((:instance get-cells-from-expr-value-when-nested))
  :disable get-cells-from-expr-value-when-nested
  :enable consp-when-positive-len)

(defrule nat-list-product-of-prefix-commuted
  (implies (and (prefixp a b)
                (nat-listp b))
           (equal (* (nat-list-product (nthcdr (len a) b))
                     (nat-list-product a))
                  (nat-list-product b)))
  :use nat-list-product-of-prefix
  :disable nat-list-product-of-prefix)

(defrule len-of-pairwise-curry-binary-x-fn-when-not-reserrp
  (implies (not (reserrp (pairwise-curry-binary-x-fn funcells argcells)))
           (equal (len (pairwise-curry-binary-x-fn funcells argcells))
                  (min (len funcells) (len argcells))))
  :induct (three-cdrs-induct funcells argcells argcells)
  :enable (three-cdrs-induct pairwise-curry-binary-x-fn len))

(defruled not-reserrp-of-pairwise-curry-binary-x-fn-when-eval-app-list
  (implies (and (list-of-primop-int-binary-x funcells)
                (equal (len funcells) (len argcells))
                (not (reserrp (eval-app-list funcells argcells limit))))
           (not (reserrp (pairwise-curry-binary-x-fn funcells argcells))))
  :use eval-app-list-when-primop-binary-x
  :disable eval-app-list-when-primop-binary-x)

(defruled int-values-from-curried-step
  (implies (and (expr-value-case funval :primop)
                (primop-value-case (expr-value-primop->val funval)
                                   :int-binary)
                (int-binary-primop-case
                 (primop-value-int-binary->op (expr-value-primop->val funval))
                 :add)
                (expr-value-listp cells1)
                (expr-value-listp cells2)
                (posp k1)
                (posp k2)
                (equal (* k1 (len cells1)) (* k2 (len cells2)))
                (not (reserrp
                      (pairwise-curry-binary-x-fn
                       (repeat-each k1 (pairwise-curry-binary-fn
                                        (repeat (len cells1) funval)
                                        cells1))
                       (repeat-each k2 cells2)))))
           (and (list-of-int-values cells1)
                (list-of-int-values cells2)))
  :use ((:instance int-values-when-pairwise-binary-args-fn-of-add-not-reserrp
                   (funcells (repeat (* k1 (len cells1)) funval))
                   (args1 (repeat-each k1 cells1))
                   (args2 (repeat-each k2 cells2))))
  :disable int-values-when-pairwise-binary-args-fn-of-add-not-reserrp)

(defruled facts-from-curried-eval-app-list
  (implies (and (expr-value-case funval :primop)
                (primop-value-case (expr-value-primop->val funval)
                                   :int-binary)
                (int-binary-primop-case
                 (primop-value-int-binary->op (expr-value-primop->val funval))
                 :add)
                (expr-value-listp cells1)
                (expr-value-listp cells2)
                (consp cells1)
                (posp k1)
                (posp k2)
                (equal (* k1 (len cells1)) (* k2 (len cells2)))
                (not (reserrp
                      (eval-app-list
                       (repeat-each k1 (pairwise-curry-binary-fn
                                        (repeat (len cells1) funval)
                                        cells1))
                       (repeat-each k2 cells2)
                       lim))))
           (and (list-of-int-values cells1)
                (list-of-int-values cells2)
                (integerp lim)
                (<= (+ 2 (* k1 (len cells1))) lim)))
  :use ((:instance not-reserrp-of-pairwise-curry-binary-x-fn-when-eval-app-list
                   (funcells (repeat-each k1 (pairwise-curry-binary-fn
                                              (repeat (len cells1) funval)
                                              cells1)))
                   (argcells (repeat-each k2 cells2))
                   (limit lim))
        (:instance limit-when-eval-app-list-of-int-binary-x-not-reserrp
                   (funcells (repeat-each k1 (pairwise-curry-binary-fn
                                              (repeat (len cells1) funval)
                                              cells1)))
                   (argcells (repeat-each k2 cells2))
                   (limit lim))
        (:instance int-values-from-curried-step))
  :disable (repeat-each-of-pairwise-curry-binary-fn
            eval-app-list-when-primop-binary-x
            pairwise-curry-binary-x-fn-of-pairwise-curry-binary-fn))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; What a successful addition tells us

(defruled facts-when-eval-app-of-int-add-not-reserrp
  (implies (and (expr-valuep funval)
                (expr-value-case funval :primop)
                (primop-value-case (expr-value-primop->val funval)
                                   :int-binary)
                (int-binary-primop-case
                 (primop-value-int-binary->op (expr-value-primop->val funval))
                 :add)
                (expr-value-wfp arg1)
                (expr-valuep arg1)
                (expr-value-wfp arg2)
                (expr-valuep arg2)
                (expr-is-nested-vectors-of-base-values arg1)
                (expr-is-nested-vectors-of-base-values arg2)
                (mv-nth 0 (list-prefix-join (list (dims-of-expr-value arg1)
                                                  (dims-of-expr-value arg2))))
                (not (reserrp (eval-app funval (list arg1 arg2) limit))))
           (and (integerp limit)
                (<= (+ 4 (nat-list-product
                          (mv-nth 1 (list-prefix-join
                                     (list (dims-of-expr-value arg1)
                                           (dims-of-expr-value arg2))))))
                    limit)
                (list-of-int-values (get-cells-from-expr-value arg1))
                (list-of-int-values (get-cells-from-expr-value arg2))))
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
                 (:instance eval-app-when-funval-is-curried-binary-op-vector-raw
                            (fun-frame (dims-of-expr-value arg1))
                            (cells (pairwise-curry-binary-fn
                                    (repeat (nat-list-product
                                             (dims-of-expr-value arg1))
                                            funval)
                                    (get-cells-from-expr-value arg1)))
                            (argvals (list arg2))
                            (argval arg2)
                            (arg-frame (dims-of-expr-value arg2))
                            (pframe (mv-nth 1 (list-prefix-join
                                               (list (dims-of-expr-value arg1)
                                                     (dims-of-expr-value arg2)))))
                            (limit (1- limit)))
                 (:instance facts-from-curried-eval-app-list
                            (cells1 (get-cells-from-expr-value arg1))
                            (cells2 (get-cells-from-expr-value arg2))
                            (k1 (nat-list-product
                                 (nthcdr (len (dims-of-expr-value arg1))
                                         (mv-nth 1 (list-prefix-join
                                                    (list (dims-of-expr-value arg1)
                                                          (dims-of-expr-value arg2)))))))
                            (k2 (nat-list-product
                                 (nthcdr (len (dims-of-expr-value arg2))
                                         (mv-nth 1 (list-prefix-join
                                                    (list (dims-of-expr-value arg1)
                                                          (dims-of-expr-value arg2)))))))
                            (lim (+ -2 limit)))
                 (:instance nat-list-product-of-prefix
                            (a (dims-of-expr-value arg1))
                            (b (mv-nth 1 (list-prefix-join
                                          (list (dims-of-expr-value arg1)
                                                (dims-of-expr-value arg2))))))
                 (:instance nat-list-product-of-prefix
                            (a (dims-of-expr-value arg2))
                            (b (mv-nth 1 (list-prefix-join
                                          (list (dims-of-expr-value arg1)
                                                (dims-of-expr-value arg2))))))
                 (:instance prefixp-of-list-prefix-join-of-two
                            (a (dims-of-expr-value arg1))
                            (b (dims-of-expr-value arg2)))
                 (:instance pos-listp-of-list-prefix-join-of-two
                            (a (dims-of-expr-value arg1))
                            (b (dims-of-expr-value arg2)))
                 (:instance nat-listp-of-mv-nth-1-of-list-prefix-join
                            (lists (list (dims-of-expr-value arg1)
                                         (dims-of-expr-value arg2)))))
           :in-theory (e/d (dims-of-expr-value-when-primop
                            lift-expr-value-to-frame-when-scalar
                            lift-expr-value-to-frame-when-nested
                            consp-when-positive-len)
                           (eval-app-when-funval-is-binary-op
                            eval-app-when-funval-is-curried-binary-op-vector
                            eval-app-when-funval-is-binary-op-fully
                            eval-app-of-int-add-commutative
                            eval-app-list-when-primop-binary-x
                            repeat-each-of-pairwise-curry-binary-fn
                            pairwise-curry-binary-x-fn-of-pairwise-curry-binary-fn)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; When an addition succeeds

(defrule dims-of-car-of-pairwise-curry-binary-fn
  (equal (dims-of-expr-value (car (pairwise-curry-binary-fn funcells argcells)))
         nil)
  :enable (pairwise-curry-binary-fn dims-of-expr-value-when-primop)
  :expand ((pairwise-curry-binary-fn funcells argcells)))

(defruled nat-list-product-of-prefix-bound
  (implies (and (prefixp a b)
                (acl2::pos-listp b))
           (<= (nat-list-product a) (nat-list-product b)))
  :use ((:instance nat-list-product-of-prefix)
        (:instance posp-of-nat-list-product-of-nthcdr-when-pos-listp
                   (x b) (n (len a))))
  :disable (nat-list-product-of-prefix
            nat-list-product-of-prefix-commuted
            posp-of-nat-list-product-of-nthcdr-when-pos-listp)
  :rule-classes :linear)

(defruled eval-app-of-int-add-not-reserrp
  (implies (and (expr-valuep funval)
                (expr-value-case funval :primop)
                (primop-value-case (expr-value-primop->val funval)
                                   :int-binary)
                (int-binary-primop-case
                 (primop-value-int-binary->op (expr-value-primop->val funval))
                 :add)
                (expr-value-wfp arg1)
                (expr-valuep arg1)
                (expr-value-wfp arg2)
                (expr-valuep arg2)
                (expr-is-nested-vectors-of-base-values arg1)
                (expr-is-nested-vectors-of-base-values arg2)
                (list-of-int-values (get-cells-from-expr-value arg1))
                (list-of-int-values (get-cells-from-expr-value arg2))
                (mv-nth 0 (list-prefix-join (list (dims-of-expr-value arg1)
                                                  (dims-of-expr-value arg2))))
                (integerp limit)
                (<= (+ 4 (nat-list-product
                          (mv-nth 1 (list-prefix-join
                                     (list (dims-of-expr-value arg1)
                                           (dims-of-expr-value arg2))))))
                    limit))
           (not (reserrp (eval-app funval (list arg1 arg2) limit))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((eval-app funval (list arg1 arg2) limit)
                    (:free (fv) (eval-app fv (list arg2) (+ -1 limit))))
           :use ((:instance nat-list-product-of-prefix
                            (a (dims-of-expr-value arg1))
                            (b (mv-nth 1 (list-prefix-join
                                          (list (dims-of-expr-value arg1)
                                                (dims-of-expr-value arg2))))))
                 (:instance nat-list-product-of-prefix
                            (a (dims-of-expr-value arg2))
                            (b (mv-nth 1 (list-prefix-join
                                          (list (dims-of-expr-value arg1)
                                                (dims-of-expr-value arg2))))))
                 (:instance nat-list-product-of-prefix-bound
                            (a (dims-of-expr-value arg1))
                            (b (mv-nth 1 (list-prefix-join
                                          (list (dims-of-expr-value arg1)
                                                (dims-of-expr-value arg2))))))
                 (:instance prefixp-of-list-prefix-join-of-two
                            (a (dims-of-expr-value arg1))
                            (b (dims-of-expr-value arg2)))
                 (:instance pos-listp-of-list-prefix-join-of-two
                            (a (dims-of-expr-value arg1))
                            (b (dims-of-expr-value arg2)))
                 (:instance nat-listp-of-mv-nth-1-of-list-prefix-join
                            (lists (list (dims-of-expr-value arg1)
                                         (dims-of-expr-value arg2)))))
           :in-theory (e/d (fun-value-param-dims-of-int-binary
                            dims-of-expr-value-when-primop
                            check-list-suffix-of-nil
                            list-prefix-join-of-nil-and
                            true-listp-when-nat-listp
                            lift-expr-value-to-frame-when-scalar
                            lift-expr-value-to-frame-when-nested
                            eval-app-of-nil-args
                            consp-when-positive-len)
                           (eval-app-when-funval-is-binary-op
                            eval-app-when-funval-is-curried-binary-op-vector
                            eval-app-when-funval-is-binary-op-fully
                            eval-app-of-int-add-commutative
                            list-prefix-join-of-two-commutative)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; A successful addition has compatible argument shapes

(defruled join-when-eval-app-of-curried-vector-not-reserrp
  (implies (and (expr-value-listp cells)
                (list-of-primop-int-binary-x cells)
                (acl2::pos-listp fun-frame)
                (equal (len cells) (nat-list-product fun-frame))
                (expr-value-list-wfp cells)
                (consp argvals)
                (not (reserrp
                      (eval-app (expr-value-with-nonempty-dims fun-frame cells)
                                argvals limit))))
           (mv-nth 0 (list-prefix-join
                      (list fun-frame
                            (dims-of-expr-value (car argvals))))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((eval-app (expr-value-with-nonempty-dims fun-frame cells)
                              argvals limit))
           :in-theory (e/d (check-list-suffix-of-nil
                            true-listp-when-nat-listp
                            list-of-primop-int-binary-x
                            car-of-repeat)
                           (eval-app-when-funval-is-curried-binary-op-vector
                            list-prefix-join-of-two-commutative)))))

(defruled join-when-eval-app-of-int-add-not-reserrp
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
                (not (reserrp (eval-app funval (list arg1 arg2) limit))))
           (mv-nth 0 (list-prefix-join (list (dims-of-expr-value arg1)
                                             (dims-of-expr-value arg2)))))
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
                 (:instance join-when-eval-app-of-curried-vector-not-reserrp
                            (fun-frame (dims-of-expr-value arg1))
                            (cells (pairwise-curry-binary-fn
                                    (repeat (nat-list-product
                                             (dims-of-expr-value arg1))
                                            funval)
                                    (get-cells-from-expr-value arg1)))
                            (argvals (list arg2))
                            (limit (1- limit))))
           :in-theory (e/d (dims-of-expr-value-when-primop
                            lift-expr-value-to-frame-when-scalar
                            lift-expr-value-to-frame-when-nested)
                           (eval-app-when-funval-is-binary-op
                            eval-app-when-funval-is-curried-binary-op-vector
                            eval-app-when-funval-is-binary-op-fully
                            eval-app-of-int-add-commutative
                            list-prefix-join-of-two-commutative)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Commutativity of lifted integer addition, strong form

; If adding two arrays of base values succeeds in one order,
; it succeeds in the other order, with the same result.

(defthm eval-app-of-int-add-commutative-strong
  (implies (and (expr-valuep funval)
                (expr-value-case funval :primop)
                (primop-value-case (expr-value-primop->val funval)
                                   :int-binary)
                (int-binary-primop-case
                 (primop-value-int-binary->op (expr-value-primop->val funval))
                 :add)
                (expr-value-wfp arg1)
                (expr-valuep arg1)
                (expr-value-wfp arg2)
                (expr-valuep arg2)
                (expr-is-nested-vectors-of-base-values arg1)
                (expr-is-nested-vectors-of-base-values arg2)
                (not (reserrp (eval-app funval (list arg1 arg2) limit))))
           (and (not (reserrp (eval-app funval (list arg2 arg1) limit)))
                (equal (eval-app funval (list arg2 arg1) limit)
                       (eval-app funval (list arg1 arg2) limit))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance join-when-eval-app-of-int-add-not-reserrp)
                 (:instance facts-when-eval-app-of-int-add-not-reserrp)
                 (:instance eval-app-of-int-add-not-reserrp
                            (arg1 arg2) (arg2 arg1))
                 (:instance eval-app-of-int-add-commutative))
           :in-theory (disable eval-app-of-int-add-commutative
                               eval-app-when-funval-is-binary-op
                               eval-app-when-funval-is-curried-binary-op-vector
                               eval-app-when-funval-is-binary-op-fully))))
