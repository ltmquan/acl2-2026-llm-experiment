; Commutativity of Remora integer addition, lifted to arrays
; (the corollary at the end of Section 3 of the paper).

(in-package "REMORA")

(include-book "lifting")

(local (include-book "std/lists/top" :dir :system))

(local (in-theory (enable not-reserrp-when-expr-value-listp
                          not-reserrp-when-expr-valuep
                          expr-valuep-when-result-not-error
                          expr-value-listp-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Pure ACL2 list reasoning
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule prim-int-add-commutative
  (equal (prim-int-add y x)
         (prim-int-add x y))
  :enable (prim-int-add check-expr-value-int))

(define list-of-primop-int-add ((funcells expr-value-listp))
  :returns (yes/no booleanp)
  :short "Check if every cell is the (first-stage) integer addition."
  (or (endp funcells)
      (and (expr-value-case (car funcells) :primop)
           (primop-value-case (expr-value-primop->val (car funcells))
                              :int-binary)
           (int-binary-primop-case
            (primop-value-int-binary->op (expr-value-primop->val (car funcells)))
            :add)
           (list-of-primop-int-add (cdr funcells)))))

(defrule list-of-primop-int-add-of-repeat
  (implies (and (expr-value-case f :primop)
                (primop-value-case (expr-value-primop->val f) :int-binary)
                (int-binary-primop-case
                 (primop-value-int-binary->op (expr-value-primop->val f))
                 :add))
           (list-of-primop-int-add (repeat n f)))
  :induct (repeat n f)
  :enable (repeat list-of-primop-int-add))

(defrule pairwise-binary-args-fn-commutative-for-add
  (implies (list-of-primop-int-add funcells)
           (equal (pairwise-binary-args-fn funcells args2 args1)
                  (pairwise-binary-args-fn funcells args1 args2)))
  :induct (three-cdrs-induct funcells args1 args2)
  :enable (pairwise-binary-args-fn
           list-of-primop-int-add
           int-binary-op-apply
           three-cdrs-induct))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The principal frame does not depend on the order of the two frames
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule prefixp-antisymmetric-for-true-lists
  (implies (and (prefixp x y)
                (prefixp y x)
                (true-listp x)
                (true-listp y))
           (equal x y))
  :use ((:instance acl2::prefixp-when-equal-lengths (x x) (y y)))
  :enable acl2::list-equiv
  :rule-classes nil)

(defrule list-prefix-join-of-two-commutative
  (equal (list-prefix-join (list b a))
         (list-prefix-join (list a b)))
  :enable list-prefix-join
  :use ((:instance prefixp-antisymmetric-for-true-lists
                   (x (true-list-fix a)) (y (true-list-fix b)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Commutativity of integer addition on arrays of compatible shapes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; If the Remora integer addition is applied (with lifting) to two arrays of
; base values whose shapes are compatible (one is a prefix of the other),
; and both orders of the arguments evaluate without error,
; then the two results are the same.

(defthm eval-app-of-int-add-commutative
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
                (not (reserrp (eval-app funval (list arg1 arg2) limit)))
                (not (reserrp (eval-app funval (list arg2 arg1) limit))))
           (equal (eval-app funval (list arg2 arg1) limit)
                  (eval-app funval (list arg1 arg2) limit)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance eval-app-when-funval-is-binary-op-fully
                            (arg1-frame (dims-of-expr-value arg1))
                            (arg2-frame (dims-of-expr-value arg2))
                            (pframe (mv-nth 1 (list-prefix-join
                                               (list (dims-of-expr-value arg1)
                                                     (dims-of-expr-value arg2))))))
                 (:instance eval-app-when-funval-is-binary-op-fully
                            (arg1 arg2)
                            (arg2 arg1)
                            (arg1-frame (dims-of-expr-value arg2))
                            (arg2-frame (dims-of-expr-value arg1))
                            (pframe (mv-nth 1 (list-prefix-join
                                               (list (dims-of-expr-value arg1)
                                                     (dims-of-expr-value arg2)))))))
           :in-theory (disable eval-app-when-funval-is-binary-op-fully
                               eval-app-when-funval-is-binary-op
                               eval-app-when-funval-is-curried-binary-op-vector))
          (and stable-under-simplificationp
               '(:in-theory (e/d (list-prefix-join)
                                 (eval-app-when-funval-is-binary-op-fully
                                  eval-app-when-funval-is-binary-op
                                  eval-app-when-funval-is-curried-binary-op-vector
                                  list-prefix-join-of-two-commutative))))))
