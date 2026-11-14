; Examples of Section 2 of the paper, checked by evaluation
; with the Kestrel ACL2 Remora interpreter.

(in-package "REMORA")

(include-book "commutativity-total")

(include-book "kestrel/remora/parser-interface" :dir :system)
(include-book "kestrel/remora/validator" :dir :system)
(include-book "kestrel/remora/evaluation" :dir :system)

(include-book "std/testing/assert-bang" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 1: directly at the level of eval-app, on expression values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The value of the Remora primitive + (as in the initial environment).
(defconst *plus*
  (expr-value-primop (primop-value-int-binary (int-binary-primop-add))))

(assert-event
 (equal *plus*
        (omap::lookup "+" (primop-values))))

(define int-expr-value ((i integerp))
  :returns (val expr-valuep)
  (expr-value-base (base-value-int (int-value i))))

; Build a nested-vector expression value from a nested list of integers.
(mutual-recursion
 (defun nested-int-value (x)
   (declare (xargs :mode :program))
   (if (integerp x)
       (int-expr-value x)
     (expr-value-vector (nested-int-value-list x))))
 (defun nested-int-value-list (xs)
   (declare (xargs :mode :program))
   (if (consp xs)
       (cons (nested-int-value (car xs))
             (nested-int-value-list (cdr xs)))
     nil)))

(defconst *limit* 1000)

(defmacro remora-add (x y)
  `(eval-app *plus*
             (list (nested-int-value ',x) (nested-int-value ',y))
             *limit*))

;; Scalars: (+ 1 2) is 3.
(assert-event (equal (remora-add 1 2) (nested-int-value 3)))

;; Same shapes: [1 2 3] + [4 5 6] is [5 7 9].
(assert-event (equal (remora-add (1 2 3) (4 5 6))
                     (nested-int-value '(5 7 9))))

;; Compatible ranks (lifting): [1 2] + [[1 2] [3 4]] is [[2 3] [5 6]].
(assert-event (equal (remora-add (1 2) ((1 2) (3 4)))
                     (nested-int-value '((2 3) (5 6)))))

;; Lifting is symmetric: [[1 2] [3 4]] + [1 2] is [[2 3] [5 6]] too.
(assert-event (equal (remora-add ((1 2) (3 4)) (1 2))
                     (nested-int-value '((2 3) (5 6)))))

;; Shape [10 5] lifted against shape [10 5 3 4] is not exercised here,
;; but a scalar lifted against a matrix is: 10 + [[1 2] [3 4]].
(assert-event (equal (remora-add 10 ((1 2) (3 4)))
                     (nested-int-value '((11 12) (13 14)))))

;; Ill-formed additions are run-time errors:

;; [1 2 3] + [4 5]  (shapes [3] and [2])
(assert-event (reserrp (remora-add (1 2 3) (4 5))))

;; [1 2 3 4] + [[1 2] [3 4]]  (shapes [4] and [2 2], same number of cells)
(assert-event (reserrp (remora-add (1 2 3 4) ((1 2) (3 4)))))

;; [1 2] + [[1 2] [3 4] [5 6]]  (shapes [2] and [3 2]: not prefixes)
(assert-event (reserrp (remora-add (1 2) ((1 2) (3 4) (5 6)))))

;; [1 2] + [[1 2] [[5 6]]], as literally written in the paper:
;; the second argument is not even a well-formed array.
(assert-event
 (not (expr-value-wfp (nested-int-value '((1 2) ((5 6)))))))
; (It violates the guard of eval-app, so it is not evaluated at this level;
; see Part 2 for its evaluation from Remora syntax.)

;; The ill-formed cases are errors no matter how large the limit is
;; (checked here for a much larger limit).
(assert-event
 (reserrp (eval-app *plus*
                    (list (nested-int-value '(1 2 3))
                          (nested-int-value '(4 5)))
                    1000000)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 2: the same examples written in Remora syntax,
;;; through the parser, (optionally) the static checker, and the evaluator
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse, check, and evaluate a Remora expression; return its value or error.
(define run-remora ((code stringp))
  :mode :program
  (b* ((ast (parse-top-exp-from-string code))
       ((when (reserrp ast)) ast)
       (tast (check-top-expr ast))
       ((when (reserrp tast)) tast))
    (eval-top-expr (type+expr->expr tast) *limit*)))

; Parse and evaluate without static checking, to observe run-time behavior.
(define run-remora-unchecked ((code stringp))
  :mode :program
  (b* ((ast (parse-top-exp-from-string code))
       ((when (reserrp ast)) ast))
    (eval-top-expr ast *limit*)))

(assert-event (equal (run-remora "(+ 1 2)") (nested-int-value 3)))

(assert-event (equal (run-remora "(+ [1 2 3] [4 5 6])")
                     (nested-int-value '(5 7 9))))

(assert-event (equal (run-remora "(+ [1 2] [[1 2] [3 4]])")
                     (nested-int-value '((2 3) (5 6)))))

(assert-event (equal (run-remora-unchecked "(+ [1 2] [[1 2] [3 4]])")
                     (nested-int-value '((2 3) (5 6)))))

;; The ill-formed additions are rejected, both by the full pipeline
;; and by the evaluator alone (run-time errors).

(assert-event (reserrp (run-remora "(+ [1 2 3] [4 5])")))
(assert-event (reserrp (run-remora-unchecked "(+ [1 2 3] [4 5])")))

(assert-event (reserrp (run-remora "(+ [1 2 3 4] [[1 2] [3 4]])")))
(assert-event (reserrp (run-remora-unchecked "(+ [1 2 3 4] [[1 2] [3 4]])")))

(assert-event (reserrp (run-remora "(+ [1 2] [[1 2] [3 4] [5 6]])")))
(assert-event (reserrp (run-remora-unchecked "(+ [1 2] [[1 2] [3 4] [5 6]])")))

(assert-event (reserrp (run-remora "(+ [1 2] [[1 2] [[5 6]]])")))
(assert-event (reserrp (run-remora-unchecked "(+ [1 2] [[1 2] [[5 6]]])")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 3: the theorems agree with the examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The right-hand side of eval-app-when-funval-is-binary-op-fully,
;; computed for [1 2] + [[1 2] [3 4]], is the value computed by the interpreter.
(assert-event
 (b* ((arg1 (nested-int-value '(1 2)))
      (arg2 (nested-int-value '((1 2) (3 4))))
      ((mv & pframe) (list-prefix-join (list (dims-of-expr-value arg1)
                                             (dims-of-expr-value arg2)))))
   (equal (expr-value-with-nonempty-dims
           pframe
           (pairwise-binary-args-fn
            (repeat-each (nat-list-product pframe)
                         (get-cells-from-expr-value *plus*))
            (repeat-each (nat-list-product
                          (nthcdr (len (dims-of-expr-value arg1)) pframe))
                         (get-cells-from-expr-value arg1))
            (repeat-each (nat-list-product
                          (nthcdr (len (dims-of-expr-value arg2)) pframe))
                         (get-cells-from-expr-value arg2))))
          (remora-add (1 2) ((1 2) (3 4))))))

;; The strong commutativity theorem, instantiated: [1 2] + [[1 2] [3 4]]
;; and [[1 2] [3 4]] + [1 2] agree (also checked by evaluation above).
(assert-event
 (equal (remora-add (1 2) ((1 2) (3 4)))
        (remora-add ((1 2) (3 4)) (1 2))))
