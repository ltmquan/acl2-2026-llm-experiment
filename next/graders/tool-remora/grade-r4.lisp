;; Grader for tool-remora, R4 (grader's own evaluation of the Section 2 examples; independent of the model).
;; It validates the interpreter (books/kestrel/remora on master) and our reading of the examples; R4 itself
;; checks that the model's /work/examples.lisp certifies and contains these evaluations (CHECKLIST R4).
;; It also defines the constants used by the CHECKLIST R3 non-vacuity procedure.
(in-package "REMORA")
(include-book "kestrel/remora/parser-interface" :dir :system)
(include-book "kestrel/remora/validator" :dir :system)
(include-book "kestrel/remora/evaluation" :dir :system)

;; Full pipeline on Remora source: parse, check (static semantics), evaluate.
;; Returns (:val v) or (:error stage).
(defun grader-run (code)
  (declare (xargs :mode :program))
  (b* ((ast (parse-top-exp-from-string code))
       ((when (reserrp ast)) (list :error :parse))
       (tast (check-top-expr ast))
       ((when (reserrp tast)) (list :error :static))
       (val (eval-top-expr (type+expr->expr tast) 1000000))
       ((when (reserrp val)) (list :error :eval)))
    (list :val val)))

(defmacro grader-int (i) `(expr-value-base (base-value-int (int-value ,i))))
(defconst *grader-plus*
  (expr-value-primop (primop-value-int-binary (int-binary-primop-add))))
(defconst *grader-v12*   (expr-value-vector (list (grader-int 1) (grader-int 2))))
(defconst *grader-v123*  (expr-value-vector (list (grader-int 1) (grader-int 2) (grader-int 3))))
(defconst *grader-v45*   (expr-value-vector (list (grader-int 4) (grader-int 5))))
(defconst *grader-v1234* (expr-value-vector (list (grader-int 1) (grader-int 2) (grader-int 3) (grader-int 4))))
(defconst *grader-m1234* ; [[1 2] [3 4]]
  (expr-value-vector (list (expr-value-vector (list (grader-int 1) (grader-int 2)))
                           (expr-value-vector (list (grader-int 3) (grader-int 4))))))
(defconst *grader-m123456* ; [[1 2] [3 4] [5 6]], shape [3 2]
  (expr-value-vector (list (expr-value-vector (list (grader-int 1) (grader-int 2)))
                           (expr-value-vector (list (grader-int 3) (grader-int 4)))
                           (expr-value-vector (list (grader-int 5) (grader-int 6))))))
(defconst *grader-m2356* ; [[2 3] [5 6]]
  (expr-value-vector (list (expr-value-vector (list (grader-int 2) (grader-int 3)))
                           (expr-value-vector (list (grader-int 5) (grader-int 6))))))

;; ---- Sec. 2 through the whole pipeline (source text)
;; (+ 1 2) is 3; [1 2 3] + [4 5 6] is [5 7 9]
(assert-event (equal (grader-run "(+ 1 2)") (list :val (grader-int 3))))
(assert-event (equal (grader-run "(+ [1 2 3] [4 5 6])")
                     (list :val (expr-value-vector (list (grader-int 5) (grader-int 7) (grader-int 9))))))
;; [1 2] + [[1 2] [3 4]] gives [[2 3] [5 6]]
(assert-event (equal (grader-run "(+ [1 2] [[1 2] [3 4]])") (list :val *grader-m2356*)))
;; ill-formed additions are errors (on master the static checker rejects them before evaluation):
;; [1 2 3] + [4 5]
(assert-event (equal (car (grader-run "(+ [1 2 3] [4 5])")) :error))
;; [1 2 3 4] + [[1 2] [3 4]]
(assert-event (equal (car (grader-run "(+ [1 2 3 4] [[1 2] [3 4]])")) :error))
;; [1 2] + [[1 2] [[5 6]]] as printed (a ragged array)
(assert-event (equal (car (grader-run "(+ [1 2] [[1 2] [[5 6]]])")) :error))
;; ... and as the text describes it (shapes [2] and [3 2]): [1 2] + [[1 2] [3 4] [5 6]]
(assert-event (equal (car (grader-run "(+ [1 2] [[1 2] [3 4] [5 6]])")) :error))

;; ---- the same examples at the level of eval-app (the "run-time" behaviour, no static checking)
(assert-event (equal (eval-app *grader-plus* (list *grader-v12* *grader-m1234*) 1000) *grader-m2356*))
(assert-event (reserrp (eval-app *grader-plus* (list *grader-v123* *grader-v45*) 1000)))
(assert-event (reserrp (eval-app *grader-plus* (list *grader-v1234* *grader-m1234*) 1000)))
(assert-event (reserrp (eval-app *grader-plus* (list *grader-v12* *grader-m123456*) 1000)))
;; commutativity on the example (for the R3 non-vacuity procedure)
(assert-event (equal (eval-app *grader-plus* (list *grader-m1234* *grader-v12*) 1000) *grader-m2356*))
