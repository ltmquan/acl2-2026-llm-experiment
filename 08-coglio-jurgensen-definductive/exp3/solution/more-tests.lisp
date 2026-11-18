; Additional tests of DEFINDUCTIVE, beyond the examples in the paper.

(in-package "ACL2")

(include-book "definductive")
(include-book "std/testing/must-fail" :dir :system)

;; Recursive rule listed before the base rule; formals named like rule
;; variables; a variable only in a non-predicate premise.
(defstub rel (* *) => *)
(definductive closure2
  :preds ((rstar x y))
  :irules ((trans ((rstar x y) (rstar y z)) (rstar x z))
           (step ((rel x y)) (rstar x y))
           (loop ((rel x w)) (rstar x x))))

(defthm rstar-step-check (implies (rel a b) (rstar a b)))

;; Three levels in a clique, rules with the same name for different
;; predicates, complex terms in conclusions and premises.
(definductive three-levels
  :preds ((la n) (lb n) (lc n))
  :irules ((base ((natp n) (< n 3)) (la (* 3 n)))
           (base ((la n)) (lb (+ 1 n)))
           (base ((lb n)) (lc (+ 1 n)))
           (step ((lc n) (let ((m (+ 1 n))) (natp m))) (la (+ 1 n)))))

(defthm lb-of-1 (lb 1)
  :hints (("Goal" :use ((:instance la-base (n 0)) (:instance lb-base (n 0))))))

;; Zero-ary predicate, and a predicate depending on an earlier clique only.
(definductive zero-ary
  :preds ((flag0) (q x))
  :irules ((intro () (flag0))
           (q-intro ((flag0) (consp x)) (q (car x)))))

(defthm q-of-car (implies (consp x) (q (car x))))

;; Companion predicate iterating over a list (Section 4.8/6 style).
(definductive all-nats
  :preds ((good x) (goods xs))
  :irules ((leaf ((natp x)) (good x))
           (node ((goods xs) (consp xs)) (good (cons :node xs)))
           (nil () (goods nil))
           (cons ((good x) (goods xs)) (goods (cons x xs)))))

(defthm-good-proof-validp-clique-flag
  (defthm good-implies-consp-or-natp
    (implies (good-proof-validp proof x) (or (natp x) (consp x)))
    :flag good-proof-validp)
  (defthm goods-implies-true-listp
    (implies (goods-proof-validp proof xs) (true-listp xs))
    :flag goods-proof-validp))

;; Rule induction on a mutually recursive clique, via the flag macro.
(defthm-good-induct-clique-flag
  (defthm good-natp-or-consp
    (implies (good x) (or (natp x) (consp x)))
    :hints ('(:expand ((good x))))
    :flag good-induct)
  (defthm goods-true-listp
    (implies (goods xs) (true-listp xs))
    :hints ('(:expand ((goods xs))))
    :flag goods-induct))

;; Many rules (performance).
(definductive many-rules
  :preds ((m x))
  :irules ((r0 () (m 0))
           (r1 ((m x)) (m (+ 1 x)))
           (r2 ((m x)) (m (+ 2 x)))
           (r3 ((m x)) (m (+ 3 x)))
           (r4 ((m x)) (m (+ 4 x)))
           (r5 ((m x)) (m (+ 5 x)))
           (r6 ((m x) (m y)) (m (+ x y)))
           (r7 ((m x) (m y)) (m (* x y)))
           (r8 ((m x) (m y)) (m (- x y)))
           (r9 ((m x)) (m (- x)))
           (r10 ((m x)) (m (cons x x)))
           (r11 ((m x) (m y) (m z)) (m (list x y z)))
           (r12 ((m x)) (m (car x)))
           (r13 ((m x)) (m (cdr x)))
           (r14 ((m x) (natp x)) (m (expt 2 x)))
           (r15 ((m x) (m y)) (m (if (< x y) x y)))
           (r16 ((m x)) (m (list x)))
           (r17 ((m x)) (m (nfix x)))
           (r18 ((m x)) (m (ifix x)))
           (r19 ((m x)) (m (rfix x)))
           (r20 ((m x)) (m (fix x)))))

;; Errors.

(must-fail (definductive bad1 :preds ((r* a b)) :irules ())) ; R* not new? new here, but no rules
(must-fail (definductive bad2 :preds ((bq x)) :irules ((a () (bq 1 2)))))
(must-fail (definductive bad3 :preds ((bq x)) :irules ((a () (other 1)))))
(must-fail (definductive bad4 :preds ((bq x)) :irules ((a ((bq (bq x))) (bq x)))))
(must-fail (definductive bad5 :preds ((bq x)) :irules ((a () (bq 0)) (a () (bq 1)))))
(must-fail (definductive bad6 :preds ((bq proof)) :irules ((a () (bq 0)))))
(must-fail (definductive bad7 :preds ((bq x)) :irules ((a () (bq 0))) :bogus 1))
(must-fail (definductive bad8 :preds ((car x)) :irules ((a () (car 0)))))
(must-fail (definductive bad9 :preds ((bq x)) :irules ((a ((iff (bq x) t)) (bq 0)))))
(must-fail (definductive bad10 :preds ((bq x) (bq2 x))
             :irules ((a ((bq2 x)) (bq x)) (b ((bq x)) (bq2 x)))))
(must-fail (definductive bad11 :preds ((bq x)) :irules ((a ((undefined-fn x)) (bq x)))))

;; XDOC inputs.
(definductive documented
  :preds ((dp x))
  :irules ((base () (dp nil)))
  :parents (acl2::top)
  :short "A documented inductive definition."
  :long "<p>Just a test.</p>")
