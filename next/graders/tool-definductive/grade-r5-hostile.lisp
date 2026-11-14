; Grader book for tool-definductive, requirement 5 (hostile theory):
; the paper's four calls (as in grade-r2) after including libraries with many
; enabled rewrite rules and enabling unrelated rewrite rules of our own.
; The rules are recorded in NOTES.md.

(in-package "ACL2")

(include-book "definductive")
(include-book "grader-utils")

; Libraries with many enabled rewrite rules (arithmetic, lists).
; (Not arithmetic-3/5: they define a function TREE, which clashes with the
; paper's nat-trees.)
(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "std/typed-lists/top" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)

; Enable definitions that libraries normally keep disabled.
(in-theory (enable two-nats-measure nat-list-measure))

; Unrelated (true) rewrite rules that change the shape of common terms.
(defthm grader-hostile-equal-cons
  (equal (equal (cons a b) c)
         (and (consp c) (equal a (car c)) (equal b (cdr c)))))
(defthm grader-hostile-acl2-count-cons
  (equal (acl2-count (cons a b))
         (+ 1 (acl2-count a) (acl2-count b))))
(defthm grader-hostile-o<-nats
  (implies (and (natp x) (natp y))
           (equal (o< x y) (< x y))))
(defthm grader-hostile-natp-of-1+
  (implies (natp n) (natp (+ 1 n))))
(defthm grader-hostile-car-when-not-consp
  (implies (not (consp x)) (equal (car x) nil)))
(defthm grader-hostile-cdr-when-not-consp
  (implies (not (consp x)) (equal (cdr x) nil)))

; Section 3
(defstub r (* *) => *) ; uninterpreted, for abstraction

; Section 4
(deflabel grader-before-rtc)
(definductive refl-trans-closure
  :preds ((r* a b))
  :irules ((base ((r x y)) (r* x y))
           (refl () (r* x x))
           (trans ((r* x y) (r* y z)) (r* x z))))
(deflabel grader-after-rtc)

; Section 4.2
(deflabel grader-before-nt)
(definductive nat-trees
  :preds ((nat n) (tree tr) (trees trs))
  :irules (;; natural numbers:
           (zero () (nat 0))
           (succ ((nat n)) (nat (1+ n)))
           ;; trees of natural numbers:
           (leaf ((nat n)) (tree n))
           (branch ((nat n) (trees trs)) (tree (cons n trs)))
           ;; lists of trees of natural numbers:
           (empty () (trees nil))
           (cons ((tree tr) (trees trs)) (trees (cons tr trs)))))
(deflabel grader-after-nt)

; Section 4.2
(deflabel grader-before-eo)
(definductive even-and-odd
  :preds ((even n) (odd n))
  :irules ((zero () (even 0))
           (from-even ((even n)) (odd (1+ n)))
           (from-odd ((odd n)) (even (1+ n)))))
(deflabel grader-after-eo)

; Footnote 4
(deflabel grader-before-j0)
(definductive just-0 :preds ((p x)) :irules ((zero () (p 0))))
(deflabel grader-after-j0)
