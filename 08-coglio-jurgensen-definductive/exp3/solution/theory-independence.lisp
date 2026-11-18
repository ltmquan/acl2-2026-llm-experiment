; Requirement 5: the DEFINDUCTIVE calls of examples.lisp also succeed after
; including unrelated arithmetic books, enabling unrelated rules, and
; installing unrelated default hints.  (Note that some arithmetic libraries,
; e.g. arithmetic-5, define a function TREE, which conflicts with the TREE
; predicate of the NAT-TREES example, and therefore cannot be used here.)

(in-package "ACL2")

(include-book "definductive")
(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "ihs/ihs-lemmas" :dir :system)
(include-book "std/lists/top" :dir :system)

;; Enable some normally disabled rules, disable some normally enabled ones,
;; add an unrelated rewrite rule, and add an unrelated default hint.
(in-theory (enable acl2-count nfix ifix two-nats-measure nth update-nth
                   len append true-listp member-equal
))
(in-theory (disable o< o-p o-finp car-cons cdr-cons natp-compound-recognizer))
(defthm unrelated-rule (equal (+ 1 (+ 1 x)) (+ 2 x)))
(set-default-hints '((and stable-under-simplificationp
                          '(:in-theory (enable car-cdr-elim)))))
(set-verify-guards-eagerness 2)

(defstub r (* *) => *)

(definductive refl-trans-closure
  :preds ((r* a b))
  :irules ((base ((r x y)) (r* x y))
           (refl () (r* x x))
           (trans ((r* x y) (r* y z)) (r* x z))))

(definductive nat-trees
  :preds ((nat n) (tree tr) (trees trs))
  :irules ((zero () (nat 0))
           (succ ((nat n)) (nat (1+ n)))
           (leaf ((nat n)) (tree n))
           (branch ((nat n) (trees trs)) (tree (cons n trs)))
           (empty () (trees nil))
           (cons ((tree tr) (trees trs)) (trees (cons tr trs)))))

(definductive even-and-odd
  :preds ((even n) (odd n))
  :irules ((zero () (even 0))
           (from-even ((even n)) (odd (1+ n)))
           (from-odd ((odd n)) (even (1+ n)))))

(definductive just-0 :preds ((p x)) :irules ((zero () (p 0))))
