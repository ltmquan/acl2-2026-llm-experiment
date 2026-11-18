; Tests for the MSET library.

(in-package "MSET")

(include-book "mset")
(include-book "std/testing/assert-bang" :dir :system)

;; Concrete bags.
(defconst *b1* '((a . 2) (b . 1) (c . 3)))   ; {a,a,b,c,c,c}
(defconst *b2* '((a . 1) (c . 5) (d . 2)))   ; {a,c,c,c,c,c,d,d}

;; Recognizer, fixer, equivalence
(assert-event (bagp *b1*))
(assert-event (bagp *b2*))
(assert-event (bagp nil))
(assert-event (not (bagp '((a . 0)))))          ; zero count not allowed
(assert-event (not (bagp '((a . -1)))))
(assert-event (not (bagp '((a . 1/2)))))
(assert-event (not (bagp '((b . 1) (a . 1)))))  ; keys out of order
(assert-event (not (bagp 5)))
(assert-event (equal (bfix *b1*) *b1*))
(assert-event (bequiv *b1* *b1*))
(assert-event (not (bequiv *b1* *b2*)))

;; Empty
(assert-event (equal (empty) nil))
(assert-event (emptyp (empty)))
(assert-event (not (emptyp *b1*)))

;; Count and membership
(assert-event (equal (count 'a *b1*) 2))
(assert-event (equal (count 'c *b1*) 3))
(assert-event (equal (count 'z *b1*) 0))
(assert-event (in 'b *b1*))
(assert-event (not (in 'd *b1*)))

;; Insert / delete
(assert-event (equal (insert 'a *b1*) '((a . 3) (b . 1) (c . 3))))
(assert-event (equal (insert 'd *b1*) '((a . 2) (b . 1) (c . 3) (d . 1))))
(assert-event (equal (insert 'x (empty)) '((x . 1))))
(assert-event (equal (insert-n 'b 4 *b1*) '((a . 2) (b . 5) (c . 3))))
(assert-event (equal (insert-n 'b 0 *b1*) *b1*))
(assert-event (equal (insert-n 'e 2 *b1*) '((a . 2) (b . 1) (c . 3) (e . 2))))
(assert-event (equal (delete 'a *b1*) '((a . 1) (b . 1) (c . 3))))
(assert-event (equal (delete 'b *b1*) '((a . 2) (c . 3))))
(assert-event (equal (delete 'z *b1*) *b1*))
(assert-event (equal (delete-all 'c *b1*) '((a . 2) (b . 1))))
(assert-event (equal (delete-all 'z *b1*) *b1*))

;; Cardinality and support
(assert-event (equal (cardinality *b1*) 6))
(assert-event (equal (cardinality *b2*) 8))
(assert-event (equal (cardinality (empty)) 0))
(assert-event (equal (support *b1*) '(a b c)))
(assert-event (equal (support (empty)) nil))

;; Sub-bags
(assert-event (subbag '((a . 1) (c . 2)) *b1*))
(assert-event (subbag (empty) *b1*))
(assert-event (subbag *b1* *b1*))
(assert-event (not (subbag *b1* *b2*)))
(assert-event (not (subbag '((a . 3)) *b1*)))
(assert-event (equal (subbag-witness '((a . 3)) *b1*) 'a))
(assert-event (equal (count-diff-witness *b1* (insert 'b *b1*)) 'b))

;; Binary operations
(assert-event (equal (sum *b1* *b2*) '((a . 3) (b . 1) (c . 8) (d . 2))))
(assert-event (equal (union *b1* *b2*) '((a . 2) (b . 1) (c . 5) (d . 2))))
(assert-event (equal (intersect *b1* *b2*) '((a . 1) (c . 3))))
(assert-event (equal (diff *b1* *b2*) '((a . 1) (b . 1))))
(assert-event (equal (diff *b2* *b1*) '((c . 2) (d . 2))))
(assert-event (equal (diff *b1* *b1*) (empty)))
(assert-event (equal (sum *b1* (empty)) *b1*))
(assert-event (equal (intersect *b1* (empty)) (empty)))

;; Conversions with lists
(assert-event (equal (from-list '(c a b a c c)) *b1*))
(assert-event (equal (from-list nil) (empty)))
(assert-event (equal (to-list *b1*) '(a a b c c c)))
(assert-event (equal (to-list *b2*) '(a c c c c c d d)))
(assert-event (equal (to-list (empty)) nil))
(assert-event (equal (from-list (to-list *b2*)) *b2*))
(assert-event (equal (len (to-list *b2*)) (cardinality *b2*)))

;; Non-symbol elements (ordering by <<: numbers, strings, symbols, conses)
(assert-event (equal (from-list '((1 2) "s" 3 x 3))
                     '((3 . 2) ("s" . 1) (x . 1) ((1 2) . 1))))

;; Behavior on non-bags.  These calls violate the guards, so they are checked
;; by the theorem prover (which evaluates ground terms without guard
;; checking) instead of by ASSERT-EVENT.
(defthm non-bag-test-1 (equal (bfix '((a . 0))) nil) :rule-classes nil)
(defthm non-bag-test-2 (equal (bfix 'junk) nil) :rule-classes nil)
(defthm non-bag-test-3 (bequiv 'junk nil) :rule-classes nil)
(defthm non-bag-test-4 (bequiv '((a . 0)) (empty)) :rule-classes nil)
(defthm non-bag-test-5 (emptyp 'junk) :rule-classes nil)
(defthm non-bag-test-6 (equal (count 'a 'junk) 0) :rule-classes nil)
(defthm non-bag-test-7 (equal (insert 'a 'junk) '((a . 1))) :rule-classes nil)
(defthm non-bag-test-8 (equal (cardinality '((a . 0) (b . 2))) 0) :rule-classes nil)
(defthm non-bag-test-9 (equal (sum 'junk '((a . 1))) '((a . 1))) :rule-classes nil)
(defthm non-bag-test-10 (equal (to-list '((b . 1) (a . 1))) nil) :rule-classes nil)
(defthm non-bag-test-11 (equal (insert-n 'a -3 '((a . 1))) '((a . 1))) :rule-classes nil)

;; All library functions are guard-verified.
(assert-event
 (let ((world (w state)))
   (and (eq (acl2::getpropc 'bagp 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'bfix 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'bequiv 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'empty 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'emptyp 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'count 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'in 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'insert 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'insert-n 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'delete 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'delete-all 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'cardinality 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'support 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'subbag 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'subbag-witness 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'count-diff-witness 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'sum 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'union 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'intersect 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'diff 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'from-list 'acl2::symbol-class nil world) :common-lisp-compliant)
        (eq (acl2::getpropc 'to-list 'acl2::symbol-class nil world) :common-lisp-compliant))))
