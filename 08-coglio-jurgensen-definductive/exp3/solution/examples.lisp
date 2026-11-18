; Examples of DEFINDUCTIVE from the paper
; "Inductive Definitions via Inference Rules in ACL2".

(in-package "ACL2")

(include-book "definductive")
(include-book "std/testing/must-fail" :dir :system)

;; Some parity facts used in Section 5.2 below.  (Arithmetic-3 is included
;; locally to the encapsulate, so that it does not affect the rest of this
;; book; e.g. it defines a function TREE, which is a predicate name below.)

(encapsulate
  ()
  (local (include-book "arithmetic-3/top" :dir :system))
  (defthm evenp-of-1-when-oddp
    (implies (and (integerp n) (oddp n)) (evenp (1- n))))
  (defthm oddp-of-1-when-evenp
    (implies (and (integerp n) (evenp n)) (oddp (1- n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reflexive and transitive closure (Sections 1, 3, 4).

(defstub r (* *) => *) ; uninterpreted, for abstraction

(definductive refl-trans-closure
  :preds ((r* a b))
  :irules ((base ((r x y)) (r* x y))
           (refl () (r* x x))
           (trans ((r* x y) (r* y z)) (r* x z))))

;; Check the forms of some of the generated theorems (without adding rules).

(defthm r*-base-check (implies (r x y) (r* x y))
  :rule-classes nil
  :hints (("Goal" :by r*-base)))

(defthm r*-refl-check (r* x x)
  :rule-classes nil
  :hints (("Goal" :by r*-refl)))

(defthm r*-trans-check (implies (and (r* x y) (r* y z)) (r* x z))
  :rule-classes nil
  :hints (("Goal" :by r*-trans)))

(defthm r*-when-proof-validp-check
  (implies (and (r*-proof-validp proof a b)
                (r*-proofp proof))
           (r* a b))
  :rule-classes nil
  :hints (("Goal" :by r*-when-proof-validp)))

(defthm r*-alt-when-r*-proof-validp-check
  (implies (r*-proof-validp proof a b) (r*-alt a b))
  :rule-classes nil
  :hints (("Goal" :by r*-alt-when-r*-proof-validp)))

(defthm r*-alt-when-r*-check
  (implies (r* a b) (r*-alt a b))
  :rule-classes nil
  :hints (("Goal" :by r*-alt-when-r*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Natural numbers, trees, and lists of trees (Section 4.2).

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Even and odd numbers (Section 4.2).

(definductive even-and-odd
  :preds ((even n) (odd n))
  :irules ((zero () (even 0))
           (from-even ((even n)) (odd (1+ n)))
           (from-odd ((odd n)) (even (1+ n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The paper's NO-PROOF-TREES example (Section 4.8) is rejected, because the
;; predicate cannot be assigned a level (its proof tree type would be empty).
;; This is checked here, before P is defined below.

(must-fail
 (definductive no-proof-trees
   :preds ((p x))
   :irules ((recurse ((p x)) (p x)))))

;; A predicate that does not depend on itself (Footnote 4).

(definductive just-0 :preds ((p x)) :irules ((zero () (p 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 5.1: inference rule theorems, derived inference rules.

(defthm trans-base-right (implies (and (r* x y) (r y z)) (r* x z)))

(defthm trans-base-left (implies (and (r x y) (r* y z)) (r* x z))
  ;; As explained in Footnote 11, this needs a :use hint with r*-base
  ;; (disabled, so that the hypothesis (r* x y) that it contributes is not
  ;; simplified away before it is used to instantiate the free variable y of
  ;; r*-trans).
  :hints (("Goal" :use r*-base :in-theory (disable r*-base))))

(defthm even-add-2 (implies (even n) (even (+ 2 n)))
  ;; From odd-from-even (as a rewrite rule) and even-from-odd (instantiated
  ;; to make its conclusion match the one of this theorem).
  :hints (("Goal" :use (:instance even-from-odd (n (+ 1 n))))))

(local (include-book "arithmetic/top" :dir :system))

(defun nat-recursion (m) ; induction on natural numbers
  (if (zp m) m (nat-recursion (1- m))))

(defthm even-add-double (implies (and (natp m) (even n)) (even (+ (* 2 m) n)))
  ;; By induction on m, applying even-add-2 in the induction step.
  :hints (("Goal" :induct (nat-recursion m))
          (and stable-under-simplificationp
               '(:use (:instance even-add-2 (n (+ (* 2 (1- m)) n)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 5.2: proof tree construction.

(mutual-recursion
 (defun proof-for-even (n) ; proof tree that n is even
   (declare (xargs :guard (and (natp n) (evenp n)) :verify-guards nil))
   (b* (((when (zp n)) (even-proof-zero)) ; base case
        (odd-proof (proof-for-odd (1- n)))) ; proof tree that n-1 is odd
     (make-even-proof-from-odd :n (1- n) :premise1-proof odd-proof)))
 (defun proof-for-odd (n) ; proof tree that n is odd
   (declare (xargs :guard (and (natp n) (oddp n)) :verify-guards nil))
   (b* (((when (zp n)) ; impossible -- result is irrelevant
         (make-odd-proof-from-even :n 0 :premise1-proof (even-proof-zero)))
        (even-proof (proof-for-even (1- n)))) ; proof tree that n-1 is even
     (make-odd-proof-from-even :n (1- n) :premise1-proof even-proof))))

(flag::make-flag proof-for-even/odd-flag proof-for-even)

(defthm even-proofp-of-proof-for-even (even-proofp (proof-for-even n))
  :hints (("Goal" :expand ((proof-for-even n)))))

(defthm odd-proofp-of-proof-for-odd (odd-proofp (proof-for-odd n))
  :hints (("Goal" :expand ((proof-for-odd n)))))

(defthm-proof-for-even/odd-flag ; flag event for the mutual recursion above
  (defthm even-proof-validp-of-proof-for-even
    (implies (and (natp n) (evenp n)) (even-proof-validp (proof-for-even n) n))
    :flag proof-for-even)
  (defthm odd-proof-validp-of-proof-for-odd
    (implies (and (natp n) (oddp n)) (odd-proof-validp (proof-for-odd n) n))
    :flag proof-for-odd)
  :hints (("Goal" :in-theory (disable evenp oddp))))

(defthm even-when-evenp (implies (and (natp n) (evenp n)) (even n))
  :hints
  (("Goal" :use (:instance even-when-proof-validp (proof (proof-for-even n))))))

(defthm odd-when-oddp (implies (and (natp n) (oddp n)) (odd n))
  :hints
  (("Goal" :use (:instance odd-when-proof-validp (proof (proof-for-odd n))))))

(defthm even-of-pred-when-odd (implies (odd n) (even (1- n)))
  :hints (("Goal"
           :expand ((odd n) (odd-proof-validp (odd-proof n) n))
           :use (:instance even-when-proof-validp
                           (proof (odd-proof-from-even->premise1-proof
                                   (odd-proof n)))
                           (n (1- n))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 5.3: proof tree induction.

(defthm-even-proof-validp-clique-flag
  (defthm natp-when-even-proof-validp
    (implies (even-proof-validp proof n) (natp n))
    :flag even-proof-validp)
  (defthm natp-when-odd-proof-validp
    (implies (odd-proof-validp proof n) (natp n))
    :flag odd-proof-validp))

(defthm natp-when-even/odd (implies (or (even n) (odd n)) (natp n))
  :hints (("Goal" :in-theory (enable even odd))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 5.4: inference rule induction.

(encapsulate
  (((f *) => *))
  (local (defun f (x) x))
  (defthm r-of-f (implies (r x y) (r (f x) (f y)))))

(defthm r*-of-f (implies (r* a b) (r* (f a) (f b)))
  :hints (("Goal" :induct (r* a b) ; inference rule induction
                  :in-theory (enable r*-base r*-refl r*-trans)
                  :expand ((r* a b) (r*-proof-validp (r*-proof a b) a b)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 5.5: functional instantiation of the minimality theorems.

(defthm r*-of-f-alt (implies (r* a b) (r* (f a) (f b)))
  :hints (("Goal"
           :use (:functional-instance r*-alt-when-r*
                                      (r*-alt (lambda (a b) (r* (f a) (f b)))))
           :in-theory (enable r*-base r*-refl r*-trans))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Invalid definitions (Section 4.8).

(must-fail
 (definductive no-proof-trees
   :preds ((p2 x))
   :irules ((recurse ((p2 x)) (p2 x)))))


(must-fail
 (definductive conj-premise
   :preds ((q x) (q2 x))
   :irules ((zero () (q 0))
            (zero () (q2 0))
            (conj ((and (q x) (q2 x))) (q (1+ x))))))

(must-fail
 (definductive disj-premise
   :preds ((q x) (q2 x))
   :irules ((zero () (q 0))
            (zero () (q2 0))
            (disj ((or (q x) (q2 x))) (q (1+ x))))))

(must-fail
 (definductive neg-premise
   :preds ((q x))
   :irules ((zero () (q 0))
            (neg ((not (q x))) (q (1+ x))))))

(must-fail
 (definductive impl-premise
   :preds ((q x))
   :irules ((zero () (q 0))
            (impl ((implies (q x) (natp x))) (q (1+ x))))))
