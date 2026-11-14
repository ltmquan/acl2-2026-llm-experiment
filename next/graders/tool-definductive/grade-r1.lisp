; Grader book for tool-definductive, requirement 1:
; the events generated for the paper's examples have the names and forms shown
; in Sections 3, 4 and 5 of the paper.

(in-package "ACL2")

(include-book "grade-r2") ; the paper's four calls on the model's tool

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Theories of the events of each call (used only to open generated
; definitions in the semantic checks below).

(deftheory grader-rtc-all
  (set-difference-theories (universal-theory 'grader-after-rtc)
                           (universal-theory 'grader-before-rtc)))
(deftheory grader-nt-all
  (set-difference-theories (universal-theory 'grader-after-nt)
                           (universal-theory 'grader-before-nt)))
(deftheory grader-eo-all
  (set-difference-theories (universal-theory 'grader-after-eo)
                           (universal-theory 'grader-before-eo)))
(deftheory grader-j0-all
  (set-difference-theories (universal-theory 'grader-after-j0)
                           (universal-theory 'grader-before-j0)))
(grader-validp-theory grader-rtc-validp grader-before-rtc grader-after-rtc)
(grader-validp-theory grader-nt-validp grader-before-nt grader-after-nt)
(grader-validp-theory grader-eo-validp grader-before-eo grader-after-eo)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Section 3 / 4: refl-trans-closure

; Proof tree type (Section 3): deftagsum r*-proof, summands and fields.
(grader-assert r1-rtc-proof-type
  (equal (grader-flextypes-summary 'r*-proof (w state))
         '((r*-proof (:base (x nil) (y nil))
                     (:refl (x nil))
                     (:trans (x nil) (y nil) (z nil)
                             (premise1-proof r*-proofp)
                             (premise2-proof r*-proofp)))))
  "r*-proof is not a deftagsum with the paper's summands :base (x y), :refl (x), :trans (x y z premise1-proof premise2-proof)")

(grader-assert r1-rtc-proof-count
  (and (equal (cdr (assoc 'fty::count (grader-sum 'r*-proof 'r*-proof (w state))))
              'r*-proof-count)
       (equal (len (grader-formals 'r*-proof-count (w state))) 1))
  "r*-proof-count is not the FTY count function of r*-proof")

; Validity (Section 3): formals (proof a b) and the case analysis shown.
(grader-assert r1-rtc-validp-formals
  (equal (grader-formals 'r*-proof-validp (w state)) '(proof a b))
  "r*-proof-validp does not have formals (proof a b)")

(grader-try r1-rtc-validp-base
  (defthm grader-r*-validp-base
    (equal (r*-proof-validp (r*-proof-base x y) a b)
           (and (r x y) (equal a x) (equal b y)))
    :hints (("Goal" :in-theory (union-theories (current-theory :here)
                                               (theory 'grader-rtc-validp))))
    :rule-classes nil))

(grader-try r1-rtc-validp-refl
  (defthm grader-r*-validp-refl
    (equal (r*-proof-validp (r*-proof-refl x) a b)
           (and (equal a x) (equal b x)))
    :hints (("Goal" :in-theory (union-theories (current-theory :here)
                                               (theory 'grader-rtc-validp))))
    :rule-classes nil))

(grader-try r1-rtc-validp-trans
  (defthm grader-r*-validp-trans
    (implies (and (r*-proofp p1) (r*-proofp p2))
             (equal (r*-proof-validp (r*-proof-trans x y z p1 p2) a b)
                    (and (equal a x)
                         (equal b z)
                         (r*-proof-validp p1 x y)
                         (r*-proof-validp p2 y z))))
    :hints (("Goal" :in-theory (union-theories (current-theory :here)
                                               (theory 'grader-rtc-validp))))
    :rule-classes nil))

; Predicate (Section 4.4): defun-sk r* with skolem r*-proof and minimality.
(grader-assert r1-rtc-pred-formals
  (and (equal (grader-formals 'r* (w state)) '(a b))
       (equal (len (grader-formals 'r*-proof (w state))) 2)
       (not (getpropc 'r*-proof 'unnormalized-body nil (w state))))
  "r* does not have formals (a b), or r*-proof is not its (undefined) skolem function of arity 2")

(grader-try r1-rtc-pred-body
  (defthm grader-r*-body
    (equal (r* a b)
           (let ((proof (r*-proof a b)))
             (and (r*-proofp proof)
                  (r*-proof-validp proof a b)
                  (r*-proof-minimalp proof a b))))
    :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                               '((:definition r*)))))
    :rule-classes nil))

(grader-formula r1-rtc-suff r*-suff
  (implies (and (r*-proofp proof) (r*-proof-validp proof a b) (r*-proof-minimalp proof a b))
           (r* a b)))

(grader-assert r1-rtc-minimalp-formals
  (equal (grader-formals 'r*-proof-minimalp (w state)) '(proof a b))
  "r*-proof-minimalp does not have formals (proof a b)")

(grader-try r1-rtc-minimalp-forall
  (grader-defthm-using grader-r*-minimalp-forall
    (implies (and (r*-proof-minimalp proof a b)
                  (r*-proofp proof2)
                  (r*-proof-validp proof2 a b))
             (<= (r*-proof-count proof) (r*-proof-count proof2)))
    grader-rtc-all (r*-proof-minimalp r*-proof-count)
    r*-proof-minimalp (proof a b) proof2))

; Inference rule theorems (Section 3).
(grader-formula r1-rtc-base r*-base (implies (r x y) (r* x y)))
(grader-formula r1-rtc-refl r*-refl (r* x x))
(grader-formula r1-rtc-trans r*-trans (implies (and (r* x y) (r* y z)) (r* x z)))

; Section 4.4 / 5.2.
(grader-formula r1-rtc-when-proof-validp r*-when-proof-validp
  (implies (and (r*-proof-validp proof a b) (r*-proofp proof)) (r* a b)))

; Section 3 / 4.7: encapsulated r*-alt.
(grader-assert r1-rtc-alt-constrained
  (and (equal (len (grader-formals 'r*-alt (w state))) 2)
       (getpropc 'r*-alt 'constrainedp nil (w state))
       (not (getpropc 'r*-alt 'unnormalized-body nil (w state))))
  "r*-alt is not a constrained (encapsulated) binary function")
(grader-formula r1-rtc-alt-base r*-alt-base (implies (r x y) (r*-alt x y)))
(grader-formula r1-rtc-alt-refl r*-alt-refl (r*-alt x x))
(grader-formula r1-rtc-alt-trans r*-alt-trans
  (implies (and (r*-alt x y) (r*-alt y z)) (r*-alt x z)))
(grader-assert r1-rtc-alt-constraints
  (grader-set-equal (grader-constraints 'r*-alt (w state))
                    (grader-translate-list '((implies (r x y) (r*-alt x y))
                                             (r*-alt x x)
                                             (implies (and (r*-alt x y) (r*-alt y z)) (r*-alt x z)))
                                           (w state)))
  "the constraints of r*-alt are not exactly r*-alt-base, r*-alt-refl, r*-alt-trans")
(grader-formula r1-rtc-alt-when-proof-validp r*-alt-when-r*-proof-validp
  (implies (r*-proof-validp proof a b) (r*-alt a b)))
(grader-formula r1-rtc-alt-when-r* r*-alt-when-r*
  (implies (r* a b) (r*-alt a b)))

; Section 4.5: r*-induct with measure, and an induction rule for r*.
(grader-assert r1-rtc-induct
  (and (equal (grader-formals 'r*-induct (w state)) '(a b))
       (equal (getpropc 'r*-induct 'recursivep nil (w state)) '(r*-induct))
       (equal (access justification
                      (getpropc 'r*-induct 'justification nil (w state))
                      :measure)
              '(r*-proof-count (r*-proof a b))))
  "r*-induct is not a singly recursive function of (a b) with measure (r*-proof-count (r*-proof a b))")
(grader-assert r1-rtc-induction-rule
  (let ((rules (getpropc 'r* 'induction-rules nil (w state))))
    (and (consp rules)
         (member-equal '(r*-induct a b) (grader-induction-schemes rules))))
  "there is no induction rule from (r* a b) to (r*-induct a b)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Section 4.2: nat-trees (two cliques)

(grader-assert r1-nt-nat-proof-type
  (equal (grader-flextypes-summary 'nat-proof (w state))
         '((nat-proof (:zero) (:succ (n nil) (premise1-proof nat-proofp)))))
  "nat-proof is not a deftagsum with summands :zero (), :succ (n premise1-proof)")

(grader-assert r1-nt-tree-proof-clique
  (equal (grader-flextypes-summary 'tree-proof-clique (w state))
         '((tree-proof (:leaf (n nil) (premise1-proof nat-proofp))
                       (:branch (n nil) (trs nil)
                                (premise1-proof nat-proofp)
                                (premise2-proof trees-proofp)))
           (trees-proof (:empty)
                        (:cons (tr nil) (trs nil)
                               (premise1-proof tree-proofp)
                               (premise2-proof trees-proofp)))))
  "tree-proof-clique is not the fty::deftypes of tree-proof and trees-proof shown in Section 4.2")

(grader-assert r1-nt-validp-formals
  (and (equal (grader-formals 'nat-proof-validp (w state)) '(proof n))
       (equal (grader-formals 'tree-proof-validp (w state)) '(proof tr))
       (equal (grader-formals 'trees-proof-validp (w state)) '(proof trs)))
  "nat/tree/trees-proof-validp do not have formals (proof n)/(proof tr)/(proof trs) (Section 3, 4.3)")
(grader-assert r1-nt-validp
  (and (equal (getpropc 'nat-proof-validp 'recursivep nil (w state)) '(nat-proof-validp))
       (grader-set-equal (getpropc 'tree-proof-validp 'recursivep nil (w state))
                         '(tree-proof-validp trees-proof-validp)))
  "nat/tree/trees-proof-validp are not recursive as their types (Section 4.3)")

(grader-try r1-nt-validp-semantics
  (defthm grader-nat-validp-succ
    (implies (nat-proofp p)
             (equal (nat-proof-validp (nat-proof-succ m p) n)
                    (and (equal n (1+ m)) (nat-proof-validp p m))))
    :hints (("Goal" :in-theory (union-theories (current-theory :here)
                                               (theory 'grader-nt-validp))))
    :rule-classes nil)
  (defthm grader-tree-validp-branch
    (implies (and (nat-proofp p1) (trees-proofp p2))
             (equal (tree-proof-validp (tree-proof-branch n trs p1 p2) tr)
                    (and (equal tr (cons n trs))
                         (nat-proof-validp p1 n)
                         (trees-proof-validp p2 trs))))
    :hints (("Goal" :in-theory (union-theories (current-theory :here)
                                               (theory 'grader-nt-validp))))
    :rule-classes nil)
  (defthm grader-trees-validp-empty
    (equal (trees-proof-validp (trees-proof-empty) trs)
           (equal trs nil))
    :hints (("Goal" :in-theory (union-theories (current-theory :here)
                                               (theory 'grader-nt-validp))))
    :rule-classes nil))

(grader-try r1-nt-preds
  (defthm grader-tree-body
    (equal (tree tr)
           (let ((proof (tree-proof tr)))
             (and (tree-proofp proof)
                  (tree-proof-validp proof tr)
                  (tree-proof-minimalp proof tr))))
    :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                               '((:definition tree)))))
    :rule-classes nil)
  (defthm grader-nat-body
    (equal (nat n)
           (let ((proof (nat-proof n)))
             (and (nat-proofp proof)
                  (nat-proof-validp proof n)
                  (nat-proof-minimalp proof n))))
    :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                               '((:definition nat)))))
    :rule-classes nil))

(grader-formula r1-nt-nat-zero nat-zero (nat 0))
(grader-formula r1-nt-nat-succ nat-succ (implies (nat n) (nat (1+ n))))
(grader-formula r1-nt-tree-leaf tree-leaf (implies (nat n) (tree n)))
(grader-formula r1-nt-tree-branch tree-branch
  (implies (and (nat n) (trees trs)) (tree (cons n trs))))
(grader-formula r1-nt-trees-empty trees-empty (trees nil))
(grader-formula r1-nt-trees-cons trees-cons
  (implies (and (tree tr) (trees trs)) (trees (cons tr trs))))

(grader-formula r1-nt-nat-when-proof-validp nat-when-proof-validp
  (implies (and (nat-proof-validp proof n) (nat-proofp proof)) (nat n)))
(grader-formula r1-nt-tree-when-proof-validp tree-when-proof-validp
  (implies (and (tree-proof-validp proof tr) (tree-proofp proof)) (tree tr)))
(grader-formula r1-nt-trees-when-proof-validp trees-when-proof-validp
  (implies (and (trees-proof-validp proof trs) (trees-proofp proof)) (trees trs)))

(grader-assert r1-nt-alt-constraints
  (let ((expected (grader-translate-list
                   '((nat-alt 0)
                     (implies (nat-alt n) (nat-alt (1+ n)))
                     (implies (nat-alt n) (tree-alt n))
                     (implies (and (nat-alt n) (trees-alt trs)) (tree-alt (cons n trs)))
                     (trees-alt nil)
                     (implies (and (tree-alt tr) (trees-alt trs)) (trees-alt (cons tr trs))))
                   (w state))))
    (and (getpropc 'nat-alt 'constrainedp nil (w state))
         (getpropc 'tree-alt 'constrainedp nil (w state))
         (getpropc 'trees-alt 'constrainedp nil (w state))
         (grader-set-equal (grader-constraints 'nat-alt (w state)) expected)
         (grader-set-equal (grader-constraints 'tree-alt (w state)) expected)
         (grader-set-equal (grader-constraints 'trees-alt (w state)) expected)))
  "nat-alt, tree-alt, trees-alt are not introduced by one encapsulate constrained exactly by the six alt rules")
(grader-formula r1-nt-alt-zero nat-alt-zero (nat-alt 0))
(grader-formula r1-nt-alt-succ nat-alt-succ (implies (nat-alt n) (nat-alt (1+ n))))
(grader-formula r1-nt-alt-leaf tree-alt-leaf (implies (nat-alt n) (tree-alt n)))
(grader-formula r1-nt-alt-branch tree-alt-branch
  (implies (and (nat-alt n) (trees-alt trs)) (tree-alt (cons n trs))))
(grader-formula r1-nt-alt-empty trees-alt-empty (trees-alt nil))
(grader-formula r1-nt-alt-cons trees-alt-cons
  (implies (and (tree-alt tr) (trees-alt trs)) (trees-alt (cons tr trs))))
(grader-formula r1-nt-nat-alt-when-proof-validp nat-alt-when-nat-proof-validp
  (implies (nat-proof-validp proof n) (nat-alt n)))
(grader-formula r1-nt-tree-alt-when-proof-validp tree-alt-when-tree-proof-validp
  (implies (tree-proof-validp proof tr) (tree-alt tr)))
(grader-formula r1-nt-trees-alt-when-proof-validp trees-alt-when-trees-proof-validp
  (implies (trees-proof-validp proof trs) (trees-alt trs)))
(grader-formula r1-nt-nat-alt-when-nat nat-alt-when-nat (implies (nat n) (nat-alt n)))
(grader-formula r1-nt-tree-alt-when-tree tree-alt-when-tree (implies (tree tr) (tree-alt tr)))
(grader-formula r1-nt-trees-alt-when-trees trees-alt-when-trees (implies (trees trs) (trees-alt trs)))

(grader-assert r1-nt-induct
  (and (equal (getpropc 'nat-induct 'recursivep nil (w state)) '(nat-induct))
       (consp (getpropc 'nat 'induction-rules nil (w state)))
       (grader-set-equal (getpropc 'tree-induct 'recursivep nil (w state))
                         '(tree-induct trees-induct))
       (assoc-eq 'tree-induct (table-alist 'flag::flag-fns (w state))))
  "nat-induct (singly recursive, with an induction rule for nat) or the mutually recursive tree-induct/trees-induct with a flag macro are missing (Section 4.5)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Section 4.2: even-and-odd (levels)

(grader-assert r1-eo-proof-clique
  (equal (grader-flextypes-summary 'even-proof-clique (w state))
         '((even-proof (:zero) (:from-odd (n nil) (premise1-proof odd-proofp)))
           (odd-proof (:from-even (n nil) (premise1-proof even-proofp)))))
  "even-proof-clique is not the fty::deftypes of even-proof and odd-proof shown in Section 4.2")

(grader-assert r1-eo-levels
  (let* ((ev (grader-sum 'even-proof-clique 'even-proof (w state)))
         (od (grader-sum 'even-proof-clique 'odd-proof (w state)))
         (evm (cdr (assoc 'fty::measure ev)))
         (odm (cdr (assoc 'fty::measure od))))
    (and (eq (cdr (assoc :base-case-override (cdr (assoc 'fty::kwd-alist od)))) :from-even)
         (consp evm) (eq (car evm) 'two-nats-measure) (member-equal (caddr evm) '(0 '0))
         (consp odm) (eq (car odm) 'two-nats-measure) (member-equal (caddr odm) '(1 '1))))
  "odd-proof lacks :base-case-override :from-even, or the measures are not (two-nats-measure ... 0/1) (Section 4.2)")

(grader-assert r1-eo-ctors
  (and (grader-callable 'even-proof-zero 0 (w state))
       (getpropc 'make-even-proof-from-odd 'macro-body nil (w state))
       (grader-callable 'odd-proof-from-even->premise1-proof 1 (w state))
       (grader-callable 'even-proof-from-odd 2 (w state)))
  "even-proof-zero, make-even-proof-from-odd or odd-proof-from-even->premise1-proof (used in Section 5.2) are missing")

(grader-assert r1-eo-validp-formals
  (and (equal (grader-formals 'even-proof-validp (w state)) '(proof n))
       (equal (grader-formals 'odd-proof-validp (w state)) '(proof n)))
  "even/odd-proof-validp do not have formals (proof n)")
(grader-assert r1-eo-validp
  (and (grader-set-equal (getpropc 'even-proof-validp 'recursivep nil (w state))
                         '(even-proof-validp odd-proof-validp))
       (getpropc 'defthm-even-proof-validp-clique-flag 'macro-body nil (w state)))
  "even/odd-proof-validp are not mutually recursive, or the flag macro defthm-even-proof-validp-clique-flag (Section 5.3) is missing")

(grader-try r1-eo-validp-semantics
  (defthm grader-even-validp-zero
    (equal (even-proof-validp (even-proof-zero) n) (equal n 0))
    :hints (("Goal" :in-theory (union-theories (current-theory :here)
                                               (theory 'grader-eo-validp))))
    :rule-classes nil)
  (defthm grader-odd-validp-from-even
    (implies (even-proofp p)
             (equal (odd-proof-validp (odd-proof-from-even m p) n)
                    (and (equal n (1+ m)) (even-proof-validp p m))))
    :hints (("Goal" :in-theory (union-theories (current-theory :here)
                                               (theory 'grader-eo-validp))))
    :rule-classes nil))

(grader-formula r1-eo-even-zero even-zero (even 0))
(grader-formula r1-eo-odd-from-even odd-from-even (implies (even n) (odd (1+ n))))
(grader-formula r1-eo-even-from-odd even-from-odd (implies (odd n) (even (1+ n))))
(grader-formula r1-eo-even-when-proof-validp even-when-proof-validp
  (implies (and (even-proof-validp proof n) (even-proofp proof)) (even n)))
(grader-formula r1-eo-odd-when-proof-validp odd-when-proof-validp
  (implies (and (odd-proof-validp proof n) (odd-proofp proof)) (odd n)))

(grader-assert r1-eo-alt-constraints
  (let ((expected (grader-translate-list
                   '((even-alt 0)
                     (implies (even-alt n) (odd-alt (1+ n)))
                     (implies (odd-alt n) (even-alt (1+ n))))
                   (w state))))
    (and (getpropc 'even-alt 'constrainedp nil (w state))
         (getpropc 'odd-alt 'constrainedp nil (w state))
         (grader-set-equal (grader-constraints 'even-alt (w state)) expected)
         (grader-set-equal (grader-constraints 'odd-alt (w state)) expected)))
  "even-alt and odd-alt are not introduced by one encapsulate constrained exactly by the three alt rules")
(grader-formula r1-eo-alt-zero even-alt-zero (even-alt 0))
(grader-formula r1-eo-alt-from-even odd-alt-from-even (implies (even-alt n) (odd-alt (1+ n))))
(grader-formula r1-eo-alt-from-odd even-alt-from-odd (implies (odd-alt n) (even-alt (1+ n))))
(grader-formula r1-eo-even-alt-when-proof-validp even-alt-when-even-proof-validp
  (implies (even-proof-validp proof n) (even-alt n)))
(grader-formula r1-eo-odd-alt-when-proof-validp odd-alt-when-odd-proof-validp
  (implies (odd-proof-validp proof n) (odd-alt n)))
(grader-formula r1-eo-even-alt-when-even even-alt-when-even (implies (even n) (even-alt n)))
(grader-formula r1-eo-odd-alt-when-odd odd-alt-when-odd (implies (odd n) (odd-alt n)))

(grader-assert r1-eo-induct
  (and (grader-set-equal (getpropc 'even-induct 'recursivep nil (w state))
                         '(even-induct odd-induct))
       (equal (grader-formals 'even-induct (w state)) '(n))
       (equal (grader-formals 'odd-induct (w state)) '(n))
       (assoc-eq 'even-induct (table-alist 'flag::flag-fns (w state))))
  "even-induct/odd-induct are not mutually recursive functions of n accompanied by a flag macro (Section 4.5)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Footnote 4: just-0 (non-recursive)

(grader-assert r1-j0-proof-type
  (and (equal (grader-flextypes-summary 'p-proof (w state)) '((p-proof (:zero))))
       (not (cdr (assoc 'fty::recp (grader-sum 'p-proof 'p-proof (w state))))))
  "p-proof is not a non-recursive deftagsum with the single summand :zero (Section 4.2: recursive exactly when the predicate depends on itself)")
(grader-assert r1-recp
  (and (cdr (assoc 'fty::recp (grader-sum 'r*-proof 'r*-proof (w state))))
       (cdr (assoc 'fty::recp (grader-sum 'nat-proof 'nat-proof (w state)))))
  "r*-proof or nat-proof is not recursive")
(grader-assert r1-j0-pred
  (equal (grader-formals 'p (w state)) '(x))
  "p does not have formals (x)")
(grader-assert r1-j0-validp-formals
  (equal (grader-formals 'p-proof-validp (w state)) '(proof x))
  "p-proof-validp does not have formals (proof x)")
(grader-formula r1-j0-zero p-zero (p 0))
(grader-formula r1-j0-when-proof-validp p-when-proof-validp
  (implies (and (p-proof-validp proof x) (p-proofp proof)) (p x)))
(grader-formula r1-j0-alt-zero p-alt-zero (p-alt 0))
(grader-formula r1-j0-alt-when-proof-validp p-alt-when-p-proof-validp
  (implies (p-proof-validp proof x) (p-alt x)))
(grader-formula r1-j0-alt-when-p p-alt-when-p (implies (p x) (p-alt x)))

(grader-final)
