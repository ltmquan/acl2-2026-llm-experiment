; Tests for the :EXEC facility of DEFINDUCTIVE.

(in-package "ACL2")

(include-book "definductive")

(include-book "std/testing/must-be-redundant" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (i) Even and odd naturals.

(definductive evenodd-exec
  :preds ((even x) (odd x))
  :irules ((even-zero ()
                      (even 0))
           (odd-succ ((natp n) (even n))
                     (odd (1+ n)))
           (even-succ ((natp n) (odd n))
                      (even (1+ n))))
  :exec ((even :name even-exec :measure (acl2-count x))
         (odd :name odd-exec :measure (acl2-count x)))
  :exec-binds ((odd-succ (n (1- x)))
               (even-succ (n (1- x)))))

(must-be-redundant
 (defthm even-exec-correct
   (iff (even-exec x) (even x))))

(must-be-redundant
 (defthm odd-exec-correct
   (iff (odd-exec x) (odd x))))

(must-be-redundant
 (defthm booleanp-of-even-exec
   (booleanp (even-exec x))))

(must-be-redundant
 (defthm booleanp-of-odd-exec
   (booleanp (odd-exec x))))

(assert-event (even-exec 0))
(assert-event (not (odd-exec 0)))
(assert-event (odd-exec 1))
(assert-event (not (even-exec 1)))
(assert-event (even-exec 100))
(assert-event (not (odd-exec 100)))
(assert-event (odd-exec 101))
(assert-event (not (even-exec -2)))
(assert-event (not (odd-exec -1)))
(assert-event (not (even-exec 1/2)))
(assert-event (not (even-exec 'a)))
(assert-event (not (odd-exec '(1 2))))

; The executable functions are mutually recursive,
; and they do not call the predicates, their witnesses, or the proof checkers.

(assert-event (equal (getpropc 'even-exec 'recursivep nil (w state))
                     '(even-exec odd-exec)))

(defun fns-called-by-exec (fns wrld)
  (declare (xargs :mode :program))
  (if (endp fns)
      nil
    (union-eq (all-fnnames (body (car fns) nil wrld))
              (fns-called-by-exec (cdr fns) wrld))))

(defun no-forbidden-calls (fns forbidden wrld)
  (declare (xargs :mode :program))
  (not (intersectp-eq (fns-called-by-exec fns wrld) forbidden)))

(assert-event
 (no-forbidden-calls '(even-exec odd-exec)
                     '(even odd even-proof odd-proof
                       even-proof-validp odd-proof-validp)
                     (w state)))

; The correctness theorems can be used to evaluate the predicates.

(defthm even-of-10
  (even 10)
  :hints (("Goal" :use (:instance even-exec-correct (x 10))
           :in-theory '((:e even-exec)))))

(defthm not-odd-of-10
  (not (odd 10))
  :hints (("Goal" :use (:instance odd-exec-correct (x 10))
           :in-theory '((:e odd-exec)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (ii) Naturals and finitely branching trees of naturals:
; a tree is (cons label subtrees), where label is a natural
; and subtrees is a list of trees.

(definductive nat-trees
  :preds ((nat x)
          (tree x)
          (forest x))
  :irules ((nat-zero ()
                     (nat 0))
           (nat-succ ((natp n) (nat n))
                     (nat (1+ n)))
           (tree-node ((nat label) (forest subtrees))
                      (tree (cons label subtrees)))
           (forest-nil ()
                       (forest nil))
           (forest-cons ((tree first) (forest rest))
                        (forest (cons first rest))))
  :exec ((nat :name nat-exec :measure (acl2-count x))
         (tree :name tree-exec :measure (acl2-count x))
         (forest :name forest-exec :measure (acl2-count x)))
  :exec-binds ((nat-succ (n (1- x)))
               (tree-node (label (car x)) (subtrees (cdr x)))
               (forest-cons (first (car x)) (rest (cdr x)))))

(must-be-redundant
 (defthm nat-exec-correct
   (iff (nat-exec x) (nat x))))

(must-be-redundant
 (defthm tree-exec-correct
   (iff (tree-exec x) (tree x))))

(must-be-redundant
 (defthm forest-exec-correct
   (iff (forest-exec x) (forest x))))

(must-be-redundant
 (defthm booleanp-of-nat-exec
   (booleanp (nat-exec x))))

(must-be-redundant
 (defthm booleanp-of-tree-exec
   (booleanp (tree-exec x))))

(must-be-redundant
 (defthm booleanp-of-forest-exec
   (booleanp (forest-exec x))))

(assert-event (nat-exec 0))
(assert-event (nat-exec 5))
(assert-event (not (nat-exec -5)))
(assert-event (not (nat-exec 'x)))
(assert-event (forest-exec nil))
(assert-event (tree-exec '(3)))
(assert-event (tree-exec '(3 (1) (2 (0) (7)))))
(assert-event (forest-exec '((1) (2 (0) (7)))))
(assert-event (not (tree-exec nil)))
(assert-event (not (tree-exec '(a))))
(assert-event (not (tree-exec '(3 (1) (2 (-1))))))
(assert-event (not (tree-exec '(3 (1) . 4))))
(assert-event (not (forest-exec '(1))))

(assert-event
 (no-forbidden-calls '(nat-exec tree-exec forest-exec)
                     '(nat tree forest nat-proof tree-proof forest-proof)
                     (w state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (iii) A typing judgement for a small expression language,
; with three mutually recursive predicates in one clique.
; Expressions are:
;   integer literals, boolean literals (T and NIL),
;   variables (non-boolean symbols), whose types are in an environment,
;   (PLUS A B), (LT A B), (NOT A), (IF C A B), and (EQ A B),
; where EQ compares two well-typed expressions of any type.
; The environment is an alist from variables to :INT or :BOOL.

(definductive typing
  :preds ((int-expr env e)
          (bool-expr env e)
          (typed-expr env e))
  :irules ((int-lit ((integerp e))
                    (int-expr env e))
           (int-var ((symbolp e)
                     (not (booleanp e))
                     (equal (cdr (assoc-equal e env)) :int))
                    (int-expr env e))
           (int-plus ((int-expr env a) (int-expr env b))
                     (int-expr env (list 'plus a b)))
           (int-if ((bool-expr env c) (int-expr env a) (int-expr env b))
                   (int-expr env (list 'if c a b)))
           (bool-lit ((booleanp e))
                     (bool-expr env e))
           (bool-var ((symbolp e)
                      (not (booleanp e))
                      (equal (cdr (assoc-equal e env)) :bool))
                     (bool-expr env e))
           (bool-lt ((int-expr env a) (int-expr env b))
                    (bool-expr env (list 'lt a b)))
           (bool-not ((bool-expr env a))
                     (bool-expr env (list 'not a)))
           (bool-if ((bool-expr env c) (bool-expr env a) (bool-expr env b))
                    (bool-expr env (list 'if c a b)))
           (bool-eq ((typed-expr env a) (typed-expr env b))
                    (bool-expr env (list 'eq a b)))
           (typed-int ((int-expr env e))
                      (typed-expr env e))
           (typed-bool ((bool-expr env e))
                       (typed-expr env e)))
  :verify-guards nil
  :exec ((int-expr :name int-expr-exec :measure (* 2 (acl2-count e)))
         (bool-expr :name bool-expr-exec :measure (* 2 (acl2-count e)))
         (typed-expr :name typed-expr-exec
                     :measure (1+ (* 2 (acl2-count e)))))
  :exec-binds ((int-plus (a (cadr e)) (b (caddr e)))
               (int-if (c (cadr e)) (a (caddr e)) (b (cadddr e)))
               (bool-lt (a (cadr e)) (b (caddr e)))
               (bool-not (a (cadr e)))
               (bool-if (c (cadr e)) (a (caddr e)) (b (cadddr e)))
               (bool-eq (a (cadr e)) (b (caddr e)))))

(must-be-redundant
 (defthm int-expr-exec-correct
   (iff (int-expr-exec env e) (int-expr env e))))

(must-be-redundant
 (defthm bool-expr-exec-correct
   (iff (bool-expr-exec env e) (bool-expr env e))))

(must-be-redundant
 (defthm typed-expr-exec-correct
   (iff (typed-expr-exec env e) (typed-expr env e))))

(must-be-redundant
 (defthm booleanp-of-int-expr-exec
   (booleanp (int-expr-exec env e))))

(must-be-redundant
 (defthm booleanp-of-bool-expr-exec
   (booleanp (bool-expr-exec env e))))

(must-be-redundant
 (defthm booleanp-of-typed-expr-exec
   (booleanp (typed-expr-exec env e))))

(assert-event (int-expr-exec nil 3))
(assert-event (not (bool-expr-exec nil 3)))
(assert-event (bool-expr-exec nil t))
(assert-event (int-expr-exec '((x . :int)) 'x))
(assert-event (not (int-expr-exec '((x . :bool)) 'x)))
(assert-event (bool-expr-exec '((x . :bool)) 'x))
(assert-event (int-expr-exec '((x . :int)) '(plus x (plus 1 2))))
(assert-event (not (int-expr-exec '((x . :bool)) '(plus x 1))))
(assert-event (bool-expr-exec '((x . :int)) '(lt x 7)))
(assert-event (int-expr-exec '((x . :int) (b . :bool))
                             '(if (not b) (plus x 1) 0)))
(assert-event (not (int-expr-exec '((x . :int) (b . :bool))
                                  '(if (not b) (lt x 1) 0))))
(assert-event (bool-expr-exec '((x . :int) (b . :bool))
                              '(if b (lt x 1) (eq b nil))))
(assert-event (bool-expr-exec nil '(eq (plus 1 2) 3)))
(assert-event (bool-expr-exec nil '(eq (eq 1 2) t)))
(assert-event (typed-expr-exec nil '(eq (eq 1 2) t)))
(assert-event (typed-expr-exec nil '(plus 1 2)))
(assert-event (not (typed-expr-exec nil '(plus 1 t))))
(assert-event (not (typed-expr-exec nil '(plus 1 2 3))))
(assert-event (not (typed-expr-exec nil 'undefined-var)))
(assert-event (not (typed-expr-exec nil "string")))

(assert-event
 (no-forbidden-calls '(int-expr-exec bool-expr-exec typed-expr-exec)
                     '(int-expr bool-expr typed-expr
                       int-expr-proof bool-expr-proof typed-expr-proof)
                     (w state)))

(assert-event (equal (getpropc 'int-expr-exec 'recursivep nil (w state))
                     '(int-expr-exec bool-expr-exec typed-expr-exec)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (iv) Reflexive and transitive closure:
; the middle variable Y of the transitivity rule has no binding,
; so :EXEC fails.

(defstub r (* *) => *)

(must-fail
 (definductive refl-trans-closure-exec
   :preds ((r* a b))
   :irules ((base ((r x y))
                  (r* x y))
            (refl ()
                  (r* x x))
            (trans ((r* x y) (r* y z))
                   (r* x z)))
   :exec ((r* :name r*-exec :measure (acl2-count a)))))

; The failure is due to :EXEC: without it, the same definition succeeds.

(must-succeed*
 (definductive refl-trans-closure-noexec
   :preds ((r* a b))
   :irules ((base ((r x y))
                  (r* x y))
            (refl ()
                  (r* x x))
            (trans ((r* x y) (r* y z))
                   (r* x z)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Other failures.

; Termination fails without the natp premise.

(must-fail
 (definductive nat-nonterminating
   :preds ((nnat x))
   :irules ((nnat-zero () (nnat 0))
            (nnat-succ ((acl2-numberp n) (nnat n)) (nnat (1+ n))))
   :verify-guards nil
   :exec ((nnat :name nnat-exec))
   :exec-binds ((nnat-succ (n (1- x))))))

; Binding adequacy fails with a wrong binding.

(must-fail
 (definductive nat-wrong-binding
   :preds ((wnat x))
   :irules ((wnat-zero () (wnat 0))
            (wnat-succ ((natp n) (wnat n)) (wnat (1+ n))))
   :exec ((wnat :name wnat-exec :measure (nfix x)))
   :exec-binds ((wnat-succ (n (- x 2))))))

; Missing entries in :EXEC.

(must-fail
 (definductive evenodd-missing
   :preds ((even2 x) (odd2 x))
   :irules ((even2-zero () (even2 0))
            (odd2-succ ((natp n) (even2 n)) (odd2 (1+ n)))
            (even2-succ ((natp n) (odd2 n)) (even2 (1+ n))))
   :exec ((even2 :name even2-exec))
   :exec-binds ((odd2-succ (n (1- x)))
                (even2-succ (n (1- x))))))

; Binding terms may only use the formals.

(must-fail
 (definductive nat-bad-binding-vars
   :preds ((bnat x))
   :irules ((bnat-zero () (bnat 0))
            (bnat-succ ((natp n) (bnat n)) (bnat (1+ n))))
   :exec ((bnat :name bnat-exec))
   :exec-binds ((bnat-succ (n (1- y))))))

; Bindings must be for variables of the rule.

(must-fail
 (definductive nat-bad-binding-var
   :preds ((cnat x))
   :irules ((cnat-zero () (cnat 0))
            (cnat-succ ((natp n) (cnat n)) (cnat (1+ n))))
   :exec ((cnat :name cnat-exec))
   :exec-binds ((cnat-succ (n (1- x)) (m (1- x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Further successful variants.

(must-succeed*

 ; Default measure; non-recursive predicates;
 ; a rule variable occurring twice in the conclusion;
 ; rules with the same name for different predicates, distinguished by
 ; (PRED RULE) in :EXEC-BINDS; predicates of a preceding clique;
 ; and :EXEC-HINTS.

 (definductive misc
   :preds ((same x y)
           (small x)
           (pair-of-small p)
           (len-even l))
   :irules ((same-rule ()
                       (same x x))
            (base ((natp n) (< n 10))
                  (small n))
            (base ((small a) (small b))
                  (pair-of-small (cons a b)))
            (len-nil ()
                     (len-even nil))
            (len-cons2 ((same a a) (len-even l))
                       (len-even (cons a (cons b l)))))
   :exec ((same :name same-exec)
          (small :name small-exec)
          (pair-of-small :name pair-of-small-exec)
          (len-even :name len-even-exec :measure (len l)))
   :exec-binds (((pair-of-small base) (a (car p)) (b (cdr p)))
                (len-cons2 (a (car l)) (b (cadr l)) (l (cddr l))))
   :exec-hints (("Goal" :in-theory (enable len))))

 (assert-event (same-exec 1 1))
 (assert-event (not (same-exec 1 2)))
 (assert-event (small-exec 3))
 (assert-event (not (small-exec 10)))
 (assert-event (pair-of-small-exec '(3 . 4)))
 (assert-event (not (pair-of-small-exec '(3 . 40))))
 (assert-event (len-even-exec '(1 2 3 4)))
 (assert-event (not (len-even-exec '(1 2 3))))

 (must-be-redundant
  (defthm len-even-exec-correct
    (iff (len-even-exec l) (len-even l)))))

(must-succeed*

 ; Variables of the rules that coincide with formals of the predicate
 ; in different positions.

 (definductive swapped
   :preds ((le2 x y))
   :irules ((le2-refl ((natp x)) (le2 x x))
            (le2-step ((natp x) (le2 y x)) (le2 y (1+ x))))
   :verify-guards nil
   :exec ((le2 :name le2-exec :measure (acl2-count y)))
   :exec-binds ((le2-step (x (1- y)))))

 (assert-event (le2-exec 3 5))
 (assert-event (le2-exec 3 3))
 (assert-event (not (le2-exec 5 3)))
 (assert-event (not (le2-exec -1 3))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; An explicit :EXEC NIL is the same as no :EXEC.

(must-succeed*
 (definductive no-exec
   :preds ((zp0 x))
   :irules ((zp0-rule () (zp0 0)))
   :exec nil)
 (assert-event (not (function-symbolp 'zp0-exec (w state)))))

; :EXEC-BINDS without :EXEC is an error.

(must-fail
 (definductive binds-without-exec
   :preds ((zp1 x))
   :irules ((zp1-rule () (zp1 0)))
   :exec-binds ((zp1-rule))))
