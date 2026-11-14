; Hidden test book for fw-definductive-exec, requirement 4 ("the checker's own
; definitions with :exec ... are admitted, with e-correct and booleanp-of-e in
; exactly the form above, and the executable functions run on concrete inputs").
; Three definductive calls with :exec, written to the interface in the prompt,
; and for each predicate p with executable version E:
;  - E-correct (the prompt's e-correct for :name e) has exactly the form (iff (E x1 ... xn) (p x1 ... xn));
;  - booleanp-of-E has exactly the form (booleanp (E x1 ... xn));
;  - E has the formals of p, and nothing reachable from its body (outside its
;    own clique) is a defun-sk predicate (non-executable), a witness
;    (constrained) or a defchoose;
;  - E evaluates on concrete data (assert-event).  The inputs are chosen so
;    that no evaluation order of the rule tests and bindings violates a guard
;    of a primitive (default guard checking is on in books).

(in-package "ACL2")

(include-book "definductive")
(include-book "grader-utils")
(include-book "std/testing/assert-bang" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; 1. Less-or-equal on naturals: one recursive predicate, a binding for a
;    variable under 1+ in the conclusion, a measure on the second formal.

(grader-try h1-le
  (definductive grader-le
    :preds ((le a b))
    :irules ((le-refl ((natp n)) (le n n))
             (le-step ((natp n) (le m n)) (le m (1+ n))))
    :exec ((le :name le-exec :measure (nfix b)))
    :exec-binds ((le-step (n (1- b))))))

(grader-formula h1-le-correct le-exec-correct (iff (le-exec a b) (le a b)))
(grader-formula h1-le-booleanp booleanp-of-le-exec (booleanp (le-exec a b)))
(grader-assert h1-le-formals
  (equal (grader-formals 'le-exec (w state)) '(a b))
  "le-exec does not have the formals (a b) of le")
(grader-assert h1-le-clean
  (null (grader-exec-clean 'le-exec (w state)))
  "le-exec reaches a defun-sk predicate, witness, defchoose or constrained function")
(grader-try h1-le-run
  (assert-event (equal (le-exec 2 5) t))
  (assert-event (equal (le-exec 3 3) t))
  (assert-event (equal (le-exec 0 0) t))
  (assert-event (equal (le-exec 5 2) nil))
  (assert-event (equal (le-exec 1 -1) nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; 2. Even-length and odd-length lists: a clique of two predicates over
;    conclusions (cons a l), with bindings through car/cdr, two levels.

(grader-try h2-evl
  (definductive grader-evl
    :preds ((evl x) (oddl x))
    :irules ((evl-nil () (evl nil))
             (evl-cons ((oddl l)) (evl (cons a l)))
             (oddl-cons ((evl l)) (oddl (cons a l))))
    :exec ((evl :name evl-exec :measure (acl2-count x))
           (oddl :name oddl-exec :measure (acl2-count x)))
    :exec-binds ((evl-cons (a (car x)) (l (cdr x)))
                 (oddl-cons (a (car x)) (l (cdr x))))))

(grader-formula h2-evl-correct evl-exec-correct (iff (evl-exec x) (evl x)))
(grader-formula h2-oddl-correct oddl-exec-correct (iff (oddl-exec x) (oddl x)))
(grader-formula h2-evl-booleanp booleanp-of-evl-exec (booleanp (evl-exec x)))
(grader-formula h2-oddl-booleanp booleanp-of-oddl-exec (booleanp (oddl-exec x)))
(grader-assert h2-formals
  (and (equal (grader-formals 'evl-exec (w state)) '(x))
       (equal (grader-formals 'oddl-exec (w state)) '(x))
       (grader-set-equal (getpropc 'evl-exec 'recursivep nil (w state))
                         '(evl-exec oddl-exec)))
  "evl-exec/oddl-exec do not have formals (x) or are not mutually recursive")
(grader-assert h2-clean
  (and (null (grader-exec-clean 'evl-exec (w state)))
       (null (grader-exec-clean 'oddl-exec (w state))))
  "evl-exec or oddl-exec reaches a defun-sk predicate, witness, defchoose or constrained function")
(grader-try h2-run
  (assert-event (equal (evl-exec nil) t))
  (assert-event (equal (evl-exec '(1 2)) t))
  (assert-event (equal (evl-exec '(1 2 3)) nil))
  (assert-event (equal (oddl-exec '(1 2 3)) t))
  (assert-event (equal (oddl-exec nil) nil))
  (assert-event (equal (oddl-exec '(a)) t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; 3. Addition as a ternary relation: a constant conclusion argument, two
;    bound variables in one rule, a literal variable repeated in the
;    conclusion, and the binding-adequacy obligation needing the (natp k)
;    premise.

(grader-try h3-plus
  (definductive grader-plus
    :preds ((plus a b c))
    :irules ((plus-zero ((natp n)) (plus 0 n n))
             (plus-succ ((natp m) (natp k) (plus m n k)) (plus (1+ m) n (1+ k))))
    :exec ((plus :name plus-exec :measure (nfix a)))
    :exec-binds ((plus-succ (m (1- a)) (k (1- c))))))

(grader-formula h3-plus-correct plus-exec-correct
  (iff (plus-exec a b c) (plus a b c)))
(grader-formula h3-plus-booleanp booleanp-of-plus-exec (booleanp (plus-exec a b c)))
(grader-assert h3-formals
  (equal (grader-formals 'plus-exec (w state)) '(a b c))
  "plus-exec does not have the formals (a b c) of plus")
(grader-assert h3-clean
  (null (grader-exec-clean 'plus-exec (w state)))
  "plus-exec reaches a defun-sk predicate, witness, defchoose or constrained function")
(grader-try h3-run
  (assert-event (equal (plus-exec 2 3 5) t))
  (assert-event (equal (plus-exec 0 4 4) t))
  (assert-event (equal (plus-exec 2 3 6) nil))
  (assert-event (equal (plus-exec 2 'x 2) nil))
  (assert-event (equal (plus-exec 1 0 2) nil)))

(grader-final)
