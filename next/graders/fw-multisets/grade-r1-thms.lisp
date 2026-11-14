; Grader R1 (fw-multisets): the required theorems, in our statements.  Each is
; proved :by / :use the model's lemma of the required name (count-of-X), or by
; the model's rules with the model's definitions of the required functions
; disabled and no induction.  Where the unconditional statement fails, the
; statement with bagp (and natp) hypotheses on the arguments is tried, since
; the behavior on non-bags is the model's choice.  Results are printed as
; GRADER-OK / GRADER-FAIL lines.
(in-package "ACL2")
(include-book "grader-mset-model-defs")
(include-book "std/lists/duplicity" :dir :system)

; ---------------------------------------------------------------- closure
(gr-thm gr-bagp-of-bfix (mset::bagp (mset::bfix b)))
(gr-thm gr-bagp-of-empty (mset::bagp (mset::empty)))
(gr-thm gr-bagp-of-insert (mset::bagp (mset::insert a b)) :hyps ((mset::bagp b)))
(gr-thm gr-bagp-of-insert-n (mset::bagp (mset::insert-n a n b)) :hyps ((natp n) (mset::bagp b)))
(gr-thm gr-bagp-of-delete (mset::bagp (mset::delete a b)) :hyps ((mset::bagp b)))
(gr-thm gr-bagp-of-delete-all (mset::bagp (mset::delete-all a b)) :hyps ((mset::bagp b)))
(gr-thm gr-bagp-of-sum (mset::bagp (mset::sum x y)) :hyps ((mset::bagp x) (mset::bagp y)))
(gr-thm gr-bagp-of-union (mset::bagp (mset::union x y)) :hyps ((mset::bagp x) (mset::bagp y)))
(gr-thm gr-bagp-of-intersect (mset::bagp (mset::intersect x y)) :hyps ((mset::bagp x) (mset::bagp y)))
(gr-thm gr-bagp-of-diff (mset::bagp (mset::diff x y)) :hyps ((mset::bagp x) (mset::bagp y)))
(gr-thm gr-bagp-of-from-list (mset::bagp (mset::from-list l)))

; ---------------------------------------------------------------- count (function spec: a natural)
(gr-thm gr-natp-of-count (natp (mset::count a b)) :hyps ((mset::bagp b)))

; ---------------------------------------------------------------- count-of-X (names fixed by the prompt)
(gr-name-exists mset::count-of-empty)
(gr-name-exists mset::count-of-insert)
(gr-name-exists mset::count-of-insert-n)
(gr-name-exists mset::count-of-delete)
(gr-name-exists mset::count-of-delete-all)
(gr-name-exists mset::count-of-sum)
(gr-name-exists mset::count-of-union)
(gr-name-exists mset::count-of-intersect)
(gr-name-exists mset::count-of-diff)
(gr-name-exists mset::count-of-from-list)
(gr-rewrite-rule mset::count-of-empty)
(gr-rewrite-rule mset::count-of-insert)
(gr-rewrite-rule mset::count-of-insert-n)
(gr-rewrite-rule mset::count-of-delete)
(gr-rewrite-rule mset::count-of-delete-all)
(gr-rewrite-rule mset::count-of-sum)
(gr-rewrite-rule mset::count-of-union)
(gr-rewrite-rule mset::count-of-intersect)
(gr-rewrite-rule mset::count-of-diff)
(gr-rewrite-rule mset::count-of-from-list)

(gr-thm gr-count-of-empty
  (equal (mset::count a (mset::empty)) 0)
  :by mset::count-of-empty)
(gr-thm gr-count-of-insert
  (equal (mset::count a (mset::insert x b))
         (if (equal a x) (+ 1 (mset::count a b)) (mset::count a b)))
  :hyps ((mset::bagp b)) :by mset::count-of-insert)
(gr-thm gr-count-of-insert-n
  (equal (mset::count a (mset::insert-n x n b))
         (if (equal a x) (+ (nfix n) (mset::count a b)) (mset::count a b)))
  :hyps ((natp n) (mset::bagp b)) :by mset::count-of-insert-n)
(gr-thm gr-count-of-delete
  (equal (mset::count a (mset::delete x b))
         (if (equal a x) (nfix (- (mset::count a b) 1)) (mset::count a b)))
  :hyps ((mset::bagp b)) :by mset::count-of-delete)
(gr-thm gr-count-of-delete-all
  (equal (mset::count a (mset::delete-all x b))
         (if (equal a x) 0 (mset::count a b)))
  :hyps ((mset::bagp b)) :by mset::count-of-delete-all)
(gr-thm gr-count-of-sum
  (equal (mset::count a (mset::sum x y))
         (+ (mset::count a x) (mset::count a y)))
  :hyps ((mset::bagp x) (mset::bagp y)) :by mset::count-of-sum)
(gr-thm gr-count-of-union
  (equal (mset::count a (mset::union x y))
         (max (mset::count a x) (mset::count a y)))
  :hyps ((mset::bagp x) (mset::bagp y)) :by mset::count-of-union)
(gr-thm gr-count-of-intersect
  (equal (mset::count a (mset::intersect x y))
         (min (mset::count a x) (mset::count a y)))
  :hyps ((mset::bagp x) (mset::bagp y)) :by mset::count-of-intersect)
(gr-thm gr-count-of-diff
  (equal (mset::count a (mset::diff x y))
         (nfix (- (mset::count a x) (mset::count a y))))
  :hyps ((mset::bagp x) (mset::bagp y)) :by mset::count-of-diff)
(gr-thm gr-count-of-from-list
  (equal (mset::count a (mset::from-list l))
         (duplicity a l))
  :by mset::count-of-from-list)

; ---------------------------------------------------------------- in
(gr-thm gr-in-iff-count
  (iff (mset::in a b) (< 0 (mset::count a b)))
  :hyps ((mset::bagp b)))

; ---------------------------------------------------------------- support (function spec: the keys, an oset)
(gr-thm gr-support-is-keys
  (equal (mset::support b) (omap::keys (mset::bfix b)))
  :hyps ((mset::bagp b)))
(gr-thm gr-setp-of-support (set::setp (mset::support b)))

; ---------------------------------------------------------------- subbag
(gr-thm gr-subbag-count-leq
  (implies (mset::subbag x y)
           (<= (mset::count a x) (mset::count a y)))
  :hyps ((mset::bagp x) (mset::bagp y)))
(gr-thm gr-subbag-reflexive (mset::subbag x x) :hyps ((mset::bagp x)))
(gr-thm gr-subbag-antisymmetric
  (implies (and (mset::bagp x) (mset::bagp y) (mset::subbag x y) (mset::subbag y x))
           (equal x y)))
(gr-thm gr-subbag-transitive
  (implies (and (mset::subbag x y) (mset::subbag y z))
           (mset::subbag x z))
  :hyps ((mset::bagp x) (mset::bagp y) (mset::bagp z)))

; ---------------------------------------------------------------- cardinality
(gr-thm gr-cardinality-of-empty (equal (mset::cardinality (mset::empty)) 0))
(gr-thm gr-cardinality-of-insert
  (equal (mset::cardinality (mset::insert a b)) (+ 1 (mset::cardinality b)))
  :hyps ((mset::bagp b)))
(gr-thm gr-cardinality-of-delete
  (implies (mset::in a b)
           (equal (mset::cardinality (mset::delete a b)) (- (mset::cardinality b) 1)))
  :hyps ((mset::bagp b)))
(gr-thm gr-cardinality-of-sum
  (equal (mset::cardinality (mset::sum x y))
         (+ (mset::cardinality x) (mset::cardinality y)))
  :hyps ((mset::bagp x) (mset::bagp y)))

; ---------------------------------------------------------------- to-list / from-list
(gr-thm gr-from-list-of-to-list
  (equal (mset::from-list (mset::to-list b)) (mset::bfix b)))
(gr-thm gr-len-of-to-list
  (equal (len (mset::to-list b)) (mset::cardinality b)))

; ---------------------------------------------------------------- algebra
(gr-thm gr-sum-commutative (equal (mset::sum x y) (mset::sum y x))
  :hyps ((mset::bagp x) (mset::bagp y)))
(gr-thm gr-sum-associative (equal (mset::sum (mset::sum x y) z) (mset::sum x (mset::sum y z)))
  :hyps ((mset::bagp x) (mset::bagp y) (mset::bagp z)))
(gr-thm gr-union-commutative (equal (mset::union x y) (mset::union y x))
  :hyps ((mset::bagp x) (mset::bagp y)))
(gr-thm gr-union-associative (equal (mset::union (mset::union x y) z) (mset::union x (mset::union y z)))
  :hyps ((mset::bagp x) (mset::bagp y) (mset::bagp z)))
(gr-thm gr-intersect-commutative (equal (mset::intersect x y) (mset::intersect y x))
  :hyps ((mset::bagp x) (mset::bagp y)))
(gr-thm gr-intersect-associative
  (equal (mset::intersect (mset::intersect x y) z) (mset::intersect x (mset::intersect y z)))
  :hyps ((mset::bagp x) (mset::bagp y) (mset::bagp z)))
