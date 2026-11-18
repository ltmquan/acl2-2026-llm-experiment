# tool-remora: what a person must inspect

`grade.sh <work>` prints `R<n> PASS|FAIL|MANUAL`. The grading copy (path on the first line) keeps all logs;
`zz-grader/` in it holds the certified grader books, which a reviewer can include in ACL2 master
(`/opt/acl2-master/saved_acl2`, after `(include-book "kestrel/remora/portcullis" :dir :system)` and
`(in-package "REMORA")`).

## R2 — a changed statement (MANUAL)
R2 is MANUAL when a theorem exists with the paper's name, its statement differs from `targets.lisp` (the
paper's, arg2l read as arg2), and the name is mentioned in `/work/README.md`. The diff (paper vs model) is
printed. Read the README's justification. PASS only if all of these hold:
1. the change is forced by the master interpreter (the paper's statement is false, or does not translate,
   against it), and README.md says why;
2. it is the smallest such change: typically an added hypothesis excluding a case the interpreter now treats
   differently (empty frames routed to `eval-app-empty`: e.g. `(not (member-equal 0 pframe))` or
   `pos-listp` of a frame; a lower bound on `limit`), or a package qualifier such as `acl2::pos-listp`
   (already accepted mechanically, see NOTES.md);
3. the conclusion is unchanged, and no hypothesis was added that is not needed (to judge, the reviewer may
   ask: would the paper's statement be false without it? Try the counterexample README gives, or construct
   one with an empty vector or a small `limit`);
4. the theorem is still non-vacuous: R1's check already shows the paper's hypotheses hold on
   `[1 2] + [[1 2] [3 4]]`; evaluate any added hypothesis on the same values (constants in
   `zz-grader/grade-r4.lisp`: `*grader-plus*`, `*grader-v12*`, `*grader-m1234*`, limit 1000).
FAIL otherwise. (A changed statement not mentioned in README.md is a mechanical FAIL.)

## R3 — the commutativity corollary (always MANUAL)
The prompt lets the model state it. grade.sh lists theorems that mention both `(eval-app f (list a b) l)`
and `(eval-app f (list b a) l)`. Find the theorem (README.md should name it). PASS if:
1. it is a `defthm`/`defrule` (not local) in a certified book;
2. its conclusion is `(equal (eval-app f (list a b) l) (eval-app f (list b a) l))`, or an equivalent stated
   through the paper's final theorem (e.g. equality of the two right-hand sides is not enough unless it is
   connected to `eval-app`);
3. `f` is restricted to integer addition (`int-binary` primop with op `:add`), and the other hypotheses are
   only well-formedness, nested-vectors-of-base-values, prefix-compatibility of the two frames, and non-error
   of one or both applications;
4. non-vacuity: in ACL2 master, include the model's books and `zz-grader/grade-r4`, bind
   `f = *grader-plus*`, `a = *grader-v12*`, `b = *grader-m1234*`, `l = 1000` (other variables: the values
   they are equated to) and evaluate every hypothesis: all must be true. (`grade-r4.lisp` already checks
   that both orders give `[[2 3] [5 6]]` on the interpreter.)

## R4 — examples.lisp (MANUAL after the mechanical part)
Mechanical part: `/work/examples.lisp` exists, certifies, contains `assert-event`. Also reported: the
grader's own `grade-r4.lisp` (independent of the model) passes on the interpreter. Read `examples.lisp`.
PASS if its `assert-event`s, by evaluation with the books' interpreter (parse+check+`eval-top-expr`, or
`eval-app` on constructed values), check:
1. `[1 2] + [[1 2] [3 4]]` equals `[[2 3] [5 6]]` (the value is compared, not only "no error");
2. the ill-formed additions give errors. Section 2 has three: `[1 2 3] + [4 5]`, `[1 2 3 4] + [[1 2] [3 4]]`,
   and `[1 2] + [[1 2] [[5 6]]]` (printed ragged; the text says its shapes are [2] and [3 2], i.e.
   `[[1 2] [3 4] [5 6]]`). The prompt says "the two"; accept any two of the three, with either reading of the
   third. An error at the static-checking stage counts (on master the checker rejects all three).
FAIL if an example is missing or only asserted about a hand-written constant.

## R5 — a `.lisp` file that is not a book
If README.md says a failing `.lisp` is not a book (an `ld` script) and nothing else needs it, treat R5 as
PASS and note it.
