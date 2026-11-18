# fw-multisets grader: notes

## Mapping of requirements
| R | how | mechanical? |
|---|---|---|
| 1 | files (`mset.lisp`, `package.lsp` with `(defpkg "MSET" ...)`, `cert.acl2` mentioning `package.lsp`), and the library meets the prompt's specification: `grade-r1-defs.lisp`, `grade-r1-thms.lisp`; `grade-r1-witness.lisp` only as a fallback | mechanical part; then MANUAL (R1-M: documentation of non-bag behavior) |
| 2 | `mset-tests.lisp` includes `"mset"`; every required function name occurs inside some `assert-event` (or `assert-equal`) | yes |
| 3 | `cert.pl --acl2 /opt/acl2/saved_acl2` on both books | yes |

Revised prompt: R1 now explicitly covers the specification, and the witness names are fixed.

## What R1 checks
- `grade-r1-defs.lisp`: (a) guards verified (`symbol-class` = `:common-lisp-compliant`) for all 20 required
  functions: bagp bfix bequiv empty emptyp count in insert insert-n delete delete-all cardinality support subbag
  sum union intersect diff from-list to-list (a macro or missing function fails); (b) `bequiv` is an
  equivalence (`equivalence-relationp`, i.e. `defequiv`), and has a congruence rule (result `equal` or `bequiv`)
  for every bag argument: emptyp 1, count 2, in 2, insert 2, insert-n 3, delete 2, delete-all 2, cardinality 1,
  support 1, subbag 1 2, sum/union/intersect/diff 1 2, to-list 1; (c) no list conversion: the functions
  reachable from `count`, `insert`, `delete` through the bodies (`unnormalized-body`, so both `mbe` branches) of
  MSET-package functions contain none of: `mset::to-list`, `mset::from-list`, any MSET function whose name
  contains `LIST`, `omap::keys`, `omap::values`, `omap::from-lists`, `omap::from-alist`, `omap::list-in`,
  `omap::list-notin`, `omap::list-lookup`, `strip-cars`, `strip-cdrs`, `alist-keys`, `alist-vals`,
  `true-list-fix`, `list-fix`, `set::mergesort`. Library functions (OMAP, ACL2, SET) are not entered: an omap
  is an alist internally, which is not a "conversion". `bfix` is entered, so a `bfix` that converts to lists
  makes `count` fail.
- `grade-r1-thms.lisp`: 66 checks, our statements in package ACL2 with `mset::` prefixes: closure of bfix,
  empty, insert, insert-n, delete, delete-all, sum, union, intersect, diff, from-list; `(natp (count a b))`; the
  ten `count-of-X` exist and have `:rewrite` rules, and our statements of them (insert-n with `(nfix n)`, delete
  with `(nfix (- c 1))`, diff with `(nfix (- cx cy))`, union `max`, intersect `min`, from-list `duplicity`);
  `(iff (in a b) (< 0 (count a b)))`; `support` = `(omap::keys (bfix b))` and is a `set::setp`; subbag soundness
  `count-le-when-subbag` (exists; `(implies (subbag x y) (<= (count a x) (count a y)))`, `:by` it), reflexivity, antisymmetry (with bagp), transitivity;
  cardinality of empty, insert, delete (when `in`), sum; `(equal (from-list (to-list b)) (bfix b))`,
  `(equal (len (to-list b)) (cardinality b))`; commutativity and associativity of sum, union, intersect.
- Witness theorems with the prompt's names (in `grade-r1-thms.lisp`): `bag-extensionality` and
  `subbag-when-counts-le` exist, and our statements `(implies (and (bagp x) (bagp y) (equal (count
  (count-diff-witness x y) x) (count (count-diff-witness x y) y))) (equal x y))` and `(implies (<= (count
  (subbag-witness x y) x) (count (subbag-witness x y) y)) (subbag x y))` (bagp hypotheses as fallback) are proved
  `:by` them or by the policy below. Only the `count-of-X` are checked for `:rewrite` (extensionality cannot be
  a rewrite rule).
- Fallback (`grade-r1-witness.lisp`, generated only if one of the two fixed-name witness statements fails): the
  same statements with each candidate witness (defun-sk skolems, defchooses, other 2-argument functions of
  mset.lisp, both argument orders), each by `gr-thm`. A success turns that failure (and its missing-name
  failure) into MANUAL; otherwise it stays FAIL.

## Hint policy (recorded as asked)
Each statement passes if one of these succeeds, in order (each under a prover step limit):
1. `:by` the model's lemma of the required name (only `count-of-X` have fixed names);
2. no hints except `:do-not-induct t`, with the **definitions of the 20 required functions disabled**, so the
   model's rewrite rules must do the work;
3. `:by` each model theorem (MSET package) whose formula mentions all MSET functions of the statement
   (subsumption: the model's lemma may have fewer hypotheses or be more general);
4. `:use` each such theorem (and the `count-of-X` lemma), definitions disabled, no induction.
If the unconditional statement fails, the same is tried with `bagp` hypotheses on the bag arguments (and
`natp n`), because the behavior on non-bags is the model's choice. Witness theorems also try the current
theory (definitions enabled) and the theory with W's own definition disabled, still without induction.
Consequence: a theorem the model did not state but that follows from its rules without induction or definition
expansion passes (e.g. commutativity of `sum` from extensionality + `count-of-sum`); we consider that
"available as rewrite rules". Only the ten `count-of-X` are checked for `:rewrite` rule classes, since the
other names are not fixed.
Every check prints `GRADER-OK`/`GRADER-FAIL` and does not stop the book, so failures do not mask each other;
grade.py checks that all 66 checks of `grade-r1-thms` reported.

## Interpretations
- `support` "the keys, as an oset": `(omap::keys (bfix b))` (or with `(bagp b)`), and `set::setp`.
- `count` "a natural; 0 when absent": only `natp` is checked separately; "0 when absent" follows from
  `count-of-empty`/`count-of-delete-all` and is not checked on its own.
- `emptyp`, `bequiv` semantics beyond equivalence/congruence and `to-list`'s order ("in key order") are not
  checked mechanically beyond the round-trip and length theorems; R2's tests evaluate them.
- R2 accepts `assert-equal` as well as `assert-event` (both from std/testing; the prompt says assert-event).

## Validation (scratch only)
- Revised prompt (fixed witness names): stub with `count-diff-witness`, `bag-extensionality` (:rule-classes
  nil), `subbag-witness`, `subbag-when-counts-le`, `count-le-when-subbag`: all 66 theorem checks OK, R1 MANUAL
  (doc only), R2/R3 PASS. Stub with the witness and theorem renamed (`my-diff-w`, `my-ext`): fixed-name checks
  fail, the fallback finds `my-diff-w` (:by `my-ext`), R1 reported MANUAL with that reason.
Earlier runs (before the revision):
- Stub library (functions on omaps; theorems with exactly our statements under `skip-proofs`, antisymmetry and
  transitivity as `:rule-classes nil`; a `defun-sk` witness and a 2-argument `subbag-witness`), run through a
  harness that disables only the banned scan: R1 MANUAL (all 44 defs checks and 61 theorem checks OK, both
  witness theorems OK by search), R2 PASS, R3 PASS.
- Negative stub (insert-n calls `omap::keys`, `count-of-diff` renamed, `to-list` guards not verified, union's
  2nd congruence removed, sum-commutativity lemma removed): FAIL lines for the guard, the congruence, nolist
  insert (reachable via insert-n), and the missing `count-of-diff` name/rule; our count-of-diff statement still
  passes (by the model's rules), and sum commutativity still passes (by extensionality + count-of-sum).
- Nearly empty library (only bagp, count): every check reports (missing functions: "does not translate"), no
  masking.
