# fw-definductive-exec grader: notes

Run: `grade.sh <work-dir>` (ACL2 master at /opt/acl2-master by default). Files: `grade-r1.lisp`,
`grade-hidden.lisp` (our hidden tests), `grader-utils.lisp` (copied from tool-definductive, plus
`grader-exec-clean`), `check-exec.py` (banned events, R1/R3 static checks, and it writes `grade-h2.lisp`).
`grade.sh` also copies the books' `std/util/definductive-tests.lisp`, byte for byte, to
`grade-r2-definductive-tests.lisp` next to the model's files.

## Requirement -> checks
- R1: `/work/definductive.lisp` exists, defines `(defmacro definductive ...)`, certifies and is included by
  grade-r1. It must keep at least 50% of the lines of the books' file (difflib), so that it is a modified
  copy. The kept/changed line counts and the other .lisp files in /work are printed as `R1INFO`.
- R2 (rewiring): the copy of definductive-tests.lisp is unchanged. Its first include, `(include-book
  "definductive")`, is relative, so in the work copy it loads the model's definductive.lisp. It must
  certify with cert.pl and default flags. `cert-flags` lines are deleted from every .acl2 file of the work
  copy, so a copied std/util/cert.acl2 (`:ttags :all`) cannot widen the flags.
- R3: exec-tests.lisp certifies, and a static check of its forms:
  (i) an :exec call with preds even/odd and rules (even 0), (odd (1+ v)) with premises (natp v) before
  (even v), and (even (1+ v)) with (natp v) before (odd v) (any variable name);
  (ii) an :exec call with at least 3 predicates, a singleton clique and a mutual clique, and a conclusion
  argument that is a cons;
  (iii) an :exec call with a dependency clique (SCC) of at least 3 predicates;
  (iv) a must-fail definductive with :exec that has a rule (q x y) (q y z) => (q x z) and no :exec-binds
  entry for y in that rule;
  (v) every :name of every :exec call outside must-fail appears as a call inside an assert-event.
  (ii) and (iii) apply to every predicate of the call (`:exec` must list all of them).
- R4 = grade-hidden.lisp (the checker's own :exec definitions, not shown to the model). It has 3
  definitions, each written to the prompt's :exec/:exec-binds interface: le on naturals (binding
  n := (1- b)); even/odd-length lists (a mutual clique, bindings through car/cdr); addition as a ternary
  relation (a constant argument, two bindings, an adequacy obligation that needs a natp premise). For each
  p with `:name e`, the book checks that the call is admitted; that `e-correct` is exactly
  `(iff (e x1..xn) (p x1..xn))` (translated, `equal`, with p's formals from :preds); that `booleanp-of-e` is
  exactly `(booleanp (e x1..xn))`; and that e has p's formals. It also checks executability: every function
  reachable from e's body (e's clique excluded) must not be constrained (e.g. a defun-sk witness), must not
  come from defchoose, and must not be non-executable (defun-sk predicates). Finally it runs `assert-event`
  on concrete inputs. The check labels inside the book are h1-*, h2-*, h3-* (one prefix per definition).
- H2 (informative, not counted): grade-h2.lisp, generated from the model's exec-tests.lisp, applies the same
  form, formals and executability checks to the model's own :exec definitions. R3 asks only that
  exec-tests.lisp certify with (i)-(v), not for these forms, so H2 is not folded into R3.

## Interpretations
- Theorem names: `e-correct` and `booleanp-of-e` for `:name e`. The revised prompt states these names
  explicitly.
- The hidden assert-event inputs avoid guard violations of primitives under any order of evaluating the
  bindings and tests. Books run with guard checking on, and p-exec need not be guard-verified. For
  example, `(evl-exec 7)` would evaluate `(car 7)` and is not used.
- Rule variables are bound from conclusion arguments by position; the first occurrence of a repeated
  variable gives its value (le-refl, plus-zero). This follows the prompt's "x_i when t_i is literally v".

## Validation (2026-11-14, master 1d2b39a424)
- R2: the books' definductive.lisp, copied unchanged into a scratch directory (no cert.acl2 needed), passes:
  the rewired tests certify (about 40 s). With a mock exec-tests.lisp, grade.sh gives R1 PASS (100% kept),
  R2 PASS, and R3 FAIL ("Illegal key/value args (:EXEC ...)", as expected for the unextended tool). R4 fails
  gracefully on every check; no raw Lisp errors.
- check-exec.py: R3S PASS on the mock exec-tests.lisp. It fails, each with the matching reason, when the
  premise order in (i) is swapped, an assert-event is removed (v), a binding for y is added in (iv), a
  rule that closes the 3-clique is removed (iii), or the cons rule is removed (ii). R1S fails on a truncated
  file.
- The hidden definitions without :exec are admitted by the books' definductive (default
  `:verify-guards t`). Their termination and binding-adequacy obligations are proved by `thm`.
- The R4 checks were exercised in a scratch directory: hand-written exec functions for the three hidden predicates,
  with skip-proofs'd correctness theorems (scratch only), give 17/17 GRADER-PASS. The assert-event
  expectations match those functions. Replacing a recursive call with the defun-sk predicate `le`, or
  adding a call to the witness `evl-proof`, makes the clean checks and runs fail.
- The :exec part cannot be run for real: no implementation exists.
