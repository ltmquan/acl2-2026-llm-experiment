# tool-smtlink3 grader: notes

## Files
- `grade.sh <work-dir>` runs `grade.py` (python3 -I), which does all the steps listed in its docstring.
- `books/`: the grader books, copied to `<copy>/grader/` and certified there. `cert.acl2` includes
  `../smtlink` (with `:ttags :all`) in the portcullis, so the SMT package exists when the books are read.
  It sets `; cert-flags: ? t :ttags :all`.
  - `grader-common.lisp`: includes ../smtlink, ../examples and std/testing/must-fail. It defines
    `x^2-y^2` if the model did not, and introduces `smt::specialize-unary-rational-` as a copy of
    `smt::specialize-unary-rational--` when only the latter exists (see below).
  - `grade-r3.lisp`: the paper's goal proves, and a false variant must fail (real Z3, which answers sat).
  - `grade-r3-unknown.lisp` / `grade-r3-error.lisp`: the paper's goal must fail with a fake `z3` first on
    PATH (answers `unknown`, or prints `(error ...)` and exits 1).
  - `grade-r4.lisp`: the paper's goal and hint verbatim (renamed to grader-poly-ineq-example), and a
    version with the hypotheses reversed. It also checks that the five functions of the 5.4 encapsulate
    are constrained, with the paper's arities.
  - `grade-r6.lisp`, `grade-r7.lisp`: supplementary restatements of the 4.1 and 5.7 goals.
- Erlang is not involved. Z3 is taken from PATH at grading time (`shutil.which("z3")`).

## Interpretations
- Theorem names in grader books are prefixed `grader-`. Restating `poly-ineq-example` under its own
  name would be redundant with the model's event and so would test nothing.
- **Hint goal "Goal''"**: the PDF shows `("Goal''" :smtlink ...)` (two primes after Goal). I checked in
  ACL2 8.7 that a hint on Goal'' does fire for this goal, and for the permuted goal, without any extra
  theory (ACL2 produces Goal' and Goal'' from the x^2-y^2 expansion and normalization). The grader uses
  "Goal''" verbatim.
- **Hint name `smt::specialize-unary-rational-`** (hint line 19): the PDF really shows this name with a
  single trailing hyphen. The encapsulate elides the rule ("..."), so the model may name the unary-minus
  rule `specialize-unary-rational--`. grader-common accepts either name. If only the `--` name exists, it
  adds the paper's name as a copy of that theorem, so the paper's hint can still be used verbatim.
  **Prompt issue**: the prompt's pdftotext rendering also shows the letter-spaced
  `s p e c i a l i z e - u n a r y - r a t i o n a l -`. A model will probably guess either name.
  We accept both.
- `x^2-y^2` is used but never defined in the paper. It is the Smtlink 2.0 example function
  `(- (* x x) (* y y))`. If the model's books do not define it, the grader defines it that way.
- **The false variant (R3)** replaces the final `3` with `5`. The counterexample is x = 9/10, y = 0.
  (Replacing it with `4` is NOT false: grade.py's grid search finds no counterexample.)
- **R3 "unknown/errors"** is tested with a fake `z3` on PATH, as allowed by the brief. If the model calls
  Z3 by absolute path, the fakes are never called. grade.py detects this (no wrapper call at all) and
  reports the solver-dependent parts as MANUAL rather than FAIL.
- **R4 "with the :smtlink hint shown"**: grade-r4 uses the paper's hint verbatim. The model's own
  examples.lisp is only checked for a `poly-ineq-example` with the paper's statement (packages ignored,
  `(/ 9 8)` = `9/8`, `real/rationalp` = `rationalp`) and an `:smtlink` hint. It is also checked for
  another `:smtlink` theorem with the same hypotheses in a different order and the same conclusion.
  grade.py also requires that Z3 answered `unsat` while grade-r4 was certified, so that ACL2 did not
  prove it alone.
- **R5**: the model's must-fail form must be an `:smtlink` defthm that mentions x^2-y^2, and so is a
  variant of the goal. Falsity is checked by evaluating the formula on a grid of rationals. If no
  counterexample is found, R5 is MANUAL.
- **R6**: the 4.1 goal uses an unspecified `foo`. The model's example must have exactly the shape
  `(implies (and (integerp y) (= x (* 2 y))) (F x y))` (`equal` accepted for `=`). The paper gives no
  hint for it, and probably the tool needs an integer theory that the paper does not name. So grade-r6
  (grader-foo with the paper's rational theory) failing turns R6 into MANUAL, not FAIL, provided the
  model's own examples are present. For `:hypothesize` we only require a proved `:smtlink` defthm whose
  hint contains `:hypothesize` (its argument syntax is not given in the paper).
- **R7**: the 5.7 goal is trivial for ACL2 alone, so a pass must show that the tool did the work.
  grade-r7 puts the hint on "Goal" (before simplification), and grade.py requires that Z3 answered
  `unsat` during grade-r7. The model's example must have hints that are only `:smtlink` hints
  ("automatically") naming both translation theorems. The full theory is not in the paper, so a
  grade-r7 failure with the model's example present is MANUAL.
- **R2**: allowed ttag books = the single file F with `define-trusted-clause-processor`, plus the model
  books F includes, transitively. `:ttags` is allowed elsewhere only as an include-book argument (needed
  to include smtlink). The world check uses `trusted-cl-proc-table` (minus ACL2's own
  `proof-builder-cl-proc`), `(global-val 'clause-processor-rules ...)` and
  `(global-val 'ttags-seen ...)`. Each ttag seen after including smtlink+examples must already be seen
  after including F alone.
- **Cert flags**: cert.pl's default is `? t`, which rejects ttags. grade.py gives every model book
  `? t :ttags :all` (appending to its own .acl2, or copying the directory's cert.acl2 into a
  book-specific .acl2). It keeps a model-supplied `:ttags` list. The source scan above still restricts
  where ttags may be used. cert-flags allowing skip-proofs or defaxioms are reported as BANNED.
- **R9 "all books"** = every `.lisp` file under /work (except our `grader/`).
- The model's `.cert`, `.port` and compiled files are not copied, so everything is recertified.

## Validation (done in my scratch directory; mocks never placed in graders/)
- Section 5 goal: in plain ACL2 8.7, a `:clause-processor` hint on "Goal''" fires for the goal (Goal''
  exists).
- I wrote a mock tool (~100 lines; trusted only; a naive SMT-LIB printer calling `z3` via `sh -c`; one
  identity verified clause processor; the 5.4 encapsulate with `specialize-unary-rational--`). Its
  examples.lisp has poly-ineq-example, a permuted version, a must-fail variant, a 4.1 goal and a
  `:hypothesize` goal. `grade.sh` on it gave: R1 MANUAL, R2 MANUAL (world: one trusted CP
  SMT::MOCK-CP, one verified rule), R3 PASS, R4 PASS, R5 PASS, R6 PASS, R7 FAIL (no 5.7 example, as
  expected), R8 MANUAL, R9 PASS. The logs show z3 answered sat/unsat as expected, the fakes were called
  (unknown, error), and every script had `(set-logic AUFNIRA)`. This run also exercised the
  `specialize-unary-rational-` alias path and the cert-flag injection (the mock had no cert-flags).
- Variants:
  - *bogus* (the trusted CP ignores Z3's answer): R3 FAIL, R5 FAIL;
  - *abs* (z3 called by absolute path): R1/R3/R4 MANUAL with "z3 not called via PATH";
  - *ttag* (examples.lisp includes oslib, a ttag'd community book): R2 FAIL "ttags not reached
    through the trusted book";
  - mock files defining a `define-trusted-clause-processor` symbol in a defpkg import list (initially
    a false BANNED; the scanner now skips defpkg forms);
  - *r7* (int-sym-* functions and the two translation theorems defined): grade-r7 reads, translates and
    certifies (with the mock's vacuous translation).
- grade.py's structural checker was unit-tested on a synthetic examples.lisp (package prefixes, `9/8`
  literal, permutation, the 5.7 goal with spaced parentheses, `:hypothesize`, must-fail with `4` →
  MANUAL, with `5` → counterexample x=13/16, y=3/16).
- Not validated: a real Smtlink 3 implementation, which does not exist locally. Smtlink 2 in
  /opt/acl2/books/projects/smtlink needs Python+z3py and uses different hint syntax, so it was not run
  against these books.
