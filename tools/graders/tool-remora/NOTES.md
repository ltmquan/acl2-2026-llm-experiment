# tool-remora grader: interpretations and validation

## Files
- `grade.sh <work>`: the grader (ACL2 master `/opt/acl2-master/saved_acl2`, its `cert.pl`).
- `check.py`: banned events, book discovery, statement diff for R2, candidate search for R3. Banned list and
  s-expression reader copied from `../check-prove.py`.
- `targets.lisp`: the five theorems of Sec. 3 transcribed verbatim from the PDF (arg2l -> arg2).
- `grade-r1.lisp`: the seven helpers are defined (not constrained) with the arities the statements use
  (`pairwise-curry-binary-fn` 2, `pairwise-binary-args-fn` 3, the five others 1; `pairwise-curry-binary-x-fn`
  appears in no statement, any arity).
- `grade-r1v.lisp`: the helpers mean what the paper says, on `[1 2] + [[1 2] [3 4]]` (see below).
- `grade-r2-1,2,3,5.lisp`, `grade-r2-4a.lisp`, `grade-r2-4b.lisp`: each paper theorem restated and proved
  `:by` the model's theorem of the same name.
- `grade-r4.lisp`: our own Sec. 2 evaluations on the interpreter (independent of the model).

## How grade.sh finds the model's books
Every `.lisp` under `/work` is certified (default flags). `zz-grader/grader-model.lisp` includes all of them
(fallback: only the books defining a theorem or helper name). Grader books are in `zz-grader/` with their own
`cert.acl2` (only `kestrel/remora/portcullis`), and include `kestrel/remora/expression-evaluation` before the
model's books, so the statements are about the books' interpreter: a model that defined its own `eval-app`
would clash and fail.

## Interpretations
- Statements are read in package "REMORA" (the interpreter's). R2 accepts a theorem if the paper's statement
  follows `:by` from the model's theorem of that name. If not: missing -> FAIL; same formula but `:by` fails
  -> FAIL; changed and named in README.md -> MANUAL with the diff; changed and not named -> FAIL.
- `pos-listp` (undo-expr-value-with-nonempty-dims-3): "REMORA" does not import `ACL2::POS-LISTP`, and the
  interpreter defines no `REMORA::POS-LISTP`, so the statement as printed does not translate on master
  (checked: "The symbol POS-LISTP (in package "REMORA") has neither a function nor macro definition").
  grade.sh accepts either reading: variant a uses `acl2::pos-listp`; variant b uses `remora::pos-listp`, which
  the model must then define, and proves it equal to `acl2::pos-listp`. The R2 diff ignores `acl2::`/`remora::`
  prefixes, so writing `acl2::pos-listp` does not count as a change.
- R1 "define the helper functions": besides existence (grade-r1), grade-r1v checks the meaning the paper gives
  them, because a trivial definition (e.g. a predicate that is always false) would make the R2 theorems
  vacuous. On `funval = +`, `arg1 = [1 2]`, `arg2 = [[1 2] [3 4]]`: `expr-is-nested-vectors-of-base-values`
  holds of both args; `list-of-primop-int-binary` / `list-of-base-values` hold of the lifted cells of the first
  step; `pairwise-curry-binary-fn` equals `eval-app-list` on them; every hypothesis of
  `eval-app-when-funval-is-binary-op-fully` holds, with `pframe = (2 2)`; and its right-hand side evaluates to
  `[[2 3] [5 6]]`. The representation returned by `get-cells-from-expr-value` is not fixed by the paper
  (Remora cells or ACL2 integers), so it is checked only through that composition.
- R3 (own statement) is MANUAL; grade.sh lists candidate theorems (mentioning `eval-app` on `(list a b)` and
  `(list b a)`).
- R4: the prompt says "the two ill-formed additions" but Sec. 2 has three (`[1 2 3]+[4 5]`,
  `[1 2 3 4]+[[1 2] [3 4]]`, `[1 2]+[[1 2] [[5 6]]]`); the third is printed as a ragged array while the text
  gives its shapes as [2] and [3 2]. grade-r4 checks all three, the third in both readings; the CHECKLIST
  accepts any two. On master all three are rejected by the static checker (`check-top-expr`) before
  evaluation, and also give errors at the `eval-app` level.

## Do the paper's statements still make sense on master (1d2b39a424)?
- All five translate against the master interpreter with stub helpers (defstub, arities as above) under
  `skip-proofs`, once `pos-listp` is read as `acl2::pos-listp` (see above). `expr-value-kind`,
  `expr-value-case`, `primop-value-case ... :int-binary`, `lift-expr-value-to-frame` (3 args),
  `list-prefix-join`, `repeat-each`, `nat-list-product`, `prefixp`, `reserrp` all exist with the paper's arities.
- Concrete evaluation on master: `propagate-...-when-vector` holds on `[[1 2] [3 4]]` (both sides give the four
  cells); `undo-expr-value-with-nonempty-dims-3` holds on cells 1..4 with frame (2 2), pframe (2 2 3), and on
  frame (2), pframe (2 5); `eval-app` of `+` on `[1 2]`, `[[1 2] [3 4]]` is `[[2 3] [5 6]]`, which is what the
  right-hand side of the final theorem gives with natural helper definitions (pframe (2 2); `[1 2]` replicated by
  `repeat-each 2` to 1 1 2 2).
- eval-app-empty routing: master's `eval-app` sends any step whose principal frame contains 0 to
  `eval-app-empty`, which returns a `:vector-empty`, while `expr-value-with-nonempty-dims` with a 0 dimension
  returns `(:vector nil)` (checked: `[]+[]` gives `(:VECTOR-EMPTY ...)`, the RHS gives `(:VECTOR NIL)`). So
  `eval-app-when-funval-is-binary-op(-fully)` are true on master only if `expr-is-nested-vectors-of-base-values`
  excludes empty arrays. That is the natural reading of the name (in the fixtype, `:vector` is non-empty), and
  grade-r1v does not force either choice; a model that includes empty vectors must add a hypothesis, which R2
  then reports for MANUAL review. Master also curries primops (`int-binary` -> `int-binary-x` via
  `eval-app-cell`) and runs three result checks after `eval-app-list`; both are covered by the
  `(not (reserrp ...))` hypotheses, so no statement needs to change for them.

## Validation (in a scratch directory)
- Certified `kestrel/remora/evaluation-tests` and `evaluation-rules` on master (writes `.cert`s under /opt).
- grade-r4.lisp certifies alone on master: all 12 assertions hold.
- Mock solution `mockR` (scratch only): natural helper definitions, the five statements and a commutativity
  theorem under `skip-proofs`, a small `examples.lisp`.
  - real grade.sh: rejected (banned `skip-proofs`), as required;
  - scratch copy of grade.sh without the banned scan and with `:skip-proofs-okp t` for the grader books:
    R1 PASS, R2 PASS (all five `:by`, theorem 4 via variant a), R3 MANUAL, R4 MANUAL (grade-r4 passes), R5 PASS;
  - `mockR3`: theorem 4 with `pos-listp` and a model `REMORA::POS-LISTP` -> R2 PASS via variant b.
- Negative tests (`mockR2`): theorem 1 renamed -> "MISSING"; an extra hypothesis named in README.md -> MANUAL
  with diff; an extra hypothesis not in README.md -> FAIL with diff; R2 FAIL overall; a nested-vectors
  predicate that is always false -> R1 FAIL (grade-r1v). The R3 candidate search finds the mock's theorem.
- Not validated: real proofs (no solution written).
