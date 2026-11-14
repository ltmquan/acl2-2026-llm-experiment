# fw-ftc-macro grader: notes

## Mapping of requirements
| R | how | mechanical? |
|---|---|---|
| 1 | the macro in `def-ftc-integral.lisp` meets the interface: hidden books `grade-r1-{lin,exp,sym,fail}.lisp` + error-message inspection | mechanical part; then MANUAL (R1-M) |
| 2 | `tests.lisp` parsed; calls (a)-(d) identified; for each a generated `grade-r2-<x>.lisp` proves the closed form at concrete endpoints from the model's `int-NAME-ftc`; the model's own check after each call is detected syntactically; (e) a must-fail with a numerically wrong antiderivative | yes (MANUAL only if (e) cannot be evaluated) |
| 3 | `cert.pl --acl2 /opt/acl2r/saved_acl2r` on both books | yes |

Revised prompt: R1 now explicitly covers the specification and announces the checker's own calls; the
continuity and `int-name-is-integral` forms are stated exactly.

## Hidden tests (R1)
- `grade-r1-lin`: lambda integrand 2x, antiderivative x^2, (interval nil nil), no theorems; values
  int(1,3) = 8 and int(3,-2) = -5 (reversed bounds) from `int-gr-lin-ftc`.
- `grade-r1-exp`: `acl2-exp` with itself, (interval nil nil), theorems supplied (proved in the book from
  `acl2-exp-derivative` and `exp-continuous-2`, library books included locally; a realness rule
  `gr-realp-acl2-exp` is left in the world for the side conditions); value int(0,1) = e^1 - e^0.
- `grade-r1-sym`: symbol integrand/antiderivative (our `defun`s 3x^2 and x^3), (interval 0 nil), no theorems;
  value int(0,2) = 8.
- `grade-r1-fail`: three `must-fail`s: 2x with x^3; cosine with cosine; 3x with x^2 plus a supplied derivative
  theorem about other functions (F = 5, f = 0).
- After each successful call, `gr-check-ftc` (in `grader-ftc-lib.lisp`) checks the generated events:
  `NAME-integrand` (lambda case) has the lambda's body; `map-NAME`, `riemann-NAME`, `int-NAME` have the
  ftc-2.lisp bodies; `strict-int-NAME` is introduced by `defun-std` with the ftc-2.lisp body (bodies are taken
  from `get-event`, translated, formals renamed); `int-NAME-ftc`'s formula equals the translation of the
  prompt's form exactly; `int-NAME-is-integral`'s formula equals the translation of the prompt's form exactly
  (the hypotheses in the prompt's order, as `strict-int-rcdfn-prime-is-integral-of-rcdfn-prime`).

## Interpretations
- Names are interned in the package of NAME (`int-NAME-ftc` etc.), and `NAME-integrand` exists only for a
  lambda integrand; `map-NAME` calls `NAME-integrand` (lambda) or f (symbol).
- The domain inside `strict-int-NAME` may be the `:domain` term, its quoted value, or a call of a 0-ary function
  whose body is one of those (ftc-2.lisp itself uses `rcdfn-domain`). In `int-NAME-ftc` it must be the term.
- For a lambda antiderivative, `(F b)` in `int-NAME-ftc` may be the lambda application or its beta-reduction.
- The continuity theorem supplied in `grade-r1-exp` has exactly the prompt's form (as `rcdfn-prime-continuous`);
  the derivative theorem exactly the prompt's derivative form.
- R2 identification: (a) and (c) by exact rational evaluation of the lambdas (or unary `defun`s of tests.lisp)
  at 2, 3, 5; (b) by the symbols `acl2-cosine`/`acl2-sine` (or eta-expanded lambdas); (d) by `acl2-ln`, and its
  antiderivative is checked in ACL2 to equal x ln x - x for x > 0 (with `arithmetic/top`). (a)-(c) must not
  pass `:derivative-thm`/`:continuity-thm`. Our endpoint values: (a) int(0,3) = 9, (b) int(0,1) =
  sin 1 - sin 0, (c) int(1,2) = 1/2, (d) int(1,2) = (2 ln 2 - 2) - (1 ln 1 - 1), each proved by `:use` of the
  model's `int-NAME-ftc` with `int-NAME`/`strict-int-NAME` disabled. "Followed by a check" = some later form
  before the next call mentions `int-NAME-ftc` or `int-NAME`. (e) = a `def-ftc-integral` under `must-fail`
  whose antiderivative's difference quotient (h = 10^-6) is off from the integrand by > 0.01 at 2, 3 or 5.
- Banned events: `check-prove.py`'s list plus raw-mode/untouchable forms, and `cert-flags:`/`cert_param:`
  comments enabling skip-proofs or ttags. `make-event` is allowed (the macro needs it).

## Validation (scratch only)
- After the revision: stub mock again R1 MANUAL (all four hidden books PASS), R2 PASS, R3 PASS; a stub with the
  first two hypotheses of `int-NAME-is-integral` swapped -> GRADER-FAIL with the formula.
Earlier:
- A stub `def-ftc-integral` (generates the events, theorems under `skip-proofs`, refuses pairs not in a list of
  correct ones) with `skip-proofs-okp` cert flags; the grader was run through a harness that only disables the
  banned scan. All four R1 books certify; `gr-check-ftc` reports nothing.
- Negative stubs: hypotheses of `int-NAME-ftc` swapped -> GRADER-FAIL with the formula; `strict-int-NAME` by
  `defun` -> "not defun-std"; `riemann-NAME` body changed -> body mismatch.
- A mock `tests.lisp` with (a)-(e): R2 PASS, R3 PASS, R1 MANUAL. Negative: theorems supplied to (a) and (b),
  check after (c) deleted -> R2 FAIL naming those three.
- Unmodified `grade.sh` on the stub: all FAIL "banned event: skip-proofs" (as it should).
- Found while validating: a call named `cos` makes `map-cos` etc. symbols of COMMON-LISP (cannot be defined).
  Our hidden names are `gr-*`; a model test named like a CL symbol would fail its own certification.
