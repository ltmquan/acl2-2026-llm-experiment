# luu-flipgraph: the "given" package

Paper: Luu, Medley, Manolios, "Formalizing the Connectivity Theorem for the Matrix
Multiplication Flip Graph in ACL2" (ACL2 Workshop 2026).
Authors' books: `reference-books/pr-2103/books/workshops/2026/luu-medley-manolios/` (they certify on 8.7).

**Logic: acl2** (plain ACL2 8.7, `/opt/acl2/saved_acl2`).

## Targets (`targets.lisp`)

| Target | Authors' theorem | Meaning |
|---|---|---|
| MAIN-1 | `flip-plus-connectivity` (main.lisp:148), in existential form | for n >= 2, every correct n x n scheme over F2 reaches every other one by valid flip/plus moves |
| MAIN-2 | `algo-to-correct-scheme` (algo-completeness.lisp:41) | completeness: a correct bilinear algorithm translates to a correct scheme |
| MAIN-3 | `scheme-algo-correct` (scheme-algo.lisp:470) | soundness: the algorithm built from a correct scheme is correct |
| MAIN-4 | `algo-scheme-of-scheme-algo` (scheme-algo.lisp:451) | round trip: scheme to algorithm and back is the identity |

MAIN-1 uses the survey's existential `flip-plus-reachablep` (approved by the author). The
`defun-sk` is in defs.lisp. It has the same hypotheses as the original: `(correct-schemep sch n)
(correct-schemep sch2 n) (natp n) (<= 2 n)`.

**MAIN-3 and MAIN-4 are separate targets, not a conjunction**, because their hypotheses differ.
`scheme-algo-correct` assumes `(correct-schemep sch n)`, and `algo-scheme-of-scheme-algo` assumes only
`(schemep sch n)`. A conjunction under `correct-schemep` would weaken the round trip.
The other hypotheses, `(natp n) (< 0 n)`, are the same.

The statements are verbatim from the authors (`defrule` is written as `defthm`, and hints are dropped).

## defs.lisp

- 1017 lines and 30405 bytes. It has 89 of the authors' definitions (`define`, plus one `defun-sk`, `algo-correctp`)
  and the new `defun-sk flip-plus-reachablep`.
  The files are bits 11, scheme 29, tensor 3, mm-tensor 7, entry 1, adequacy 5, matmul-expr 23,
  algo-completeness 1 and scheme-algo 9 (89 in all).
- The set is the definitional closure of the four statements. It was computed in ACL2 from the bodies, guards
  and measures of the definitions; see `verify/closure.lsp`, `closure.out` and `closure.txt`.
  It leaves out `main-path` and every path or lemma construction (graft-path, add-arbitrary, add-duplicate,
  zero-subset, iterate, arbitrary, gf2span, zero-support, ...). It also leaves out `list-to-scheme`,
  `computes-productp`, `eval-scheme` and the adequacy/completeness machinery, because no statement needs them.
- Include-books: these are the authors' non-local includes of bits.lisp and bags.lisp:
  `kestrel/bv/bitxor`, `kestrel/bv/bitand`, `std/util/define`, `std/util/defrule`, `std/lists/repeat`,
  `std/basic/inductions` and `std/obags/top`.
  There are also local includes of `std/lists/append`, `std/lists/nth` and `arithmetic/top-with-meta`.
  The authors include these locally too.
- There is no skip-proofs, defaxiom or ttag.

### Deviations from the authors' text
1. **`///` sections are removed** from every `define`, along with all of their theorems. The define
   headers and bodies are verbatim, including `:returns`, `:guard`, `:guard-hints`, `:measure`, `:enabled` and
   `:verify-guards :after-returns`. So the `:returns` type theorems (for example `booleanp-of-...`, `bitp-of-eval-lform`,
   and `bagp` of `apply-moves` under the hypothesis `(obag::bagp sch)`) are still exported, as part of the authors'
   definition forms. The rule names that `defun-sk` generates are exported as usual: `algo-correctp-necc` and
   `flip-plus-reachablep-suff`.
2. **No global theorems or theory events from the authors' files** are included. This leaves out
   `bitxor-of-ifix-arg1`, `bitand-of-ifix-arg1`, `(in-theory (disable ifix))`, the bags.lisp lemmas and all the
   other `defrule`s. They are not needed to admit the definitions.
3. **Local lemmas, needed only for guard verification**, are all `local`, so none is exported.
   - The authors' lemmas, copied verbatim and checked textually (`verify/textcheck.py`):
     - matmul-expr.lisp: `true-listp-when-prod-listp`, `prodp-of-nth-when-prod-listp`,
       `nat-listp-when-index-listp`, `idx-rowp-when-outs-rowp`, `true-listp-when-outs-rowp`, `len-of-outs-rowp`,
       `idx-tablep-when-outs-rowsp`, `true-listp-when-outs-rowsp` and `len-of-outs-rowsp`. These come from `///` sections,
       so they sit in a local `encapsulate` that enables the function, as `///` does.
     - matmul-expr.lisp:223-290: the outs-rows/nth lemmas, 7 of them.
     - matmul-expr.lisp:95: `integerp-of-eval-lform`, which the authors' `:guard-hints` name.
   - The authors' statements with my own simpler proofs: `bit-list-p-when-bit-listnp`, `bit-list-listp-when-bit-matp`,
     `bitp-of-mat-entry` and `integerp-of-mat-entry`. The last one is named in the authors' `:guard-hints`, so a rule
     with that name must exist.
   - My own lemmas: `mat-triple-listp-when-summand-listp`, for the guard of `correct-schemep`; the 8.7 world
     without the authors' exported lemmas needed it. Also `nth-dim-induct`, `bitp-of-nth-when-bit-listnp-local` and
     `bit-listnp-of-nth-when-bit-matp-local`.
   - A greedy minimization (`verify/minimize.py`) removed each local event in turn and recertified. Every one is
     needed.
4. **`flip-plus-reachablep` is new.** The authors do not have it. The survey drafted it, and it is marked in the file.
5. Each definition has a `;; file:line` comment above it.

## Verification (all on ACL2 8.7, `/opt/acl2/saved_acl2`; `verify/run-all.sh` reruns V1-V3)
- **V1 passes.** `cert.pl defs.lisp` certifies in about 6 s (`verify/V1-defs.cert.out`).
- **V2 passes.** `verify/v2-skip.lisp` includes "defs" and admits MAIN-1 to MAIN-4 under `skip-proofs`, with
  `:skip-proofs-okp t` in `v2-skip.acl2`. It certifies (`verify/V2-v2-skip.cert.out`).
- **V3 passes.** `verify/v3-authors.lisp` includes the authors' `main` and `scheme-algo` books, which were certified
  on 8.7 in a scratch copy. It adds the identical `defun-sk flip-plus-reachablep` and proves every target with
  `:in-theory nil` and a `:use`:
  - MAIN-1: `(:instance flip-plus-reachablep-suff (moves (main-path sch sch2 n)))` and `flip-plus-connectivity`.
  - MAIN-2, MAIN-3 and MAIN-4: the authors' theorems directly.

  It certifies (`verify/V3-v3-authors.cert.out`).
  - **The definitions are identical in both worlds.** For all 89 + 2 functions (the 89 authors' definitions,
    `flip-plus-reachablep` and its witness), the dump compares formals, `body`, `guard`, measure, symbol-class
    (guard-verified status), constrainedp, defchoose axiom and constraints. It was taken once in a defs.lisp
    world and once in the authors' world, and the two dumps are byte-identical (`verify/dump-defs.txt` and
    `verify/dump-authors.txt`).
  - **The text is verbatim.** `verify/textcheck.py` finds all 105 copied forms (89 definitions and 16 lemmas)
    verbatim in the authors' sources (`verify/textcheck.out`).
- **check-exp2.py**:
  - `verify/test-solution.lisp`, the skip-proofs solution, gives `BANNED: skip-proofs`, as expected.
  - `verify/test-solution-noproof.lisp` has the exact target statements and no proofs. It passes the BANNED, include
    and TARGET-matching checks and then fails certification, as expected (`verify/check-noproof.log`). A solution
    with the real V3 proofs cannot be run through the checker, because they need the authors' non-system books.
    So target matching was confirmed this way, and V3 confirmed provability.
