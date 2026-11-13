# Given package: gamboa-stirling

Paper: "A Mechanical Proof of Stirling's Approximation in ACL2(r)", R. Gamboa (ACL2-2026).
Logic: **acl2r** (image `/opt/acl2r/saved_acl2r`, ACL2(r) 8.7).

## Targets (targets.lisp)
| Target | Authors' name | Paper location (papers/gamboa-stirling.txt) | Meaning |
|---|---|---|---|
| MAIN-1 | stirling-approximation-to-factorial | Sec. 5, l.814-822 | n!/(sqrt(2 pi) n^n e^-n sqrt n) is i-close to 1 for i-large natural n |
| MAIN-2 | stirling-approximation-to-ln-factorial | Sec. 5, l.826-832 | ln n! is i-close to ln(n^n) - n + ln sqrt(2 pi n) for i-large positive n |
| MAIN-3 | wallis-product-convergence | Sec. 4, l.678-682 | standard-part of the n-th Wallis partial product is pi/2 for i-large natural n |

## defs.lisp
27 lines, 1076 bytes. Contents:
- include-books (all certified in 8.7): `arithmetic/factorial` (factorial), `nonstd/nsa/factorial`,
  `nonstd/nsa/sqrt` (acl2-sqrt), `nonstd/nsa/exp` (acl2-exp), `nonstd/nsa/ln` (acl2-ln),
  `nonstd/nsa/trig` (acl2-pi). `i-close`, `i-large`, `standard-part` are ACL2(r) primitives.
- the only author definition, `wallis-product`, verbatim from the paper (txt l.664-669).
No local lemmas, no skip-proofs/defaxiom/ttags.

## Deviations
- Theorem names: the targets are named MAIN-1..3 (the brief's convention); the authors' names are in the comments.
- The authors' books are not available, so all text is transcribed from the PDF text. pdftotext spaces the
  letters out (e.g. `( w a l l i s - p r o d u c t n )`); I collapsed the spaces. I made no other change.
- `arithmetic/factorial` is included explicitly even though `nonstd/nsa/factorial` already pulls it in.
  The paper (l.84) names it as the source of `factorial`. The include is redundant but does no harm.
- No other author definitions are given (`iter-factorial`, `wallis-factor`, `stirling-constant`, the
  trapezoid/integral functions, ...). No target mentions them, and they would give away the proof route.

## Verification (logs in verify/)
- V1: `defs.lisp` certifies with cert.pl on `/opt/acl2r/saved_acl2r` (scratch copy;
  verify/defs.cert.out, verify/certlog.txt).
- V2: `verify/test-skip.lisp` includes "defs" and admits MAIN-1..3 under skip-proofs. With
  `verify/test-skip.acl2` (cert-flags `:skip-proofs-okp t`) it certifies (verify/test-skip.cert.out).
- V3 (no authors' books): I checked the statements and `wallis-product` by hand against the paper text
  (txt l.664-669, 678-682, 814-822, 826-832). They agree token for token. The paper's listing of `factorial`
  (l.84-88) is identical to the loaded definition: `:pe`/`body` output is in verify/v3-defs.log, which also
  shows the library definitions of acl2-pi, acl2-sqrt, acl2-exp, acl2-ln and the arities of i-close (2),
  i-large (1) and standard-part (1).
- check-exp2.py:
  - With the skip-proofs test, it reports `BANNED: skip-proofs`, as expected
    (verify/check-exp2-test-skip.log).
  - With `verify/test-solution.lisp`, it gets past BANNED and TARGET-MISMATCH and then reports
    "FAILED: did not certify", which is also expected. That file states MAIN-1..3 identically, but each
    proof fails at once because of `:hints (("Goal" :by nil))`. So target matching works; no real proofs
    exist (verify/check-exp2-test-solution.log).
