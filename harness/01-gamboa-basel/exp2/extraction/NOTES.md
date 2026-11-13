# Given package: gamboa-basel

Paper: R. Gamboa, "An Alternative Proof in ACL2(r) of Euler's Solution to the Basel Problem"
(`/home/user/acl2-exp/papers/gamboa-basel.pdf`). **Logic: ACL2(r)** (`/opt/acl2r/saved_acl2r`, 8.7).

## Targets
| Target | Author's name | Source | Meaning |
|---|---|---|---|
| MAIN-1 | `basel-series-closed-form-close` | paper Sec. 6, p. 13 (`gamboa-basel.txt` l. 794-799) | for every infinitely large posp n, sum_{k=1}^{n-1} 1/k^2 is i-close to pi^2/6 |

## defs.lisp
17 lines, 602 bytes. Contents:
- `(include-book "nonstd/nsa/trig" :dir :system)`: provides `acl2-pi` (trig.lisp:1074).
  `i-close` and `i-large` are ACL2(r) built-ins.
- `basel-series`: verbatim from the paper (Sec. 3, p. 3). This is the only author definition.
  No route-revealing definitions (`omega-series`, `zeta`, `basel-odds`, ...) are included.

No skip-proofs, defaxiom or ttags. No local lemmas were needed: termination proves with no help, and no
guards are declared, so no guard verification takes place.

## Deviations from the author's text
- The paper uses `defthmd basel-series-closed-form-close`. Per the brief, the target is `(defthm MAIN-1 ...)`
  with no hints. The paper elides the hints (`:hints ...`). The statement is unchanged.
- The author's books are not available. The include-book of `nonstd/nsa/trig` is our choice: it is the
  8.7 community book that defines `acl2-pi`. The paper does not show its include-books.
- No other deviations. The definition and the statement match the paper exactly.

## Verification
- **V1 (pass).** `defs.lisp` certifies with cert.pl on `/opt/acl2r/saved_acl2r` (8.7) in the scratch copy
  `<scratch>/given-gamboa-basel/`.
  Script: `verify/run-v1-v2.sh`. Logs: `verify/v1-v2-certify.log` and `verify/defs.cert.out`.
- **V2 (pass).** `verify/test-targets.lisp` includes "defs" and admits MAIN-1 under skip-proofs. Its
  `test-targets.acl2` sets `:skip-proofs-okp t`. It certifies (`verify/test-targets.cert.out`).
- **V3 (pass, checked against the paper).** No author books exist, so we checked the package against the
  paper's text. `verify/v3-compare.py` re-extracts the PDF with `pdftotext -layout`
  (`verify/gamboa-basel-layout.txt`), finds the `defun basel-series` form and the
  `defthmd basel-series-closed-form-close` statement, and compares them with defs.lisp and targets.lisp,
  ignoring whitespace and case. Both are IDENTICAL (`verify/v3-compare.log`).
  - We confirmed the semantics: `(basel-series 1 4)` = 49/36 = 1 + 1/4 + 1/9, so the upper bound is
    exclusive, as the paper's Aside says (`verify/sanity.log`).
  - The library `acl2-pi`, `i-close` and `i-large` are the ones the paper means, as `:pe` shows in
    `verify/sanity.log`.
  - The paper also gives a `standard-part` variant, `basel-series-closed-form`. The author prefers the
    i-close form, so the target uses that.
- **Checker** (`verify/checker.log`):
  - `verify/test-solution.lisp` (skip-proofs) is rejected as BANNED, as expected.
  - `verify/test-solution-match.lisp` has the correct statement and a deliberately failing proof. It passes
    the target-matching stage and then fails at certification (exit 1).
  - `verify/test-solution-wrong.lisp` uses pi^2/8. It is rejected with TARGET-MISMATCH (exit 4).
  - No real proof exists, so the checker could not be run end to end with a certifying solution.
