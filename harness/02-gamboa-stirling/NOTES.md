# 02 — Stirling: harness notes

Our records for this paper: how the prompts and packages were made, and how the runs went. Reviewers do not
need this; the paper folder [`../../02-gamboa-stirling/`](../../02-gamboa-stirling/) has what they review.

**Contribution (our classification).** A theorem: a classical analysis result (Wiedijk #90), plus library pieces: integration by parts in ACL2(r) and Wallis's product.

## Results

| | Experiment 1 | Experiment 2 |
|---|---|---|
| Result | proved (certified) | 3 / 3 targets proved |
| Model time | 58 min | 3 h 30 min |
| Tool calls | 183 | 222 |
| Certification time of solution.lisp (ACL2(r) 8.7) | 45.9 s | 390.7 s |
| Audit (`exp*/audit.txt`) | FLAGGED (one `pip install sympy`; see notes) | CLEAN |
| solution.lisp: lines / definitions / theorems | 1387 / 27 / 213 | 1743 / 25 / 217 |

Authors' development: not available (no public books). Per-run accounts: `exp1/run.md`, `exp2/run.md`.

## Experiment 1: how the prompt was made from the paper

**Theorem chosen:** n! ∼ √(2πn)(n/e)ⁿ, with ∼ defined as in the paper (the ratio tends to 1).

#### Sources
- **Theorem:** §1 (Introduction), p. 1, first bullet of "Stirling's approximation is usually written in one of two forms:" — typeset as `n! ∼ √(2πn) (n/e)^n`. Checked against the rendered PDF page.
- **Definition of ∼:** §1, p. 1, the two sentences immediately after the bullets.
- No other definitions: n!, e, π, √, limit are standard mathematics.

#### Edits
1. Theorem: `• n! ∼ √(2πn)(n/e)^n, or` → `n! ∼ √(2πn) (n/e)^n` — dropped the bullet and trailing ", or" (list punctuation). Typeset math converted to Unicode: radical over 2πn written √(2πn); the fraction n/e raised to n written (n/e)^n.
2. Definition: `lim_{n→∞}` written as plain text with subscript braces (typeset subscript in the PDF). Otherwise verbatim.
3. Omitted by instruction: the logarithmic form (second bullet), and the following sentences about non-standard analysis, ≈, infinitesimals, ACL2(r).
4. The theorem is a bare formula, not a sentence; the paper's only English framing ("Stirling's approximation is usually written in one of two forms") was not included. Implicit: n ranges over the positive integers (or naturals), n → ∞.

## Experiment 2: how the package was made

No author books exist, so the package was transcribed from the paper. `definitions.lisp`
includes the 8.7 books `arithmetic/factorial`, `nonstd/nsa/{factorial,sqrt,exp,ln,trig}` and defines
`wallis-product`, verbatim from the paper (§4). This is the only author definition. The paper's other
definitions (`iter-factorial`, `wallis-factor`, `stirling-constant`, the trapezoid and integral functions, …)
are not given: no target mentions them, and they would reveal the route. The PDF text spaces letters apart,
so the text was collapsed and then checked by hand against the paper.

Full notes, scripts and logs: `exp2/extraction/`.

### Changes from the authors' text

- Targets are renamed MAIN-1..3; the authors' names are in comments in `targets.lisp`.
- `arithmetic/factorial` is included explicitly, as the paper names it as the source of `factorial`, even
  though `nonstd/nsa/factorial` already includes it.
- No other change: definition and statements are the paper's text.

### Checker files

`exp2/checker/` holds the exact files `tools/check-exp2.py` certifies the solution against. The paper folder's
`exp2/definitions.lisp` is the same file with comments added (`tools/check-comments-only.py`).

| File | SHA-256 |
|---|---|
| `exp2/checker/defs.lisp` | `d4ab485410a99bf606fffee1395ce7a63a56842097460dc8e67229cb8d17c206` |

## Run notes

**Experiment 1.**
- **Audit finding.** About 9 minutes in, the model ran `pip install sympy` (downloaded from PyPI) and used it
  once, as a scratch calculator, to factor one algebraic expression while planning a lemma. The certified file
  proves that step, like every step, in ACL2, so sympy cannot affect correctness. The model fetched no
  information about the problem. This breaks the prompt's "no internet" rule. The team has to decide whether
  to count the run with a footnote or rerun it.

**Experiment 2.**
- The session's worker restarted once (infrastructure). The model noted that its files survived and
  continued.

