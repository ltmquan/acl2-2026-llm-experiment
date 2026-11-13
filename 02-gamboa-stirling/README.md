# 02 — Stirling

**Paper:** Ruben Gamboa, *A Mechanical Proof of Stirling's Approximation in ACL2(r)* (ACL2 Workshop 2026). PDF in `source/paper.pdf`.
**Logic:** ACL2(r).

## The paper

The paper proves Stirling's approximation in ACL2(r) in both usual forms: n!/(√(2πn)(n/e)ⁿ) is
i-close to 1, and ln n! is i-close to n ln n − n + ln √(2πn), for every infinitely large n. It follows the
textbook route. It computes ∫ ln by the fundamental theorem of calculus and bounds the trapezoid-rule error,
which gives n! ∼ C√n(n/e)ⁿ. It then proves Wallis's product, which needs integration by parts (new in ACL2(r))
and the recurrence for ∫ sinⁿ. Finally, it combines the two to show C = √(2π).

**Contribution.** A theorem: a classical analysis result (Wiedijk #90), plus library pieces: integration by
parts in ACL2(r) and Wallis's product.

**Authors' ACL2 books.** **None available.** The author's books are not in the ACL2 community books, and there is
**no pull request** for them in the ACL2 repository (we checked the open and closed pull requests on
2026-11-13). `source/` therefore has only the paper. The experiment-2 definitions and targets were
transcribed from the paper and checked against its text.

## Files

```
02-gamboa-stirling/
  README.md
  source/
    paper.pdf
  exp1/
    prompt.txt            the exact prompt sent to the model
    solution.lisp         the model's final /work/solution.lisp
    audit.txt             transcript audit (tools/audit.py)
    review.md             short factual review of the run
  exp2/
    prompt.txt            the exact prompt sent to the model
    definitions.lisp      the definitions, annotated with their source locations (comments only)
    targets.lisp          the target theorems (the authors' names in comments)
    checker/              the exact files the checker certifies against (hashes below)
    extraction/           how definitions.lisp was built and verified (NOTES.md, scripts, logs)
    solution.lisp         the model's final /work/solution.lisp
    audit.txt
    review.md
```

## Results

| | Experiment 1 (English → ACL2) | Experiment 2 (ACL2 statements) |
|---|---|---|
| Result | proved (certified) | all 3 target(s) proved (certified, statements matched) |
| Model time | 58 min | 3 h 30 min |
| Tool calls | 183 | 222 |
| Certification time of solution.lisp (ACL2(r) 8.7) | 45.9 s | 390.7 s |
| Audit | FLAGGED (one `pip install sympy`; see notes) | CLEAN |
| solution.lisp: lines / definitions / theorems | 1387 / 27 / 213 | 1743 / 25 / 217 |

Authors' development (for scale): not available (no public books).

*Model time* runs from when the model received the prompt to the end of its run (setup not included).
Certification time is for `solution.lisp` alone, with its dependencies already certified, on our build
(experiment 2: against `exp2/checker/`). Sizes are counted with `tools/sizes.py` (definitions = `defun`,
`define`, `defun-sk`, `defmacro`, … and encapsulated functions; theorems = `defthm`, `defrule`, …, local
ones included). Both experiments: first attempt, Claude Opus 5.5 at medium effort.

## Experiment 1: English definitions and theorem

**Theorem given:** n! ∼ √(2πn)(n/e)ⁿ, with ∼ defined as in the paper (the ratio tends to 1).

### Statement rewrites (paper text → prompt)

The definitions and theorem were copied from the paper as close to verbatim as possible. Every edit:

#### Sources
- **Theorem:** §1 (Introduction), p. 1, first bullet of "Stirling's approximation is usually written in one of two forms:" — typeset as `n! ∼ √(2πn) (n/e)^n`. Checked against the rendered PDF page.
- **Definition of ∼:** §1, p. 1, the two sentences immediately after the bullets.
- No other definitions: n!, e, π, √, limit are standard mathematics.

#### Edits
1. Theorem: `• n! ∼ √(2πn)(n/e)^n, or` → `n! ∼ √(2πn) (n/e)^n` — dropped the bullet and trailing ", or" (list punctuation). Typeset math converted to Unicode: radical over 2πn written √(2πn); the fraction n/e raised to n written (n/e)^n.
2. Definition: `lim_{n→∞}` written as plain text with subscript braces (typeset subscript in the PDF). Otherwise verbatim.
3. Omitted by instruction: the logarithmic form (second bullet), and the following sentences about non-standard analysis, ≈, infinitesimals, ACL2(r).
4. The theorem is a bare formula, not a sentence; the paper's only English framing ("Stirling's approximation is usually written in one of two forms") was not included. Implicit: n ranges over the positive integers (or naturals), n → ∞.

### Prompt

<details>
<summary>Experiment 1 prompt (also in exp1/prompt.txt)</summary>

```text
Formalize the definitions and the theorem below in ACL2, and prove the theorem.

<definitions>
The symbol ∼ is used here formally to indicate asymptotic equivalence. In particular, f(n) ∼ g(n) means that lim_{n→∞} f(n)/g(n) = 1.
</definitions>

<theorem>
n! ∼ √(2πn) (n/e)^n
</theorem>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
Put your work in /work/solution.lisp; it must certify with `cert.pl` (add `--acl2 acl2r` for ACL2(r)), and its last
event must be the theorem, named MAIN.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done. When you are done, print the final contents of /work/solution.lisp.
```

</details>

## Experiment 2: the authors' ACL2 definitions and statements

### Targets

| Target | Authors' name | Source | Meaning |
|---|---|---|---|
| MAIN-1 | `stirling-approximation-to-factorial` | paper §5 | n!/(√(2π) nⁿ e⁻ⁿ √n) is i-close to 1 for i-large natural n |
| MAIN-2 | `stirling-approximation-to-ln-factorial` | paper §5 | ln n! is i-close to ln(nⁿ) − n + ln √(2πn) for i-large positive n |
| MAIN-3 | `wallis-product-convergence` | paper §4 | the standard part of the n-th Wallis partial product is π/2 for i-large natural n |

### How the definitions were extracted

No author books exist, so the package was transcribed from the paper. `definitions.lisp`
includes the 8.7 books `arithmetic/factorial`, `nonstd/nsa/{factorial,sqrt,exp,ln,trig}` and defines
`wallis-product`, verbatim from the paper (§4). This is the only author definition. The paper's other
definitions (`iter-factorial`, `wallis-factor`, `stirling-constant`, the trapezoid and integral functions, …)
are not given: no target mentions them, and they would reveal the route. The PDF text spaces letters apart,
so the text was collapsed and then checked by hand against the paper.

The general procedure, and how each package was checked, is in [`../EXPERIMENT-2.md`](../EXPERIMENT-2.md);
the full notes for this paper are in `exp2/extraction/NOTES.md`.

Checker files:

| File | SHA-256 |
|---|---|
| `exp2/checker/defs.lisp` | `d4ab485410a99bf606fffee1395ce7a63a56842097460dc8e67229cb8d17c206` |

`exp2/definitions.lisp` differs from `exp2/checker/defs.lisp` only in comments
(`tools/check-comments-only.py`).

### Statement rewrites (authors' ACL2 → targets)

- Targets are renamed MAIN-1..3; the authors' names are in comments in `targets.lisp`.
- `arithmetic/factorial` is included explicitly, as the paper names it as the source of `factorial`, even
  though `nonstd/nsa/factorial` already includes it.
- No other change: definition and statements are the paper's text.

### Prompt

<details>
<summary>Experiment 2 prompt (also in exp2/prompt.txt)</summary>

```text
Prove the theorems below in ACL2.

1. Create /work/defs.lisp containing exactly the text between the tags. defs.lisp holds the definitions the theorems use. Do not modify these files.

<defs.lisp>
(in-package "ACL2")

(include-book "arithmetic/factorial" :dir :system)
(include-book "nonstd/nsa/factorial" :dir :system)
(include-book "nonstd/nsa/sqrt" :dir :system)
(include-book "nonstd/nsa/exp" :dir :system)
(include-book "nonstd/nsa/ln" :dir :system)
(include-book "nonstd/nsa/trig" :dir :system)

(defun wallis-product (n)
  (if (zp n)
      1
      (* (/ (* 2 n) (1- (* 2 n)))
         (/ (* 2 n) (1+ (* 2 n)))
         (wallis-product (1- n)))))
</defs.lisp>

2. Write /work/solution.lisp. It must (include-book "defs") and then prove every theorem in <theorems>, each with exactly the name and statement given (MAIN-1, MAIN-2, MAIN-3). You may add your own definitions and lemmas before them.

<theorems>
(defthm MAIN-1
  (implies (and (natp n)
                (i-large n))
           (i-close (/ (factorial n)
                       (* (acl2-sqrt (* 2 (acl2-pi)))
                          (expt n n)
                          (/ (acl2-exp n))
                          (acl2-sqrt n)))
                    1)))

(defthm MAIN-2
  (implies (and (posp n)
                (i-large n))
           (i-close (acl2-ln (factorial n))
                    (+ (acl2-ln (expt n n))
                       (- n)
                       (acl2-ln (acl2-sqrt (* 2 (acl2-pi) n)))))))

(defthm MAIN-3
  (implies (and (natp n)
                (i-large n))
           (equal (standard-part (wallis-product n))
                  (/ (acl2-pi) 2))))
</theorems>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
/work/solution.lisp must certify with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done. When you are done, print the final contents of /work/solution.lisp.
```

</details>

## Notes for reviewers

**Experiment 1.**
- **Audit finding.** About 9 minutes in, the model ran `pip install sympy` (downloaded from PyPI) and used it
  once, as a scratch calculator, to factor one algebraic expression while planning a lemma. The certified file
  proves that step, like every step, in ACL2, so sympy cannot affect correctness. The model fetched no
  information about the problem. This breaks the prompt's "no internet" rule. The team has to decide whether
  to count the run with a footnote or rerun it.

**Experiment 2.**
- The session's worker restarted once (infrastructure). The model noted that its files survived and
  continued.

