# 01 — Basel

**Paper:** Ruben Gamboa, *An Alternative Proof in ACL2(r) of Euler's Solution to the Basel Problem* (ACL2 Workshop 2026). PDF in `source/paper.pdf`.
**Logic:** ACL2(r).

## The paper

The paper proves in ACL2(r) that the sum of the reciprocals of the squares of the positive
integers is π²/6 (the Basel problem). It follows a modern proof, not Euler's original argument. The
statement uses non-standard analysis: for every infinitely large n, the partial sum is infinitely close
to π²/6.

**Contribution.** A theorem: a classical result (Wiedijk's list of 100 theorems, #14) formalized along a new
route in ACL2(r).

**Authors' ACL2 books.** **None available.** The author's books are not in the ACL2 community books, and there is
**no pull request** for them in the ACL2 repository (we checked the open and closed pull requests on
2026-11-13). `source/` therefore has only the paper. The experiment-2 definitions and target were
transcribed from the paper and checked against its text.

## Files

```
01-gamboa-basel/
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
| Result | proved (certified) | all 1 target(s) proved (certified, statements matched) |
| Model time | 52 min | 28 min |
| Tool calls | 84 | 120 |
| Certification time of solution.lisp (ACL2(r) 8.7) | 133.8 s | 11.6 s |
| Audit | CLEAN | CLEAN |
| solution.lisp: lines / definitions / theorems | 537 / 12 / 64 | 712 / 9 / 84 |

Authors' development (for scale): not available (no public books).

*Model time* runs from when the model received the prompt to the end of its run (setup not included).
Certification time is for `solution.lisp` alone, with its dependencies already certified, on our build
(experiment 2: against `exp2/checker/`). Sizes are counted with `tools/sizes.py` (definitions = `defun`,
`define`, `defun-sk`, `defmacro`, … and encapsulated functions; theorems = `defthm`, `defrule`, …, local
ones included). Both experiments: first attempt, Claude Opus 5.5 at medium effort.

## Experiment 1: English definitions and theorem

**Theorem given:** Σ_{i≥1} 1/i² = π²/6, the paper's headline result.

### Statement rewrites (paper text → prompt)

The definitions and theorem were copied from the paper as close to verbatim as possible. Every edit:

#### Sources
- Theorem sentence: abstract, sentence 1: "Leonhard Euler showed in 1735 that the sum of the squares of the
  reciprocals of the positive integers is exactly π²/6."
- Formula: §1, "In this paper we formalize in ACL2 a modern proof of Σ_{i=1}^∞ 1/i² = π²/6".

#### Edits
- "Leonhard Euler showed in 1735 that the sum …" → "The sum …" (removes history/attribution; would identify the problem — though the Basel problem is famous anyway).
- Formula detached from "In this paper we formalize in ACL2 a modern proof of" (anonymization; removes ACL2 framing).
- Definitions block: "None beyond standard mathematics." (added; nothing in the statement is non-standard).

### Prompt

<details>
<summary>Experiment 1 prompt (also in exp1/prompt.txt)</summary>

```text
Formalize the definitions and the theorem below in ACL2, and prove the theorem.

<definitions>
None beyond standard mathematics.
</definitions>

<theorem>
The sum of the squares of the reciprocals of the positive integers is exactly π²/6:

    Σ_{i=1}^{∞} 1/i² = π²/6.
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
| MAIN-1 | `basel-series-closed-form-close` | paper §6, p. 13 | for every infinitely large positive integer n, Σ_{k=1}^{n-1} 1/k² is i-close to π²/6 |

### How the definitions were extracted

No author books exist, so the package was transcribed from the paper. `definitions.lisp`
includes `nonstd/nsa/trig` (which defines `acl2-pi`; our choice, since the paper does not show its
include-books) and defines `basel-series`, verbatim from §3. This is the only author definition. Definitions
that would reveal the proof route (`omega-series`, `zeta`, `basel-odds`, …) are not given. A script
re-extracted the PDF text and confirmed that the definition and the statement match the paper token for token
(`exp2/extraction/verify/v3-compare.log`).

The general procedure, and how each package was checked, is in [`../EXPERIMENT-2.md`](../EXPERIMENT-2.md);
the full notes for this paper are in `exp2/extraction/NOTES.md`.

Checker files:

| File | SHA-256 |
|---|---|
| `exp2/checker/defs.lisp` | `41675c2b37f813596f7a3b22017b424caddef67acbf9d22de68bbc3608eaa4b3` |

`exp2/definitions.lisp` differs from `exp2/checker/defs.lisp` only in comments
(`tools/check-comments-only.py`).

### Statement rewrites (authors' ACL2 → targets)

- The paper's `defthmd basel-series-closed-form-close` becomes `(defthm MAIN-1 …)` without hints (the paper
  elides them). The statement is unchanged.
- The paper also gives a `standard-part` variant (`basel-series-closed-form`). The target uses the i-close
  form, which the author presents as the preferred one.

### Prompt

<details>
<summary>Experiment 2 prompt (also in exp2/prompt.txt)</summary>

```text
Prove the theorems below in ACL2.

1. Create /work/defs.lisp containing exactly the text between the tags. defs.lisp holds the definitions the theorems use. Do not modify these files.

<defs.lisp>
(in-package "ACL2")

(include-book "nonstd/nsa/trig" :dir :system)

(defun basel-series (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      0
      (+ (expt i -2)
         (basel-series (1+ i) n))))
</defs.lisp>

2. Write /work/solution.lisp. It must (include-book "defs") and then prove every theorem in <theorems>, each with exactly the name and statement given (MAIN-1). You may add your own definitions and lemmas before them.

<theorems>
(defthm MAIN-1
  (implies (and (posp n)
                (i-large n))
           (i-close (basel-series 1 n)
                    (/ (expt (acl2-pi) 2) 6))))
</theorems>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
/work/solution.lisp must certify with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done. When you are done, print the final contents of /work/solution.lisp.
```

</details>

## Notes for reviewers

**Experiment 2.**
- **Checker change.** The model wrapped each section of its file in `(encapsulate () …)`, so MAIN-1 sits inside
  the last (non-local) `encapsulate`, not at the top level. The first version of `check-exp2.py` looked only at top-level events and reported
  `TARGET-MISMATCH: missing main-1`. We then changed the checker to also accept a target exported from an
  `encapsulate` or `progn` at any depth, but never one under `local`. We tested that a local MAIN is still
  rejected. With this change the unchanged solution passes. An extra book that includes the solution and
  proves the target statement `:by main-1` also certified, which confirms that MAIN-1 is exported with
  exactly the target statement.

