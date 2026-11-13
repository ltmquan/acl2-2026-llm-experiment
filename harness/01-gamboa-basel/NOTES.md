# 01 — Basel: harness notes

Our records for this paper: how the prompts and packages were made, and how the runs went. Reviewers do not
need this; the paper folder [`../../01-gamboa-basel/`](../../01-gamboa-basel/) has what they review.

**Contribution (our classification).** A theorem: a classical result (Wiedijk's list of 100 theorems, #14) formalized along a new route in ACL2(r).

## Results

| | Experiment 1 | Experiment 2 |
|---|---|---|
| Result | proved (certified) | 1 / 1 targets proved |
| Model time | 52 min | 28 min |
| Tool calls | 84 | 120 |
| Certification time of solution.lisp (ACL2(r) 8.7) | 133.8 s | 11.6 s |
| Audit (`exp*/audit.txt`) | CLEAN | CLEAN |
| solution.lisp: lines / definitions / theorems | 537 / 12 / 64 | 712 / 9 / 84 |

Authors' development: not available (no public books). Per-run accounts: `exp1/run.md`, `exp2/run.md`.

## Experiment 1: how the prompt was made from the paper

**Theorem chosen:** Σ_{i≥1} 1/i² = π²/6, the paper's headline result.

#### Sources
- Theorem sentence: abstract, sentence 1: "Leonhard Euler showed in 1735 that the sum of the squares of the
  reciprocals of the positive integers is exactly π²/6."
- Formula: §1, "In this paper we formalize in ACL2 a modern proof of Σ_{i=1}^∞ 1/i² = π²/6".

#### Edits
- "Leonhard Euler showed in 1735 that the sum …" → "The sum …" (removes history/attribution; would identify the problem — though the Basel problem is famous anyway).
- Formula detached from "In this paper we formalize in ACL2 a modern proof of" (anonymization; removes ACL2 framing).
- Definitions block: "None beyond standard mathematics." (added; nothing in the statement is non-standard).

## Experiment 2: how the package was made

No author books exist, so the package was transcribed from the paper. `definitions.lisp`
includes `nonstd/nsa/trig` (which defines `acl2-pi`; our choice, since the paper does not show its
include-books) and defines `basel-series`, verbatim from §3. This is the only author definition. Definitions
that would reveal the proof route (`omega-series`, `zeta`, `basel-odds`, …) are not given. A script
re-extracted the PDF text and confirmed that the definition and the statement match the paper token for token
(`exp2/extraction/verify/v3-compare.log`).

Full notes, scripts and logs: `exp2/extraction/`.

### Changes from the authors' text

- The paper's `defthmd basel-series-closed-form-close` becomes `(defthm MAIN-1 …)` without hints (the paper
  elides them). The statement is unchanged.
- The paper also gives a `standard-part` variant (`basel-series-closed-form`). The target uses the i-close
  form, which the author presents as the preferred one.

### Checker files

`exp2/checker/` holds the exact files `tools/check-exp2.py` certifies the solution against. The paper folder's
`exp2/definitions.lisp` is the same file with comments added (`tools/check-comments-only.py`).

| File | SHA-256 |
|---|---|
| `exp2/checker/defs.lisp` | `41675c2b37f813596f7a3b22017b424caddef67acbf9d22de68bbc3608eaa4b3` |

## Run notes

**Experiment 2.**
- **Checker change.** The model wrapped each section of its file in `(encapsulate () …)`, so MAIN-1 sits inside
  the last (non-local) `encapsulate`, not at the top level. The first version of `check-exp2.py` looked only at top-level events and reported
  `TARGET-MISMATCH: missing main-1`. We then changed the checker to also accept a target exported from an
  `encapsulate` or `progn` at any depth, but never one under `local`. We tested that a local MAIN is still
  rejected. With this change the unchanged solution passes. An extra book that includes the solution and
  proves the target statement `:by main-1` also certified, which confirms that MAIN-1 is exported with
  exactly the target statement.

