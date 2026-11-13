# 03 — Flip graph: harness notes

Our records for this paper: how the prompts and packages were made, and how the runs went. Reviewers do not
need this; the paper folder [`../../03-luu-flipgraph/`](../../03-luu-flipgraph/) has what they review.

**Contribution (our classification).** A theorem: a recent (2026) combinatorial and linear-algebra result. The paper reports 29 books, 215 definitions and 791 theorems; the connectivity proof alone is 19 books with 137 functions and 527 theorems.

## Results

| | Experiment 1 | Experiment 2 |
|---|---|---|
| Result | proved (certified) | 4 / 4 targets proved |
| Model time | 50 min | 58 min |
| Tool calls | 177 | 166 |
| Certification time of solution.lisp (ACL2 8.7) | 26.7 s | 56.1 s |
| Audit (`exp*/audit.txt`) | CLEAN | CLEAN |
| solution.lisp: lines / definitions / theorems | 1750 / 98 / 255 | 3420 / 91 / 455 |

Authors' development: 66 files (including `experiments/`), 27,404 lines, 753 definitions, 1,963 theorems. Per-run accounts: `exp1/run.md`, `exp2/run.md`.

## Experiment 1: how the prompt was made from the paper

**Theorem chosen:** Theorem 5.1 (flip-plus connectivity): over F2, for n ≥ 2, the flip graph with flip and plus edges is strongly connected.

#### Sources
- Theorem: §5, Theorem 5.1, p. 8 (verbatim, both sentences; label "(Flip-plus connectivity [12])" dropped).
- Notation + F2 convention: §2 opening paragraph, p. 2.
- Rank-one tensor: Definition 2.1, p. 2.
- M(n): Definition 2.2 (eq. (1)) and the sentence after it, p. 2.
- Scheme: Definition 2.3, p. 3 (schemes are **multisets** of nonzero rank-one tensors).
- Flip/plus: Definition 2.5 and the closing sentence "These transformations on the B and C positions are defined analogously.", p. 3.

#### Edits
1. "Our definitions are over F2, consistent with the proof. The definitions extend to any field, but the connectivity proof does not: it deletes identical pairs of summands, which relies on 1 + 1 = 0." → "The definitions are over F2." Reason: remove "we"/"our"; the cut text is a proof hint.
2. Dropped "We also only consider square matrices, but our definitions can be extended to rectangular ones." (authorial voice; n × n is explicit everywhere).
3. Removed numbering/citations from definition labels: "Definition 2.1 (Rank-one tensor)." → "Definition (Rank-one tensor)."; same for 2.2 "[12]", 2.3 "[12]", 2.5 "[12]". Dropped equation number "(1)".
4. Dropped "The matrix multiplication tensor is defined as follows." (connective).
5. Kept "We call such a multiset a scheme" and "we define the matrix multiplication tensor" — definitional "we", not authorial reference; reviewer may change to "Such a multiset is called a scheme."
6. Omitted all intervening text: rank-R decomposition (eq. 2) and the algorithm discussion, unit matrices E_ij, Strassen example (Ex. 2.4), §2.3, and the paragraph after Def 2.5 ("Both transformations preserve the sum ... again a decomposition of M(n)") — the latter is an intermediate fact/lemma.
7. Math notation transcribed to plain Unicode: F2^(n×n), subscripts as _{…}, M(n) for script-M superscript (n), A^(r) for A^{(r)}.
8. Theorem: label removed only.

## Experiment 2: how the package was made

`definitions.lisp` holds 89 of the authors' definitions (`define`s and one `defun-sk`), the
definitional closure of the four statements, computed in ACL2 from bodies, guards and measures. Each `define`
is verbatim except that its `///` section (theorems) is removed; `:returns` theorems stay, as part of the
definition form. It leaves out `main-path` and every path construction. Local lemmas, needed only for guard
verification, are the authors' lemmas copied verbatim, plus a few of our own; a greedy minimization showed
that each one is needed. The one non-author definition is `flip-plus-reachablep` (below).

Full notes, scripts and logs: `exp2/extraction/`.

**What the model saw.** The checker's `defs.lisp` needs local lemmas to admit some definitions, so the model
got `exp2/model-facing/defs.lisp` instead (local lemmas, hints and comments removed, definitions wrapped in
`skip-proofs`). The two copies define the same world (`tools/world-dump.lsp`).

### Changes from the authors' text

- **MAIN-1 is existential.** The authors' theorem states that the constructive `main-path` is a valid path.
  Giving that statement would hand over both the formalization and the proof, so MAIN-1 instead says that a
  valid path exists, using a new `defun-sk flip-plus-reachablep` (in `definitions.lisp`, marked as not from the
  authors). The hypotheses are the original ones: `(correct-schemep sch n) (correct-schemep sch2 n) (natp n)
  (<= 2 n)`. We proved MAIN-1 from the authors' theorem by instantiating the witness with `main-path`.
- **MAIN-3 and MAIN-4 are separate targets**, not one conjunction, because their hypotheses differ:
  `scheme-algo-correct` assumes `correct-schemep`, `algo-scheme-of-scheme-algo` only `schemep`.
- Otherwise verbatim: `defrule` written as `defthm`, hints dropped.

### Checker files

`exp2/checker/` holds the exact files `tools/check-exp2.py` certifies the solution against. The paper folder's
`exp2/definitions.lisp` is the same file with comments added (`tools/check-comments-only.py`).

| File | SHA-256 |
|---|---|
| `exp2/checker/defs.lisp` | `b8c4e6067eb732a37edf0ffe2a11b6e940fd59a5dca96ee842b23511ef23647b` |

## Run notes

**Experiment 1.**
- For comparison: the paper reports that its connectivity proof is 19 books with 137 functions and 527
  theorems, and that an unassisted LLM formalization of the companion paper proved connectivity in 9 books
  with 409 theorems.


