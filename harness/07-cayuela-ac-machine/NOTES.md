# 07 — AC machine: harness notes

Our records for this paper: how the prompts and packages were made, and how the runs went. Reviewers do not
need this; the paper folder [`../../07-cayuela-ac-machine/`](../../07-cayuela-ac-machine/) has what they review.

**Contribution (our classification).** A case study (mechanical checking of a derivation). The paper's headline (the torque sign) is a restatement of a lemma, so for experiment 1 we chose its most substantial derivation. This is the easy tier of the experiment.

## Results

| | Experiment 1 | Experiment 2 |
|---|---|---|
| Result | proved (certified) | 4 / 4 targets proved |
| Model time | 6 min | 2.6 min |
| Tool calls | 41 | 18 |
| Certification time of solution.lisp (ACL2(r) 8.7) | 7.1 s | 1.5 s |
| Audit (`exp*/audit.txt`) | CLEAN | CLEAN |
| solution.lisp: lines / definitions / theorems | 240 / 5 / 30 | 100 / 0 / 15 |

Authors' development: 14 files, 1,069 lines, 43 definitions, 78 theorems. Per-run accounts: `exp1/run.md`, `exp2/run.md`.

## Experiment 1: how the prompt was made from the paper

**Theorem chosen:** The three-phase collapse: Σ_{n=0}^{2} (2/3)(A·e^{jnγ}) e^{jnγ} = A for every planar vector A, with γ = 2π/3.

#### Sources
- Theorem: §4.2, displayed equation after "Generalized to an arbitrary planar vector A constant in n:"
  Σ_{n=0}^{2} (2/3)(A · e^{jnγ}) e^{jnγ} = A. (In the paper A carries a vector arrow.)
- "a vector (a, b) corresponds to the complex number a + jb": §2, "using the identification of R² with C".
- "· … the planar dot … product": §2 ("·, × are the planar dot and cross products").
- "γ = 2π/3": §4.1 ("with γ = 2π/3") and Fig. 1.

#### Edits
- "Generalized to an arbitrary planar vector A constant in n:" → "For an arbitrary planar vector A:" ("Generalized" refers to the
  paper's flux-linkage context; "constant in n" is implicit once A is a fixed vector).
- Vector arrow on A dropped (plain-text rendering).
- Definitions assembled from three places; "where j is the imaginary unit" added (engineering notation; j is otherwise undefined).
- Cross product omitted (not used by this theorem).
- Electrical-engineering context (flux linkage, stator, 120° symmetry) omitted: not needed to state the theorem.

## Experiment 2: how the package was made

`definitions.lisp` has two parts. Part A is verbatim from books 00, 01, 02 and 05: the complex/vector
functions, the authors' encapsulated `cosine`/`sine` (with its constraints), `eiz`, `e0 e1 e2` and `torque-W`.
Part B is from book 06 (the ACL2(r) version), with every function renamed with a `G-` prefix (see below).
It includes `arithmetic-5/top` and `nonstd/nsa/trig`.

Full notes, scripts and logs: `exp2/extraction/`.

**What the model saw.** The checker's `defs.lisp` needs local lemmas to admit some definitions, so the model
got `exp2/model-facing/defs.lisp` instead (local lemmas, hints and comments removed, definitions wrapped in
`skip-proofs`). The two copies define the same world (`tools/world-dump.lsp`).

### Changes from the authors' text

- **Part B renamed with prefix `G-`.** Book 06 redefines `cplxp`, `re`, `cplx` and `cscale` with different
  bodies from book 00, so the two cannot share one world. Every book-06 function the targets use is renamed
  (`cplxp → g-cplxp`, …); MAIN-3 and MAIN-4 use the renamed names. Bodies are otherwise verbatim.
- **`g-gamma-val` is written neutrally** as `(* 2/3 (acl2-pi))`, not the authors'
  `(+ (* 1/3 (acl2-pi)) (* 1/3 (acl2-pi)))`, which hints at the cosine-of-sums route. We proved the two equal.
- The book-06 lemma `cplxp-of-omega-pow` is local (needed only for guard verification).

### Checker files

`exp2/checker/` holds the exact files `tools/check-exp2.py` certifies the solution against. The paper folder's
`exp2/definitions.lisp` is the same file with comments added (`tools/check-comments-only.py`).

| File | SHA-256 |
|---|---|
| `exp2/checker/defs.lisp` | `56d3c7d464ae45750665a433f1d6d6f9b5bc28d9e4412933c560797e8d5c909b` |

## Run notes

**Experiment 1.**
- Pilot run: the prompt lacks the final "print the file" sentence of the other prompts. The audit cut-off is
  the end of the model's run; one later tool call (after our request) is excluded.


