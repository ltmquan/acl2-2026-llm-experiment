# 05 — Linear III: harness notes

Our records for this paper: how the prompts and packages were made, and how the runs went. Reviewers do not
need this; the paper folder [`../../05-russinoff-linear3/`](../../05-russinoff-linear3/) has what they review.

**Contribution (our classification).** A library: a textbook chapter of linear algebra, with a method (constructive definitions over constrained functions, for later functional instantiation). There is no single headline theorem; the main results are injective ⇒ dim V ≤ dim W and (surjective ⇔ equal dimension), a constructive inverse, extension to a basis, well-defined subspace dimension, and kernel/image bases.

## Results

| | Experiment 1 | Experiment 2 |
|---|---|---|
| Result | proved (certified) | 6 / 6 targets proved |
| Model time | 16 min | 55 min |
| Tool calls | 53 | 194 |
| Certification time of solution.lisp (ACL2 8.7) | 1.2 s | 3.6 s |
| Audit (`exp*/audit.txt`) | CLEAN | CLEAN |
| solution.lisp: lines / definitions / theorems | 934 / 101 / 201 | 2038 / 20 / 248 |

Authors' development: 2 files, 7,592 lines, 193 definitions, 473 theorems. Per-run accounts: `exp1/run.md`, `exp2/run.md`.

## Experiment 1: how the prompt was made from the paper

**Theorem chosen:** If T: V → W is injective then dim V ≤ dim W, and then T is surjective iff dim V = dim W (two results of §4, composed into one statement).

#### Sources
- Theorem: Sec. 4, p. 9 — prose before `injection-dim-<=` ("Now suppose lin is injective and vdim > wdim") and before `injection-surjection-dim-=` ("Next, we show that if lin is injective, then lin is surjective iff vdim = wdim.").
- F, V, axioms: Sec. 1 p. 1 ("arbitrary finite-dimensional vector space over the generic field"; field "arbitrary"), Sec. 2 p. 3 bullets.
- W: Sec. 4 p. 8 ("a vector space W, essentially the same as V, but with the functions renamed").
- Linear transformation: Sec. 4 p. 8; injective/surjective: Sec. 4 p. 9 (code only, translated).

#### Theorem: COMPOSED (flag)
No single English sentence states both results. Composed:
- "Now suppose lin is injective and vdim > wdim. … Thus, we have [injection-dim-<=]" → "If T is injective, then dim V ≤ dim W." (contrapositive of the proof's setup, stated as the formal result says).
- "Next, we show that if lin is injective, then lin is surjective iff vdim = wdim." → "Moreover, if T is injective, then T is surjective iff dim V = dim W." ("we show that" dropped, "Next" → "Moreover").
- Note: the task description says "injective + equal dimensions ⇒ surjective"; the paper's result is the **iff**, so the iff is used.

#### Edits to definitions
- ACL2 names → math: `lin` → T; `vdim`/`wdim` → dim V / dim W; `v0`/`w0` → 0; `vbasis0` → "the canonical basis"; `(vcoords0 x)` → "the coordinates of x"; `f0` → 0. (Rule 3.)
- "The following encapsulation characterizes the vector space V over the field F" / "The constrained functions include the following" → "The vector space V is given by the following" (removes encapsulation/representation hint).
- Operation bullets: ACL2 names removed; "constant function that returns" → "constant that is". "The associated exported theorems (elided above, along with the local definitions) include" → "These satisfy"; "v+"/"v*" → "vector addition"/"scalar multiplication". "constrained functions" → "functions".
- vdim bullet ("the length of vbasis0, which is the dimension of V") → "The length of the canonical basis is the dimension of V, written dim V."
- "Four additional axioms … are exported" → "The following axioms … hold" (five listed, see next).
- posp-vdim bullet: kept "this ensures that V is a nontrivial vector space"; **cut** "The only reason for this assumption is that it simplifies…matrices over F" (formalization hint).
- **Added** axiom "the list of coordinates of x is a list of dim V scalars": only in the code (`flistnp-vcoords0`), not in prose.
- "vlist" terminology dropped (not needed).
- W paragraph: **composed** from "a vector space W, essentially the same as V, but with the functions renamed … All definitions and lemmas pertaining to V are readily adapted to W"; "same field F" is implied by `lin-v*` using the same scalar c.
- Linear transformation, injective, surjective: **translated from ACL2 code** (lin encapsulate, `lin-injective-p`, `lin-surjective-p`); no paper prose exists. "a generic linear transformation lin mapping V to W" kept.

#### Left undefined (standard)
Field, vector space axioms (named only generically, as the paper does), linear combination (paper's `vcomb` = Σ c_i x_i, standard), list/length.

## Experiment 2: how the package was made

`definitions.lisp` includes `projects/linear/reduction` (Parts I–II, in 8.7) and copies the
authors' Part III forms verbatim from master `vectors.lisp`, in order: the V, W, lin and sp encapsulates, the
`sbasis1` encapsulate, and the constructive functions the targets use (`lin-inv`, `extend-to-basis`,
`kbasis`, `kcoords`, `ibasis`, `icoords`, …). Definitions no target needs are left out. Admitting the
encapsulate witnesses, a termination hint and the `sbasis1` encapsulate needs 89 local lemmas, copied verbatim
from `support/vectors.lisp`; a greedy pruning removed every one that was not needed.
**Caveat:** some of these local lemmas are steps the authors also use toward the targets (for example
`vdepp-vcomb-v0`). They are not exported, but the checker's copy of `definitions.lisp` contains them. The
model saw a different copy without them (see the experiment-2 report).

Full notes, scripts and logs: `exp2/extraction/`.

**What the model saw.** The checker's `defs.lisp` needs local lemmas to admit some definitions, so the model
got `exp2/model-facing/defs.lisp` instead (local lemmas, hints and comments removed, definitions wrapped in
`skip-proofs`). The two copies define the same world (`tools/world-dump.lsp`).

### Changes from the authors' text

- Package DM (the authors' package), with `cert.acl2` loading `projects/numbers/portcullis`.
- Targets are named MAIN-k. MAIN-1, MAIN-5 and MAIN-6 are conjunctions of the authors' theorems with the same
  hypotheses. `defthmd` became `defthm`; hints and rule classes dropped. Statement bodies are the authors' text.
- The kernel and image halves are separate targets because their constructions and proofs differ, and the
  image proof builds on the kernel one.
- The 8.7 Parts I–II differ from master only in the field encapsulate (master adds formals, guards and a
  `defattach` to `f+ f* f- f/`); constraints and bodies are identical, and Part III declares no guards.

### Checker files

`exp2/checker/` holds the exact files `tools/check-exp2.py` certifies the solution against. The paper folder's
`exp2/definitions.lisp` is the same file with comments added (`tools/check-comments-only.py`).

| File | SHA-256 |
|---|---|
| `exp2/checker/cert.acl2` | `e39b0ab97ce3526d595a9df27a4e5a4fe42bdbbc2e6eef70ed6a782d17901975` |
| `exp2/checker/defs.lisp` | `5c74b7d933b519762fb813de4fd0b02384fcbbf8b4564b6cc47594bf305941d7` |

## Run notes

**Experiment 2.**
- Proving the targets on 8.7 needs Part II lemmas that are only on master (e.g. `sol0p`, `flist-minus`); the
  model had to re-derive what it needed.

