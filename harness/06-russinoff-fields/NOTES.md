# 06 — Fields: harness notes

Our records for this paper: how the prompts and packages were made, and how the runs went. Reviewers do not
need this; the paper folder [`../../06-russinoff-fields/`](../../06-russinoff-fields/) has what they review.

**Contribution (our classification).** Mainly a library and representation technique (fields and embeddings as first-order objects), with standard algebra theorems proved along the way.

## Results

| | Experiment 1 | Experiment 2 |
|---|---|---|
| Result | proved (certified) | 4 / 4 targets proved |
| Model time | 38 min | 1 h 57 min |
| Tool calls | 91 | 237 |
| Certification time of solution.lisp (ACL2 8.7) | 2.6 s | 750.5 s |
| Audit (`exp*/audit.txt`) | CLEAN | CLEAN |
| solution.lisp: lines / definitions / theorems | 1541 / 58 / 230 | 3101 / 58 / 552 |

Authors' development: 6 files without `galois.lisp`, 24,094 lines, 486 definitions, 1,616 theorems. Per-run accounts: `exp1/run.md`, `exp2/run.md`.

## Experiment 1: how the prompt was made from the paper

**Theorem chosen:** If f is a field (a tower of simple algebraic extensions over Q, F_p or the generic field F0), then f satisfies the field axioms; in particular every nonzero element has a multiplicative inverse. Composed from §3.

**THEOREM IS COMPOSED (flag).** The paper has no single English statement. Sources: the first sentence of §3 (p. 5), plus the "In particular" clause taken from §3's `fmul-frecip-**`, "the defining property of the multiplicative inverse" (pp. 6–7).

#### Sources
- F0: §1 p.1. Base fields and Q/F_p/F0: §2 pp.2–3. Extension and recursive definition: §2 ¶1 p.2 (degree ≥ 2 from the fieldp code, p.5). "Field reserved": §1 p.2. Monic: p.4. Reducible: p.5. Structure list: p.3.

#### Edits (original → edited)
1. "The first defines a generic field through seven constrained functions: (fp x), a predicate…; … The exported constraints on these functions correspond to the usual field axioms." → "A generic field F0 is defined through seven functions: … Nothing is assumed about these functions except that they satisfy the usual field axioms." The ACL2 names and "encapsulation" are removed.
2. "Our theory" → "The theory". "Since we are interested in number fields and finite fields," is deleted.
3. "we shall include the generic field described in Section 1 as a base field, for two reasons: …" → "the generic field F0 is included as a base field." The motivation is cut.
4. "we shall informally refer to … as Q, Fp, and F0" → "Q, F_p, and F0 denote …".
5. Added "of degree at least 2". It is stated only in the `fieldp` code.
6. "A field will be recursively defined" → "is recursively defined". Added "The term field is reserved for these objects." (from §1).
7. Monic: "(i.e., with leading coefficient (fone f))" → a full sentence.
8. "If a polynomial p has a non-constant monic divisor of lesser degree, then the following function returns such a divisor and p is said to be reducible" → "A polynomial p over f is reducible if …; otherwise p is irreducible." The `defchoose` is removed.
9. The structure bullet list is turned into prose, without ACL2 names.
10. Theorem: "Our next objective is to prove that if f satisfies the predicate fieldp, then f satisfies the field axioms, i.e., …F0, and the polynomials over f satisfy the axioms for a commutative ring with unity." → "If f is a field, then f satisfies the field axioms, i.e., …F0." The ring clause is dropped because it is a supporting result. "In particular …" is added (composed).

**Omitted on purpose:**
- the encodings (0, a prime, `'f0`, (p . f));
- polynomials as coefficient lists with leading-zero stripping;
- the Bézout-based inverse in an extension, which is both an encoding and a proof hint.

## Experiment 2: how the package was made

`definitions.lisp` is assembled from verbatim line ranges of master `extensions.lisp`,
`vectors.lisp`, `polynomials.lisp` and `embeddings.lisp`, plus the 8.7 books `projects/groups/groups` and
`projects/linear/field`. It contains the 21-function mutual recursion, `fieldp`, the 16 axiom predicates,
`field-axioms-p`, polynomial evaluation, roots and factorization, `edegree`, the lifting functions and
embeddings. Local lemmas are purely syntactic length facts needed for termination. Two predicates are new (not
by the authors): `algebraic-witness` (for MAIN-3) and `all-embeddingp` (for MAIN-4).

Full notes, scripts and logs: `exp2/extraction/`.

**What the model saw.** The checker's `defs.lisp` needs local lemmas to admit some definitions, so the model
got `exp2/model-facing/defs.lisp` instead (local lemmas, hints and comments removed, definitions wrapped in
`skip-proofs`). The two copies define the same world (`tools/world-dump.lsp`).

### Changes from the authors' text

- **MAIN-3 and MAIN-4 are neutral restatements.** The authors' statements use the constructive `min-poly` and
  `embeddings`, which would reveal the proof. MAIN-3 says instead that a suitable polynomial exists
  (`defun-sk algebraic-witness`); MAIN-4 bounds the length of any duplicate-free list of embeddings. Both were
  proved from the authors' theorems on master.
- **The termination hint of `factorization` is changed.** The authors' hint uses `reduciblep-product`, which
  needs most of the MAIN-1 theory; we prove the needed length bound locally instead. Measure and body are
  unchanged.
- MAIN-2 conjoins two authors' theorems with the same hypotheses. `defthmd` became `defthm`, hints dropped.
- Package DM, with `cert.acl2` loading `projects/numbers/portcullis`.

### Checker files

`exp2/checker/` holds the exact files `tools/check-exp2.py` certifies the solution against. The paper folder's
`exp2/definitions.lisp` is the same file with comments added (`tools/check-comments-only.py`).

| File | SHA-256 |
|---|---|
| `exp2/checker/cert.acl2` | `e39b0ab97ce3526d595a9df27a4e5a4fe42bdbbc2e6eef70ed6a782d17901975` |
| `exp2/checker/defs.lisp` | `31fdd442fa69360e77e32dc00d02c894f9baae30e7a1e7b3162ca818cb533b6e` |

## Run notes

**Experiment 2.**
- The model ended its first turn while waiting for a certification and was woken by its own `Monitor` tool
  (a local wait loop); it was not prompted by anyone. The audit therefore uses the whole transcript as the run.
- The final message claims the given `defs.lisp` had an unbalanced paren. It did not: the model dropped a paren
  when writing the file from the prompt. The checker uses its own copy, so this does not matter.

