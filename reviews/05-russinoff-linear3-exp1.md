# Review: 05-russinoff-linear3, experiment 1

Reviewer audit of `05-russinoff-linear3/exp1/solution.lisp` against the prompt (`exp1/prompt.txt`) and the
paper's own books (`source/authors-books/vectors.lisp`, and `projects/linear/field.lisp` in the community books).

**Verdict:** no problem found that makes `MAIN` wrong, weaker than the prompt, or vacuous. `MAIN` is the
conjunction of the paper's `injection-dim-<=` and `injection-surjection-dim-=`, stated over axioms that match the
paper's encapsulates one-to-one. The only additions are `booleanp` constraints on the recognizers (item 1), which
the proof does not need.

## Reproduction

- Image: `Dockerfile.base` (SBCL 2.6.1, ACL2 at commit `bc6f4f49e81a0711214a8d91f0d06e0e084d2204`, tag 8.7).
- The solution includes no community books; no setup needed.
- `tools/check-exp1.sh` (ACL2 path changed from `/opt/acl2` to `/root/acl2`): no banned events, last event is
  `(defthm MAIN …)`, `CERTIFIED with saved_acl2`. Proof time 0.51 s (the repo reports 1.2 s on other hardware).
- `solution.cert`: the only "ttag"/"skip-proofs" matches are the certificate's field names (`TTAGS`,
  `SKIPPED-PROOFSP`).

## Checks

1. **Soundness.** No `skip-proofs`, `defaxiom`, trust tags, `defattach`, `:program` mode, `make-event`,
   redefinition or `include-book`. The only `local` events are encapsulate witness definitions.
2. **The theorem.** `MAIN` (`solution.lisp:929`):
   `(implies (injective) (and (<= (dim-v) (dim-w)) (iff (surjective) (equal (dim-v) (dim-w)))))`.
   This is exactly the prompt's theorem, and the conjunction of the authors' `injection-dim-<=` and
   `injection-surjection-dim-=` (`vectors.lisp:1135`, `:1152`), which have the same hypothesis.
3. **Axioms against the paper**, one-to-one:
   - Field F (`solution.lisp:7`) vs `projects/linear/field.lisp`: the same 16 constraints (6 closure, 2 comm,
     2 assoc, 2 identities, 2 inverses, distributivity, 0 ≠ 1), plus `fp-booleanp`.
   - V (`solution.lisp:608`) vs `vectors.lisp:16`: the same 12 vector-space constraints (4 closure, comm,
     assoc, identity, inverse, unit, scalar assoc, two distributive laws), plus `vp-booleanp`.
   - Basis axioms: the same 5 (positive dimension; basis is a list of vectors; coordinates are a list of dim V
     scalars; spanning; independence). The paper's `flistnp`/`flistn0` (`field.lisp:159`, `:200`) mean the same as
     the solution's `f-listp` + length / `all-f0`.
   - W (`solution.lisp:686`): a renamed copy of V over the same field, as in the paper and the prompt.
   - T (`solution.lisp:817`) vs `lin` (`vectors.lisp:1010`): the same 4 constraints.
   - `injective` vs `lin-injective-p`: identical. `surjective` uses `defun-sk … exists` where the paper uses
     `defchoose lin-preimage`; logically the same.
   - `dim-v`/`dim-w` are the lengths of the bases, as in the paper (`vdim`).
4. **Computation tests.** Not applicable: every function in `MAIN` is constrained (generic field, spaces and
   map), so nothing executes. The model instantiations below replace them.
5. **Non-vacuity** (`05-russinoff-linear3-exp1-nonvac.lisp`, certified on top of `solution.lisp`). `MAIN` is
   functionally instantiated on two concrete models over the solution's generic field, which discharges every
   constraint of V, W and T for each model:
   - V = F (dim 1), W = F×F (dim 2), T(x) = (x, 0). Proves T is injective, then derives from `MAIN` that T is
     **not** surjective; also checks directly that (0, 1) has no preimage.
   - V = W = F (dim 1), T = identity. Proves T is injective, then derives from `MAIN` that T **is** surjective.

   So the hypothesis `(injective)` is satisfiable, the constraints have models with different dimensions, and
   both directions of the iff are exercised.

## Potential problems (most important first)

1. **Low. Extra `booleanp` constraints** on `fp`, `vp`, `wp` (`solution.lisp:24`, `:632`, `:710`; also on the internal helper space `gp`), not in the
   paper or the prompt. Strictly, `MAIN` covers only fields and spaces whose recognizers return `t`/`nil`. Any
   recognizer can be replaced by a boolean version without changing the structure, so this is not a real
   restriction. **Checked:** with all four `booleanp` constraints removed (`fp`, `gp`, `vp`, `wp`), the
   solution still certifies (0.49 s), so the proof does not depend on them.
2. **Very low. Linear combination recurses on the vectors** (`vlc`, on `xs`) where the paper's `vcomb` recurses on
   the coefficients. They differ only when the two lists have different lengths; every axiom that uses `vlc`
   requires equal lengths.
3. **Very low. One-sided identity axioms** (`0 + x = x`, `1·x = x`) where the paper uses `x + 0 = x`. Equivalent
   given commutativity.
4. **Note. `MAIN` is about one generic V, W and T** (constrained functions), so it applies to a particular space or
   map only by functional instantiation. That is the paper's own method, and the non-vacuity book shows it works.
5. **Note. "Basis is a list of dim V vectors"** is encoded as "basis is a true list of vectors" with dim V defined
   as its length. Same as the paper's `vlistnp-basis0`.
6. **Note. No theory of subspaces.** The solution does not define subspaces, subspace dimension, kernels or images.
   This is out of scope for experiment 1, not a gap in the solution:
   - **The prompt doesn't ask for it.** `exp1/prompt.txt` defines only V, W, T, injective and surjective.
   - **The paper doesn't use subspaces for this theorem.** In the authors' `vectors.lisp`, the two results the prompt
     combines, `injection-dim-<=` (line 1135) and `injection-surjection-dim-=` (line 1152), come before the subspace
     section (line 1245). Their proof sketches (lines 1129–1150) use only bases and linear dependence.
   - **Experiment 2 covers the subspace results.** `MAIN-4` (`sdim-well-defined`, well-defined subspace dimension),
     `MAIN-5` (basis of the kernel) and `MAIN-6` (basis of the image) are experiment-2 targets. The experiment-2
     solution proves all six targets, also on ACL2 master (`harness/master-recheck.txt:9`).

   If the subspace results should also have been tested in experiment 1, that is a point about how the prompt was
   chosen, not about this solution.

## Suggested follow-up

None required. Optionally, ask the authors whether a model-written `booleanp` constraint on recognizers is
acceptable; the proof does not need it (checked above).
