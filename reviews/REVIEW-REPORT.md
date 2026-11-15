# Review report: papers 04, 05 and 06, experiment 1

Reviewer: Sam. Assigned papers: 04-binmonjil-chandy-lamport, 05-russinoff-linear3 and 06-russinoff-fields, all
ACL2 only. This report covers the experiment-1 solutions: the model got English definitions and an English
theorem, and wrote the ACL2 definitions, statement and proof itself. The detailed findings are in the per-paper
files listed at the end.

## Summary

| Paper | Certifies on ACL2 8.7 | `MAIN` matches prompt and paper | Non-vacuous | Most important caveat |
|---|---|---|---|---|
| 04 Chandy–Lamport | yes | yes; stronger in one respect | yes | Starting-state hypothesis differs from the paper's; segment-completion definitions are not used by the proof |
| 05 Linear III | yes | yes, exactly | yes | Extra `booleanp` constraints on recognizers (not needed by the proof) |
| 06 Fields | yes | yes | yes | Extension multiplication is not proved to be polynomial multiplication mod p |

For all three, I found no problem that makes `MAIN` false, weaker than the prompt, or vacuous.

## How the checks were done

- **Image.** `Dockerfile.base` was changed to build only SBCL 2.6.1 and ACL2 at commit `bc6f4f49e8` (tag 8.7),
  without ACL2s. The README says the experiments used SBCL 2.2.9; the image uses 2.6.1.
- **Setup inside the image.** Certifying community books first needs `make build/Makefile-features` in
  `books/`. Then:
  - 04 needs `misc/records` and `misc/equal-by-g`;
  - 06 needs `kestrel/prime-fields/prime-fields` and `prime-fields-rules`;
  - 05 needs no books.
- **Certification.** Each solution was checked with the repo's `tools/check-exp1.sh` (only its ACL2 path changed).
  The script rejects banned events, requires the last event to be `(defthm MAIN …)`, and certifies.
- **Soundness scan.** Each file was also scanned for `defattach`, `:program` mode and `local` events. The
  "ttag"/"skip-proofs" strings in the `.cert` files are only the certificate's field names.
- **Faithfulness.** Each `MAIN` and the definitions it depends on were compared with the prompt and with the
  authors' own ACL2 books in `source/authors-books/`.
- **Non-vacuity.** For each paper, a small extra book was certified on top of the solution, showing that
  `MAIN`'s hypotheses hold for real examples.
- **Who did what.** The 06 audit was done directly. The 04 and 05 audits were done by delegated agents following the
  same steps; I spot-checked their output files, `MAIN` statements and non-vacuity certificates.

## 04 Chandy–Lamport

**What `MAIN` says.** Let `prefix` be a legal execution from the initial state, `st` the state it reaches, and `e`
a complete checkpoint segment from `st`. Then running the prerecording inputs of `e` followed by its postrecording
inputs gives a state equivalent to running `e`.

**Against the paper.** The paper's theorem is `checkpoint-complete-segment-reordered-run-state-equivalent`
(`global_reorder.lisp:5748`). The two statements have the same shape, but differ in these places:
- **Starting state: a real difference.**
  - The paper assumes any state satisfying its structural invariant (`good-state-p`) with no recovery in
    progress.
  - The solution assumes a state reachable from its initial state by a legal prefix.
  - Neither covers the other. The paper never defines `good-state-p` in its text, so the prompt substituted
    reachability. This was the prompt's choice, not the model's.
- **Pre/post classification and completion: same intent, different mechanism.**
  - The paper keeps separate cut bookkeeping during a scan, and proves it agrees with the real state.
  - The solution reads the real state directly: a process has taken its cut once the snapshot id is in its list.
  - Both classify an input before its own effect, so the recording event itself is prerecording.
  - No proof shows the two definitions agree.
- **Conclusion.** Same equivalence relation (the arguments are swapped). Internally the solution proves the two
  final states are *equal*, which is stronger.
- **Scope.** The paper's model includes crash, recovery and no-op inputs, which its theorem then excludes. The
  solution leaves all three out of the model.

The paper's printed `checkpoint-start-end-segment-p` (p. 11–12) omits four conjuncts that the books contain, so the
comparison used the books.

**Non-vacuity and tests.** A concrete two-process run was checked:
- one message in flight in each direction, and a snapshot started by process 1;
- the recorded snapshot is the correct Chandy–Lamport one;
- the reordering actually changes the order of inputs, and both orders reach the same state.

A certified book shows that all three hypotheses of `MAIN` hold together for this run, and that three malformed
segments are rejected.

**Potential problems.**
1. **Low to moderate.** The proof only uses the `legal-exec` part of `complete-segment-p`. The key lemma
   (`reorder-from-state`) holds for any legal execution and any snapshot id. So mistakes in `checkpoint-complete`,
   `incomplete-before-each` or `segment-target` would not be caught by the proof. They were checked only on the one
   example system.
2. **Low.** A compute step builds its outgoing messages from the new local state. The authors' model uses the old
   one. The prompt leaves this open.
3. **Low.** The topology is unconstrained: no consistency between in/out lists, and no unique ids. The authors
   constrain both. This makes the theorem more general.
4. **Low.** Checkpoint initiation is legal for any valid process. The authors restrict it only during recovery,
   which neither model includes.
5. **Low.** `MAIN` does not state that the reordered execution is legal. Neither the prompt nor the authors' theorem
   does either.

**Not checked:** topologies larger than two processes, and concurrent snapshots.

**Visualization.** `04-binmonjil-chandy-lamport-exp1-commute.html` is an interactive page that runs a JavaScript
port of the solution's model, using the ACL2 names. The port agreed with ACL2 on 41 executions, comparing final
state, `pre-inputs`, `post-inputs`, `complete-segment-p` and `state-equiv`. The page shows:
- the state and each step;
- a space–time diagram with the recording cut;
- the sort of `e` into pre-then-post, one adjacent swap at a time, with each swap checked by running both orders.

On 2,000 random segments (3,046 swaps), every swap commuted, every swapped order was legal, and every final state
was unchanged.

## 05 Linear III

**What `MAIN` says.** If the linear map T from V to W is injective, then dim V ≤ dim W, and T is surjective exactly
when dim V = dim W.

**Against the paper.** `MAIN` is the conjunction of the authors' `injection-dim-<=` and `injection-surjection-dim-=`
(`vectors.lisp:1135`, `:1152`, §4 p. 9). Both have the same hypothesis. The paper never states the two together;
the prompt combined them.

The axioms match the paper's one-to-one:
- the 16 field constraints;
- the 12 vector-space constraints;
- the 5 basis constraints;
- the 4 constraints on T.

The definitions:
- **`injective`** is the same as the paper's `lin-injective-p`: T(x) = 0 implies x = 0, for x in V.
  - This is the kernel form of injectivity. It is equivalent to "T(x) = T(y) implies x = y" for linear maps, by the
    standard argument.
  - The solution does not prove that equivalence; it uses the kernel form throughout, as the prompt and the paper do.
- **`surjective`** says every y in W has a preimage, written with a `defun-sk … exists`. The paper writes the same
  thing with a `defchoose` (`lin-preimage`).
- **`injective-necc`** is the theorem ACL2 generates from the `defun-sk`. It is the only way the proof uses
  injectivity.

**Non-vacuity.** `MAIN` was functionally instantiated on two concrete models:
- V = F, W = F×F, T(x) = (x, 0). T is injective, and `MAIN` then gives that T is not surjective.
- V = W = F, T the identity. T is injective, and `MAIN` then gives that T is surjective.

So both directions of the "exactly when" are exercised. Nothing executes in this solution, because every function
is generic, so there are no computation tests.

**Potential problems.**
1. **Low.** The model added `booleanp` constraints on the recognizers `fp`, `vp`, `wp` and `gp`, which the paper
   doesn't have. With all four removed, the solution still certifies, so the proof does not need them.
2. **Very low.** Linear combination recurses on the vectors rather than the coefficients. This matters only when
   the two lists have different lengths, which every axiom rules out.
3. **Very low.** The identity axioms are one-sided, which is equivalent given commutativity.

**Subspaces.** The solution has no theory of subspaces. This is out of scope, not a gap:
- the experiment-1 prompt doesn't mention subspaces;
- the paper's proofs of these two theorems don't use them (the subspace section starts at `vectors.lisp:1245`);
- experiment 2 tests the subspace results (`MAIN-4` to `MAIN-6`), and its solution proves them.

## 06 Fields

**What `MAIN` says.** If f is a field, then f satisfies the 16 field axioms. Here a field is Q, F_p (p prime),
the generic field F0, or a simple extension of a field by a monic irreducible polynomial of degree ≥ 2. The
axioms include x·x⁻¹ = 1 for nonzero x.

**Against the paper.** The 16 axioms match the paper's F0 constraints (`projects/linear/field.lisp`) and its
`field-axioms-p` (`extensions.lisp:831`) one-to-one.

The definitions of field, extension and reducible match the paper's (`extensions.lisp:493–527`):
- the same primality test;
- the same conditions on the extension polynomial;
- "reducible" means "some monic q with 0 < deg q < deg p divides p". The solution writes this with a `defun-sk`,
  the paper with a `defchoose`.

The polynomial representations differ:
- the solution lists coefficients constant-first and pads elements to exactly deg p coefficients;
- the paper lists them highest-first, with a nonzero leading coefficient.

I found no case where this changes the meaning.

**Tests and non-vacuity.** Concrete computations all gave the right answers:
- remainders and divisibility over F₂ and Q;
- √2·√2 = 2 and 1/(1+√2) = −1+√2 in Q(√2);
- a·(1+a) = 1 in F₄.

A certified book proves:
- x²+1 over F₂ is reducible, so that extension is not a field;
- F₄ = F₂[x]/(x²+x+1) is a field;
- α·α⁻¹ = 1 in F₄.

**Potential problems.**
1. **Moderate.** Extension multiplication is the solution's own step-by-step routine (`vapply`). It is not proved
   to equal "multiply as polynomials, then take the remainder mod p", which is how the paper defines it. `MAIN`
   proves the result is *a* field; it doesn't prove that the field is F[X]/p. Tests agree with hand calculation.
2. **Moderate, related.** Divisibility, and therefore irreducibility and `fieldp`, uses the same routine. A bug in
   it would affect both `fieldp` and multiplication, and neither would catch it.
3. **Low.** The solution doesn't prove that an extension contains f or a root of p. Neither the prompt nor this part
   of the paper asks for it.
4. **Low.** Non-vacuity was checked for one level of extension only.

**Suggested follow-up.** Prove that `vapply` equals multiplication followed by remainder mod p. That would close
items 1 and 2.

## How much the proofs rely on `:hints`

For each paper, I made a variant of the solution with as few `:hints` as I could get without changing the
formalization. Each variant keeps every result of the original with the same statement, and certifies with the
repo's checker.

| Paper | Hints before | Hints after | Changes besides removing hints | Proof time |
|---|---|---|---|---|
| 06 | 173 | 90 | some lemmas moved; 5 `:induction` rules added | 1.2 s → 2.1 s |
| 05 | 63 | 43 | 3 existing theory events moved | 0.46 s → 0.46 s |
| 04 | 21 | 15 | none | 0.21 s → 0.35 s |

How the hints were removed:
- **Unneeded hints:** many could be deleted outright: 43 in 06, 17 in 05 and 6 in 04.
- **06, ordering:** the file disables its own functions globally, then re-enables one in nearly every lemma. Moving
  those lemmas to where the functions are still enabled removed many hints.
- **06, induction rules:** ACL2 did not try induction on functions defined inside the large `mutual-recursion`.
  One `:induction` rule per function replaced many `:induct` hints.

The hints that remain fall into the same kinds in all three papers:
- **Quantifiers.** Every use of a `forall` needs a hint naming the instance, because ACL2 never fills one in by
  itself. Examples: `field-axioms` (06), `cl-inv` (04), `injective` and `surjective` (05).
- **Algebra by hand.** Identities derived from the field or vector-space axioms need specific instances of
  associativity and commutativity, and ACL2 won't find them.
- **Choosing an induction.** Some goals need a specific induction scheme, often a custom one.
- **Functional instantiation and specific lemma instances.** The 05 generic-space results are applied to V and W
  this way, and the main assembly steps in 04 and 05 apply earlier lemmas to specific values.

Removing these would need design changes: one predicate per axiom instead of a quantified invariant, an algebra
library, or different definitions. Each per-paper hints file explains this in detail.

## Things not checked

- Topologies beyond two processes and concurrent snapshots for 04.
- A two-level extension tower for 06.
- That `vapply` is polynomial multiplication mod p for 06 (item 1 above).
- Any experiment-2 solution beyond the subspace check for 05.

## Files in `reviews/`

| File | Contents |
|---|---|
| `04-binmonjil-chandy-lamport-exp1.md` | full 04 audit |
| `04-binmonjil-chandy-lamport-exp1-nonvac.lisp`, `-eval.lsp` | non-vacuity book and concrete run |
| `04-binmonjil-chandy-lamport-exp1-theorem-comparison.md` | paper's theorem vs `MAIN`, with diagrams |
| `04-binmonjil-chandy-lamport-exp1-commute.html` (+ `-viz-tools/`) | interactive model and commuting demo |
| `04-binmonjil-chandy-lamport-exp1-hints.md`, `-solution-no-hints.lisp` | hints analysis |
| `05-russinoff-linear3-exp1.md` | full 05 audit |
| `05-russinoff-linear3-exp1-nonvac.lisp` | non-vacuity book |
| `05-russinoff-linear3-exp1-hints.md`, `-solution-no-hints.lisp` | hints analysis |
| `06-russinoff-fields-exp1.md` | full 06 audit |
| `06-russinoff-fields-exp1-nonvac.lisp` | non-vacuity book |
| `06-russinoff-fields-exp1-hints.md`, `-solution-no-hints.lisp` | hints analysis |
| `hint-reduction-tools/` | scripts used for the hints analyses |
