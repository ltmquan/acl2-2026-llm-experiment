# 05-russinoff-linear3, experiment 1: reducing `:hints`

The same experiment as `06-russinoff-fields-exp1-hints.md` and `04-binmonjil-chandy-lamport-exp1-hints.md`, run on
`05-russinoff-linear3/exp1/solution.lisp`. The result is `05-russinoff-linear3-exp1-solution-no-hints.lisp` in this
folder.

## Result

| | Original | No-hints variant |
|---|---|---|
| `:hints` | 63 | **43** |
| Events | 169 | 169 |
| Top-level `in-theory` events | 7 | 4 (3 moved into an `encapsulate`) |
| Proof time (ACL2 8.7) | 0.46 s | 0.46 s |
| `tools/check-exp1.sh` | CERTIFIED | CERTIFIED |

- **Same statements.** With hints and `in-theory` events removed at every level, the two files are identical (169
  forms, same order). `MAIN` is unchanged and still the last event.
- **Only change besides hints:** each of the three `(in-theory (disable (:executable-counterpart glc/vlc/wlc) …))`
  events now sits inside its `encapsulate`, just before `glc-gcoord`, `vlc-vcoord` and `wlc-wcoord`, instead of just
  after the `encapsulate`. Nothing was added.
- **Smaller hints:** many of the 43 remaining hints are smaller than before. 20 hint parts and 15 `:use` instances
  were removed.

## Method

The same scripts as for 06 and 04 (`hint-reduction-tools/`), certifying in the `acl2:latest` image (ACL2 8.7):

1. **Whole hints.** For each of the 63 hints, I certified a copy with only that hint removed. 17 were removable, and
   removing all 17 together certified.
2. **Hint parts.** For each remaining hint, I tried dropping each part (`:in-theory`, `:induct`, `:expand`, `:use`,
   `:cases`, …). 20 parts were removable on their own, and removing all 20 together certified. One goal spec left
   empty (`("Subgoal 1")` in `part3-core`) was deleted.
3. **`:use` instances.** In multi-instance `:use` lists, 15 instances were removable on their own, and removing all
   15 together certified.
4. **Moving existing theory events (3 hints).** `glc-gcoord`, `vlc-vcoord` and `wlc-wcoord` each disabled the
   executable counterpart of `glc`, `vlc` or `wlc`. The file already disables these globally right after each
   `encapsulate`. Moving that existing event to just before the theorem made the hint unnecessary.
5. **Final check.** After step 4, no whole hint and no hint part can be removed on its own.

Tried without success: `f*-finv` enables `f*` and `ffix`, which are disabled globally at lines 65 and 108. Moving the
theorem above those `disable`s proves it without a hint. But it then becomes an earlier rewrite rule, and the later
`f*-finv-2` fails: ACL2 tries newer rules first, so changing where a rule appears can break later proofs. So it was
left in place.

## Why the remaining 43 stay

### 1. Field and group algebra by hand (17 hints): would need an algebra library

`f+-comm-2`, `f*-comm-2`, `f+-cancel-lemma`, `f+-x-x-means-0`, `f*-f0-1`, `f+-zero-means-neg`, `f*-f--1`,
`f*-finv-2`, `f*-finv-3`, `gadd-zero-means-neg`, `gadd-idem-means-zero`, `gmul-f0`, `gmul-g0`, `gmul-fneg`,
`g-solve-1`, `g-solve`, `gadd-4`.

These derive identities from the axioms of an abstract field F and an abstract vector space G, such as 0·x = 0 and
(−c)·x = −(c·x). Each needs specific instances of associativity, commutativity or cancellation. This is the same
situation as group 2 of the 06 write-up: ACL2's rewriter won't choose these instances, and making
associativity/commutativity into general rules loops.

### 2. Choosing an induction (7 hints)

- `remove-nth-fv+`, `nth-fv+` (`ind-juvn`) and `remove-nth-zeros`, `nth-zeros`, `zeros-from-nth-and-remove`
  (`ind-jun`): custom schemes that recurse on an index and one or two lists at once. Here `nth`, `remove-nth`, `fv+`
  and `zeros` suggest different inductions, and none of them is the combined one needed.
- `fdep-nontrivial`, `fdep-lincomb-zero`: induction on `fdep`, the Gaussian-elimination function. Without the hint
  ACL2 fails at the top level without inducting on `fdep`.

An `:induction` rule per pattern would only move each hint into its own event, so it doesn't reduce reliance.

### 3. Instantiating the generic space (5 hints): inherent to the design

`vdep-correct`, `wdep-correct`, `wmul-f0`, `wmul-w0` and `w-solve` obtain results for V and W by
`:functional-instance` of the results proved once for the generic space G. Functional instantiation always
needs a hint. This mirrors the paper, which also proves results generically and instantiates them.

### 4. Quantifiers (3 hints): inherent to the design

`injective`, `preimage` and `surjective` are `defun-sk`s. `t-basis-indep` and `surj-witness-props` need instances of
`injective-necc` and `surjective-necc`, and `inj-eqdim-surj` instantiates with `(surjective-witness)`. ACL2 does
not instantiate quantifiers by itself.

### 5. Assembling the main results (8 hints)

`flc-elim-zero-a`, `flc-elim-zero`, `gdep-correct`, `inj-dim-le`, `surj-dim-le`, `part3-core` (a case split on the
first coefficient, and an instance of `w-solve` and `preimage-suff`), `inj-eqdim-preimage` and `main`. Each applies
specific earlier lemmas, typically `wdep-correct` or `vdep-correct` (from 3) applied to a specific list of
vectors. These are the real steps of the dimension argument. ACL2 won't find them itself, because the lemmas'
variables (which vectors, which coefficient) don't appear in the goal.

### 6. Theory settings (3 hints)

`f*-finv`, `glc-fv*` and `glc-fv+` enable `f*`/`f+` and `ffix`, which the file disables globally. Moving
`f*-finv` was tried and broke a later proof (see Method). `glc-fv*` and `glc-fv+` depend on `glc`, which is
defined long after the `disable`s, so they can't be moved before them.

## Caveats

- **Rest of the theory untested.** "Not removable" means "not removable by the method above". Other moves or rules
  may do better.
- **`in-theory` inside an `encapsulate`.** The moved events still take effect after the `encapsulate`: after
  including the variant, `(disabledp 'glc)`, `'vlc` and `'wlc` each report the executable counterpart disabled, as
  in the original.
