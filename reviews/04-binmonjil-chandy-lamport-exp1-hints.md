# 04-binmonjil-chandy-lamport, experiment 1: reducing `:hints`

The same experiment as `06-russinoff-fields-exp1-hints.md`, run on `04-binmonjil-chandy-lamport/exp1/solution.lisp`.
The result is `04-binmonjil-chandy-lamport-exp1-solution-no-hints.lisp` in this folder.

## Result

| | Original | No-hints variant |
|---|---|---|
| `:hints` | 21 | **15** |
| Events | 107 | 107 (identical, same order) |
| Global `in-theory` events | 5 | 5 |
| Proof time (ACL2 8.7) | 0.21 s | 0.35 s |
| `tools/check-exp1.sh` | CERTIFIED | CERTIFIED |

- **Only hints changed.** Every event keeps its statement, rule classes and position, checked by
  `hint-reduction-tools/compare.py`. `MAIN` is unchanged and still the last event. Unlike 06, nothing was added or
  moved.
- **Hints removed:** `g-pop-chans`, `ps-of-step`, `chan-of-step`, `newly-recorded-sends-marker`, `marker-retained`
  and `recorded-before-run` no longer need any hint.
- **Hints made smaller:** 11 of the 15 remaining hints lost parts. 13 hint parts and 4 `:use` instances were removed
  (table below).

The solution was already sparing with hints: 21 for 60 theorems, where 06 had 173 for about 230.

## Method

The same scripts as for 06 (`hint-reduction-tools/`), certifying in the `acl2:latest` image (ACL2 8.7):

1. **Whole hints.** For each of the 21 hints, I certified a copy with only that hint removed. 6 were removable, and
   removing all 6 together certified.
2. **Hint parts.** For each remaining hint, I tried dropping each part (`:in-theory`, `:induct`, `:expand`,
   `:do-not-induct`, `:use`, `:cases`). 13 parts were removable on their own, and removing all 13 together certified.
3. **`:use` instances.** In multi-instance `:use` lists, 5 instances were removable on their own. Of the four in
   `ne-cond-before`, only three can be dropped together. Kept: 4 removals.
4. **Final check.** No whole hint in the final file can be removed on its own.

Nothing was restructured. The 06 restructurings (moving lemmas before a global `disable`, adding `:induction`
rules) have no counterpart here, for the reasons below.

## The remaining 15 hints, before and after

| Theorem | Original hint | Now |
|---|---|---|
| `g-deliver` | `:induct (deliver p ob c)` + `(enable g-of-s-redux)` | `:induct` only |
| `cl-inv-step-point` | `(disable …)` + 3 `:use` instances | 3 `:use` instances |
| `cl-inv-step` | `:expand` + `(disable …)` + `:use` | `:expand` + `:use` |
| `sids-init-pstates` | `(enable g-of-s-redux)` | unchanged |
| `cl-inv-init` | `(enable cl-inv sids-of ps-of)` | unchanged |
| `chans-commute` | `(e/d (chan-of) (g-chans-step))` + functional instance of `equal-by-g` + computed hint | functional instance + computed hint |
| `g-step-commute` | `(disable …)` + `:cases` on `k` | `:cases` only |
| `step-commute` | `(disable ne-cond)` + functional instance of `equal-by-g` | functional instance only |
| `chan-run-unchanged` | `:induct (cl-run u qs)` + `(enable outs-of)` | `(enable outs-of)` only |
| `ne-cond-before` | `(disable …)` + `:do-not-induct` + 5 `:use` instances | 2 `:use` instances |
| `commute-past-post` | `:induct` + `(disable ne-cond)`; subgoal `:use` of 3 instances | `:induct`; subgoal `:use` of 2 |
| `reorder-general` | `:induct (reorder-ind …)` + `(disable legal-input ne-cond)` | `:induct` only |
| `reorder-from-state` | `(disable reorder-general)` + `:use` | `:use` only |
| `cl-inv-reachable` | `(disable init-state (:e init-state))` | unchanged |
| `main` | `(disable …` 8 names`)` + `:use` of 2 lemmas | `:use` only |

## Why the remaining 15 stay

### 1. Using the quantified invariant `cl-inv` (4 hints): inherent to the design

`cl-inv` is a `defun-sk`: for every sid, q and p, if q has recorded sid, p hasn't, and p is an outgoing neighbour of
q, then sid's marker is in the channel from q to p. As with `field-axioms` in 06, ACL2 never instantiates a `forall`
itself, so each use needs `:use cl-inv-necc` with chosen instances (`cl-inv-step-point`, `ne-cond-before`).
Proving `cl-inv` needs the skolem witness opened (`cl-inv-step`: `:expand` plus `:use` with the
`cl-inv-witness` components; `cl-inv-init`: enable `cl-inv`).

**Way to remove them:** replace the quantified invariant with a recursive checker over the finite process and sid
lists. That would change the main invariant of the proof.

### 2. Equality of records via `equal-by-g` (2 hints): the standard records technique

`step-commute` and `chans-commute` prove that two `misc/records` records are equal by showing every field is equal.
The `misc/equal-by-g` book provides this only as a constrained theorem, used via `:functional-instance`. There is no
rule that applies on its own. `chans-commute` also keeps a computed hint that enables `chan-of` once the goal is
stable.

**Way to remove them:** a pointwise-equality rewrite rule for these specific records. That's possible, but it
would be a rule written specifically for these two proofs, which is the same reliance in another form.

### 3. Choosing an induction (3 hints)

- `g-deliver`: `deliver` recurses with an accumulator `c` that changes; the hint picks `deliver`'s own scheme.
- `commute-past-post`: induction on `(cl-run u qs)` while the goal also mentions `x`.
- `reorder-general`: a custom scheme `reorder-ind` (defined in the solution for this proof), which does the
  real work of the reordering.

An `:induction` rule (as used in 06) would only move each of these into a separate event one-for-one, so it wouldn't
reduce reliance.

### 4. A case split (1 hint)

`g-step-commute` splits on whether the field `k` is `:pstates`, `:chans` or something else. ACL2 doesn't do this
split by itself.

### 5. Applying a lemma ACL2 won't apply by itself (2 hints)

- `reorder-from-state` is `reorder-general` with `qs` = nil. Once `qs` is nil, `(append qs …)` and
  `(cl-run u nil)` simplify, so the rule's pattern no longer appears in the goal (confirmed by the failure
  checkpoint).
- `main` uses `reorder-from-state` with `sid` = `(segment-target st e)` and `cl-inv-reachable`. Without the hint,
  ACL2 first opens `init-state`, `complete-segment-p` and `cl-run`, and the rules no longer match (confirmed by the
  failure checkpoint).

These are short, deliberate final steps of the proof.

### 6. Theory settings (3 hints)

- `sids-init-pstates` enables `g-of-s-redux`, which `misc/records` disables by default because it causes case
  splits.
- `chan-run-unchanged` enables `outs-of`, which the file disables globally at line 459.
- `cl-inv-reachable` disables `init-state` so that the induction hypothesis matches.

Each setting is needed by exactly one theorem. Moving it into a global theory event would only relocate the hint,
so it was not done (the same rule as group 5 in the 06 write-up).

## Caveats

- **Rest of the theory untested.** "Not removable" means "not removable by the method above". The proof was not
  restructured, and other combinations may do better.
- **Slower proofs.** Proof time rose from 0.21 s to 0.35 s, as ACL2 now searches where the removed `disable`s
  directed it.
- **Computed hint untested.** The scripts don't try removing the computed hint in `chans-commute` (the
  `stable-under-simplificationp` form), only keyword parts.
