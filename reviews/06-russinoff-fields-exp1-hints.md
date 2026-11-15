# 06-russinoff-fields, experiment 1: reducing `:hints`

Reviewer experiment on `06-russinoff-fields/exp1/solution.lisp`: how much of the proof depends on `:hints`?
The result is `06-russinoff-fields-exp1-solution-no-hints.lisp` in this folder.

## Result

| | Original | No-hints variant |
|---|---|---|
| `:hints` | 173 | **90** |
| Events | 249 | 254 (all 249 kept, plus 5 added) |
| Global `in-theory` events | 17 | 17 |
| Proof time (ACL2 8.7) | 1.2 s | 2.1 s |
| `tools/check-exp1.sh` | CERTIFIED | CERTIFIED |

- **Same results.** Every event of the original is kept with the same statement and rule classes, checked by
  `hint-reduction-tools/compare.py` (which strips hints and compares the remaining forms). `MAIN` is unchanged and still
  the last event.
- **Additions:** `natind`, plus five `:induction` rules (`vzero-induction`, `vadd-induction`, `vneg-induction`,
  `vscale-induction`, `vapply-induction`). Each rule has the trivial statement `t`; it only tells ACL2 which induction
  to use. None of them adds a logical assumption.
- **Moves:** the opener lemmas `vzero-opener` … `vapply-atom` now come before the first global `disable`. The `ext-*`
  lemmas sit in the existing region where `fep`, `fadd`, … are enabled. `(disable field-axioms)` now comes after
  `field-axioms-fp`.
- Of the 90 remaining hints, many are smaller than before: 39 hint parts and 12 `:use` instances were removed.

## Method

Everything was checked by certifying in the `acl2:latest` image (`Dockerfile.base`, ACL2 8.7). The scripts are in
`hint-reduction-tools/`.

1. **Unneeded hints.** For each of the 173 hints, I certified a copy with only that hint removed. A hint affects only
   its own proof, not the logical world, so all individually removable hints can be removed together. 43 were
   removable, and removing all 43 together certified.
2. **Opener lemmas moved before the global `disable` (12 hints).** The original disables its vector functions
   (line 199) and then proves 12 opener lemmas, each with `:in-theory (enable <that function>)`. Proving them before the
   `disable` needs no hints.
3. **Induction rules (18 hints).** `vzero`, `vadd`, `vneg`, `vscale` and `vapply` belong to the large `mutual-recursion`
   with `fep`, `fadd`, … . Without hints, ACL2 did not induct on them at all. For example, `len-vzero` failed at the top
   level without trying induction. The model therefore wrote `:induct (ind1 x)` and similar many times. One
   `:induction` rule per function states the scheme once, and with these rules 18 more hints became removable.
4. **Lemmas moved to where the theory is already right (10 hints).** The 7 `ext-*` lemmas each enabled one field
   function, and they now sit in the region where those are enabled. `field-axioms-q/f0/fp` each enabled
   `field-axioms`, and the `disable` now comes after them.
5. **Smaller hints.** For each remaining hint I tried dropping each part (`:in-theory`, `:induct`, `:expand`, `:use`, …)
   and each instance in multi-instance `:use` lists. 39 parts and 12 instances were removable, and removing all of them
   together certified.
6. **Final check.** No whole hint in the final file can be removed on its own. Of the added rules,
   `vecp-induction` was not needed and was dropped.

Tried without success: opener rules for `last1`/`butlast1` meant to replace 8 `:expand` hints. Left enabled, they
break `inv-step-key`. Disabled right after their block, they certify but don't make any hint removable.

## Why the remaining 90 stay

None of the remaining hints could be removed without changing the formalization's design. Grouped by reason:

### 1. Using the quantified `field-axioms` (18 hints): inherent to the design

`field-axioms` is a `defun-sk` saying "for all x, y, z, `axioms-body`". The proof of `fieldp-field-axioms` needs this
quantified form: the induction hypothesis for the base field `b` must cover all elements of `b`. ACL2 never instantiates
a `forall` on its own; the instance has to come from `:use field-axioms-necc`. This covers the 16 `b-*` lemmas
(`b-fep-zero` … `b-mul-inv`), plus `axioms-body-ext` and `field-axioms-ext`.

**Way to remove them:** state the axioms the way the paper does, with one `defun-sk` per axiom (`fadd-comm-p`, …;
`authors-books/extensions.lisp:688–847`) and `:rewrite :direct`. Each axiom's instance then becomes an ordinary rewrite
rule usable without hints, and the 16 `b-*` lemmas need no proof hints. This replaces `field-axioms`/`axioms-body` with
16 definitions and changes every proof that opens them (`axioms-body-q/f0/fp/ext`, `field-axioms-ext`, `MAIN`'s
derivation). That is a significant change to the theory, so it was not done.

### 2. Deriving field algebra by hand (14 hints): would need an algebra library

Lemmas `b-add-comm2` … `b-mul-inv-cancel` and `b-add-self` derive identities such as −(−x) = x or x·0 = 0 from the
axioms of an *arbitrary* field `b`. Each needs specific instances of associativity, commutativity or uniqueness of
negation. ACL2's rewriter won't choose those instances itself: making associativity or commutativity a general
rewrite rule either loops or points the wrong way for these goals.

**Way to remove them:** a normalizing algebra library for abstract fields, such as ordered rewriting with
`:loop-stopper`, or a meta-rule that normalizes sums and products. That is a large addition, not a cleanup.

### 3. Choosing between competing inductions (17 hints): limited by ACL2's heuristics

Examples: `vapply-vadd-right`, `vapply-vzero-right`, `vapply-commute`, `vadd-vzero`, `len-vapply`, `vecp-is-polyp`,
`pmod-division`, `vneg-unique`. These goals contain several recursive functions, and ACL2 chooses the wrong one to
induct on. For example, without its hint `vapply-vadd-right` inducts on `v`/`w` (from `vadd`) instead of on `a`, and
fails. An `:induction` rule adds schemes but can't overrule ACL2's choice between them.

**Way to remove them:** change argument order or definitions so the intended scheme wins, for example by defining
`vapply` by recursion on the vector argument. This changes definitions the rest of the proof relies on.

### 4. Opening a term at one specific place (`:expand`, 13 hints)

Examples: `butlast1-vadd`, `last1-vadd` (and the `vneg`/`vscale`/`vzero` versions), `len-trim-pos`,
`inv-search-opener`, `vapply-vtimesx-left`. Each must open `last1`, `butlast1`, `trim` or `inv-search` on a variable or
on one specific term, which ACL2 doesn't do by default. General opener rules were tried (see Method) and either break
later proofs or don't help.

### 5. Local theory changes (16 hints)

Examples: `polyp-trim`, `polyp-pmod`, `pmod-cons`, `pmod-atom`, `vshift-vzero`, `consp-vtimesx`, `vtimesx-atom`,
`vtimesx-last-zero`, `vapply-vone-left`, `vscale-vone`, `pad-trim`, `last1-trim-nonzero`, `vzerop-means-vzero`,
`vzerop-vzero`, `vadd-self-cancel`, `vzero-not-vone`. Each enables one definition that the file disables globally (`pmod`, `trim`,
`vone`, `vtimesx-def`, `vzero-opener`, …). Each could be moved into an `in-theory` region like steps 2 and 4, but these
lemmas are spread out, so that would mean adding an enable/disable pair per lemma. That moves the hint into a
global event without reducing reliance on it, so it was not done.

### 6. Inverse correctness (16 hints): the hardest proof in the file

`finv` (measure), `inv-step-key0`, `inv-step-key`, `irreducible-pmod-nonzero`, `inv-base-case`, `inv-case-const`,
`inv-step-props`, `inv-search-correct-0`, `ext-inverse` (9 hints), plus 7 `:use` hints on the supporting algebra lemmas `vapply-comm-vec`,
`vapply-assoc`, `vapply-modulus-step`, `vapply-modulus`, `vapply-vtimesx-left+`, `vtimesx-vapply-pmod` and
`vneg-equal-vzero`. These
supply the invariant of the inverse search, the instance of `reducible-suff` that turns "no factor" into "remainder
nonzero", and the instances of the division lemma. These are real proof ideas, not theory settings. Removing them
would require a different, more automatic proof of the inverse, such as the paper's extended-Euclid formulation
(`r$`, `s$`).

## Caveats

- **Remaining-hint counts are approximate.** The six groups above add up to more than 90, because some lemmas fit two
  groups.
- **Rest of the theory untested.** "Not removable" means "not removable without restructuring". Each step was
  verified only by certifying with ACL2 8.7 in this image, and other combinations of moves and rules may do better.
- **Slower proofs.** Proof time rose from 1.2 s to 2.1 s, as ACL2 now searches where hints used to direct it.

## Files

- `06-russinoff-fields-exp1-solution-no-hints.lisp`: the variant. To check it, copy it to `solution.lisp` or pass it to
  `tools/check-exp1.sh`.
- `hint-reduction-tools/`:
  - `hints.py`: finds and removes hints, hint parts and `:use` instances, and generates variants.
  - `phase.sh` and `runone.sh`: certify all variants in parallel in the `acl2-review` container.
  - `compare.py`: checks that statements are unchanged.
