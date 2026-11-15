# Review: 06-russinoff-fields, experiment 1

Reviewer audit of `06-russinoff-fields/exp1/solution.lisp` against the prompt (`exp1/prompt.txt`) and the
paper's own books (`source/authors-books/extensions.lisp`, and `projects/linear/field.lisp` in the community books).

**Verdict:** no problem found that makes `MAIN` wrong or vacuous. The statement matches the prompt and the
paper's notion of field. Main caveat: extension multiplication (and with it divisibility) is the solution's own
routine, checked by tests but not proved to be "multiply, then take the remainder mod p" (items 1–2).

## Reproduction

- Image: `Dockerfile.base` (SBCL 2.6.1, ACL2 at commit `bc6f4f49e81a0711214a8d91f0d06e0e084d2204`, tag 8.7).
- Setup: `make build/Makefile-features` in `books/`, then certify `kestrel/prime-fields/prime-fields` and
`kestrel/prime-fields/prime-fields-rules`.
- `tools/check-exp1.sh` (ACL2 path changed from `/opt/acl2` to `/root/acl2`): no banned events, last event is
`(defthm MAIN …)`, `CERTIFIED with saved_acl2`. Proof time 1.2 s.
- `solution.cert`: the two "ttag" matches are the certificate's field names (`TTAGS`, `SKIPPED-PROOFSP`).



## Checks

1. **Soundness.** No `skip-proofs`, `defaxiom`, trust tags, `defattach`, `:program` mode or redefinition. The only
  `local` events are the F0 witness functions and one included book.
2. **Axiom list.** `MAIN` (`solution.lisp:1515`) states the same 16 axioms as the paper's F0 constraints
  (`projects/linear/field.lisp`) and its `field-axioms-p` (`authors-books/extensions.lisp:831`), one-to-one.
3. **Definitions against the paper** (`extensions.lisp:493–527`):
  - Base fields `(:q)`, `(:fp p)`, `(:f0)` vs the paper's `0`, `p`, `'f0`. Same primality test (`dm::primep`);
   same F_p element set.
  - Extensions: both require a base that is a field, p a polynomial over it, monic, irreducible, deg p ≥ 2.
  - Reducible: both say "some monic q with 0 < deg q < deg p divides p" (`defun-sk` vs the paper's
  `defchoose` plus a check; logically the same).
  - Theorem shape: paper `(implies (fieldp f) (field-axioms-p f))`; `MAIN` is the same.
4. **Computation tests** (all correct): x²+1 mod x+1 over F₂ = 0; x+1 | x²+1 over F₂; x+1 ∤ x²+x+1 and
  x ∤ x²+x+1 over F₂; x³+5 mod x²−2 over Q = 5+2x; √2·√2 = 2 and 1/(1+√2) = −1+√2 in Q(√2);
   a·(1+a) = 1 in F₄.
5. **Non-vacuity** (`06-russinoff-fields-exp1-nonvac.lisp`, certified on top of `solution.lisp`):
  - `(not (fieldp '(:ext (:fp 2) (1 0 1))))`: x²+1 is reducible over F₂, so not a field.
  - `(fieldp '(:ext (:fp 2) (1 1 1)))`: F₄ is a field.
  - α·α⁻¹ = 1 in F₄.



## Potential problems (most important first)

1. **Moderate. Extension multiplication is not proved to be polynomial multiplication mod p.** The paper defines
  it as `prem(pmul x y, p)`. The solution's `vapply` (`solution.lisp:177–195`) multiplies by X and reduces at each
   step (Horner). `MAIN` proves the result is *a* field, but nothing proves it is F[X]/p. Tests agree with hand
   calculation. Addition, element set, zero, one, negation and inverse don't have this gap: the first two are right
   by inspection and the axioms then force the rest.
2. **Moderate, related. Divisibility uses the same routine.** `pmod` is `vapply(a, 1)` (`solution.lisp:309`), so
  `pdivides`, `reducible` and `fieldp` depend on it too. A bug there would change which polynomials count as
   irreducible, and `fieldp` and `fmul` could not catch each other. The paper's `prem` is independent long
   division. Tests and the non-vacuity proofs show it behaves correctly where it matters.
3. **Low. Different polynomial representation.** Paper: highest coefficient first, nonzero leading coefficient.
  Solution: constant term first, elements padded to exactly deg p coefficients, `polyp` allows trailing zeros.
   Still one-to-one; `monicp` requires the last coefficient to be 1, which rules out trailing zeros where it
   matters. No change of meaning found.
4. **Very low. Q operations apply** `rfix` (paper uses raw `+`, `*`). Affects only non-elements; no effect on `MAIN`.
5. **Low. No proof that the extension contains f or a root of p.** Neither prompt nor this part of the paper asks
  for it (the paper defers `flift` and roots to later books), so this is consistent, but only the field axioms
   are checked, not the "extension" part.
6. **Low. Non-vacuity checked for one level only.** No two-level tower example was certified.
7. **Notes, no action.** Identity and distributive axioms are one-sided (equivalent given commutativity, and
  identical to the paper's constraints). `fieldp` requires exact list shapes. The F0 witness model is the
   rationals (only shows consistency).



## Suggested follow-up

Prove in ACL2 that `vapply` equals multiplying as polynomials and then taking the remainder mod p. This would
close items 1 and 2.