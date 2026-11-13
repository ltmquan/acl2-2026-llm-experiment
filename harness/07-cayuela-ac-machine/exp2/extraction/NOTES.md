# Given package: cayuela-ac-machine

Paper: P. O. Cayuela, "Mechanized Verification of Complex-to-Vector Derivations in a
Three-Phase AC Machine Model" (ACL2 Workshop 2026).
Authors' books: `reference-books/workshop-2026/cayuela-ac-machine/`.

**Logic: ACL2(r)** (`/opt/acl2r/saved_acl2r`, ACL2 8.7). All four targets are in one session/world.

## Targets (`targets.lisp`)
| Target | Authors' name | Location | Meaning |
|---|---|---|---|
| MAIN-1 | `eq33-35-collapse-concrete` | 09-nonvacuity-acl2r.lisp:38 | three-phase collapse lemma, with s3 = `(acl2-sqrt 3)` |
| MAIN-2 | `eq-im-w-is-crossp` (= `torque-exponent-sign-is-plus`, 05:53) | 05-torque-sign-correction.lisp:44 | Im(i_S i_R* e^{-j eps}) = i_S x (i_R e^{+j eps}) |
| MAIN-3 | `trinary-collapse-lemma` | 06-generic-omega-collapse-acl2r.lisp:108 | collapse lemma for any real pair omega with 1+omega+omega^2=0 |
| MAIN-4 | `trinary-collapse-CONCRETE` | 06-generic-omega-collapse-acl2r.lisp:184 | collapse lemma for omega = e^{j 2pi/3}, unconditional |

MAIN-2 is stated over the authors' encapsulated `cosine`/`sine` (book 01). This encapsulate
and `eiz` admit under ACL2(r) without change; book 09 itself loads them under ACL2(r).

## defs.lisp
167 lines, 6624 bytes. Includes `arithmetic-5/top` and `nonstd/nsa/trig` (8.7 community books).
- Part A (verbatim from 00, 01, 02, 05): `cplxp cplx re imz cconj cadd cscale cmul dotp crossp`,
  the `cosine`/`sine` encapsulate (with its 7 constraint theorems, which are part of the
  definition), `eiz`, `e0 e1 e2`, `torque-W`.
- Part B (from 06-generic-omega-collapse-acl2r.lisp, renamed): `g-cplxp g-re g-im g-cplx
  g-realpairp g-c+ g-cscale g-c* g-vdot g-omega-pow g-collapse-sum g-gamma-val g-omega-real`.
- No skip-proofs, defaxiom or ttags. The only lemma is `g-cplxp-of-g-omega-pow` (the authors'
  `cplxp-of-omega-pow`). It is `local` and is needed for the authors' `(verify-guards omega-pow)`.

## Deviations from the authors' text
1. **Renaming of Part B (prefix `G-`).** Book 06-acl2r re-declares `cplxp`, `re`, `cplx` and
   `cscale` with bodies different from book 00, so the two cannot coexist. A function
   such as `c+`, `c*`, `vdot`, `realpairp`, `omega-pow`, `collapse-sum` or `omega-real` would also
   change its body in a joint world, because its body calls a renamed function. To keep one
   consistent prefix, and so that V3 can define the given functions next to the authors'
   originals, every 06 function used by the targets is renamed:
   `cplxp->g-cplxp, re->g-re, im->g-im, cplx->g-cplx, realpairp->g-realpairp, c+->g-c+,
   cscale->g-cscale, c*->g-c*, vdot->g-vdot, omega-pow->g-omega-pow,
   collapse-sum->g-collapse-sum, gamma-val->g-gamma-val, omega-real->g-omega-real`,
   plus the lemma `cplxp-of-omega-pow->g-cplxp-of-g-omega-pow`. Apart from this renaming
   the bodies, guards and declarations are verbatim. `c-` is unused by the targets and is
   omitted. MAIN-3 and MAIN-4 use the renamed names.
2. **`g-gamma-val` is written neutrally** as `(* 2/3 (acl2-pi))` rather than the authors'
   `(+ (* 1/3 (acl2-pi)) (* 1/3 (acl2-pi)))`. The authors' form hints at the cosine-of-sums
   route. The value is equal, and V3 proves `(equal (g-gamma-val) (gamma-val))`.
3. The 06 lemma `cplxp-of-omega-pow` is made `local` (admission scaffolding only).
4. Comments are shortened. Book 06's header comment, which describes the proof route, is dropped.

## Verification (all on 8.7 ACL2(r), `/opt/acl2r/saved_acl2r`, cert.pl from `/opt/acl2/books/build`)
- **V1 — PASS.** defs.lisp certifies (`verify/V1-defs.cert.out`).
- **V2 — PASS.** `verify/test-targets.lisp` includes "defs" and admits MAIN-1..4 under skip-proofs.
  It certifies (`verify/V2-test-targets.cert.out`).
- **V3 — PASS.** All 14 of the authors' books, including all three top books, certify under
  8.7 ACL2(r).
  - `verify/v3-main12.lisp` includes the authors' `09-nonvacuity-acl2r` (and hence 00–05), then
    `(include-book "defs")`. This succeeds only if every Part-A event in defs.lisp, including
    the encapsulate, is redundant with, i.e. identical to, the authors' event. MAIN-1 and
    MAIN-2 are then proved by `:use eq33-35-collapse-concrete` / `:use eq-im-w-is-crossp`
    with `:in-theory nil`. Certified.
  - `verify/v3-main34.lisp` includes the authors' `06-generic-omega-collapse-acl2r` and then
    embeds Part B of defs.lisp verbatim (checked by `verify/gen-v3-main34.py`: VERBATIM). It proves
    each `g-f` equal to the authors' `f` (`g-omega-pow` by induction, `g-gamma-val` by
    arithmetic). MAIN-3 and MAIN-4 are then proved from `trinary-collapse-lemma` /
    `trinary-collapse-CONCRETE`. Certified.
  - `verify/compare-defs.py` compares the definitions token by token. All are identical
    (Part B modulo the `G-` prefix), except `g-gamma-val`, as intended (`verify/compare-defs.log`).
- **check-exp2.py:**
  - `verify/test-targets.lisp` is rejected with BANNED: skip-proofs, as expected.
  - `verify/test-solution.lisp` is accepted with "CERTIFIED with saved_acl2r; targets matched:
    main-1, main-2, main-3, main-4". It is a real-proof solution that includes "defs", with
    the authors' hints ported (`verify/check-exp2-test-solution.log`).
