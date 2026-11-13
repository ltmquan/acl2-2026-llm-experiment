# Given package: russinoff-linear3 (Russinoff, "A Formalization of Elementary Linear Algebra: Part III")

Logic: **acl2** (ACL2 8.7, `/opt/acl2/saved_acl2`). Package: **"DM"** (the authors' package).

## Files
- `defs.lisp`: 1428 lines, 48,739 bytes, 142 top-level forms. 348 lines are exported definitions and
  in-theory events. 792 lines are LOCAL proof support (89 local events). The rest is comments
  and source-location markers.
- `cert.acl2`: `(include-book "projects/numbers/portcullis" :dir :system)`. It defines the DM package, the
  same defpkg that the Part I–II books carry in their portcullis. `check-exp2.py` copies it next to the solution.
- `targets.lisp`: MAIN-1 … MAIN-6 (package DM), no hints.
- `verify/`: scripts and logs (see below).

## Targets
| target | authors' theorem(s) (master `books/projects/linear/vectors.lisp`) | meaning |
|---|---|---|
| MAIN-1 | `injection-dim-<=` (l.1135) ∧ `injection-surjection-dim-=` (l.1152) | if lin is injective, dim V ≤ dim W, and lin is surjective iff dim V = dim W |
| MAIN-2 | `lin-lin-inv` (l.1235) | for bijective lin, the constructive matrix inverse `lin-inv` is a right inverse |
| MAIN-3 | `vbasisp-extend-to-basis` (l.625) | `extend-to-basis` extends a nonempty independent list to a basis |
| MAIN-4 | `sdim-well-defined` (l.1426) | subspace dimension is well defined: `(= (sdim1) (sdim))` |
| MAIN-5 | `klistnp-kbasis` (1608) ∧ `vindepp-kbasis` (1670) ∧ `flistnp-kcoords` (1688) ∧ `kbasis-spans` (1710) | `kbasis` is a basis of the kernel of lin, with coordinates `kcoords` |
| MAIN-6 | `ilistnp-ibasis` (1800) ∧ `ibasis-lin-indep` (1823) ∧ `flistnp-icoords` (1831) ∧ `ibasis-spans` (1866) | `ibasis` is a basis of the image of lin (length idim = vdim − kdim), with coordinates `icoords` |

**Decision on survey item 5.** I split the kernel/image basis facts into two targets, MAIN-5 (kernel) and
MAIN-6 (image), each a conjunction of its four facts. The two halves have different constructions and
proofs, and the image proof builds on the kernel one, so the split shows partial success. MAIN-6 is
therefore the survey's "MAIN-5, image half". The survey's secondary MAIN-6 (vdepp-vcomb-v0) is **not**
a target. Every statement is the authors' text, with the authors' constructive functions (`lin-inv`,
`extend-to-basis`, `kbasis`, `kcoords`, `ibasis`, `icoords`) kept.

## Contents of defs.lisp
- `(include-book "projects/linear/reduction" :dir :system)` gives Parts I–II from the 8.7 tree.
- These authors' forms are copied verbatim from master `vectors.lisp`, in the authors' order:
  - the V encapsulate; `vcoord-mat`, `vindepp`, `vdepp`, `vdep-coeffs`, `vcoords`, `vbasisp`, `vunspanned`, `extend-to-basis`;
  - the W encapsulate (in full); `wcoord-mat`, `windepp`;
  - the lin encapsulate; `lin-list`, `lin-mat`, `lin-injective-p`, `lin-preimage`, `lin-surjective-p`, `lin-inv`;
  - the sp encapsulate; `slistnp`, `sunspanned`, `sbasis0-aux` (with the authors' measure and hints), `sbasis0`, `sdim`, `scoords0`;
  - the `sbasis1`/`scoords1`/`sdim1` encapsulate (with the authors' hints);
  - `in-kernel-p`, `klistnp`, `kbasis-coord`, `kbasis-coords-aux`, `kbasis-coords`, `kbasis-aux`, `kbasis`, `kdim`, `kcoords-aux`, `kcoords`;
  - `in-image-p`, `idim`, `extend-kbasis`, `firstn`, `ibasis`, `ilistnp`, `icoords`;
  - the authors' `in-theory` events on these functions (for example `(disable lin-injective-p lin-surjective-p)` and `(disable (kbasis))`).
- Each form is preceded by a `;; vectors.lisp:<line>` comment.
- These authors' definitions are omitted because no target needs them: `vindepp-sk`, `vdepp-sk`, `vbasis-mat`,
  `wdepp`, `wdep-coeffs`, `wcoords`, `windepp-sk`, `wdepp-sk`, `wbasisp`, `wbasis-mat`, `wunspanned`,
  `extend-to-wbasis`, and `nth-vcomb` (a proof helper).
- **LOCAL admission lemmas.** There are 89 events, copied verbatim from master `support/vectors.lisp`. Each is marked
  `;; support/vectors.lisp:<line>` and is either wrapped in `(local …)` or converted from the authors'
  `local-defthm(d)` to `(local (defthm(d) …))`. They are needed:
  - for the lin encapsulate's witness: `c*w0` and its W lemmas;
  - for the `sbasis0-aux` termination hint: `vdepp-if->-vdim`;
  - for the `sbasis1` encapsulate: `slistnp-sbasis0`, `flistnp-scoords0`, `sbasis0-spans` and `vindepp-sbasis0`,
    with their whole proof chain (vcoords0-vcomb, vdepp-vcomb-v0, vindepp-vcomb-v0, vdepp-v0, vdepp-vcomb,
    and the S-section lemmas).

  I pruned the set greedily: each candidate was removed if `defs.lisp` still certified without it
  (`verify/prune.sh` and `prune.log`, 33 of 122 candidates removed). The local includes of
  `support/reduction` and `support/cramer` also turned out to be unnecessary and were dropped.
  - **Caveat:** these local events contain the authors' proofs of some lemmas in the chain toward MAIN-4,
    and of a few lemmas MAIN-3/5/6 also use, mainly `vdepp-vcomb-v0`, `vindepp-vcomb-v0` and `vdepp-vcomb`.
    They are not exported, but a model reading `defs.lisp` can see them. This follows from the instruction
    to admit `sbasis0-aux` and the `sbasis1` encapsulate with LOCAL lemmas rather than skip-proofs.
- No skip-proofs, defaxiom or ttags.

## Deviations from the authors' text
1. **Package and portcullis.** The book is in package "DM", not "ACL2", so the authors' text stays verbatim.
   The DM package comes from `cert.acl2` (`projects/numbers/portcullis`). A solution must use the same
   portcullis, which `check-exp2.py` copies automatically, and start with `(in-package "DM")`.
2. **Definitions and encapsulates are verbatim**, including the encapsulates' exported constraint theorems and
   hints. Authors' theorems other than encapsulate constraints are removed or made LOCAL. The 8.7 Part I–II
   books are used instead of master Part I–II. The only Part I–II difference reachable from the definitions
   is in the field encapsulate: master adds `:formals` and `:guard` to `f+`, `f*`, `f-` and `f/`, and a
   defattach. The constraints and all bodies are identical (see V3). Part III declares no guards, so this
   does not change admissibility.
3. Target names are MAIN-k, not the authors' names, and MAIN-1, MAIN-5 and MAIN-6 are conjunctions of the
   authors' theorems. Every `defthmd` is `defthm`, and the authors' `defthmd`/`:rule-classes` choices are not
   carried over. Statement bodies are textually the authors'.
4. Proofs of the targets on 8.7 need master Part II lemmas that are not in 8.7. Examples are `sol0p` and
   its lemmas, `flist-minus`, `flistnp-append` and `len-lead+free`, used for MAIN-5/6. A solver has to
   re-derive them from Part II. No target statement or definition uses them.

## Verification
- **V1:** PASS. `defs.lisp` certifies with cert.pl on the 8.7 image in a scratch copy, in about 7 s
  (`verify/v1-cert-defs.log`, `v1-defs.cert.out`). It also certifies on the master image, as part of the
  master check below.
- **V2:** PASS. `verify/test-skip.lisp` includes `"defs"` and admits MAIN-1..6 under skip-proofs.
  It certifies on 8.7 (`v2-*.log`), with `test-skip.acl2` giving `:skip-proofs-okp t`.
- **V3:** PASS, with the master build (`/opt/acl2-master`, master `projects/linear`, the certified master
  `vectors.cert`).
  - (a) `verify/v3-authors.lisp` includes the authors' `projects/linear/vectors` and proves each MAIN-k by
    `:use` of the authors' theorem(s). It certifies (`v3-*.log`).
  - (b) Identity of definitions, three ways:
    - Textually, `verify/check-verbatim.py` checks that every non-local form of `defs.lisp` occurs (up to
      whitespace and comments) in master `vectors.lisp`, and every local event occurs in master
      `support/vectors.lisp`. Result: OK.
    - Semantically, `verify/dump-defs.lsp` prints formals, unnormalized body, constraint, guard and measure
      for every defs.lisp function and every DM function it depends on (112 functions, Parts I–III). It was
      run on 8.7 with `defs` and on master with the authors' `vectors`. `dump.diff` shows differences only in
      the formals and guards of `f+`, `f*`, `f-` and `f/` (deviation 2).
    - Redundancy: `verify/test-solution.lisp` includes `"defs"` and then the authors' master
      `projects/linear/vectors`, so every Part III definition must be redundant, i.e. identical. It then
      proves MAIN-1..6 by `:use`.
- **check-exp2.py:**
  - Run on 8.7 with the skip-proofs test, it gives `BANNED: skip-proofs`, as expected (`check-87-skip.log`).
  - A copy pointed at the master image (`check-exp2-master.py`; it differs only in the ACL2 and cert.pl
    paths) run on `test-solution.lisp` gives `CERTIFIED …; targets matched: main-1 … main-6`
    (`check-master.log`). This confirms that target matching and certification work.
  - The real-proof solution cannot run on 8.7, because the authors' Part III book is not in the 8.7 tree
    (which also means nothing leaks on 8.7).
- Source revision: `/opt/acl2` `origin/master` = 1d2b39a424eabeab269f189b37c29148d49fc516.
- `verify/gen-defs.py` generated `defs.lisp`, using `gen-defs-drop.json`. It must be run from a directory
  holding `src/vectors.lisp` and `src/support_vectors.lisp`, extracted with `git show origin/master:…`.
