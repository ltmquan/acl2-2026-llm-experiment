# Given package: binmonjil-chandy-lamport (Monjil & Ray, Chandy-Lamport reordering)

Logic: **acl2** (ACL2 8.7, `/opt/acl2/saved_acl2`). Library: `misc/records` only.

## Targets (targets.lisp)
- **MAIN-1** = authors' `checkpoint-complete-segment-reordered-run-state-equivalent`
  (global_reorder.lisp:5748). This is the global reordering theorem.
- **MAIN-2** = authors' `post-pre-two-imp-inputs-commute-under-state-equivalence`
  (local_swap.lisp:2224). This is the local post/pre swap theorem.

## defs.lisp
- Size: 1482 lines (1318 non-blank), 42,456 bytes. That is under the ~60 KB limit. It has no comments.
- Contents: `(in-package "ACL2")`, `(include-book "misc/records" :dir :system)`, then 163 authors'
  forms in the authors' order. The forms break down as 133 defuns, 29 defmacros and 1 encapsulate
  (`update-local-state-rcv`, `update-local-state-normal`, `message-to-send?`, `create-compute-message`,
  with its exported constraint `msg-type-of-create-compute-message`).
- Forms by book:
  - model: 85
  - scan: 22
  - good_state_inv: 26
  - recovery_inv: 6
  - cut_meta_inv: 13
  - local_swap: 10 (the `checkpoint-segment-*` functions, `checkpoint-completes-at-segment-end-p`,
    `checkpoint-start-end-segment-p` and `post-pre-swap-start-p`)
- The set is the transitive symbol closure of the two target statements
  (verify/extract.py, verify/closure.py, verify/gen.py).
- Nothing from global_reorder, channel_equivalence or basic is needed.
- None of these are included: `reorder-inputs`, `swap-first-after-before`, `inversion-count`,
  `before/after-cut-inputs`, `number-of-before-cut-inputs`, `two-imp-inputs-swappable-p`,
  `post-pre-two-imp-inputs-swappable-p`.
- `cut_meta_inv` invariants and `post-pre-swap-start-p` are present only because MAIN-2's statement
  needs them. Since there is one defs.lisp, they are also visible for MAIN-1.
- No theorems are exported besides the encapsulate constraint. No local lemmas were needed: all
  measures are `acl2-count`, and every definition admits without hints.
- No skip-proofs, defaxiom or ttags.

## Deviations from the authors' text
- Comments and blank lines inside forms are removed, and trailing whitespace is stripped.
  Otherwise every form is verbatim.
- 4 of the authors' 5 top-level encapsulates are not included because no statement needs them
  (`make-proc-ids`, `make-nbrs-to/from`, `make-init-local-state`). The defstub `complete-this` and
  the unused model/scan/good_state_inv functions are also left out.
- MAIN-1: the authors' `:rule-classes nil` and `:hints` are dropped, as targets carry no hints.
  The statement is unchanged. MAIN-2: the hints are dropped.

## Verification (8.7, scratch `<scratch>/`)
- **V1 PASS.** `cert.pl defs` certified (verify/defs.cert.out).
- **V2 PASS.** verify/test-skip.lisp (with `test-skip.acl2` cert-flags `:skip-proofs-okp t`)
  includes "defs" and admits MAIN-1 and MAIN-2 under skip-proofs. It certified
  (verify/test-skip.cert.out).
- **V3 PASS.**
  - All 9 authors' books certified unchanged on 8.7 in about 5 minutes (verify/authors-cert.log).
  - verify/faithful.lisp includes the authors' `global_reorder`. It proves MAIN-1 and MAIN-2 by
    `:use` of the authors' theorems with `:in-theory nil`, and it certified.
  - Definition identity was checked with verify/dump.lsp on both worlds (defs.lisp vs. the
    authors' books). For every function it compares formals, `body`, justification (measure),
    guard and symbol-class. It also compares every macro's args and body, and the encapsulated
    functions' `constraint-info`. The two dumps are byte-identical (verify/dump-diff.txt).
- **Checker:**
  - `check-exp2.py verify/test-solution.lisp` (the skip-proofs solution) is rejected as BANNED,
    which is expected (verify/check-skip.log).
  - verify/real-solution.lisp includes "defs" and then the authors' certified `global_reorder`
    (absolute scratch path), with redundant identical definitions. It proves both targets by `:use`.
    The checker reports `CERTIFIED with saved_acl2; targets matched: main-1, main-2`
    (verify/check-real.log).
