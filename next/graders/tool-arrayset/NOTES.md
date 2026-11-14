# tool-arrayset grader: interpretations and validation

## Files
- `grade.sh <work>`: the grader (ACL2 8.7, `/opt/acl2/saved_acl2`, `cert.pl` from `/opt/acl2/books`).
- `check.py`: helpers (banned events, Rust token comparison, Fig. 7 comparison, form comparison, book discovery).
  Banned list and s-expression reader copied from `../check-prove.py`.
- `fig5-6.rs`: transcription of the `Arrayset` struct, `free_head`, `used_head` (Sec. 5.1) and `aset_add`
  (Fig. 5), `aset_del_head`, `aset_del` (Fig. 6). `fig7.lsp`: transcription of Fig. 7. `targets.lisp`: Figs. 8-9.
- `grade-r4-1..4.lisp`: the four theorems of Figs. 8-9 verbatim, each `:by` the model's theorem of the same name.
- `grade-r4v.lisp`: non-vacuity (R4). `grade-r3x.lisp`: our own execution of Fig. 4 (evidence for R3).

## How grade.sh finds the model's books
The prompt fixes only `src/arrayset.rs`, `examples.lisp` and `README.md`. grade.sh certifies every `.lisp`
under `/work` (except unchanged copies of `books/projects/rac` files, in case the model copied RAC to build
it) with default cert flags, then writes `zz-grader/grader-model.lisp` that includes all certified books; if
they cannot be included together, it includes only the books that define the four theorem names or `asetp`.
Grader books live in `zz-grader/` with their own `cert.acl2` (no portcullis; package "RTL" is built in), so
the model's `cert.acl2` does not apply to them. The generated `ASET_DEL` file is the `.lisp` that defines
`ASET_DEL` (by reading, not by name).

## Interpretations
- R1 "as in Figures 5-6": token equality after dropping `//` comments, whitespace and `pub`. The `ARR_SZ`
  line is checked separately (value 1024, any type): the paper's `const ARR_SZ: uint = 1024;` does not compile
  (`uint` is not a Rust type; a `type uint = usize;` alias is a fine fix). Other differences are MANUAL with
  the rule in CHECKLIST.md. `rustc` is tried as a library (edition 2021, then 2015), then as a binary.
  The paper's code compiles with warnings only (checked: `fig5-6.rs` + `ARR_SZ` + two stub functions).
- R2: "re-run the RAC translator per the README" is mechanized as: `rac -a foo.cpp` for the generated
  `foo.lisp` (RAC always writes `foo.lisp` from `foo.cpp`), compared form for form; other layouts fall back
  to MANUAL (CHECKLIST R2). The comparison with Fig. 7 ignores `(BITS x 63 0)` wrappers: our own RAC run on
  the figure's code gives Fig. 7 exactly except the first argument of `ASET_FIND_VAL_FROM`, which is
  `(AG 'USED_LST ASET)` rather than `(BITS (AG 'USED_LST ASET) 63 0)` when the field and the parameter have
  the same type (the paper's Plexi output evidently declared them with different types).
  "Certifies against rtl/rel11/lib/rac": the RAC script itself certifies the regenerated book after
  `(include-book "rtl/rel11/lib/rac")`; we also require the model's file to certify under `cert.pl` and to
  mention `rtl/rel11/lib/rac` (RAC's output contains that `include-book`).
- R3 is MANUAL: the prompt does not fix how the example is reproduced (size 5 with `ARR_SZ` = 6, or the
  model's `ARR_SZ`). Figure 4 vs text: panel (a) is `anext` = 0 2 1 4 5 3, `used_lst` = 1, `free_lst` = 5
  (used 1 -> 2 -> 1 holding 22, 33; free 5 -> 3 -> 4 -> 5). Panel (b) is `anext` = 0 3 2 4 5 1, `used_lst` = 2,
  free 5 -> 1 -> 3 -> 4 -> 5. The text's free traversal "5 -> 1 -> 3 -> 4 -> 5" is described right after (a)
  but is the free list of (b); (b) is exactly what Figs. 5-6 compute from (a) (find_val_from returns 2,
  `used_lst` := 2, the head 1 moves to the free head). So figure and text agree on (b), and on (a) the text's
  free traversal is wrong; "the text is authoritative" changes nothing for (b). Also, "size 5" means five
  usable slots 1..5 (slot 0 unused), so `ARR_SZ` would be 6 at that size.
- R3 extra (`grade-r3x.lisp`, reported inside the R3 line): Fig. 4 at the model's `ARR_SZ`: init, add 22,
  add 33 gives (a) (by Fig. 5, `aset_add` stores at the new used head, so 33 is the head); `aset_del 22`
  must give a one-element circular used list holding 33, a free list one longer, with 22's slot at the free
  head. It uses `aset-used-list` / `aset-free-list` (Sec. 5.3) and `used_head` / `free_head`.
- R4: `:by` checks that the model's theorem (same name, not local) implies the paper's statement read in
  package "RTL", over the model's own definitions. Non-vacuity: the hypotheses of each theorem are evaluated
  on the Fig. 4(a)-analogue built with the model's `aset_init` and `aset_add` (the paper fixes the names of
  all functions involved; it does not fix `aset_init`'s arity, so grade.sh reads it from the generated
  `ASET_INIT`: 0 formals -> `(aset_init)`, 1 formal -> `(aset_init nil)`, the empty record; anything else ->
  MANUAL). The Fig. 9 length hypothesis `(+ used free) = ARR_SZ - 1` is then a real constraint on
  `aset_init` (all slots 1..ARR_SZ-1 on the free list).
- R5: every `.lisp` must certify; a non-book `.lisp` is a CHECKLIST override.

## Validation (all in a scratch directory)
- `apt-get install -y flex`, then RAC builds from a copy of `/opt/acl2/books/projects/rac` (`make release`,
  `make rac`); `rac -a` works and certifies its output against `rtl/rel11/lib/rac`.
- Fig. 7 check: a RAC transcription of Fig. 6 (with stub callees) translated by RAC gives Fig. 7 up to the
  `BITS` wrapper noted above; `check.py fig7` reports PASS on it.
- Mock solution `mockA` (scratch only): Rust = `fig5-6.rs` + rough `aset_transfer`/`aset_find_val_from`/
  `aset_init`; RAC source for all eight functions (`ARR_SZ` = 1024, translated by RAC); mock predicates and the
  four theorems under `skip-proofs`; an `examples.lisp`.
  - real `grade.sh`: rejected for the `skip-proofs` (all R FAIL, banned) as required;
  - scratch copy of grade.sh without the banned scan and with `:skip-proofs-okp t` for the grader books:
    R1 PASS, R2 PASS (Fig. 7 up to BITS; `rac -a` reproduces the file), R3 MANUAL with `grade-r3x` PASS,
    R4 PASS (all four `:by` and `grade-r4v`), R5 PASS. This exercised every grader book.
- Negative tests:
  - `mockV` (no skip-proofs; `asetp` made false, so the four theorems are proved vacuously): real grade.sh
    gives R4 FAIL "non-vacuity check failed", everything else as before;
  - `mockC`: an extra hypothesis in `aset_del_head-used-list--thm` -> R4 FAIL naming that theorem;
    `aset_init` renamed in the Rust -> R1 FAIL "aset_init missing"; `LOG<>` replaced by hand in the
    generated `ASET_DEL` -> R2 FAIL (lacks `log<>`, and the regenerated output differs);
  - a changed `aset_del` body (`err = 0`) -> R1 MANUAL with the token diff.
- `grade-r3x.lisp` had one wrong assertion on the first run (the circular used list of (a)); fixed and rerun.
- Not validated: proofs of the real theorems (no solution written); a README-driven layout where the RAC
  source has a different base name (falls back to MANUAL).
