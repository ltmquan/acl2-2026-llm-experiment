# tool-arrayset: what a person must inspect

`grade.sh <work>` prints `R<n> PASS|FAIL|MANUAL`. A MANUAL line says what to inspect; decide it as below.
The grading copy (path printed on the first line) keeps every log and the regenerated RAC output.

## R1 — `src/arrayset.rs` (only when R1 is MANUAL)
R1 is MANUAL when the file compiles and all eight functions exist, but the struct or one of `free_head`,
`used_head`, `aset_add`, `aset_del_head`, `aset_del` differs token-wise from `fig5-6.rs` (our transcription of
Sec. 5.1 and Figs. 5-6; whitespace, `//` comments and `pub` are ignored). The token diff is printed.
- PASS if every difference is one of: a visibility or `#[allow(...)]`/`#[inline]` attribute; a different
  type name in the `ARR_SZ` declaration (`uint` is not a Rust type; the value must be 1024); removal of the
  unused `let mut idx` / `let idx: usize;` lines; parentheses around `if` conditions removed. These do not
  change behaviour.
- FAIL for any other change (a changed condition, assignment, call, constant, argument order, return value),
  even if it looks equivalent.
- `aset_transfer`, `aset_find_val_from`, `aset_init` are written "from the text": they are not compared;
  their behaviour is exercised by R3's execution check and R4's non-vacuity check.

## R2 — RAC translation
grade.sh builds RAC from `/opt/acl2/books/projects/rac` (needs flex), finds the generated file that defines
`ASET_DEL`, checks (a) its `ASET_DEL` against `fig7.lsp` (identical, or identical after dropping
`(BITS x 63 0)` wrappers, is a pass), (b) all eight functions are in it, (c) it certifies and includes
`rtl/rel11/lib/rac`, (d) running `rac -a` on the `.cpp` with the same base name reproduces it form for form
and the regenerated book certifies against `rtl/rel11/lib/rac`.
- MANUAL "Fig. 7 differs": the diff is printed. PASS if the form is that of Fig. 7: `LET` of `PREV_INDEX` to
  `(ARR_SZ)`, an `MV-LET` over `(PREV_INDEX ASET)`, `IF1`/`LOG<` on `USED_LST`, a call of
  `ASET_FIND_VAL_FROM`, `IF1 (LOGAND1 (LOG< ...) (LOG<> ...))`, `AS 'USED_LST` then `ASET_DEL_HEAD`, and
  `AS 'ERR (ARR_SZ)` in both else branches. Differences in `BITS`/`SI` wrappers or argument types are fine.
  FAIL if the structure differs (e.g. no `MV-LET`, different branches).
- MANUAL "no RAC source next to ...": follow the commands in `/work/README.md` in a scratch copy, with RAC
  built as above (`cd rac/src && make release RAC=... ACL2=/opt/acl2/saved_acl2 && make rac ...`). PASS if
  they regenerate the graded file (same forms) with the RAC translator, from RAC source, without hand edits.
- MANUAL "output differs": the regenerated file differs from the model's; FAIL unless README.md documents a
  purely mechanical step after `rac` (e.g. concatenating files) that explains the difference exactly.
- (e) Always (also when R2 is PASS): open the RAC source and `src/arrayset.rs` side by side. The RAC source
  must be a translation of the Rust (same functions, same statements, modulo syntax: `usize`/`i64` typedefs,
  `array<...>` for Rust arrays, `for` loops). If the README says a transpiler produced it, rerun the
  transpiler once and check it reproduces the RAC source. A RAC source that implements different algorithms
  than the Rust is a FAIL of R2.

## R3 — `examples.lisp` reproduces Figure 4(b)
Mechanical part: `examples.lisp` certifies, has `assert-event`s, calls `aset_del`. The line also reports the
grader's own check `grade-r3x.lisp` (Fig. 4 executed on the model's functions at the model's `ARR_SZ`).
Read `examples.lisp`. PASS if it, by execution with `assert-event`:
1. builds the state of Fig. 4(a): contents {33, 22}, 33 at the used head, either at size 5 (indices 0..5,
   `ARR_SZ` = 6, `anext` = 0 2 1 4 5 3, `used_lst` = 1, `free_lst` = 5, `avals[1]` = 22, `avals[2]` = 33) or at
   the model's `ARR_SZ` by adds (e.g. init, add 22, add 33);
2. applies `aset_del 22` and checks the result: used list shortened by one (only 33 left), free list one
   longer; at size 5 the result must be Fig. 4(b): `anext` = 0 3 2 4 5 1, `used_lst` = 2, `free_lst` = 5, and
   the free traversal 5 -> 1 -> 3 -> 4 -> 5 of the Sec. 5 text.
   The text is authoritative where the figure differs (see NOTES.md: the text's free traversal is that of
   panel (b)).
The assertions must be about values computed by the model's functions (not constants compared with
themselves). If `grade-r3x` FAILS, look at its log: it means the model's `aset_add`/`aset_del` do not behave
as Sec. 5 says at the model's size, which also makes R3 a FAIL unless `examples.lisp` shows a size-5 build
that does reproduce Fig. 4(b) and the difference is explained by the size.

## R4 — non-vacuity when it is MANUAL
R4 is MANUAL only when `ASET_INIT` has neither 0 nor 1 formals, so the grader cannot build the instance.
Then, in ACL2 8.7: include the model's books (as `zz-grader/grader-model.lisp` does), build the Fig. 4(a)
state with the model's own initialiser and `(aset_add 33 (aset_add 22 <init>))`, and evaluate the
`assert-event` forms of `grade-r4v.lisp` with `*grader-s1*` / `*grader-a*` defined from that state.
PASS if all are true.

## R5 — a `.lisp` file that is not a book
R5 fails if any `.lisp` under `/work` does not certify. If README.md says a failing file is not a book (e.g.
an `ld` script or a RAC parser artefact), and nothing else requires it, treat it as PASS and note it.
Unchanged copies of `books/projects/rac` files are skipped automatically.
