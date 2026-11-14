# tool-aes-mir grader: notes

## Mapping of requirements
| R | how | mechanical? |
|---|---|---|
| 1 | prechecks + diff for a person | MANUAL (prechecks can FAIL) |
| 2 | JSON found and parsed; recorded options; embedded crate sources = current files; README command re-run | yes (MANUAL if the command cannot be run) |
| 3 | certification + a book naming the JSON | MANUAL after the mechanical part |
| 4 | generated `grade-r4.lisp`: run.lisp's `mir-aes-encrypt`/`-decrypt` exist, arity 2, logic mode; run.lisp certifies | yes |
| 5 | `grade-r5.lisp` (FIPS C.1, B) through an adapter generated over run.lisp | yes (`--adapter` overrides) |
| 6 | `grade-r6.lisp` (our 66 inputs) through the same adapter | yes |
| 7 | `cert.pl` on every `.lisp` under /work except `subject/` | yes |

## Interpretations
- Revised prompt: requirement 4 fixes `/work/run.lisp` with `(mir-aes-encrypt key block)` and
  `(mir-aes-decrypt key block)` in the representation of `aes::aes-128-encrypt`. Old R4/R5/R6 are now R5/R6/R7.
  The names are looked up in the package of run.lisp's `in-package` (the prompt does not fix the package).
  The adapter is now generated (two program-mode wrappers); `--adapter` is kept as an override.
- R6: the prompt says the checker runs its own inputs; ours are: corner cases all-zero and all-#xff (key = block), 64 pairs from
  splitmix64 (gamma #x9E3779B97F4A7C15, standard mixer) with seed `#x4752414445522D44` ("GRADER-D"); pair i
  takes outputs 4i..4i+3, each as 8 little-endian bytes; key = bytes 0-15, block = bytes 16-31. The first
  pseudorandom pair is key `(36 105 198 64 116 9 71 61 68 192 219 19 190 112 33 173)`, block
  `(255 133 122 206 4 108 126 76 94 15 4 246 113 58 236 126)`. Expected ciphertexts are computed in-book by
  `aes::aes-128-encrypt` (argument order: plaintext, key). The model's own 66 in-book inputs are checked only by
  certification (R7).
- FIPS-197 vectors are transcribed (C.1: key 000102..0f, plaintext 00112233..ff, ciphertext 69c4e0d8..c55a;
  B: key 2b7e1516..4f3c, input 3243f6a8..0734, output 3925841d..0b32) and checked in `grade-r5.lisp` against
  `aes::aes-128-encrypt`/`-decrypt` before use, so they do not rest on the transcription.
- R2 "produced with `--mir elaborated` as in Section 6.2": we require `ullbc: true`, `mir: "Elaborated"` and
  `monomorphize: false` in the options Charon records in the file (Section 6.2: no monomorphization). Other
  flags are not checked. The JSON may be `.json`, `.ullbc` or gzipped.
- Regeneration: the first README line with `charon rustc|cargo` and `--mir elaborated` (continuations joined)
  is run in a second copy, with `/work/` rewritten to the copy and `--dest-file` redirected; run from
  `subject/`, then from the work root. Outputs compared as JSON after removing `dest_dir`/`dest_file` and
  rewriting the copy path to `/work`. Two runs of Charon here differ only in those two fields (tested).
- Absolute `/work/...` paths in the model's books: if /work does not exist, the grader symlinks /work to the
  copy for the run; otherwise it warns.
- Banned events: the list of `check-prove.py` (plus a few raw-mode/untouchable forms), and `cert-flags:` /
  `cert_param:` comments that enable skip-proofs or ttags. `acl2-customization.lsp` files are not scanned
  (cert.pl does not load them).
- R3 "fixtypes and an executable interpreter": judged by a person (CHECKLIST); only certification and the
  presence of an import test naming the JSON are mechanical.

## Validation (all in scratch, nothing of it in this directory)
- After the revision: the master mock with a logic-mode `run.lisp` (package RUST, over `rust::run-fn`), no
  `--adapter`: R1 MANUAL, R2 PASS, R3 FAIL (expected, no import test in the mock), R4 PASS, R5 PASS, R6 PASS
  (66/66), R7 PASS (19 books). `run.lisp` with the functions in program mode -> R4 GRADER-FAIL.
Earlier (old numbering R4/R5/R6 = new R5/R6/R7):
- Reference implementation: master's `books/kestrel/rust/{mir,import}` (164dd21c04) does **not** certify on
  8.7 (fails in `mir/interp.lisp`, FTY result-type theorems), so it was used on master: a mock /work with those
  books under `acl2/`, master's adapted `aes_fixslice_encrypt.rs` as `subject/src/lib.rs`, JSON produced with
  the local Charon 0.1.315 via the mock README command, and an adapter over `rust::run-fn` and
  `*aes-fixslice-program*`. `GRADER_ACL2=/opt/acl2-master/saved_acl2 GRADER_CERT=... grade.py mock --adapter`:
  R1 MANUAL, R2 PASS (regenerated identically), R3 FAIL (expected: the mock had no import test; master's uses a
  ttag to gunzip), R4 PASS, R5 PASS (all 66 agree), R6 PASS (18 books). 4.5 minutes.
- Negative: adapter with key/block swapped -> R4 FAIL (C.1), R5 FAIL (inputs 2..65; 0 and 1 have key = block);
  edited `lib.rs` after the JSON -> R2 FAIL (stale sources); README with `--mir promoted` -> R2 FAIL; README with
  `--monomorphize` added -> R2 FAIL (regenerated JSON differs).
- On 8.7: `grade-r4.lisp` and `grade-r5.lisp` certify with a stub adapter that calls the specification itself
  (checks translation, the FIPS constants against 8.7's `aes-spec`, and the generator).
- Charon's `files` field embeds the crate sources, which is what the staleness check uses; confirmed on the
  mock.

## Problems to fix before launch
- The pristine crate is at `/opt/inputs/aes-0.9.1.crate` in the task environment; the grader also looks at
  `/home/user/acl2-exp/toolchain/aes-src/aes-0.9.1.crate` or `GRADER_AES_CRATE`.
- The JSON is about 4 MB here (paper: 6.9 MB with their Charon); make sure `submit` keeps it (it is not a build
  output), or R2/R3 fail for lack of the file.
