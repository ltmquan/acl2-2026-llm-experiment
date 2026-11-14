# tool-aes-mir: what a person must inspect

`grade.sh <work-dir> [--adapter <file>]` prints `R1`..`R6`. Logs are under `<copy>/work/grader-logs/`.

## R1 (always MANUAL once the prechecks pass)
Prechecks (mechanical, FAIL if not met): `subject/Cargo.toml`, `subject/ADAPTATION.md`, and a `.rs` file under
`subject/` sharing at least 10 function names with upstream `src/soft/fixslice32.rs`.
The grader extracts the pristine file from the crate (`/opt/inputs/aes-0.9.1.crate`, or
`toolchain/aes-src/aes-0.9.1.crate` here) and writes:
- `r1-adaptation.diff` (`diff -u upstream model`) and `r1-adaptation-ignoring-whitespace.diff` (`diff -u -w -B`);
- `r1-functions.txt`: functions only upstream, only in the adaptation, and in both.

Procedure:
1. Every hunk of `r1-adaptation-ignoring-whitespace.diff` must be covered by an entry of `ADAPTATION.md`
   (a hunk is covered if the entry names the function or construct and says what changed). Comment-only hunks
   need no entry. Any uncovered change to code: **R1 fails**.
2. Every "upstream only" function must be listed as dropped (AES-192/256, trait impls, `cfg` branches); every
   "adaptation only" function must be listed as added (expect single-block `encrypt`/`decrypt` entry points,
   possibly `encrypt_block`/`decrypt_block`).
3. Scope as in Section 4.2: AES-128 only, byte-array types instead of `cipher`'s `Array`/`FixsliceKeys128`,
   single-block `encrypt` and `decrypt` entry points. The round-operation and key-schedule bodies should be
   upstream text; a rewrite of them (rather than an adaptation layer) must be listed and is acceptable only if
   listed.
4. It is a cargo crate: `Cargo.toml` with no registry dependencies (R2's regeneration compiles it offline).

## R2 (MANUAL only if the README command could not be run)
Re-run the `charon ... --mir elaborated` command from `README.md` in a copy of /work (with `/work` replaced by
the copy), and compare the output with the committed JSON after deleting `translated.options.dest_dir` and
`dest_file` (`python3 -c 'import json,sys; ...'` or `jq 'del(.translated.options.dest_dir,
.translated.options.dest_file)'`). Equal: PASS. Also confirm the recorded options: `ullbc: true`,
`mir: "Elaborated"`, `monomorphize: false`.

## R3 (MANUAL after the mechanical part)
Mechanical: all books certify, and some certified book names the JSON file. A person confirms:
1. Fixtypes (`fty::deftypes`/`defprod`/`deftagsum`/...) for values, places/projections, rvalues, statements,
   terminators, bodies and machine state, and an executable interpreter over them (Section 6.1).
2. The import test book reads the JSON in `/work/subject/` **at certification time** (e.g. via a
   `make-event` or `defconsts` that calls the JSON parser on the file; not a pasted constant), runs the importer,
   and asserts (`assert-event`/`assert-equal`) that the result is `equal` to the program constant that the
   interpreter test books (R4) run on. A test that only checks that parsing succeeds fails R3.

## R4, R5 (MANUAL without `--adapter`)
Write `grader-aes-adapter.lisp` (template: `adapter-template.lisp`) from the README's instructions for running
encrypt/decrypt: include the model's interpreter and program books, and define `grader-aes-encrypt` and
`grader-aes-decrypt` (key, block as 16-byte lists -> 16-byte list). Only conversions and the documented call
belong in it. Then `grade.sh <work-dir> --adapter <file>`; R4 and R5 become mechanical:
- R4 (`grade-r4.lisp`): C.1 and B encrypt to the FIPS-197 ciphertexts; decrypt inverts both.
- R5 (`grade-r5.lisp`): our 66 inputs (2 corner cases, 64 from splitmix64 seed `#x4752414445522D44`) agree with
  `aes::aes-128-encrypt`.
If the README gives no usable invocation, a person may derive it from the model's own interpreter test book;
record that in the grading notes. If no invocation can be found at all, R4 and R5 fail.
Also check that the model's own R4/R5 test books exist and use `assert-event` (they are certified under R6).
