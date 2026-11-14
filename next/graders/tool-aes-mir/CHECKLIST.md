# tool-aes-mir: what a person must inspect

`grade.sh <work-dir> [--adapter <file>]` prints `R1`..`R7`. Logs are under `<copy>/work/grader-logs/`.

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
   interpreter test books (R5) run on. A test that only checks that parsing succeeds fails R3.

## R4 (mechanical)
`grade-r4.lisp` is generated with the package of `/work/run.lisp` (its `in-package`): it includes `run` and
checks that `mir-aes-encrypt` and `mir-aes-decrypt` are logic-mode functions of arity 2; run.lisp must certify.
A person only needs to look if `run.lisp` defines them in a package other than its `in-package` (then grade
with `--adapter`, below, and decide R4 by hand).

## R5, R6 (mechanical; `--adapter` is an override)
By default the grader generates `grader-aes-adapter.lisp` that calls `mir-aes-encrypt`/`mir-aes-decrypt`
directly (the prompt fixes the representation: that of `aes::aes-128-encrypt`, lists of 16 bytes):
- R5 (`grade-r5.lisp`): C.1 and B encrypt to the FIPS-197 ciphertexts; decrypt inverts both.
- R6 (`grade-r6.lisp`): our 66 inputs (2 corner cases, 64 from splitmix64 seed `#x4752414445522D44`) agree with
  `aes::aes-128-encrypt`.
Override, only if R4 fails for a reason that does not touch the interpreter (e.g. names in another package):
write `grader-aes-adapter.lisp` from `adapter-template.lisp` (conversions and the documented call only) and run
`grade.sh <work-dir> --adapter <file>`; record that the override was used. R4 stays FAIL in that case.
Also check that the model's own R5/R6 test books exist and use `assert-event` on `mir-aes-encrypt`/`-decrypt`
(they are certified under R7).
