# Experiment 3: paper → tool

Six of the papers excluded from experiments 1–2 contribute a tool or system rather than a theorem. In this
experiment the model gets the paper itself and has to build what it describes, in ACL2, without the authors'
implementation. Experiments 3 and 4 share one harness, described in [EXPERIMENT-4.md](EXPERIMENT-4.md#harness-shared-by-experiments-3-and-4).

## 1. The tasks

| Task | Paper | What the model builds | ACL2 |
|---|---|---|---|
| [`tool-definductive`](08-coglio-jurgensen-definductive/exp3/) | Coglio & Jurgensen — inductive definitions via inference rules | the `definductive` event macro, with the paper's examples and Section 5 proofs | 8.7 |
| [`tool-smtlink3`](09-chen-smtlink3/exp3/) | Chen, Greenstreet & Seltzer — Smtlink 3 | Smtlink 3: verified clause processors plus one trusted one that calls Z3 (trust tags allowed there only) | 8.7 + Z3 |
| [`tool-erlang`](10-bora-erlang/exp3/) | Bora & Greenstreet — Erlang in ACL2 | the front end, CPS evaluator and scheduler, and the paper's two example proofs | 8.7 + Erlang/OTP |
| [`tool-remora`](11-gamboa-remora/exp3/) | Gamboa — lifting argument frames in Remora | the paper's lemmas about the books' Remora interpreter | master |
| [`tool-arrayset`](12-hardin-arrayset/exp3/) | Hardin — Arrayset revisited | the Rust arrayset, its translation to ACL2 via RAC, and the Figure 8–9 theorems | 8.7 + flex |
| [`tool-aes-mir`](13-mccarthy-aes/exp3/) | McCarthy — fixsliced AES-128 | Section 6 only: the executable MIR semantics and Charon-JSON loader, running AES | 8.7 + Charon |

**The prompt** (`prompt.txt` in each task folder) is: "Build, in ACL2, the system described in the paper
below …", then the paper's text, then a numbered list of requirements, then the same environment and rules as
experiments 1–2. The paper text comes from `pdftotext -layout`, so figures are lost. Links to the authors' own
implementation are replaced by `[removed]`: the Erlang GitHub repository; McCarthy's Aeneas and Charon forks,
container image, Zenodo record and commit ids; and the path of the master `definductive.lisp`.

**The requirements** say what will be checked. They come from the paper: its names, interfaces, examples and
theorem statements. They were written, with their graders, before any run (drafts in
`harness/exp3-4/planning/tool-specs.md`).

Notes on individual tasks:
- **AES:** only the MIR-interpreter part of the paper is feasible offline. The paper's MIR JSON comes from the
  authors' own adapted copy of `fixslice32.rs`. The model instead gets the pristine RustCrypto `aes` 0.9.1
  crate (from crates.io) and an upstream Charon build, and does the adaptation and the JSON export itself.
- **Remora:** the interpreter it builds on exists only on ACL2 master, so this task runs there, with
  `books/workshops/2026` deleted.

## 2. Grading

Each task has a grader in `tools/graders/<task>/`. `grade.sh <work-dir>` scans the model's files for banned
events, certifies all of its books, then certifies our own grader books against them, and prints one verdict
per numbered requirement:

- **PASS**: checked by machine;
- **FAIL**: a machine check failed;
- **MANUAL**: the machine checks that could be done passed, but part of the requirement needs a person (an
  inspection the grader's `CHECKLIST.md` spells out).

Grader books restate the paper's theorems and prove them `:by` the model's theorems, run the paper's own
examples verbatim on the model's tool, run hidden tests, and compare against reference values (for AES, the
AES specification in `kestrel/crypto/aes`). Each grader's `NOTES.md` says how it was validated before the
runs: against stubs, mocks and deliberately broken implementations, and, where one exists locally, against a
real implementation (the authors' `definductive` on master; master's MIR interpreter for AES).

## 3. Results

All runs were first attempts, launched together on 2026-11-14 at 19:03 UTC. "Lines" counts all `.lisp` files of
the model's work; "authors" is the authors' own implementation where we have it.

| Paper | Time | Tool calls | Lines: model / authors | Requirements: pass · manual · fail | Audit |
|---|---|---|---|---|---|
| Coglio & Jurgensen — definductive | 31 min | 130 | 1,968 / 6,940 | 6 · 0 · 0 | clean |
| Chen et al. — Smtlink 3 | 32 min | 84 | 2,449 / not public | 5 · 4 · 0 | clean |
| Bora & Greenstreet — Erlang | 76 min | 187 | 2,888 / 15,060 | 1 · 6 · 0 | clean |
| Gamboa — Remora | 37 min | 109 | 1,991 / not public | 3 · 2 · 0 | flagged (benign) |
| Hardin — Arrayset | 27 min | 112 | 2,767 / not public | 4 · 1 · 0 | flagged (benign) |
| McCarthy — AES (MIR part) | 44 min | 153 | 2,914 / 7,281 | 5 · 2 · 0 | flagged (benign) |

Authors' sizes: `std/util/definductive.lisp` on master; the Erlang authors' public repository; master's
`kestrel/rust/mir` and `kestrel/rust/import`, which are the same part of the AES work the model built. The authors'
code does more than the task asked, so the sizes show scale only.

**What passed mechanically**, in brief (each task's `harness/exp3-4/runs/<task>/grade.txt` has the full output):
- definductive: the generated events have the paper's names and exact formulas; the paper's four examples are
  admitted and its Section 5 proofs go through with its hints; bad inputs are rejected with an ACL2 error; the
  generated proofs do not depend on the current theory.
- Smtlink 3: a goal is proved only on Z3's `unsat` (`sat`, `unknown` and errors fail); the paper's goal with
  its exact hint, the permuted goal, the type-terse and `:hypothesize` goals; one trusted clause processor and
  five verified ones.
- Remora: the seven helpers compute the paper's example; all five paper theorems verbatim, by `:by`.
- Arrayset: the Rust matches Figures 5–6 token for token; the RAC translator reproduces Figure 7; the Figure
  8–9 theorems verbatim, with hypotheses satisfiable on a concrete state.
- AES: the Charon JSON regenerates identically from the model's crate; FIPS-197 C.1 and B encrypt and decrypt;
  66 of our own inputs agree with the AES specification.
- Erlang: all books certify, the named theorems exist, and the closed form follows from the model's
  theorem. The rest is MANUAL because the paper fixes few names and interfaces.

**Three reported FAILs were the graders' fault**, not the models'. Each is written up in the task's `run.md`:
- definductive R3: the grader's own filling of a hint the paper leaves open;
- Arrayset R4: the grader could not load the model's two `ARR_SZ` variants together (the second exists
  because the prompt asked for an `ARR_SZ` = 6 instance); a regrade without it passes;
- multisets R1 (experiment 4): a fact true by the model's definition, which the grader's hint policy could not prove.

**Not yet done:** the MANUAL items. They need a person, ideally each paper's authors. The procedure for each is
in `tools/graders/<task>/CHECKLIST.md`.

**Audit:** see [EXPERIMENT-4.md](EXPERIMENT-4.md#audit). No run used the internet. The flags in Remora,
Arrayset and AES are local `cargo` builds and Charon runs, and loading local tools.
