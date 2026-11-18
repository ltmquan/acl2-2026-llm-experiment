# Experiment 4: future work

The model works on open items: the future-work sections of the papers (the flip-graph paper is excluded,
since its authors have already done that work in Lean), and the tractable items of Kaufmann's
`zfc-future-work` list in `books/projects/set-theory`. None of these results existed in the community books.

## 1. The tasks

**Prove tasks (17).** We fixed exact ACL2 statements, as in experiment 2. They are our statements, not the
authors': each task folder has `defs.lisp` (definitions we give, certified with no `skip-proofs`),
`targets.lisp` (theorems to prove), and, where needed, `admit.lisp` (definitions the model must admit
verbatim, e.g. the `defun-std` integrals) or `optional.lisp`.

| Task | Source | Statement |
|---|---|---|
| [`euler-product`](01-gamboa-basel/exp4/euler-product/) | Gamboa — Basel | Euler product for ζ(2): finite two-sided bound, and its nonstandard form |
| [`trapezoid`](02-gamboa-stirling/exp4/trapezoid/) | Gamboa — Stirling | trapezoid-rule error ≤ (M/12)Σh³, for every partition |
| [`stirling-bounds`](02-gamboa-stirling/exp4/stirling-bounds/) | Gamboa — Stirling | n!/(√n·nⁿ·e⁻ⁿ) decreases, with the Robbins step bound |
| [`inductance`](07-cayuela-ac-machine/exp4/inductance/) | Cayuela — AC machine | ∫₀^{2π} cos(x−mγ)cos(x−nγ) dx = π cos((m−n)γ), as a limit of sums and as an integral |
| [`rectifier-rows`](14-cayuela-rectifiers/exp4/rectifier-rows/) | Cayuela — rectifiers | six-phase and twelve-pulse rows and output waveforms, with explicit conventions for the peak |
| [`rectifier-master`](14-cayuela-rectifiers/exp4/rectifier-master/) | Cayuela — rectifiers | the integral master theorem for V_DC and V_RMS, for every firing angle, and two instances |
| [`zfc-t1` … `zfc-t11`](16-kaufmann-set-theory/exp4/) | Kaufmann — set theory | T1 equivalence relations, T2 indexed products, T3 ultrafilters, T4 cardinality, T5 transfinite recursion, T6 infinite Ramsey, T7 topology, T8 groups, T9 fields, T10 metric spaces, T11 ultraproducts |

**Build tasks (3)**, graded like experiment 3 (numbered requirements, a grader per task, hidden tests):

| Task | Source | What the model builds |
|---|---|---|
| [`ftc-macro`](02-gamboa-stirling/exp4/ftc-macro/) | Gamboa — Stirling | `def-ftc-integral`, a macro that defines an integral and proves its value by the FTC |
| [`definductive-exec`](08-coglio-jurgensen-definductive/exp4/definductive-exec/) | Coglio & Jurgensen — definductive | executable predicates for `definductive`, proved equivalent automatically (on master) |
| [`multisets`](15-jurgensen-treesets/exp4/multisets/) | Jurgensen — treesets | a multiset library on 8.7's `std/omaps` |

Choices made in writing the tasks (from `harness/exp3-4/planning/`):
- **Conventions for the rectifier rows.** The paper's printed twelve-pulse entry does not fit the master
  equation with any natural choice of peak, so the task fixes explicit conventions. It does not mention the
  apparent erratum.
- **Two "given-axiom" corollaries dropped:** Euler product = π²/6 from Basel, and the explicit Stirling bounds from Stirling.
  They would need a `defaxiom`.
- **Multisets on `std/omaps`:** the paper's own substrate, treemaps, is master-only, and master already
  contains the authors' multiset library (`kestrel/data/treebag`). So the task uses 8.7's ordered maps.
- **ZFC:** `defthmz` theorems with open `:props`. The model may add hypothesis props, but only ones the
  set-theory books accept: `zsub`/`zfn` instances and abbreviations of existing props, all justified ZFC
  instances. T3(e), a non-principal ultrafilter on ω, is optional.

## 2. Checking

**Prove tasks:** `python3 -I tools/check-prove.py <solution-dir> <task-folder>`. It:
1. copies our `defs.lisp` (and `cert.acl2`), ignoring the model's copy;
2. rejects banned events, and for ZFC also direct `zfc-table` edits, `table-redo` and `with-props`;
3. allows only `(include-book "defs")` and community books;
4. requires each `admit.lisp` definition with the same kind, name, formals and body;
5. requires every target, not under `local`, with exactly its name and statement (`defthmz` for ZFC);
6. certifies with default flags, so a hidden `skip-proofs` (for example `defthme`'s fallback) fails.

It was tested on toy tasks against a correct solution and six kinds of wrong ones, before the runs.

**Build tasks:** as in experiment 3 (`tools/graders/<task>/`).

## 3. Results

All first attempts, 2026-11-14 from 19:03 UTC, except the two T8/T9 reruns.

| Task | Time | Tool calls | Result |
|---|---|---|---|
| Gamboa — Basel: Euler product | 18 min | 99 | 3 / 3 targets |
| Gamboa — Stirling: trapezoid-rule error | 45 min | 81 | 2 / 2 |
| Gamboa — Stirling: ratio bounds | 28 min | 91 | 2 / 2 |
| Cayuela — AC machine: inductance integral | 20 min | 109 | 2 / 2 |
| Cayuela — rectifiers: rows | 5 min | 31 | 6 / 6 |
| Cayuela — rectifiers: integral master theorem | 12 min | 93 | 4 / 4 |
| Gamboa — Stirling: FTC macro | 23 min | 70 | 2 PASS · 1 MANUAL (does a failed call print its obligation?) |
| Coglio & Jurgensen — definductive: executable predicates | 52 min | 108 | 4 / 4 PASS, including our hidden `:exec` tests |
| Jurgensen — treesets: multisets | 11 min | 52 | 3 / 3 (one R1 check failed only because of the grader; see its `run.md`) |
| Kaufmann ZFC T1 equivalence relations | 5 min | 44 | 6 / 6 |
| T2 indexed products | 5 min | 31 | 4 / 4 |
| T3 ultrafilters | 20 min | 84 | 5 / 5, and the optional non-principal ultrafilter on ω |
| T4 cardinality | 9 min | 50 | 10 / 10 |
| T5 transfinite recursion | 4 min | 30 | 2 / 2 |
| T6 infinite Ramsey | 4 min | 23 | 2 / 2 |
| T7 topology | 9 min | 67 | 4 / 4 |
| T8 groups | 9 min | 63 | 7 / 8; the 8th is false as we stated it (below) |
| T8, rerun with the corrected statement | 7 min | 39 | 8 / 8 |
| T9 fields | 5 min | 31 | 1 / 3; the other 2 are false as we stated them, refuted in ACL2 (below) |
| T9, rerun with the corrected statement | 18 min | 94 | 3 / 3 |
| T10 metric spaces | 12 min | 49 | 3 / 3 |
| T11 ultraproducts | 16 min | 55 | 2 / 2 |

### Two of our statements were wrong

Our ZFC statements had been checked only to load, not proved. The models found two errors:

- **T8, `subgroup-is-group`.** The books' `groupp` does not require the operation or the inverse to be a
  function. `apply` on a relation that is not a function picks a value by choice, so the statement cannot be
  proved. The model explained why, and proved the version with `(funp op)` and `(funp inv)` added.
- **T9, our `fieldp`.** It constrained multiplication only on nonzero elements and had only left
  distributivity, so 0·x = 0 did not follow. The model proved, in ACL2, a counterexample to
  `complex-construction-is-field` and `complex-i-squared`: a structure on the rationals with 0·y = y.

The corrected tasks (`zfc-t8-r2`, `zfc-t9-r2`) add these hypotheses: `(funp op)` and `(funp inv)` for T8, and,
in `fieldp`, `funp` for all four operations and commutativity of multiplication on all of S. Both passed the
same load checks as the other packages, and the reruns proved every target. These reruns are not blind first
attempts. The corrected statements are also in `harness/exp3-4/statement-checks/zfc-task-specs-check.lisp`.

## Harness shared by experiments 3 and 4

- **Model and runs:** as in experiments 1–2: one autonomous cloud session per task, medium effort, 6-hour
  limit, no retries needed. The prompt is delivered as the file `TASK.md` on the session's own branch
  `task/<id>` (the opening message says to read it), because some prompts are up to 67 KB. The content is
  the same as `prompt.txt`.
- **Environments:** two, both with the network of experiments 1–2. Each installs a prebuilt toolchain from the
  public repository [`ltmquan/acl2-2026-llm-toolchains`](https://github.com/ltmquan/acl2-2026-llm-toolchains)
  (branch `env-v1`, commit `2e3f27c`), which holds only open-source builds:
  - **8.7:** ACL2 8.7 and ACL2(r) 8.7 with more pre-certified books; upstream Charon with its Rust nightly; the
    aes 0.9.1 crate; Z3, Erlang/OTP and flex from Ubuntu.
  - **master:** ACL2 master (1d2b39a424) with `books/workshops/2026` deleted, for Remora, executable
    `definductive` and ZFC.

  Setup takes 18–48 s instead of the 11–14 min of experiments 1–2.
- **Saving results:** each prompt ends with `submit <id>`, which commits the model's `/work` (without build
  outputs) to the branch `results/<id>` of this repository. Each session starts on a nearly empty branch, so
  none of our files are on its disk. The task folders' `solution/` directories are copies of those branches.
- **Leakage:** for these tasks, ACL2 master contains no answer. Some answers are public on GitHub: the master
  `definductive`, `treebag`, and the Erlang and AES authors' repositories. GitHub stayed reachable, as in
  experiments 1–2.

### Audit

All 28 transcripts were saved in full and checked with `tools/audit.py` (`harness/exp3-4/runs/<id>/audit.txt`):
24 clean, 4 flagged. Every flag is benign:
- AES and Arrayset: local `cargo` builds and Charon runs on the models' own crates, which have no
  dependencies (`cargo test --offline`), and the filenames `Cargo.toml` and `Cargo.lock`;
- Basel and Remora: `ToolSearch`, used to load the local tools `TaskStop` and `Monitor`.

A direct search of all 2,169 tool calls finds no `curl`, no URL access, no web tool and no `git fetch`. The only
git commands are `git status` and `git log` on the session's own one-commit checkout.
