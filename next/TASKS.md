# Next experiments: tasks, setups and prompts (for approval; nothing has run)

26 tasks, one cloud session each. `tasks/<id>/prompt.txt` is the exact text the model gets. Prove tasks
also have the files we certify against: `defs.lisp`, `targets.lisp`, and `admit.lisp` (definitions the
model must admit) or `optional.lisp` where present.

## Tasks

| Id | Source | What the model does | Setup |
|---|---|---|---|
| `tool-definductive` | inductive-definitions paper | builds `definductive` from the paper | 8.7 |
| `tool-smtlink3` | Smtlink 3 paper | builds Smtlink 3 (trust tags allowed for the final clause processor only) | 8.7 + Z3 |
| `tool-erlang` | Erlang paper | builds the front end, CPS evaluator and scheduler, and proves the two examples | 8.7 + Erlang/OTP |
| `tool-remora` | Remora paper | proves the paper's lemmas about the books' Remora interpreter | master |
| `tool-arrayset` | Arrayset paper | writes the Rust arrayset, translates it via RAC, and proves Figures 8–9 | 8.7 + flex |
| `tool-aes-mir` | AES paper | builds the MIR semantics and Charon-JSON loader of Section 6 only, and runs AES | 8.7 + Charon + aes 0.9.1 crate |
| `fw-euler-product` | Basel paper | proves the Euler-product bound and its nonstandard form | 8.7 (ACL2(r)) |
| `fw-trapezoid` | Stirling paper | proves the trapezoid-rule error bound | 8.7 (ACL2(r)) |
| `fw-ftc-macro` | Stirling paper | writes the `def-ftc-integral` macro and tests | 8.7 (ACL2(r)) |
| `fw-stirling-bounds` | Stirling paper | proves that n!/(√n·nⁿ·e⁻ⁿ) decreases, with the Robbins step bound | 8.7 (ACL2(r)) |
| `fw-inductance` | AC-machine paper | proves the air-gap inductance integral | 8.7 (ACL2(r)) |
| `fw-rectifier-rows` | rectifier paper | proves the six-phase and twelve-pulse rows and waveforms | 8.7 (ACL2(r)) |
| `fw-rectifier-master` | rectifier paper | proves the integral master theorem and two instances | 8.7 (ACL2(r)) |
| `fw-definductive-exec` | inductive-definitions paper | extends `definductive` with executable predicates | master |
| `fw-multisets` | treesets paper | writes a multiset library on `std/omaps` | 8.7 |
| `zfc-t1` … `zfc-t10` | `zfc-future-work` list | prove the T1–T10 statements of `zfc-tasks.md` | master |
| `zfc-t11` | `zfc-future-work` list | ultraproducts (optional, as approved) | master |

## Decisions made while writing them (please check)

1. **The tool tasks give the paper as text.** The text is from `pdftotext -layout`, so figures are lost
   and code listings keep only their text. Links to the authors' own code are replaced by `[removed]`:
   - the Erlang GitHub repository;
   - McCarthy's Aeneas/Charon forks, devenv image, Zenodo record and commit ids;
   - the path of the master `definductive.lisp`.
   Other references are left as they are.
2. **Future-work items give exact ACL2 statements**, as in experiment 2, not English only as the drafts
   proposed. They are our statements, not the authors', so they can be checked mechanically and need no
   faithfulness review. Definitions that need a proof to be admitted (the `defun-std` integrals) must be
   admitted verbatim by the model. All statements are checked:
   - every `defs.lisp` certifies with no `skip-proofs`;
   - the targets admit under `skip-proofs` (ACL2(r) 8.7, or master for ZFC).
3. **Dropped from the drafts:** the "given-axiom" corollaries (Euler product = π²/6 from Basel; the explicit
   Stirling bounds from Stirling). They would need a `defaxiom`, and they are one-step corollaries.
4. **Added to the rectifier master task:** the two instances the draft names in English (three-phase midpoint
   and bridge), stated in ACL2.
5. **ZFC:** each task gets the T*n* definitions as `defs.lisp`. Theorems are `defthmz` with open `:props`;
   the checker restates each with `:by`. T3(e), the non-principal ultrafilter on ω, is marked optional.
6. **AES:** the paper's MIR JSON comes from the authors' hand-adapted copy of `fixslice32.rs`. The model
   gets the pristine crate (from crates.io) and an upstream Charon build, and does the adaptation and the JSON
   export itself (requirements 1–2).
7. **Saving the work:** each prompt ends with `submit <id>`. It commits `/work` (without build outputs) and
   pushes it to the branch `results/<id>` of this private repository. Each session is started on the nearly
   empty branch `results-base`, so none of our files are on its disk. This avoids rebuilding solutions from
   transcripts, which experiment 2 needed for three papers. A session could still fetch `main`, but nothing
   there answers these tasks, and the audit flags any git fetch.

## Setups

Two environments. Both have the same network as experiments 1–2 (package registries only, which includes
GitHub). Both install from the public toolchain repository
[`ltmquan/acl2-2026-llm-toolchains`](https://github.com/ltmquan/acl2-2026-llm-toolchains), branch `env-v1`
(commit `2e3f27c`; if the branch is ever moved, the move is recorded here).

| Environment | `install.sh` arguments | Used by |
|---|---|---|
| `acl2-next-87` | `--acl2 8.7 --extra charon --apt "z3 erlang-nox flex" --input aes-0.9.1.crate --submit acl2-2026-llm-experiment` | all 8.7 tasks |
| `acl2-next-master` | `--acl2 master --remove books/workshops/2026 --submit acl2-2026-llm-experiment` | `tool-remora`, `fw-definductive-exec`, `zfc-*` |

- **Leaks:**
  - The master tasks need master because their inputs exist only there (the Remora interpreter,
    `definductive`, the set-theory future-work list). Deleting `workshops/2026` removes the papers'
    supporting books.
  - For these tasks, master contains no answer. The Remora lemmas, executable `definductive` predicates and
    the ZFC items are absent; this was checked by grep.
  - The 8.7 tasks' answers are not in 8.7.
  - Some answers are public on GitHub: the master `definductive` and multisets (`treebag`), and the Erlang
    and AES authors' repositories. GitHub stays reachable because it comes with package-registry access, so,
    as before, the prompt says "do not use the internet" and the transcript audit checks every network command.
- **Tested** in cloud sessions on 2026-11-14:
  - `acl2-next-87`: setup 35–48 s; ACL2(r) certifies; Charon runs on a test crate with `--mir elaborated`
    (25 s, first run).
  - `acl2-next-master`: setup 18–32 s; `workshops/2026` is gone; a ZFC book certifies.
  - In both, `submit` pushes `results/<id>` and leaves no unpushed commit, and the checkout holds only the
    `results-base` README.
