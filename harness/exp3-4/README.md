# Experiments 3–4: our records

Reviewers do not need this folder; the task folders `NN-<paper>/exp3/` and `NN-<paper>/exp4/<item>/` hold what
they review. The reports are [EXPERIMENT-3.md](../../EXPERIMENT-3.md) and [EXPERIMENT-4.md](../../EXPERIMENT-4.md).

| Path | What it is |
|---|---|
| `runs/<task>/run.md` | timing, tool calls, audit result, grade summary, and our review of any reported FAIL |
| `runs/<task>/grade.txt` | the output of `tools/check-prove.py` or `tools/graders/<task>/grade.sh` on the model's work (temporary paths shown as `<tmp>`) |
| `runs/<task>/audit.txt` | the output of `tools/audit.py` on the full transcript, with any flagged tool calls |
| `planning/` | the task drafts (`tool-specs.md`, `future-work-tasks.md`, `zfc-tasks.md`) and the plan approved before the runs (`TASKS.md`) |
| `statement-checks/` | the files used to check that the drafted statements load; `zfc-task-specs-check.lisp` has the corrected T8/T9 statements |
| `build/` | `make-tasks.py` (writes every prompt), `redact.py` (paper text with links to the authors' code removed), `split-zfc.py` (ZFC packages) |
| `tasks-index.json` | the task list with environment and prompt size |

## Task ids

| Task | Folder |
|---|---|
| `tool-definductive`, `fw-definductive-exec` | `08-coglio-jurgensen-definductive/exp3/`, `…/exp4/definductive-exec/` |
| `tool-smtlink3` | `09-chen-smtlink3/exp3/` |
| `tool-erlang` | `10-bora-erlang/exp3/` |
| `tool-remora` | `11-gamboa-remora/exp3/` |
| `tool-arrayset` | `12-hardin-arrayset/exp3/` |
| `tool-aes-mir` | `13-mccarthy-aes/exp3/` |
| `fw-euler-product` | `01-gamboa-basel/exp4/euler-product/` |
| `fw-trapezoid`, `fw-stirling-bounds`, `fw-ftc-macro` | `02-gamboa-stirling/exp4/{trapezoid,stirling-bounds,ftc-macro}/` |
| `fw-inductance` | `07-cayuela-ac-machine/exp4/inductance/` |
| `fw-rectifier-rows`, `fw-rectifier-master` | `14-cayuela-rectifiers/exp4/{rectifier-rows,rectifier-master}/` |
| `fw-multisets` | `15-jurgensen-treesets/exp4/multisets/` |
| `zfc-t1` … `zfc-t11`, `zfc-t8-r2`, `zfc-t9-r2` | `16-kaufmann-set-theory/exp4/zfc-*/` |

## The two environments' setup scripts

Both: network "Limited" with package registries allowed, no extra hosts, MCP servers not allowed; the
experiment repository attached and checked out on `task/<task>`.

8.7 tasks (all except Remora, executable `definductive` and ZFC):

```bash
#!/bin/bash
set -euo pipefail
export TOOLCHAIN_REF=env-v1
curl -fsSL "https://raw.githubusercontent.com/ltmquan/acl2-2026-llm-toolchains/$TOOLCHAIN_REF/setup/install.sh" \
  | bash -s -- --acl2 8.7 --extra charon --apt "z3 erlang-nox flex" --input aes-0.9.1.crate \
      --submit acl2-2026-llm-experiment 2>&1 | tee /var/log/acl2-setup.log
```

Master tasks:

```bash
#!/bin/bash
set -euo pipefail
export TOOLCHAIN_REF=env-v1
curl -fsSL "https://raw.githubusercontent.com/ltmquan/acl2-2026-llm-toolchains/$TOOLCHAIN_REF/setup/install.sh" \
  | bash -s -- --acl2 master --remove "books/workshops/2026" \
      --submit acl2-2026-llm-experiment 2>&1 | tee /var/log/acl2-setup.log
```

`env-v1` was at commit `2e3f27c` for every run. The toolchain repository's `build/build-bundles.sh` records how
the bundles were made.
