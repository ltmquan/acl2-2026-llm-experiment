# Next experiments (for approval; nothing has run)

| Path | What it is |
|---|---|
| [`TASKS.md`](TASKS.md) | **Start here.** The 26 tasks, the decisions made in writing them, and the two setups. |
| `tasks/<id>/` | Per task: `prompt.txt` (exactly what the model gets) and, for prove tasks, the files we certify against. |
| `build/` | Scripts that generate `tasks/` (`make-tasks.py`), the paper texts (`redact.py`) and the ZFC packages (`split-zfc.py`). |
| `tool-specs.md`, `future-work-tasks.md`, `zfc-tasks.md` | The earlier drafts the tasks come from: acceptance criteria, leakage checks, difficulty. |
| `statement-checks/` | The files used to check that the draft statements load. |

Nothing here has been proved. The statements have only been checked to load under `skip-proofs`.
