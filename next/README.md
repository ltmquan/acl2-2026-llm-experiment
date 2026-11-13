# Next experiments (drafts, not yet approved or run)

Drafts for the follow-up experiments. Nothing here has been run, and nothing has been proved. The ACL2
statements in `statement-checks/` have only been checked to load, under `skip-proofs`. They are not
solutions.

| File | What it is |
|---|---|
| `tool-specs.md` | Six excluded tool papers: the model gets the paper and builds the tool. Each spec gives what to build, acceptance criteria taken from the paper, the extra setup needed, leakage sources, and feasibility. |
| `future-work-tasks.md` | Six items from the papers' future-work sections (the flip graph is excluded): task statements, the ACL2 base each needs, candidate ACL2 statements, leakage checks. |
| `zfc-tasks.md` | Tractable items from Kaufmann's `zfc-future-work` list (ACL2 `books/projects/set-theory`, base commit 65589c5afd, 2026-07-05): task statements and candidate ACL2(zfc) statements. |
| `statement-checks/` | The files used to check that the candidate statements load. |

Please comment on the
statements: are they faithful to what the papers or the list ask for, and are they well posed?
