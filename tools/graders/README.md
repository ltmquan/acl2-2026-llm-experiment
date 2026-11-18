# Graders for the experiment 3–4 build tasks (written before any run)

One folder per build task. Experiment 3: `tool-definductive`, `tool-smtlink3`, `tool-erlang`, `tool-remora`,
`tool-arrayset`, `tool-aes-mir`. Experiment 4: `fw-ftc-macro`, `fw-definductive-exec`, `fw-multisets`. The
prove tasks are checked by [`../check-prove.py`](../check-prove.py) instead.

Each folder has:
- `grade.sh <work-dir>`: copies the model's work to a fresh directory, rejects banned events, certifies the
  model's books, certifies our grader books against them, and prints one line per numbered requirement of the
  task's `prompt.txt`: `R<n> PASS`, `R<n> FAIL <reason>` or `R<n> MANUAL <what to inspect>`;
- grader books (`grade-r<n>.lisp` and helpers): the paper's statements restated and proved `:by` the model's
  theorems, the paper's examples run verbatim on the model's tool, hidden tests, reference values;
- `CHECKLIST.md`: for each MANUAL requirement, exactly what a person must inspect and how to decide;
- `NOTES.md`: how the grader was validated before the runs (stubs, mocks, deliberately broken
  implementations, and real implementations where one existed locally), and every interpretation it makes.

The run of each grader on the model's work is in `harness/exp3-4/runs/<task>/grade.txt`. Four graders were
corrected after the runs, for cases the grader got wrong; each correction is described at the end of its
`NOTES.md`.

`tool-aes-mir/grade.py` looks for Charon and the `aes` 0.9.1 crate at the paths of the task environment
(`charon` on the `PATH`, `/opt/inputs/`), unless `GRADER_CHARON` or `GRADER_AES_CRATE` is set, and falls back to the paths of our build machine.
