# fw-definductive-exec

- Task folder: [`08-coglio-jurgensen-definductive/exp4/definductive-exec/`](../../../../08-coglio-jurgensen-definductive/exp4/definductive-exec/) (prompt, our files, and the model's work under `solution/`)
- Model run: 2026-11-14 19:04 to 2026-11-14 19:56 UTC, 52 min, 108 tool calls.
  First attempt; no retry.
- Saved by the model with `submit fw-definductive-exec`; the saved work is the task folder's `solution/`.
- Audit (`audit.txt`): CLEAN.

## Grade

```
R1 PASS
R2 PASS
R3 PASS
R4 PASS
H2 PASS   (informative: e-correct / booleanp-of-e forms and executability for exec-tests.lisp's own definitions; not counted)
SUMMARY fw-definductive-exec: 4 PASS, 0 FAIL, 0 MANUAL (R1-R4); informative H2 PASS; logs in <tmp>
```

Full output: `grade.txt`.

## Note

The grader was corrected after the run: the informative check H2 now skips definitions inside `must-succeed*` and `must-fail`, which are undone and so never in the book's world. The first grading reported H2 as failed for that reason.
