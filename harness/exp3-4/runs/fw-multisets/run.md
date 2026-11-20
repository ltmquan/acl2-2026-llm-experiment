# fw-multisets

- Task folder: [`15-jurgensen-treesets/exp4/multisets/`](../../../../15-jurgensen-treesets/exp4/multisets/) (prompt, our files, and the model's work)
- Model run: 2026-11-14 19:04 to 2026-11-14 19:15 UTC, 11 min, 52 tool calls.
  First attempt; no retry.
- Saved by the model with `submit fw-multisets`; the saved work is in the task folder.
- Audit (`audit.txt`): CLEAN.

## Grade

```
R1 MANUAL mechanical checks passed; CHECKLIST R1-M: confirm mset.lisp documents the behavior on non-bags
R2 PASS 59 assertions cover all 20 functions
R3 PASS
SUMMARY fw-multisets: 2 PASS, 0 FAIL, 1 MANUAL
```

Full output: `grade.txt`.

## Note

The grader was corrected after the run: its hint policy now also tries the model's own definitions (with no induction), so facts that hold by definition, such as `support` = `keys`, are recognized. The first grading reported this one check as failed.
