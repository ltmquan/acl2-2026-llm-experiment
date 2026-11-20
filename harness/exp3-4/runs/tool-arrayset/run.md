# tool-arrayset

- Task folder: [`12-hardin-arrayset/exp3/`](../../../../12-hardin-arrayset/exp3/) (prompt, our files, and the model's work)
- Model run: 2026-11-14 19:03 to 2026-11-14 19:30 UTC, 27 min, 112 tool calls.
  First attempt; no retry.
- Saved by the model with `submit tool-arrayset`; the saved work is in the task folder.
- Audit (`audit.txt`): FLAGGED.

## Grade

```
R1 PASS (compiles with 'rustc --edition 2021 --crate-type lib'; struct and the five functions match Sec. 5.1/Figs. 5-6 token for token)
R2 PASS several files define ASET_DEL (gen/arrayset.lisp gen/arrayset6.lisp); checked gen/arrayset.lisp; Fig. 7: PASS identical to Figure 7 up to (BITS x 63 0) wrappers; rac -a gen/arrayset.cpp reproduces gen/arrayset.li
R3 MANUAL examples.lisp certifies, 49 assert-event forms; inspect it per CHECKLIST R3 (grader's own Fig. 4(b) execution check PASSES)
R4 PASS (four theorems verbatim by :by; hypotheses satisfiable on the Fig. 4(a) instance built with aset_init/aset_add; graded on arrayset-thms.lisp alone (the model's books define the same names in several instances))
R5 PASS (9 books: arrayset-defs.lisp arrayset-invariants.lisp arrayset-thms.lisp arrayset6-defs.lisp arrayset6-invariants.lisp arrayset6-thms.lisp examples.lisp gen/arrayset.lisp gen/arrayset6.lisp)
SUMMARY: PASS (1 MANUAL item(s) to inspect, see CHECKLIST.md)
```

Full output: `grade.txt`.

## Note

The grader was corrected after the run: when the model's books cannot all be loaded together (here, two instances of the arrayset with `ARR_SZ` = 1024 and 6, as the prompt asked, defining the same names), it grades on the first book that defines the four theorems.
