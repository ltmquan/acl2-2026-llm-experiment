# tool-smtlink3

- Task folder: [`09-chen-smtlink3/exp3/`](../../../../09-chen-smtlink3/exp3/) (prompt, our files, and the model's work)
- Model run: 2026-11-14 19:04 to 2026-11-14 19:36 UTC, 32 min, 84 tool calls.
  First attempt; no retry.
- Saved by the model with `submit tool-smtlink3`; the saved work is in the task folder.
- Audit (`audit.txt`): CLEAN.

## Grade

```
R2 world: trusted after F: (SMT::SMTLINK-TRUSTED-CP); trusted after all: (SMT::SMTLINK-TRUSTED-CP); verified cl-procs: (SMT::SIMPLIFY-CP-CORRECT SMT::TYPE-EXTRACT-CP-CORRECT SMT::TERM-REWRITE-CP-CORRECT SMT::TYPE-FIX-CP-
R1 MANUAL inspect the clause-processor chain (CHECKLIST R1); no file mentions python
R2 MANUAL one trusted CP (SMT::SMTLINK-TRUSTED-CP); verified CP rules (SMT::SIMPLIFY-CP-CORRECT SMT::TYPE-EXTRACT-CP-CORRECT SMT::TERM-REWRITE-CP-CORRECT SMT::TYPE-FIX-CP-CORRECT SMT::TYPE-INFERENCE-CP-CORRECT SMT::STRIP
R3 PASS
R4 PASS
R5 PASS
R6 PASS
R7 MANUAL alist goal proved by alist-to-array-example; but the grader's restatement (grade-r7) did not prove with a z3 unsat answer: see CHECKLIST R7
R8 MANUAL follow README.md to print the SMT-LIB script and rewritten term of poly-ineq-example (CHECKLIST R8)
R9 PASS
SUMMARY tool-smtlink3: 5 PASS, 0 FAIL, 4 MANUAL; files in <tmp>
```

Full output: `grade.txt`.
