# 09 — Chen, Greenstreet & Seltzer — Smtlink 3

**Paper:** Christopher K. Chen, Mark R. Greenstreet, Margo I. Seltzer, *Smtlink 3: Rewrite-driven Compilation to SMT-LIB*. PDF: `source/paper.pdf`.

Smtlink 3 is a new architecture for Smtlink: a chain of verified clause processors driven by `rewrite$` does type inference, type fixing, term rewriting and simplification, and one final trusted clause processor writes an SMT-LIB script and calls Z3.

Not in experiments 1–2: a tool; it relies on Z3 and a trusted clause processor, and states no theorem of its own.

## Experiment 3 — the model built the tool from the paper

The model received `exp3/prompt.txt`: the paper's text (links to the authors' code removed) and a numbered
list of requirements. Its work is in `exp3/solution/`. The grader is [`tools/graders/tool-smtlink3/`](../tools/graders/tool-smtlink3/);
its `CHECKLIST.md` says how to judge each MANUAL requirement.

**Result:** 5 PASS, 4 MANUAL, 0 FAIL.

**To review:** R1 and R2: does the clause-processor chain follow the paper, with only the final one trusted (the grader found one trusted and five verified)? R7: the model's alist-to-array goal proves, but the grader's restatement did not. R8: printing the SMT-LIB script, per the README.
