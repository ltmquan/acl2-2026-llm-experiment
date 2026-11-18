# 11 — Gamboa — Remora argument frames

**Paper:** Ruben Gamboa, *Towards Formalizing the Semantics of Lifting Argument Frames When Evaluating Remora Expressions*. PDF: `source/paper.pdf`.

Work in progress: lemmas about the Kestrel Remora interpreter, showing that applying an integer binary primitive to two prefix-compatible arrays is a pairwise map over replicated cells.

Not in experiments 1–2: work in progress; lemmas about an interpreter written by others.

## Experiment 3 — the model built the tool from the paper

The model received `exp3/prompt.txt`: the paper's text (links to the authors' code removed) and a numbered
list of requirements. Its work is in `exp3/solution/`. The grader is [`tools/graders/tool-remora/`](../tools/graders/tool-remora/);
its `CHECKLIST.md` says how to judge each MANUAL requirement.

**Result:** 3 PASS (all five paper theorems verbatim by `:by`; the helpers compute the paper's example), 2 MANUAL, 0 FAIL. Runs on ACL2 master, where the interpreter is.

**To review:** R3: the commutativity corollary, whose statement was the model's. R4: the Section 2 examples.
