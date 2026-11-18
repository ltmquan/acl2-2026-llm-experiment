# 08 — Coglio & Jurgensen — inductive definitions

**Paper:** Alessandro Coglio, Grant Jurgensen, *Inductive Definitions via Inference Rules in ACL2*. PDF: `source/paper.pdf`.

The paper presents `definductive`, an event macro that defines predicates from inference rules. It builds FTY proof-tree types, validity functions and `defun-sk` predicates, and generates the inference-rule theorems, a rule-induction scheme and minimality theorems.

Not in experiments 1–2: the contribution is an ACL2 feature (a tool), not a theorem.

## Experiment 3 — the model built the tool from the paper

The model received `exp3/prompt.txt`: the paper's text (links to the authors' code removed) and a numbered
list of requirements. Its work is in `exp3/solution/`. The grader is [`tools/graders/tool-definductive/`](../tools/graders/tool-definductive/);
its `CHECKLIST.md` says how to judge each MANUAL requirement.

**Result:** 6 of 6 requirements pass.

**To review:** nothing is MANUAL. The grader's filled-in hints are listed in its `NOTES.md` (marked FILL).

## Experiment 4 — future work

### Executable predicates (Section 8 future work)

`exp4/definductive-exec/`: the prompt (`prompt.txt`) and the model's work (`solution/`). The grader is
[`tools/graders/fw-definductive-exec/`](../tools/graders/fw-definductive-exec/).

**Result:** R1–R4 PASS: the books' `definductive-tests.lisp` still certifies unchanged, and our hidden `:exec` definitions pass, including the exact form of `e-correct`.

**To review:** nothing is MANUAL. The model's extended `definductive.lisp` is a modified copy of the books' file.
