# 12 — Hardin — Arrayset revisited

**Paper:** David Hardin, *Arrayset Revisited*. PDF: `source/paper.pdf`.

An array-backed set written in Restricted Algorithmic Rust, translated to ACL2 through RAC, with correctness theorems about its free and used lists.

Not in experiments 1–2: a toolchain case study; the definitions its theorems need were not available.

## Experiment 3 — the model built the tool from the paper

The model received `exp3/prompt.txt`: the paper's text (links to the authors' code removed) and a numbered
list of requirements. Its work is in `exp3/solution/`. The grader is [`tools/graders/tool-arrayset/`](../tools/graders/tool-arrayset/);
its `CHECKLIST.md` says how to judge each MANUAL requirement.

**Result:** 4 PASS (Figures 5–6 token for token; Figure 7 reproduced by the RAC translator; the Figure 8–9 theorems verbatim and non-vacuous), 1 MANUAL, 0 FAIL.

**To review:** R3: the Figure 4 example, on the model's `ARR_SZ` = 6 instance.
