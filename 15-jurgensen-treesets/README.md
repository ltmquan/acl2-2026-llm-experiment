# 15 — Jurgensen — treesets

**Paper:** Grant Jurgensen, *Treesets: Efficient Finite Sets with Unique Representations*. PDF: `source/paper.pdf`.

A library of finite sets as trees with unique representations, so that set equality is ordinary equality. Its future work includes multisets as maps to positive integers.

Not in experiments 1–2: a library paper; most key theorems were already in ACL2 8.7.

## Experiment 4 — future work

### Multisets (Section 9 future work)

`exp4/multisets/`: the prompt (`prompt.txt`) and the model's work (`solution/`). The grader is
[`tools/graders/fw-multisets/`](../tools/graders/fw-multisets/).

**Result:** 2 PASS, 1 MANUAL, 0 FAIL: all 110 theorem, guard and congruence checks pass. Built on 8.7's `std/omaps`: master already contains the authors' version (`kestrel/data/treebag`).

**To review:** the documentation of behaviour on non-bags (R1).
