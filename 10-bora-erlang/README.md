# 10 — Bora & Greenstreet — Erlang in ACL2

**Paper:** Kuter Bora, Mark R. Greenstreet, *Erlang in ACL2: A Continuation-Passing Style Evaluator*. PDF: `source/paper.pdf`.

The paper translates Erlang ASTs into ACL2, evaluates them with a continuation-passing-style evaluator with fuel, and schedules processes with an encapsulated fair scheduler. It proves a closed form for `sum_of_nats` and properties of a parallel reduce.

Not in experiments 1–2: the evaluator is the contribution; there is no standalone theorem.

## Experiment 3 — the model built the tool from the paper

The model received `exp3/prompt.txt`: the paper's text (links to the authors' code removed) and a numbered
list of requirements. Its work is in `exp3/solution/`. The grader is [`tools/graders/tool-erlang/`](../tools/graders/tool-erlang/);
its `CHECKLIST.md` says how to judge each MANUAL requirement.

**Result:** 1 PASS (certification), 6 MANUAL, 0 FAIL. The named theorems exist and the closed form for `sum-of-nats` follows from the model's theorem.

**To review:** R1–R6: the paper fixes few names and interfaces, so a person checks the front end, the evaluator, the fairness constraint, the examples and the theorem statements. The authors' code (github.com/KuterBora/Erlang-in-ACL2) renames some functions: `eval-cont-list` is `apply-k`.
