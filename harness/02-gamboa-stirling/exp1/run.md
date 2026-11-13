# 02 Stirling — Experiment 1, attempt 1

## Run
- Model time: 58 min. Tool calls: 183.
- Ended normally (the model finished and printed or reported its solution).

## Audit
```
$ python3 -I tools/audit.py <transcripts> task-02
task-02: FLAGGED  pages=8 run_tool_calls=183 run_end=2026-11-12T06:14:58.355912Z post_run_calls=0 flags=1
    - network-like pattern pip @ 2026-11-12T05:24:56.575106Z Bash {"command": "pip install sympy 2>&1 | tail -1; python3 -c \"\nimport sympy as sp\nn=sp.symbols('n',positive=True)\ny=2*(n**2+n+1)/((2*n+1)*n*(n+1))\ne=sp.factor

transcript complete (oldest page reached): True
tool calls in the run: 183
tools used: Bash
server-side web search/fetch counters checked in 1 result event(s): all zero
```

## How solution.lisp was recovered
At the end the model printed `/work/solution.lisp` in four `sed -n` chunks. `solution.lisp` is
those four outputs joined; the line counts match the ranges and nothing was cut off.

## Checker
`tools/check-exp1.sh`: **CERTIFIED** with ACL2(r) 8.7 (45.9 s). No banned events; the last event is `(defthm MAIN …)`.

## Approach (from the transcript)
- Route:
  1. bounds on partial sums of the exp series, transferred with `defthm-std`;
  2. A(n) = (n!)² e^{2n}/n^{2n+1} is decreasing and A(n)e^{−2/n} is increasing, so A(n) ≈ A(m) for infinite n, m;
  3. Wallis integrals as standard parts of hyperfinite sums, with a discrete integration by parts for
     sinᵐcos, giving I₀ = π/2, I₁ = 1, the recurrence and monotonicity;
  4. the Wallis bounds 2/(2k+1) ≤ π p_k² ≤ 1/k;
  5. A(m) ≈ 2π, so the ratio is ≈ 1 for i-large n, and transfer gives an ε–N MAIN.
- It worked in separate books and merged them, then fixed one rewrite loop caused by the new order.
- Struggles were local: arithmetic-5 loops and reasoning about `abs`.

## Notes
- **Audit finding.** About 9 minutes in, the model ran `pip install sympy` (downloaded from PyPI) and used it
  once, as a scratch calculator, to factor one algebraic expression while planning a lemma. The certified file
  proves that step, like every step, in ACL2, so sympy cannot affect correctness. The model fetched no
  information about the problem. This breaks the prompt's "no internet" rule. The team has to decide whether
  to count the run with a footnote or rerun it.
