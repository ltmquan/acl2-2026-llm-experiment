# 01 Basel — Experiment 1, attempt 1

## Run
- Model time: 52 min. Tool calls: 84.
- Ended normally (the model finished and printed or reported its solution).

## Audit
```
$ python3 -I tools/audit.py <transcripts> task-01
task-01: CLEAN  pages=5 run_tool_calls=84 run_end=2026-11-12T06:05:41.741750Z post_run_calls=0 flags=0

transcript complete (oldest page reached): True
tool calls in the run: 84
tools used: Bash
server-side web search/fetch counters checked in 1 result event(s): all zero
```

## How solution.lisp was recovered
The final message refers to the file printed by its last tool call
(`cat /work/solution.lisp`). `solution.lisp` is that output, verbatim. The model's own `cert.pl` run on
this file reported success.

## Checker
`tools/check-exp1.sh`: **CERTIFIED** with ACL2(r) 8.7 (133.8 s). No banned events; the last event is `(defthm MAIN …)`.

## Approach (from the transcript)
- Route: the elementary cosecant-sum proof (sometimes attributed to Cauchy), not the paper's route.
  1. sin x ≤ x and x cos x ≤ sin x on (0,2], from the alternating Taylor-series lemmas in `nonstd/nsa/trig-approx`
     with `defthm-std`. These give 1/x² ≤ csc²x ≤ 1 + 1/x² on (0, π/2).
  2. csc²(2y) = (csc²y + csc²(π/2−y))/4, so U(2M) = 4U(M) + 2 and U(2ⁿ) = ⅔(4ⁿ−1).
  3. A sandwich: π²/6 − 4/2ⁿ ≤ S_{2ⁿ−1} ≤ π²/6.
  4. Monotonicity, plus N = 2^⌈4/ε⌉ − 1, gives an ε–N statement for all n ≥ N.
- Difficulties: paren errors while patching files with Python; arithmetic-5 normalizing `expt` (it switched to
  its own `pow2`); sin²(π/4) = 1/2 under arithmetic-5; `defun-sk` witness plumbing for the final quantifiers.
  It used `arithmetic/top-with-meta` in a local encapsulate for the trigonometry and `arithmetic-5` elsewhere.
- It built the file in chunks with a check script, then concatenated them and certified with `cert.pl`.
