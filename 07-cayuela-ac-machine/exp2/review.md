# 07 AC machine — Experiment 2, attempt 1

## Run
- Model time: 2.6 min. Tool calls: 18.
- Ended normally (the model finished and printed or reported its solution).

## Audit
```
$ python3 -I tools/audit.py <transcripts> task-07
task-07: CLEAN  pages=1 run_tool_calls=18 run_end=2026-11-12T23:57:42.831639Z post_run_calls=0 flags=0

transcript complete (oldest page reached): True
tool calls in the run: 18
tools used: Bash
server-side web search/fetch counters checked in 1 result event(s): all zero
```

## How solution.lisp was recovered
Taken verbatim from the `lisp` block of the final message.

## Checker
`tools/check-exp2.py`: **CERTIFIED** with ACL2(r) 8.7; every target matched (1.5 s).

## Approach (from the transcript)
- MAIN-1: the key lemma (acl2-sqrt 3)² = 3 via `sqrt-sqrt`, restated with `expt` because arithmetic-5
  normalizes x·x to (expt x 2); then automatic.
- MAIN-2: proved with no hints.
- MAIN-3: from the hypothesis, ω = (−1/2, s) with s² = 3/4 (s = 0 is excluded because 1+c+c² has no real
  root), then a polynomial collapse lemma.
- MAIN-4: cos and sin of 2π/3 from the trig book's π/3 values and π−x identities, then the collapse lemma.
