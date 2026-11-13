# 03 Flip graph — Experiment 1, attempt 1

## Run
- Model time: 50 min. Tool calls: 177.
- Ended normally (the model finished and printed or reported its solution).

## Audit
```
$ python3 -I tools/audit.py <transcripts> task-03
task-03: CLEAN  pages=7 run_tool_calls=177 run_end=2026-11-12T06:05:37.978762Z post_run_calls=0 flags=0

transcript complete (oldest page reached): True
tool calls in the run: 177
tools used: Bash
server-side web search/fetch counters checked in 1 result event(s): all zero
```

## How solution.lisp was recovered
The model's final `cat` was cut off by the harness, so it printed the file again in five
`sed -n` chunks. `solution.lisp` is those chunks joined: exactly 1750 lines, ending with MAIN.

## Checker
`tools/check-exp1.sh`: **CERTIFIED** with ACL2 8.7 (26.7 s). No banned events; the last event is `(defthm MAIN …)`.

## Approach (from the transcript)
- A direct constructive proof:
  1. create and cancel identical pairs;
  2. steer a pair to any rank-one t with a catalyst summand, using that each E_x is an XOR of factors of the
     scheme (n ≥ 2 gives two summands with different A-factors);
  3. expand terms into elementary terms when the standard scheme S0 is present;
  4. route S → S⊎S0⊎S0 → S0 → S0⊎T⊎T → T.
- It worked in 13 incremental part files, with many short fix-and-retry cycles.

## Notes
- For comparison: the paper reports that its connectivity proof is 19 books with 137 functions and 527
  theorems, and that an unassisted LLM formalization of the companion paper proved connectivity in 9 books
  with 409 theorems.
