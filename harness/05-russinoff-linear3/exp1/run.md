# 05 Linear III — Experiment 1, attempt 1

## Run
- Model time: 16 min. Tool calls: 53.
- Ended normally (the model finished and printed or reported its solution).

## Audit
```
$ python3 -I tools/audit.py <transcripts> task-05
task-05: CLEAN  pages=3 run_tool_calls=53 run_end=2026-11-12T05:31:50.725085Z post_run_calls=0 flags=0

transcript complete (oldest page reached): True
tool calls in the run: 53
tools used: Bash, Read, Write
server-side web search/fetch counters checked in 1 result event(s): all zero
```

## How solution.lisp was recovered
The final message prints the complete file; it is byte-identical to the model's last read
of `/work/solution.lisp`.

## Checker
`tools/check-exp1.sh`: **CERTIFIED** with ACL2 8.7 (1.2 s). No banned events; the last event is `(defthm MAIN …)`.

## Approach (from the transcript)
- Route: a field layer; the coordinate space Fⁿ with Gaussian elimination; a generic space G; V and W by
  functional instantiation of G; then T and MAIN.
- Brief struggles: Fⁿ lemmas, one ACL2 run that hit the model's own 120 s timeout (it killed the run and added
  a lemma), and a paren typo in a hint.
