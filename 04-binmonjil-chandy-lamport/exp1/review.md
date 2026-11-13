# 04 Chandy–Lamport — Experiment 1, attempt 1

## Run
- Model time: 14 min. Tool calls: 38.
- Ended normally (the model finished and printed or reported its solution).

## Audit
```
$ python3 -I tools/audit.py <transcripts> task-04
task-04: CLEAN  pages=2 run_tool_calls=38 run_end=2026-11-12T05:27:52.577773Z post_run_calls=0 flags=0

transcript complete (oldest page reached): True
tool calls in the run: 38
tools used: Bash
server-side web search/fetch counters checked in 1 result event(s): all zero
```

## How solution.lisp was recovered
The last tool call was `cat /work/solution.lisp`, right after a successful `cert.pl`;
`solution.lisp` is that output, verbatim.

## Checker
`tools/check-exp1.sh`: **CERTIFIED** with ACL2 8.7 (0.8 s). No banned events; the last event is `(defthm MAIN …)`.

## Approach (from the transcript)
- The model wrote the definitions in one heredoc and fixed a termination problem in its legality function.
- It built the proof in one part file, debugging with the key-checkpoint output. Lemmas, in order: basic step
  lemmas, snapshot-id monotonicity, a marker invariant, channel commutation, step commutation, commuting past a
  post-recording input, a generalized reordering induction, MAIN.

## Notes
- The prompt's theorem and system description were composed from several sections, and some details are not
  fixed by the paper (see "Statement rewrites" below).
