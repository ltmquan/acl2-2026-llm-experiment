# 04 Chandy–Lamport — Experiment 2, attempt 1

## Run
- Model time: 25 min. Tool calls: 85.
- Ended normally (the model finished and printed or reported its solution).

## Audit
```
$ python3 -I tools/audit.py <transcripts> task-04
task-04: CLEAN  pages=4 run_tool_calls=85 run_end=2026-11-13T00:31:45.700208Z post_run_calls=0 flags=0

transcript complete (oldest page reached): True
tool calls in the run: 85
tools used: Bash, Read, Write
server-side web search/fetch counters checked in 1 result event(s): all zero
```

## How solution.lisp was recovered
Taken verbatim from the `lisp` block of the final message (1063 lines).

## Checker
`tools/check-exp2.py`: **CERTIFIED** with ACL2 8.7; every target matched (4.0 s).

## Approach (from the transcript)
- The model put every relevant system step into a canonical "update one process, pop one incoming channel
  head, append to outgoing channels" form, and proved a pairwise commutation lemma under a non-empty-channel
  side condition.
- MAIN-2 follows from that lemma and the marker-in-transit premise. MAIN-1 uses a list-commutation lemma and
  an induction invariant (markers in transit, absence of the target snapshot id, legality of replayed
  receives, no repeats in the cut-not-taken list).
- Most iterations were on the marker-invariant step; its proof output reached about 50k lines and had to be
  split into case lemmas.

## Notes
- The session's worker restarted once (infrastructure), after the file had certified. The resumed turn
  re-certified the file and printed it.
