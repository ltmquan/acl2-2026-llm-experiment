# 07 AC machine — Experiment 1, attempt 1

## Run
- Model time: 6 min. Tool calls: 41.
- Ended normally (the model finished and printed or reported its solution).

## Audit
```
$ python3 -I tools/audit.py <transcripts> task-07 --until=task-07@2026-11-12T04:22:57.393886Z
task-07: CLEAN  pages=3 run_tool_calls=41 run_end=2026-11-12T04:22:57.393886Z post_run_calls=1 flags=0

transcript complete (oldest page reached): True
tool calls in the run: 41
tools used: Bash
server-side web search/fetch counters checked in 2 result event(s): all zero
calls after the run (not part of the run): 1
```

## How solution.lisp was recovered
This was the pilot run, before the prompt asked the model to print the file. The session
declined our later request to print it (it treated the request from another session as untrusted), so
`solution.lisp` was rebuilt from the file writes in the transcript.

## Checker
`tools/check-exp1.sh`: **CERTIFIED** with ACL2(r) 8.7 (7.1 s). No banned events; the last event is `(defthm MAIN …)`.

## Approach (from the transcript)
- The model used ACL2(r) with the real `acl2-exp` (complex exponential) and `acl2-pi`, so √3 never appears as
  a free variable; cos and sin of 2π/3 are derived from library facts, not assumed.

## Notes
- Pilot run: the prompt lacks the final "print the file" sentence of the other prompts. The audit cut-off is
  the end of the model's run; one later tool call (after our request) is excluded.
