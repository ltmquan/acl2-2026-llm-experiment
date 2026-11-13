# 05 Linear III — Experiment 2, attempt 1

## Run
- Model time: 55 min. Tool calls: 194.
- Ended normally (the model finished and printed or reported its solution).

## Audit
```
$ python3 -I tools/audit.py <transcripts> task-05
task-05: CLEAN  pages=8 run_tool_calls=194 run_end=2026-11-13T00:55:30.273271Z post_run_calls=0 flags=0

transcript complete (oldest page reached): True
tool calls in the run: 194
tools used: Bash, Read, Write
server-side web search/fetch counters checked in 1 result event(s): all zero
```

## How solution.lisp was recovered
The final message did not include the file; the model printed it with `cat`, whose output
is not in the saved transcript. `solution.lisp` was rebuilt by replaying, in order, all of the model's file
writes and file-changing shell commands (ACL2 runs stubbed out). The result is 2,038 lines and 92,561 bytes,
matching the size the model reported.

## Checker
`tools/check-exp2.py`: **CERTIFIED** with ACL2 8.7; every target matched (3.6 s).

## Approach (from the transcript)
- The proofs reduce independence to matrix rank, using the row-reduction theorems of Parts I–II and a new
  `fcomb` (row vector times matrix).
- The V-space lemmas were written once; the W copies were made by a Python renaming script (duplicated text,
  not functional instances).
- MAIN-3 by induction along `extend-to-basis`; MAIN-1/2 through the rank of `lin-mat` and `lin-inv`; MAIN-4
  by a rank bound on independent lists in a span; MAIN-5 from the RREF of the transposed `lin-mat`; MAIN-6
  from MAIN-5 and `extend-to-basis`.
- Certifying community books took the first ~15 minutes, then ~140 edit/test cycles, mostly on MAIN-5 and
  MAIN-6.

## Notes
- Proving the targets on 8.7 needs Part II lemmas that are only on master (e.g. `sol0p`, `flist-minus`); the
  model had to re-derive what it needed.
