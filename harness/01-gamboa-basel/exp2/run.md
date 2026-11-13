# 01 Basel — Experiment 2, attempt 1

## Run
- Model time: 28 min. Tool calls: 120.
- Ended normally (the model finished and printed or reported its solution).

## Audit
```
$ python3 -I tools/audit.py <transcripts> task-01
task-01: CLEAN  pages=5 run_tool_calls=120 run_end=2026-11-13T00:26:25.564040Z post_run_calls=0 flags=0

transcript complete (oldest page reached): True
tool calls in the run: 120
tools used: Bash
server-side web search/fetch counters checked in 1 result event(s): all zero
```

## How solution.lisp was recovered
Taken from the fenced `lisp` block of the final message, which the model printed right after
`cat solution.lisp` in its last tool call.

## Checker
`tools/check-exp2.py`: **CERTIFIED** with ACL2(r) 8.7; every target matched (11.6 s).

## Approach (from the transcript)
- Built the proof from scratch, using an elementary argument (often credited to Hofbauer). The sine bounds
  x − x³/6 ≤ sin x ≤ x come from the alternating-series Taylor facts in `nonstd/nsa/trig(-approx)` via
  `defthm-std`, and give csc² bounds.
- A doubling identity for csc², plus split/reverse/reflect lemmas, gives closed forms for csc² sums at powers of
  two. This bounds the odd-square sums and gives π²/6 − 12/k ≤ Σ_{j≤k} 1/j² ≤ π²/6. MAIN-1 then follows by
  an infinitesimal argument.
- The model reported that plain arithmetic lemmas were very slow under arithmetic-5, so it mostly used
  `arithmetic/top-with-meta`, with tau toggled per section.
- It developed the proof in separate files and concatenated them in the last minutes, wrapping each in
  `(encapsulate () …)` so that local libraries stay scoped.

## Notes
- **Checker change.** The model wrapped each section of its file in `(encapsulate () …)`, so MAIN-1 sits inside
  the last (non-local) `encapsulate`, not at the top level. The first version of `check-exp2.py` looked only at top-level events and reported
  `TARGET-MISMATCH: missing main-1`. We then changed the checker to also accept a target exported from an
  `encapsulate` or `progn` at any depth, but never one under `local`. We tested that a local MAIN is still
  rejected. With this change the unchanged solution passes. An extra book that includes the solution and
  proves the target statement `:by main-1` also certified, which confirms that MAIN-1 is exported with
  exactly the target statement.
