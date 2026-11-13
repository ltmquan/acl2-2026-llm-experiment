# 03 Flip graph — Experiment 2, attempt 1

## Run
- Model time: 58 min. Tool calls: 166.
- Ended normally (the model finished and printed or reported its solution).

## Audit
```
$ python3 -I tools/audit.py <transcripts> task-03
task-03: CLEAN  pages=7 run_tool_calls=166 run_end=2026-11-13T00:59:37.059026Z post_run_calls=0 flags=0

transcript complete (oldest page reached): True
tool calls in the run: 166
tools used: Bash, Read, Write
server-side web search/fetch counters checked in 1 result event(s): all zero
```

## How solution.lisp was recovered
The final message did not repeat the file. `solution.lisp` was rebuilt from the model's three
`Read` calls of `/work/solution.lisp` at the end (lines 1–900, 900–2199, 2199–3420; the overlaps agree and
there are no gaps).

## Checker
`tools/check-exp2.py`: **CERTIFIED** with ACL2 8.7; every target matched (56.1 s).

## Approach (from the transcript)
- A layered development: obag extensionality and algebra, bit-matrix algebra, single and derived
  flip/plus moves with a frame lemma, then the pair construction {X, X} for any summand.
- MAIN-1, constructively: a span lemma (every matrix is a sum of scheme components, using n ≥ 2), adding pairs
  for S2, splitting leftovers into unit pieces by multilinearity, cancelling even-multiplicity pieces.
- MAIN-4 via a linear-form/output-index round trip; MAIN-2 by evaluation on unit-matrix pairs plus an n⁶
  tensor extensionality lemma; MAIN-3 via bilinearity and unit decomposition.
- Friction was routine ACL2 work (rule interference, backchaining, induction schemes, free-variable binding).
  The MAIN-1 cancellation phase took longest.
