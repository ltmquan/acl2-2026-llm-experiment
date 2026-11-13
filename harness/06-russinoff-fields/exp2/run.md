# 06 Fields — Experiment 2, attempt 1

## Run
- Model time: 1 h 57 min. Tool calls: 237.
- Ended normally (the model finished and printed or reported its solution).

## Audit
```
$ python3 -I tools/audit.py <transcripts> task-06
task-06: CLEAN  pages=11 run_tool_calls=237 run_end=2026-11-13T01:47:35.330319Z post_run_calls=0 flags=0

transcript complete (oldest page reached): True
tool calls in the run: 237
tools used: Bash, Monitor, SendUserFile
server-side web search/fetch counters checked in 2 result event(s): all zero
```

## How solution.lisp was recovered
The final message did not contain the file, and the transcript stores only a 30,000-character
preview of the model's `cat`. `solution.lisp` was rebuilt by replaying all 230 shell commands in order (ACL2
runs stubbed out). The result is 3,101 lines and 133,566 bytes, exactly the size the session recorded for the
`cat` output, and the preview ends at the same point.

## Checker
`tools/check-exp2.py`: **CERTIFIED** with ACL2 8.7; every target matched (750.5 s).

## Approach (from the transcript)
- Built bottom-up in 12 staged books: base fields (Fermat for prime inverses), generic field lemmas, polynomial
  coefficient extensionality, convolution and ring laws, division, gcd/Bézout/inverses, MAIN-1 by induction on
  the tower, then evaluation, the factor theorem and `factorization`/`proots` (MAIN-2).
- MAIN-3 used coordinate vectors over f and a linear-dependence lemma for n+1 vectors of length n; applied to
  the powers of x this gives a nonzero polynomial, made monic, of whose irreducible factors x is a root.
- MAIN-4 by induction on the tower, grouping embeddings by their tails and using the MAIN-2 root bound.
- Early time went to waiting for community books to certify. The longest stalls were two ~10-minute hangs in
  the MAIN-3 part, which were killed and given new hints.

## Notes
- The model ended its first turn while waiting for a certification and was woken by its own `Monitor` tool
  (a local wait loop); it was not prompted by anyone. The audit therefore uses the whole transcript as the run.
- The final message claims the given `defs.lisp` had an unbalanced paren. It did not: the model dropped a paren
  when writing the file from the prompt. The checker uses its own copy, so this does not matter.
