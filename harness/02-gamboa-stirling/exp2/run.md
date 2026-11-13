# 02 Stirling — Experiment 2, attempt 1

## Run
- Model time: 3 h 30 min. Tool calls: 222.
- Ended normally (the model finished and printed or reported its solution).

## Audit
```
$ python3 -I tools/audit.py <transcripts> task-02
task-02: CLEAN  pages=11 run_tool_calls=222 run_end=2026-11-13T03:26:59.799744Z post_run_calls=0 flags=0

transcript complete (oldest page reached): True
tool calls in the run: 222
tools used: Bash, Read
server-side web search/fetch counters checked in 1 result event(s): all zero
```

## How solution.lisp was recovered
Taken from the single fenced `lisp` block of the final message (1743 lines), which matches the
model's last reads of `/work/solution.lisp`.

## Checker
`tools/check-exp2.py`: **CERTIFIED** with ACL2(r) 8.7; every target matched (390.7 s).

## Approach (from the transcript)
- Built the proof from scratch. It used `nonstd/nsa/derivatives` (mean value theorem) and the
  Reid–Gamboa differentiator books `sin-cos-minimal` and `ln-derivative-real`.
- It proved one generic "nonnegative derivative implies nondecreasing" theorem by functional instantiation of
  `mvt-theorem-sk`, and used it with 0-ary standard constants for parameterized instances (Wallis integrals Iₙ,
  log bounds).
- Wallis: antiderivatives Fₙ of sinⁿ, the recurrence for Iₙ, Iₙ₊₁ ≤ Iₙ, and a squeeze of W(n) for MAIN-3.
  Stirling: telescoping bounds on ℓ(n), a `defun-std` limit, and the constant identified through
  ln W(n) = 4ℓ(n) − 2ℓ(2n) − ln(4+2/n).
- All three theorems were proved in separate files after about 2 h. Merging them into one book took about
  1.3 h: in the combined book, rules from other sections made proofs hang. The model reordered sections and
  used `deftheory`/`in-theory` snapshots to restore each section's own theory.

## Notes
- The session's worker restarted once (infrastructure). The model noted that its files survived and
  continued.
