# fw-multisets

- Task folder: [`15-jurgensen-treesets/exp4/multisets/`](../../../../15-jurgensen-treesets/exp4/multisets/) (prompt, our files, and the model's work under `solution/`)
- Model run: 2026-11-14 19:04 to 2026-11-14 19:15 UTC, 11 min, 52 tool calls.
  First attempt; no retry.
- Saved by the model with `submit fw-multisets` to branch `results/fw-multisets` of this repository.
- Audit (`audit.txt`): CLEAN.

## Grade

```
R1 FAIL grade-r1-thms: GR-SUPPORT-IS-KEYS: not proved
R2 PASS 59 assertions cover all 20 functions
R3 PASS
SUMMARY fw-multisets: 2 PASS, 1 FAIL, 0 MANUAL
```

Full output: `grade.txt`.

## Review

R1 reported FAIL on one of its 110 checks, `gr-support-is-keys`. Review: the model defines
`support` as `(omap::keys (bfix b))`, so the statement holds by definition. It fails only because the
grader's hint policy disables the required definitions. It proves at once with `support` enabled:
`(defthm ... (implies (bagp b) (equal (support b) (omap::keys (bfix b)))) :hints (("Goal" :in-theory (enable support))))`
certifies on top of the model's book. Counted as passed; the other 109 checks passed.
