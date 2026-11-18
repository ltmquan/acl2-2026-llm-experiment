# 16 — Kaufmann — set theory in ACL2

**Author:** Matt Kaufmann.

ACL2(zfc): ZF set theory in ACL2 through the community books `projects/set-theory`. Its `zfc-future-work` documentation topic lists open items; this folder takes the tractable ones. There is no PDF here: the source is the list in the books (base commit 65589c5afd, same content on master).

Not in experiments 1–2: an extended abstract on the integration of set theory into ACL2.

## Experiment 4 — future work

### ZFC future-work items T1–T11

One folder per item, `exp4/zfc-tN/`: prompt, our definitions, targets (`optional.lisp` for T3(e)), and the model's work (`solution/`). Checked by `tools/check-prove.py` on ACL2 master.

| Item | Topic | Result |
|---|---|---|
| T1 | equivalence relations, quotients | 6 / 6 |
| T2 | indexed Cartesian products | 4 / 4 |
| T3 | filters and ultrafilters | 5 / 5, and the optional non-principal ultrafilter on ω |
| T4 | cardinality basics | 10 / 10 |
| T5 | transfinite recursion | 2 / 2 |
| T6 | infinite Ramsey | 2 / 2 |
| T7 | topology | 4 / 4 |
| T8 | groups | 7 / 8; `zfc-t8-r2` (corrected statement): 8 / 8 |
| T9 | fields, ℂ as pairs | 1 / 3; `zfc-t9-r2` (corrected statement): 3 / 3 |
| T10 | metric spaces | 3 / 3 |
| T11 | ultraproducts | 2 / 2 |

T8 and T9: two of our statements were false, and the first-run models found it. See [EXPERIMENT-4.md](../EXPERIMENT-4.md#two-of-our-statements-were-wrong).

**To review:** whether each statement captures its item on the list.
