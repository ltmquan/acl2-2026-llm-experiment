# Tools behind `../04-binmonjil-chandy-lamport-exp1-commute.html`

- `model.js`: JavaScript port of `04-binmonjil-chandy-lamport/exp1/solution.lisp`, with the concrete application
  functions of `../04-binmonjil-chandy-lamport-exp1-eval.lsp`. It defines four topologies (`CONFIGS`):
  - `consistent`: the original;
  - `duplicates`: duplicate ids and neighbours;
  - `out-not-in`: 1 sends to 2, but 2 doesn't list 1 as incoming;
  - `outside`: neighbours that are not processes.

  The page inlines this code: the page is `template.html` with `/*MODEL*/` replaced by the lines of `model.js` from
  `class Pair` up to, but not including, the export block.
- `gen.js`: writes `tests.lsp`, checking the port against ACL2 on 41 executions in the consistent topology. It
  compares the final state, `pre-inputs`, `post-inputs`, `complete-segment-p` and `state-equiv` of the reordering.
  Load it after `solution` and the `defattach` block of the eval file. All 41 printed `(t t t t t)` on ACL2 8.7.
- `gen-topologies.js`: writes `tests-topologies.lsp`, which attaches each topology with `defattach` and runs the
  same comparison on 30 random executions per topology. Load it after `(include-book "solution")`. All 120 printed
  `(T T T T T)`.
- `swaps.js`: on 2,000 random segments in the consistent topology (3,046 swaps), checks that every adjacent post/pre
  swap commutes, that every swapped order is legal, and that the final state is unchanged. All passed.
- `explore.js`: the same check with random segments in each topology (3,000 per topology).
- `exhaustive.js [maxlen]`: enumerates every legal segment of up to `maxlen` inputs (default 7) from the page's
  starting state, in each topology. For every complete segment it checks `MAIN`'s conclusion, equality of the
  final states and legality of the reordered run, and on every segment it checks that all swaps commute. Results
  for `maxlen` = 7 are in section 5 of the page; all checks passed, and the `outside` topology has no complete
  segments.
