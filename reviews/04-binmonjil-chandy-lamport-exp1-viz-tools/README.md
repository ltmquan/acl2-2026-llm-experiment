# Tools behind `../04-binmonjil-chandy-lamport-exp1-commute.html`

- `model.js`: JavaScript port of `04-binmonjil-chandy-lamport/exp1/solution.lisp`, with the concrete functions of
  `../04-binmonjil-chandy-lamport-exp1-eval.lsp`. The page inlines this code: it is `template.html` with
  `/*MODEL*/` replaced by `model.js`, minus its first 4 comment lines and its export block.
- `gen.js`: writes `tests.lsp`, which checks the port against ACL2 on 41 executions: the example plus 40 random
  legal ones. It compares the final state, `pre-inputs`, `post-inputs`, `complete-segment-p` and `state-equiv` of the
  reordering. To run it, load `solution` and the `defattach` block of the eval file, then the generated forms. All 41
  printed `(t t t t t)` on ACL2 8.7.
- `swaps.js`: on 2,000 random segments (3,046 swaps), checks that every adjacent post/pre swap commutes, that every
  swapped order is legal, and that the final state is unchanged. All passed.
