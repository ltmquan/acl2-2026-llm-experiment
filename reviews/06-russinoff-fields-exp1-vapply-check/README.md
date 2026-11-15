# Checks of `vapply`, `pmod` and `pdivides` in `06-russinoff-fields/exp1/solution.lisp`

- `gen.py [out.lsp]`: writes 2,000 ACL2 checks against an independent reference (schoolbook multiplication and
  long division, written in Python). The cases cover the base fields F₂, F₅, F₇ and Q, with monic p of degree 1–5
  and random a and v. Each case checks three things: `vapply` = (a·v) mod p, `pmod` = a mod p, and `pdivides`. 400
  of the cases have p genuinely dividing a. Run it with `python3 -I gen.py cases.lsp`, then feed
  `(include-book "solution")` followed by `cases.lsp` to ACL2 8.7. All 2,000 printed `(T T T)` or `(T)`.
- `off-domain.lsp`: the two kinds of input where the routines differ from the reference.
  - Non-monic p = 2x² + 1: `pmod` of x² gives −1, while the true remainder is −1/2.
  - A vector with 3 coefficients for deg p = 2: `vapply` returns it unreduced.

  Neither kind can reach `MAIN`.
