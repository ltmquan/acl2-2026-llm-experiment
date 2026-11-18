# fw-ftc-macro: what a person must inspect

## R1-M: the failed obligation is printed (R1 is MANUAL once every mechanical check passes)
The grader runs, in a plain ACL2(r) session, `(def-ftc-integral gr-bad1 :integrand (lambda (x) (* 2 x))
:antiderivative (lambda (x) (* x x x)) :domain (interval nil nil))` after including the macro, and saves the
output as `grader-logs/r1-failed-call.log`. Decide:
- PASS if the call stops with an ACL2 error (not a raw Lisp error or a hang) whose message shows the derivative
  obligation that could not be proved: the prompt's derivative form with F = (lambda (x) (* x x x)) and
  f = (lambda (x) (* 2 x)) substituted (or the same with the lambdas applied/beta-reduced). Prover output for a
  failed `defthm` alone, without the macro's own error that prints the obligation, does not count.
- FAIL otherwise.
Also skim `def-ftc-integral.lisp`: the generated `int-NAME` must be the library-style integral (no `defaxiom`,
`skip-proofs`, or a definition of `int-NAME` by its closed form). The mechanical body checks already enforce
the ftc-2.lisp shapes; this is a sanity look.

## R2-e (only if R2 prints MANUAL)
If the must-fail call's integrand or antiderivative could not be evaluated numerically (symbols, or functions
other than + - * / expt), confirm by reading `tests.lisp` that its antiderivative is mathematically wrong for its
integrand on its domain, and that the call is otherwise well-formed (so it fails for the wrong antiderivative,
not for a syntax error). PASS if so.
