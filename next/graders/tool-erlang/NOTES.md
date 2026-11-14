# tool-erlang grader: notes

## Files
- `grade.sh <work-dir>` runs `grade.py` (python3 -I). It copies the work dir (without .cert, .port,
  compiled or .beam files), scans for banned events, certifies every model .lisp with cert.pl and the
  default flags, then certifies the grader books in `<copy>/grader/` and prints R1..R7.
- `books/grader-util.lisp`: finds a function or macro by *name* in any known package. The model may
  put the paper's names (eval-cont-list, sum-of-nats, ...) in its own package, so our books never
  read a model symbol; they intern at run time.
- `books/grade-r2.lisp` (includes ../examples): `eval-cont-list` is a unique, logic-mode, recursive
  function.
- `books/grade-r3.lisp` (includes ../examples and ../reduce): at least one constrained function has an
  attachment that was not present before the model's books were included. The pairs are printed.
- `books/grade-r5.lisp` (includes ../sum-of-nats): sum-of-nats, sum-test-world-p, erl-val-integer->val
  and eval-cont-list are logic-mode functions, make-erl-val-integer is a macro or function, and
  `(sum-of-nats k)` = k(k+1)/2 for k = 0..30.
- `books/grade-r6.lisp` (includes ../reduce): wtree-p and create-wtree are logic-mode functions.
- `erlang/`: the paper's Erlang programs, transcribed from the PDF (pdftotext drops underscores:
  "sum of nats" is `sum_of_nats`, "is integer" is `is_integer`, "helper( , [])" is `helper(_, [])`).
  Only `-module`/`-export` lines were added. Also `subset.erl` (ours), one function per construct of
  R1. All compile with erlc (OTP 25.3) and give the values listed in CHECKLIST.md.

## Requirement table
| R | how | mechanical part | manual part |
|---|-----|-----------------|-------------|
| 1 | MANUAL | README.md exists | run front end on `2 + 2.` and erlang/*.erl |
| 2 | MANUAL after mech. | grade-r2 | fuel, out-of-fuel status, receive yields |
| 3 | MANUAL after mech. | grade-r3 (attachment to a constrained fn) | constraint = fairness |
| 4 | MANUAL after mech. | examples certifies, ≥3 assert forms | the three runs and their expected values |
| 5 | MANUAL after mech. | grade-r5, a defthm in sum-of-nats.lisp | main theorem shape, linear fuel, non-vacuity |
| 6 | MANUAL after mech. | grade-r6, ≥3 defthms in reduce.lisp | the three properties, over the constrained scheduler |
| 7 | PASS/FAIL | all .lisp certify, no banned events | — |

## Interpretations
- The paper fixes too few interfaces (the calling convention of eval-cont-list, the representation of
  states and worlds, the scheduler's name) to restate its theorems, so R2–R6 are MANUAL after the
  mechanical preconditions, with exact procedures in CHECKLIST.md.
  The fixed names are checked mechanically: eval-cont-list, sum-of-nats, sum-test-world-p,
  erl-val-integer->val, make-erl-val-integer, wtree-p, create-wtree. Paper-named lemmas such as
  eval-sum-of-nats-induct are not required, because R5 does not ask for them.
- The scheduler encapsulate name is not fixed, so R3 looks for any constrained function, introduced by
  the model's books, with an attachment.
- Figure 2 (`add_pairs_nd`) is not used: the paper's own code has a syntax error
  (`List1, List2 = lists:split(...)`, which needs `{List1, List2}`), and no requirement uses it.
- The two-process exchange of 4.3 (Joe-Robert) has no source in the paper. Any program of that shape
  counts (CHECKLIST R4).
- Banned: everything in check-prove.py's list, all trust-tag machinery (the prompt forbids trust tags
  here), `:ttags` and `:skip-checks` anywhere, and cert-flags that allow skip-proofs, defaxioms or ttags.
  Atoms inside `defpkg` import lists are ignored.

## Validation (scratch only)
- The Erlang files compile and run with OTP 25 (`erlc`, `erl -noshell`). add_pairs gives [3,7,11,15],
  sum_of_nats(10) gives 55, and `2 + 2.` parses to `{op,1,'+',{integer,1,2},{integer,1,2}}`.
- A stub work dir: package "ERL" (to test cross-package lookup), a trivial eval-cont-list with fuel, a
  constrained scheduler with defattach, sum-of-nats and the paper's other names, wtree-p/create-wtree
  and 3 trivial theorems. Result: R1–R6 MANUAL, R7 PASS; grade-r3 printed `((ERL::SCHEDULER .
  ERL::SCHEDULER-EXEC))`.
- A bad stub, varied over runs: eval-cont-list in program mode → R2 FAIL; no defattach → R3 FAIL; only 2
  asserts → R4 FAIL; sum-of-nats off by one → R5 FAIL ("does not compute N(N+1)/2"); a defttag in
  reduce.lisp → BANNED and R7 FAIL; a book that does not certify → dependent requirements FAIL and the
  dependent grader books are skipped.
- Not validated: the model's front-end interface (unknown in advance), hence R1 is MANUAL.

## Possible prompt issues
- R5 says "proves the theorem of Section 4.1 (equation 1)". The paper states equation 1 informally, so
  the exact statement is up to the model. This is graded by hand.
- Figure 1 uses `spawn` inside the program, but Section 3.1 says the authors' evaluator cannot spawn
  during evaluation. R4 requires add_pairs to run to [3,7,11,15], so the model must support spawn
  (or pre-spawn the server). The model is not told which, and both are accepted in CHECKLIST R4.
