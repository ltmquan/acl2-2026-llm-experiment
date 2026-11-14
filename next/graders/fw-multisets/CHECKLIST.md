# fw-multisets: what a person must inspect

## R1-M: documented behavior on non-bags (R1 is MANUAL once every mechanical check passes)
Read `mset.lisp` (xdoc, `:short`/`:long`, or comments). PASS if, for the functions taking bags, it says what they
do on non-bags (e.g. "all functions fix their bag arguments with `bfix`, which maps a non-bag to the empty
bag"), including `insert-n` with a non-natural `n`. A single global statement is enough if it is accurate for
every function. FAIL if absent or contradicted by the definitions.

## When a theorem check prints GRADER-FAIL (optional override, to be recorded)
The grader proves each of our statements from the model's rules (hint policy in NOTES.md). If a statement
fails only because the model states it in a way that none of the attempts reaches (for example a theorem about
a fixed point `(bfix x)` that needs one rewrite the model left disabled), a person may accept it if a lemma of
the model, instantiated by hand, gives our statement directly (`:use` with an instance, no other hints, no
induction). Record the lemma and the instance in the grading notes; anything more than that is a FAIL.

## Extensionality / subbag completeness witness
`grade-r1-witness.lisp` is generated from the candidate witness functions found in `mset.lisp` (defun-sk skolem
functions, `defchoose`s, and 2-argument functions that are not required functions). If both theorems fail and
the model's witness is introduced some other way (e.g. by a macro), a person states the theorem with that
witness as in `grade-r1-witness.lisp` and applies the override rule above.
