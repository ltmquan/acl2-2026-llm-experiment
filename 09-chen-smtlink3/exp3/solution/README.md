# Smtlink 3: rewrite-driven compilation to SMT-LIB (reimplementation)

This directory is my own ACL2 implementation of the system described in
"Smtlink 3: Rewrite-driven Compilation to SMT-LIB" (Chen, Greenstreet and
Seltzer, ACL2-2026). The authors' code was not used. The `:smtlink` hint
translates an ACL2 goal to SMT-LIB with a chain of clause processors. All of
them are verified except the last one, which writes an SMT-LIB script
(logic `AUFNIRA`) and runs Z3.

## Files

| File | Contents |
|------|----------|
| `package.lsp`, `cert.acl2`, `*.acl2` | The `SMT` package and the certification setup. |
| `base.lisp` | Tag functions, the evaluator `SMT-EV`, typed terms, smt-judgements, `SMT-JUDGEMENT->EXPR`. |
| `cps.lisp` | The verified clause processors, each proved correct against `SMT-EV` with a `:clause-processor` rule. |
| `smt-theory.lisp` | The `rational-+`, `rational--`, `rational-*`, `rational-/`, `rational-<` encapsulate of Section 5.4, with its `return-of-...` and `specialize-...` theorems. |
| `trusted.lisp` | The only trusted code and the only book with a trust tag: the SMT-LIB translator, the Z3 call, and `def-smt-array`. |
| `smtlink.lisp` | The top-level book: the computed hint that calls `rewrite$` and drives the chain, and the `:smtlink` custom keyword hint. |
| `examples.lisp` | The examples from the paper (see below). |

Certify everything with `cert.pl examples.lisp`, which takes about 15 seconds.

## Using it

```lisp
(include-book "smtlink" :ttags ((:smtlink)))   ; package SMT must be defined (package.lsp)

(defthm name
  goal
  :hints (("Goal''" :smtlink (:translation-theory <theory expression>
                              :types (recognizer ...)      ; optional
                              :hypothesize (term ...)      ; optional
                              :print t                     ; optional
                              :smt-file "goal.smt2"        ; optional
                              :max-rounds 10               ; optional
                              :simplify-theory <theory>    ; optional, default (theory 'minimal-theory)
                              :smt-solver "z3"))))         ; optional
```

- **`:translation-theory`**: the theory that term rewriting uses (Section 5.4), for example
  `(union-theories (theory 'minimal-theory) '(smt::specialize-binary-rational-operators ...))`.
  The default is `(current-theory :here)`.
- **`:types`**: extra type recognizers for type inference. `booleanp`, `integerp` and
  `rationalp` are always included.
- **`:hypothesize`**: extra hypotheses (Section 4.1). For each hypothesis `h`, Smtlink adds the
  subgoal that the negation of the goal implies `h`.

## Printing the SMT-LIB script and the term after rewriting

Add **`:print t`** to the `:smtlink` hint. For that goal, Smtlink then prints:

- the term after each round of term rewriting (`Smtlink: term after rewriting`);
- the extracted smt-judgement (`Smtlink: smt-judgement`);
- the term after simplification (`Smtlink: term after simplification`);
- the SMT-LIB script sent to the solver, and the solver's answer (`Smtlink: SMT-LIB script`).

To keep the script in a file, add **`:smt-file "name.smt2"`**. The file is written to that path
and is not deleted. Without this option the script goes to a temporary file in `/tmp`, which is
removed afterwards.

If the solver does not answer `unsat`, the script is printed even without `:print t`.

For example:

```lisp
(thm (implies (and (integerp y) (= x (* 2 y))) (foo x y))
     :hints (("Goal" :smtlink (:translation-theory
                               (union-theories (theory 'minimal-theory)
                                               (cons 'foo smt::*rational-translation-rules*))
                               :print t))))
```

## Architecture (Figure 1 of the paper)

A goal inside Smtlink is a clause of the form
`((not (smtlink-goal 'info)) (not H) lit1 ... litn)`, where:

- `(smtlink-goal x)` is `t`, so the first literal is always false;
- `info` records the stage, the configuration and the computed data (typed terms, smt-judgement);
- `H` is the type-correctness hypothesis of the paper, `t` at first.

The computed hint `smt::smtlink-driver` is installed with `add-default-hints!`. It recognises
these clauses and applies the next clause processor. As Section 5.1 describes, it calls
`rewrite$` itself (a clause processor cannot call it) and passes the result to the next
clause processor as its hint. That clause processor then emits a side goal that re-checks the
result.

Side goals are tagged with `(not (smtlink-side 'theory))`. The driver strips the tag and proves
the side goal in the indicated theory.

1. **`smtlink-entry-cp`** (verified): puts the goal in clause form and adds the `:hypothesize`
   hypotheses.
   - Side goals: the clausified goal implies the original goal; and for each hypothesis `h`,
     `(or h goal)`.
2. **`type-inference-cp`** (verified, Section 5.2).
   - For each literal, the hint builds the term
     `(implies path-cond (and (ti-equal (hide (cdr (cons 'id (r x)))) (r x)) ...))` for every
     subterm `x` and every recognizer `r`. The other literals are assumed false.
   - It rewrites that term with `rewrite$` and reads off the judgements that became `t`.
   - The clause processor builds the typed terms (`judgements`, `smt-judgements`, `guts` fields,
     with ordered sets) and the hypothesis `H'`.
   - Side goal: `(or H' lit1 ... litn)`, i.e. the type judgements are correct.
3. **`type-fix-cp`** (verified, Section 5.3): selects one judgement per node, top-down. For
   function calls it uses typing theorems `(implies (and (r1 v1) ...) (r (f v1 ...)))` that it
   finds among the rewrite rules in the world.
4. **`term-rewrite-cp`** (verified, Section 5.4).
   - The hint rewrites each literal with `rewrite$`, using the `:translation-theory` and the
     judgements of that literal as hypotheses.
   - If the term changed, the new goal goes back to type inference, up to `:max-rounds` times.
     Side goal: `(or (not H) (not (or new-lits)) lits)`.
   - If the term did not change, the goal goes on to type extraction.
5. **`type-extract-cp`** (verified, Section 5.5).
   - Gathers the variable and function judgements into an smt-judgement
     `((vars ((name . x) (judgement . r)) ...) (fns ((name . f) (domain ...) (range . r)) ...))`.
     Ambiguous judgements are reported as errors.
   - Replaces `H` by `Tu = (smt-judgement->expr smtj)`.
   - Side goal: `(or (not H) Tu lits)`.
6. **`simplify-cp`** (verified, Section 5.5): the hint rewrites the literals under the variable
   judgements in `:simplify-theory`, which erases recognizers such as `(rationalp x)`.
   - Side goal: `(or (not Tu) (not (or new-lits)) lits)`.
7. **`smtlink-trusted-cp`** (trusted, Section 5.6).
   - Checks that the hypothesis is `(smt-judgement->expr smtj)`.
   - Translates the smt-judgement into declarations (`declare-sort`, `declare-fun`,
     `declare-const`) and the goal into `(assert (not ...))`, then runs `(check-sat)`.
   - The goal is proved **only if Z3 answers `unsat`**. In that case the clause processor returns
     the function judgements of the smt-judgement as new goals, since they must hold universally.
     `sat`, `unknown`, or any other output or error makes the proof fail.

## Trusted computing base

`trusted.lisp` (about 640 lines, including comments) is the only trusted code. The functions of
`smt-theory.lisp` are ordinary constrained functions. The trusted clause processor maps them to
`+ - * / <`, and their constraints make that mapping faithful on rationals. The soundness
argument is in the header of `trusted.lisp`.

The translator rejects goals that it could not translate faithfully:

- ill-sorted terms;
- lambdas;
- constants other than numbers and booleans;
- equalities between arrays, and arrays passed to uninterpreted functions.

Arrays (Section 5.7) are user-defined.

- **Registration:** `(smt::def-smt-array :recognizer ... :key-p ... :val-p ... :select ...
  :store ...)` proves the read-over-write and typing theorems and records the array theory in a
  table.
- **Check before use:** the trusted clause processor maps `:select`/`:store` to SMT-LIB
  `select`/`store` only after it checks that those exact theorems are in the world.

## Examples (`examples.lisp`)

- **`poly-ineq-example`**: the running example of Section 5, with the paper's `:smtlink` hint on
  `"Goal''"` and the translation theory of Section 5.4.
- **`poly-ineq-example-permuted`**: the same goal with its hypotheses permuted.
- **`poly-ineq-example-false`**: a false variant, wrapped in `must-fail`. Z3 answers `sat`.
- **`type-terse-example`**: the type-terse goal of Section 4.1,
  `(implies (and (integerp y) (= x (* 2 y))) (foo x y))`. Type inference gives `x` its type from
  the equality.
- **`hypothesize-example`**: uses `:hypothesize ((rationalp x))`. Type inference cannot derive
  this from `(pos-ratp x)`, and the proof fails without the hint.
- **`alist-to-array-example`**: the alist-to-array goal of Section 5.7. The translation theory
  contains `int-sym-top-down-translation-of-assoc-equal` and
  `int-sym-top-down-translation-of-acons`.
  - It converges on the term
    `(equal (int-sym-array-select (int-sym-array-store (int-sym-array-store (int-sym-array-from-al al) k2 (cons k2 v2)) k1 (cons k1 v1)) k1) (cons k1 v1))`.
  - The alist type and the lifting function are declared uninterpreted.

## Limitations

These match the paper or are simplifications of it:

- no FTY types;
- no counterexamples;
- no quantifiers;
- type recognizers must be unary;
- only the coercion Int to Real is supported between sorts.
