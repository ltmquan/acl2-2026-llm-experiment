# tool-smtlink3: manual checks

Run `grade.sh <work-dir>` first. It prints the grading copy (`<tmp>/work`), the certification logs, and
the Z3 call logs (`<tmp>/z3log/<book>/call-*/{args,input.smt2,output}`). A requirement reported `FAIL`
stays failed. Decide a `MANUAL` requirement only as described below. If an item cannot be decided,
record it as FAIL with the reason.

## R1: the chain of clause processors of Section 5 (grade.py: MANUAL when its mechanical checks pass)
Mechanical checks already done: smtlink.lisp certifies, `rewrite$` occurs in the model's code, and every
logged solver input contains `(check-sat)`.
Open `/work/smtlink.lisp` and the books it includes. PASS only if all of the following hold:
1. `:smtlink` is a hint (a custom keyword hint, or a computed/default hint keyed on it) that runs these
   stages in order:
   (a) type inference: a computed hint calls `rewrite$` on per-subterm type questions, and a clause
       processor takes the result as a hint (5.1–5.2);
   (b) type fixing or judgement selection (5.3);
   (c) term rewriting with the user's `:translation-theory` (5.4), with the rewritten term passed to a
       clause processor as an untrusted hint;
   (d) type extraction and simplification (5.5);
   (e) a final clause processor that writes SMT-LIB and runs `z3` (5.6).
   A stage may be split across several clause processors or merged with its neighbour (the paper has 6),
   but (a), (c) and (e) must be separate steps, and `rewrite$` must really be used for (a) and (c).
2. Python is not used anywhere: no `python` command, and no `.py` file in /work used by the tool.
   grade.py lists the files that mention "python". A mention in a comment or doc string is fine.
3. To see the stages in action, run `acl2` in `<tmp>/work`, then
   `(include-book "examples" :ttags :all)` and `(set-gag-mode nil)`, and resubmit poly-ineq-example under
   a new name. The proof output must show the clause-processor steps and the side goals.

## R2: only the final clause processor is trusted (MANUAL when the mechanical part passes)
Mechanical checks already done: exactly one `define-trusted-clause-processor` in the model's files.
Trust-tag machinery (defttag, sys-call*, progn!, raw mode, include-raw) appears only in that book F and in
model books that F includes. In an ACL2 world containing smtlink and examples, the trusted-cl-proc-table
holds exactly one clause processor (besides ACL2's own `proof-builder-cl-proc`), and it comes from F.
Every ttag in `ttags-seen` is reached through F. At least one `:clause-processor` rule (a verified
clause processor) exists. The `R2 world:` line lists them.
PASS only if:
1. Each stage (a)–(d) of R1 is carried out by a function that has a `:clause-processor` rule in the list
   printed by grade.py. Look up each rule with `:pe <rule>` and check that it is proved against an
   evaluator (defevaluator or similar) with the standard `(implies (and (pseudo-term-listp cl) (alistp a)
   (ev (conjoin-clauses (cp cl ...)) a)) (ev (disjoin cl) a))` shape, or the meta-extract variant.
2. The side goals described in the paper are returned:
   - type inference returns a clause asserting that the type annotations are correct (5.2);
   - rewriting returns a goal equating the original and rewritten terms under the type hypothesis
     (condition (2) of 4.2);
   - extraction returns the condition of (3) in 4.3.
   Read the clause-processor definitions to check this. They return a list of clauses; the side goals
   are the extra clauses.
3. The trusted book F (and the books it includes) does only SMT-LIB printing, running the solver and
   reading its answer. It must not redefine ACL2 functions in raw Lisp (`progn!`/raw mode used only to
   run a process or write a file).

## R3: unsat only, AUFNIRA (MANUAL only when the tool does not call `z3` through PATH)
Mechanical checks: grade-r3 proves the paper's goal and the false variant fails (Z3 answers sat).
grade-r3-unknown and grade-r3-error fail the paper's goal with a fake `z3` that answers `unknown` or
reports an error. Every captured script contains `(set-logic AUFNIRA)`.
If MANUAL: the tool probably calls Z3 by an absolute path or another route. Find the command in F, put a
fake solver at that location in a scratch copy (or edit the copy to call `z3` from PATH, changing nothing
else), and redo the two fake runs: `cert.pl` on `grader/grade-r3-unknown.lisp` and on
`grader/grade-r3-error.lisp`, with the fake first on PATH. PASS only if both books certify, so that the
proof fails, and the generated script contains `(set-logic AUFNIRA)`.
Use R8's printing facility to see the script.

## R4 (MANUAL only if Z3 is not called through PATH)
Confirm, as in R3, that Z3 is really called when grade-r4's proofs succeed (for example with a fake z3
that answers sat at the tool's solver location: grade-r4 must then fail).

## R5 (MANUAL when no counterexample is found)
grade.py evaluates the must-fail'd formula on a grid of rationals. If it finds no counterexample, check
by hand that the formula is false: give a point (x, y) that satisfies the hypotheses and violates the
conclusion, and check it with ACL2 using a `thm` on the instance or by evaluation. PASS if one exists.

## R6 (MANUAL when the model's own examples pass but grade-r6 fails)
grade.py has already found in examples.lisp a proved `:smtlink` theorem of the exact Section 4.1 shape
`(implies (and (integerp y) (= x (* 2 y))) (F x y))` and a proved theorem that uses `:hypothesize`.
grade-r6 restates the 4.1 goal with grader-foo (y^4 < 1 + x^2 y^2) and the paper's rational
translation theory. If grade-r6 failed, read `<tmp>/cert-grade-r6.log`:
- PASS if the failure is only because the tool needs an integer translation theory that the paper does
  not give. The model's F must then be a real arithmetic fact, not just `t` or a tautology the
  rewriter proves, and the model's README or examples must show that type inference derived the type of
  x (no hypothesis on x).
- FAIL otherwise (e.g. the tool cannot infer the type of x).
Also check that the model's `:hypothesize` example needs the hypothesis: the added hypothesis is used
in the SMT query, and the extra subgoal of 4.1 (negated goal implies the hypothesis) is generated and
proved. Run the example with `(set-gag-mode nil)` to see it.

## R7 (MANUAL when the model's example passes but grade-r7 fails)
grade.py has already found in examples.lisp a proof of the Section 5.7 goal, verbatim, whose only hints
are `:smtlink` hints naming `int-sym-top-down-translation-of-assoc-equal` and
`int-sym-top-down-translation-of-acons`. grade-r7 restates it with two candidate hints. If grade-r7
failed, PASS if:
(a) the model's own hint differs only by adding further user rules (types or returns rules for the
    int-sym-array functions);
(b) Z3 was called for the model's proof: rerun it with `(set-gag-mode nil)` or use R8, and the SMT-LIB
    script contains the array store/select terms; and
(c) the theorems named in the paper have the paper's statements (5.7).
Otherwise FAIL.

## R8 (always MANUAL)
Follow /work/README.md to print, for poly-ineq-example, (a) the SMT-LIB script and (b) the term after
rewriting. PASS if both are printed without editing the model's files, (a) is a complete script (set-logic
AUFNIRA, declarations, `(assert (not ...))`, `(check-sat)`) and (b) is an ACL2 term over
`smt::rational-+` etc. comparable to the paper's listing in 5.4.
