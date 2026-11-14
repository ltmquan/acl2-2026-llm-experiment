# tool-erlang: manual checks

Run `grade.sh <work-dir>` first. It prints the grading copy (`<tmp>/work`), where every model book is
already certified, and the grader logs. A `FAIL` stays a fail. For each `MANUAL` line, follow the
procedure below. Do everything in `<tmp>/work` (a copy), never in the saved /work. If an item cannot be
decided, record FAIL with the reason. The Erlang inputs are in this directory under `erlang/`. They are
transcribed from the PDF; `subset.erl` is ours. All compile with `erlc` (OTP 25), and their expected
values are given below.

## R1: front end (MANUAL whenever README.md exists)
1. From /work/README.md copy (a) the exact command that turns a `.erl` file into ACL2 forms, and
   (b) the form(s) that load the converted module and the ACL2 form that runs a function of it on given
   arguments with given fuel under the executable scheduler. If the README lacks either, FAIL.
2. Use `run-erl.sh` from this directory, which converts and then runs ACL2 in the grading copy:
   `./run-erl.sh <grading-copy>/work erlang/<f>.erl '<command (a), with {erl} for the file and {out}
   for its output if it writes one>' '<forms (b), with {out} for the converted file>'`
   Run it for `erlang/add_pairs.erl`, `erlang/sum_of_nats.erl`, `erlang/reduce.erl` and
   `erlang/subset.erl`. For the `2 + 2.` check, put `-module(t). -export([f/0]). f() -> 2 + 2.` in a
   scratch `t.erl` and run that, unless the README gives an expression-level command.
3. PASS only if:
   - the AST for `2 + 2` is printed (or appears in the converted file) as
     `(:binop + (:integer 2) (:integer 2))`, or as an FTY value of exactly that shape;
   - every file converts with exit status 0 and loads in ACL2 without error, using the README's forms
     unchanged except for the placeholders;
   - in subset.erl's output, each construct appears as its own AST node: no construct is dropped or
     replaced by an "unsupported" marker. Local, remote and fun calls must be tagged distinctly
     (Section 3), and argument lists must be cons chains;
   - the run form, used on subset.erl's functions with ample fuel, gives the expected values listed at
     the end of this file: integers() = 42, iff(-1) = neg, cases([7]) = 7, tries(0) = infinity,
     funs(4) = 5, calls(9) = {42,[2,9],9}, in the evaluator's value representation;
   - the README's form, given fuel 0 (or 1), returns an out-of-fuel status (this also serves R2).
   The front end may use `erl_scan`/`erl_parse` or its own parser, and may be written in any language.

## R2: eval-cont-list (MANUAL when grade-r2 passes)
Mechanical: a unique logic-mode, recursive function named `eval-cont-list` (any package) exists after
including examples.lisp.
In ACL2, run `(include-book "examples")` in `<tmp>/work` and `:pe eval-cont-list`. PASS only if:
1. there is a fuel quantity that is a natural number: a formal, or the `fuel` field of the continuation
   structure, as Section 3.3 says. Each step decrements it, and the termination measure depends on it;
2. evaluating any expression with fuel 0 (or too little fuel) returns a distinguishable out-of-fuel
   status, not a value and not an error. Try it on the AST of `1 + 2` with fuel 0 and with ample fuel;
   the latter must give 3;
3. on a `receive`, the evaluator returns to its caller (the scheduler) with the remaining continuation
   list inside the state, and does not loop or consume a message itself. Try the AST of
   `receive Z -> Z end` with an empty inbox: the result must be a suspended state. After a message is
   placed in the inbox (as the scheduler would), running it again must yield that message.
   Follow the model's README or examples for how to build these calls.

## R3: scheduler (MANUAL when grade-r3 passes)
Mechanical: some constrained function introduced by the model's books has an executable attachment.
grade.py prints the pairs (`attachments added by the model's books`).
PASS only if:
1. the constrained function is the scheduler (or its step-selection function), introduced by
   `encapsulate`;
2. its exported constraint (`:pe` the encapsulate, or `(constraint-info 'f (w state))`) states the
   fairness condition of Section 3.1: if a non-stuttering action is available (some process is
   runnable or some message is pending delivery), the chosen action is a non-stuttering one. A
   constraint that only gives types, or one that pins the scheduler to a single deterministic choice
   (equality with the executable version), does not count;
3. the attached function is executable (`defattach` succeeded, so its guards are verified) and is the
   one used by the runs in examples.lisp.

## R4: runs in examples.lisp (MANUAL when there are at least 3 assert forms and examples certifies)
Read examples.lisp. PASS only if all of the following hold:
1. `assert-event` (or assert!/assert-equal) forms check:
   - running `add_pairs([1,2,3,4,5,6,7,8])` from Figure 1 gives `[3,7,11,15]` in the evaluator's value
     representation, with the Figure 1 code obtained through the front end or written as ASTs, not a
     hand-simplified program (compare with `erlang/add_pairs.erl`);
   - a two-process exchange in the style of Section 4.3 (Joe/Robert): two processes send each other
     messages, acknowledge receipt, and both exit. The assertion checks both processes' exit values.
     The paper gives no source, so any program of this shape counts;
   - the reduce of Section 4.3 (Figure 5's code, or the reduce-v2 variant) on a tree of at least 3
     workers. The assertion checks the root's total against the expected sum.
   All three must run through the executable scheduler (the attachment).
2. Independently of examples.lisp, reproduce add_pairs with the README's own interface:
   `./run-erl.sh <grading-copy>/work erlang/add_pairs.erl '<README command>' '<README load forms>
   <README run form for add_pairs:add_pairs with argument [1,2,3,4,5,6,7,8] and ample fuel>'`.
   The printed result must be `[3,7,11,15]` in the value representation. If the README's interface
   cannot run it, FAIL.

## R5: sum_of_nats (MANUAL when grade-r5 passes)
Mechanical (grade-r5): sum-of-nats, sum-test-world-p, erl-val-integer->val and eval-cont-list are
logic-mode functions, and make-erl-val-integer exists. The theorem `sum-of-nats-correct` exists. The
exact statement `(implies (natp n) (equal (sum-of-nats n) (/ (+ (* n n) n) 2)))` follows by `:by` from
sum-of-nats-correct or from another theorem of the model.
grade-r5 prints sum-of-nats-correct's statement in `<copy>/work/grader/grade-r5.cert.out`
(`GRADER-THEOREM`). PASS only if that statement has:
1. hypotheses: N is the evaluator's representation of a natural-number Erlang integer; the process's
   logical world satisfies `sum-test-world-p`; and the fuel is at least an explicit expression linear in
   N, such as `(* 8 (+ 1 n))`. Any a·n + b with constants a, b counts; an existentially chosen or
   unbounded fuel does not;
2. conclusion: evaluating the Erlang call `sum_of_nats(N)` with eval-cont-list (directly or through the
   model's run function) produces the Erlang integer whose value is (N^2 + N)/2, either as the closed
   form or as `(sum-of-nats n)`, since the closed form of sum-of-nats is already checked mechanically;
3. hypotheses that are satisfiable: run `erlang/sum_of_nats.erl`'s `sum_of_nats(5)` through run-erl.sh
   (R1) with the theorem's fuel bound for N = 5, and confirm it gives 15.

## R6: reduce (MANUAL when grade-r6 passes)
Mechanical (grade-r6): wtree-p and create-wtree are logic-mode functions, and the theorems
`reduce-invariant-preserved`, `reduce-no-blocked-worker` and `reduce-root-value` exist. Their
statements are printed in `<copy>/work/grader/grade-r6.cert.out` (`GRADER-THEOREM`). PASS only if:
1. **reduce-invariant-preserved**: for a worker tree (wtree-p, or built by create-wtree) satisfying the
   invariant, both delivering a message and running a process give a state satisfying the invariant. It
   may be one theorem covering the scheduler's step, or a conjunction. The invariant: each terminated
   process holds the sum of the leaf values of its subtree;
2. **reduce-no-blocked-worker**: invariant ∧ "no non-stuttering action available" ⇒ no worker in the
   tree is blocked;
3. **reduce-root-value**: if the root process (index 0) has terminated, its value is the sum of all
   indices 0..n-1: n(n-1)/2, `(sum-of-nats (- n 1))`, or an equivalent stated sum;
4. "for every scheduler satisfying the constraint": the statements are about the constrained scheduler
   function (or quantify over any action), not about the attached executable scheduler alone. Check
   with `:pe` on the functions the statements use;
5. non-vacuity: the invariant holds in the initial state. This needs a theorem, or evaluation for
   n = 1..5 on the state from create-wtree. Otherwise FAIL.

## Expected values for the erlang/ inputs (from OTP 25)
- `add_pairs:add_pairs([1,2,3,4,5,6,7,8])` = `[3,7,11,15]`
- `sum_of_nats:sum_of_nats(10)` = `55`
- `reduce:reduce(none, [], 7)` = `7`; `reduce:reduce(Parent, [], 5)` sends `{self(), 5}` to Parent
- `erl_parse:parse_exprs` of `2 + 2.` = `[{op,1,'+',{integer,1,2},{integer,1,2}}]`
- subset: integers() = 42, atoms() = hello, tuples() = {1,two,{3}}, lists([2]) = [0,1,2], binops(5,3) = 8,
  match({1,2}) = 3, iff(-1) = neg, cases([7]) = 7, tries(0) = infinity, funs(4) = 5,
  calls(9) = {42,[2,9],9}, sendrecv(P) = ok when P answers {_, pong}
