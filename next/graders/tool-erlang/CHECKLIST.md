# tool-erlang: manual checks

Run `grade.sh <work-dir>` first. It prints the grading copy (`<tmp>/work`), where every model book is
already certified, and the grader logs. A `FAIL` stays a fail. For each `MANUAL` line, follow the
procedure below. Do everything in `<tmp>/work` (a copy), never in the saved /work. If an item cannot be
decided, record FAIL with the reason. The Erlang inputs are in this directory under `erlang/`. They are
transcribed from the PDF; `subset.erl` is ours. All compile with `erlc` (OTP 25), and their expected
values are given below.

## R1: front end (MANUAL whenever README.md exists)
1. Follow /work/README.md exactly to run the front end on:
   (a) the expression `2 + 2.`;
   (b) `erlang/add_pairs.erl` (Figure 1), `erlang/sum_of_nats.erl` (Section 2.1) and
       `erlang/reduce.erl` (Figure 5);
   (c) `erlang/subset.erl`, one function per construct of the requirement: integers, atoms, tuples,
       lists, binary operators, match, `if`, `case`, `try`/`catch`, funs and closures, local, remote
       and fun calls, send and receive.
2. PASS only if:
   - (a) prints `(:binop + (:integer 2) (:integer 2))`, or an FTY value whose printed form has exactly
     that shape (constructor for binop with op `+` and two integer-2 children);
   - every file in (b) and (c) is translated without error into ACL2 forms that ACL2 can read. Load
     them with `ld`, or as the README says;
   - in the output for (c), each construct appears as its own AST node: no construct is dropped or
     replaced by an "unsupported" marker. Local, remote and fun calls must be tagged distinctly
     (Section 3: "we tag each call as a local, remote, or fun call"), and argument lists must be
     normalized to cons chains as Section 3 describes. A list or tuple representation that the README
     documents is acceptable.
   The front end may use `erl_scan`/`erl_parse` or its own parser. Python is fine here; only ACL2
   books are restricted.

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
Read examples.lisp. PASS only if `assert-event` (or assert!/assert-equal) forms check all of the
following, and the book certifies (it does, if grade.py got this far):
1. Running `add_pairs([1,2,3,4,5,6,7,8])` from Figure 1 gives `[3,7,11,15]` in the evaluator's value
   representation. The program must be the Figure 1 code, obtained through the front end or written as
   ASTs, not a hand-simplified program. Compare it with `erlang/add_pairs.erl`.
2. A two-process exchange in the style of Section 4.3 (Joe/Robert): two processes send each other
   messages, acknowledge receipt, and both exit. The assertion must check both processes' exit values.
   The paper gives no source, so any program of this shape counts.
3. The reduce of Section 4.3 (Figure 5's code, or the reduce-v2 variant that sends the total back) on a
   tree of at least 3 workers. The assertion must check the root's total (and each worker's result, for
   reduce-v2) against the expected sum.
All three must run through the executable scheduler (the attachment), not by calling the AST evaluator
on one process.
Also run the front end on `erlang/add_pairs.erl` and `erlang/reduce.erl` (R1). Check that the ASTs used in
examples.lisp match its output, or that the README explains how they were produced.

## R5: sum_of_nats (MANUAL when grade-r5 passes and sum-of-nats.lisp has a defthm)
Mechanical: sum-of-nats, sum-test-world-p, erl-val-integer->val and eval-cont-list are logic-mode
functions, make-erl-val-integer exists, and `(sum-of-nats k)` = k(k+1)/2 for k = 0..30.
Find the main theorem in sum-of-nats.lisp. PASS only if one defthm, not local, states:
1. hypotheses: N is the evaluator's representation of a natural-number Erlang integer; the process's
   logical world satisfies `sum-test-world-p`; and the fuel is at least an explicit expression linear in
   N, such as `(* 8 (+ 1 n))` (any a·n + b with constants a, b counts; an existentially chosen or
   unbounded fuel does not);
2. conclusion: evaluating the Erlang call `sum_of_nats(N)` with eval-cont-list (directly or through the
   model's documented wrapper) produces the Erlang integer whose value is (N^2 + N)/2, written as the
   closed form. A conclusion with `(sum-of-nats n)` counts only if a theorem in the same book also
   gives the closed form and the two are combined in a stated theorem;
3. the hypotheses are satisfiable: instantiate the theorem with N = 5, a world built as in the model's
   examples, and the stated fuel bound. Evaluate the evaluator call and confirm it gives 15.

## R6: reduce (MANUAL when grade-r6 passes and reduce.lisp has at least 3 defthms)
Mechanical: wtree-p and create-wtree exist as logic-mode functions.
Find the three theorems in reduce.lisp. PASS only if all three are present (not local, no skip-proofs,
which certification already guarantees) and:
1. **invariant preservation**: for a worker tree (wtree-p / built by create-wtree) satisfying the
   invariant, delivering a message or running a process, as chosen by the *constrained* scheduler
   function, gives a state satisfying the invariant. The invariant: each terminated process holds the
   sum of the leaf values of its subtree;
2. **no deadlock**: invariant ∧ "no non-stuttering action available" ⇒ no worker in the tree is
   blocked;
3. **result**: if the root process (index 0) has terminated, its value is the sum of all indices
   0..n-1, i.e. n(n-1)/2, or `(sum-of-nats (- n 1))`, or an equivalent stated sum.
"For every scheduler satisfying the constraint" means the theorems mention the constrained
scheduler function (or quantify over the chosen action) and do not depend on the attached executable
function: no `defattach`-only facts, no theorems about the executable scheduler alone.
Also check that the invariant holds initially: a theorem, or evaluation for n = 1..5 on the state from
create-wtree. Otherwise the theorems may be vacuous: FAIL.

## Expected values for the erlang/ inputs (from OTP 25)
- `add_pairs:add_pairs([1,2,3,4,5,6,7,8])` = `[3,7,11,15]`
- `sum_of_nats:sum_of_nats(10)` = `55`
- `reduce:reduce(none, [], 7)` = `7`; `reduce:reduce(Parent, [], 5)` sends `{self(), 5}` to Parent
- `erl_parse:parse_exprs` of `2 + 2.` = `[{op,1,'+',{integer,1,2},{integer,1,2}}]`
- subset: integers() = 42, atoms() = hello, tuples() = {1,two,{3}}, lists([2]) = [0,1,2], binops(5,3) = 8,
  match({1,2}) = 3, iff(-1) = neg, cases([7]) = 7, tries(0) = infinity, funs(4) = 5,
  calls(9) = {42,[2,9],9}, sendrecv(P) = ok when P answers {_, pong}
