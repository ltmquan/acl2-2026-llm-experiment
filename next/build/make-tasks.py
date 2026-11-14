#!/usr/bin/env python3
"""Write next/tasks/<id>/ (prompt.txt + files) for every task of the next experiments."""
import os, re, shutil, json

NB = "/home/user/acl2-exp/next-build"
OUT = "/home/user/acl2-exp/repo/next/tasks"

# ---------------------------------------------------------------- common text
ENV = {
 "8.7": "ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.\n"
        "Books are certified with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).",
 "master": "ACL2 (`acl2`) and ACL2(r) (`acl2r`) are installed at a development version newer than 8.7\n"
           "(git commit 1d2b39a424 of 2026-11-12), with the community books. Books are certified with `cert.pl`\n"
           "(add `--acl2 acl2r` for ACL2(r)).",
}
RULES = ("Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer\n"
         "questions; work until you are done.")
def finish(tid, what="numbered requirement whether it is met"):
    return (f"When you are done, run `submit {tid}`, which saves /work. Then print a short summary: the files you\n"
            f"wrote, and for each {what}.")

def tool_prompt(paper, intro, reqs, env, tid, extra_env="", rules=RULES):
    text = open(f"{NB}/papers/{paper}.txt").read().strip()
    import textwrap
    rq = "\n".join(textwrap.fill(f"{i}. {r}", 110, subsequent_indent="   ", break_on_hyphens=False, break_long_words=False) for i, r in enumerate(reqs, 1))
    return f"""{intro}

<paper>
{text}
</paper>

<requirements>
{rq}
</requirements>

{ENV[env]}{(chr(10) + extra_env) if extra_env else ""}
Put all your work in /work. {rules}
{finish(tid)}
"""

def prove_prompt(intro, defs, admit, targets, env, logic, tid, extra="", cert_acl2=None, defthm="defthm"):
    ca = f"\n<cert.acl2>\n{cert_acl2.strip()}\n</cert.acl2>\n" if cert_acl2 else ""
    files = "/work/defs.lisp" + (" and /work/cert.acl2" if cert_acl2 else "")
    adm = ""
    n = 3
    if admit:
        adm = f"""
3. Admit these definitions in /work/solution.lisp, after including defs and before the theorems, with exactly
these names, formals and bodies. You may add declarations and hints to them, and your own events before them.

<definitions-to-admit>
{admit.strip()}
</definitions-to-admit>
"""
        n = 4
    return f"""{intro}

1. Create {files} containing exactly the text between the tags.
defs.lisp holds the definitions the theorems use. Do not modify these files.

<defs.lisp>
{defs.strip()}
</defs.lisp>
{ca}
2. Write /work/solution.lisp. It must (include-book "defs") and then prove every theorem in <theorems>, each
as a `{defthm}` with exactly the name and statement given. You may add your own definitions and lemmas, and any
`:rule-classes` and hints.{extra}
{adm}
<theorems>
{targets.strip()}
</theorems>

{ENV[env]}
/work/solution.lisp must certify with `cert.pl{" --acl2 acl2r" if logic == "acl2r" else ""}`.
{RULES}
{finish(tid, "theorem whether it is proved")}
"""

# ---------------------------------------------------------------- tool tasks
TOOL_INTRO = ("Build, in ACL2, the system described in the paper below. The authors' implementation is not available;\n"
              "write your own, following the paper. Where the paper gives names, interfaces, generated events or example\n"
              "inputs, use them exactly. The requirements after the paper say what will be checked.")
TASKS = {}

TASKS["tool-definductive"] = dict(env="8.7", setup="8.7", paper="coglio-jurgensen-definductive",
 intro=TOOL_INTRO, reqs=[
 "`/work/definductive.lisp` defines the event macro `definductive` with the interface of Section 4.1, "
 "`(definductive name :preds (...) :irules (...))`, generating the events described in Sections 3 and 4: "
 "proof-tree types (one per clique of mutually dependent predicates), validity and count functions, the "
 "`defun-sk` predicates with their minimality functions, the inference-rule theorems, the `-when-proof-validp` "
 "theorems, the encapsulated `-alt` predicates with their theorems, and the rule-induction scheme, with the "
 "names and forms the paper shows.",
 "`/work/examples.lisp` includes your book and admits the paper's examples `refl-trans-closure` (after "
 "`(defstub r (* *) => *)`), `nat-trees`, `even-and-odd` and `just-0`.",
 "`/work/examples.lisp` also proves the paper's Section 5 theorems about these examples with the hints the paper "
 "shows: `trans-base-right`, `trans-base-left`, `r*-of-f` (both by `r*-induct` and by functional instantiation of "
 "`r*-alt-when-r*`), `even-add-2`, `even-add-double`, `even-when-evenp`, `odd-when-oddp`, "
 "`even-of-pred-when-odd`, and `natp-when-even/odd` with its flag theorem.",
 "Invalid definitions are rejected with an ACL2 error, not a raw Lisp error: the paper's `no-proof-trees`, and "
 "premises that are `and`, `or`, `not` or `implies` of defined predicates. Show each with `must-fail` in "
 "`/work/examples.lisp`.",
 "The proofs that `definductive` generates do not depend on the current theory: every call in requirement 2 "
 "also succeeds after `(in-theory nil)` and after enabling unrelated rewrite rules.",
 "Both books certify with `cert.pl`."])

TASKS["tool-smtlink3"] = dict(env="8.7", setup="8.7", paper="chen-smtlink3",
 intro=TOOL_INTRO, extra_env="Z3 4.8.12 is installed as `z3`.",
 rules=("Trust tags are allowed only in the book that defines the final, trusted clause processor that calls the SMT\n"
        "solver, and in books it includes to run shell commands. Do not use skip-proofs, defaxiom, or redefinition.\n"
        "Do not use the internet. No one will answer questions; work until you are done."),
 reqs=[
 "`/work/smtlink.lisp` (and books it includes) implements the `:smtlink` hint as the chain of clause processors of "
 "Section 5: type inference with `rewrite$` (5.1–5.2), type fixing and judgement selection (5.3), term rewriting "
 "with a user `:translation-theory` (5.4), extraction of type judgements, simplification (5.5), and a final trusted "
 "clause processor that writes an SMT-LIB script and runs Z3 (5.6). Do not use Python.",
 "Only the final clause processor is trusted. The earlier clause processors are verified clause processors "
 "(`:clause-processor` rules proved against an evaluator), each returning the side goals the paper describes.",
 "The final clause processor proves its goal only when Z3 answers `unsat`; `sat`, `unknown` and errors make "
 "the proof fail. The script uses logic AUFNIRA.",
 "`/work/examples.lisp` proves `poly-ineq-example` of Section 5 with the `:smtlink` hint shown, using the "
 "`rational-+`, `rational-*`, ... encapsulate of Section 5.4, and the same goal with its hypotheses permuted.",
 "`/work/examples.lisp` contains a false variant of that goal wrapped in `must-fail`.",
 "`/work/examples.lisp` proves the type-terse goal of Section 4.1 and a goal using the `:hypothesize` hint.",
 "`/work/examples.lisp` proves the alist-to-array goal of Section 5.7 automatically, with a user translation "
 "theory containing the two translation theorems the paper names.",
 "There is a way to print the SMT-LIB script and the term after rewriting for a goal, and "
 "`/work/README.md` says how.",
 "All books certify with `cert.pl`."])

TASKS["tool-erlang"] = dict(env="8.7", setup="8.7", paper="bora-erlang",
 intro=TOOL_INTRO, extra_env="Erlang/OTP 25 is installed (`erl`, `erlc`, with `erl_scan` and `erl_parse`).",
 reqs=[
 "A front end turns Erlang source into the ACL2 AST of Section 3 (with `erl_scan`/`erl_parse` or your own "
 "parser for the subset): `2 + 2.` becomes `(:binop + (:integer 2) (:integer 2))` or an FTY value of that "
 "shape. The subset covers integers, atoms, tuples, lists, binary operators, match, `if`, `case`, `try`/`catch`, "
 "funs and closures, local, remote and fun calls, send and receive. `/work/README.md` gives the exact command "
 "that turns a `.erl` file into ACL2 forms, and the ACL2 form that runs a function of a loaded module on given "
 "arguments with given fuel, under the executable scheduler.",
 "The CPS evaluator `eval-cont-list` of Sections 3.2–3.3 is admitted in logic mode with a natural-number fuel "
 "argument; running out of fuel returns an out-of-fuel status. On `receive` it yields to the scheduler.",
 "The scheduler is an `encapsulate` whose exported constraint is the fairness condition of Section 3.1, with an "
 "executable version attached by `defattach`.",
 "`/work/examples.lisp` runs `add_pairs([1,2,3,4,5,6,7,8])` (Figure 1) to `[3,7,11,15]`, the two-process "
 "exchange of Section 4.3 to completion with both exit values, and the reduce of Section 4.3 on a small tree, "
 "with `assert-event`.",
 "`/work/sum-of-nats.lisp` proves the theorem of Section 4.1 (equation 1) for `sum_of_nats`, named "
 "`sum-of-nats-correct`, with your own explicit fuel bound linear in N, and `(equal (sum-of-nats n) (/ (+ (* n n) n) 2))` "
 "for natural n.",
 "`/work/reduce.lisp` proves the three reduce properties of Section 4.2 for every scheduler satisfying the "
 "constraint, named `reduce-invariant-preserved`, `reduce-no-blocked-worker` and `reduce-root-value`: the "
 "invariant is preserved by message delivery and by running a process, invariant plus no non-stuttering action "
 "implies no blocked worker, and if the root (index 0) terminates its value is the sum of the indices.",
 "All books certify with `cert.pl`."])

TASKS["tool-remora"] = dict(env="master", setup="master", paper="gamboa-remora",
 intro=("Formalize, in ACL2, the work described in the paper below. The Remora interpreter it builds on is in the\n"
        "community books (`books/kestrel/remora`). The author's own lemmas are not available; write your own,\n"
        "following the paper. Where the paper gives names and statements, use them exactly. The requirements after\n"
        "the paper say what will be checked."),
 reqs=[
 "Define the helper functions the paper uses: `pairwise-curry-binary-fn`, `pairwise-curry-binary-x-fn`, "
 "`pairwise-binary-args-fn`, `get-cells-from-expr-value`, `expr-is-nested-vectors-of-base-values`, "
 "`list-of-primop-int-binary` and `list-of-base-values`.",
 "Prove the paper's theorems with the paper's names and statements, against the interpreter in the books: "
 "`propagate-not-reserrp-cells-at-depth-in-expr-value-list-when-vector`, "
 "`eval-app-list-when-primop-binary-and-bases`, `eval-app-when-funval-is-binary-op`, "
 "`undo-expr-value-with-nonempty-dims-3` and `eval-app-when-funval-is-binary-op-fully` (read `arg2l` as "
 "`arg2`). If the interpreter has changed so that a statement must change, make the smallest change and list "
 "every change in `/work/README.md`.",
 "Prove the commutativity corollary at the end of Section 3 for integer addition, in a statement of your own.",
 "`/work/examples.lisp` checks by evaluation the examples of Section 2: `[1 2] + [[1 2] [3 4]]` gives "
 "`[[2 3] [5 6]]`, and the two ill-formed additions give errors.",
 "All books certify with `cert.pl`."])

TASKS["tool-arrayset"] = dict(env="8.7", setup="8.7", paper="hardin-arrayset",
 intro=TOOL_INTRO, extra_env=("The RAC translator sources are in `books/projects/rac` (not built). Also installed: flex, bison, g++,\n"
                              "make, rustc and cargo (no crate registry access)."),
 reqs=[
 "`/work/src/arrayset.rs` is the Restricted Algorithmic Rust arrayset of Section 5.1 and compiles with "
 "`rustc`. `free_head`, `used_head`, `aset_add`, `aset_del_head` and `aset_del` are as in Figures 5–6; write "
 "`aset_transfer`, `aset_find_val_from` and `aset_init` from the text.",
 "ACL2 code for these functions is produced mechanically by the RAC translator (`books/projects/rac`), from RAC "
 "source that your own transpiler or you produce from the Rust. The generated `ASET_DEL` has the form of Figure "
 "7 and certifies against `rtl/rel11/lib/rac`. `/work/README.md` gives the commands.",
 "`/work/examples.lisp` reproduces the example of Figure 4(b) by execution with `assert-event` (the text of "
 "Section 5 is authoritative where the figure differs).",
 "Prove `aset_add-val-at-used_head--thm` and `aset_del-val-at-free_head--thm` (Figure 8) and "
 "`aset_del_head-used-list--thm` and `aset_del_head-free-list--thm` (Figure 9), with the paper's names and "
 "statements, over your own `asetp`, preconditions, `no-dups-anext` and list functions.",
 "All books certify with `cert.pl`."])

TASKS["tool-aes-mir"] = dict(env="8.7", setup="8.7+charon", paper="mccarthy-aes",
 intro=("The paper below describes three artifacts. Build, in ACL2, the third one only: the executable MIR semantics\n"
        "of Section 6, with its loader for Charon's ULLBC JSON, running the paper's AES subject. The authors'\n"
        "implementation is not available; write your own, following the paper. The requirements after the paper say\n"
        "what will be checked."),
 extra_env=("Charon (upstream, `charon`) and its Rust toolchain are installed. The pristine RustCrypto `aes` 0.9.1\n"
            "crate is at /opt/inputs/aes-0.9.1.crate (a .tar.gz); there is no crate registry access."),
 reqs=[
 "`/work/subject/` holds your own adaptation of `src/soft/fixslice32.rs` from the crate, in the manner of Section "
 "4.2 (AES-128 only, byte-array types instead of the `cipher` crate's, single-block `encrypt` and `decrypt` "
 "entry points), as a cargo crate, with `/work/subject/ADAPTATION.md` listing every difference from upstream.",
 "Charon's ULLBC JSON for that crate, produced with `--mir elaborated` as in Section 6.2, is in `/work/subject/`, "
 "with the command in `/work/README.md`.",
 "The ACL2 MIR semantics of Section 6.1 (fixtypes and an executable interpreter) and the JSON importer of Section "
 "6.2 certify with `cert.pl`. An import test book parses the JSON at certification time and checks that the "
 "result equals the program value the interpreter tests use.",
 "`/work/run.lisp` defines `(mir-aes-encrypt key block)` and `(mir-aes-decrypt key block)`, which run the "
 "interpreter on the imported crate's `encrypt` and `decrypt`. They take and return the same representation "
 "of keys and blocks as `aes::aes-128-encrypt` and `aes::aes-128-decrypt` in `kestrel/crypto/aes/aes-spec`.",
 "By execution with `assert-event` on `mir-aes-encrypt` and `mir-aes-decrypt`, the interpreter reproduces the "
 "FIPS-197 AES-128 ciphertexts of Appendix C.1 and Appendix B byte for byte, and decrypt inverts both.",
 "By execution, `mir-aes-encrypt` agrees with `aes::aes-128-encrypt` on 66 inputs: 2 corner cases and 64 "
 "pseudorandom key/block pairs. The checker will also run its own inputs.",
 "All books certify with `cert.pl`."])

# ---------------------------------------------------------------- future work: prove-these-statements tasks
def fw(name): return {k: open(f"{NB}/fw/{name}/{k}.lisp").read() if os.path.exists(f"{NB}/fw/{name}/{k}.lisp") else ""
                      for k in ("defs", "admit", "targets")}
FW_INTRO = "Prove the theorems below in ACL2(r)."
FWX = {
 "fw-euler-product": ("euler-product",
   "Prove the theorems below in ACL2(r). `basel-series(i, n)` is the sum of 1/k² for i ≤ k < n, and\n"
   "`euler-zeta2-product(i, n)` is the product of 1/(1 − p⁻²) over the primes p with i ≤ p < n."),
 "fw-trapezoid": ("trapezoid",
   "Prove the theorems below in ACL2(r): the error bound of the composite trapezoid rule for a function `tf` with\n"
   "a bounded second derivative on an interval, for every partition."),
 "fw-stirling-bounds": ("stirling-bounds",
   "Prove the theorems below in ACL2(r). `stirling-ratio(n)` is n! / (√n · nⁿ · e⁻ⁿ)."),
 "fw-inductance": ("inductance",
   "Prove the theorems below in ACL2(r): the value of the integral of cos(x − mγ)·cos(x − nγ) over [0, 2π],\n"
   "with γ = 2π/3 and integers m, n, as a limit of Riemann sums and as a definite integral."),
 "fw-rectifier-rows": ("rectifier-rows",
   "Prove the theorems below in ACL2(r). `sa` is the sampling function sin(x)/x. `envelope6` is the maximum of\n"
   "six cosines 60° apart, and the `-output` functions are rectifier output waveforms built from it."),
 "fw-rectifier-master": ("rectifier-master",
   "Prove the theorems below in ACL2(r). `sa` is the sampling function sin(x)/x. `int-cos` and `int-cos-sq`\n"
   "are definite integrals of cos and cos², and `vdc-integral` and `vrms-integral` are the average and RMS of\n"
   "V·cos θ over the window [α − T/2, α + T/2]."),
}
for tid, (d, intro) in FWX.items():
    f = fw(d)
    TASKS[tid] = dict(env="8.7", setup="8.7", kind="prove", logic="acl2r", intro=intro, **f)

TASKS["fw-ftc-macro"] = dict(env="8.7", setup="8.7", kind="text", text="""Work in ACL2(r). Write an event macro `def-ftc-integral` that, given an integrand and a user-supplied
antiderivative, introduces the definite integral of the integrand and proves its value by the Fundamental
Theorem of Calculus, by functional instantiation of `ftc-2` in `nonstd/integrals/ftc-2.lisp`.

Interface:

(def-ftc-integral name
  :integrand      f          ; unary function symbol, or (lambda (x) term)
  :antiderivative F          ; unary function symbol, or (lambda (x) term)
  :domain         dom        ; a ground term evaluating to an interval, e.g. (interval 1 nil)
  :derivative-thm thm1       ; optional: name of an existing theorem of the form below
  :continuity-thm thm2       ; optional: name of an existing theorem of the form below
  :hints          hints)     ; optional: hints for the obligations the macro must prove

The derivative theorem has the form
  (implies (and (standardp x) (inside-interval-p x dom) (inside-interval-p x1 dom) (i-close x x1) (not (= x x1)))
           (i-close (/ (- (F x) (F x1)) (- x x1)) (f x)))
and the continuity theorem the form (as `rcdfn-prime-continuous` in `ftc-2.lisp`)
  (implies (and (standardp x) (inside-interval-p x dom) (i-close x x1) (inside-interval-p x1 dom))
           (i-close (f x) (f x1)))
where f and F stand for the given functions or lambdas applied to the argument.

Generated events, named from `name`:
- `name-integrand` (when f is a lambda), `map-name`, `riemann-name`, `strict-int-name` (a `defun-std`) and
  `int-name`, defined as the corresponding functions in `ftc-2.lisp`;
- `int-name-is-integral`, as `strict-int-rcdfn-prime-is-integral-of-rcdfn-prime` in `ftc-2.lisp`:
  (implies (and (standardp a) (standardp b) (<= a b) (inside-interval-p a dom) (inside-interval-p b dom)
                (partitionp p) (equal (car p) a) (equal (car (last p)) b) (i-small (mesh p)))
           (i-close (riemann-name p) (strict-int-name a b)));
- `int-name-ftc`: `(implies (and (inside-interval-p a dom) (inside-interval-p b dom)) (equal (int-name a b) (- (F b) (F a))))`.

If `:derivative-thm` or `:continuity-thm` is omitted, the macro must try to prove that obligation itself, and on
failure stop with an error that prints the obligation. The macro must also prove the other side conditions of
`ftc-2` (realness of f and F on the domain, that the domain is an interval, non-triviality).

Requirements:
1. The macro is in /work/def-ftc-integral.lisp and meets the specification above: the interface, the generated
   events with exactly these names and forms, the automatic obligations, and the error on failure. The checker
   will also run calls of its own.
2. /work/tests.lisp includes it and contains at least these calls, each followed by a check that `int-name-ftc`
   gives the expected closed form at concrete endpoints:
   (a) f(x) = x², F(x) = x³/3, dom = (interval nil nil), with no theorems supplied;
   (b) f = `acl2-cosine`, F = `acl2-sine`, dom = (interval nil nil), with no theorems supplied;
   (c) f(x) = 1/x², F(x) = −1/x, dom = (interval 1 nil), with no theorems supplied;
   (d) f = `acl2-ln`, F(x) = x·ln x − x, dom = (interval 1 nil); you may supply the theorems;
   (e) a call with a wrong antiderivative, wrapped in `must-fail`.
3. Both books certify with `cert.pl --acl2 acl2r`.""")

TASKS["fw-definductive-exec"] = dict(env="master", setup="master", kind="text", text="""You are given the event macro `definductive` in the community books (`books/std/util/definductive.lisp`, with
`definductive-doc.lisp` and `definductive-tests.lisp`). It defines predicates p₁, …, p_k from inference rules as
`defun-sk` existentials over proof trees, and generates rule theorems and induction principles. Extend it with
an optional facility that also generates an executable definition of each predicate and proves it equivalent
to the original predicate.

New optional inputs (default nil; behavior must be unchanged when they are absent):

:exec ((p1 :name p1-exec :measure m1)       ; one entry per predicate in :preds
       (p2 :name p2-exec :measure m2) ...)  ; mi: term over pi's formals (o-p valued)
:exec-binds ((rule-name (v term) ...) ...)  ; per rule: how to compute each rule variable that is not
                                            ; literally a conclusion argument, as a term over the formals
                                            ; of the conclusion's predicate
:exec-hints ...                             ; optional hints for the generated obligations

Semantics. For a rule r with conclusion (p t₁ … t_n), where p has formals x₁ … x_n, each rule variable v gets a
value: from :exec-binds, or x_i when t_i is literally v. A rule variable with no value is an error. Under those
values, (p-exec x₁ … x_n) holds iff for some rule with conclusion predicate p, each x_i equals the instantiated
t_i and the instantiated premises hold, in order, where a premise on a defined predicate q is evaluated by
q-exec. The p-exec functions of a clique are mutually recursive and use the given measures.

The tool must prove automatically, or stop with an error that shows the failed obligation:
(a) termination, for each recursive premise under the preceding tests;
(b) binding adequacy: if the x_i equal the t_i under some values of the rule variables and the non-predicate
    premises hold, then the bound terms evaluate to those values.
It must then generate and prove `p-exec-correct`, (iff (p-exec x1 ... xn) (p x1 ... xn)), and
`booleanp-of-p-exec`, for every p. The p-exec functions must not call the defun-sk predicates, their witnesses
or any defchoose, so that they execute on concrete data.

Requirements:
1. Your extended tool is /work/definductive.lisp (a modified copy of the books' file, under the same name in
   /work); other changed files are also in /work.
2. A copy of `definductive-tests.lisp` that includes your /work/definductive.lisp instead certifies unchanged.
3. /work/exec-tests.lisp certifies, with:
   (i) even/odd on naturals (conclusions (even 0), (odd (1+ n)) and (even (1+ n)), with premise (natp n) before
       the recursive premise);
   (ii) naturals plus finitely branching trees of naturals (conclusions using cons);
   (iii) a typing judgement for a small expression language of your choice, with at least three predicates in one
         clique;
   (iv) `must-fail` on reflexive-transitive closure with the transitivity rule and no binding for its middle
        variable;
   (v) `assert-event` evaluations of each p-exec on concrete inputs.""")

TASKS["fw-multisets"] = dict(env="8.7", setup="8.7", kind="text", text="""Work in ACL2. Using the ordered-map library `std/omaps` (`omap::mapp`, `omap::update`, `omap::lookup`,
`omap::assoc`, `omap::delete`, `omap::keys`, ...), implement a library of finite multisets (bags) in a new
package `MSET`. A bag is an `omap::mapp` whose values are all positive integers (the multiplicities); the empty
map is the empty bag.

Required functions, all guard-verified. Their behavior on non-bags is your choice, but document it.
- `bagp`, `bfix` and `bequiv`, with `bequiv` an equivalence that every function below respects;
- `empty` and `emptyp`;
- `count a b` (a natural; 0 when absent) and `in a b`;
- `insert a b` (count + 1), `insert-n a n b` (count + n, for natural n), `delete a b` (count − 1, removing the
  key at 0) and `delete-all a b`;
- `cardinality b` (the sum of the counts) and `support b` (the keys, as an oset);
- `subbag x y`;
- `sum x y` (counts add), `union x y` (max), `intersect x y` (min) and `diff x y` (truncated subtraction);
- `from-list l` and `to-list b` (each element repeated by its count, in key order).

Required theorems, as rewrite rules unless that is impossible:
- closure: `bagp` of every function above that returns a bag;
- `count-of-X` for every X in {empty, insert, insert-n, delete, delete-all, sum, union, intersect, diff,
  from-list}, giving the count in terms of the counts of the arguments (for `from-list`, in terms of `duplicity`
  from `std/lists/duplicity`);
- `in` iff count > 0;
- extensionality, with a witness function `(count-diff-witness x y)` and the theorem `bag-extensionality`:
  for bags x and y, if (count (count-diff-witness x y) x) = (count (count-diff-witness x y) y), then x = y;
- `subbag` iff pointwise ≤ of counts: `subbag-when-counts-le`, with a witness function
  `(subbag-witness x y)`: if (count (subbag-witness x y) x) ≤ (count (subbag-witness x y) y) then
  (subbag x y); and `count-le-when-subbag`: if (subbag x y) then (count a x) ≤ (count a y). Also
  reflexivity, antisymmetry (for bags) and transitivity;
- `cardinality` of empty, insert, delete (when in) and sum;
- `(equal (from-list (to-list b)) (bfix b))` and `(equal (len (to-list b)) (cardinality b))`;
- commutativity and associativity of `sum`, `union` and `intersect`.

`count`, `insert` and `delete` must be implemented directly by map operations, with no conversion to lists.

Requirements:
1. The library is /work/mset.lisp, with the package in /work/package.lsp and a /work/cert.acl2 that loads it.
   It meets the specification above: the functions, guard verification, `bequiv` congruences, the theorems, and
   the implementation requirement. The checker will state the theorems in its own form and prove them from
   your rules.
2. /work/mset-tests.lisp includes the library and evaluates each function on concrete bags with `assert-event`.
3. Both books certify with `cert.pl`.""")

# ---------------------------------------------------------------- ZFC
ZFC_INTRO = """Prove the theorems below in ACL2(zfc), the set theory of the community books `projects/set-theory` (ACL2
with `projects/set-theory/top` included; see `:doc zfc` and the books themselves)."""
ZFC_EXTRA = """ Each theorem is a `defthmz`: you may add hypothesis
functions (keys of `zfc-table`, such as the `$prop` functions of your own `zsub` and `zfn` events) to its
`:props` list. Do not use `table` events on `zfc-table` directly, or `defthme`'s `:skip` option."""
for k in range(1, 12):
    d = f"{NB}/zfc/zfc-t{k}"
    title = open(f"{d}/title.txt").read().strip()
    tgt = open(f"{d}/targets.lisp").read()
    opt = open(f"{d}/optional.lisp").read() if os.path.exists(f"{d}/optional.lisp") else ""
    TASKS[f"zfc-t{k}"] = dict(env="master", setup="master", kind="zfc", title=title,
        defs=open(f"{d}/defs.lisp").read(), cert=open(f"{d}/cert.acl2").read(), targets=tgt, optional=opt)

# ---------------------------------------------------------------- write
def write(tid, T):
    D = os.path.join(OUT, tid)
    if os.path.isdir(D): shutil.rmtree(D)
    os.makedirs(D)
    kind = T.get("kind", "tool")
    if kind == "tool":
        p = tool_prompt(T["paper"], T["intro"], T["reqs"], T["env"], tid, T.get("extra_env", ""),
                        T.get("rules", RULES))
    elif kind == "prove":
        p = prove_prompt(T["intro"], T["defs"], T["admit"], T["targets"], T["env"], T["logic"], tid)
        open(f"{D}/defs.lisp", "w").write(T["defs"])
        open(f"{D}/targets.lisp", "w").write(T["targets"])
        if T["admit"]: open(f"{D}/admit.lisp", "w").write(T["admit"])
    elif kind == "zfc":
        tg = T["targets"]
        extra = ZFC_EXTRA
        if T["optional"]:
            extra += ("\n\nThe last theorem, after the ;; optional marker, is optional: try it after the others.")
            tg = tg.rstrip() + "\n\n;; optional\n" + T["optional"]
        p = prove_prompt(ZFC_INTRO, T["defs"], "", tg, T["env"], "acl2", tid, extra=extra,
                         cert_acl2=T["cert"], defthm="defthmz")
        for f, s in (("defs.lisp", T["defs"]), ("cert.acl2", T["cert"]), ("targets.lisp", T["targets"])):
            open(f"{D}/{f}", "w").write(s)
        if T["optional"]: open(f"{D}/optional.lisp", "w").write(T["optional"])
    else:
        p = f"{T['text'].strip()}\n\n{ENV[T['env']]}\nPut all your work in /work. {RULES}\n{finish(tid)}\n"
    open(f"{D}/prompt.txt", "w").write(p)
    return len(p)

if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    index = {}
    for tid, T in TASKS.items():
        n = write(tid, T)
        index[tid] = dict(env=T["env"], setup=T["setup"], prompt_bytes=n)
        print(f"{tid:24s} {T['setup']:12s} {n:6d} bytes")
    json.dump(index, open(os.path.join(OUT, "index.json"), "w"), indent=1)
