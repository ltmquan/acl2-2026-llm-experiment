# Tool-building specs: what counts as success (written before any run)

Setting: an autonomous session gets one unpublished ACL2-2026 paper and must BUILD the tool or system the
paper describes, in ACL2 8.7 (`/opt/acl2`, books at `/opt/acl2/books`), without the authors' code.
"8.7" means the 8.7 tree on disk. "master" means `origin/master` of the ACL2 repo (head 1d2b39a424,
2026-11-12). Anything that exists only on master is hidden from runs unless this spec says otherwise.

Machine facts checked on 2026-11-13. These hold for all six papers:
- No SMT solver is installed: no `z3`, no `cvc5`, and no Python `z3` module.
- No Erlang/OTP, OCaml, Charon or Aeneas is installed.
- Installed: rustc/cargo (stable, with no crate registry cache), g++, make, bison.
- `flex` is not installed.
- Network access is assumed to be off for the runs.

Two local copies of the authors' supporting materials sit on this machine:
- `/home/user/acl2-exp/reference-books/workshop-2026/{coglio-jurgensen,mccarthy-aeneas}`
- the master checkout under `/opt/acl2/.git`

Neither may be visible to a run. Sandboxes must hide `/opt/acl2/.git` and `/home/user/acl2-exp/reference-books`.

Grading convention: a criterion passes only if it is mechanically checked. That means one of:
- a grader-written book certifies with `cert.pl` against the model's code;
- a stated `defthm` is admitted verbatim (modulo the package prefix);
- an `assert-event` / `assert-equal` evaluates to true.

---

## 1. coglio-jurgensen-definductive — "Inductive Definitions via Inference Rules in ACL2"

**What to build.** An event macro `definductive`. It takes predicate signatures and inference rules and generates:
- FTY proof-tree types, with one type per clique of mutually dependent predicates;
- proof-tree validity functions;
- `defun-sk` predicate definitions, based on a minimal valid proof tree;
- inference-rule theorems;
- a rule-induction scheme;
- minimality ("smallest predicate") theorems, via constrained `-alt` predicates.

The generated proofs must not depend on the ambient theory (Sec. 4.1).

**Acceptance criteria.** Interface: `(definductive name :preds ((p x1 ...) ...) :irules ((rule (prem ...) concl) ...))` (Sec. 4.1).

1. `refl-trans-closure` (Sec. 4, p.4) is admitted after `(defstub r (* *) => *)`. The following events then exist with the shapes shown in Sec. 3/4.4:
   - `r*-proof` (deftagsum with `:base/:refl/:trans`), `r*-proofp`, `r*-proof-validp`, `r*-proof-count`;
   - `r*` (defun-sk with skolem `r*-proof`) and `r*-proof-minimalp`.
2. The rule theorems `r*-base`, `r*-refl` and `r*-trans` exist, with the exact formulas in Sec. 3, p.4.
3. `r*-when-proof-validp` exists, of the form shown in Sec. 5.2 (no minimality hypothesis).
4. Encapsulated `r*-alt` exists with `r*-alt-base/-refl/-trans`, together with `r*-alt-when-r*-proof-validp` and `r*-alt-when-r*` (Sec. 3, 4.7).
5. `r*-induct` exists and `:induct (r* a b)` works. The grader's book proves `r*-of-f` from `r-of-f` with the Sec. 5.4 hints. It also proves the same theorem via `:functional-instance r*-alt-when-r*` (Sec. 5.5).
6. Derived rules prove as in Sec. 5.1:
   - `trans-base-right` proves by rewriting;
   - `trans-base-left` proves with a `:use` of `r*-base` (fn. 11).
7. `nat-trees` (Sec. 4.2, p.6) is admitted. It must give two cliques, `nat` and `{tree, trees}`, and produce `fty::deftypes tree-proof-clique`.
8. `even-and-odd` (Sec. 4.2, p.6) is admitted. `odd-proof` has only a recursive summand, so the levels need `:base-case-override` and `two-nats-measure`. The grader's book then certifies the following:
   - `even-add-2`, and `even-add-double` by induction on m (Sec. 5.1);
   - `proof-for-even/odd` with `even-when-evenp` and `odd-when-oddp` (Sec. 5.2). The constructor names `make-even-proof-from-odd` and `even-proof-zero` must exist.
   - `even-of-pred-when-odd`, using the accessor `odd-proof-from-even->premise1-proof` (Sec. 5.2);
   - the flag event `defthm-even-proof-validp-clique-flag` with `natp-when-even/odd-proof-validp`, and `natp-when-even/odd` (Sec. 5.3).
9. `just-0` (fn. 4) is accepted.
10. These are rejected with an error, not a raw Lisp error:
    - `no-proof-trees` (Sec. 4.8);
    - a premise that is an `(and (p ..) (q ..))` / `(or ...)` of defined predicates;
    - `(not (p ...))` and `(implies (p ...) ...)` premises.
11. Robustness (Sec. 4.1): criteria 1–8 still succeed after `(in-theory nil)` or with a theory containing hostile rewrite rules. The grader runs them with `(in-theory (disable ...))` of the common rules.
12. Optional, at scale: a 10–20-rule definition modelled on the Remora `dim-eq` rules (Sec. 6: `add-comm`, `add0`, `add1`, `add3m`) is admitted in a reasonable time (< 60 s).

**Inputs beyond the paper.**
- FTY (`centaur/fty`, with `deftagsum`/`deftypes`, `:base-case-override` and `two-nats-measure`), `defun-sk`, `make-flag` and `std/util`. All are in 8.7. Nothing external is needed.

**Leakage.**
- The authors' tool is on master only:
  - `books/std/util/definductive.lisp` (6,940 lines), `definductive-doc.lisp` and `definductive-tests.lisp` (53 calls). The first commit is f070496592, dated 2026-07-16.
  - Supporting files `books/workshops/2026/coglio-jurgensen/` (refl-trans-closure*.lisp, even-and-odd, nat-trees, just-0, no-proof-trees, empty). The first commit is f655197883, dated 2026-10-28.
  - Local copy: `reference-books/workshop-2026/coglio-jurgensen`.
- The paper cites `[books]/std/util/definductive.lisp` and acl2.org/manual (topic `definductive`).
- Master `kestrel/remora` also uses definductive: `ispace-equivalence`, `type-validity` and others, and `package.lsp` imports the symbol.
- 8.7 has no general tool, only specific prior proof-tree developments (cited in Sec. 7).

**Special rules / verdict.** No trust tags are needed.
- **Feasible.** It is pure ACL2 macro programming over FTY. The paper gives the exact generated-event shapes for r*.
- The main risk is that the generated proofs must be theory-independent and must work for mutual cliques.

---

## 2. chen-smtlink3 — "Smtlink 3: Rewrite-driven Compilation to SMT-LIB"

**What to build.** A new Smtlink, used through a `:smtlink` computed hint. It is a chain of 6 clause processors (Sec. 5):
1. type inference, using a computed hint that calls `rewrite$` (5.1–5.2);
2. type fixing / `smt-judgement` selection (5.3);
3. iterated term rewriting with a user `:translation-theory` (5.4);
4. extraction of unconditional type judgements;
5. simplification (5.5).

CPs 1–5 must be verified clause processors. Each returns a side subgoal that re-validates the `rewrite$` output. The sixth is a trusted clause processor. It emits an SMT-LIB script (logic AUFNIRA) and runs an external solver. It returns the empty clause only on `unsat`.

**Acceptance criteria.**
1. `poly-ineq-example` (Sec. 5, p.10) proves with exactly the `:smtlink (:translation-theory (union-theories (theory 'minimal-theory) '(smt::return-of-rational-+ ... smt::specialize-unary-rational-/)))` hint shown. This uses the user encapsulate of `rational-+/-/*/'/'/<` from Sec. 5.4. `x^2-y^2` is taken from `projects/smtlink/examples/examples.lisp`.
2. For that goal, the script written by CP 6 contains the following (Sec. 5.6). The grader inspects a dump flag or the file.
   - `(set-logic AUFNIRA)`;
   - `(declare-const X Real)` and `(declare-const Y Real)`;
   - one `(assert (not ...))` over `+ * < -` on reals;
   - `(check-sat)`.
3. Negative test: a false variant of the goal (for example `<` replaced by `>`) must fail. `sat` and `unknown` must both lead to proof failure (Sec. 5.6).
4. A type-terse goal: `(implies (and (integerp y) (= x (* 2 y))) (foo x y))`, with a suitable SMT-expressible `foo`, proves without an `(integerp x)` hypothesis (Sec. 4.1). A `:hypothesize` hint adds a hypothesis plus a side subgoal (Sec. 4.1).
5. The alist-to-array goal of Sec. 5.7 (p.14) proves automatically, using a user translation theory containing:
   - `int-sym-top-down-translation-of-assoc-equal`;
   - `int-sym-top-down-translation-of-acons`.
   The model must define `int-sym-alist-p` and the `int-sym-array-*` functions itself. The arrays are declared uninterpreted in SMT-LIB.
6. A rewriting check: the intermediate term after CP 3 has the `SMT::RATIONAL-*` form shown on p.10–11. Order-agnostic processing holds: permuting the hypotheses of criterion 1 still proves (Sec. 6.3).
7. Trust boundary:
   - only CP 6 uses `defttag` and a trusted `:clause-processor`;
   - CPs 1–5 are admitted with `define-trusted-clause-processor` absent, i.e. as `:clause-processor` rules proved against an evaluator;
   - Python is not used.
   Report the line count of the trusted part. The paper's figure is 459 lines (Sec. 6.2); this is informative, not pass/fail.

**Inputs beyond the paper.**
- **Z3**, or another SMT-LIB2 solver, which is external and not installed. It must be provided as a binary on PATH. The paper used Z3 5.3.1 (Sec. 6.3).
- **Smtlink 2.0** (prior work by the same group) is in 8.7 at `books/projects/smtlink`. On master it dates from 5bcb241949 (2018-02-21). It is uncertified and needs ttags `:tshell`, `:read-string` and `Smtlink`. Post-8.7 master has only 3 small maintenance commits to it (2026-08/09, McCarthy), not Smtlink 3.
- `rewrite$` is at `books/tools/rewrite-dollar.lisp` (8.7). Also in 8.7: `std/osets`, `clause-processors/meta-extract-*` and `tshell` (`centaur/misc/tshell`).

**Leakage.**
- Smtlink 3 code is not on master. A tree-wide grep for `smt-judgement` and `int-sym-array` finds nothing. The paper cites no repository.
- The 8.7 Smtlink 2 is a strong head start for criteria 1 and 2 (the same example and the same architecture family). Using it as a base is allowed: it is prior work. Graders should note how much was reused.

**Special rules / verdict.**
- Trust tags must be allowed, for the final CP and for `tshell`.
- **Feasible with setup:** install a Z3 binary (offline package or binary in the sandbox) and allow ttags.
- Without a solver, only criteria 6–7 and script generation (2) can be checked.

---

## 3. bora-erlang — "Erlang in ACL2: A Continuation-Passing Style Evaluator"

**What to build.**
- An Erlang-to-ACL2 front end that turns `erl_scan`/`erl_parse` ASTs into FTY data (Sec. 3).
- A CPS AST evaluator, `eval-cont-list`, over lists of tag-sum continuations and an `estate`. The `estate` holds val, bindings, module/world and outbox. The evaluator runs on fuel (Sec. 3.2–3.3).
- An encapsulated non-deterministic scheduler, with one weak fairness constraint and a `defattach` executable version (Sec. 3.1, 4.3).
- The paper's two example proofs (Sec. 4).

**Acceptance criteria.**
1. AST representation (Sec. 3): `2 + 2.` maps to `(:binop + (:integer 2) (:integer 2))`, or an FTY-equivalent with the same shape. The supported subset covers:
   - integers, atoms, tuples and lists;
   - binops, match, `if`, `case`, `try-catch`, funs and closures;
   - local, remote and fun calls;
   - send and receive.
   Maps and floats are excluded.
2. The evaluator is admitted in logic mode with an explicit natp fuel. Running out of fuel returns an out-of-fuel status, not non-termination (Sec. 3.3). On `receive` it yields its continuation to the scheduler (Fig. 4).
3. The executable scheduler runs `add_pairs([1,2,3,4,5,6,7,8])` (Fig. 1) to `[3,7,11,15]` (p.3).
4. A Joe-Robert-style exchange runs to completion with both exit values retrievable (Sec. 4.3): two processes send to each other, acknowledge, and exit.
5. A reduce with a fun-combine, sending the total back to every worker, runs on a small tree (Sec. 4.3).
6. The scheduler is an `encapsulate`. Its exported constraint is: if a non-stuttering action exists, it picks one (Sec. 3.1). The executable version is attached with `defattach`.
7. Theorem (Sec. 4.1, eq. 1): if `N` is an Erlang integer with natp value, the world satisfies `sum-test-world-p`, and the fuel is at least an explicit bound linear in N (the paper's bound is 8*(1+N)), then:
   - evaluating `sum_of_nats(N)` returns `(make-erl-val-integer :val (sum-of-nats (erl-val-integer->val N)))`;
   - `(sum-of-nats n)` equals `(/ (+ (* n n) n) 2)`.
   The model's own constant is accepted.
8. Reduce, for the simplified reduce of Fig. 5 on a `wtree-p`/`create-wtree` worker tree (Sec. 4.2):
   - (a) the invariant is preserved by message delivery and by running a process;
   - (b) invariant plus no non-stuttering action implies no blocked worker;
   - (c) if the root (index 0) terminates, its value is the sum of the indices 0..n-1.
   All three hold for every scheduler satisfying the constraint.

**Inputs beyond the paper.**
- **Erlang/OTP** (`erl_scan`, `erl_parse`) is needed to run the paper's Erlang front end. It is external and not installed.
- Alternative without OTP: the model hand-writes ASTs or writes a parser for the subset in ACL2. In that case criterion 1 is checked on the ACL2 side only.
- FTY and arithmetic-5 are in 8.7. No other people's ACL2 code is needed.

**Leakage.**
- The authors' code is at https://github.com/KuterBora/Erlang-in-ACL2, cited in the paper (Sec. 4). Its paths are `books/erl-arithmetic/sum_of_nats.lisp`, `books/reduce-v2/proofs/inv.lisp` and `scheduler/examples/{Joe-Robert,reduce-v2}.lisp`.
- It is not on master: `workshops/2026/README` lists the paper with no directory, and a grep for `eval-cont-list` finds nothing. Nothing similar is in 8.7.

**Special rules / verdict.** No ttags are needed.
- **Feasible with setup:** either install Erlang/OTP or waive the Erlang-side front end (supply ASTs).
- Criteria 1–6 are realistic.
- Criteria 7–8 are very hard: the paper reports rewriter blow-up and heavy hand guidance. Grade them separately.

---

## 4. gamboa-remora — "Towards Formalizing the Semantics of Lifting Argument Frames ..."

**What to build.** A reasoning layer, not an interpreter: a library of one-step and "glue" rules about the Kestrel ACL2 Remora interpreter (`eval-app`, `eval-app-list`). It is partial-correctness style, with every rule assuming `(not (reserrp ...))`. Chaining the rules gives a commutative-diagram theorem: applying an integer binary primop to two prefix-compatible arrays is a pairwise list map over replicated cells, repacked. The paper also mentions a commutativity corollary. The author's helper functions must be defined by the model:
- `pairwise-curry-binary-fn`, `pairwise-curry-binary-x-fn` and `pairwise-binary-args-fn`;
- `get-cells-from-expr-value` and `expr-is-nested-vectors-of-base-values`;
- `list-of-primop-int-binary` and `list-of-base-values`.

**Acceptance criteria.** All are against a pinned interpreter snapshot (see Inputs).
1. `propagate-not-reserrp-cells-at-depth-in-expr-value-list-when-vector` (Sec. 3, p.5) is proved verbatim.
2. `eval-app-list-when-primop-binary-and-bases` (p.5) is proved, with the model's definitions of the three helpers.
3. `eval-app-when-funval-is-binary-op` (p.6), the one-step `eval-app` rule, is proved.
4. `undo-expr-value-with-nonempty-dims-3` (p.6–7), the glue lemma, is proved verbatim. All its functions are in the interpreter.
5. `eval-app-when-funval-is-binary-op-fully` (p.7–8) is proved. The `arg2l` typo is read as `arg2`. If the pinned interpreter routes zero dimensions to `eval-app-empty`, the hypotheses may add `pos-listp` for the frames; that weakening must be reported.
6. Corollary (Sec. 3, end): for `+`, `(eval-app plus (list a b) l)` equals `(eval-app plus (list b a) l)` when both are non-error and compatible. The exact statement is the model's; the grader checks that it is non-vacuous on a concrete example.
7. Sanity checks by evaluation, run on the interpreter:
   - `[1 2] + [[1 2] [3 4]]` gives `[[2 3] [5 6]]`;
   - `[1 2] + [[1 2] [[5 6]]]` gives an error;
   - `[1 2 3] + [4 5]` gives an error (Sec. 2).
   - Criterion 5's right-hand side agrees with the interpreter on these inputs.
   Section 4 (`nested-map`) is unfinished in the paper and is not graded.

**Inputs beyond the paper.**
- **The Kestrel Remora interpreter (others' code, mainly Coglio)** is on master only, at `books/kestrel/remora`. The first commit is 37bfec4ecf, dated 2026-04-08, after the 8.7 release (2026-03-23). It is not in 8.7.
  - The interpreter's include closure (`expression-evaluation`) is 27 Remora books plus master-only system books such as `kestrel/fty/fty-treeset` (2026-07-26) and `kestrel/fty/nat-list-list` (2026-05-06).
  - It must be vendored as a pinned snapshot and checked to certify on 8.7 before any run.
  - The interpreter changed after the paper was written: curried primops on 2026-07-20, mutual recursion on 2026-08-04, and `eval-app-empty`.
- `prefixp` (std/lists) and fty `reserrp` (kestrel/fty) are in 8.7.

**Leakage.**
- The author's own lemmas are nowhere on master. A grep for `pairwise-curry-binary`, `undo-expr-value-with-nonempty-dims`, `get-cells-from-expr-value` and `nested-map` finds nothing, and the README has no directory for the paper.
- A snapshot exposes adjacent work by others:
  - Coglio's `evaluation-rules.lisp`: `lift-expr-value-to-frame-*` rules and `eval-app-of-int-add-no-lifting`;
  - `matmul-verification.lisp` and `softmax-verification.lisp`.
- The full Remora directory also contains `definductive` uses, which leak paper 1. Ship only the interpreter closure.

**Special rules / verdict.** No ttags are needed.
- **Feasible with setup:** we must build, pin and certify on 8.7 a pre-paper snapshot of the interpreter closure. This backport is untested.
- Even then, criteria 3 and 5 are very hard (the author reports a year of work).
- Not feasible from 8.7 alone.

---

## 5. hardin-arrayset — "Arrayset Revisited"

**What to build.**
- The circular-list array-backed multiset in Restricted Algorithmic Rust. It is `Arrayset` with `anext`, `avals`, `free_lst`, `used_lst` and `err`, and `ARR_SZ` = 1024 (Sec. 5.1).
- The operations `aset_init`, `aset_add`, `aset_del_head`, `aset_del`, `aset_transfer`, `aset_find_val_from`, `free_head` and `used_head`.
- A translation path from RAR to ACL2 RTL-record code. The paper's path is a Plexi-style RAR-to-RAC transpiler followed by the RAC translator (Fig. 3).
- The verification layer: preconditions, `no-dups-anext`, `aset-used-list`/`aset-free-list` and the correctness theorems.

**Acceptance criteria.**
1. The RAR source compiles with `rustc`. `free_head`, `used_head`, `aset_add`, `aset_del_head` and `aset_del` match Figs. 5–6 and Sec. 5.1 verbatim. The model writes `aset_transfer`, `aset_find_val_from` and `aset_init` from the prose of Sec. 5.1.
2. The ACL2 code is produced mechanically, by running the RAC translator (`projects/rac`) on RAC output from the model's transpiler or from hand-written RAC. The generated `ASET_DEL` has the shape of Fig. 7: `AG`, `AS`, `IF1`, `LOG<`, `LOGAND1`, `LOG<>`, `BITS`/`SI` and an `MV-LET`. It certifies against `rtl/rel11/lib/rac`.
3. An executable check on a small instance reproduces Fig. 4(b):
   - (a) contents {33, 22}; `aset_del 22` leaves a used list of {33} and a free list one longer;
   - (b) the circular traversals 1→2→1 (used) and 5→1→3→4→5 (free).
   Note that panel (a) of the figure conflicts with the text; the text is authoritative.
4. `aset_add-val-at-used_head--thm` (Fig. 8) is proved verbatim.
5. `aset_del-val-at-free_head--thm` (Fig. 8) is proved verbatim.
6. `aset_del_head-used-list--thm` and `aset_del_head-free-list--thm` (Fig. 9) are proved verbatim, with the model's `asetp`, preconditions, `no-dups-anext` and list functions. The grader also checks that the hypotheses are satisfiable on the criterion 3 instance, to rule out vacuity.
7. Optional: preservation of the no-duplicates / permutation invariant by `aset_add` and `aset_del` (Sec. 5.1; the Verus analogue is in Fig. 10).

**Inputs beyond the paper.**
- **RAC translator (Russinoff)** is in 8.7 at `books/projects/rac`; `bin/` is empty. Building it needs g++, bison and flex, and **flex is missing**. Install flex or ship a prebuilt `rac` binary. The RAC parser has been on master since long before 8.7.
- **RTL rel11** (`rtl/rel11/lib/{rac,bits,defs}`) is in 8.7 and certified.
- **Plexi (Hardin's RAR-to-RAC transpiler)** is not public; the 2023 README says the prototype is not included. The model must write its own or hand-translate. The paper says Plexi is based on the `plex` crate, but there is no crate cache offline.
- Fair prior work by Hardin in 8.7:
  - `workshops/2020/hardin` (RAC stack);
  - `workshops/2023/hardin` (RAC circular doubly-linked list: `half-rac-thms`, `cdll-thms`, and Rust and RAC sources in `src/`).

**Leakage.**
- None found. Neither master nor 8.7 has an arrayset (grep for `arrayset`, `aset_del` and `anext` finds nothing), and `workshops/2026/README` lists the paper with no directory.
- The ACL2-22 predecessor [10] has no supporting books. The paper cites no URL for its code.

**Special rules / verdict.** No ttags are needed.
- **Feasible with setup:** install flex, or provide a prebuilt RAC parser, so the RAC route can be graded.
- Otherwise criterion 2 must be relaxed to accept hand-written RAC-style ACL2.
- Criteria 5–6 are hard (the author used the proof builder).

---

## 6. mccarthy-aes — "Verifying RustCrypto's Fixsliced AES-128 in ACL2: An Aeneas Backend and an Executable MIR Semantics"

**What to build.** Three artifacts (Sec. 1):
- (a) An ACL2 backend for Aeneas, plus Charon changes: a monomorphization carve-out, defunctionalized iterators and fueled loops (Sec. 3). It prints each crate as one book over a handwritten `rust-primitives` runtime, using `ok`/`result-fail`, `massert`, `array-index`, `IterMut` and `apply-back`.
- (b) RustCrypto `aes` v0.9.1 `fixslice32.rs`, extracted and proved equal to `kestrel/crypto/aes` for all keys and blocks (Sec. 5).
- (c) An executable MIR interpreter, with a loader for Charon ULLBC JSON (Sec. 6).

**Acceptance criteria.**
1. Extraction shape (Sec. 3, 3.3): the backend extracts
   - `rotate_rows_1` to `(defun aes-fixslice-encrypt-rotate-rows-1 (x) (b* (((ok v) (...-ror-distance 1 0))) (...-ror x v)))`;
   - `shift_rows_2` to a fueled `-loop0 (n iter back)` that uses `IterMut-next`, `option-case`, `apply-back` and a `massert` of length 8.
   Names may differ only in numeric suffixes.
2. The generated AES book certifies as plain ACL2 with no ttags, axioms or skip-proofs (Sec. 4.3). The paper's book has 74 defuns; the count is informative only.
3. Known answers by execution (Sec. 5.5):
   - the FIPS-197 C.1 vector, encrypt and decrypt with round trips, at fuel 100;
   - the A.1 key expansion against `aes::keyexpansion`.
4. `encrypt-correct` (Sec. 5) is proved verbatim with GL and rewriting, with no ttags in the include closure:
   `(implies (and (aes::inp key) (aes::inp block)) (equal (aes-fixslice-encrypt-encrypt 100 key block) (ok (aes::aes-128-encrypt block key))))`.
5. `decrypt-correct` (Sec. 5) is proved verbatim, against `aes::aes-128-decrypt`.
6. MIR interpreter (Sec. 6):
   - the loader imports Charon `--mir elaborated` ULLBC JSON for the crate;
   - the interpreter runs encrypt, reproducing FIPS-197 C.1 and B byte for byte, and decrypt inverts both;
   - 66 differential inputs (2 corner cases plus 64 pseudorandom) agree with `aes::aes-128-encrypt`.
   Coverage: 6 terminator kinds plus Abort, Assign/StorageLive/StorageDead, 8 rvalue forms and 12 binops, including the overflow-checked ones.

**Inputs beyond the paper.**
- **Aeneas and Charon (others' tools)** are external, built from OCaml 5.3 and Rust nightly-2026-06-01 respectively. Neither is installed, and building them needs the network.
- **The RustCrypto `aes` 0.9.1 source** (`src/soft/fixslice32.rs`, commit 507938c) is external, third-party, and not on disk.
- **`kestrel/crypto/aes/aes-spec`** is in 8.7, with `aes::inp`, `aes-128-encrypt/-decrypt` and `keyexpansion`. Its test book `aes-spec-tests.lisp` is master only (894b4cb87e, 2026-08-31).
- **GL** (`centaur/gl`), FTY and `kestrel/bv` are in 8.7.

**Leakage.**
- Master has all three artifacts:
  - `books/workshops/2026/mccarthy-aeneas/` (102 files: the generated book, `rust-primitives` and the full proof stack; 204c4d65f5, 2026-10-28);
  - `books/kestrel/rust/{mir,import,samples}` (164dd21c04, 2026-08-10), including the adapted `samples/aes_fixslice_encrypt.rs` and `aes_ullbc_elaborated.json.gz`.
  - Local copy: `reference-books/workshop-2026/mccarthy-aeneas`.
- URLs cited in the paper:
  - github.com/bendyarm/aeneas (acl2-backend branch, 23cf8c88), which has all 78 books in `tests/acl2`;
  - bendyarm/charon (58b7d543);
  - github.com/bendyarm/aeneas-acl2-devenv, Zenodo 10.5281/zenodo.22365956, and the image ghcr.io/bendyarm/aeneas-acl2-dev;
  - master commit b652707d.
- The prebuilt devenv image contains the backend itself, so it must not be used as the "Aeneas" input.
- 8.7 has only unrelated Axe AES equivalences (JVM/x86), and Axe needs ttags.

**Special rules / verdict.**
- Ttags are disallowed for criteria 2, 4 and 5, for parity with the paper.
- The GL blasts need several GB of RAM per book (7 GB OOM before the variable-order fix) and about 15 min of wall time.
- **Not feasible as specified** offline: no Aeneas/Charon toolchain, no crate source, and no network.
- **Feasible with setup X:** pre-provision upstream (not bendyarm) Aeneas and Charon builds plus the pristine crate source. Criteria 1–5 are then a very large task.
- A reduced variant is feasible from the paper and 8.7 alone: criterion 6 (MIR interpreter), with a hand-written ACL2 MIR fixture in place of the Charon JSON.

---

## Summary

| Paper | Build target | #criteria | Extra setup | Trust tags? | Feasibility |
|---|---|---|---|---|---|
| coglio-jurgensen-definductive | `definductive` event macro (proof-tree types, validity fns, defun-sk preds, rule thms, rule induction, `-alt` minimality) | 12 | none | no | feasible |
| chen-smtlink3 | Smtlink 3: 5 verified CPs (rewrite$-driven type inference / fixing / rewriting / extraction) + trusted SMT-LIB CP | 7 | Z3 (or any SMT-LIB2 solver) binary; Smtlink 2 in 8.7 as base | yes (final CP, tshell) | feasible with setup (solver + ttags) |
| bora-erlang | Erlang→FTY AST front end, CPS evaluator with fuel, encapsulated scheduler + defattach, two example proofs | 8 | Erlang/OTP for front end, or waive it and supply ASTs | no | feasible with setup; proofs (7–8) very hard |
| gamboa-remora | Lemma layer over Kestrel Remora interpreter: one-step + glue rules, `eval-app-...-fully`, commutativity | 7 | pinned post-8.7 snapshot of `kestrel/remora` interpreter closure (+ master-only kestrel/fty books), certified on 8.7 | no | feasible with setup (untested backport); not feasible from 8.7 alone |
| hardin-arrayset | RAR circular arrayset + RAR→RAC→ACL2 translation + Fig. 8/9 theorems | 7 | flex (or prebuilt RAC parser) to build `projects/rac`; Plexi unavailable, model writes own | no | feasible with setup |
| mccarthy-aes | Aeneas ACL2 backend + extracted fixsliced AES proofs + MIR interpreter/loader | 6 | upstream Aeneas+Charon (OCaml, Rust nightly), RustCrypto aes 0.9.1 source, multi-GB RAM for GL | no (disallowed for parity) | not feasible offline; feasible with heavy setup; MIR-only variant feasible |
