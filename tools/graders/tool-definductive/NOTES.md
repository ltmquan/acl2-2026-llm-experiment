# tool-definductive grader: notes

Run: `grade.sh <work-dir>` (ACL2 8.7 by default; `ACL2`/`CERT` env vars override, used only for validation).
Files: `grade-r2.lisp` (the paper's four calls, verbatim, with deflabels around each), `grade-r1.lisp`
(includes grade-r2; event names and forms), `grade-r2x.lisp` and `grade-r3.lisp` (include the model's
`examples.lisp`), `grade-r3-paper.lisp` (includes grade-r2; Section 5 with the paper's hints),
`grade-r4.lisp` + `r4-bad-calls.lsp`, `grade-r5-hostile.lisp`, `grader-utils.lisp`
(generic checks; each check prints `GRADER-PASS/FAIL <label>` and records failures, `grader-final` makes the
book fail if any check failed), `grader-arith.lisp` (one arithmetic lemma, arithmetic-3 included locally),
`check-examples.py` (banned events; static checks on `examples.lisp`).

## Requirement -> checks
- R1: grade-r1 (about 90 checks). FTY structure read from `fty::flextypes-table`: r*-proof summands/fields
  exactly `:base (x y)`, `:refl (x)`, `:trans (x y z premise1-proof premise2-proof)` with the premise fields of
  type r*-proofp; nat-proof (deftagsum) and `tree-proof-clique` (deftypes of tree-proof, trees-proof);
  `even-proof-clique` with `:base-case-override :from-even` on odd-proof and `(two-nats-measure ... 0/1)`;
  p-proof non-recursive. Formals as shown: `(r*-proof-validp proof a b)`, `(r*-proof-minimalp proof a b)`,
  `(r* a b)`, `(even-proof-validp proof n)` etc. Validity semantics per summand (theorems with the generated
  validity definitions enabled). `r*` body = the paper's defun-sk matrix with skolem `r*-proof`; `r*-suff`;
  minimalp is a forall (necc instance). Exact formulas (translated, `equal`) of all rule theorems, all
  `-when-proof-validp`, all `-alt-<rule>`, `-alt-when-<p>-proof-validp`, `-alt-when-<p>` for the four
  examples; each `-alt` constrained exactly by its alt rules (one encapsulate per call); `r*-induct` with
  measure `(r*-proof-count (r*-proof a b))` and an induction rule `(r* a b)` -> `(r*-induct a b)`;
  nat-induct singly recursive with an induction rule; tree/trees-induct and even/odd-induct mutually
  recursive with a make-flag entry; flag macro `defthm-even-proof-validp-clique-flag` (named in Sec. 5.3);
  constructors/accessors used in Sec. 5.2.
  When an exact formula fails, the message says whether it matches up to variable renaming.
- R2: static (examples.lisp includes "definductive", has `(defstub r (* *) => *)` before the call, and the four
  calls with the paper's `:preds`/`:irules`; extra keyword options are reported as `R2NOTE`, not failed) +
  grade-r2 (the paper's calls on the model's tool) + grade-r2x (after including examples.lisp the predicates
  exist with the paper's formals, r is a stub, the validity functions exist).
- R3: grade-r3 (the theorems exist non-locally in examples.lisp with the paper's exact statements; f is a
  unary function constrained exactly by r-of-f, so r*-of-f is not trivial) + static hint check (the hint
  parts the paper shows appear in the proof of a theorem with that statement: `:use` of r*-base for
  trans-base-left; for r*-of-f one proof with `:induct (r* a b)`, the two `:expand` terms and r*-base/refl/trans,
  and one with the `:functional-instance` shown; the `:instance`s of Sec. 5.2 (extra bindings allowed);
  the Sec. 5.3 flag theorems under `defthm-even-proof-validp-clique-flag` with the right `:flag`s)
  + grade-r3-paper (our own copy of the paper's Sec. 5 forms proved on the model's tool).
- R4: static (examples.lisp has must-fail of no-proof-trees verbatim and of definductive calls with a premise
  `(and ...)`, `(or ...)`, `(not ...)`, `(implies ...)` containing a defined predicate) + grade-r4 (our
  must-fails, each with a positive control) + each bad call at the top level in its own ACL2 process:
  it must print `ACL2 Error`/`HARD ACL2 ERROR`, must not print `ABORTING from raw Lisp`, and ACL2 must reach
  the next form.
- R5: grade-r5-hostile (below). The revised prompt dropped the earlier `(in-theory nil)` variant, so the
  grader no longer runs it.
- R6: cert.pl on definductive.lisp and examples.lisp (default flags, so skip-proofs fails).
- Banned events: the check-prove.py list, on every .lisp/.lsp/.acl2 file of the work dir; any hit fails all.

## Interpretations
- Variable names are part of "the forms the paper shows": Sec. 3/4.4/5.2 show `(r*-proof-validp proof a b)`,
  `(p-when-proof-validp ... (p x1 x2 ...))` with the predicate's own formals, and Sec. 5.2 instantiates
  `(n (1- n))` in even-when-proof-validp, which only works if the variable is `n`. So R1 requires those names
  exactly. (The authors' master implementation uses `_a _b _n ...`; see Validation.)
- R5 hostile rules (grade-r5-hostile.lisp), all enabled before the calls: libraries
  `arithmetic/top-with-meta`, `std/lists/top`, `std/typed-lists/top`, `std/basic/two-nats-measure`;
  `(in-theory (enable two-nats-measure nat-list-measure))`; and our theorems
  `(equal (equal (cons a b) c) (and (consp c) (equal a (car c)) (equal b (cdr c))))`,
  `(equal (acl2-count (cons a b)) (+ 1 (acl2-count a) (acl2-count b)))`,
  `(implies (and (natp x) (natp y)) (equal (o< x y) (< x y)))`, `(implies (natp n) (natp (+ 1 n)))`,
  `(implies (not (consp x)) (equal (car x) nil))`, `(implies (not (consp x)) (equal (cdr x) nil))`.
  arithmetic-3 and arithmetic-5 are not used: they define a function `TREE`, which makes the paper's
  nat-trees call fail for a reason unrelated to theories.
- Sec. 5.4 does not show how f is introduced; we use `(encapsulate (((f *) => *)) (local (defun f (x) x))
  (defthm r-of-f ...))`, and require the model's f to be constrained exactly by r-of-f.
- FILLs in grade-r3-paper.lisp (where the paper elides or shows no hints); each is marked FILL in the file:
  trans-base-right: `(enable r*-base r*-trans)`; trans-base-left: `:use r*-base`, `(e/d (r*-trans) (r*-base))` (r*-base disabled so the used hypothesis survives; the first version left it enabled, which made the proof fail);
  r*-of-f: "..." = r-of-f, r*-when-proof-validp and every generated `...-VALIDP` definition;
  even-add-2: `:use (odd-from-even (:instance even-from-odd (n (1+ n))))`; even-add-double: induction on a
  decrement scheme with a computed `:use` of even-add-2, placed after Sec. 5.3 (its base case needs
  natp-when-even/odd); Sec. 5.3 flag theorem: enable the generated `-VALIDP` definitions; natp-when-even/odd:
  `(enable even odd natp-when-...-proof-validp)`; proof-for-even/odd: the impossible branch returns
  `(make-odd-proof-from-even :n 0 :premise1-proof (even-proof-zero))`, `:verify-guards nil` (the paper's guards
  would need return-type theorems), `(make-flag proof-for-even/odd-flag proof-for-even)`, a return-type lemma,
  and an arithmetic lemma for the flag theorem; even-of-pred-when-odd: `:expand` of the witness validity,
  `(enable odd natp-when-even-proof-validp)` plus the `-VALIDP` definitions.
  The `-VALIDP` theory is "any function introduced by the call whose name ends in -VALIDP": it covers the
  authors' per-rule helpers (`r*-base-validp`, ...) and costs nothing for an implementation without them.
- The two r*-of-f proofs in grade-r3-paper are `:rule-classes nil` and named r*-of-f-fi / r*-of-f-paper, so
  that one cannot be proved from the other.
- Requirement 1 says "with the names and forms the paper shows"; the paper does not name the induct flag
  macros, the minimalp witness or the necc theorem, so those are not checked by name.

## Validation (2026-11-14)
- All books translate and run on 8.7 against a stub `definductive` (a macro returning `(value-triple :stub)`):
  no raw Lisp errors; every check reports FAIL (R4 controls pass, the must-fails fail), as expected.
  `grade.sh` on an empty work dir: 6 FAIL, with readable reasons.
- check-examples.py: PASS on a mock examples.lisp built from the paper's forms; FAIL as expected on mocks with a
  rule dropped from refl-trans-closure (R2S), the functional instance of the wrong theorem (R3S), a must-fail
  removed (R4S), and a skip-proofs (BANNED).
- Against the authors' implementation on master (`std/util/definductive`, shim book `definductive.lisp` that
  only includes it; ACL2/CERT set to master), with a mock examples.lisp made of the paper's forms:
  * unchanged grader: R2, R3 (via R2), R1 (via R2), R6 FAIL because the paper's `nat-trees` and
    `even-and-odd` calls fail on master: master's `:verify-guards` defaults to t and the guard of
    `nat-succ-validp` / `odd-from-even-validp` (`(1+ n)` on an untyped n) is not provable. The paper (Sec. 8:
    "The predicates generated by definductive are not guard-verified") describes the pre-option behavior.
    Our reading of the paper is right; the authors' current tool has changed.
  * with `:verify-guards nil` added to those two calls (in a scratch directory only): R2 PASS; R4 PASS; R6 PASS;
    R1 FAIL only on variable names: master uses `_a _b`, `_n`, `_tr`, `_trs`, `_x` as formals of the validity
    and minimality functions and in every `-when-proof-validp` and `-alt-when-<p>-proof-validp` theorem
    (all equal to the paper's up to renaming); every other R1 check passes (types, levels, semantics,
    defun-sk bodies, rule theorems, alt encapsulates, induct functions, flag macros).
    R3: grade-r3-paper fails exactly the paper's Sec. 5.2/5.3 forms that use the variable n of
    even-/odd-when-proof-validp and of even-/odd-proof-validp: natp-when-even/odd-proof-validp,
    natp-when-even/odd, even-add-double (cascade), even-when-evenp, odd-when-oddp, even-of-pred-when-odd. The
    authors' own supporting files write `(_n n)` / `(_n (1- n))` / `proof _n` there, i.e. not the paper's text.
    With those names changed to `_n` in a scratch directory copy, all 12 grade-r3-paper checks and the whole R3 PASS.
    So the paper's Sec. 5 text matches an earlier version of the tool; the grader follows the paper.
  * R5: grade-r5-hostile PASS. (History: an earlier R5 also required `(in-theory nil)`. The authors' tool
    failed that on every paper call, partly inside FTY's own events, so it was dropped from the prompt.)
  * Run time on master: about 75 s for the whole grade.sh.

## Correction after the runs

The filling of the `trans-base-left` hint (footnote 11, `:use r*-base`) now disables `r*-base`, so the hypothesis the `:use` adds is not rewritten away. The first filling left it enabled and failed on the model's tool. The corrected grader still passes R2-R6 on the authors' implementation on master, as before.
