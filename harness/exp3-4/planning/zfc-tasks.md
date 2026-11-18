# ACL2(zfc) future-work tasks: candidate task statements

Source: Matt Kaufmann's `books/projects/set-theory/` in the ACL2 repository
(`/opt/acl2`, `origin/master`), xdoc topic `zfc-future-work` in `doc.lisp`.
Everything below was checked against local files only.

## 0. Provenance, base snapshot, build, axioms

### 0.1 Correction: where the future-work list comes from

The list is **not** in 6211b25fd4 (2026-05-23). `git show 6211b25fd4:books/projects/set-theory/doc.lisp`
has no `zfc-future-work` topic. The history is:

| commit | date | what happened |
|---|---|---|
| 6211b25fd4 | 2026-05-23 | Tweaks to the `zfc`/`zfc-model` docs and `logic.txt`. No future-work list yet. |
| cdb4cbdc58, 6d232162e4, b7c01a067f, e22f084640, 0ebe09cad6 | 2026-06-17..28 | `topology/` subdirectory and `finite/` and `utilities/` added; compact⇒regular and compact⇒normal; closed subspace of a compact space is compact (the last two written with Claude Code). |
| 904acf5898, e867f4eea5 | 2026-07-01 | `reals/` started: Dedekind cuts, sum, negation. |
| f4711653c2 | 2026-07-04 | `algebra/` started (groups, the integers as a group). **The list first appears, as `future-work.txt`.** |
| 65589c5afd | 2026-07-05 | `future-work.txt` replaced by xdoc topic **`zfc-future-work`** (the same content, revised). |

The list refers to `topology/`, `algebra/` and `reals/`, and none of these exist at 6211b25fd4.
So 6211b25fd4 is not a usable base: it has 33 files and no topology, algebra, reals, finite
or utilities. **The fair base is 65589c5afd** (equivalently f4711653c2, since only the docs differ).

### 0.2 Base tree at 65589c5afd (56 `.lisp` books, plus `.sys/` useless-runes files)

```
README.txt  cert.acl2  portcullis.acl2  portcullis.lisp  package.lsp  logic.txt  to-do.txt  top.lisp  doc.lisp
base.lisp  bijection.lisp  cantor.lisp  defthmz-plus.lisp  finseqs.lisp  foldr.lisp  fun-space.lisp
identity.lisp  image-plus.lisp  induction-support.lisp  induction.lisp  injective-funp.lisp
intersection.lisp  inverse.lisp  iterate.lisp  ordinals.lisp  phoenix.lisp  prove-acl2p.lisp
restrict.lisp  schroeder-bernstein-1.lisp  schroeder-bernstein-support.lisp  schroeder-bernstein.lisp
set-algebra.lisp  skolem.lisp  swap.lisp  tc.lisp  zfns.lisp  zify-motivation.lisp  zify.lisp
finite/{cert.acl2, base, finite-bang, finite-domain, finite-image, finite-inverse, finite-restrict, finite-union2, top}.lisp
topology/{cert.acl2, prelims, compact, normal, subspace, compact-is-regular, compact-is-normal,
          closed-subspace-is-compact, finite-intersection-closure}.lisp
algebra/{groups, integer-group}.lisp
reals/{cert.acl2, dedekind, sum, negative}.lisp
utilities/{cert.acl2, defthme, remove-hypz, change-pkg}.lisp
```

### 0.3 What changed on master after the base (65589c5afd..origin/master, up to 1d2b39a424, 2026-11-12)

The `.lisp` changes in the directory are:

- 80e6c7170c: a comment in `prove-acl2p.lisp`.
- 8db0a0132b: a one-line fix in `zify.lisp` (a doubled word in an error message).
- 93217959b5 and 12f9e9617b: comments in `base.lisp`, about `min-in` giving Global Choice.
- 4dbf21fe2b (2026-11-09): the macro `force?` is removed in favor of `force` (`force?-props` is renamed `force-props`) in `base.lisp`, `zify.lisp` and `doc.lisp`.
- 9a31d62d86 and 20f539fad6: useless-runes files.

**No item on the future-work list was done on master after the list was written.**
I grepped master for ultrafilter, Ramsey, transfinite recursion, metric space and cardinal,
in set-theory/, hol-in-acl2/ and the rest of books/. The only hits are in the
future-work doc itself. So no item has an authors' version to compare against, and there is
no leakage from master. The list says "some progress by Matt Kaufmann" on cardinals and on
transfinite recursion, but that work is **not in the repository**. It may appear later, so
re-check master before grading.

Practical consequence: master's `books/projects/set-theory` (as in `/opt/acl2-master/books`, 1d2b39a424)
has the same mathematical content as the base. It is the simplest base to hand out, and it builds
with the master `saved_acl2`.

### 0.4 How ACL2(zfc) is built and used

- **No special image and no special flag.** ACL2(zfc) is ordinary ACL2 with `projects/set-theory/top`
  included (`:doc zfc`: "System View: ACL2(zfc) is the system obtained by including the community book
  projects/set-theory/top"). The only restriction is that ACL2(r) is excluded (`cert.acl2` has
  `; cert_param: (non-acl2r)`).
- Portcullis: `cert.acl2` does `(include-book "portcullis")`. `portcullis.acl2` does `(ld "package.lsp")`,
  which runs `defpkg "ZF"`. The ZF package imports the ACL2 exports except `apply omega union intersection fn-equal map tc subsetp functionp`.
  Each subdirectory's `cert.acl2` does `(include-book "../portcullis")`. A solution directory needs a
  `cert.acl2` along the lines of `(include-book "projects/set-theory/portcullis" :dir :system)` plus
  `; cert_param: (non-acl2r)`, and its books start with `(in-package "ZF")`.
- `top.lisp` does **not** include `topology/`, `algebra/` or `reals/`. Include those books explicitly.
- I verified the build here (20 s wall time with `-j4`, 70 books including dependencies):
  ```
  cd /opt/acl2-master/books && ./build/cert.pl --acl2 /opt/acl2-master/saved_acl2 -j4 \
    projects/set-theory/top.lisp projects/set-theory/topology/compact-is-normal.lisp \
    projects/set-theory/topology/closed-subspace-is-compact.lisp \
    projects/set-theory/topology/finite-intersection-closure.lisp \
    projects/set-theory/algebra/integer-group.lisp projects/set-theory/reals/sum.lisp \
    projects/set-theory/reals/negative.lisp projects/set-theory/finite/top.lisp
  ```
  Note: this wrote `.cert` files into `/opt/acl2-master/books`.

### 0.5 defaxiom / ttag situation

- **No `defaxiom`, no `defttag`, no trust tags** anywhere in the set-theory books. `:doc zfc` says:
  "There is no use of trust tags". The grep hits are only in `doc.lisp` prose and in comments.
- The ZF axioms live in one `encapsulate` in `base.lisp`. It constrains `zfc`, `in`, `pair`, `min-in`,
  `union`, `omega` and `powerset`, and the local witness of `(zfc)` is `nil`. Every exported axiom
  has `(zfc)` as a hypothesis. Comprehension and Replacement are schemes, implemented by the macros
  `zsub` and `zfn`. Each instance introduces a constrained zero-ary *hypothesis function* `NAME$prop`
  (local witness `nil`) and records it in `zfc-table`. That table has a strict guard: it only accepts
  props justified by a `zsub`/`zfn` form or by `extend-zfc-table`, plus a pass-2 exception for
  `defthmz+`/`with-props`.
- `defthmz NAME FORM :props (p1 ... pk)` is `defthm` with `(force (p1)) ... (force (pk))` added as hypotheses.
  The default is `(zfc)`. Every `pi` must be a key of `zfc-table`. The meaning of "these hypotheses are true"
  comes from the metatheory in `:doc zfc-model` and `logic.txt`.
- **No defaxiom/ttag exception is needed.** Everything is a genuine ACL2 theorem with hypotheses.
  The harness does need these conventions:
  1. Accept final theorems whose hypotheses include `(zfc)` and other `zfc-table` keys, including
     `$prop`s from `zsub`/`zfn`/`zify`/`extend-zfc-table` events in the solution. `check-props`
     enforces this automatically. A task's `:props` list is therefore **open**: the solver may add
     any `zfc-table` key.
  2. Ban `skip-proofs`, `defaxiom`, `defttag`, redefinition (`redef`, `set-ld-redefinition-action`),
     direct `(table zfc-table ...)` events, and `table-redo`/`with-props` outside `defthmz+`.
     Or flag them for manual review.
  3. Watch out for `utilities/defthme.lisp`. Its `try-cmd` wraps a failed forward/backward lemma in
     **`skip-proofs`**, and so does its `:skip` option. A textual ban on `skip-proofs` will not
     catch this. Certify with the default `:skip-proofs-okp nil` (the `cert.pl` default), which rejects
     any book that ran skip-proofs, or ban `:skip` and inspect `try-cmd-table`.
  4. Suggested checker: the harness supplies a definitions book with the definitions below, verbatim.
     The solver's book includes it. A checker book includes the solution and restates each target as
     `(defthmz T FORM :props <solver's list> :hints (("Goal" :by SOLVER-THM)))`.

All the "candidate ACL2(zfc) statements" below were admitted by the master ACL2 on top of the
base books, but **only as translation checks** (theorems wrapped in `skip-proofs`, `:rule-classes nil`).
The combined check file is `/home/user/acl2-exp/ext/zfc-task-specs-check.lisp`. It runs cleanly
with `(ld "zfc-task-specs-check.lisp")` after the topology, algebra and reals books are certified.
The `:props` lists shown are a plausible minimum and are open (convention 1). Rule classes
are not part of any task: the checker should restate targets with `:rule-classes nil`, because some
targets, such as `tr-unique` and `eqnum-naturals-equal`, are not valid `:rewrite` rules as written. The `skip-proofs` wrapper
in that file is for checking the statements only. It must not appear in any model solution.

### 0.6 Base vocabulary (ZF package)

| notion | base name (book) |
|---|---|
| membership, subset, extensionality | `(in a x)`, `(subset x y)`, `extensionality` (base) |
| {x,y}, {x}, ∪, x∪y, x∪{s} | `pair`, `singleton`, `union`, `union2`, `insert` (base) |
| power set, ω, empty set | `powerset`, `(omega)`, `0` (base); naturals are von Neumann ordinals, so `(in i n)` ⇔ i<n (`in-natp`) |
| ordered pair | ACL2 `cons` (`cons-as-ordered-pair`), `car`/`cdr` |
| choice / regularity | `(min-in x)` (global choice) |
| comprehension, replacement | macros `zsub`, `zfn`; `zify` turns an ACL2 function into a set function |
| A×B | `prod2` (base), `prod2$prop`, `in-prod2` |
| relation, function | `relation-p`, `funp` (base) |
| application, domain, inverse, image | `apply`, `domain`, `inverse`, `image` (= domain of inverse) |
| composition | `(compose f g)` = f∘g, `rcompose` (base) |
| injective, bijection | `injective-funp` (base), `bijection` (bijection.lisp) |
| restriction | `(restrict f s)` (restrict.lisp) |
| difference, intersection | `diff`, `int2` (set-algebra.lisp); `(intersection s)` (intersection.lisp) |
| function space B^A | `(fun-space a b)` (fun-space.lisp) |
| equinumerous | `(exists-bijection s1 s2)` (schroeder-bernstein.lisp); theorem `schroeder-bernstein` |
| Cantor | `cantor`: `(implies (funp f) (not (equal (image f) (powerset (domain f)))))` (cantor.lisp) |
| finite | `(finite s)` = image of a function with a natural-number domain covers s (finite/base.lisp); `finite-union2`, `finite-implies-finite-image`, `finite-restrict`, `bijection-collapse-enum` |
| ordinals | `transitive`, `in-is-linear`, `ordinal-p`, `ordinal-trichotomy`, `ordinal-proper-subset-is-element` (base, ordinals.lisp) |
| ∈-induction | macro `prove-inductive-suffices` (induction.lisp), `tc` (tc.lisp) |
| iteration, finite sequences | `iterate`, `finseqs` |
| identity function, swap, Skolem function | `identity-fun`, `swap`, `skolem` |
| topology | `tpp` (= `tpp-int2` ∧ `tpp-union`; the space is `(union tp)`), `closed`, `compact`, `open-cover`, `hausdorff`, `regular`, `normal`, `subspace`; theorems `compact-hausdorff-is-regular`, `compact-regular-is-normal`, `compact-hausdorff-is-normal`, `closed-subspace-is-compact`, `finite-intersection-closure` |
| groups | `apply2`, `group-identity-p`, `group-inverse-p`, `group-associative-p`, `groupp`, `abelian-p`, `abelian-group-p`; `integers`, `abelian-group-p-integers` |
| reals | Dedekind cuts: `rational-setp`, `drp`, `(rationals)`, `r2dr`, `dr+`, `dr-unary--`, props `dr-prop0`, `dr-sum-prop`. There is **no real multiplication, order or completeness yet.** |
| universe | `v`, `v-omega` (contains all ACL2 objects), `acl2p` |

---

## 1. Selected (tractable) tasks

Each task is self-contained. The harness should ship the listed definitions verbatim as a "task
definitions" book. The solver must prove the theorems about those definitions, may add any lemmas,
definitions and `zsub`/`zfn` instances it likes, and may use any `zfc-table` props.

### T1. Equivalence relations and quotients

**Statement.** Let S be a set and R a set of ordered pairs. R is an *equivalence relation on S* if
R ⊆ S×S and R is reflexive on S, symmetric and transitive. For a∈S, the *class* [a] = {y∈S : (a,y)∈R}.
The *quotient* S/R = {c ⊆ S : c = [a] for some a∈S}. A *partition* of S is a set P of nonempty, pairwise
disjoint sets whose union is S. For a partition P, let ~_P = {(x,y)∈S×S : x,y lie in a common block of P}.
Prove, for every equivalence relation R on S and every partition P of S:
(a) for a,b∈S, [a]=[b] iff (a,b)∈R;
(b) S/R is a partition of S;
(c) ~_P is an equivalence relation on S;
(d) S/(~_P) = P and ~_(S/R) = R;
(e) there is a function with domain S and image S/R sending each a to [a].

**Base names used:** `prod2`, `in`, `subset`, `powerset`, `union`, `int2`, `funp`, `domain`, `image`, `apply`, `zsub`.

```lisp
(defun-sk refl-on (r s) (forall x (implies (in x s) (in (cons x x) r))))
(defun-sk sym-rel (r) (forall (x y) (implies (in (cons x y) r) (in (cons y x) r))))
(defun-sk trans-rel (r)
  (forall (x y z) (implies (and (in (cons x y) r) (in (cons y z) r)) (in (cons x z) r))))
(defun equivalence-on (r s)
  (and (subset r (prod2 s s)) (refl-on r s) (sym-rel r) (trans-rel r)))
(zsub eqv-class (a r s) y s (in (cons a y) r))
(defun-sk is-eqv-class (c r s) (exists a (and (in a s) (equal c (eqv-class a r s)))))
(zsub quotient (r s) c (powerset s) (is-eqv-class c r s))
(defun-sk pairwise-disjoint (p)
  (forall (c d) (implies (and (in c p) (in d p) (not (equal c d))) (equal (int2 c d) 0))))
(defun partition-p (p s) (and (equal (union p) s) (not (in 0 p)) (pairwise-disjoint p)))
(defun-sk same-block (x y p) (exists c (and (in c p) (in x c) (in y c))))
(zsub partition-rel (p s) q (prod2 s s) (same-block (car q) (cdr q) p))
(defun-sk maps-to-classes (f r s)
  (forall a (implies (in a s) (equal (apply f a) (eqv-class a r s)))))
(defun-sk exists-quotient-map (r s)
  (exists f (and (funp f) (equal (domain f) s) (equal (image f) (quotient r s))
                 (maps-to-classes f r s))))

(defthmz eqv-class-equal
  (implies (and (equivalence-on r s) (in a s) (in b s))
           (equal (equal (eqv-class a r s) (eqv-class b r s)) (in (cons a b) r)))
  :props (zfc prod2$prop eqv-class$prop))
(defthmz quotient-is-partition
  (implies (equivalence-on r s) (partition-p (quotient r s) s))
  :props (zfc prod2$prop diff$prop eqv-class$prop quotient$prop))
(defthmz partition-rel-is-equivalence
  (implies (partition-p p s) (equivalence-on (partition-rel p s) s))
  :props (zfc prod2$prop diff$prop partition-rel$prop))
(defthmz quotient-of-partition-rel
  (implies (partition-p p s) (equal (quotient (partition-rel p s) s) p))
  :props (zfc prod2$prop diff$prop eqv-class$prop quotient$prop partition-rel$prop))
(defthmz partition-rel-of-quotient
  (implies (equivalence-on r s) (equal (partition-rel (quotient r s) s) r))
  :props (zfc prod2$prop diff$prop eqv-class$prop quotient$prop partition-rel$prop))
(defthmz quotient-map-exists
  (implies (equivalence-on r s) (exists-quotient-map r s))
  :props (zfc prod2$prop domain$prop inverse$prop eqv-class$prop quotient$prop))
```
**Difficulty:** moderate. Parts (a)–(c) are easy to moderate. (d) needs two extensionality
arguments. (e) needs a Replacement or `zify`-style construction.
**Later master version:** none. **Leakage:** none.

### T2. Cartesian product of an indexed family (with the Axiom of Choice)

The binary product `prod2` is already in `base.lisp`. The open item is the general product.

**Statement.** Let F be a function (a *family*) with index set I = dom F. Its product ΠF is the set of all
functions f with domain I such that f(i)∈F(i) for every i∈I. Prove:
(a) the membership characterization: f∈ΠF iff f is a function with domain I and f(i)∈F(i) for all i∈I;
(b) ΠF is empty iff F(i) is empty for some i∈I;
(c) if every F(i) is nonempty, then for every i∈I and y∈F(i) some f∈ΠF has f(i)=y;
(d) for any sets A, B, the product of the family {(0,A),(1,B)} is equinumerous with A×B.

**Base names used:** `fun-space`, `funp`, `domain`, `image`, `union`, `apply`, `prod2`, `pair`, `exists-bijection`, `min-in` (choice).

```lisp
(defun-sk choice-fn-p (f fam)
  (forall i (implies (in i (domain fam)) (in (apply f i) (apply fam i)))))
(zsub prod-family (fam) f (fun-space (domain fam) (union (image fam))) (choice-fn-p f fam))
(defun-sk nonempty-values (fam)
  (forall i (implies (in i (domain fam)) (not (equal (apply fam i) 0)))))
(defun-sk has-coordinate (fam i y)
  (exists f (and (in f (prod-family fam)) (equal (apply f i) y))))

(defthmz in-prod-family
  (implies (funp fam)
           (equal (in f (prod-family fam))
                  (and (funp f) (equal (domain f) (domain fam)) (choice-fn-p f fam))))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop))
(defthmz prod-family-empty-iff
  (implies (funp fam)
           (iff (equal (prod-family fam) 0) (not (nonempty-values fam))))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop))
(defthmz projection-surjective
  (implies (and (funp fam) (nonempty-values fam) (in i (domain fam)) (in y (apply fam i)))
           (has-coordinate fam i y))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop))
(defthmz prod-family-binary
  (exists-bijection (prod-family (pair (cons 0 a) (cons 1 b))) (prod2 a b))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop))
```
**Difficulty:** moderate. (b) is the Axiom of Choice in product form, available through `min-in` and a
Replacement instance. (d) is the longest part.
**Later master version:** none.

### T3. Filters and ultrafilters

**Statement.** A *filter on* a set S is a set U of subsets of S with S∈U, ∅∉U, closed upward within S
(X∈U and X⊆Y⊆S imply Y∈U) and closed under binary intersection. An *ultrafilter on S* is a filter U on S
such that for every X⊆S, X∈U or S∖X∈U. For a∈S, the *principal filter* at a is {X⊆S : a∈X}.
A filter U on S is *maximal* if every filter V on S with U⊆V equals U. Prove:
(a) every principal filter at a point of S is an ultrafilter on S;
(b) a filter on S is an ultrafilter iff it is maximal;
(c) if U is an ultrafilter on S, X,Y⊆S and X∪Y∈U, then X∈U or Y∈U;
(d) an ultrafilter on S that contains a finite set is principal; hence every ultrafilter on a finite set is principal.
(e) *(stretch, separately graded)* there is a non-principal ultrafilter on ω.

**Base names used:** `powerset`, `subset`, `int2`, `diff`, `union2`, `finite`, `(omega)`, `zsub`.

```lisp
(defun-sk upward-closed (u s)
  (forall (x y) (implies (and (in x u) (subset x y) (subset y s)) (in y u))))
(defun-sk int2-closed (u)
  (forall (x y) (implies (and (in x u) (in y u)) (in (int2 x y) u))))
(defun filter-on (u s)
  (and (subset u (powerset s)) (in s u) (not (in 0 u)) (upward-closed u s) (int2-closed u)))
(defun-sk ultra-p (u s)
  (forall x (implies (subset x s) (or (in x u) (in (diff s x) u)))))
(defun ultrafilter-on (u s) (and (filter-on u s) (ultra-p u s)))
(zsub principal-filter (a s) x (powerset s) (in a x))
(defun-sk principal-p (u s) (exists a (and (in a s) (equal u (principal-filter a s)))))
(defun-sk maximal-filter-p (u s)
  (forall v (implies (and (filter-on v s) (subset u v)) (equal u v))))
(defun-sk exists-nonprincipal-ultrafilter (s)
  (exists u (and (ultrafilter-on u s) (not (principal-p u s)))))

(defthmz principal-filter-is-ultrafilter
  (implies (in a s) (ultrafilter-on (principal-filter a s) s))
  :props (zfc diff$prop principal-filter$prop))
(defthmz ultra-iff-maximal
  (implies (filter-on u s) (iff (ultra-p u s) (maximal-filter-p u s)))
  :props (zfc diff$prop))
(defthmz ultrafilter-prime
  (implies (and (ultrafilter-on u s) (subset x s) (subset y s) (in (union2 x y) u))
           (or (in x u) (in y u)))
  :props (zfc diff$prop))
(defthmz ultrafilter-with-finite-member-is-principal
  (implies (and (ultrafilter-on u s) (in x u) (finite x)) (principal-p u s))
  :props (zfc diff$prop principal-filter$prop))
(defthmz ultrafilter-on-finite-set-is-principal
  (implies (and (ultrafilter-on u s) (finite s)) (principal-p u s))
  :props (zfc diff$prop principal-filter$prop))
;; (e) stretch:
(defthmz nonprincipal-ultrafilter-exists
  (exists-nonprincipal-ultrafilter (omega))
  :props (zfc diff$prop principal-filter$prop))
```
**Choice in the base:** the base has **global choice** through `min-in`, but **no Zorn's lemma, no
well-ordering theorem and no transfinite recursion**. Part (e) therefore needs one of those built
first, for example through T5. **Difficulty:** (a)–(c) easy to moderate; (b) the maximal⇒ultra
direction is moderate; (d) moderate, by induction on finite sets with `finite` as defined;
(e) very hard. **Later master version:** none. Recommend (a)–(d) as the task and (e) as a separate stretch.

### T4. Cardinality basics

The base has Cantor's theorem (`cantor`: no function from a set onto its power set) and
Schröder–Bernstein (`schroeder-bernstein`, in terms of `exists-bijection`), but no "injects into"
notion and no results about finite cardinalities.

**Statement.** Write A ≈ B when there is a bijection from A onto B (`exists-bijection`), and A ≼ B when
there is an injective function with domain A and image contained in B. Prove:
(a) ≈ is reflexive, symmetric and transitive;
(b) A ≼ B and B ≼ A imply A ≈ B;
(c) S ≼ P(S) but not P(S) ≼ S, for every set S;
(d) pigeonhole: for every natural n, not (n+1 ≼ n), where n = {0,…,n−1};
(e) for naturals m,n, m ≈ n implies m = n;
(f) ω is not finite;
(g) a set is finite iff it is equinumerous with some natural number.
(h) *(stretch, needs T5 or a well-ordering theorem)* every set is equinumerous with an ordinal; define |S| as
the least such ordinal and prove |S| = |T| iff S ≈ T.

**Base names used:** `exists-bijection`, `injective-funp`, `domain`, `image`, `powerset`, `finite`, `(omega)`, `natp`, `schroeder-bernstein`, `cantor`, `identity-fun`, `compose`, `inverse`, `bijection-collapse-enum`.

```lisp
(defun-sk injects-into (a b)
  (exists f (and (injective-funp f) (equal (domain f) a) (subset (image f) b))))
(defun-sk eqnum-to-nat (s) (exists n (and (natp n) (exists-bijection n s))))

(defthmz eqnum-reflexive (exists-bijection s s))
(defthmz eqnum-symmetric (implies (exists-bijection a b) (exists-bijection b a))
  :props (zfc prod2$prop domain$prop inverse$prop))
(defthmz eqnum-transitive
  (implies (and (exists-bijection a b) (exists-bijection b c)) (exists-bijection a c))
  :props (zfc prod2$prop domain$prop inverse$prop compose$prop))
(defthmz injects-both-ways-implies-eqnum
  (implies (and (injects-into a b) (injects-into b a)) (exists-bijection a b))
  :props (sbt-prop))
(defthmz set-injects-into-powerset (injects-into s (powerset s)))
(defthmz powerset-does-not-inject (not (injects-into (powerset s) s))
  :props (zfc prod2$prop domain$prop inverse$prop))
(defthmz pigeonhole (implies (natp n) (not (injects-into (+ 1 n) n)))
  :props (zfc prod2$prop domain$prop inverse$prop))
(defthmz eqnum-naturals-equal
  (implies (and (natp m) (natp n) (exists-bijection m n)) (equal m n))
  :rule-classes nil :props (zfc prod2$prop domain$prop inverse$prop))
(defthmz omega-not-finite (not (finite (omega))))
(defthmz finite-iff-eqnum-to-nat (iff (finite s) (eqnum-to-nat s))
  :props (zfc prod2$prop domain$prop inverse$prop))
```
**Difficulty:** (a)–(c) easy to moderate, with (c) as the "no injection" strengthening of `cantor`;
(d)–(g) moderate, by induction on naturals; (h) very hard. **Later master version:** none in the
repository. The doc mentions unpublished "some progress by Matt Kaufmann", so this item has the highest
leakage risk if he publishes. Re-check before grading.

### T5. Transfinite recursion on ordinals

**Statement.** Let G be an arbitrary unary operation on sets (a constrained ACL2 function `tr-g`).
For an ordinal α, call f a *G-recursion on α* if f is a function with domain α and, for every β∈α,
f(β) = G(f↾β), where f↾β is the restriction of f to β. Prove that for every ordinal α
(a) any two G-recursions on α are equal, and
(b) a G-recursion on α exists.
(Optional extension: a macro that instantiates (a)–(b) for a concrete G by functional instantiation, the
same way `prove-inductive-suffices` does for ∈-induction.)

**Base names used:** `ordinal-p`, `funp`, `domain`, `apply`, `restrict`, `prove-inductive-suffices`/`in-pred-holds-when-inductive`, `ordinal-trichotomy`, `zfn`, `union`.

```lisp
(defstub tr-g (x) t)
(defun-sk tr-step-ok (f)
  (forall b (implies (in b (domain f)) (equal (apply f b) (tr-g (restrict f b))))))
(defun tr-fn-p (f a) (and (funp f) (equal (domain f) a) (tr-step-ok f)))
(defun-sk tr-exists (a) (exists f (tr-fn-p f a)))

(defthmz tr-unique
  (implies (and (ordinal-p a) (tr-fn-p f1 a) (tr-fn-p f2 a)) (equal f1 f2))
  :rule-classes nil :props (zfc domain$prop restrict$prop diff$prop))
(defthmz tr-existence
  (implies (ordinal-p a) (tr-exists a))
  :props (zfc domain$prop restrict$prop diff$prop))
```
`zsub`/`zfn` instances whose body mentions the stub `tr-g` are legitimate. The base does exactly
this with the stub `in-pred` in `induction.lisp`. **Difficulty:** hard. Part (b) needs ordinal
facts that are not all in the base (elements of ordinals are ordinals, unions of chains of
ordinals), compatibility of approximations, Replacement over α, and ∈-induction.
**Later master version:** none in the repository ("some progress by Matt Kaufmann", unpublished).
Leakage risk as for T4.

### T6. Infinite Ramsey theorem (pairs)

**Statement.** Let c be a function defined on ω×ω whose values lie in r = {0,…,r−1} for some natural r.
Then there is an infinite H ⊆ ω and a colour k such that c(m,n) = k for all m,n∈H with m<n.
Prove this first for r = 2, then for every natural r.

**Base names used:** `(omega)`, `prod2`, `funp`, `domain`, `image`, `apply`, `finite`, `natp`, `subset`.

```lisp
(defun-sk homogeneous (h c k)
  (forall (m n) (implies (and (in m h) (in n h) (< m n)) (equal (apply c (cons m n)) k))))
(defun-sk exists-infinite-homogeneous (c)
  (exists (h k) (and (subset h (omega)) (not (finite h)) (homogeneous h c k))))

(defthmz infinite-ramsey-2
  (implies (and (funp c) (equal (domain c) (prod2 (omega) (omega))) (subset (image c) 2))
           (exists-infinite-homogeneous c))
  :props (zfc prod2$prop domain$prop inverse$prop))
(defthmz infinite-ramsey
  (implies (and (natp r) (funp c) (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) r))
           (exists-infinite-homogeneous c))
  :props (zfc prod2$prop domain$prop inverse$prop))
```
**Difficulty:** hard. The proof needs "ω is not finite" (T4 f) and the infinite pigeonhole principle
for subsets of ω, and a recursive construction (ACL2 recursion on naturals over `zsub`-defined sets
is allowed). **Later master version:** none.

### T7. Topology: continuity, compactness and the Hausdorff property

The base has topologies (`tpp`), closed sets, compactness, subspaces, Hausdorff, regular and normal
spaces, and three theorems (compact Hausdorff ⇒ regular, compact regular ⇒ normal, closed subspace of
a compact space is compact). It has no continuous maps, no images of compact spaces, and nothing on
compact subsets of Hausdorff spaces.

**Statement.** For topologies T₁, T₂ (with spaces X₁ = ⋃T₁, X₂ = ⋃T₂), f is *continuous* from T₁ to T₂ if f
is a function with domain X₁, image ⊆ X₂, and f⁻¹[V] = {x∈X₁ : f(x)∈V} ∈ T₁ for every V∈T₂. Prove:
(a) the composite of continuous maps is continuous;
(b) if T₁ is compact and f is continuous from T₁ onto X₂, then T₂ is compact;
(c) in a Hausdorff space every singleton {x}, x∈X, is closed;
(d) in a Hausdorff space, every subset S⊆X whose subspace topology is compact is closed.

**Base names used:** `tpp`, `compact`, `hausdorff`, `closed`, `subspace`, `singleton`, `compose`, `funp`, `domain`, `image`, `apply`, `union`.

```lisp
(zsub preimage (f v) x (domain f) (in (apply f x) v))
(defun-sk preimages-open (f tp1 tp2)
  (forall v (implies (in v tp2) (in (preimage f v) tp1))))
(defun continuous (f tp1 tp2)
  (and (funp f) (equal (domain f) (union tp1)) (subset (image f) (union tp2))
       (preimages-open f tp1 tp2)))

(defthmz continuous-compose
  (implies (and (continuous f tp1 tp2) (continuous g tp2 tp3))
           (continuous (compose g f) tp1 tp3))
  :props (zfc prod2$prop domain$prop inverse$prop compose$prop preimage$prop))
(defthmz continuous-image-of-compact
  (implies (and (tpp tp1) (tpp tp2) (compact tp1) (continuous f tp1 tp2)
                (equal (image f) (union tp2)))
           (compact tp2))
  :props (zfc prod2$prop domain$prop inverse$prop preimage$prop))
(defthmz hausdorff-singleton-closed
  (implies (and (tpp tp) (hausdorff tp) (in x (union tp))) (closed (singleton x) tp))
  :props (zfc diff$prop))
(defthmz compact-subset-of-hausdorff-is-closed
  (implies (and (tpp tp) (hausdorff tp) (subset s (union tp)) (compact (subspace s tp)))
           (closed s tp))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop subspace-fn$prop))
```
**Difficulty:** (a) and (c) easy to moderate; (b) moderate, since covers must be pulled back and a finite
subcover pushed forward; (d) hard, comparable to `compact-hausdorff-is-regular`. **Later master
version:** none.

### T8. Groups: uniqueness, subgroups, homomorphisms, kernels

The base has only the definition `groupp` and the integers as an abelian group.

**Statement.** Use the base definition of a group (S, op, e, inv). A *subgroup* of it is H⊆S with e∈H,
closed under op and inv. A *homomorphism* from (S₁,op₁) to (S₂,op₂) is a function f with domain S₁,
image ⊆ S₂ and f(x·y) = f(x)·f(y). Its *kernel* is {x∈S₁ : f(x) = e₂}. A subset H is *normal* if gxg⁻¹∈H for
all g∈S, x∈H. Prove:
(a) the identity is unique, and so are inverses (xy = e ⇒ y = x⁻¹);
(b) a subgroup, with op and inv restricted to it, is a group;
(c) the intersection of a nonempty set of subgroups is a subgroup;
(d) for groups G₁, G₂ and a homomorphism f: f(e₁) = e₂ and f(x⁻¹) = f(x)⁻¹;
the kernel is a normal subgroup of G₁; the image is a subgroup of G₂;
f is injective iff its kernel is {e₁}.

**Base names used:** `groupp`, `group-identity-p`, `apply2`, `apply`, `restrict`, `prod2`, `intersection`, `image`, `injective-funp`, `singleton`.

```lisp
(defun-sk closed-under-op (h op)
  (forall (x y) (implies (and (in x h) (in y h)) (in (apply2 op x y) h))))
(defun-sk closed-under-inv (h inv) (forall x (implies (in x h) (in (apply inv x) h))))
(defun subgroup-p (h s op e inv)
  (and (subset h s) (in e h) (closed-under-op h op) (closed-under-inv h inv)))
(defun-sk all-subgroups (hs s op e inv)
  (forall h (implies (in h hs) (subgroup-p h s op e inv))))
(defun-sk preserves-op (f s1 op1 op2)
  (forall (x y) (implies (and (in x s1) (in y s1))
                         (equal (apply f (apply2 op1 x y))
                                (apply2 op2 (apply f x) (apply f y))))))
(defun group-hom-p (f s1 op1 s2 op2)
  (and (funp f) (equal (domain f) s1) (subset (image f) s2) (preserves-op f s1 op1 op2)))
(zsub kernel (f s1 e2) x s1 (equal (apply f x) e2))
(defun-sk normal-in (h s op inv)
  (forall (g x) (implies (and (in g s) (in x h))
                         (in (apply2 op (apply2 op g x) (apply inv g)) h))))

(defthmz group-identity-unique
  (implies (and (groupp s op e inv) (in e2 s) (group-identity-p s op e2)) (equal e2 e))
  :rule-classes nil :props (zfc prod2$prop domain$prop inverse$prop))
(defthmz group-inverse-unique
  (implies (and (groupp s op e inv) (in x s) (in y s) (equal (apply2 op x y) e))
           (equal y (apply inv x)))
  :rule-classes nil :props (zfc prod2$prop domain$prop inverse$prop))
(defthmz subgroup-is-group
  (implies (and (groupp s op e inv) (subgroup-p h s op e inv))
           (groupp h (restrict op (prod2 h h)) e (restrict inv h)))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))
(defthmz intersection-of-subgroups
  (implies (and (groupp s op e inv) (not (equal hs 0)) (all-subgroups hs s op e inv))
           (subgroup-p (intersection hs) s op e inv))
  :props (zfc prod2$prop domain$prop inverse$prop intersection$prop))
(defthmz hom-preserves-identity-and-inverse
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2) (group-hom-p f s1 op1 s2 op2))
           (and (equal (apply f e1) e2)
                (implies (in x s1) (equal (apply f (apply inv1 x)) (apply inv2 (apply f x))))))
  :props (zfc prod2$prop domain$prop inverse$prop))
(defthmz kernel-is-normal-subgroup
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2) (group-hom-p f s1 op1 s2 op2))
           (and (subgroup-p (kernel f s1 e2) s1 op1 e1 inv1)
                (normal-in (kernel f s1 e2) s1 op1 inv1)))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))
(defthmz image-is-subgroup
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2) (group-hom-p f s1 op1 s2 op2))
           (subgroup-p (image f) s2 op2 e2 inv2))
  :props (zfc prod2$prop domain$prop inverse$prop))
(defthmz injective-iff-trivial-kernel
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2) (group-hom-p f s1 op1 s2 op2))
           (iff (injective-funp f) (equal (kernel f s1 e2) (singleton e1))))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))
```
**Difficulty:** easy to moderate. Most of the work is set-level bookkeeping with `restrict` and `image`.
**Later master version:** none. (The list also points at Russinoff's `books/projects/groups` and
`fields`. Those are ordinary ACL2 developments, not set theory, so they are not a leak of these
statements, but they could be mined for ideas.)

### T9. Fields; the complex numbers as ordered pairs

The base reals (`reals/`) have no multiplication, so "ℂ as pairs of reals" cannot be stated today without
first building real multiplication. The tractable version is the general pair construction over any
field in which −1 is not a square, plus the rationals as an instance.
"Algebraically closed" (the fundamental theorem of algebra) is dropped.

**Statement.** A *field* (S, +, ·, 0, 1, −, ⁻¹) is: (S,+,0,−) an abelian group; 0≠1; · a binary operation on S;
(S∖{0}, · restricted, 1, ⁻¹) an abelian group; and · distributes over +. Suppose −1 is not a square in S. On S×S
define (a,b)+(c,d) = (a+c, b+d), (a,b)·(c,d) = (ac−bd, ad+bc), −(a,b) = (−a,−b), and, for (a,b)≠(0,0),
(a,b)⁻¹ = (a·n⁻¹, (−b)·n⁻¹) with n = a²+b². Prove:
(a) (S×S, +, ·, (0,0), (1,0), −, ⁻¹) is a field;
(b) (0,1)·(0,1) = −(1,0);
(c) the rationals form a field whose + and · are ordinary rational addition and multiplication and in which −1 is not a square.
(Stretch: define multiplication of Dedekind reals and prove that the reals form a field satisfying the
hypothesis, giving ℂ = ℝ×ℝ.)

**Base names used:** `abelian-group-p`, `groupp`, `apply2`, `apply`, `restrict`, `prod2`, `diff`, `singleton`, `(rationals)` (reals/dedekind), `zsub`.

```lisp
(defun-sk distributive-p (s add mul)
  (forall (x y z) (implies (and (in x s) (in y s) (in z s))
                           (equal (apply2 mul x (apply2 add y z))
                                  (apply2 add (apply2 mul x y) (apply2 mul x z))))))
(defun nonzeros (s zero) (diff s (singleton zero)))
(defun fieldp (s add mul zero one neg recip)
  (and (abelian-group-p s add zero neg)
       (not (equal zero one))
       (equal (domain mul) (prod2 s s))
       (subset (image mul) s)
       (abelian-group-p (nonzeros s zero)
                        (restrict mul (prod2 (nonzeros s zero) (nonzeros s zero)))
                        one recip)
       (distributive-p s add mul)))
(defun-sk minus-one-not-square (s mul neg one)
  (forall x (implies (in x s) (not (equal (apply2 mul x x) (apply neg one))))))
(defun cx-a (p) (car (car (car p))))   ; p = (((a . b) . (c . d)) . result)
(defun cx-b (p) (cdr (car (car p))))
(defun cx-c (p) (car (cdr (car p))))
(defun cx-d (p) (cdr (cdr (car p))))
(zsub c-add (s add) p (prod2 (prod2 (prod2 s s) (prod2 s s)) (prod2 s s))
      (equal (cdr p) (cons (apply2 add (cx-a p) (cx-c p)) (apply2 add (cx-b p) (cx-d p)))))
(zsub c-mul (s add mul neg) p (prod2 (prod2 (prod2 s s) (prod2 s s)) (prod2 s s))
      (equal (cdr p)
             (cons (apply2 add (apply2 mul (cx-a p) (cx-c p))
                           (apply neg (apply2 mul (cx-b p) (cx-d p))))
                   (apply2 add (apply2 mul (cx-a p) (cx-d p)) (apply2 mul (cx-b p) (cx-c p))))))
(zsub c-neg (s neg) p (prod2 (prod2 s s) (prod2 s s))
      (equal (cdr p) (cons (apply neg (car (car p))) (apply neg (cdr (car p))))))
(defun c-norm2 (u add mul)
  (apply2 add (apply2 mul (car u) (car u)) (apply2 mul (cdr u) (cdr u))))
(zsub c-recip (s add mul zero neg recip) p
      (prod2 (diff (prod2 s s) (singleton (cons zero zero))) (prod2 s s))
      (equal (cdr p)
             (cons (apply2 mul (car (car p)) (apply recip (c-norm2 (car p) add mul)))
                   (apply2 mul (apply neg (cdr (car p))) (apply recip (c-norm2 (car p) add mul))))))
(defun-sk rational-ops-standard (add mul)
  (forall (x y) (implies (and (rationalp x) (rationalp y))
                         (and (equal (apply2 add x y) (+ x y)) (equal (apply2 mul x y) (* x y))))))
(defun-sk rationals-field-witness ()
  (exists (add mul neg recip)
    (and (fieldp (rationals) add mul 0 1 neg recip)
         (minus-one-not-square (rationals) mul neg 1)
         (rational-ops-standard add mul))))

(defthmz complex-construction-is-field
  (implies (and (fieldp s add mul zero one neg recip) (minus-one-not-square s mul neg one))
           (fieldp (prod2 s s) (c-add s add) (c-mul s add mul neg) (cons zero zero) (cons one zero)
                   (c-neg s neg) (c-recip s add mul zero neg recip)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop restrict$prop
              c-add$prop c-mul$prop c-neg$prop c-recip$prop))
(defthmz complex-i-squared
  (implies (fieldp s add mul zero one neg recip)
           (equal (apply2 (c-mul s add mul neg) (cons zero one) (cons zero one))
                  (apply (c-neg s neg) (cons one zero))))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop restrict$prop c-mul$prop c-neg$prop))
(defthmz rationals-form-field (rationals-field-witness)
  :props (zfc rationals$prop v$prop prod2$prop domain$prop inverse$prop))
```
**Difficulty:** hard, mostly because of volume: about 10 field axioms over pairs, with equational
reasoning carried out abstractly through `apply2`. (b) is easy and (c) is moderate (use `zify`).
The Dedekind-reals stretch is very hard. **Later master version:** none.

### T10. Metric spaces with Dedekind-real distances

**Statement.** A *metric* on X is a function d with domain X×X whose values are Dedekind reals (`drp`),
such that for a,b,c∈X: 0 ≤ d(a,b) (as cuts: r2dr(0) ⊆ d(a,b)); d(a,b) = 0 iff a = b; d(a,b) = d(b,a);
d(a,c) ≤ d(a,b)+d(b,c) (cut inclusion into `dr+`). A subset U⊆X is *open* if for each a∈U there is a
rational ε>0 such that every b∈X with d(a,b) ≤ ε (i.e. ε∉d(a,b)) lies in U. Prove:
(a) the open sets form a topology whose underlying space is X;
(b) that topology is Hausdorff;
(c) d(p,q) = |p−q| (as the cut `r2dr`) is a metric on the rationals.

**Base names used:** `drp`, `r2dr`, `dr+`, `dr-sum-prop`, `(rationals)`, `tpp`, `hausdorff`, `prod2`, `powerset`, `zsub`.

```lisp
(defun-sk dr-valued (d x)
  (forall (a b) (implies (and (in a x) (in b x)) (drp (apply d (cons a b))))))
(defun-sk metric-axioms (d x)
  (forall (a b c)
    (implies (and (in a x) (in b x) (in c x))
             (and (subset (r2dr 0) (apply d (cons a b)))
                  (iff (equal (apply d (cons a b)) (r2dr 0)) (equal a b))
                  (equal (apply d (cons a b)) (apply d (cons b a)))
                  (subset (apply d (cons a c))
                          (dr+ (apply d (cons a b)) (apply d (cons b c))))))))
(defun metric-p (d x)
  (and (funp d) (equal (domain d) (prod2 x x)) (dr-valued d x) (metric-axioms d x)))
(defun-sk ball-inside (u a eps d x)
  (forall b (implies (and (in b x) (not (in eps (apply d (cons a b))))) (in b u))))
(defun-sk has-ball (u a d x)
  (exists eps (and (rationalp eps) (< 0 eps) (ball-inside u a eps d x))))
(defun-sk metric-open-p (u d x) (forall a (implies (in a u) (has-ball u a d x))))
(zsub metric-topology (d x) u (powerset x) (metric-open-p u d x))
(zsub q-dist () p (prod2 (prod2 (rationals) (rationals)) (powerset (rationals)))
      (equal (cdr p) (r2dr (abs (- (car (car p)) (cdr (car p)))))))

(defthmz metric-topology-is-topology
  (implies (metric-p d x)
           (and (tpp (metric-topology d x)) (equal (union (metric-topology d x)) x)))
  :props (zfc prod2$prop diff$prop metric-topology$prop))
(defthmz metric-topology-is-hausdorff
  (implies (metric-p d x) (hausdorff (metric-topology d x)))
  :props (dr-sum-prop diff$prop metric-topology$prop))
(defthmz rationals-metric (metric-p (q-dist) (rationals))
  :props (dr-sum-prop q-dist$prop))
```
**Difficulty:** (a) moderate (it does not need the triangle inequality); (b) hard, because it needs
facts about cuts and `dr+` that are not in the base; (c) moderate to hard. **Later master version:** none.

### T11. Reduced products and ultraproducts (builds on T1–T3)

**Statement.** For a family F with index set I and a filter U on I, define f ~_U g on ΠF iff
{i∈I : f(i) = g(i)} ∈ U. The *reduced product* (an ultraproduct when U is an ultrafilter) is ΠF/~_U. Prove:
(a) ~_U is an equivalence relation on ΠF;
(b) if every F(i) is nonempty and U is the principal ultrafilter at i₀∈I, then the ultraproduct is
equinumerous with F(i₀).

```lisp
;; uses the T1, T2, T3 definitions
(zsub agree-set (f g i) x i (equal (apply f x) (apply g x)))
(zsub ultra-rel (fam u) q (prod2 (prod-family fam) (prod-family fam))
      (in (agree-set (car q) (cdr q) (domain fam)) u))
(defun ultraproduct (fam u) (quotient (ultra-rel fam u) (prod-family fam)))
(defthmz reduced-product-relation-is-equivalence
  (implies (and (funp fam) (filter-on u (domain fam)))
           (equivalence-on (ultra-rel fam u) (prod-family fam)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop))
(defthmz principal-ultraproduct
  (implies (and (funp fam) (nonempty-values fam) (in i0 (domain fam)))
           (exists-bijection (ultraproduct fam (principal-filter i0 (domain fam))) (apply fam i0)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop prod-family$prop
              agree-set$prop ultra-rel$prop principal-filter$prop eqv-class$prop quotient$prop))
```
**Difficulty:** (a) moderate; (b) moderate to hard. Łoś's theorem needs first-order logic and is dropped.
**Later master version:** none.

### T12. Better `defthme` automation (assessed; not recommended as a graded task)

The item "improve (and possibly rename) defthme … to provide more help with reasoning involving
quantifiers" is tool engineering with no single theorem as its target. It can only be made checkable
as a benchmark: give a fixed list of set equalities and quantifier lemmas from the base, delete their
`:hints`, and require a new macro to prove N of them with no hints and no `skip-proofs`/`try-cmd`
fallback. That depends on the chosen corpus and is easy to game. Possible later; not recommended now.

---

## 2. Dropped items

| item from `zfc-future-work` | why dropped |
|---|---|
| Ordinal and cardinal arithmetic | Needs transfinite recursion (T5) first; a follow-on to T5. |
| Closed unbounded and stationary subsets of ω₁ | Needs ω₁ (Hartogs or well-ordering) and recursion; long. |
| Mostowski collapse lemma | Needs well-founded recursion on classes; hard. |
| Independence results | Needs forcing or inner models; research-scale. |
| Large cardinals | Research-scale; statements not checkable in a useful way. |
| Reflection theorem or macro | Metatheorem or macro; research-scale. |
| First-order logic soundness/completeness; model theory; Łoś | Large new syntax and semantics development. |
| HOL→ACL2(zfc) translation; HOL soundness | Research and engineering; overlaps `hol-in-acl2`. |
| Temporal logics over infinite paths | Too open-ended to state as a checkable theorem. |
| Polynomial rings over the reals; calculus/analysis | Needs real multiplication, order and completeness, none of which exist yet. |
| ℂ algebraically closed (FTA) | Needs analysis over ℝ; very hard. |

---

## 3. Summary

| # | item | main base names used | later master version? | difficulty | recommend |
|---|---|---|---|---|---|
| T1 | Equivalence relations, quotients, partitions | `prod2 zsub powerset union int2 funp domain image apply` | none | moderate | **yes** |
| T2 | Indexed Cartesian product + AC form | `fun-space prod2 pair domain image union apply min-in exists-bijection` | none (binary `prod2` already in base) | moderate | **yes** |
| T3 | Filters/ultrafilters (a–d); non-principal existence (e) | `powerset int2 diff union2 finite omega` | none | (a–d) easy-mod; (e) very hard | **yes** (a–d); (e) stretch |
| T4 | Cardinality basics (≈, ≼, CSB, strict Cantor, pigeonhole, ω infinite, finite⇔≈n) | `exists-bijection injective-funp schroeder-bernstein cantor finite omega identity-fun compose` | none in repo (unpublished "progress" noted) | easy-mod; (h) very hard | **yes** (a–g) |
| T5 | Transfinite recursion (uniqueness + existence) | `ordinal-p restrict funp domain apply prove-inductive-suffices zfn` | none in repo (unpublished "progress" noted) | hard | **yes** (flagship) |
| T6 | Infinite Ramsey (pairs, 2 and r colours) | `omega prod2 funp domain image finite` | none | hard | **yes** (after T4 f) |
| T7 | Topology: continuity, compact images, Hausdorff closedness | `tpp compact hausdorff closed subspace compose singleton` | none | (a,c) easy-mod; (b) mod; (d) hard | **yes** |
| T8 | Groups: uniqueness, subgroups, homs, kernel, image | `groupp group-identity-p apply2 restrict intersection image injective-funp` | none | easy-mod | **yes** (warm-up) |
| T9 | Fields; ℂ-style pair construction; ℚ is a field | `abelian-group-p apply2 restrict prod2 diff rationals zsub` | none | hard (volume) | yes (ℝ×ℝ version stretch) |
| T10 | Metric spaces over Dedekind reals | `drp r2dr dr+ rationals tpp hausdorff zsub` | none | mod–hard | yes |
| T11 | Reduced products / ultraproducts | T1–T3 definitions, `exists-bijection` | none | mod–hard | optional |
| T12 | `defthme` automation | `utilities/defthme.lisp` | none | n/a | **no** (not cleanly checkable) |

Base: **65589c5afd** (2026-07-05). The list did not exist at 6211b25fd4. Master 1d2b39a424 has the
same mathematical content, apart from the cosmetic `force?`→`force` change. Build: ordinary non-ACL2(r)
`saved_acl2` plus `cert.pl`. No defaxiom or ttags. The harness must accept `(zfc)`/`$prop` hypothesis
functions with open `:props`, and must stop `defthme`'s silent `skip-proofs` fallback.
