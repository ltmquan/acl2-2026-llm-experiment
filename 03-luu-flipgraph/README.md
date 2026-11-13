# 03 — Flip graph

**Paper:** Quan Luu, Zeke Medley, Panagiotis Manolios, *Formalizing the Connectivity Theorem for the Matrix Multiplication Flip Graph in ACL2* (ACL2 Workshop 2026). PDF in `source/paper.pdf`.
**Logic:** ACL2.

## The paper

Over F2, a matrix multiplication scheme is a multiset of nonzero rank-one tensors A⊗B⊗C that sum
to the matrix multiplication tensor M(n). Flip and plus moves rewrite two summands without changing the sum.
The paper formalizes the proof (Medley et al., arXiv:2609.17533) that for n ≥ 2 the flip graph with flip and
plus edges is strongly connected. The proof is constructive: `main-path` computes a path between any two
correct schemes. A side development connects schemes to bilinear algorithms (soundness, completeness, round
trip).

**Contribution.** A theorem: a recent (2026) combinatorial and linear-algebra result. The paper reports 29
books, 215 definitions and 791 theorems; the connectivity proof alone is 19 books with 137 functions and 527
theorems.

**Authors' ACL2 books.** Pull request [acl2/acl2#2103](https://github.com/acl2/acl2/pull/2103) (opened 2026-11-06,
not merged when we ran the experiments), directory `books/workshops/2026/luu-medley-manolios/`. A copy is in
`source/authors-books/`. All books certify on ACL2 8.7.

## Files

```
03-luu-flipgraph/
  README.md
  source/
    paper.pdf
    authors-books/        the authors' ACL2 books (copy)
  exp1/
    prompt.txt            the exact prompt sent to the model
    solution.lisp         the model's final /work/solution.lisp
    audit.txt             transcript audit (tools/audit.py)
    review.md             short factual review of the run
  exp2/
    prompt.txt            the exact prompt sent to the model
    definitions.lisp      the definitions, annotated with their source locations (comments only)
    targets.lisp          the target theorems (the authors' names in comments)
    checker/              the exact files the checker certifies against (hashes below)
    model-facing/         the definitions file the model was given (see below)
    extraction/           how definitions.lisp was built and verified (NOTES.md, scripts, logs)
    solution.lisp         the model's final /work/solution.lisp
    audit.txt
    review.md
```

## Results

| | Experiment 1 (English → ACL2) | Experiment 2 (ACL2 statements) |
|---|---|---|
| Result | proved (certified) | all 4 target(s) proved (certified, statements matched) |
| Model time | 50 min | 58 min |
| Tool calls | 177 | 166 |
| Certification time of solution.lisp (ACL2 8.7) | 26.7 s | 56.1 s |
| Audit | CLEAN | CLEAN |
| solution.lisp: lines / definitions / theorems | 1750 / 98 / 255 | 3420 / 91 / 455 |

Authors' development (for scale): 66 files (including `experiments/`), 27,404 lines, 753 definitions, 1,963 theorems.

*Model time* runs from when the model received the prompt to the end of its run (setup not included).
Certification time is for `solution.lisp` alone, with its dependencies already certified, on our build
(experiment 2: against `exp2/checker/`). Sizes are counted with `tools/sizes.py` (definitions = `defun`,
`define`, `defun-sk`, `defmacro`, … and encapsulated functions; theorems = `defthm`, `defrule`, …, local
ones included). Both experiments: first attempt, Claude Opus 5.5 at medium effort.

## Experiment 1: English definitions and theorem

**Theorem given:** Theorem 5.1 (flip-plus connectivity): over F2, for n ≥ 2, the flip graph with flip and plus edges is strongly connected.

### Statement rewrites (paper text → prompt)

The definitions and theorem were copied from the paper as close to verbatim as possible. Every edit:

#### Sources
- Theorem: §5, Theorem 5.1, p. 8 (verbatim, both sentences; label "(Flip-plus connectivity [12])" dropped).
- Notation + F2 convention: §2 opening paragraph, p. 2.
- Rank-one tensor: Definition 2.1, p. 2.
- M(n): Definition 2.2 (eq. (1)) and the sentence after it, p. 2.
- Scheme: Definition 2.3, p. 3 (schemes are **multisets** of nonzero rank-one tensors).
- Flip/plus: Definition 2.5 and the closing sentence "These transformations on the B and C positions are defined analogously.", p. 3.

#### Edits
1. "Our definitions are over F2, consistent with the proof. The definitions extend to any field, but the connectivity proof does not: it deletes identical pairs of summands, which relies on 1 + 1 = 0." → "The definitions are over F2." Reason: remove "we"/"our"; the cut text is a proof hint.
2. Dropped "We also only consider square matrices, but our definitions can be extended to rectangular ones." (authorial voice; n × n is explicit everywhere).
3. Removed numbering/citations from definition labels: "Definition 2.1 (Rank-one tensor)." → "Definition (Rank-one tensor)."; same for 2.2 "[12]", 2.3 "[12]", 2.5 "[12]". Dropped equation number "(1)".
4. Dropped "The matrix multiplication tensor is defined as follows." (connective).
5. Kept "We call such a multiset a scheme" and "we define the matrix multiplication tensor" — definitional "we", not authorial reference; reviewer may change to "Such a multiset is called a scheme."
6. Omitted all intervening text: rank-R decomposition (eq. 2) and the algorithm discussion, unit matrices E_ij, Strassen example (Ex. 2.4), §2.3, and the paragraph after Def 2.5 ("Both transformations preserve the sum ... again a decomposition of M(n)") — the latter is an intermediate fact/lemma.
7. Math notation transcribed to plain Unicode: F2^(n×n), subscripts as _{…}, M(n) for script-M superscript (n), A^(r) for A^{(r)}.
8. Theorem: label removed only.

### Prompt

<details>
<summary>Experiment 1 prompt (also in exp1/prompt.txt)</summary>

```text
Formalize the definitions and the theorem below in ACL2, and prove the theorem.

<definitions>
Throughout, ⊎ is multiset union, ∪ set union, and \ both multiset and set difference. The definitions are over F2.

Definition (Rank-one tensor). Rank-one tensors are non-zero tensors that can be written as A ⊗ B ⊗ C for some matrices A, B, C ∈ F2^(n×n).

Definition (Matrix Multiplication Tensor). For n ∈ N, we define the matrix multiplication tensor M(n) ∈ F2^(n×n) ⊗ F2^(n×n) ⊗ F2^(n×n) such that for all n × n matrices D, F ∈ F2^(n×n) and all k, ℓ,

    (DF)_{k,ℓ} = Σ_{g,h,i,j=1}^{n} M(n)_{g,h,i,j,k,ℓ} D_{g,h} F_{i,j}.

Equivalently, M(n) records which products of entries of D and F contribute to each entry of DF.

Definition (Schemes and vertices). The vertices of the matrix multiplication flip graph for n × n matrix multiplication are multisets

    S = { A^(1) ⊗ B^(1) ⊗ C^(1), …, A^(|S|) ⊗ B^(|S|) ⊗ C^(|S|) }

of nonzero rank-one tensors satisfying

    Σ_{s∈S} s = M(n).

We call such a multiset a scheme. The size |S| is the rank of the scheme.

Definition (Flip and plus transformations). Let S be a scheme. If S can be transformed into S′ by one of the following operations, then there is a directed edge from S to S′.

Flip. Flip on the A position applies to two summands A ⊗ B ⊗ C, A′ ⊗ B′ ⊗ C′ with A = A′ and replaces them by A ⊗ B ⊗ (C + C′), A′ ⊗ (B′ − B) ⊗ C′. Equivalently,

    S′ = S \ {A ⊗ B ⊗ C, A′ ⊗ B′ ⊗ C′} ⊎ {A ⊗ B ⊗ (C + C′), A′ ⊗ (B′ − B) ⊗ C′},

with any zero summands deleted.

Plus. Plus on the A position takes two summands A ⊗ B ⊗ C, A′ ⊗ B′ ⊗ C′, and replaces the second summand by two summands: (A′ − A) ⊗ B′ ⊗ C′, and A ⊗ B′ ⊗ C′. Equivalently,

    S′ = S \ {A′ ⊗ B′ ⊗ C′} ⊎ {(A′ − A) ⊗ B′ ⊗ C′, A ⊗ B′ ⊗ C′},

with any zero summands deleted.

These transformations on the B and C positions are defined analogously.
</definitions>

<theorem>
Over F2, for every n ≥ 2, the directed matrix multiplication flip graph whose edges are ordinary flip and plus transformations is strongly connected. Equivalently, for any two schemes S and S′ for M(n), there is a directed path from S to S′ using only flip and plus transformations.
</theorem>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
Put your work in /work/solution.lisp; it must certify with `cert.pl` (add `--acl2 acl2r` for ACL2(r)), and its last
event must be the theorem, named MAIN.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done. When you are done, print the final contents of /work/solution.lisp.
```

</details>

## Experiment 2: the authors' ACL2 definitions and statements

### Targets

| Target | Authors' theorem | Meaning |
|---|---|---|
| MAIN-1 | `flip-plus-connectivity` (main.lisp:148), in existential form | for n ≥ 2, every correct n×n scheme over F2 reaches every other one by valid flip/plus moves |
| MAIN-2 | `algo-to-correct-scheme` (algo-completeness.lisp:41) | completeness: a correct bilinear algorithm translates to a correct scheme |
| MAIN-3 | `scheme-algo-correct` (scheme-algo.lisp:470) | soundness: the algorithm built from a correct scheme is correct |
| MAIN-4 | `algo-scheme-of-scheme-algo` (scheme-algo.lisp:451) | round trip: scheme → algorithm → scheme is the identity |

### How the definitions were extracted

`definitions.lisp` holds 89 of the authors' definitions (`define`s and one `defun-sk`), the
definitional closure of the four statements, computed in ACL2 from bodies, guards and measures. Each `define`
is verbatim except that its `///` section (theorems) is removed; `:returns` theorems stay, as part of the
definition form. It leaves out `main-path` and every path construction. Local lemmas, needed only for guard
verification, are the authors' lemmas copied verbatim, plus a few of our own; a greedy minimization showed
that each one is needed. The one non-author definition is `flip-plus-reachablep` (below).

The general procedure, and how each package was checked, is in [`../EXPERIMENT-2.md`](../EXPERIMENT-2.md);
the full notes for this paper are in `exp2/extraction/NOTES.md`.

**What the model saw.** The checker's `definitions.lisp` needs local lemmas to admit some definitions. Those
lemmas can contain parts of the proofs, so the model was given `exp2/model-facing/defs.lisp`
instead: local lemmas and hints removed, comments removed, and each definition wrapped in `skip-proofs`, with
`exp2/model-facing/cert.acl2` allowing `skip-proofs` for that one book. The model's own solution could not use
`skip-proofs`, and the checker certifies it against the fully proved `checker/defs.lisp`. A dump of every
name each version introduces (formals, body, guard, measure, constraints, macro bodies) was identical for the
two versions (`tools/world-dump.lsp`).

Checker files:

| File | SHA-256 |
|---|---|
| `exp2/checker/defs.lisp` | `b8c4e6067eb732a37edf0ffe2a11b6e940fd59a5dca96ee842b23511ef23647b` |

`exp2/definitions.lisp` differs from `exp2/checker/defs.lisp` only in comments
(`tools/check-comments-only.py`).

### Statement rewrites (authors' ACL2 → targets)

- **MAIN-1 is existential.** The authors' theorem states that the constructive `main-path` is a valid path.
  Giving that statement would hand over both the formalization and the proof, so MAIN-1 instead says that a
  valid path exists, using a new `defun-sk flip-plus-reachablep` (in `definitions.lisp`, marked as not from the
  authors). The hypotheses are the original ones: `(correct-schemep sch n) (correct-schemep sch2 n) (natp n)
  (<= 2 n)`. We proved MAIN-1 from the authors' theorem by instantiating the witness with `main-path`.
- **MAIN-3 and MAIN-4 are separate targets**, not one conjunction, because their hypotheses differ:
  `scheme-algo-correct` assumes `correct-schemep`, `algo-scheme-of-scheme-algo` only `schemep`.
- Otherwise verbatim: `defrule` written as `defthm`, hints dropped.

### Prompt

<details>
<summary>Experiment 2 prompt (also in exp2/prompt.txt)</summary>

```text
Prove the theorems below in ACL2.

1. Create /work/defs.lisp, /work/cert.acl2, each containing exactly the text between its tags. defs.lisp holds the definitions the theorems use. Do not modify these files. Some definitions in defs.lisp are admitted with skip-proofs: their admissibility has been checked separately, and cert.acl2 permits skip-proofs so that books including defs.lisp can be certified. Your own files must not use skip-proofs: your solution will be checked against fully proved definitions without that permission.

<defs.lisp>
(in-package "ACL2")

(include-book "kestrel/bv/bitxor" :dir :system)

(include-book "kestrel/bv/bitand" :dir :system)

(include-book "std/util/define" :dir :system)

(include-book "std/util/defrule" :dir :system)

(include-book "std/lists/repeat" :dir :system)

(include-book "std/basic/inductions" :dir :system)

(include-book "std/obags/top" :dir :system)

(local (include-book "std/lists/append" :dir :system))

(local (include-book "std/lists/nth" :dir :system))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(skip-proofs
(define bit-list-p (x)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (bitp (car x))
         (bit-list-p (cdr x))))))

(skip-proofs
(define bit-listnp (x (n natp))
  :returns (yes/no booleanp)
  (if (zp n)
      (null x)
    (and (consp x)
         (bitp (car x))
         (bit-listnp (cdr x) (1- n))))))

(skip-proofs
(define bit-listn0 ((n natp))
  :returns (r bit-list-p
              )
  (repeat n 0)))

(skip-proofs
(define bit-list-add ((x bit-list-p) (y bit-list-p))
  :returns (z bit-list-p)
  (if (and (consp x) (consp y))
      (cons (bitxor (car x) (car y))
            (bit-list-add (cdr x) (cdr y)))
    nil)))

(skip-proofs
(define bit-list-scale ((b bitp) (x bit-list-p))
  :returns (z bit-list-p)
  (if (atom x)
      nil
    (cons (bitand b (car x))
          (bit-list-scale b (cdr x))))))

(skip-proofs
(define bit-list-outer ((u bit-list-p) (v bit-list-p))
  :returns (z bit-list-p)
  (if (atom u)
      nil
    (append (bit-list-scale (car u) v)
            (bit-list-outer (cdr u) v)))))

(skip-proofs
(define bit-list-listp (a)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom a)
      (null a)
    (and (bit-list-p (car a))
         (bit-list-listp (cdr a))))))

(skip-proofs
(define bit-matp (a (m natp) (n natp))
  :returns (yes/no booleanp)
  :measure (nfix m)
  (if (zp m)
      (null a)
    (and (consp a)
         (bit-listnp (car a) n)
         (bit-matp (cdr a) (1- m) n)))))

(skip-proofs
(define bit-mat0 ((m natp) (n natp))
  :returns (a bit-list-listp
              )
  (repeat m (bit-listn0 n))))

(skip-proofs
(define bit-mat-add ((a bit-list-listp) (b bit-list-listp))
  :returns (c bit-list-listp)
  (if (and (consp a) (consp b))
      (cons (bit-list-add (car a) (car b))
            (bit-mat-add (cdr a) (cdr b)))
    nil)))

(skip-proofs
(define mat-flat ((a bit-list-listp))
  :returns (l bit-list-p :hyp (bit-list-listp a))
  (if (atom a)
      nil
    (append (car a) (mat-flat (cdr a))))))

(skip-proofs
(define mat-triplep (s)
  :enabled t
  :returns (yes/no booleanp)
  (and (true-listp s)
       (equal (len s) 3)
       (bit-list-listp (car s))
       (bit-list-listp (cadr s))
       (bit-list-listp (caddr s)))))

(skip-proofs
(define summand ((a bit-list-listp) (b bit-list-listp) (c bit-list-listp))
  :enabled t
  :returns (s mat-triplep :hyp :guard)
  (list a b c)))

(skip-proofs
(define summand-A ((s mat-triplep))
  :enabled t
  :returns (a bit-list-listp :hyp :guard)
  (car s)))

(skip-proofs
(define summand-B ((s mat-triplep))
  :enabled t
  :returns (b bit-list-listp :hyp :guard)
  (cadr s)))

(skip-proofs
(define summand-C ((s mat-triplep))
  :enabled t
  :returns (c bit-list-listp :hyp :guard)
  (caddr s)))

(skip-proofs
(define summand0p ((s mat-triplep) (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (or (equal (summand-A s) (bit-mat0 n n))
      (equal (summand-B s) (bit-mat0 n n))
      (equal (summand-C s) (bit-mat0 n n)))))

(skip-proofs
(define summandp (s (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (and (mat-triplep s)
       (bit-matp (car s) n n)
       (bit-matp (cadr s) n n)
       (bit-matp (caddr s) n n)
       (not (summand0p s n)))))

(skip-proofs
(define summand-dimp (s (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (and (mat-triplep s)
       (bit-matp (car s) n n)
       (bit-matp (cadr s) n n)
       (bit-matp (caddr s) n n))))

(skip-proofs
(define summand-dim-listp (l (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (summand-dimp (car l) n)
         (summand-dim-listp (cdr l) n)))))

(skip-proofs
(define summand-listp (x (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (summandp (car x) n)
         (summand-listp (cdr x) n)))))

(skip-proofs
(define schemep (x (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (and (obag::bagp x)
       (summand-listp x n))))

(skip-proofs
(define pos-next ((p natp))
  :enabled t
  (case p (0 1) (1 2) (t 0))))

(skip-proofs
(define pos-prev ((p natp))
  :enabled t
  (case p (0 2) (1 0) (t 1))))

(skip-proofs
(define summand-get-pos ((s mat-triplep) p)
  :enabled t
  :returns (m bit-list-listp :hyp :guard)
  (case p
    (0 (car s))
    (1 (cadr s))
    (t (caddr s)))))

(skip-proofs
(define summand-set-pos ((s mat-triplep) p (m bit-list-listp))
  :enabled t
  :returns (s1 mat-triplep :hyp :guard)
  (case p
    (0 (summand m (cadr s) (caddr s)))
    (1 (summand (car s) m (caddr s)))
    (t (summand (car s) (cadr s) m)))))

(skip-proofs
(define mat-triple-listp (l)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (mat-triplep (car l))
         (mat-triple-listp (cdr l))))))

(skip-proofs
(define flip ((s1 mat-triplep) (s2 mat-triplep) (p natp))
  :enabled t
  :returns (l mat-triple-listp :hyp :guard)
  (let ((q (pos-next p))
        (r (pos-prev p)))
    (list (summand-set-pos s1 r (bit-mat-add (summand-get-pos s1 r)
                                             (summand-get-pos s2 r)))
          (summand-set-pos s2 q (bit-mat-add (summand-get-pos s2 q)
                                             (summand-get-pos s1 q)))))))

(skip-proofs
(define plus ((target mat-triplep) (pivot mat-triplep) (p natp))
  :enabled t
  :returns (l mat-triple-listp :hyp :guard)
  (list (summand-set-pos target p (bit-mat-add (summand-get-pos target p)
                                               (summand-get-pos pivot p)))
        (summand-set-pos target p (summand-get-pos pivot p)))))

(skip-proofs
(define move-kind ((move true-listp)) :enabled t (car move)))

(skip-proofs
(define move-pos ((move true-listp)) :enabled t (cadr move)))

(skip-proofs
(define move-s1 ((move true-listp)) :enabled t (caddr move)))

(skip-proofs
(define move-s2 ((move true-listp)) :enabled t (cadddr move)))

(skip-proofs
(define move-p (move)
  :enabled t
  :returns (yes/no booleanp)
  (and (true-listp move)
       (equal (len move) 4)
       (or (eq (move-kind move) :flip)
           (eq (move-kind move) :plus))
       (natp (move-pos move))
       (< (move-pos move) 3)
       (mat-triplep (move-s1 move))
       (mat-triplep (move-s2 move)))))

(skip-proofs
(define move-list-p (moves)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom moves)
      (null moves)
    (and (move-p (car moves))
         (move-list-p (cdr moves))))))

(skip-proofs
(define insert-all-nonzero ((l mat-triple-listp) (s obag::bagp) (n natp))
  :enabled t
  :returns (s1 obag::bagp :hyp (obag::bagp s))
  (if (atom l)
      s
    (if (summand0p (car l) n)
        (insert-all-nonzero (cdr l) s n)
      (obag::insert (car l) (insert-all-nonzero (cdr l) s n))))))

(skip-proofs
(define move-validp ((move move-p) (sch obag::bagp))
  :enabled t
  :returns (yes/no booleanp)
  (case (move-kind move)
    (:flip (and (natp (move-pos move))
                (< (move-pos move) 3)
                (if (equal (move-s1 move) (move-s2 move))
                    (<= 2 (obag::occs (move-s1 move) sch))
                  (and (obag::in (move-s1 move) sch)
                       (obag::in (move-s2 move) sch)
                       (equal (summand-get-pos (move-s1 move) (move-pos move))
                              (summand-get-pos (move-s2 move) (move-pos move)))))))
    (:plus (and (natp (move-pos move))
                (< (move-pos move) 3)
                (if (equal (move-s1 move) (move-s2 move))
                    (<= 2 (obag::occs (move-s1 move) sch))
                  (and (obag::in (move-s1 move) sch)
                       (obag::in (move-s2 move) sch)))))
    (t nil))))

(skip-proofs
(define apply-move ((move move-p) (sch obag::bagp) (n natp))
  :returns (sch1 obag::bagp :hyp (obag::bagp sch))
  (case (move-kind move)
    (:plus (insert-all-nonzero (plus (move-s1 move) (move-s2 move) (move-pos move))
                               (obag::delete (move-s1 move) sch)
                               n))
    (:flip (insert-all-nonzero (flip (move-s1 move) (move-s2 move) (move-pos move))
                               (obag::delete (move-s1 move)
                                             (obag::delete (move-s2 move) sch))
                               n))
    (t sch))))

(skip-proofs
(define apply-moves ((moves move-list-p) (sch obag::bagp) (n natp))
  :returns (sch1 obag::bagp :hyp (obag::bagp sch))
  (if (atom moves)
      sch
    (apply-moves (cdr moves) (apply-move (car moves) sch n) n))))

(skip-proofs
(define path-validp ((moves move-list-p) (sch obag::bagp) (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (if (atom moves)
      t
    (and (move-validp (car moves) sch)
         (path-validp (cdr moves) (apply-move (car moves) sch n) n)))))

(skip-proofs
(defun-sk flip-plus-reachablep (sch sch2 n)
  (exists (moves)
          (and (path-validp moves sch n)
               (equal (apply-moves moves sch n) sch2)))))

(skip-proofs
(define tensor ((a bit-list-listp) (b bit-list-listp) (c bit-list-listp))
  :returns (tt bit-list-p :hyp :guard)
  (bit-list-outer (mat-flat a)
                  (bit-list-outer (mat-flat b) (mat-flat c)))))

(skip-proofs
(define summand-tensor ((s mat-triplep))
  :enabled t
  (tensor (car s) (cadr s) (caddr s))))

(skip-proofs
(define scheme-sum ((l mat-triple-listp) (n natp))
  :returns (tt bit-list-p)
  (if (atom l)
      (bit-listn0 (* n n n n n n))
    (bit-list-add (summand-tensor (car l))
                  (scheme-sum (cdr l) n)))))

(skip-proofs
(define bit-unit-list ((j natp) (n natp))
  :returns (l bit-list-p)
  (if (zp n)
      nil
    (if (zp j)
        (cons 1 (bit-listn0 (1- n)))
      (cons 0 (bit-unit-list (1- j) (1- n)))))))

(skip-proofs
(define bit-mat-unit ((i natp) (j natp) (m natp) (n natp))
  :returns (a bit-list-listp)
  (if (zp m)
      nil
    (if (zp i)
        (cons (bit-unit-list j n) (bit-mat0 (1- m) n))
      (cons (bit-listn0 n) (bit-mat-unit (1- i) j (1- m) n))))))

(skip-proofs
(define mm-tensor-3 ((i natp) (j natp) (k natp) (n natp))
  :returns (tt bit-list-p)
  :verify-guards :after-returns
  (if (zp k)
      (bit-listn0 (* n n n n n n))
    (bit-list-add
     (tensor (bit-mat-unit i j n n)
             (bit-mat-unit j (1- k) n n)
             (bit-mat-unit i (1- k) n n))
     (mm-tensor-3 i j (1- k) n)))))

(skip-proofs
(define mm-tensor-2 ((i natp) (j natp) (n natp))
  :returns (tt bit-list-p)
  :verify-guards :after-returns
  (if (zp j)
      (bit-listn0 (* n n n n n n))
    (bit-list-add (mm-tensor-3 i (1- j) n n)
                  (mm-tensor-2 i (1- j) n)))))

(skip-proofs
(define mm-tensor-1 ((i natp) (n natp))
  :returns (tt bit-list-p)
  :verify-guards :after-returns
  (if (zp i)
      (bit-listn0 (* n n n n n n))
    (bit-list-add (mm-tensor-2 (1- i) n n)
                  (mm-tensor-1 (1- i) n)))))

(skip-proofs
(define mm-tensor ((n natp))
  :returns (tt bit-list-p)
  (mm-tensor-1 n n)))

(skip-proofs
(define correct-schemep (sch (n natp))
  :returns (yes/no booleanp)
  (and (schemep sch n)
       (equal (scheme-sum sch n) (mm-tensor n)))))

(skip-proofs
(define mat-entry ((i natp) (j natp) (a bit-list-listp))
  :enabled t
  (nth j (nth i a))))

(skip-proofs
(define bit-mat-scale ((b bitp) (a bit-list-listp))
  :returns (c bit-list-listp)
  (if (atom a)
      nil
    (cons (bit-list-scale b (car a))
          (bit-mat-scale b (cdr a))))))

(skip-proofs
(define mat-mul-entry ((d bit-list-listp) (f bit-list-listp)
                       (k natp) (l natp) (h natp) (n natp))
  :guard (and (bit-matp d n n) (bit-matp f n n) (< k n) (< l n) (<= h n))

  :returns (b bitp)
  :verify-guards :after-returns
  (if (zp h)
      0
    (bitxor (bitand (mat-entry k (1- h) d) (mat-entry (1- h) l f))
            (mat-mul-entry d f k l (1- h) n)))))

(skip-proofs
(define bit-mat-mul-row ((d bit-list-listp) (f bit-list-listp)
                         (k natp) (c natp) (n natp))
  :guard (and (bit-matp d n n) (bit-matp f n n) (< k n) (<= c n))
  :returns (r bit-list-p)
  :verify-guards :after-returns
  (if (zp c)
      nil
    (cons (mat-mul-entry d f k (- n c) n n)
          (bit-mat-mul-row d f k (1- c) n)))))

(skip-proofs
(define bit-mat-mul-rows ((d bit-list-listp) (f bit-list-listp)
                          (c natp) (n natp))
  :guard (and (bit-matp d n n) (bit-matp f n n) (<= c n))
  :returns (a bit-list-listp)
  :verify-guards :after-returns
  (if (zp c)
      nil
    (cons (bit-mat-mul-row d f (- n c) n n)
          (bit-mat-mul-rows d f (1- c) n)))))

(skip-proofs
(define bit-mat-mul ((d bit-list-listp) (f bit-list-listp) (n natp))
  :guard (and (bit-matp d n n) (bit-matp f n n))
  :returns (a bit-list-listp)
  (bit-mat-mul-rows d f n n)))

(skip-proofs
(define lformp (e (n natp))
  :returns (yes/no booleanp)
  (and (consp e)
       (true-listp e)
       (equal (len e) 3)
       (case (car e)
         (:var (and (natp (cadr e)) (natp (caddr e))
                    (< (cadr e) n) (< (caddr e) n)))
         (:add (and (lformp (cadr e) n) (lformp (caddr e) n)))
         (:scale (and (bitp (cadr e)) (lformp (caddr e) n)))
         (t nil)))))

(skip-proofs
(define eval-lform (e (m bit-list-listp) (n natp))
  :guard (and (lformp e n) (bit-matp m n n))

  :returns (b bitp :hyp :guard
              )
  :verify-guards :after-returns
  (case (car e)
    (:var (mat-entry (cadr e) (caddr e) m))
    (:add (bitxor (eval-lform (cadr e) m n) (eval-lform (caddr e) m n)))
    (:scale (bitand (cadr e) (eval-lform (caddr e) m n)))
    (t 0))))

(skip-proofs
(define lform-mat (e (n natp))
  :guard (lformp e n)

  :returns (a bit-list-listp)
  :verify-guards :after-returns
  (case (car e)
    (:var (bit-mat-unit (cadr e) (caddr e) n n))
    (:add (bit-mat-add (lform-mat (cadr e) n) (lform-mat (caddr e) n)))
    (:scale (bit-mat-scale (cadr e) (lform-mat (caddr e) n)))
    (t (bit-mat0 n n)))))

(skip-proofs
(define prodp (p (n natp))
  :returns (yes/no booleanp)
  (and (true-listp p)
       (equal (len p) 3)
       (eq (car p) :mul)
       (lformp (cadr p) n)
       (lformp (caddr p) n))))

(skip-proofs
(define prod-listp (l (n natp))
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (prodp (car l) n)
         (prod-listp (cdr l) n)))))

(skip-proofs
(define index-listp (l (r natp))
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (natp (car l))
         (< (car l) r)
         (index-listp (cdr l) r)))))

(skip-proofs
(define idx-rowp (x)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (nat-listp (car x))
         (idx-rowp (cdr x))))))

(skip-proofs
(define idx-tablep (x)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (idx-rowp (car x))
         (idx-tablep (cdr x))))))

(skip-proofs
(define outs-rowp (row (r natp) (n natp))
  :returns (yes/no booleanp)
  (if (zp n)
      (null row)
    (and (consp row)
         (index-listp (car row) r)
         (outs-rowp (cdr row) r (1- n))))))

(skip-proofs
(define outs-rowsp (outs (r natp) (m natp) (n natp))
  :returns (yes/no booleanp)
  (if (zp m)
      (null outs)
    (and (consp outs)
         (outs-rowp (car outs) r n)
         (outs-rowsp (cdr outs) r (1- m) n)))))

(skip-proofs
(define algop (alg (n natp))
  :returns (yes/no booleanp)
  (and (consp alg)
       (prod-listp (car alg) n)
       (outs-rowsp (cdr alg) (len (car alg)) n n))))

(skip-proofs
(define prod-value (p (d bit-list-listp) (f bit-list-listp) (n natp))
  :guard (and (prodp p n) (bit-matp d n n) (bit-matp f n n))

  :returns (b bitp)
  (bitand (eval-lform (cadr p) d n)
          (eval-lform (caddr p) f n))))

(skip-proofs
(define prods-xor ((idxs nat-listp) (prods true-listp)
                   (d bit-list-listp) (f bit-list-listp) (n natp))
  :guard (and (index-listp idxs (len prods))
              (prod-listp prods n)
              (bit-matp d n n)
              (bit-matp f n n))

  :returns (b bitp)
  :verify-guards :after-returns
  (if (atom idxs)
      0
    (bitxor (prod-value (nth (car idxs) prods) d f n)
            (prods-xor (cdr idxs) prods d f n)))))

(skip-proofs
(define algo-entry (alg (d bit-list-listp) (f bit-list-listp)
                    (k natp) (l natp) (n natp))
  :guard (and (algop alg n) (bit-matp d n n) (bit-matp f n n)
              (< k n) (< l n))

  :returns (b bitp)
  (prods-xor (nth l (nth k (cdr alg))) (car alg) d f n)))

(skip-proofs
(define eval-algo-row (alg (d bit-list-listp) (f bit-list-listp)
                       (k natp) (c natp) (n natp))
  :guard (and (algop alg n) (bit-matp d n n) (bit-matp f n n)
              (< k n) (<= c n))
  :returns (row bit-list-p)
  (if (zp c)
      nil
    (cons (algo-entry alg d f k (- n c) n)
          (eval-algo-row alg d f k (1- c) n)))))

(skip-proofs
(define eval-algo-rows (alg (d bit-list-listp) (f bit-list-listp)
                        (c natp) (n natp))
  :guard (and (algop alg n) (bit-matp d n n) (bit-matp f n n)
              (<= c n))
  :returns (a bit-list-listp)
  (if (zp c)
      nil
    (cons (eval-algo-row alg d f (- n c) n n)
          (eval-algo-rows alg d f (1- c) n)))))

(skip-proofs
(define eval-algo (alg (d bit-list-listp) (f bit-list-listp) (n natp))
  :guard (and (algop alg n) (bit-matp d n n) (bit-matp f n n))
  :returns (a bit-list-listp)
  (eval-algo-rows alg d f n n)))

(skip-proofs
(define occ-parity ((r natp) (idxs nat-listp))
  :returns (b bitp)
  (if (atom idxs)
      0
    (bitxor (if (equal (car idxs) r) 1 0)
            (occ-parity r (cdr idxs))))))

(skip-proofs
(define c-mat-row ((r natp) (row idx-rowp))
  :returns (x bit-list-p)
  (if (atom row)
      nil
    (cons (occ-parity r (car row))
          (c-mat-row r (cdr row))))))

(skip-proofs
(define c-mat ((r natp) (outs idx-tablep))
  :returns (a bit-list-listp)
  (if (atom outs)
      nil
    (cons (c-mat-row r (car outs))
          (c-mat r (cdr outs))))))

(skip-proofs
(define triples-from ((prods true-listp) (outs idx-tablep) (r natp) (n natp))
  :guard (prod-listp prods n)

  :returns (l mat-triple-listp)
  (if (atom prods)
      nil
    (cons (list (lform-mat (cadr (car prods)) n)
                (lform-mat (caddr (car prods)) n)
                (c-mat r outs))
          (triples-from (cdr prods) outs (1+ r) n)))))

(skip-proofs
(define algo-triples (alg (n natp))
  :guard (algop alg n)

  :returns (l mat-triple-listp)
  (triples-from (car alg) (cdr alg) 0 n)))

(skip-proofs
(define algo-scheme (alg (n natp))
  :guard (algop alg n)
  :returns (sch obag::bagp)
  (insert-all-nonzero (algo-triples alg n) nil n)))

(skip-proofs
(defun-sk algo-correctp (alg n)
  (forall (d f)
          (implies (and (bit-matp d n n)
                        (bit-matp f n n))
                   (equal (eval-algo alg d f n)
                          (bit-mat-mul d f n))))))

(skip-proofs
(define mat-lform-row ((a bit-list-listp) (i natp) (c natp) (n natp))
  :guard (and (bit-matp a n n) (< i n) (<= c n))
  :returns (e (lformp e n) :hyp :guard
              )
  (if (zp c)
      '(:scale 0 (:var 0 0))
    (if (equal (mat-entry i (- n c) a) 1)
        (list :add (list :var i (- n c)) (mat-lform-row a i (1- c) n))
      (mat-lform-row a i (1- c) n)))))

(skip-proofs
(define mat-lform-rows ((a bit-list-listp) (c natp) (n natp))
  :guard (and (bit-matp a n n) (<= c n) (< 0 n))
  :returns (e (lformp e n) :hyp :guard
              )
  (if (zp c)
      '(:scale 0 (:var 0 0))
    (list :add (mat-lform-row a (- n c) n n) (mat-lform-rows a (1- c) n)))))

(skip-proofs
(define mat-lform ((a bit-list-listp) (n natp))
  :guard (and (bit-matp a n n) (< 0 n))
  :returns (e (lformp e n) :hyp :guard)
  (mat-lform-rows a n n)))

(skip-proofs
(define c-indices ((l mat-triple-listp) (k natp) (j natp) (r natp))
  :returns (idxs nat-listp :hyp (natp r))
  (if (atom l)
      nil
    (if (equal (mat-entry k j (caddr (car l))) 1)
        (cons r (c-indices (cdr l) k j (1+ r)))
      (c-indices (cdr l) k j (1+ r))))))

(skip-proofs
(define triples-outs-row ((l mat-triple-listp) (k natp) (c natp) (n natp))
  :guard (<= c n)
  :returns (row idx-rowp)
  (if (zp c)
      nil
    (cons (c-indices l k (- n c) 0)
          (triples-outs-row l k (1- c) n)))))

(skip-proofs
(define triples-outs-rows ((l mat-triple-listp) (c natp) (n natp))
  :guard (<= c n)
  :returns (outs idx-tablep)
  (if (zp c)
      nil
    (cons (triples-outs-row l (- n c) n n)
          (triples-outs-rows l (1- c) n)))))

(skip-proofs
(define triples-outs ((l mat-triple-listp) (n natp))
  :returns (outs idx-tablep)
  (triples-outs-rows l n n)))

(skip-proofs
(define scheme-prods ((l mat-triple-listp) (n natp))
  :guard (and (summand-dim-listp l n) (< 0 n))
  :returns (prods true-listp)
  (if (atom l)
      nil
    (cons (list :mul (mat-lform (car (car l)) n) (mat-lform (cadr (car l)) n))
          (scheme-prods (cdr l) n)))))

(skip-proofs
(define scheme-algo ((l mat-triple-listp) (n natp))
  :guard (and (summand-dim-listp l n) (< 0 n))
  :returns (alg consp)
  (cons (scheme-prods l n) (triples-outs l n))))
</defs.lisp>

<cert.acl2>
; cert-flags: ? t :skip-proofs-okp t
</cert.acl2>

2. Write /work/solution.lisp. It must (include-book "defs") and then prove every theorem in <theorems>, each with exactly the name and statement given (MAIN-1, MAIN-2, MAIN-3, MAIN-4). You may add your own definitions and lemmas before them.

<theorems>
(in-package "ACL2")

(include-book "defs")

(defthm main-1
  (implies (and (correct-schemep sch n)
                (correct-schemep sch2 n)
                (natp n) (<= 2 n))
           (flip-plus-reachablep sch sch2 n)))

(defthm main-2
  (implies (and (algop alg n) (natp n) (< 0 n) (algo-correctp alg n))
           (correct-schemep (algo-scheme alg n) n)))

(defthm main-3
  (implies (and (correct-schemep sch n) (natp n) (< 0 n))
           (algo-correctp (scheme-algo sch n) n)))

(defthm main-4
  (implies (and (schemep sch n) (natp n) (< 0 n))
           (equal (algo-scheme (scheme-algo sch n) n) sch)))
</theorems>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
/work/solution.lisp must certify with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done. When you are done, print the final contents of /work/solution.lisp.
```

</details>

## Notes for reviewers

**Experiment 1.**
- For comparison: the paper reports that its connectivity proof is 19 books with 137 functions and 527
  theorems, and that an unassisted LLM formalization of the companion paper proved connectivity in 9 books
  with 409 theorems.


