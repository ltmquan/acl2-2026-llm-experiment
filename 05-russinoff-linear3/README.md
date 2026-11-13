# 05 — Linear III

**Paper:** David M. Russinoff, *A Formalization of Elementary Linear Algebra: Part III* (ACL2 Workshop 2026). PDF in `source/paper.pdf`.
**Logic:** ACL2.

## The paper

Part III builds finite-dimensional vector spaces and linear maps on top of Parts I–II (matrices
over a generic field, row reduction). V is an encapsulation with a canonical basis and coordinate function; W
is a renamed copy; `lin` is a constrained linear map V → W; `sp` is a constrained subspace. Because every
vector has coordinates, independence, coordinates relative to any basis, extension to a basis, the inverse of
a bijective map, and bases of kernel and image are all defined constructively by row reduction.

**Contribution.** A library: a textbook chapter of linear algebra, with a method (constructive definitions over
constrained functions, for later functional instantiation). There is no single headline theorem; the main
results are injective ⇒ dim V ≤ dim W and (surjective ⇔ equal dimension), a constructive inverse, extension
to a basis, well-defined subspace dimension, and kernel/image bases.

**Authors' ACL2 books.** In the ACL2 community books on master, added after 8.7:
`books/projects/linear/vectors.lisp` and `books/projects/linear/support/vectors.lisp` (commit 1d2b39a424).
A copy is in `source/authors-books/`.

## Files

```
05-russinoff-linear3/
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
| Result | proved (certified) | all 6 target(s) proved (certified, statements matched) |
| Model time | 16 min | 55 min |
| Tool calls | 53 | 194 |
| Certification time of solution.lisp (ACL2 8.7) | 1.2 s | 3.6 s |
| Audit | CLEAN | CLEAN |
| solution.lisp: lines / definitions / theorems | 934 / 101 / 201 | 2038 / 20 / 248 |

Authors' development (for scale): 2 files, 7,592 lines, 193 definitions, 473 theorems.

*Model time* runs from when the model received the prompt to the end of its run (setup not included).
Certification time is for `solution.lisp` alone, with its dependencies already certified, on our build
(experiment 2: against `exp2/checker/`). Sizes are counted with `tools/sizes.py` (definitions = `defun`,
`define`, `defun-sk`, `defmacro`, … and encapsulated functions; theorems = `defthm`, `defrule`, …, local
ones included). Both experiments: first attempt, Claude Opus 5.5 at medium effort.

## Experiment 1: English definitions and theorem

**Theorem given:** If T: V → W is injective then dim V ≤ dim W, and then T is surjective iff dim V = dim W (two results of §4, composed into one statement).

### Statement rewrites (paper text → prompt)

The definitions and theorem were copied from the paper as close to verbatim as possible. Every edit:

#### Sources
- Theorem: Sec. 4, p. 9 — prose before `injection-dim-<=` ("Now suppose lin is injective and vdim > wdim") and before `injection-surjection-dim-=` ("Next, we show that if lin is injective, then lin is surjective iff vdim = wdim.").
- F, V, axioms: Sec. 1 p. 1 ("arbitrary finite-dimensional vector space over the generic field"; field "arbitrary"), Sec. 2 p. 3 bullets.
- W: Sec. 4 p. 8 ("a vector space W, essentially the same as V, but with the functions renamed").
- Linear transformation: Sec. 4 p. 8; injective/surjective: Sec. 4 p. 9 (code only, translated).

#### Theorem: COMPOSED (flag)
No single English sentence states both results. Composed:
- "Now suppose lin is injective and vdim > wdim. … Thus, we have [injection-dim-<=]" → "If T is injective, then dim V ≤ dim W." (contrapositive of the proof's setup, stated as the formal result says).
- "Next, we show that if lin is injective, then lin is surjective iff vdim = wdim." → "Moreover, if T is injective, then T is surjective iff dim V = dim W." ("we show that" dropped, "Next" → "Moreover").
- Note: the task description says "injective + equal dimensions ⇒ surjective"; the paper's result is the **iff**, so the iff is used.

#### Edits to definitions
- ACL2 names → math: `lin` → T; `vdim`/`wdim` → dim V / dim W; `v0`/`w0` → 0; `vbasis0` → "the canonical basis"; `(vcoords0 x)` → "the coordinates of x"; `f0` → 0. (Rule 3.)
- "The following encapsulation characterizes the vector space V over the field F" / "The constrained functions include the following" → "The vector space V is given by the following" (removes encapsulation/representation hint).
- Operation bullets: ACL2 names removed; "constant function that returns" → "constant that is". "The associated exported theorems (elided above, along with the local definitions) include" → "These satisfy"; "v+"/"v*" → "vector addition"/"scalar multiplication". "constrained functions" → "functions".
- vdim bullet ("the length of vbasis0, which is the dimension of V") → "The length of the canonical basis is the dimension of V, written dim V."
- "Four additional axioms … are exported" → "The following axioms … hold" (five listed, see next).
- posp-vdim bullet: kept "this ensures that V is a nontrivial vector space"; **cut** "The only reason for this assumption is that it simplifies…matrices over F" (formalization hint).
- **Added** axiom "the list of coordinates of x is a list of dim V scalars": only in the code (`flistnp-vcoords0`), not in prose.
- "vlist" terminology dropped (not needed).
- W paragraph: **composed** from "a vector space W, essentially the same as V, but with the functions renamed … All definitions and lemmas pertaining to V are readily adapted to W"; "same field F" is implied by `lin-v*` using the same scalar c.
- Linear transformation, injective, surjective: **translated from ACL2 code** (lin encapsulate, `lin-injective-p`, `lin-surjective-p`); no paper prose exists. "a generic linear transformation lin mapping V to W" kept.

#### Left undefined (standard)
Field, vector space axioms (named only generically, as the paper does), linear combination (paper's `vcomb` = Σ c_i x_i, standard), list/length.

### Prompt

<details>
<summary>Experiment 1 prompt (also in exp1/prompt.txt)</summary>

```text
Formalize the definitions and the theorem below in ACL2, and prove the theorem.

<definitions>
Let F be an arbitrary field. V is an arbitrary finite-dimensional vector space over F. Elements of V and F are called vectors and scalars, respectively. The vector space V is given by the following:

  • a predicate that recognizes vectors;
  • a constant that is the zero vector, 0;
  • the unary additive inverse;
  • the binary operations of vector addition and multiplication by a scalar.

These satisfy the closure properties of the operations along with the other standard vector space axioms, which guarantee that the space forms an abelian group under vector addition and that the associative and distributive properties of scalar multiplication are satisfied.

Finite dimensionality is formalized by means of two additional functions:

  • a list of vectors called the canonical basis of V;
  • a unary function that returns the list of coordinates of a given vector with respect to this basis.

The length of the canonical basis is the dimension of V, written dim V. The following axioms pertaining to the canonical basis hold:

  • dim V is a positive integer; this ensures that V is a nontrivial vector space;
  • the canonical basis is a list of dim V vectors;
  • for every vector x, the list of coordinates of x is a list of dim V scalars;
  • every vector x is a linear combination of the canonical basis with coefficients given by the coordinates of x;
  • if a linear combination of the canonical basis evaluates to 0, then all coefficients are 0.

W is a second vector space over the same field F, essentially the same as V: it is given by its own recognizer, zero vector, additive inverse, vector addition, scalar multiplication, canonical basis and coordinate function, subject to the same axioms, and its dimension dim W is the length of its canonical basis.

T is a generic linear transformation mapping V to W, i.e., a function satisfying:

  • if x is in V, then T(x) is in W;
  • T(0) = 0;
  • if x and y are in V, then T(x + y) = T(x) + T(y);
  • if c is a scalar and x is in V, then T(c·x) = c·T(x).

T is injective if for every x in V, T(x) = 0 implies x = 0.

T is surjective if for every y in W there exists x in V such that T(x) = y.
</definitions>

<theorem>
If T is injective, then dim V ≤ dim W. Moreover, if T is injective, then T is surjective iff dim V = dim W.
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

| Target | Authors' theorem(s) (master `projects/linear/vectors.lisp`) | Meaning |
|---|---|---|
| MAIN-1 | `injection-dim-<=` ∧ `injection-surjection-dim-=` | if lin is injective, dim V ≤ dim W, and lin is surjective iff dim V = dim W |
| MAIN-2 | `lin-lin-inv` | for bijective lin, the constructive inverse `lin-inv` is a right inverse |
| MAIN-3 | `vbasisp-extend-to-basis` | `extend-to-basis` extends a nonempty independent list to a basis |
| MAIN-4 | `sdim-well-defined` | subspace dimension is well defined |
| MAIN-5 | `klistnp-kbasis` ∧ `vindepp-kbasis` ∧ `flistnp-kcoords` ∧ `kbasis-spans` | `kbasis` is a basis of the kernel, with coordinates `kcoords` |
| MAIN-6 | `ilistnp-ibasis` ∧ `ibasis-lin-indep` ∧ `flistnp-icoords` ∧ `ibasis-spans` | `ibasis` is a basis of the image, with coordinates `icoords` |

### How the definitions were extracted

`definitions.lisp` includes `projects/linear/reduction` (Parts I–II, in 8.7) and copies the
authors' Part III forms verbatim from master `vectors.lisp`, in order: the V, W, lin and sp encapsulates, the
`sbasis1` encapsulate, and the constructive functions the targets use (`lin-inv`, `extend-to-basis`,
`kbasis`, `kcoords`, `ibasis`, `icoords`, …). Definitions no target needs are left out. Admitting the
encapsulate witnesses, a termination hint and the `sbasis1` encapsulate needs 89 local lemmas, copied verbatim
from `support/vectors.lisp`; a greedy pruning removed every one that was not needed.
**Caveat:** some of these local lemmas are steps the authors also use toward the targets (for example
`vdepp-vcomb-v0`). They are not exported, but the checker's copy of `definitions.lisp` contains them. The
model saw a different copy without them (see the experiment-2 report).

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
| `exp2/checker/cert.acl2` | `e39b0ab97ce3526d595a9df27a4e5a4fe42bdbbc2e6eef70ed6a782d17901975` |
| `exp2/checker/defs.lisp` | `5c74b7d933b519762fb813de4fd0b02384fcbbf8b4564b6cc47594bf305941d7` |

`exp2/definitions.lisp` differs from `exp2/checker/defs.lisp` only in comments
(`tools/check-comments-only.py`).

### Statement rewrites (authors' ACL2 → targets)

- Package DM (the authors' package), with `cert.acl2` loading `projects/numbers/portcullis`.
- Targets are named MAIN-k. MAIN-1, MAIN-5 and MAIN-6 are conjunctions of the authors' theorems with the same
  hypotheses. `defthmd` became `defthm`; hints and rule classes dropped. Statement bodies are the authors' text.
- The kernel and image halves are separate targets because their constructions and proofs differ, and the
  image proof builds on the kernel one.
- The 8.7 Parts I–II differ from master only in the field encapsulate (master adds formals, guards and a
  `defattach` to `f+ f* f- f/`); constraints and bodies are identical, and Part III declares no guards.

### Prompt

<details>
<summary>Experiment 2 prompt (also in exp2/prompt.txt)</summary>

```text
Prove the theorems below in ACL2.

1. Create /work/defs.lisp, /work/cert.acl2, each containing exactly the text between its tags. defs.lisp holds the definitions the theorems use. Do not modify these files. Some definitions in defs.lisp are admitted with skip-proofs: their admissibility has been checked separately, and cert.acl2 permits skip-proofs so that books including defs.lisp can be certified. Your own files must not use skip-proofs: your solution will be checked against fully proved definitions without that permission.

<defs.lisp>
(in-package "DM")

(include-book "projects/linear/reduction" :dir :system)

(skip-proofs
(encapsulate (((vp *) => *)        ;vector recognizer
              ((v+ * *) => *)      ;vector addition
	      ((v0) => *)          ;zero vector
	      ((v- *) => *)        ;additive inverse
	      ((v* * *) => *)      ;scalar multiplication
	      ((vbasis0) => *)     ;canonical basis
	      ((vcoords0 *) => *)) ;coordinates relative ro basis
  (local (defun vp (x) (fp x)))
  (local (defun v+ (x y) (f+ x y)))
  (local (defun v0 () (f0)))
  (local (defun v- (x) (f- x)))
  (local (defun v* (c x) (f* c x)))
  (local (defun vbasis0 () (list (f1))))
  (local (defun vcoords0 (x) (list x)))
  (defthm vp-v0
    (vp (v0)))
  (defthm vp-v-
    (implies (vp x) (vp (v- x))))
  (defthm v+closed (implies (and (vp x) (vp y)) (vp (v+ x y))))
  (defthmd v+comm
    (implies (and (vp x) (vp y)) (equal (v+ x y) (v+ y x)))
    )
  (defthmd v+assoc
    (implies (and (vp x) (vp y) (vp z)) (equal (v+ x (v+ y z)) (v+ (v+ x y) z)))
    )
  (defthm v+id
    (implies (vp x) (equal (v+ x (v0)) x)))
  (defthm v+inv
    (implies (vp x) (equal (v+ x (v- x)) (v0))))
  (defthm v*closed
    (implies (and (fp c) (vp x)) (vp (v* c x))))
  (defthm v*id
    (implies (vp x) (equal (v* (f1) x) x)))
  (defthmd v*assoc
    (implies (and (fp c) (fp d) (vp x)) (equal (v* c (v* d x)) (v* (f* c d) x)))
    )
  (defthmd vdistf
    (implies (and (fp c) (fp d) (vp x)) (equal (v+ (v* c x) (v* d x)) (v* (f+ c d) x)))
    )
  (defthmd vdistv
    (implies (and (fp c) (vp x) (vp y)) (equal (v+ (v* c x) (v* c y)) (v* c (v+ x y))))
    )
  (defun vlistnp (x n)
    (if (zp n)
        (null x)
      (and (consp x)
           (vp (car x))
	   (vlistnp (cdr x) (1- n)))))
  (defun vcomb (flist vlist)
    (if (consp flist)
        (v+ (v* (car flist) (car vlist))
	    (vcomb (cdr flist) (cdr vlist)))
      (v0)))
  (defun vdim () (len (vbasis0)))
  (defthmd posp-vdim
    (posp (vdim)))
  (in-theory (disable (vdim) (vlistnp) (vcomb)))
  (defthm vlistnp-basis0
    (vlistnp (vbasis0) (vdim)))
  (defthm flistnp-vcoords0
    (implies (vp x) (flistnp (vcoords0 x) (vdim))))
  (defthm vbasis0-spans
    (implies (vp x)
             (equal (vcomb (vcoords0 x) (vbasis0))
		    x)))
  (defthmd vbasis0-lin-indep
    (implies (and (flistnp c (vdim))
                  (equal (vcomb c (vbasis0)) (v0)))
	     (equal (flistn0 (vdim)) c)))
  (in-theory (disable vdim))))

(skip-proofs
(defun vcoord-mat (l)
  (if (consp l)
      (cons (vcoords0 (car l))
	    (vcoord-mat (cdr l)))
    ())))

(skip-proofs
(defund vindepp (l)
  (or (null l)
      (equal (row-rank (vcoord-mat l))
             (len l)))))

(skip-proofs
(defund vdepp (l)
  (not (vindepp l))))

(skip-proofs
(defun vdep-coeffs (l)
  (nth (1- (len l)) (row-reduce-mat (vcoord-mat l)))))

(skip-proofs
(defund vcoords (x l)
  (if (null l)
      ()
    (let ((c (vdep-coeffs (cons x l))))
      (flist-scalar-mul (f- (f/ (car c))) (cdr c))))))

(skip-proofs
(defund vbasisp (l)
  (and (vlistnp l (vdim))
       (vindepp l))))

(skip-proofs
(defund vunspanned (l)
  (nth (car (free-inds (row-reduce (vcoord-mat l)) (vdim)))
       (vbasis0))))

(skip-proofs
(defun extend-to-basis (l)
  (declare (xargs :measure (nfix (- (vdim) (len l)))))
  (if (and (vlistnp l (len l)) (vindepp l) (< (len l) (vdim)))
      (extend-to-basis (cons (vunspanned l) l))
    l)))

(skip-proofs
(encapsulate (((wp *) => *)        ;vector recognizer
              ((w+ * *) => *)      ;vector addition
	      ((w0) => *)          ;zero vector
	      ((w- *) => *)        ;additive inverse
	      ((w* * *) => *)      ;scalar multiplication
	      ((wbasis0) => *)     ;canonical basis
	      ((wcoords0 *) => *)) ;coordinates relative ro basis
  (local (defun wp (x) (fp x)))
  (local (defun w+ (x y) (f+ x y)))
  (local (defun w0 () (f0)))
  (local (defun w- (x) (f- x)))
  (local (defun w* (c x) (f* c x)))
  (local (defun wbasis0 () (list (f1))))
  (local (defun wcoords0 (x) (list x)))
  (defthm wp-w0
    (wp (w0)))
  (defthm wp-w-
    (implies (wp x) (wp (w- x))))
  (defthm w+closed (implies (and (wp x) (wp y)) (wp (w+ x y))))
  (defthmd w+comm
    (implies (and (wp x) (wp y)) (equal (w+ x y) (w+ y x)))
    )
  (defthmd w+assoc
    (implies (and (wp x) (wp y) (wp z)) (equal (w+ x (w+ y z)) (w+ (w+ x y) z)))
    )
  (defthm w+id
    (implies (wp x) (equal (w+ x (w0)) x)))
  (defthm w+inv
    (implies (wp x) (equal (w+ x (w- x)) (w0))))
  (defthm w*closed
    (implies (and (fp c) (wp x)) (wp (w* c x))))
  (defthm w*id
    (implies (wp x) (equal (w* (f1) x) x)))
  (defthmd w*assoc
    (implies (and (fp c) (fp d) (wp x)) (equal (w* c (w* d x)) (w* (f* c d) x)))
    )
  (defthmd wdistf
    (implies (and (fp c) (fp d) (wp x)) (equal (w+ (w* c x) (w* d x)) (w* (f+ c d) x)))
    )
  (defthmd wdistw
    (implies (and (fp c) (wp x) (wp y)) (equal (w+ (w* c x) (w* c y)) (w* c (w+ x y))))
    )
  (defun wlistnp (x n)
    (if (zp n)
        (null x)
      (and (consp x)
           (wp (car x))
	   (wlistnp (cdr x) (1- n)))))
  (defun wcomb (flist wlist)
    (if (consp flist)
        (w+ (w* (car flist) (car wlist))
	    (wcomb (cdr flist) (cdr wlist)))
      (w0)))
  (defun wdim () (len (wbasis0)))
  (defthmd posp-wdim
    (posp (wdim)))
  (in-theory (disable (wdim) (wlistnp) (wcomb)))
  (defthm wlistnp-basis0
    (wlistnp (wbasis0) (wdim)))
  (defthm flistnp-wcoords0
    (implies (wp x) (flistnp (wcoords0 x) (wdim))))
  (defthm wbasis0-spans
    (implies (wp x)
             (equal (wcomb (wcoords0 x) (wbasis0))
		    x)))
  (defthmd wbasis0-lin-indep
    (implies (and (flistnp c (wdim))
                  (equal (wcomb c (wbasis0)) (w0)))
	     (equal (flistn0 (wdim)) c)))
  (in-theory (disable wdim))))

(skip-proofs
(defun wcoord-mat (l)
  (if (consp l)
      (cons (wcoords0 (car l))
	    (wcoord-mat (cdr l)))
    ())))

(skip-proofs
(defund windepp (l)
  (or (null l)
      (equal (row-rank (wcoord-mat l))
             (len l)))))

(skip-proofs
(encapsulate (((lin *) => *))
  (local (defun lin (x) (declare (ignore x)) (w0)))
  (defthm lin-val
    (implies (vp x) (wp (lin x))))
  (defthm lin-v0
    (equal (lin (v0)) (w0)))
  (defthm lin-v+
    (implies (and (vp x) (vp y))
             (equal (lin (v+ x y))
	            (w+ (lin x) (lin y)))))
  (defthm lin-v*
    (implies (and (fp c) (vp x))
             (equal (lin (v* c x))
	            (w* c (lin x)))))))

(skip-proofs
(defun lin-list (l)
  (if (consp l)
      (cons (lin (car l))
            (lin-list (cdr l)))
    ())))

(skip-proofs
(defund lin-mat ()
  (wcoord-mat (lin-list (vbasis0)))))

(in-theory (disable (lin-mat)))

(skip-proofs
(defun-sk lin-injective-p ()
  (forall (x)
    (implies (and (vp x) (equal (lin x) (w0)))
             (equal x (v0))))))

(skip-proofs
(defchoose lin-preimage x (y)
  (and (vp x)
       (equal (lin x) y))))

(skip-proofs
(defun-sk lin-surjective-p ()
  (forall (y)
    (implies (wp y)
             (and (vp (lin-preimage y))
	          (equal (lin (lin-preimage y))
		         y))))))

(in-theory (disable lin-injective-p lin-surjective-p))

(skip-proofs
(defund lin-inv (y)
  (vcomb (car (fmat* (list (wcoords0 y)) (inverse-mat (lin-mat))))
         (vbasis0))))

(skip-proofs
(encapsulate (((sp *) => *))
  (local (defun sp (x) (vp x)))
  (defthm sp-vp (implies (sp x) (vp x)))
  (defthm sp-v0 (sp (v0)))
  (defthm sp-v- (implies (sp x) (sp (v- x))))
  (defthm s+closed (implies (and (sp x) (sp y)) (sp (v+ x y))))
  (defthm s*closed (implies (and (fp c) (sp x)) (sp (v* c x))))))

(skip-proofs
(defun slistnp (x n)
  (if (zp n)
      (null x)
    (and (consp x)
         (sp (car x))
         (slistnp (cdr x) (1- n))))))

(skip-proofs
(defchoose sunspanned x (l)
  (and (sp x) (vindepp (cons x l)))))

(skip-proofs
(defun sbasis0-aux (l)
  (declare (xargs :measure (nfix (- (vdim) (len l)))
                  ))
  (let ((x (sunspanned l)))
    (if (and (slistnp l (len l)) (sp x) (vindepp (cons x l)))
        (sbasis0-aux (cons x l))
      l))))

(skip-proofs
(defund sbasis0 ()
  (sbasis0-aux ())))

(skip-proofs
(defun sdim () (len (sbasis0))))

(in-theory (disable (slistnp) (sbasis0-aux) (sbasis0) (sdim)))

(skip-proofs
(defund scoords0 (x)
  (vcoords x (sbasis0))))

(skip-proofs
(encapsulate (((sbasis1) => *) ((scoords1 *) => *))
  (local (defun sbasis1 () (sbasis0)))
  (local (defun scoords1 (x) (scoords0 x)))
  (defun sdim1 () (len (sbasis1)))
  (defthmd slistnp-sbasis1
    (slistnp (sbasis1) (sdim1))
    )
  (defthmd flistnp-scoords1
    (implies (and (posp (sdim)) (sp x)) (flistnp (scoords1 x) (sdim1)))
    )
  (defthmd sbasis1-spans
    (implies (and (posp (sdim)) (sp x))
             (equal (vcomb (scoords1 x) (sbasis1))
                    x))
    )
  (defthm vindepp-sbasis1
    (vindepp (sbasis1))
    )))

(skip-proofs
(defund in-kernel-p (x)
  (and (vp x)
       (equal (lin x) (w0)))))

(skip-proofs
(defun klistnp (x n)
  (if (zp n)
      (null x)
    (and (consp x)
         (in-kernel-p (car x))
         (klistnp (cdr x) (1- n))))))

(skip-proofs
(defund kbasis-coord (i j)
  (let* ((ar (row-reduce (transpose-mat (lin-mat))))
	 (l (lead-inds ar)))
    (if (member i l)
        (f- (entry (index i l) j ar))
      (if (= i j)
          (f1)
        (f0))))))

(skip-proofs
(defun kbasis-coords-aux (i j)
  (if (posp i)
      (append (kbasis-coords-aux (1- i) j)
              (list (kbasis-coord (1- i) j)))
    ())))

(skip-proofs
(defund kbasis-coords (j) (kbasis-coords-aux (vdim) j)))

(skip-proofs
(defun kbasis-aux (f)
  (if (consp f)
      (cons (vcomb (kbasis-coords (car f)) (vbasis0))
            (kbasis-aux (cdr f)))
    ())))

(skip-proofs
(defund kbasis ()
  (let ((ar (row-reduce (transpose-mat (lin-mat)))))
    (kbasis-aux (free-inds ar (vdim))))))

(in-theory (disable (kbasis)))

(skip-proofs
(defund kdim () (len (kbasis))))

(in-theory (disable (kdim)))

(skip-proofs
(defun kcoords-aux (x f)
  (if (consp f)
      (cons (nth (car f) (vcoords0 x))
            (kcoords-aux x (cdr f)))
    ())))

(skip-proofs
(defund kcoords (x)
   (let* ((ar (row-reduce (transpose-mat (lin-mat))))
          (f (free-inds ar (vdim))))
     (kcoords-aux x f))))

(skip-proofs
(defund in-image-p (x)
  (let ((p (lin-preimage x)))
    (and (vp p) (equal (lin p) x)))))

(skip-proofs
(defun idim () (- (vdim) (kdim))))

(skip-proofs
(defund extend-kbasis ()
  (if (posp (kdim))
      (extend-to-basis (kbasis))
    (vbasis0))))

(in-theory (disable (extend-kbasis)))

(skip-proofs
(defun firstn (n l)
  (if (zp n)
      ()
    (cons (car l) (firstn (1- n) (cdr l))))))

(skip-proofs
(defund ibasis ()
  (lin-list (firstn (idim) (extend-kbasis)))))

(in-theory (disable (ibasis)))

(skip-proofs
(defun ilistnp (x n)
  (if (zp n)
      (null x)
    (and (consp x)
         (in-image-p (car x))
         (ilistnp (cdr x) (1- n))))))

(skip-proofs
(defund icoords (x)
  (firstn (idim) (vcoords (lin-preimage x) (extend-kbasis)))))
</defs.lisp>

<cert.acl2>
(include-book "projects/numbers/portcullis" :dir :system)
; cert-flags: ? t :skip-proofs-okp t
</cert.acl2>

2. Write /work/solution.lisp. It must (include-book "defs") and then prove every theorem in <theorems>, each with exactly the name and statement given (MAIN-1, MAIN-2, MAIN-3, MAIN-4, MAIN-5, MAIN-6). You may add your own definitions and lemmas before them.

<theorems>
(in-package "DM")


(defthm MAIN-1
  (and (implies (lin-injective-p)
                (<= (vdim) (wdim)))
       (implies (lin-injective-p)
                (iff (lin-surjective-p)
                     (equal (vdim) (wdim))))))

(defthm MAIN-2
  (implies (and (lin-injective-p)
                (lin-surjective-p)
                (wp y))
           (let ((x (lin-inv y)))
             (and (vp x)
                  (equal (lin x) y)))))

(defthm MAIN-3
  (implies (and (vlistnp l n) (posp n) (vindepp l))
           (vbasisp (extend-to-basis l))))

(defthm MAIN-4
  (= (sdim1) (sdim)))

(defthm MAIN-5
  (and (klistnp (kbasis) (kdim))
       (vindepp (kbasis))
       (implies (in-kernel-p x)
                (flistnp (kcoords x) (kdim)))
       (implies (in-kernel-p x)
                (equal (vcomb (kcoords x) (kbasis)) x))))

(defthm MAIN-6
  (and (ilistnp (ibasis) (idim))
       (windepp (ibasis))
       (implies (in-image-p x)
                (flistnp (icoords x) (idim)))
       (implies (in-image-p x)
                (equal (wcomb (icoords x) (ibasis)) x))))
</theorems>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
/work/solution.lisp must certify with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done. When you are done, print the final contents of /work/solution.lisp.
```

</details>

## Notes for reviewers

**Experiment 2.**
- Proving the targets on 8.7 needs Part II lemmas that are only on master (e.g. `sol0p`, `flist-minus`); the
  model had to re-derive what it needed.

