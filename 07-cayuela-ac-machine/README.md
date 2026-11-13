# 07 — AC machine

**Paper:** P. O. Cayuela, *Mechanized Verification of Complex-to-Vector Derivations in a Three-Phase AC Machine Model* (ACL2 Workshop 2026). PDF in `source/paper.pdf`.
**Logic:** ACL2(r).

## The paper

The paper mechanically checks a hand derivation from electrical engineering: translating the
complex-number model of a three-phase AC machine into planar vectors. The results are mostly identities over
pairs: the three-phase collapse lemma, the torque-sign correction, and a generic version for any ω with
1 + ω + ω² = 0. An ACL2(r) part shows the hypotheses are satisfiable.

**Contribution.** A case study (mechanical checking of a derivation). The paper's headline (the torque sign) is
a restatement of a lemma, so for experiment 1 we chose its most substantial derivation. This is the easy tier
of the experiment.

**Authors' ACL2 books.** In the ACL2 community books on master, `books/workshops/2026/cayuela-ac-machine/` (added
2026-10-14, after 8.7), and in a public GitHub repository of the author. A copy is in
`source/authors-books/`. All 14 books certify on ACL2(r) 8.7.

## Files

```
07-cayuela-ac-machine/
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
| Model time | 6 min | 2.6 min |
| Tool calls | 41 | 18 |
| Certification time of solution.lisp (ACL2(r) 8.7) | 7.1 s | 1.5 s |
| Audit | CLEAN | CLEAN |
| solution.lisp: lines / definitions / theorems | 240 / 5 / 30 | 100 / 0 / 15 |

Authors' development (for scale): 14 files, 1,069 lines, 43 definitions, 78 theorems.

*Model time* runs from when the model received the prompt to the end of its run (setup not included).
Certification time is for `solution.lisp` alone, with its dependencies already certified, on our build
(experiment 2: against `exp2/checker/`). Sizes are counted with `tools/sizes.py` (definitions = `defun`,
`define`, `defun-sk`, `defmacro`, … and encapsulated functions; theorems = `defthm`, `defrule`, …, local
ones included). Both experiments: first attempt, Claude Opus 5.5 at medium effort.

## Experiment 1: English definitions and theorem

**Theorem given:** The three-phase collapse: Σ_{n=0}^{2} (2/3)(A·e^{jnγ}) e^{jnγ} = A for every planar vector A, with γ = 2π/3.

### Statement rewrites (paper text → prompt)

The definitions and theorem were copied from the paper as close to verbatim as possible. Every edit:

#### Sources
- Theorem: §4.2, displayed equation after "Generalized to an arbitrary planar vector A constant in n:"
  Σ_{n=0}^{2} (2/3)(A · e^{jnγ}) e^{jnγ} = A. (In the paper A carries a vector arrow.)
- "a vector (a, b) corresponds to the complex number a + jb": §2, "using the identification of R² with C".
- "· … the planar dot … product": §2 ("·, × are the planar dot and cross products").
- "γ = 2π/3": §4.1 ("with γ = 2π/3") and Fig. 1.

#### Edits
- "Generalized to an arbitrary planar vector A constant in n:" → "For an arbitrary planar vector A:" ("Generalized" refers to the
  paper's flux-linkage context; "constant in n" is implicit once A is a fixed vector).
- Vector arrow on A dropped (plain-text rendering).
- Definitions assembled from three places; "where j is the imaginary unit" added (engineering notation; j is otherwise undefined).
- Cross product omitted (not used by this theorem).
- Electrical-engineering context (flux linkage, stator, 120° symmetry) omitted: not needed to state the theorem.

### Prompt

<details>
<summary>Experiment 1 prompt (also in exp1/prompt.txt)</summary>

```text
Formalize the definitions and the theorem below in ACL2, and prove the theorem.

<definitions>
A planar vector (a, b) is identified with the complex number a + jb (the identification of R² with C), where j is the imaginary unit.
· is the planar dot product.
γ = 2π/3.
</definitions>

<theorem>
For an arbitrary planar vector A:

    Σ_{n=0}^{2} (2/3) (A · e^{jnγ}) e^{jnγ} = A.
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

| Target | Authors' name | Location | Meaning |
|---|---|---|---|
| MAIN-1 | `eq33-35-collapse-concrete` | 09-nonvacuity-acl2r.lisp:38 | three-phase collapse lemma with s3 = `(acl2-sqrt 3)` |
| MAIN-2 | `eq-im-w-is-crossp` | 05-torque-sign-correction.lisp:44 | Im(i_S i_R* e^{−jε}) = i_S × (i_R e^{+jε}) |
| MAIN-3 | `trinary-collapse-lemma` | 06-generic-omega-collapse-acl2r.lisp:108 | collapse lemma for any real pair ω with 1+ω+ω²=0 |
| MAIN-4 | `trinary-collapse-CONCRETE` | 06-generic-omega-collapse-acl2r.lisp:184 | collapse lemma for ω = e^{j2π/3}, unconditional |

### How the definitions were extracted

`definitions.lisp` has two parts. Part A is verbatim from books 00, 01, 02 and 05: the complex/vector
functions, the authors' encapsulated `cosine`/`sine` (with its constraints), `eiz`, `e0 e1 e2` and `torque-W`.
Part B is from book 06 (the ACL2(r) version), with every function renamed with a `G-` prefix (see below).
It includes `arithmetic-5/top` and `nonstd/nsa/trig`.

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
| `exp2/checker/defs.lisp` | `56d3c7d464ae45750665a433f1d6d6f9b5bc28d9e4412933c560797e8d5c909b` |

`exp2/definitions.lisp` differs from `exp2/checker/defs.lisp` only in comments
(`tools/check-comments-only.py`).

### Statement rewrites (authors' ACL2 → targets)

- **Part B renamed with prefix `G-`.** Book 06 redefines `cplxp`, `re`, `cplx` and `cscale` with different
  bodies from book 00, so the two cannot share one world. Every book-06 function the targets use is renamed
  (`cplxp → g-cplxp`, …); MAIN-3 and MAIN-4 use the renamed names. Bodies are otherwise verbatim.
- **`g-gamma-val` is written neutrally** as `(* 2/3 (acl2-pi))`, not the authors'
  `(+ (* 1/3 (acl2-pi)) (* 1/3 (acl2-pi)))`, which hints at the cosine-of-sums route. We proved the two equal.
- The book-06 lemma `cplxp-of-omega-pow` is local (needed only for guard verification).

### Prompt

<details>
<summary>Experiment 2 prompt (also in exp2/prompt.txt)</summary>

```text
Prove the theorems below in ACL2.

1. Create /work/defs.lisp, /work/cert.acl2, each containing exactly the text between its tags. defs.lisp holds the definitions the theorems use. Do not modify these files. Some definitions in defs.lisp are admitted with skip-proofs: their admissibility has been checked separately, and cert.acl2 permits skip-proofs so that books including defs.lisp can be certified. Your own files must not use skip-proofs: your solution will be checked against fully proved definitions without that permission.

<defs.lisp>
(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)

(include-book "nonstd/nsa/trig" :dir :system)

(skip-proofs
(defun cplxp (z)
  (declare (xargs :guard t))
  (and (consp z) (acl2-numberp (car z)) (acl2-numberp (cdr z)))))

(skip-proofs
(defun cplx (re im)
  (declare (xargs :guard (and (acl2-numberp re) (acl2-numberp im))))
  (cons re im)))

(skip-proofs
(defun re (z) (declare (xargs :guard (consp z))) (car z)))

(skip-proofs
(defun imz (z) (declare (xargs :guard (consp z))) (cdr z)))

(skip-proofs
(defun cconj (z)
  (declare (xargs :guard (cplxp z)))
  (cplx (re z) (- (imz z)))))

(skip-proofs
(defun cadd (z w)
  (declare (xargs :guard (and (cplxp z) (cplxp w))))
  (cplx (+ (re z) (re w)) (+ (imz z) (imz w)))))

(skip-proofs
(defun cscale (k z)
  (declare (xargs :guard (and (acl2-numberp k) (cplxp z))))
  (cplx (* k (re z)) (* k (imz z)))))

(skip-proofs
(defun cmul (z w)
  (declare (xargs :guard (and (cplxp z) (cplxp w))))
  (cplx (- (* (re z) (re w)) (* (imz z) (imz w)))
        (+ (* (re z) (imz w)) (* (imz z) (re w))))))

(skip-proofs
(defun dotp (z w)
  (declare (xargs :guard (and (cplxp z) (cplxp w))))
  (+ (* (re z) (re w)) (* (imz z) (imz w)))))

(skip-proofs
(defun crossp (z w)
  (declare (xargs :guard (and (cplxp z) (cplxp w))))
  (- (* (imz z) (re w)) (* (re z) (imz w)))))

(skip-proofs
(encapsulate
 (((cosine *) => *) ((sine *) => *))
 (local (defun cosine (x) (declare (ignore x)) 1))
 (local (defun sine (x) (declare (ignore x)) 0))
 (defthm pythagorean-cos-sin
   (equal (+ (* (cosine x) (cosine x)) (* (sine x) (sine x))) 1))
 (defthm cosine-even
   (equal (cosine (- x)) (cosine x)))
 (defthm sine-odd
   (equal (sine (- x)) (- (sine x))))
 (defthm cosine-difference
   (equal (cosine (- x y))
          (+ (* (cosine x) (cosine y)) (* (sine x) (sine y)))))
 (defthm sine-difference
   (equal (sine (- x y))
          (- (* (sine x) (cosine y)) (* (cosine x) (sine y)))))
 (defthm acl2-numberp-cosine (acl2-numberp (cosine x)))
 (defthm acl2-numberp-sine (acl2-numberp (sine x)))))

(skip-proofs
(defun eiz (theta)
  (declare (xargs :guard t))
  (cplx (cosine theta) (sine theta))))

(skip-proofs
(defun e0 () (declare (xargs :guard t)) (cplx 1 0)))

(skip-proofs
(defun e1 (s3)
  (declare (xargs :guard (acl2-numberp s3)))
  (cplx (- (/ 1 2)) (/ s3 2))))

(skip-proofs
(defun e2 (s3)
  (declare (xargs :guard (acl2-numberp s3)))
  (cplx (- (/ 1 2)) (- (/ s3 2)))))

(skip-proofs
(defun torque-W (i-s i-r eps)
  (declare (xargs :guard (and (cplxp i-s) (cplxp i-r))))
  (cmul i-s (cconj (cmul i-r (eiz eps))))))

(skip-proofs
(defun g-cplxp (u)
  (declare (xargs :guard t))
  (and (consp u) (acl2-numberp (car u)) (acl2-numberp (cdr u)))))

(skip-proofs
(defun g-re (u) (declare (xargs :guard (consp u))) (car u)))

(skip-proofs
(defun g-im (u) (declare (xargs :guard (consp u))) (cdr u)))

(skip-proofs
(defun g-cplx (a b)
  (declare (xargs :guard (and (acl2-numberp a) (acl2-numberp b))))
  (cons a b)))

(skip-proofs
(defun g-realpairp (u)
  (declare (xargs :guard t))
  (and (consp u) (realp (g-re u)) (realp (g-im u)))))

(skip-proofs
(defun g-c+ (u v)
  (declare (xargs :guard (and (g-cplxp u) (g-cplxp v))))
  (g-cplx (+ (g-re u) (g-re v)) (+ (g-im u) (g-im v)))))

(skip-proofs
(defun g-cscale (k u)
  (declare (xargs :guard (and (acl2-numberp k) (g-cplxp u))))
  (g-cplx (* k (g-re u)) (* k (g-im u)))))

(skip-proofs
(defun g-c* (u v)
  (declare (xargs :guard (and (g-cplxp u) (g-cplxp v))))
  (g-cplx (- (* (g-re u) (g-re v)) (* (g-im u) (g-im v)))
          (+ (* (g-re u) (g-im v)) (* (g-im u) (g-re v))))))

(skip-proofs
(defun g-vdot (u v)
  (declare (xargs :guard (and (g-cplxp u) (g-cplxp v))))
  (+ (* (g-re u) (g-re v)) (* (g-im u) (g-im v)))))

(skip-proofs
(defun g-omega-pow (omega n)
  (declare (xargs :guard (and (g-cplxp omega) (natp n))
                  :verify-guards nil))
  (if (zp n) (g-cplx 1 0) (g-c* omega (g-omega-pow omega (1- n))))))

(skip-proofs
(verify-guards g-omega-pow))

(skip-proofs
(defun g-collapse-sum (A omega)
  (declare (xargs :guard (and (g-cplxp A) (g-cplxp omega))))
  (g-c+ (g-cscale (* 2/3 (g-vdot A (g-omega-pow omega 0))) (g-omega-pow omega 0))
        (g-c+ (g-cscale (* 2/3 (g-vdot A (g-omega-pow omega 1))) (g-omega-pow omega 1))
              (g-cscale (* 2/3 (g-vdot A (g-omega-pow omega 2))) (g-omega-pow omega 2))))))

(skip-proofs
(defun g-gamma-val () (* 2/3 (acl2-pi))))

(skip-proofs
(defun g-omega-real () (g-cplx (acl2-cosine (g-gamma-val)) (acl2-sine (g-gamma-val)))))
</defs.lisp>

<cert.acl2>
; cert-flags: ? t :skip-proofs-okp t
</cert.acl2>

2. Write /work/solution.lisp. It must (include-book "defs") and then prove every theorem in <theorems>, each with exactly the name and statement given (MAIN-1, MAIN-2, MAIN-3, MAIN-4). You may add your own definitions and lemmas before them.

<theorems>
(defthm MAIN-1
  (implies (and (realp ra) (realp ia))
           (equal (cadd (cscale (* 2/3 (dotp (cplx ra ia) (e0))) (e0))
                  (cadd (cscale (* 2/3 (dotp (cplx ra ia) (e1 (acl2-sqrt 3))))
                                (e1 (acl2-sqrt 3)))
                        (cscale (* 2/3 (dotp (cplx ra ia) (e2 (acl2-sqrt 3))))
                                (e2 (acl2-sqrt 3)))))
                  (cplx ra ia))))

(defthm MAIN-2
  (equal (imz (torque-W i-s i-r eps))
         (crossp i-s (cmul i-r (eiz eps)))))

(defthm MAIN-3
  (implies (and (g-realpairp A) (g-realpairp omega)
                (equal (g-c+ (g-cplx 1 0) (g-c+ omega (g-c* omega omega)))
                       (g-cplx 0 0)))
           (equal (g-collapse-sum A omega) A)))

(defthm MAIN-4
  (implies (g-realpairp A)
           (equal (g-collapse-sum A (g-omega-real)) A)))
</theorems>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
/work/solution.lisp must certify with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done. When you are done, print the final contents of /work/solution.lisp.
```

</details>

## Notes for reviewers

**Experiment 1.**
- Pilot run: the prompt lacks the final "print the file" sentence of the other prompts. The audit cut-off is
  the end of the model's run; one later tool call (after our request) is excluded.


