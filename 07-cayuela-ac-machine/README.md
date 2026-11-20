# 07 — AC machine

**Paper:** P. O. Cayuela, *Mechanized Verification of Complex-to-Vector Derivations in a Three-Phase AC Machine Model*. PDF: `source/paper.pdf`. **Logic:** ACL2(r).

The paper mechanically checks a hand derivation from electrical engineering: translating the complex-number model of a three-phase AC machine into planar vectors. The results are mostly identities over pairs: the three-phase collapse lemma, the torque-sign correction, and a generic version for any ω with 1 + ω + ω² = 0. An ACL2(r) part shows the hypotheses are satisfiable.

**Authors' ACL2 books:** `source/authors-books/` (copy). From ACL2 master, `books/workshops/2026/cayuela-ac-machine/`.

## Experiment 1 — the model wrote the definitions, the statement and the proof

The model received only `exp1/prompt.txt` (below). Its answer is `exp1/solution.lisp`; it certifies, and its last
event is `MAIN`.

**To review:** do the definitions and `MAIN` in `exp1/solution.lisp` state the theorem in the prompt?

<details>
<summary>Experiment 1 prompt (exp1/prompt.txt)</summary>

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

## Experiment 2 — the model proved the authors' statements

The model received `exp2/prompt.txt` (below): the authors' definitions and the target theorems. Its answer is
`exp2/solution.lisp`; it certifies and proves every target with exactly the given statement.

- `exp2/definitions.lisp`: the definitions, with a comment before each form giving where in the authors'
  sources it comes from.
- `exp2/targets.lisp`: the target theorems, with the authors' theorem names in comments.

| Target | Authors' name | Location | Meaning |
|---|---|---|---|
| MAIN-1 | `eq33-35-collapse-concrete` | 09-nonvacuity-acl2r.lisp:38 | three-phase collapse lemma with s3 = `(acl2-sqrt 3)` |
| MAIN-2 | `eq-im-w-is-crossp` | 05-torque-sign-correction.lisp:44 | Im(i_S i_R* e^{−jε}) = i_S × (i_R e^{+jε}) |
| MAIN-3 | `trinary-collapse-lemma` | 06-generic-omega-collapse-acl2r.lisp:108 | collapse lemma for any real pair ω with 1+ω+ω²=0 |
| MAIN-4 | `trinary-collapse-CONCRETE` | 06-generic-omega-collapse-acl2r.lisp:184 | collapse lemma for ω = e^{j2π/3}, unconditional |

<details>
<summary>Experiment 2 prompt (exp2/prompt.txt)</summary>

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

## Experiment 4 — future work

### The air-gap inductance integral (Sections 5, 9)

`exp4/inductance/`: the prompt (`prompt.txt`), our definitions (`defs.lisp`), the theorems to prove
(`targets.lisp`; `admit.lisp`: the integral, to admit verbatim), and the model's proof (`solution.lisp`). The checker (`tools/check-prove.py`) requires
every target verbatim against our `defs.lisp`.

**Result:** 2 / 2 targets: as a limit of Riemann sums and as a definite integral.

**To review:** whether our statement captures the future-work item. The checker settles the proof.
