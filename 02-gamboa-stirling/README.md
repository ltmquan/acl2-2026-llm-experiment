# 02 — Stirling

**Paper:** Ruben Gamboa, *A Mechanical Proof of Stirling's Approximation in ACL2(r)*. PDF: `source/paper.pdf`. **Logic:** ACL2(r).

The paper proves Stirling's approximation in ACL2(r) in both usual forms: n!/(√(2πn)(n/e)ⁿ) is i-close to 1, and ln n! is i-close to n ln n − n + ln √(2πn), for every infinitely large n. It follows the textbook route. It computes ∫ ln by the fundamental theorem of calculus and bounds the trapezoid-rule error, which gives n! ∼ C√n(n/e)ⁿ. It then proves Wallis's product, which needs integration by parts (new in ACL2(r)) and the recurrence for ∫ sinⁿ. Finally, it combines the two to show C = √(2π).

**Authors' ACL2 books:** None: not in the ACL2 community books, and no pull request to the ACL2 repository. Experiment 2's definitions and targets were transcribed from the paper.

## Experiment 1 — the model wrote the definitions, the statement and the proof

The model received only `exp1/prompt.txt` (below). Its answer is `exp1/solution.lisp`; it certifies, and its last
event is `MAIN`.

**To review:** do the definitions and `MAIN` in `exp1/solution.lisp` state the theorem in the prompt?

<details>
<summary>Experiment 1 prompt (exp1/prompt.txt)</summary>

```text
Formalize the definitions and the theorem below in ACL2, and prove the theorem.

<definitions>
The symbol ∼ is used here formally to indicate asymptotic equivalence. In particular, f(n) ∼ g(n) means that lim_{n→∞} f(n)/g(n) = 1.
</definitions>

<theorem>
n! ∼ √(2πn) (n/e)^n
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

| Target | Authors' name | Source | Meaning |
|---|---|---|---|
| MAIN-1 | `stirling-approximation-to-factorial` | paper §5 | n!/(√(2π) nⁿ e⁻ⁿ √n) is i-close to 1 for i-large natural n |
| MAIN-2 | `stirling-approximation-to-ln-factorial` | paper §5 | ln n! is i-close to ln(nⁿ) − n + ln √(2πn) for i-large positive n |
| MAIN-3 | `wallis-product-convergence` | paper §4 | the standard part of the n-th Wallis partial product is π/2 for i-large natural n |

<details>
<summary>Experiment 2 prompt (exp2/prompt.txt)</summary>

```text
Prove the theorems below in ACL2.

1. Create /work/defs.lisp containing exactly the text between the tags. defs.lisp holds the definitions the theorems use. Do not modify these files.

<defs.lisp>
(in-package "ACL2")

(include-book "arithmetic/factorial" :dir :system)
(include-book "nonstd/nsa/factorial" :dir :system)
(include-book "nonstd/nsa/sqrt" :dir :system)
(include-book "nonstd/nsa/exp" :dir :system)
(include-book "nonstd/nsa/ln" :dir :system)
(include-book "nonstd/nsa/trig" :dir :system)

(defun wallis-product (n)
  (if (zp n)
      1
      (* (/ (* 2 n) (1- (* 2 n)))
         (/ (* 2 n) (1+ (* 2 n)))
         (wallis-product (1- n)))))
</defs.lisp>

2. Write /work/solution.lisp. It must (include-book "defs") and then prove every theorem in <theorems>, each with exactly the name and statement given (MAIN-1, MAIN-2, MAIN-3). You may add your own definitions and lemmas before them.

<theorems>
(defthm MAIN-1
  (implies (and (natp n)
                (i-large n))
           (i-close (/ (factorial n)
                       (* (acl2-sqrt (* 2 (acl2-pi)))
                          (expt n n)
                          (/ (acl2-exp n))
                          (acl2-sqrt n)))
                    1)))

(defthm MAIN-2
  (implies (and (posp n)
                (i-large n))
           (i-close (acl2-ln (factorial n))
                    (+ (acl2-ln (expt n n))
                       (- n)
                       (acl2-ln (acl2-sqrt (* 2 (acl2-pi) n)))))))

(defthm MAIN-3
  (implies (and (natp n)
                (i-large n))
           (equal (standard-part (wallis-product n))
                  (/ (acl2-pi) 2))))
</theorems>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
/work/solution.lisp must certify with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done. When you are done, print the final contents of /work/solution.lisp.
```

</details>
