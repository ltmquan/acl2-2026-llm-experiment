# 01 — Basel

**Paper:** Ruben Gamboa, *An Alternative Proof in ACL2(r) of Euler's Solution to the Basel Problem*. PDF: `source/paper.pdf`. **Logic:** ACL2(r).

The paper proves in ACL2(r) that the sum of the reciprocals of the squares of the positive integers is π²/6 (the Basel problem). It follows a modern proof, not Euler's original argument. The statement uses non-standard analysis: for every infinitely large n, the partial sum is infinitely close to π²/6.

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
None beyond standard mathematics.
</definitions>

<theorem>
The sum of the squares of the reciprocals of the positive integers is exactly π²/6:

    Σ_{i=1}^{∞} 1/i² = π²/6.
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
| MAIN-1 | `basel-series-closed-form-close` | paper §6, p. 13 | for every infinitely large positive integer n, Σ_{k=1}^{n-1} 1/k² is i-close to π²/6 |

<details>
<summary>Experiment 2 prompt (exp2/prompt.txt)</summary>

```text
Prove the theorems below in ACL2.

1. Create /work/defs.lisp containing exactly the text between the tags. defs.lisp holds the definitions the theorems use. Do not modify these files.

<defs.lisp>
(in-package "ACL2")

(include-book "nonstd/nsa/trig" :dir :system)

(defun basel-series (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      0
      (+ (expt i -2)
         (basel-series (1+ i) n))))
</defs.lisp>

2. Write /work/solution.lisp. It must (include-book "defs") and then prove every theorem in <theorems>, each with exactly the name and statement given (MAIN-1). You may add your own definitions and lemmas before them.

<theorems>
(defthm MAIN-1
  (implies (and (posp n)
                (i-large n))
           (i-close (basel-series 1 n)
                    (/ (expt (acl2-pi) 2) 6))))
</theorems>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
/work/solution.lisp must certify with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done. When you are done, print the final contents of /work/solution.lisp.
```

</details>
