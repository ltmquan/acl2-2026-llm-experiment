Prove the theorems below in ACL2(r). `stirling-ratio(n)` is n! / (√n · nⁿ · e⁻ⁿ).

1. Create /work/defs.lisp containing exactly the text between the tags.
defs.lisp holds the definitions the theorems use. Do not modify these files.

<defs.lisp>
(in-package "ACL2")

(include-book "arithmetic/factorial" :dir :system)
(include-book "nonstd/nsa/exp" :dir :system)
(include-book "nonstd/nsa/sqrt" :dir :system)

(defun stirling-ratio (n)
  (/ (factorial n) (* (acl2-sqrt n) (expt n n) (/ (acl2-exp n)))))
</defs.lisp>

2. Write /work/solution.lisp. It must (include-book "defs") and then prove every theorem in <theorems>, each
as a `defthm` with exactly the name and statement given. You may add your own definitions and lemmas, and any
`:rule-classes` and hints.

<theorems>
(defthm stirling-ratio-decreasing
  (implies (posp n) (< (stirling-ratio (1+ n)) (stirling-ratio n))))

(defthm stirling-ratio-decrease-bounded
  (implies (posp n)
           (< (stirling-ratio n)
              (* (stirling-ratio (1+ n))
                 (acl2-exp (- (/ (* 12 n)) (/ (* 12 (1+ n)))))))))
</theorems>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
Books are certified with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
/work/solution.lisp must certify with `cert.pl --acl2 acl2r`.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done.
When you are done, run `submit fw-stirling-bounds`, which saves /work. Then print a short summary: the files you
wrote, and for each theorem whether it is proved.
