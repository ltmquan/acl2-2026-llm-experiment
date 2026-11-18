Prove the theorems below in ACL2(r). `basel-series(i, n)` is the sum of 1/k² for i ≤ k < n, and
`euler-zeta2-product(i, n)` is the product of 1/(1 − p⁻²) over the primes p with i ≤ p < n.

1. Create /work/defs.lisp containing exactly the text between the tags.
defs.lisp holds the definitions the theorems use. Do not modify these files.

<defs.lisp>
(in-package "ACL2")

(defun basel-series (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      0
    (+ (expt i -2)
       (basel-series (1+ i) n))))

(defun least-divisor-from (k n)
  (declare (xargs :measure (nfix (- (1+ n) k))))
  (if (and (integerp k) (integerp n) (< 1 k) (<= k n))
      (if (integerp (/ n k)) k (least-divisor-from (1+ k) n))
    nil))

(defun primep (n)
  (and (integerp n) (<= 2 n) (equal (least-divisor-from 2 n) n)))

(defun euler-zeta2-product (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      1
    (* (if (primep i) (/ (- 1 (expt i -2))) 1)
       (euler-zeta2-product (1+ i) n))))
</defs.lisp>

2. Write /work/solution.lisp. It must (include-book "defs") and then prove every theorem in <theorems>, each
as a `defthm` with exactly the name and statement given. You may add your own definitions and lemmas, and any
`:rule-classes` and hints.

<theorems>
(defthm euler-zeta2-product-lower
  (implies (and (integerp n) (<= 2 n))
           (<= (basel-series 1 n) (euler-zeta2-product 2 n))))

(defthm euler-zeta2-product-upper
  (implies (and (integerp n) (<= 2 n))
           (<= (euler-zeta2-product 2 n)
               (+ (basel-series 1 n) (/ (- n 1))))))

(defthm euler-product-close-to-basel-series
  (implies (and (posp n) (i-large n))
           (i-close (euler-zeta2-product 2 n) (basel-series 1 n))))
</theorems>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
Books are certified with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
/work/solution.lisp must certify with `cert.pl --acl2 acl2r`.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done.
When you are done, run `submit fw-euler-product`, which saves /work. Then print a short summary: the files you
wrote, and for each theorem whether it is proved.
