Prove the theorems below in ACL2(r): the value of the integral of cos(x − mγ)·cos(x − nγ) over [0, 2π],
with γ = 2π/3 and integers m, n, as a limit of Riemann sums and as a definite integral.

1. Create /work/defs.lisp containing exactly the text between the tags.
defs.lisp holds the definitions the theorems use. Do not modify these files.

<defs.lisp>
(in-package "ACL2")

(include-book "nonstd/nsa/trig" :dir :system)
(include-book "nonstd/integrals/integrable-functions" :dir :system)
(include-book "nonstd/integrals/make-partition" :dir :system)

(defun winding-gamma () (* 2/3 (acl2-pi)))

(defun inductance-integrand (x m n)
  (* (acl2-cosine (- x (* m (winding-gamma))))
     (acl2-cosine (- x (* n (winding-gamma))))))

(defun map-inductance-integrand (p m n)
  (if (consp p)
      (cons (inductance-integrand (car p) m n)
            (map-inductance-integrand (cdr p) m n))
    nil))

(defun riemann-inductance-integrand (p m n)
  (dotprod (deltas p) (map-inductance-integrand (cdr p) m n)))
</defs.lisp>

2. Write /work/solution.lisp. It must (include-book "defs") and then prove every theorem in <theorems>, each
as a `defthm` with exactly the name and statement given. You may add your own definitions and lemmas, and any
`:rule-classes` and hints.

3. Admit these definitions in /work/solution.lisp, after including defs and before the theorems, with exactly
these names, formals and bodies. You may add declarations and hints to them, and your own events before them.

<definitions-to-admit>
(defun-std int-inductance-integrand (a b m n)
  (if (and (realp a) (realp b) (< a b) (realp m) (realp n))
      (standard-part (riemann-inductance-integrand (make-small-partition a b) m n))
    0))
</definitions-to-admit>

<theorems>
(defthm inductance-integral-riemann-form
  (implies (and (integerp m) (integerp n)
                (partitionp p)
                (equal (car p) 0)
                (equal (car (last p)) (* 2 (acl2-pi)))
                (i-small (mesh p)))
           (i-close (riemann-inductance-integrand p m n)
                    (* (acl2-pi) (acl2-cosine (* (- m n) (winding-gamma)))))))

(defthm inductance-integral-value
  (implies (and (integerp m) (integerp n))
           (equal (int-inductance-integrand 0 (* 2 (acl2-pi)) m n)
                  (* (acl2-pi) (acl2-cosine (* (- m n) (winding-gamma)))))))
</theorems>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
Books are certified with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
/work/solution.lisp must certify with `cert.pl --acl2 acl2r`.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done.
When you are done, run `submit fw-inductance`, which saves /work. Then print a short summary: the files you
wrote, and for each theorem whether it is proved.
