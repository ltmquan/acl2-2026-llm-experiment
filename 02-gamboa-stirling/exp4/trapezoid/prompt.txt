Prove the theorems below in ACL2(r): the error bound of the composite trapezoid rule for a function `tf` with
a bounded second derivative on an interval, for every partition.

1. Create /work/defs.lisp containing exactly the text between the tags.
defs.lisp holds the definitions the theorems use. Do not modify these files.

<defs.lisp>
(in-package "ACL2")

(include-book "nonstd/integrals/integrable-functions" :dir :system)
(include-book "nonstd/integrals/make-partition" :dir :system)
(include-book "nonstd/nsa/intervals" :dir :system)
(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "nonstd/nsa/nsa" :dir :system))

(encapsulate
  (((tf *) => *) ((tf1 *) => *) ((tf2 *) => *)
   ((tf-domain) => *) ((tf2-bound) => *))
  (local (defun tf (x) (declare (ignore x)) 0))
  (local (defun tf1 (x) (declare (ignore x)) 0))
  (local (defun tf2 (x) (declare (ignore x)) 0))
  (local (defun tf-domain () (interval 0 1)))
  (local (defun tf2-bound () 0))
  (defthm intervalp-tf-domain (interval-p (tf-domain))
    :rule-classes (:type-prescription :rewrite))
  (defthm tf-domain-real
    (implies (inside-interval-p x (tf-domain)) (realp x))
    :rule-classes (:forward-chaining))
  (defthm tf-domain-non-trivial
    (or (null (interval-left-endpoint (tf-domain)))
        (null (interval-right-endpoint (tf-domain)))
        (< (interval-left-endpoint (tf-domain))
           (interval-right-endpoint (tf-domain))))
    :rule-classes nil)
  (defthm tf-real  (realp (tf x))  :rule-classes (:rewrite :type-prescription))
  (defthm tf1-real (realp (tf1 x)) :rule-classes (:rewrite :type-prescription))
  (defthm tf2-real (realp (tf2 x)) :rule-classes (:rewrite :type-prescription))
  (defthm tf1-is-derivative-of-tf
    (implies (and (standardp x)
                  (inside-interval-p x (tf-domain))
                  (inside-interval-p x1 (tf-domain))
                  (i-close x x1) (not (= x x1)))
             (i-close (/ (- (tf x) (tf x1)) (- x x1)) (tf1 x))))
  (defthm tf2-is-derivative-of-tf1
    (implies (and (standardp x)
                  (inside-interval-p x (tf-domain))
                  (inside-interval-p x1 (tf-domain))
                  (i-close x x1) (not (= x x1)))
             (i-close (/ (- (tf1 x) (tf1 x1)) (- x x1)) (tf2 x))))
  (defthm tf2-bound-type (and (realp (tf2-bound)) (<= 0 (tf2-bound)))
    :rule-classes (:rewrite (:type-prescription :corollary (realp (tf2-bound)))))
  (defthm tf2-bounded
    (implies (inside-interval-p x (tf-domain))
             (<= (abs (tf2 x)) (tf2-bound)))))

(defun map-tf (p) (if (consp p) (cons (tf (car p)) (map-tf (cdr p))) nil))
(defun riemann-tf (p) (dotprod (deltas p) (map-tf (cdr p))))

(defun trapezoid-tf (p)
  (if (and (consp p) (consp (cdr p)))
      (+ (* (- (cadr p) (car p)) (/ (+ (tf (car p)) (tf (cadr p))) 2))
         (trapezoid-tf (cdr p)))
    0))
(defun sum-cubed-deltas (p)
  (if (and (consp p) (consp (cdr p)))
      (+ (expt (- (cadr p) (car p)) 3) (sum-cubed-deltas (cdr p)))
    0))
</defs.lisp>

2. Write /work/solution.lisp. It must (include-book "defs") and then prove every theorem in <theorems>, each
as a `defthm` with exactly the name and statement given. You may add your own definitions and lemmas, and any
`:rule-classes` and hints.

3. Admit these definitions in /work/solution.lisp, after including defs and before the theorems, with exactly
these names, formals and bodies. You may add declarations and hints to them, and your own events before them.

<definitions-to-admit>
(defun-std strict-int-tf (a b)
  (if (and (realp a) (realp b)
           (inside-interval-p a (tf-domain)) (inside-interval-p b (tf-domain))
           (< a b))
      (standard-part (riemann-tf (make-small-partition a b)))
    0))

(defun int-tf (a b) (if (<= a b) (strict-int-tf a b) (- (strict-int-tf b a))))
</definitions-to-admit>

<theorems>
(defthm trapezoid-rule-error
  (implies (and (partitionp p)
                (inside-interval-p (car p) (tf-domain))
                (inside-interval-p (car (last p)) (tf-domain)))
           (<= (abs (- (int-tf (car p) (car (last p))) (trapezoid-tf p)))
               (* (/ (tf2-bound) 12) (sum-cubed-deltas p)))))

(defthm trapezoid-rule-error-mesh
  (implies (and (partitionp p)
                (inside-interval-p (car p) (tf-domain))
                (inside-interval-p (car (last p)) (tf-domain)))
           (<= (abs (- (int-tf (car p) (car (last p))) (trapezoid-tf p)))
               (* (/ (tf2-bound) 12) (- (car (last p)) (car p)) (expt (mesh p) 2)))))
</theorems>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
Books are certified with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
/work/solution.lisp must certify with `cert.pl --acl2 acl2r`.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done.
When you are done, run `submit fw-trapezoid`, which saves /work. Then print a short summary: the files you
wrote, and for each theorem whether it is proved.
