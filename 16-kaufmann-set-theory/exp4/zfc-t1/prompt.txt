Prove the theorems below in ACL2(zfc), the set theory of the community books `projects/set-theory` (ACL2
with `projects/set-theory/top` included; see `:doc zfc` and the books themselves).

1. Create /work/defs.lisp and /work/cert.acl2 containing exactly the text between the tags.
defs.lisp holds the definitions the theorems use. Do not modify these files.

<defs.lisp>
(in-package "ZF")

(include-book "projects/set-theory/top" :dir :system)
(include-book "projects/set-theory/topology/compact" :dir :system)
(include-book "projects/set-theory/topology/normal" :dir :system)
(include-book "projects/set-theory/topology/subspace" :dir :system)
(include-book "projects/set-theory/algebra/groups" :dir :system)
(include-book "projects/set-theory/reals/sum" :dir :system)

(defun-sk refl-on (r s)
  (forall x (implies (in x s) (in (cons x x) r))))

(defun-sk sym-rel (r)
  (forall (x y) (implies (in (cons x y) r) (in (cons y x) r))))

(defun-sk trans-rel (r)
  (forall (x y z) (implies (and (in (cons x y) r) (in (cons y z) r))
                           (in (cons x z) r))))

(defun equivalence-on (r s)
  (and (subset r (prod2 s s)) (refl-on r s) (sym-rel r) (trans-rel r)))

(zsub eqv-class (a r s) y s (in (cons a y) r))

(defun-sk is-eqv-class (c r s)
  (exists a (and (in a s) (equal c (eqv-class a r s)))))

(zsub quotient (r s) c (powerset s) (is-eqv-class c r s))

(defun-sk pairwise-disjoint (p)
  (forall (c d) (implies (and (in c p) (in d p) (not (equal c d)))
                         (equal (int2 c d) 0))))

(defun partition-p (p s)
  (and (equal (union p) s) (not (in 0 p)) (pairwise-disjoint p)))

(defun-sk same-block (x y p)
  (exists c (and (in c p) (in x c) (in y c))))

(zsub partition-rel (p s) q (prod2 s s) (same-block (car q) (cdr q) p))

(defun-sk maps-to-classes (f r s)
  (forall a (implies (in a s) (equal (apply f a) (eqv-class a r s)))))

(defun-sk exists-quotient-map (r s)
  (exists f (and (funp f) (equal (domain f) s)
                 (equal (image f) (quotient r s))
                 (maps-to-classes f r s))))
</defs.lisp>

<cert.acl2>
(include-book "projects/set-theory/portcullis" :dir :system)
; cert_param: (non-acl2r)
</cert.acl2>

2. Write /work/solution.lisp. It must (include-book "defs") and then prove every theorem in <theorems>, each
as a `defthmz` with exactly the name and statement given. You may add your own definitions and lemmas, and any
`:rule-classes` and hints. Each theorem is a `defthmz`: you may add hypothesis
functions (keys of `zfc-table`, such as the `$prop` functions of your own `zsub` and `zfn` events) to its
`:props` list. Do not use `table` events on `zfc-table` directly, or `defthme`'s `:skip` option.

<theorems>
(defthmz eqv-class-equal
  (implies (and (equivalence-on r s) (in a s) (in b s))
           (equal (equal (eqv-class a r s) (eqv-class b r s))
                  (in (cons a b) r)))
  :props (zfc prod2$prop eqv-class$prop))

(defthmz quotient-is-partition
  (implies (equivalence-on r s) (partition-p (quotient r s) s))
  :props (zfc prod2$prop diff$prop eqv-class$prop quotient$prop))

(defthmz partition-rel-is-equivalence
  (implies (partition-p p s) (equivalence-on (partition-rel p s) s))
  :props (zfc prod2$prop diff$prop partition-rel$prop))

(defthmz quotient-of-partition-rel
  (implies (partition-p p s) (equal (quotient (partition-rel p s) s) p))
  :props (zfc prod2$prop diff$prop eqv-class$prop quotient$prop partition-rel$prop))

(defthmz partition-rel-of-quotient
  (implies (equivalence-on r s) (equal (partition-rel (quotient r s) s) r))
  :props (zfc prod2$prop diff$prop eqv-class$prop quotient$prop partition-rel$prop))

(defthmz quotient-map-exists
  (implies (equivalence-on r s) (exists-quotient-map r s))
  :props (zfc prod2$prop domain$prop inverse$prop eqv-class$prop quotient$prop))
</theorems>

ACL2 (`acl2`) and ACL2(r) (`acl2r`) are installed at a development version newer than 8.7
(git commit 1d2b39a424 of 2026-11-12), with the community books. Books are certified with `cert.pl`
(add `--acl2 acl2r` for ACL2(r)).
/work/solution.lisp must certify with `cert.pl`.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done.
When you are done, run `submit zfc-t1`, which saves /work. Then print a short summary: the files you
wrote, and for each theorem whether it is proved.
