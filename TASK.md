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

(zsub preimage (f v) x (domain f) (in (apply f x) v))

(defun-sk preimages-open (f tp1 tp2)
  (forall v (implies (in v tp2) (in (preimage f v) tp1))))

(defun continuous (f tp1 tp2)
  (and (funp f) (equal (domain f) (union tp1))
       (subset (image f) (union tp2)) (preimages-open f tp1 tp2)))
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
(defthmz continuous-compose
  (implies (and (continuous f tp1 tp2) (continuous g tp2 tp3))
           (continuous (compose g f) tp1 tp3))
  :props (zfc prod2$prop domain$prop inverse$prop compose$prop preimage$prop))

(defthmz continuous-image-of-compact
  (implies (and (tpp tp1) (tpp tp2) (compact tp1) (continuous f tp1 tp2)
                (equal (image f) (union tp2)))
           (compact tp2))
  :props (zfc prod2$prop domain$prop inverse$prop preimage$prop))

(defthmz hausdorff-singleton-closed
  (implies (and (tpp tp) (hausdorff tp) (in x (union tp)))
           (closed (singleton x) tp))
  :props (zfc diff$prop))

(defthmz compact-subset-of-hausdorff-is-closed
  (implies (and (tpp tp) (hausdorff tp) (subset s (union tp))
                (compact (subspace s tp)))
           (closed s tp))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop subspace-fn$prop))
</theorems>

ACL2 (`acl2`) and ACL2(r) (`acl2r`) are installed at a development version newer than 8.7
(git commit 1d2b39a424 of 2026-11-12), with the community books. Books are certified with `cert.pl`
(add `--acl2 acl2r` for ACL2(r)).
/work/solution.lisp must certify with `cert.pl`.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done.
When you are done, run `submit zfc-t7`, which saves /work. Then print a short summary: the files you
wrote, and for each theorem whether it is proved.
