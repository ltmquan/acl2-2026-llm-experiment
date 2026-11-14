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

(defun-sk choice-fn-p (f fam)
  (forall i (implies (in i (domain fam)) (in (apply f i) (apply fam i)))))

(zsub prod-family (fam) f (fun-space (domain fam) (union (image fam)))
      (choice-fn-p f fam))

(defun-sk nonempty-values (fam)
  (forall i (implies (in i (domain fam)) (not (equal (apply fam i) 0)))))

(defun-sk has-coordinate (fam i y)
  (exists f (and (in f (prod-family fam)) (equal (apply f i) y))))
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
(defthmz in-prod-family
  (implies (funp fam)
           (equal (in f (prod-family fam))
                  (and (funp f) (equal (domain f) (domain fam))
                       (choice-fn-p f fam))))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop))

(defthmz prod-family-empty-iff
  (implies (funp fam)
           (iff (equal (prod-family fam) 0)
                (not (nonempty-values fam))))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop))

(defthmz projection-surjective
  (implies (and (funp fam) (nonempty-values fam)
                (in i (domain fam)) (in y (apply fam i)))
           (has-coordinate fam i y))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop))

(defthmz prod-family-binary
  (exists-bijection (prod-family (pair (cons 0 a) (cons 1 b)))
                    (prod2 a b))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop))
</theorems>

ACL2 (`acl2`) and ACL2(r) (`acl2r`) are installed at a development version newer than 8.7
(git commit 1d2b39a424 of 2026-11-12), with the community books. Books are certified with `cert.pl`
(add `--acl2 acl2r` for ACL2(r)).
/work/solution.lisp must certify with `cert.pl`.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done.
When you are done, run `submit zfc-t2`, which saves /work. Then print a short summary: the files you
wrote, and for each theorem whether it is proved.
