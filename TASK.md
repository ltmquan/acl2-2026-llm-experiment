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

(defun-sk homogeneous (h c k)
  (forall (m n) (implies (and (in m h) (in n h) (< m n))
                         (equal (apply c (cons m n)) k))))

(defun-sk exists-infinite-homogeneous (c)
  (exists (h k) (and (subset h (omega)) (not (finite h)) (homogeneous h c k))))
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
(defthmz infinite-ramsey-2
  (implies (and (funp c) (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) 2))
           (exists-infinite-homogeneous c))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz infinite-ramsey
  (implies (and (natp r) (funp c) (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) r))
           (exists-infinite-homogeneous c))
  :props (zfc prod2$prop domain$prop inverse$prop))
</theorems>

ACL2 (`acl2`) and ACL2(r) (`acl2r`) are installed at a development version newer than 8.7
(git commit 1d2b39a424 of 2026-11-12), with the community books. Books are certified with `cert.pl`
(add `--acl2 acl2r` for ACL2(r)).
/work/solution.lisp must certify with `cert.pl`.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done.
When you are done, run `submit zfc-t6`, which saves /work. Then print a short summary: the files you
wrote, and for each theorem whether it is proved.
