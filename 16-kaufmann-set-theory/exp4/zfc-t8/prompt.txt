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

(defun-sk closed-under-op (h op)
  (forall (x y) (implies (and (in x h) (in y h)) (in (apply2 op x y) h))))

(defun-sk closed-under-inv (h inv)
  (forall x (implies (in x h) (in (apply inv x) h))))

(defun subgroup-p (h s op e inv)
  (and (subset h s) (in e h) (closed-under-op h op) (closed-under-inv h inv)))

(defun-sk all-subgroups (hs s op e inv)
  (forall h (implies (in h hs) (subgroup-p h s op e inv))))

(defun-sk preserves-op (f s1 op1 op2)
  (forall (x y) (implies (and (in x s1) (in y s1))
                         (equal (apply f (apply2 op1 x y))
                                (apply2 op2 (apply f x) (apply f y))))))

(defun group-hom-p (f s1 op1 s2 op2)
  (and (funp f) (equal (domain f) s1) (subset (image f) s2)
       (preserves-op f s1 op1 op2)))

(zsub kernel (f s1 e2) x s1 (equal (apply f x) e2))

(defun-sk normal-in (h s op inv)
  (forall (g x) (implies (and (in g s) (in x h))
                         (in (apply2 op (apply2 op g x) (apply inv g)) h))))
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
(defthmz group-identity-unique
  (implies (and (groupp s op e inv) (in e2 s) (group-identity-p s op e2))
           (equal e2 e))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz group-inverse-unique
  (implies (and (groupp s op e inv) (in x s) (in y s)
                (equal (apply2 op x y) e))
           (equal y (apply inv x)))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz subgroup-is-group
  (implies (and (groupp s op e inv) (subgroup-p h s op e inv))
           (groupp h (restrict op (prod2 h h)) e (restrict inv h)))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz intersection-of-subgroups
  (implies (and (groupp s op e inv) (not (equal hs 0))
                (all-subgroups hs s op e inv))
           (subgroup-p (intersection hs) s op e inv))
  :props (zfc prod2$prop domain$prop inverse$prop intersection$prop))

(defthmz hom-preserves-identity-and-inverse
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (and (equal (apply f e1) e2)
                (implies (in x s1)
                         (equal (apply f (apply inv1 x))
                                (apply inv2 (apply f x))))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz kernel-is-normal-subgroup
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (and (subgroup-p (kernel f s1 e2) s1 op1 e1 inv1)
                (normal-in (kernel f s1 e2) s1 op1 inv1)))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

(defthmz image-is-subgroup
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (subgroup-p (image f) s2 op2 e2 inv2))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz injective-iff-trivial-kernel
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (iff (injective-funp f)
                (equal (kernel f s1 e2) (singleton e1))))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))
</theorems>

ACL2 (`acl2`) and ACL2(r) (`acl2r`) are installed at a development version newer than 8.7
(git commit 1d2b39a424 of 2026-11-12), with the community books. Books are certified with `cert.pl`
(add `--acl2 acl2r` for ACL2(r)).
/work/solution.lisp must certify with `cert.pl`.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done.
When you are done, run `submit zfc-t8`, which saves /work. Then print a short summary: the files you
wrote, and for each theorem whether it is proved.
