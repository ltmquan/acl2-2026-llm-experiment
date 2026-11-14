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

(defun-sk injects-into (a b)
  (exists f (and (injective-funp f) (equal (domain f) a) (subset (image f) b))))

(defun-sk eqnum-to-nat (s)
  (exists n (and (natp n) (exists-bijection n s))))
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
(defthmz eqnum-reflexive (exists-bijection s s))

(defthmz eqnum-symmetric
  (implies (exists-bijection a b) (exists-bijection b a))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz eqnum-transitive
  (implies (and (exists-bijection a b) (exists-bijection b c))
           (exists-bijection a c))
  :props (zfc prod2$prop domain$prop inverse$prop compose$prop))

(defthmz injects-both-ways-implies-eqnum
  (implies (and (injects-into a b) (injects-into b a))
           (exists-bijection a b))
  :props (sbt-prop))

(defthmz set-injects-into-powerset (injects-into s (powerset s)))

(defthmz powerset-does-not-inject (not (injects-into (powerset s) s))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz pigeonhole
  (implies (natp n) (not (injects-into (+ 1 n) n)))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz eqnum-naturals-equal
  (implies (and (natp m) (natp n) (exists-bijection m n)) (equal m n))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz omega-not-finite (not (finite (omega))))

(defthmz finite-iff-eqnum-to-nat (iff (finite s) (eqnum-to-nat s))
  :props (zfc prod2$prop domain$prop inverse$prop))
</theorems>

ACL2 (`acl2`) and ACL2(r) (`acl2r`) are installed at a development version newer than 8.7
(git commit 1d2b39a424 of 2026-11-12), with the community books. Books are certified with `cert.pl`
(add `--acl2 acl2r` for ACL2(r)).
/work/solution.lisp must certify with `cert.pl`.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done.
When you are done, run `submit zfc-t4`, which saves /work. Then print a short summary: the files you
wrote, and for each theorem whether it is proved.
