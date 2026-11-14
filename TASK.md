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

(defun-sk upward-closed (u s)
  (forall (x y) (implies (and (in x u) (subset x y) (subset y s)) (in y u))))

(defun-sk int2-closed (u)
  (forall (x y) (implies (and (in x u) (in y u)) (in (int2 x y) u))))

(defun filter-on (u s)
  (and (subset u (powerset s)) (in s u) (not (in 0 u))
       (upward-closed u s) (int2-closed u)))

(defun-sk ultra-p (u s)
  (forall x (implies (subset x s) (or (in x u) (in (diff s x) u)))))

(defun ultrafilter-on (u s)
  (and (filter-on u s) (ultra-p u s)))

(zsub principal-filter (a s) x (powerset s) (in a x))

(defun-sk principal-p (u s)
  (exists a (and (in a s) (equal u (principal-filter a s)))))

(defun-sk maximal-filter-p (u s)
  (forall v (implies (and (filter-on v s) (subset u v)) (equal u v))))

(defun-sk exists-nonprincipal-ultrafilter (s)
  (exists u (and (ultrafilter-on u s) (not (principal-p u s)))))
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

The last theorem, after the ;; optional marker, is optional: try it after the others.

<theorems>
(defthmz principal-filter-is-ultrafilter
  (implies (in a s) (ultrafilter-on (principal-filter a s) s))
  :props (zfc diff$prop principal-filter$prop))

(defthmz ultra-iff-maximal
  (implies (filter-on u s) (iff (ultra-p u s) (maximal-filter-p u s)))
  :props (zfc diff$prop))

(defthmz ultrafilter-prime
  (implies (and (ultrafilter-on u s) (subset x s) (subset y s)
                (in (union2 x y) u))
           (or (in x u) (in y u)))
  :props (zfc diff$prop))

(defthmz ultrafilter-with-finite-member-is-principal
  (implies (and (ultrafilter-on u s) (in x u) (finite x))
           (principal-p u s))
  :props (zfc diff$prop principal-filter$prop))

(defthmz ultrafilter-on-finite-set-is-principal
  (implies (and (ultrafilter-on u s) (finite s))
           (principal-p u s))
  :props (zfc diff$prop principal-filter$prop))

;; optional
(defthmz nonprincipal-ultrafilter-exists
  (exists-nonprincipal-ultrafilter (omega))
  :props (zfc diff$prop principal-filter$prop))
</theorems>

ACL2 (`acl2`) and ACL2(r) (`acl2r`) are installed at a development version newer than 8.7
(git commit 1d2b39a424 of 2026-11-12), with the community books. Books are certified with `cert.pl`
(add `--acl2 acl2r` for ACL2(r)).
/work/solution.lisp must certify with `cert.pl`.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done.
When you are done, run `submit zfc-t3`, which saves /work. Then print a short summary: the files you
wrote, and for each theorem whether it is proved.
