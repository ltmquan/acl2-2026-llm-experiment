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

(defun-sk choice-fn-p (f fam)
  (forall i (implies (in i (domain fam)) (in (apply f i) (apply fam i)))))

(zsub prod-family (fam) f (fun-space (domain fam) (union (image fam)))
      (choice-fn-p f fam))

(defun-sk nonempty-values (fam)
  (forall i (implies (in i (domain fam)) (not (equal (apply fam i) 0)))))

(defun-sk has-coordinate (fam i y)
  (exists f (and (in f (prod-family fam)) (equal (apply f i) y))))

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

(zsub agree-set (f g i) x i (equal (apply f x) (apply g x)))

(zsub ultra-rel (fam u) q (prod2 (prod-family fam) (prod-family fam))
      (in (agree-set (car q) (cdr q) (domain fam)) u))

(defun ultraproduct (fam u) (quotient (ultra-rel fam u) (prod-family fam)))
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
(defthmz reduced-product-relation-is-equivalence
  (implies (and (funp fam) (filter-on u (domain fam)))
           (equivalence-on (ultra-rel fam u) (prod-family fam)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop))

(defthmz principal-ultraproduct
  (implies (and (funp fam) (nonempty-values fam) (in i0 (domain fam)))
           (exists-bijection
            (ultraproduct fam (principal-filter i0 (domain fam)))
            (apply fam i0)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop
              principal-filter$prop eqv-class$prop quotient$prop))
</theorems>

ACL2 (`acl2`) and ACL2(r) (`acl2r`) are installed at a development version newer than 8.7
(git commit 1d2b39a424 of 2026-11-12), with the community books. Books are certified with `cert.pl`
(add `--acl2 acl2r` for ACL2(r)).
/work/solution.lisp must certify with `cert.pl`.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done.
When you are done, run `submit zfc-t11`, which saves /work. Then print a short summary: the files you
wrote, and for each theorem whether it is proved.
