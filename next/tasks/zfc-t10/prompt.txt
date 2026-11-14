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

(defun-sk dr-valued (d x)
  (forall (a b) (implies (and (in a x) (in b x)) (drp (apply d (cons a b))))))

(defun-sk metric-axioms (d x)
  (forall (a b c)
    (implies (and (in a x) (in b x) (in c x))
             (and (subset (r2dr 0) (apply d (cons a b)))
                  (iff (equal (apply d (cons a b)) (r2dr 0)) (equal a b))
                  (equal (apply d (cons a b)) (apply d (cons b a)))
                  (subset (apply d (cons a c))
                          (dr+ (apply d (cons a b)) (apply d (cons b c))))))))

(defun metric-p (d x)
  (and (funp d) (equal (domain d) (prod2 x x)) (dr-valued d x)
       (metric-axioms d x)))

(defun-sk ball-inside (u a eps d x)
  (forall b (implies (and (in b x) (not (in eps (apply d (cons a b)))))
                     (in b u))))

(defun-sk has-ball (u a d x)
  (exists eps (and (rationalp eps) (< 0 eps) (ball-inside u a eps d x))))

(defun-sk metric-open-p (u d x)
  (forall a (implies (in a u) (has-ball u a d x))))

(zsub metric-topology (d x) u (powerset x) (metric-open-p u d x))

(zsub q-dist () p (prod2 (prod2 (rationals) (rationals)) (powerset (rationals)))
      (equal (cdr p) (r2dr (abs (- (car (car p)) (cdr (car p)))))))
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
(defthmz metric-topology-is-topology
  (implies (metric-p d x)
           (and (tpp (metric-topology d x))
                (equal (union (metric-topology d x)) x)))
  :props (zfc prod2$prop diff$prop metric-topology$prop))

(defthmz metric-topology-is-hausdorff
  (implies (metric-p d x) (hausdorff (metric-topology d x)))
  :props (dr-sum-prop diff$prop metric-topology$prop))

(defthmz rationals-metric
  (metric-p (q-dist) (rationals))
  :props (dr-sum-prop q-dist$prop))
</theorems>

ACL2 (`acl2`) and ACL2(r) (`acl2r`) are installed at a development version newer than 8.7
(git commit 1d2b39a424 of 2026-11-12), with the community books. Books are certified with `cert.pl`
(add `--acl2 acl2r` for ACL2(r)).
/work/solution.lisp must certify with `cert.pl`.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done.
When you are done, run `submit zfc-t10`, which saves /work. Then print a short summary: the files you
wrote, and for each theorem whether it is proved.
