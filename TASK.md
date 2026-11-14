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

(defun-sk distributive-p (s add mul)
  (forall (x y z)
    (implies (and (in x s) (in y s) (in z s))
             (equal (apply2 mul x (apply2 add y z))
                    (apply2 add (apply2 mul x y) (apply2 mul x z))))))

(defun nonzeros (s zero) (diff s (singleton zero)))

(defun fieldp (s add mul zero one neg recip)
  (and (funp add) (funp mul) (funp neg) (funp recip)
       (abelian-group-p s add zero neg)
       (not (equal zero one))
       (equal (domain mul) (prod2 s s))
       (subset (image mul) s)
       (abelian-p s mul)
       (abelian-group-p (nonzeros s zero)
                        (restrict mul (prod2 (nonzeros s zero)
                                             (nonzeros s zero)))
                        one recip)
       (distributive-p s add mul)))

(defun-sk minus-one-not-square (s mul neg one)
  (forall x (implies (in x s)
                     (not (equal (apply2 mul x x) (apply neg one))))))

(defun cx-a (p) (car (car (car p))))

(defun cx-b (p) (cdr (car (car p))))

(defun cx-c (p) (car (cdr (car p))))

(defun cx-d (p) (cdr (cdr (car p))))

(zsub c-add (s add) p (prod2 (prod2 (prod2 s s) (prod2 s s)) (prod2 s s))
      (equal (cdr p) (cons (apply2 add (cx-a p) (cx-c p))
                           (apply2 add (cx-b p) (cx-d p)))))

(zsub c-mul (s add mul neg) p
      (prod2 (prod2 (prod2 s s) (prod2 s s)) (prod2 s s))
      (equal (cdr p)
             (cons (apply2 add (apply2 mul (cx-a p) (cx-c p))
                           (apply neg (apply2 mul (cx-b p) (cx-d p))))
                   (apply2 add (apply2 mul (cx-a p) (cx-d p))
                           (apply2 mul (cx-b p) (cx-c p))))))

(zsub c-neg (s neg) p (prod2 (prod2 s s) (prod2 s s))
      (equal (cdr p) (cons (apply neg (car (car p)))
                           (apply neg (cdr (car p))))))

(defun c-norm2 (u add mul)
  (apply2 add (apply2 mul (car u) (car u)) (apply2 mul (cdr u) (cdr u))))

(zsub c-recip (s add mul zero neg recip) p
      (prod2 (diff (prod2 s s) (singleton (cons zero zero))) (prod2 s s))
      (equal (cdr p)
             (cons (apply2 mul (car (car p))
                           (apply recip (c-norm2 (car p) add mul)))
                   (apply2 mul (apply neg (cdr (car p)))
                           (apply recip (c-norm2 (car p) add mul))))))

(defun-sk rational-ops-standard (add mul)
  (forall (x y) (implies (and (rationalp x) (rationalp y))
                         (and (equal (apply2 add x y) (+ x y))
                              (equal (apply2 mul x y) (* x y))))))

(defun-sk rationals-field-witness ()
  (exists (add mul neg recip)
    (and (fieldp (rationals) add mul 0 1 neg recip)
         (minus-one-not-square (rationals) mul neg 1)
         (rational-ops-standard add mul))))
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
(defthmz complex-construction-is-field
  (implies (and (fieldp s add mul zero one neg recip)
                (minus-one-not-square s mul neg one))
           (fieldp (prod2 s s) (c-add s add) (c-mul s add mul neg)
                   (cons zero zero) (cons one zero) (c-neg s neg)
                   (c-recip s add mul zero neg recip)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop restrict$prop
              c-add$prop c-mul$prop c-neg$prop c-recip$prop))

(defthmz complex-i-squared
  (implies (fieldp s add mul zero one neg recip)
           (equal (apply2 (c-mul s add mul neg) (cons zero one) (cons zero one))
                  (apply (c-neg s neg) (cons one zero))))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop restrict$prop
              c-mul$prop c-neg$prop))

(defthmz rationals-form-field (rationals-field-witness)
  :props (zfc rationals$prop v$prop prod2$prop domain$prop inverse$prop))
</theorems>

ACL2 (`acl2`) and ACL2(r) (`acl2r`) are installed at a development version newer than 8.7
(git commit 1d2b39a424 of 2026-11-12), with the community books. Books are certified with `cert.pl`
(add `--acl2 acl2r` for ACL2(r)).
/work/solution.lisp must certify with `cert.pl`.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done.
When you are done, run `submit zfc-t9-r2`, which saves /work. Then print a short summary: the files you
wrote, and for each theorem whether it is proved.
