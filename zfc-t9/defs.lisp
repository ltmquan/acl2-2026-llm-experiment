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
  (and (abelian-group-p s add zero neg)
       (not (equal zero one))
       (equal (domain mul) (prod2 s s))
       (subset (image mul) s)
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
