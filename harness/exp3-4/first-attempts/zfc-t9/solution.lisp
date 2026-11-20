;; Solution for zfc-t9.
;;
;; RATIONALS-FORM-FIELD is proved below.
;;
;; COMPLEX-CONSTRUCTION-IS-FIELD and COMPLEX-I-SQUARED are NOT provable: they
;; are false.  FIELDP only demands LEFT distributivity, x*(y+z) = x*y + x*z,
;; and the multiplicative identity/commutativity axioms only constrain products
;; of nonzero elements.  Hence 0*y is only required to be additive in y and
;; need not be 0.  The rationals with the usual +, -, / and the "weird"
;; multiplication  w(x,y) = (if x = 0 then y else x*y)  form a FIELDP in which
;; -1 is not a square (theorem FIELDP-W and MINUS-ONE-NOT-SQUARE-W below), yet
;;   * (0,1)*(0,1) = (-1, 0*1 + 1*0) = (-1, 1)  differs from  -(1,0) = (-1,0)
;;     (theorem COMPLEX-I-SQUARED-COUNTEREXAMPLE), and
;;   * (1,0)*(0,1) = (1*0 - 0*1, 1*1 + 0*0) = (-1, 1) differs from (0,1), so
;;     (1,0) is not an identity of the complex construction and it is not a
;;     FIELDP (theorem COMPLEX-CONSTRUCTION-NOT-FIELD-COUNTEREXAMPLE).
;; These counterexample theorems are proved in this book.

(in-package "ZF")

(include-book "defs")

(defun q-add2 (x) (+ (car x) (cdr x)))
(defun q-mul2 (x) (* (car x) (cdr x)))
(zify q+ q-add2 :dom (prod2 (rationals) (rationals)) :ran (rationals)
      :props (v$prop rationals$prop))
(zify q* q-mul2 :dom (prod2 (rationals) (rationals)) :ran (rationals)
      :props (v$prop rationals$prop))
(zify q- unary-- :dom (rationals) :ran (rationals)
      :props (v$prop rationals$prop))
(zify q/ unary-/ :dom (nonzeros (rationals) 0) :ran (nonzeros (rationals) 0)
      :props (v$prop rationals$prop diff$prop))
(defun nzq-mul2 (x) (* (car x) (cdr x)))
(zify q*nz nzq-mul2 :dom (prod2 (nonzeros (rationals) 0) (nonzeros (rationals) 0))
      :ran (nonzeros (rationals) 0)
      :props (v$prop rationals$prop diff$prop))

(local (include-book "arithmetic/top" :dir :system))
(defthmz abelian-group-p-q+
  (abelian-group-p (rationals) (q+) 0 (q-))
  :hints (("Goal" :in-theory (e/d (subset in-image-rewrite) (equal-apply))))
  :props (zfc v$prop rationals$prop prod2$prop domain$prop inverse$prop
              q-$prop q+$prop))

(defthmz abelian-group-p-q*nz
  (abelian-group-p (nonzeros (rationals) 0) (q*nz) 1 (q/))
  :hints (("Goal" :in-theory (e/d (subset in-image-rewrite) (equal-apply))))
  :props (zfc v$prop rationals$prop prod2$prop domain$prop inverse$prop diff$prop
              q*nz$prop q/$prop))
(defthmz restrict-q*-is-q*nz-1
  (subset (restrict (q*) (prod2 (nonzeros (rationals) 0) (nonzeros (rationals) 0)))
          (q*nz))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc v$prop rationals$prop prod2$prop domain$prop inverse$prop diff$prop
              restrict$prop q*$prop q*nz$prop))

(defthmz restrict-q*-is-q*nz-2
  (subset (q*nz)
          (restrict (q*) (prod2 (nonzeros (rationals) 0) (nonzeros (rationals) 0))))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc v$prop rationals$prop prod2$prop domain$prop inverse$prop diff$prop
              restrict$prop q*$prop q*nz$prop))

(defthmz restrict-q*-is-q*nz
  (equal (restrict (q*) (prod2 (nonzeros (rationals) 0) (nonzeros (rationals) 0)))
         (q*nz))
  :hints (("Goal" :use ((:instance extensionality-rewrite
                                   (x (restrict (q*) (prod2 (nonzeros (rationals) 0) (nonzeros (rationals) 0))))
                                   (y (q*nz))))
           :in-theory (disable nonzeros)))
  :props (zfc v$prop rationals$prop prod2$prop domain$prop inverse$prop diff$prop
              restrict$prop q*$prop q*nz$prop))

(defthmz image-q*-subset
  (subset (image (q*)) (rationals))
  :hints (("Goal" :in-theory (e/d (subset in-image-rewrite) (equal-apply))))
  :props (zfc v$prop rationals$prop prod2$prop domain$prop inverse$prop q*$prop))

(defthmz distributive-p-q
  (distributive-p (rationals) (q+) (q*))
  :props (zfc v$prop rationals$prop prod2$prop domain$prop inverse$prop q*$prop q+$prop))

(defthmz fieldp-q
  (fieldp (rationals) (q+) (q*) 0 1 (q-) (q/))
  :hints (("Goal" :in-theory (disable nonzeros abelian-group-p distributive-p)))
  :props (zfc v$prop rationals$prop prod2$prop domain$prop inverse$prop diff$prop
              restrict$prop q*$prop q*nz$prop q+$prop q-$prop q/$prop))

(defthm square-not-minus-one
  (implies (rationalp x) (not (equal (* x x) -1)))
  :hints (("Goal" :nonlinearp t)))

(defthmz minus-one-not-square-q
  (minus-one-not-square (rationals) (q*) (q-) 1)
  :hints (("Goal" :in-theory (disable equal-apply)))
  :props (zfc v$prop rationals$prop prod2$prop domain$prop inverse$prop q*$prop q-$prop))

(defthmz rational-ops-standard-q
  (rational-ops-standard (q+) (q*))
  :hints (("Goal" :in-theory (disable equal-apply)))
  :props (zfc v$prop rationals$prop prod2$prop domain$prop inverse$prop q*$prop q+$prop))

(defthmz rationals-form-field (rationals-field-witness)
  :hints (("Goal" :use ((:instance rationals-field-witness-suff
                                   (add (q+)) (mul (q*)) (neg (q-)) (recip (q/))))
           :in-theory (disable rationals-field-witness-suff fieldp minus-one-not-square
                               rational-ops-standard)))
  :props (zfc rationals$prop v$prop prod2$prop domain$prop inverse$prop
              diff$prop restrict$prop q*$prop q*nz$prop q+$prop q-$prop q/$prop))

;;; Counterexamples to COMPLEX-I-SQUARED and COMPLEX-CONSTRUCTION-IS-FIELD

(defun w-mul2 (x) (if (equal (car x) 0) (cdr x) (* (car x) (cdr x))))
(zify w* w-mul2 :dom (prod2 (rationals) (rationals)) :ran (rationals)
      :props (v$prop rationals$prop))

(defthmz restrict-w*-is-q*nz-1
  (subset (restrict (w*) (prod2 (nonzeros (rationals) 0) (nonzeros (rationals) 0)))
          (q*nz))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc v$prop rationals$prop prod2$prop domain$prop inverse$prop diff$prop
              restrict$prop w*$prop q*nz$prop))

(defthmz restrict-w*-is-q*nz-2
  (subset (q*nz)
          (restrict (w*) (prod2 (nonzeros (rationals) 0) (nonzeros (rationals) 0))))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc v$prop rationals$prop prod2$prop domain$prop inverse$prop diff$prop
              restrict$prop w*$prop q*nz$prop))

(defthmz restrict-w*-is-q*nz
  (equal (restrict (w*) (prod2 (nonzeros (rationals) 0) (nonzeros (rationals) 0)))
         (q*nz))
  :hints (("Goal" :use ((:instance extensionality-rewrite
                                   (x (restrict (w*) (prod2 (nonzeros (rationals) 0) (nonzeros (rationals) 0))))
                                   (y (q*nz))))
           :in-theory (disable nonzeros)))
  :props (zfc v$prop rationals$prop prod2$prop domain$prop inverse$prop diff$prop
              restrict$prop w*$prop q*nz$prop))

(defthmz image-w*-subset
  (subset (image (w*)) (rationals))
  :hints (("Goal" :in-theory (e/d (subset in-image-rewrite) (equal-apply))))
  :props (zfc v$prop rationals$prop prod2$prop domain$prop inverse$prop w*$prop))

(defthmz distributive-p-w
  (distributive-p (rationals) (q+) (w*))
  :props (zfc v$prop rationals$prop prod2$prop domain$prop inverse$prop w*$prop q+$prop))

(defthmz fieldp-w
  (fieldp (rationals) (q+) (w*) 0 1 (q-) (q/))
  :hints (("Goal" :in-theory (disable nonzeros abelian-group-p distributive-p)))
  :props (zfc v$prop rationals$prop prod2$prop domain$prop inverse$prop diff$prop
              restrict$prop w*$prop q*nz$prop q+$prop q-$prop q/$prop))

(defthmz minus-one-not-square-w
  (minus-one-not-square (rationals) (w*) (q-) 1)
  :hints (("Goal" :in-theory (disable equal-apply)))
  :props (zfc v$prop rationals$prop prod2$prop domain$prop inverse$prop w*$prop q-$prop))

; generic apply facts for c-mul / c-neg / restrict, without funp
(defthmz apply-c-mul-value
  (let ((v (cons (apply2 add (apply2 mul (car x) (car y))
                         (apply neg (apply2 mul (cdr x) (cdr y))))
                 (apply2 add (apply2 mul (car x) (cdr y))
                         (apply2 mul (cdr x) (car y))))))
    (implies (and (in x (prod2 s s)) (in y (prod2 s s)) (in v (prod2 s s)))
             (equal (apply (c-mul s add mul neg) (cons x y)) v)))
  :hints (("Goal" :use ((:instance apply-rewrite (r (c-mul s add mul neg)) (x (cons x y))
                                   (y (cons (apply2 add (apply2 mul (car x) (car y))
                         (apply neg (apply2 mul (cdr x) (cdr y))))
                 (apply2 add (apply2 mul (car x) (cdr y))
                         (apply2 mul (cdr x) (car y)))))))
           :in-theory (disable apply-rewrite)))
  :props (zfc prod2$prop domain$prop inverse$prop c-mul$prop))
(defthmz apply-c-neg-value
  (let ((v (cons (apply neg (car x)) (apply neg (cdr x)))))
    (implies (and (in x (prod2 s s)) (in v (prod2 s s)))
             (equal (apply (c-neg s neg) x) v)))
  :hints (("Goal" :use ((:instance apply-rewrite (r (c-neg s neg)) (x x)
                                   (y (cons (apply neg (car x)) (apply neg (cdr x))))))
           :in-theory (disable apply-rewrite)))
  :props (zfc prod2$prop domain$prop inverse$prop c-neg$prop))

(defthmz apply-restrict-c-mul-value
  (let ((v (cons (apply2 add (apply2 mul (car x) (car y))
                         (apply neg (apply2 mul (cdr x) (cdr y))))
                 (apply2 add (apply2 mul (car x) (cdr y))
                         (apply2 mul (cdr x) (car y))))))
    (implies (and (in x (prod2 s s)) (in y (prod2 s s)) (in v (prod2 s s))
                  (in (cons x y) d))
             (equal (apply (restrict (c-mul s add mul neg) d) (cons x y)) v)))
  :hints (("Goal" :use ((:instance apply-rewrite (r (restrict (c-mul s add mul neg) d)) (x (cons x y))
                                   (y (cons (apply2 add (apply2 mul (car x) (car y))
                         (apply neg (apply2 mul (cdr x) (cdr y))))
                 (apply2 add (apply2 mul (car x) (cdr y))
                         (apply2 mul (cdr x) (car y)))))))
           :in-theory (disable apply-rewrite)))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop c-mul$prop))

(in-theory (disable apply2))

(defthmz complex-i-squared-counterexample
  (and (fieldp (rationals) (q+) (w*) 0 1 (q-) (q/))
       (not (equal (apply2 (c-mul (rationals) (q+) (w*) (q-)) (cons 0 1) (cons 0 1))
                   (apply (c-neg (rationals) (q-)) (cons 1 0)))))
  :hints (("Goal" :in-theory (e/d (apply2) (fieldp equal-apply))))
  :props (zfc v$prop rationals$prop prod2$prop domain$prop inverse$prop diff$prop
              restrict$prop w*$prop q*nz$prop q+$prop q-$prop q/$prop
              c-mul$prop c-neg$prop))

(defthmz complex-construction-not-field-counterexample
  (and (fieldp (rationals) (q+) (w*) 0 1 (q-) (q/))
       (minus-one-not-square (rationals) (w*) (q-) 1)
       (not (fieldp (prod2 (rationals) (rationals))
                    (c-add (rationals) (q+))
                    (c-mul (rationals) (q+) (w*) (q-))
                    (cons 0 0) (cons 1 0) (c-neg (rationals) (q-))
                    (c-recip (rationals) (q+) (w*) 0 (q-) (q/)))))
  :hints (("Goal" :in-theory (e/d (apply2) (equal-apply group-identity-p-necc
                                            distributive-p abelian-p group-associative-p
                                            group-inverse-p minus-one-not-square))
           :use ((:instance group-identity-p-necc
                            (x (cons 0 1))
                            (s (nonzeros (prod2 (rationals) (rationals)) (cons 0 0)))
                            (op (restrict (c-mul (rationals) (q+) (w*) (q-))
                                          (prod2 (nonzeros (prod2 (rationals) (rationals)) (cons 0 0))
                                                 (nonzeros (prod2 (rationals) (rationals)) (cons 0 0)))))
                            (e (cons 1 0))))))
  :props (zfc v$prop rationals$prop prod2$prop domain$prop inverse$prop diff$prop
              restrict$prop w*$prop q*nz$prop q+$prop q-$prop q/$prop
              c-add$prop c-mul$prop c-neg$prop c-recip$prop))
