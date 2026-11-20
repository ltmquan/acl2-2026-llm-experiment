(in-package "ZF")

(include-book "defs")

;;; ------------------------------------------------------------
;;; Theorem 1: in-prod-family
;;; ------------------------------------------------------------

(defthmz in-cons-funp
  (implies (and (funp f) (in (cons x y) f))
           (and (in x (domain f))
                (equal (apply f x) y)))
  :props (zfc domain$prop)
  :hints (("Goal" :use ((:instance apply-intro-lemma (p (cons x y)))
                        (:instance in-car-domain (r f) (p (cons x y))))))
  :rule-classes nil)

(defthmz in-union-image-when-in-apply
  (implies (and (in x (domain fam))
                (in y (apply fam x)))
           (in y (union (image fam))))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal" :use ((:instance in-in-suff (a y) (x (image fam))
                                   (y (apply fam x)))
                        (:instance in-apply-image (r fam))))))

(defthmz in-image-when-choice-fn-p
  (implies (and (funp f)
                (equal (domain f) (domain fam))
                (choice-fn-p f fam)
                (in y (image f)))
           (in y (union (image fam))))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal"
           :in-theory (e/d (in-image-rewrite) (choice-fn-p-necc choice-fn-p
                                                in-union-image-when-in-apply))
           :use ((:instance in-cons-funp (x (apply (inverse f) y)))
                 (:instance choice-fn-p-necc (i (apply (inverse f) y)))
                 (:instance in-union-image-when-in-apply
                            (x (apply (inverse f) y)))))))

(defthmz subset-image-when-choice-fn-p
  (implies (and (funp f)
                (equal (domain f) (domain fam))
                (choice-fn-p f fam))
           (subset (image f) (union (image fam))))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal" :in-theory (disable choice-fn-p)
           :expand ((subset (image f) (union (image fam)))))))

(defthmz in-prod-family
  (implies (funp fam)
           (equal (in f (prod-family fam))
                  (and (funp f) (equal (domain f) (domain fam))
                       (choice-fn-p f fam))))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop)
  :hints (("Goal" :in-theory (enable prod-family$comprehension in-fun-space))))

;;; ------------------------------------------------------------
;;; A choice function for a family (Replacement + global choice)
;;; ------------------------------------------------------------

(zfn choice-of (fam) j z (domain fam) (in z (apply fam j)))

(defthmz subset-domain-choice-of
  (implies (nonempty-values fam)
           (subset (domain fam) (domain (choice-of fam))))
  :props (zfc domain$prop choice-of$prop)
  :hints (("Goal"
           :in-theory (disable nonempty-values-necc nonempty-values)
           :expand ((subset (domain fam) (domain (choice-of fam))))
           :use ((:instance nonempty-values-necc
                            (i (subset-witness (domain fam)
                                               (domain (choice-of fam)))))
                 (:instance choice-of$domain-2
                            (j (subset-witness (domain fam)
                                               (domain (choice-of fam))))
                            (z (min-in (apply fam
                                              (subset-witness (domain fam)
                                                              (domain (choice-of fam)))))))))))

(defthmz domain-choice-of
  (implies (nonempty-values fam)
           (equal (domain (choice-of fam)) (domain fam)))
  :props (zfc domain$prop choice-of$prop)
  :hints (("Goal"
           :in-theory (disable nonempty-values)
           :use ((:instance extensionality (x (domain (choice-of fam)))
                            (y (domain fam)))))))

(defthmz choice-fn-p-choice-of
  (implies (nonempty-values fam)
           (choice-fn-p (choice-of fam) fam))
  :props (zfc domain$prop choice-of$prop)
  :hints (("Goal"
           :in-theory (disable nonempty-values choice-of$chooses)
           :expand ((choice-fn-p (choice-of fam) fam))
           :use ((:instance choice-of$chooses
                            (j (choice-fn-p-witness (choice-of fam) fam))
                            (z (apply (choice-of fam)
                                      (choice-fn-p-witness (choice-of fam) fam))))))))

(defthmz choice-of-in-prod-family
  (implies (and (funp fam) (nonempty-values fam))
           (in (choice-of fam) (prod-family fam)))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop
              choice-of$prop)
  :hints (("Goal" :in-theory (disable nonempty-values))))

(defthmz prod-family-nonempty
  (implies (and (funp fam) (nonempty-values fam))
           (not (equal (prod-family fam) 0)))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop
              choice-of$prop)
  :hints (("Goal"
           :in-theory (theory 'minimal-theory)
           :use (choice-of-in-prod-family
                 (:instance 0-is-emptyset (a (choice-of fam)))))))

;;; ------------------------------------------------------------
;;; Theorem 2
;;; ------------------------------------------------------------

(defthmz prod-family-empty-when-empty-value
  (implies (and (funp fam) (not (nonempty-values fam)))
           (equal (prod-family fam) 0))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop)
  :hints (("Goal"
           :in-theory (disable choice-fn-p-necc min-in-1)
           :use ((:instance min-in-1 (z (prod-family fam)))
                 (:instance in-prod-family (f (min-in (prod-family fam))))
                 (:instance choice-fn-p-necc
                            (f (min-in (prod-family fam)))
                            (i (nonempty-values-witness fam)))))))

(defthmz prod-family-empty-iff
  (implies (funp fam)
           (iff (equal (prod-family fam) 0)
                (not (nonempty-values fam))))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop
              choice-of$prop)
  :hints (("Goal"
           :in-theory (disable prod-family-nonempty in-prod-family nonempty-values
                               prod-family-empty-when-empty-value)
           :use (prod-family-nonempty prod-family-empty-when-empty-value))))

;;; ------------------------------------------------------------
;;; Theorem 3: a choice function through a prescribed point
;;; ------------------------------------------------------------

(zfn pick-fn (fam i0 y0) j z (domain fam)
     (in z (if (equal j i0) (pair y0 y0) (apply fam j))))

(defthmz subset-domain-pick-fn
  (implies (and (nonempty-values fam)
                (in y0 (apply fam i0)))
           (subset (domain fam) (domain (pick-fn fam i0 y0))))
  :props (zfc domain$prop pick-fn$prop)
  :hints (("Goal"
           :in-theory (disable nonempty-values-necc nonempty-values)
           :expand ((subset (domain fam) (domain (pick-fn fam i0 y0))))
           :use ((:instance nonempty-values-necc
                            (i (subset-witness (domain fam)
                                               (domain (pick-fn fam i0 y0)))))
                 (:instance pick-fn$domain-2
                            (j (subset-witness (domain fam)
                                               (domain (pick-fn fam i0 y0))))
                            (z (if (equal (subset-witness (domain fam)
                                                          (domain (pick-fn fam i0 y0)))
                                          i0)
                                   y0
                                 (min-in (apply fam
                                                (subset-witness (domain fam)
                                                                (domain (pick-fn fam i0 y0))))))))))))

(defthmz domain-pick-fn
  (implies (and (nonempty-values fam)
                (in y0 (apply fam i0)))
           (equal (domain (pick-fn fam i0 y0)) (domain fam)))
  :props (zfc domain$prop pick-fn$prop)
  :hints (("Goal"
           :in-theory (disable nonempty-values)
           :use ((:instance extensionality (x (domain (pick-fn fam i0 y0)))
                            (y (domain fam)))))))

(defthmz apply-pick-fn
  (implies (in j (domain (pick-fn fam i0 y0)))
           (in (apply (pick-fn fam i0 y0) j)
               (if (equal j i0) (pair y0 y0) (apply fam j))))
  :props (zfc domain$prop pick-fn$prop)
  :hints (("Goal"
           :in-theory (disable pick-fn$chooses)
           :use ((:instance pick-fn$chooses
                            (z (apply (pick-fn fam i0 y0) j)))))))

(defthmz choice-fn-p-pick-fn
  (implies (and (nonempty-values fam)
                (in y0 (apply fam i0)))
           (choice-fn-p (pick-fn fam i0 y0) fam))
  :props (zfc domain$prop pick-fn$prop)
  :hints (("Goal"
           :in-theory (disable nonempty-values pick-fn$chooses apply-pick-fn equal-apply)
           :expand ((choice-fn-p (pick-fn fam i0 y0) fam))
           :use ((:instance apply-pick-fn
                            (j (choice-fn-p-witness (pick-fn fam i0 y0) fam)))))))

(defthmz pick-fn-at-i0
  (implies (and (nonempty-values fam)
                (in i0 (domain fam))
                (in y0 (apply fam i0)))
           (equal (apply (pick-fn fam i0 y0) i0) y0))
  :props (zfc domain$prop pick-fn$prop)
  :hints (("Goal"
           :in-theory (disable nonempty-values pick-fn$chooses apply-pick-fn equal-apply)
           :use ((:instance apply-pick-fn (j i0))))))

(defthmz projection-surjective
  (implies (and (funp fam) (nonempty-values fam)
                (in i (domain fam)) (in y (apply fam i)))
           (has-coordinate fam i y))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop
              pick-fn$prop)
  :hints (("Goal"
           :in-theory (disable nonempty-values)
           :use ((:instance has-coordinate-suff (f (pick-fn fam i y)))))))

;;; ------------------------------------------------------------
;;; Theorem 4: binary products
;;; ------------------------------------------------------------

(defun pair01 (u v)
  (pair (cons 0 u) (cons 1 v)))

(defthmz funp-pair-of-conses
  (implies (not (equal a1 a2))
           (funp (pair (cons a1 b1) (cons a2 b2))))
  :props (zfc)
  :hints (("Goal" :expand ((funp (pair (cons a1 b1) (cons a2 b2)))))))

(defthmz funp-pair01
  (funp (pair01 u v))
  :props (zfc))

(defthmz domain-pair01
  (equal (domain (pair01 u v)) (pair 0 1))
  :props (zfc domain$prop))

(defthmz apply-pair01
  (and (equal (apply (pair01 u v) 0) u)
       (equal (apply (pair01 u v) 1) v))
  :props (zfc domain$prop)
  :hints (("Goal"
           :in-theory (disable pair01 equal-apply)
           :use ((:instance in-cons-funp (f (pair01 u v)) (x 0) (y u))
                 (:instance in-cons-funp (f (pair01 u v)) (x 1) (y v))))
          (and stable-under-simplificationp
               '(:in-theory (enable pair01)))))

(in-theory (disable pair01 equal-apply))

(defthmz pair01-injective
  (implies (equal (pair01 u1 v1) (pair01 u2 v2))
           (and (equal u1 u2) (equal v1 v2)))
  :props (zfc domain$prop)
  :hints (("Goal" :in-theory (disable apply-pair01)
           :use ((:instance apply-pair01 (u u1) (v v1))
                 (:instance apply-pair01 (u u2) (v v2)))))
  :rule-classes nil)

(defthmz choice-fn-p-pair01
  (equal (choice-fn-p f (pair01 a b))
         (and (in (apply f 0) a) (in (apply f 1) b)))
  :props (zfc domain$prop)
  :hints (("Goal"
           :in-theory (disable choice-fn-p-necc)
           :expand ((choice-fn-p f (pair01 a b)))
           :use ((:instance choice-fn-p-necc (fam (pair01 a b)) (i 0))
                 (:instance choice-fn-p-necc (fam (pair01 a b)) (i 1))))))

(defthmz in-prod-family-pair01
  (equal (in f (prod-family (pair01 a b)))
         (and (funp f)
              (equal (domain f) (pair 0 1))
              (in (apply f 0) a)
              (in (apply f 1) b)))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop))

(defthmz pair01-of-applies
  (implies (and (funp f) (equal (domain f) (pair 0 1)))
           (equal (pair01 (apply f 0) (apply f 1)) f))
  :props (zfc domain$prop)
  :hints (("Goal"
           :in-theory (disable equal-apply)
           :expand ((fn-equal (pair01 (apply f 0) (apply f 1)) f)
                    (fn-equal f (pair01 (apply f 0) (apply f 1))))
           :use ((:instance fn-equal-implies-equal
                            (f (pair01 (apply f 0) (apply f 1)))
                            (g f))))))

;;; The map p |-> pair01(car p, cdr p) from (prod2 a b)

(zfn to-fam (a b) p g (prod2 a b)
     (in g (pair (pair01 (car p) (cdr p)) (pair01 (car p) (cdr p)))))

(defthmz subset-domain-to-fam
  (subset (prod2 a b) (domain (to-fam a b)))
  :props (zfc domain$prop to-fam$prop)
  :hints (("Goal"
           :expand ((subset (prod2 a b) (domain (to-fam a b))))
           :use ((:instance to-fam$domain-2
                            (p (subset-witness (prod2 a b) (domain (to-fam a b))))
                            (g (pair01 (car (subset-witness (prod2 a b)
                                                            (domain (to-fam a b))))
                                       (cdr (subset-witness (prod2 a b)
                                                            (domain (to-fam a b)))))))))))

(defthmz domain-to-fam
  (equal (domain (to-fam a b)) (prod2 a b))
  :props (zfc domain$prop to-fam$prop)
  :hints (("Goal"
           :use ((:instance extensionality (x (domain (to-fam a b)))
                            (y (prod2 a b)))))))

(defthmz apply-to-fam
  (implies (in p (prod2 a b))
           (equal (apply (to-fam a b) p)
                  (pair01 (car p) (cdr p))))
  :props (zfc domain$prop to-fam$prop)
  :hints (("Goal"
           :in-theory (disable to-fam$chooses equal-apply)
           :use ((:instance to-fam$chooses
                            (g (apply (to-fam a b) p)))))))

;;; Injectivity

(defun-sk injective-p (f)
  (forall (x1 x2)
    (implies (and (in x1 (domain f))
                  (in x2 (domain f))
                  (equal (apply f x1) (apply f x2)))
             (equal x1 x2))))

(defthmz funp-inverse-when-injective-p
  (implies (and (funp f) (injective-p f))
           (funp (inverse f)))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal"
           :expand ((funp (inverse f)))
           :in-theory (disable injective-p-necc injective-p)
           :use ((:instance in-cons-funp
                            (x (cdr (mv-nth 0 (funp-witness (inverse f)))))
                            (y (car (mv-nth 0 (funp-witness (inverse f))))))
                 (:instance in-cons-funp
                            (x (cdr (mv-nth 1 (funp-witness (inverse f)))))
                            (y (car (mv-nth 1 (funp-witness (inverse f))))))
                 (:instance injective-p-necc
                            (x1 (cdr (mv-nth 0 (funp-witness (inverse f)))))
                            (x2 (cdr (mv-nth 1 (funp-witness (inverse f))))))))))

(defthmz injective-p-to-fam
  (injective-p (to-fam a b))
  :props (zfc prod2$prop domain$prop to-fam$prop)
  :hints (("Goal"
           :expand ((injective-p (to-fam a b)))
           :use ((:instance pair01-injective
                            (u1 (car (mv-nth 0 (injective-p-witness (to-fam a b)))))
                            (v1 (cdr (mv-nth 0 (injective-p-witness (to-fam a b)))))
                            (u2 (car (mv-nth 1 (injective-p-witness (to-fam a b)))))
                            (v2 (cdr (mv-nth 1 (injective-p-witness (to-fam a b))))))))))

(defthmz injective-funp-to-fam
  (injective-funp (to-fam a b))
  :props (zfc prod2$prop domain$prop inverse$prop to-fam$prop)
  :hints (("Goal" :in-theory (disable injective-p))))

;;; Image

(defthmz apply-to-fam-in-prod-family
  (implies (in p (prod2 a b))
           (in (apply (to-fam a b) p) (prod-family (pair01 a b))))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop
              to-fam$prop))

(defthmz in-image-to-fam-1
  (implies (in y (image (to-fam a b)))
           (in y (prod-family (pair01 a b))))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop
              to-fam$prop)
  :hints (("Goal"
           :in-theory (e/d (in-image-rewrite)
                           (apply-to-fam apply-to-fam-in-prod-family
                                         in-prod-family-pair01))
           :use ((:instance in-cons-funp
                            (f (to-fam a b))
                            (x (apply (inverse (to-fam a b)) y)))
                 (:instance apply-to-fam-in-prod-family
                            (p (apply (inverse (to-fam a b)) y)))))))

(defthmz in-image-to-fam-2
  (implies (in y (prod-family (pair01 a b)))
           (in y (image (to-fam a b))))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop
              to-fam$prop)
  :hints (("Goal"
           :in-theory (disable in-apply-image)
           :use ((:instance in-apply-image
                            (r (to-fam a b))
                            (x (cons (apply y 0) (apply y 1))))))))

(defthmz image-to-fam
  (equal (image (to-fam a b)) (prod-family (pair01 a b)))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop
              to-fam$prop)
  :hints (("Goal"
           :in-theory (disable in-image-to-fam-1 in-image-to-fam-2)
           :expand ((subset (image (to-fam a b)) (prod-family (pair01 a b)))
                    (subset (prod-family (pair01 a b)) (image (to-fam a b))))
           :use ((:instance extensionality (x (image (to-fam a b)))
                            (y (prod-family (pair01 a b))))
                 (:instance in-image-to-fam-1
                            (y (subset-witness (image (to-fam a b))
                                               (prod-family (pair01 a b)))))
                 (:instance in-image-to-fam-2
                            (y (subset-witness (prod-family (pair01 a b))
                                               (image (to-fam a b)))))))))

(defthmz injective-funp-inverse-to-fam
  (injective-funp (inverse (to-fam a b)))
  :props (zfc prod2$prop domain$prop inverse$prop to-fam$prop)
  :hints (("Goal" :use injective-funp-to-fam
           :in-theory (disable injective-funp-to-fam))))

(defthmz prod-family-pair01-bijection
  (exists-bijection (prod-family (pair01 a b)) (prod2 a b))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop
              to-fam$prop)
  :hints (("Goal"
           :in-theory (disable injective-funp)
           :use ((:instance exists-bijection-suff
                            (fn (inverse (to-fam a b)))
                            (s1 (prod-family (pair01 a b)))
                            (s2 (prod2 a b)))))))

(defthmz prod-family-binary
  (exists-bijection (prod-family (pair (cons 0 a) (cons 1 b)))
                    (prod2 a b))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop
              to-fam$prop)
  :hints (("Goal"
           :in-theory '(pair01)
           :use prod-family-pair01-bijection)))
