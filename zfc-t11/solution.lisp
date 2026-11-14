(in-package "ZF")

(include-book "defs")

;;; ------------------------------------------------------------------
;;; Theorem 1: the reduced-product relation is an equivalence relation
;;; ------------------------------------------------------------------

(defthmz agree-set-same
  (equal (agree-set f f i) i)
  :props (zfc agree-set$prop)
  :hints (("Goal" :in-theory (enable extensionality-rewrite subset))))

(defthmz agree-set-commutative
  (equal (agree-set f g i) (agree-set g f i))
  :props (zfc agree-set$prop)
  :hints (("Goal" :in-theory (enable extensionality-rewrite subset))))

(defthmz subset-agree-set
  (subset (agree-set f g i) i)
  :props (zfc agree-set$prop)
  :hints (("Goal" :in-theory (enable subset))))

(defthmz subset-int2-agree-set
  (subset (int2 (agree-set f g i) (agree-set g h i))
          (agree-set f h i))
  :props (zfc diff$prop agree-set$prop)
  :hints (("Goal" :in-theory (enable subset))))

(defthmz filter-agree-set-trans
  (implies (and (filter-on u i)
                (in (agree-set f g i) u)
                (in (agree-set g h i) u))
           (in (agree-set f h i) u))
  :props (zfc diff$prop agree-set$prop)
  :hints (("Goal"
           :in-theory (disable upward-closed-necc int2-closed-necc)
           :use ((:instance int2-closed-necc
                            (x (agree-set f g i))
                            (y (agree-set g h i)))
                 (:instance upward-closed-necc
                            (s i)
                            (x (int2 (agree-set f g i) (agree-set g h i)))
                            (y (agree-set f h i)))))))

(defthmz in-ultra-rel-cons
  (equal (in (cons x y) (ultra-rel fam u))
         (and (in x (prod-family fam))
              (in y (prod-family fam))
              (in (agree-set x y (domain fam)) u)))
  :props (zfc prod2$prop ultra-rel$prop)
  :hints (("Goal" :in-theory (disable prod-family$comprehension))))

(defthmz ultra-rel-subset-prod2
  (subset (ultra-rel fam u) (prod2 (prod-family fam) (prod-family fam)))
  :props (zfc prod2$prop ultra-rel$prop)
  :hints (("Goal" :in-theory (e/d (subset) (prod-family$comprehension)))))

(defthmz reduced-product-relation-is-equivalence
  (implies (and (funp fam) (filter-on u (domain fam)))
           (equivalence-on (ultra-rel fam u) (prod-family fam)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop)
  :hints (("Goal" :in-theory (e/d (refl-on sym-rel trans-rel)
                                  (filter-on)))
          ("Goal'" :in-theory (enable filter-on))))

;;; ------------------------------------------------------------------
;;; Theorem 2: ultraproduct by a principal ultrafilter
;;; ------------------------------------------------------------------

;;; A choice function in the product with prescribed value y0 at i0.

(in-theory (disable nonempty-values))

(zfn sel (fam i0 y0) i y (domain fam)
     (if (equal i i0) (equal y y0) (in y (apply fam i))))

(defthmz sel-value
  (implies (in i (domain (sel fam i0 y0)))
           (and (implies (equal i i0)
                         (equal (apply (sel fam i0 y0) i) y0))
                (implies (not (equal i i0))
                         (in (apply (sel fam i0 y0) i) (apply fam i)))))
  :props (zfc sel$prop)
  :hints (("Goal" :use ((:instance sel$chooses
                                   (y (apply (sel fam i0 y0) i)))))))

(in-theory (disable sel$chooses))

(defthmz in-domain-sel
  (implies (and (nonempty-values fam)
                (in i (domain fam)))
           (in i (domain (sel fam i0 y0))))
  :props (zfc sel$prop)
  :hints (("Goal"
           :in-theory (disable nonempty-values-necc sel$domain-2)
           :use ((:instance nonempty-values-necc)
                 (:instance min-in-1 (z (apply fam i)))
                 (:instance sel$domain-2
                            (y (if (equal i i0) y0 (min-in (apply fam i)))))))))

(defthmz domain-sel
  (implies (nonempty-values fam)
           (equal (domain (sel fam i0 y0)) (domain fam)))
  :props (zfc domain$prop sel$prop)
  :hints (("Goal"
           :use ((:instance extensionality
                            (x (domain (sel fam i0 y0)))
                            (y (domain fam)))
                 (:instance in-domain-sel
                            (i (subset-witness (domain fam)
                                               (domain (sel fam i0 y0))))))
           :in-theory (enable subset-criterion))))

(defthmz sel-value-in-fam
  (implies (and (nonempty-values fam)
                (in i (domain fam))
                (in y0 (apply fam i0)))
           (in (apply (sel fam i0 y0) i) (apply fam i)))
  :props (zfc domain$prop sel$prop)
  :hints (("Goal" :use ((:instance sel-value))
           :in-theory (disable sel-value equal-apply))))

(defthmz apply-sel-i0
  (implies (and (nonempty-values fam)
                (in i0 (domain fam)))
           (equal (apply (sel fam i0 y0) i0) y0))
  :props (zfc domain$prop sel$prop)
  :hints (("Goal" :use ((:instance sel-value (i i0)))
           :in-theory (disable sel-value equal-apply))))

(defthmz in-image-sel
  (implies (and (nonempty-values fam)
                (in y0 (apply fam i0))
                (in y (image (sel fam i0 y0))))
           (in y (union (image fam))))
  :props (zfc domain$prop prod2$prop inverse$prop sel$prop)
  :hints (("Goal"
           :in-theory (disable sel-value-in-fam in-image-necc)
           :use ((:instance in-image-necc (f (sel fam i0 y0)) (x y))
                 (:instance in-car-domain
                            (p (cons (apply (inverse (sel fam i0 y0)) y) y))
                            (r (sel fam i0 y0)))
                 (:instance apply-intro
                            (f (sel fam i0 y0))
                            (p (cons (apply (inverse (sel fam i0 y0)) y) y)))
                 (:instance sel-value-in-fam
                            (i (apply (inverse (sel fam i0 y0)) y)))
                 (:instance in-apply-image
                            (r fam)
                            (x (apply (inverse (sel fam i0 y0)) y)))
                 (:instance in-in-suff
                            (a y)
                            (x (image fam))
                            (y (apply fam (apply (inverse (sel fam i0 y0)) y))))))))

(defthmz sel-in-prod-family
  (implies (and (nonempty-values fam)
                (in y0 (apply fam i0)))
           (in (sel fam i0 y0) (prod-family fam)))
  :props (zfc domain$prop prod2$prop inverse$prop fun-space$prop
              prod-family$prop sel$prop)
  :hints (("Goal" :in-theory (enable choice-fn-p subset))))

;;; Choice functions apply into the family.

(defthmz prod-family-apply
  (implies (and (in a (prod-family fam))
                (in i (domain fam)))
           (in (apply a i) (apply fam i)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop
              principal-filter$prop eqv-class$prop quotient$prop)
  :hints (("Goal" :in-theory (disable choice-fn-p-necc)
           :use ((:instance choice-fn-p-necc (f a))))))

;;; The principal-filter relation compares values at i0.

(defthmz in-principal-agree-set
  (implies (in i0 (domain fam))
           (equal (in (agree-set f g (domain fam))
                      (principal-filter i0 (domain fam)))
                  (equal (apply f i0) (apply g i0))))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop
              principal-filter$prop eqv-class$prop quotient$prop))

(defthmz in-eqv-class-principal
  (implies (and (in i0 (domain fam))
                (in a (prod-family fam)))
           (equal (in x (eqv-class a
                                   (ultra-rel fam (principal-filter i0 (domain fam)))
                                   (prod-family fam)))
                  (and (in x (prod-family fam))
                       (equal (apply a i0) (apply x i0)))))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop
              principal-filter$prop eqv-class$prop quotient$prop)
  :hints (("Goal" :in-theory (disable prod-family$comprehension))))

(defthmz eqv-class-principal-equal
  (implies (and (in i0 (domain fam))
                (in a (prod-family fam))
                (in b (prod-family fam))
                (equal (apply a i0) (apply b i0)))
           (equal (eqv-class a
                             (ultra-rel fam (principal-filter i0 (domain fam)))
                             (prod-family fam))
                  (eqv-class b
                             (ultra-rel fam (principal-filter i0 (domain fam)))
                             (prod-family fam))))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop
              principal-filter$prop eqv-class$prop quotient$prop)
  :hints (("Goal"
           :use ((:instance extensionality
                            (x (eqv-class a
                                          (ultra-rel fam (principal-filter i0 (domain fam)))
                                          (prod-family fam)))
                            (y (eqv-class b
                                          (ultra-rel fam (principal-filter i0 (domain fam)))
                                          (prod-family fam)))))
           :in-theory (e/d (subset)
                           (prod-family$comprehension equal-apply))))
  :rule-classes nil)

(defthmz subset-eqv-class
  (subset (eqv-class a r s) s)
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop
              principal-filter$prop eqv-class$prop quotient$prop)
  :hints (("Goal" :in-theory (enable subset))))

;;; Facts about members of the quotient.

(defthmz in-quotient-principal
  (implies (in c (quotient r s))
           (and (in (is-eqv-class-witness c r s) s)
                (equal (in x c)
                       (in x (eqv-class (is-eqv-class-witness c r s) r s)))))
  :hints (("Goal" :in-theory (disable eqv-class$comprehension)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop
              principal-filter$prop eqv-class$prop quotient$prop)
  :rule-classes nil)

(defthmz principal-class-value
  (implies (and (in i0 (domain fam))
                (in c (quotient (ultra-rel fam (principal-filter i0 (domain fam)))
                                (prod-family fam)))
                (in x c))
           (equal (apply x i0)
                  (apply (is-eqv-class-witness
                          c
                          (ultra-rel fam (principal-filter i0 (domain fam)))
                          (prod-family fam))
                         i0)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop
              principal-filter$prop eqv-class$prop quotient$prop)
  :hints (("Goal"
           :use ((:instance in-quotient-principal
                            (r (ultra-rel fam (principal-filter i0 (domain fam))))
                            (s (prod-family fam)))
                 (:instance in-eqv-class-principal
                            (a (is-eqv-class-witness
                                c
                                (ultra-rel fam (principal-filter i0 (domain fam)))
                                (prod-family fam)))))
           :in-theory (disable in-eqv-class-principal prod-family$comprehension
                               quotient$comprehension is-eqv-class))))

(defthmz principal-class-nonempty
  (implies (and (in i0 (domain fam))
                (in c (quotient (ultra-rel fam (principal-filter i0 (domain fam)))
                                (prod-family fam))))
           (in (is-eqv-class-witness
                c
                (ultra-rel fam (principal-filter i0 (domain fam)))
                (prod-family fam))
               c))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop
              principal-filter$prop eqv-class$prop quotient$prop)
  :hints (("Goal"
           :use ((:instance in-quotient-principal
                            (r (ultra-rel fam (principal-filter i0 (domain fam))))
                            (s (prod-family fam))
                            (x (is-eqv-class-witness
                                c
                                (ultra-rel fam (principal-filter i0 (domain fam)))
                                (prod-family fam))))
                 (:instance in-eqv-class-principal
                            (a (is-eqv-class-witness
                                c
                                (ultra-rel fam (principal-filter i0 (domain fam)))
                                (prod-family fam)))
                            (x (is-eqv-class-witness
                                c
                                (ultra-rel fam (principal-filter i0 (domain fam)))
                                (prod-family fam)))))
           :in-theory (disable in-eqv-class-principal prod-family$comprehension
                               quotient$comprehension is-eqv-class))))

(defthmz quotient-class-of-witness
  (implies (in c (quotient r s))
           (equal (eqv-class (is-eqv-class-witness c r s) r s) c))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop
              principal-filter$prop eqv-class$prop quotient$prop)
  :hints (("Goal"
           :use ((:instance extensionality
                            (x (eqv-class (is-eqv-class-witness c r s) r s))
                            (y c))
                 (:instance in-quotient-principal
                            (x (subset-witness
                                (eqv-class (is-eqv-class-witness c r s) r s)
                                c)))
                 (:instance in-quotient-principal
                            (x (subset-witness
                                c
                                (eqv-class (is-eqv-class-witness c r s) r s)))))
           :in-theory (e/d (subset)
                           (eqv-class$comprehension quotient$comprehension
                                                    is-eqv-class))))
  :rule-classes nil)

;;; A general criterion for injectivity.

(defun-sk inj-on-domain (f)
  (forall (x y)
          (implies (and (in x (domain f))
                        (in y (domain f))
                        (equal (apply f x) (apply f y)))
                   (equal x y))))

(defthmz inj-on-domain-pairs
  (implies (and (funp f)
                (inj-on-domain f)
                (in (cons x1 y) f)
                (in (cons x2 y) f))
           (equal x1 x2))
  :props (zfc domain$prop)
  :hints (("Goal"
           :in-theory (disable inj-on-domain-necc inj-on-domain equal-apply)
           :use ((:instance inj-on-domain-necc (x x1) (y x2))
                 (:instance apply-intro-lemma (p (cons x1 y)))
                 (:instance apply-intro-lemma (p (cons x2 y)))
                 (:instance in-car-domain (p (cons x1 y)) (r f))
                 (:instance in-car-domain (p (cons x2 y)) (r f)))))
  :rule-classes nil)

(defthmz funp-inverse-from-inj
  (implies (and (funp f)
                (inj-on-domain f))
           (funp (inverse f)))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal"
           :expand ((funp (inverse f)))
           :in-theory (disable inj-on-domain)
           :use ((:instance inj-on-domain-pairs
                            (x1 (cdr (mv-nth 0 (funp-witness (inverse f)))))
                            (x2 (cdr (mv-nth 1 (funp-witness (inverse f)))))
                            (y (car (mv-nth 0 (funp-witness (inverse f)))))))))
  :rule-classes nil)

;;; The map from the ultraproduct to (apply fam i0).

(zfn qmap (fam i0) c y
     (quotient (ultra-rel fam (principal-filter i0 (domain fam)))
               (prod-family fam))
     (equal (apply (min-in c) i0) y))

(defthmz qmap-apply
  (implies (in c (domain (qmap fam i0)))
           (equal (apply (qmap fam i0) c)
                  (apply (min-in c) i0)))
  :props (zfc qmap$prop)
  :hints (("Goal" :use ((:instance qmap$chooses
                                   (y (apply (qmap fam i0) c))))
           :in-theory (disable qmap$chooses equal-apply))))

(in-theory (disable qmap$chooses))

(defthmz domain-qmap
  (equal (domain (qmap fam i0))
         (quotient (ultra-rel fam (principal-filter i0 (domain fam)))
                   (prod-family fam)))
  :props (zfc domain$prop qmap$prop)
  :hints (("Goal"
           :use ((:instance extensionality
                            (x (domain (qmap fam i0)))
                            (y (quotient (ultra-rel fam (principal-filter i0 (domain fam)))
                                         (prod-family fam))))
                 (:instance qmap$domain-2
                            (c (subset-witness
                                (quotient (ultra-rel fam (principal-filter i0 (domain fam)))
                                          (prod-family fam))
                                (domain (qmap fam i0))))
                            (y (apply (min-in
                                       (subset-witness
                                        (quotient (ultra-rel fam (principal-filter i0 (domain fam)))
                                                  (prod-family fam))
                                        (domain (qmap fam i0))))
                                      i0))))
           :in-theory (e/d (subset-criterion)
                           (qmap$domain-2 quotient$comprehension)))))

(defthmz qmap-value
  (implies (and (in i0 (domain fam))
                (in c (quotient (ultra-rel fam (principal-filter i0 (domain fam)))
                                (prod-family fam))))
           (equal (apply (qmap fam i0) c)
                  (apply (is-eqv-class-witness
                          c
                          (ultra-rel fam (principal-filter i0 (domain fam)))
                          (prod-family fam))
                         i0)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop
              principal-filter$prop eqv-class$prop quotient$prop qmap$prop)
  :hints (("Goal"
           :use ((:instance principal-class-nonempty)
                 (:instance min-in-1 (z c))
                 (:instance principal-class-value (x (min-in c))))
           :in-theory (disable principal-class-nonempty principal-class-value
                               min-in-1 quotient$comprehension
                               prod-family$comprehension))))

(defthmz in-image-qmap-1
  (implies (and (in i0 (domain fam))
                (in y (image (qmap fam i0))))
           (in y (apply fam i0)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop
              principal-filter$prop eqv-class$prop quotient$prop
              sel$prop qmap$prop)
  :hints (("Goal"
           :use ((:instance in-image-necc (f (qmap fam i0)) (x y))
                 (:instance in-car-domain
                            (p (cons (apply (inverse (qmap fam i0)) y) y))
                            (r (qmap fam i0)))
                 (:instance apply-intro-lemma
                            (f (qmap fam i0))
                            (p (cons (apply (inverse (qmap fam i0)) y) y)))
                 (:instance qmap-value (c (apply (inverse (qmap fam i0)) y)))
                 (:instance in-quotient-principal
                            (c (apply (inverse (qmap fam i0)) y))
                            (r (ultra-rel fam (principal-filter i0 (domain fam))))
                            (s (prod-family fam)))
                 (:instance prod-family-apply
                            (a (is-eqv-class-witness (apply (inverse (qmap fam i0)) y) (ultra-rel fam (principal-filter i0 (domain fam))) (prod-family fam)))
                            (i i0)))
           :in-theory (disable in-image-necc in-car-domain qmap-value
                               prod-family-apply
                               equal-apply quotient$comprehension
                               prod-family$comprehension in-cons-apply
                               qmap-apply))))

(defthmz in-image-qmap-2
  (implies (and (nonempty-values fam)
                (in i0 (domain fam))
                (in y (apply fam i0)))
           (in y (image (qmap fam i0))))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop
              principal-filter$prop eqv-class$prop quotient$prop
              sel$prop qmap$prop)
  :hints (("Goal"
           :use ((:instance sel-in-prod-family (y0 y))
                 (:instance apply-sel-i0 (y0 y))
                 (:instance quotient$comprehension
                            (c (eqv-class (sel fam i0 y) (ultra-rel fam (principal-filter i0 (domain fam))) (prod-family fam)))
                            (r (ultra-rel fam (principal-filter i0 (domain fam))))
                            (s (prod-family fam)))
                 (:instance is-eqv-class-suff
                            (a (sel fam i0 y))
                            (c (eqv-class (sel fam i0 y) (ultra-rel fam (principal-filter i0 (domain fam))) (prod-family fam)))
                            (r (ultra-rel fam (principal-filter i0 (domain fam))))
                            (s (prod-family fam)))
                 (:instance subset-eqv-class
                            (a (sel fam i0 y))
                            (r (ultra-rel fam (principal-filter i0 (domain fam))))
                            (s (prod-family fam)))
                 (:instance in-eqv-class-principal
                            (a (sel fam i0 y))
                            (x (sel fam i0 y)))
                 (:instance principal-class-value
                            (c (eqv-class (sel fam i0 y) (ultra-rel fam (principal-filter i0 (domain fam))) (prod-family fam)))
                            (x (sel fam i0 y)))
                 (:instance qmap-value
                            (c (eqv-class (sel fam i0 y) (ultra-rel fam (principal-filter i0 (domain fam))) (prod-family fam))))
                 (:instance in-cons-apply
                            (f (qmap fam i0))
                            (x (eqv-class (sel fam i0 y) (ultra-rel fam (principal-filter i0 (domain fam))) (prod-family fam))))
                 (:instance in-image-suff
                            (r (qmap fam i0))
                            (p (cons (eqv-class (sel fam i0 y) (ultra-rel fam (principal-filter i0 (domain fam))) (prod-family fam))
                                     y))))
           :in-theory (disable sel-in-prod-family apply-sel-i0
                               quotient$comprehension is-eqv-class-suff
                               subset-eqv-class in-eqv-class-principal
                               principal-class-value qmap-value
                               in-cons-apply in-image-suff equal-apply
                               prod-family$comprehension
                               eqv-class$comprehension qmap-apply
                               is-eqv-class))))

(defthmz image-qmap
  (implies (and (nonempty-values fam)
                (in i0 (domain fam)))
           (equal (image (qmap fam i0)) (apply fam i0)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop
              principal-filter$prop eqv-class$prop quotient$prop
              sel$prop qmap$prop)
  :hints (("Goal"
           :use ((:instance extensionality
                            (x (image (qmap fam i0)))
                            (y (apply fam i0)))
                 (:instance in-image-qmap-1
                            (y (subset-witness (image (qmap fam i0))
                                               (apply fam i0))))
                 (:instance in-image-qmap-2
                            (y (subset-witness (apply fam i0)
                                               (image (qmap fam i0))))))
           :in-theory (e/d (subset-criterion)
                           (in-image-qmap-1 in-image-qmap-2)))))

(defthmz inj-on-domain-qmap
  (implies (in i0 (domain fam))
           (inj-on-domain (qmap fam i0)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop
              principal-filter$prop eqv-class$prop quotient$prop
              sel$prop qmap$prop)
  :hints (("Goal"
           :use ((:instance qmap-value (c (mv-nth 0 (inj-on-domain-witness (qmap fam i0)))))
                 (:instance qmap-value (c (mv-nth 1 (inj-on-domain-witness (qmap fam i0)))))
                 (:instance in-quotient-principal
                            (c (mv-nth 0 (inj-on-domain-witness (qmap fam i0)))) (r (ultra-rel fam (principal-filter i0 (domain fam)))) (s (prod-family fam)))
                 (:instance in-quotient-principal
                            (c (mv-nth 1 (inj-on-domain-witness (qmap fam i0)))) (r (ultra-rel fam (principal-filter i0 (domain fam)))) (s (prod-family fam)))
                 (:instance eqv-class-principal-equal
                            (a (is-eqv-class-witness (mv-nth 0 (inj-on-domain-witness (qmap fam i0))) (ultra-rel fam (principal-filter i0 (domain fam))) (prod-family fam)))
                            (b (is-eqv-class-witness (mv-nth 1 (inj-on-domain-witness (qmap fam i0))) (ultra-rel fam (principal-filter i0 (domain fam))) (prod-family fam))))
                 (:instance quotient-class-of-witness
                            (c (mv-nth 0 (inj-on-domain-witness (qmap fam i0)))) (r (ultra-rel fam (principal-filter i0 (domain fam)))) (s (prod-family fam)))
                 (:instance quotient-class-of-witness
                            (c (mv-nth 1 (inj-on-domain-witness (qmap fam i0)))) (r (ultra-rel fam (principal-filter i0 (domain fam)))) (s (prod-family fam))))
           :in-theory (disable qmap-value quotient$comprehension
                               prod-family$comprehension eqv-class$comprehension
                               is-eqv-class qmap-apply equal-apply))))

(defthmz principal-ultraproduct
  (implies (and (funp fam) (nonempty-values fam) (in i0 (domain fam)))
           (exists-bijection
            (ultraproduct fam (principal-filter i0 (domain fam)))
            (apply fam i0)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop
              principal-filter$prop eqv-class$prop quotient$prop
              sel$prop qmap$prop)
  :hints (("Goal"
           :use ((:instance exists-bijection-suff
                            (fn (qmap fam i0))
                            (s1 (ultraproduct fam (principal-filter i0 (domain fam))))
                            (s2 (apply fam i0)))
                 (:instance funp-inverse-from-inj (f (qmap fam i0)))
                 (:instance inj-on-domain-qmap))
           :in-theory (disable exists-bijection-suff inj-on-domain-qmap
                               inj-on-domain))))
