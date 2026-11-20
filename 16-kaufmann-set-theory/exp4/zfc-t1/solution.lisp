(in-package "ZF")

(include-book "defs")

;;; ---------------------------------------------------------------
;;; Basic facts about equivalence relations
;;; ---------------------------------------------------------------

(defthmz equivalence-on-in-s
  (implies (and (equivalence-on r s)
                (in (cons a b) r))
           (and (in a s) (in b s)))
  :props (zfc prod2$prop)
  :hints (("Goal" :in-theory (disable refl-on sym-rel trans-rel)
           :use ((:instance subset-necc (a (cons a b)) (x r)
                            (y (prod2 s s)))))))

(defthmz equivalence-on-refl
  (implies (and (equivalence-on r s)
                (in a s))
           (in (cons a a) r))
  :hints (("Goal" :use ((:instance refl-on-necc (x a))))))

(defthmz equivalence-on-sym
  (implies (and (equivalence-on r s)
                (in (cons a b) r))
           (in (cons b a) r))
  :hints (("Goal" :use ((:instance sym-rel-necc (x a) (y b))))))

(defthmz equivalence-on-trans
  (implies (and (equivalence-on r s)
                (in (cons a b) r)
                (in (cons b c) r))
           (in (cons a c) r))
  :hints (("Goal" :use ((:instance trans-rel-necc (x a) (y b) (z c))))))

(in-theory (disable equivalence-on))

(defthmz eqv-class-subset-s
  (subset (eqv-class a r s) s)
  :props (eqv-class$prop)
  :hints (("Goal" :in-theory (enable subset))))

(defthmz in-eqv-class-self
  (implies (and (equivalence-on r s) (in a s))
           (in a (eqv-class a r s)))
  :props (zfc eqv-class$prop))

(defthmz eqv-class-equal-1
  (implies (and (equivalence-on r s)
                (in (cons a b) r))
           (subset (eqv-class a r s) (eqv-class b r s)))
  :props (zfc eqv-class$prop)
  :hints (("Goal" :in-theory (enable subset)
           :use ((:instance equivalence-on-trans
                            (a b) (b a)
                            (c (subset-witness (eqv-class a r s)
                                               (eqv-class b r s))))))))

(defthmz eqv-class-equal
  (implies (and (equivalence-on r s) (in a s) (in b s))
           (equal (equal (eqv-class a r s) (eqv-class b r s))
                  (in (cons a b) r)))
  :props (zfc prod2$prop eqv-class$prop)
  :hints (("Goal"
           :use ((:instance extensionality
                            (x (eqv-class a r s))
                            (y (eqv-class b r s)))
                 (:instance eqv-class-equal-1)
                 (:instance eqv-class-equal-1 (a b) (b a))
                 (:instance in-eqv-class-self (a b))))))

;;; ---------------------------------------------------------------
;;; Quotient is a partition
;;; ---------------------------------------------------------------

(defthmz eqv-class-in-quotient
  (implies (in a s)
           (in (eqv-class a r s) (quotient r s)))
  :props (zfc eqv-class$prop quotient$prop)
  :hints (("Goal" :use ((:instance is-eqv-class-suff
                                   (c (eqv-class a r s)))))))

(defthmz in-quotient-witness
  (implies (in c (quotient r s))
           (and (in (is-eqv-class-witness c r s) s)
                (equal (eqv-class (is-eqv-class-witness c r s) r s) c)))
  :props (zfc quotient$prop)
  :rule-classes nil)

(defthmz in-quotient-subset
  (implies (and (in c (quotient r s)) (in x c))
           (in x s))
  :props (zfc quotient$prop)
  :hints (("Goal" :use ((:instance subset-necc (a x) (x c) (y s))))))

(defthmz union-quotient-1
  (implies (in-in x (quotient r s))
           (in x s))
  :props (zfc quotient$prop)
  :hints (("Goal" :in-theory (enable in-in))))

(defthmz union-quotient-2
  (implies (and (equivalence-on r s) (in x s))
           (in-in x (quotient r s)))
  :props (zfc eqv-class$prop quotient$prop)
  :hints (("Goal" :use ((:instance in-in-suff (a x) (x (quotient r s))
                                   (y (eqv-class x r s)))))))

(defthmz union-quotient-subset-1
  (subset (union (quotient r s)) s)
  :props (zfc quotient$prop)
  :hints (("Goal" :in-theory (enable subset))))

(defthmz union-quotient-subset-2
  (implies (equivalence-on r s)
           (subset s (union (quotient r s))))
  :props (zfc eqv-class$prop quotient$prop)
  :hints (("Goal" :in-theory (enable subset))))

(defthmz union-quotient
  (implies (equivalence-on r s)
           (equal (union (quotient r s)) s))
  :props (zfc eqv-class$prop quotient$prop)
  :hints (("Goal" :use ((:instance extensionality
                                   (x (union (quotient r s))) (y s))))))

(defthm in-implies-not-0
  (implies (in a x) (not (equal x 0))))

(defthmz not-0-in-quotient
  (implies (equivalence-on r s)
           (not (in 0 (quotient r s))))
  :props (zfc eqv-class$prop quotient$prop)
  :hints (("Goal" :in-theory (disable eqv-class$comprehension in-eqv-class-self)
           :use ((:instance in-quotient-witness (c 0))
                        (:instance in-eqv-class-self
                                   (a (is-eqv-class-witness 0 r s)))))))

(defthmz int2-eqv-classes-lemma
  (implies (and (equivalence-on r s)
                (in a s) (in b s)
                (in y (eqv-class a r s))
                (in y (eqv-class b r s)))
           (in (cons a b) r))
  :props (zfc eqv-class$prop)
  :hints (("Goal" :use ((:instance equivalence-on-trans (a a) (b y) (c b))
                        (:instance equivalence-on-sym (a b) (b y))))))

(defthmz subset-0-implies-equal-0
  (implies (subset x 0) (equal (equal x 0) t))
  :hints (("Goal" :use ((:instance extensionality (y 0))))))

(defthmz int2-eqv-classes-subset
  (implies (and (equivalence-on r s)
                (in a s) (in b s)
                (not (in (cons a b) r)))
           (subset (int2 (eqv-class a r s) (eqv-class b r s)) 0))
  :props (zfc diff$prop eqv-class$prop)
  :hints (("Goal"
           :in-theory (e/d (subset) (eqv-class$comprehension subset-x-0))
           :use ((:instance int2-eqv-classes-lemma
                            (y (subset-witness (int2 (eqv-class a r s)
                                                     (eqv-class b r s))
                                               0)))))))

(defthmz int2-eqv-classes
  (implies (and (equivalence-on r s)
                (in a s) (in b s)
                (not (equal (eqv-class a r s) (eqv-class b r s))))
           (equal (int2 (eqv-class a r s) (eqv-class b r s)) 0))
  :props (zfc prod2$prop diff$prop eqv-class$prop)
  :hints (("Goal" :use (int2-eqv-classes-subset))))

(defthmz quotient-pairwise-disjoint
  (implies (equivalence-on r s)
           (pairwise-disjoint (quotient r s)))
  :props (zfc prod2$prop diff$prop eqv-class$prop quotient$prop)
  :hints (("Goal"
           :in-theory (disable eqv-class-equal)
           :use ((:instance in-quotient-witness
                            (c (mv-nth 0 (pairwise-disjoint-witness
                                          (quotient r s)))))
                 (:instance in-quotient-witness
                            (c (mv-nth 1 (pairwise-disjoint-witness
                                          (quotient r s)))))
                 (:instance int2-eqv-classes
                            (a (is-eqv-class-witness
                                (mv-nth 0 (pairwise-disjoint-witness
                                           (quotient r s)))
                                r s))
                            (b (is-eqv-class-witness
                                (mv-nth 1 (pairwise-disjoint-witness
                                           (quotient r s)))
                                r s)))))))

(defthmz quotient-is-partition
  (implies (equivalence-on r s) (partition-p (quotient r s) s))
  :props (zfc prod2$prop diff$prop eqv-class$prop quotient$prop))

;;; ---------------------------------------------------------------
;;; The relation induced by a partition
;;; ---------------------------------------------------------------

(defthmz in-partition-rel
  (equal (in (cons x y) (partition-rel p s))
         (and (in x s) (in y s) (same-block x y p)))
  :props (zfc prod2$prop partition-rel$prop))

(defthmz partition-block-subset
  (implies (and (partition-p p s) (in c p) (in x c))
           (in x s))
  :hints (("Goal" :use ((:instance in-in-suff (a x) (x p) (y c)))
           :in-theory (disable pairwise-disjoint))))

(defthmz partition-has-block
  (implies (and (partition-p p s) (in x s))
           (and (in (in-in-witness x p) p)
                (in x (in-in-witness x p))))
  :hints (("Goal" :use ((:instance in-union (a x) (x p)))
           :in-theory (e/d (in-in) (in-union pairwise-disjoint))))
  :rule-classes nil)

(defthmz partition-blocks-equal
  (implies (and (partition-p p s)
                (in c p) (in d p) (in x c) (in x d))
           (equal (equal c d) t))
  :props (zfc diff$prop)
  :hints (("Goal" :use ((:instance pairwise-disjoint-necc)
                        (:instance in-implies-not-0 (a x) (x (int2 c d))))
           :in-theory (disable pairwise-disjoint in-implies-not-0))))

(defthmz partition-rel-subset
  (subset (partition-rel p s) (prod2 s s))
  :props (zfc prod2$prop partition-rel$prop)
  :hints (("Goal" :in-theory (enable subset))))

(defthmz partition-rel-refl
  (implies (partition-p p s)
           (refl-on (partition-rel p s) s))
  :props (zfc prod2$prop partition-rel$prop)
  :hints (("Goal" :in-theory (disable partition-p)
           :use ((:instance partition-has-block
                            (x (refl-on-witness (partition-rel p s) s)))
                 (:instance same-block-suff
                            (x (refl-on-witness (partition-rel p s) s))
                            (y (refl-on-witness (partition-rel p s) s))
                            (c (in-in-witness
                                (refl-on-witness (partition-rel p s) s)
                                p)))))))

(defthmz partition-rel-sym
  (sym-rel (partition-rel p s))
  :props (zfc prod2$prop partition-rel$prop)
  :hints (("Goal"
           :in-theory (disable in-partition-rel)
           :use ((:instance in-partition-rel
                            (x (mv-nth 0 (sym-rel-witness (partition-rel p s))))
                            (y (mv-nth 1 (sym-rel-witness (partition-rel p s)))))
                 (:instance in-partition-rel
                            (x (mv-nth 1 (sym-rel-witness (partition-rel p s))))
                            (y (mv-nth 0 (sym-rel-witness (partition-rel p s)))))
                 (:instance same-block-suff
                            (x (mv-nth 1 (sym-rel-witness (partition-rel p s))))
                            (y (mv-nth 0 (sym-rel-witness (partition-rel p s))))
                            (c (same-block-witness
                                (mv-nth 0 (sym-rel-witness (partition-rel p s)))
                                (mv-nth 1 (sym-rel-witness (partition-rel p s)))
                                p)))))))

(defthmz same-block-trans
  (implies (and (partition-p p s)
                (same-block x y p)
                (same-block y z p))
           (same-block x z p))
  :props (zfc diff$prop)
  :hints (("Goal"
           :in-theory (disable partition-p)
           :use ((:instance partition-blocks-equal
                            (c (same-block-witness x y p))
                            (d (same-block-witness y z p))
                            (x y))
                 (:instance same-block-suff
                            (y z)
                            (c (same-block-witness x y p)))))))

(defthmz partition-rel-trans
  (implies (partition-p p s)
           (trans-rel (partition-rel p s)))
  :props (zfc prod2$prop diff$prop partition-rel$prop)
  :hints (("Goal"
           :in-theory (disable partition-p)
           :use ((:instance same-block-trans
                            (x (mv-nth 0 (trans-rel-witness (partition-rel p s))))
                            (y (mv-nth 1 (trans-rel-witness (partition-rel p s))))
                            (z (mv-nth 2 (trans-rel-witness (partition-rel p s)))))))))

(defthmz partition-rel-is-equivalence
  (implies (partition-p p s) (equivalence-on (partition-rel p s) s))
  :props (zfc prod2$prop diff$prop partition-rel$prop)
  :hints (("Goal" :in-theory (e/d (equivalence-on) (partition-p)))))

;;; ---------------------------------------------------------------
;;; Quotient of the relation induced by a partition
;;; ---------------------------------------------------------------

(defthmz eqv-class-partition-rel-subset-1
  (implies (and (partition-p p s) (in c p) (in a c))
           (subset (eqv-class a (partition-rel p s) s) c))
  :props (zfc prod2$prop diff$prop eqv-class$prop partition-rel$prop)
  :hints (("Goal"
           :in-theory (e/d (subset) (partition-p))
           :use ((:instance partition-blocks-equal
                            (x a)
                            (d (same-block-witness
                                a
                                (subset-witness
                                 (eqv-class a (partition-rel p s) s) c)
                                p)))))))

(defthmz eqv-class-partition-rel-subset-2
  (implies (and (partition-p p s) (in c p) (in a c))
           (subset c (eqv-class a (partition-rel p s) s)))
  :props (zfc prod2$prop eqv-class$prop partition-rel$prop)
  :hints (("Goal"
           :in-theory (e/d (subset) (partition-p))
           :use ((:instance partition-block-subset (x a))
                 (:instance partition-block-subset
                            (x (subset-witness
                                c (eqv-class a (partition-rel p s) s))))
                 (:instance same-block-suff
                            (x a)
                            (y (subset-witness
                                c (eqv-class a (partition-rel p s) s))))))))

(defthmz eqv-class-partition-rel
  (implies (and (partition-p p s) (in c p) (in a c))
           (equal (eqv-class a (partition-rel p s) s) c))
  :props (zfc prod2$prop diff$prop eqv-class$prop partition-rel$prop)
  :hints (("Goal"
           :in-theory (disable partition-p)
           :use (eqv-class-partition-rel-subset-1
                 eqv-class-partition-rel-subset-2
                 (:instance extensionality
                            (x (eqv-class a (partition-rel p s) s))
                            (y c))))))

(defthmz quotient-partition-rel-subset-1
  (implies (and (partition-p p s)
                (in d (quotient (partition-rel p s) s)))
           (in d p))
  :props (zfc prod2$prop diff$prop eqv-class$prop quotient$prop
              partition-rel$prop)
  :hints (("Goal"
           :in-theory (disable partition-p eqv-class-partition-rel
                               quotient$comprehension)
           :use ((:instance in-quotient-witness (r (partition-rel p s)) (c d))
                 (:instance partition-has-block
                            (x (is-eqv-class-witness d (partition-rel p s) s)))
                 (:instance eqv-class-partition-rel
                            (a (is-eqv-class-witness d (partition-rel p s) s))
                            (c (in-in-witness
                                (is-eqv-class-witness d (partition-rel p s) s)
                                p)))))))

(defthm partition-p-not-0
  (implies (partition-p p s) (not (in 0 p)))
  :rule-classes nil)

(defthmz quotient-partition-rel-subset-2
  (implies (and (partition-p p s)
                (in c p))
           (in c (quotient (partition-rel p s) s)))
  :props (zfc prod2$prop diff$prop eqv-class$prop quotient$prop
              partition-rel$prop)
  :hints (("Goal"
           :in-theory (disable partition-p eqv-class-partition-rel
                               quotient$comprehension eqv-class-in-quotient)
           :use ((:instance partition-p-not-0)
                 (:instance min-in-1 (z c))
                 (:instance partition-block-subset (x (min-in c)))
                 (:instance eqv-class-partition-rel (a (min-in c)))
                 (:instance eqv-class-in-quotient
                            (a (min-in c)) (r (partition-rel p s)))))))

(defthmz quotient-of-partition-rel
  (implies (partition-p p s) (equal (quotient (partition-rel p s) s) p))
  :props (zfc prod2$prop diff$prop eqv-class$prop quotient$prop partition-rel$prop)
  :hints (("Goal"
           :in-theory (disable partition-p)
           :use ((:instance extensionality
                            (x (quotient (partition-rel p s) s))
                            (y p))
                 (:instance quotient-partition-rel-subset-1
                            (d (subset-witness (quotient (partition-rel p s) s)
                                               p)))
                 (:instance quotient-partition-rel-subset-2
                            (c (subset-witness p
                                               (quotient (partition-rel p s) s))))))))

;;; ---------------------------------------------------------------
;;; Relation induced by the quotient
;;; ---------------------------------------------------------------

(defthmz equivalence-on-in-r
  (implies (and (equivalence-on r s)
                (in q r))
           (and (consp q) (in (car q) s) (in (cdr q) s)))
  :props (zfc prod2$prop)
  :hints (("Goal" :in-theory (enable equivalence-on)
           :use ((:instance subset-necc (a q) (x r) (y (prod2 s s))))))
  :rule-classes nil)

(defthmz in-same-eqv-class
  (implies (and (equivalence-on r s)
                (in x (eqv-class w r s))
                (in y (eqv-class w r s)))
           (in (cons x y) r))
  :props (zfc eqv-class$prop)
  :hints (("Goal" :use ((:instance equivalence-on-sym (a w) (b x))
                        (:instance equivalence-on-trans (a x) (b w) (c y))))))

(defthmz in-same-quotient-block
  (implies (and (equivalence-on r s)
                (in c (quotient r s))
                (in x c)
                (in y c))
           (in (cons x y) r))
  :props (zfc eqv-class$prop quotient$prop)
  :hints (("Goal"
           :in-theory (disable in-same-eqv-class eqv-class$comprehension
                               quotient$comprehension)
           :use ((:instance in-quotient-witness)
                 (:instance in-same-eqv-class
                            (w (is-eqv-class-witness c r s)))))))

(defthmz partition-rel-quotient-subset-1
  (implies (and (equivalence-on r s)
                (in q (partition-rel (quotient r s) s)))
           (in q r))
  :props (zfc prod2$prop eqv-class$prop quotient$prop partition-rel$prop)
  :hints (("Goal"
           :use ((:instance in-same-quotient-block
                            (c (same-block-witness (car q) (cdr q)
                                                   (quotient r s)))
                            (x (car q)) (y (cdr q)))))))

(defthmz partition-rel-quotient-subset-2
  (implies (and (equivalence-on r s)
                (in q r))
           (in q (partition-rel (quotient r s) s)))
  :props (zfc prod2$prop eqv-class$prop quotient$prop partition-rel$prop)
  :hints (("Goal"
           :use ((:instance equivalence-on-in-r)
                 (:instance same-block-suff
                            (c (eqv-class (car q) r s))
                            (x (car q)) (y (cdr q)) (p (quotient r s)))))))

(defthmz partition-rel-of-quotient
  (implies (equivalence-on r s) (equal (partition-rel (quotient r s) s) r))
  :props (zfc prod2$prop diff$prop eqv-class$prop quotient$prop partition-rel$prop)
  :hints (("Goal"
           :use ((:instance extensionality
                            (x (partition-rel (quotient r s) s))
                            (y r))
                 (:instance partition-rel-quotient-subset-1
                            (q (subset-witness (partition-rel (quotient r s) s)
                                               r)))
                 (:instance partition-rel-quotient-subset-2
                            (q (subset-witness r
                                               (partition-rel (quotient r s) s))))))))

;;; ---------------------------------------------------------------
;;; The quotient map
;;; ---------------------------------------------------------------

; qmap = {p in s X P(s) : (cdr p) = [car p]}
(zsub qmap (r s)
      p
      (prod2 s (powerset s))
      (equal (cdr p) (eqv-class (car p) r s)))

(defthmz in-qmap
  (equal (in p (qmap r s))
         (and (consp p)
              (in (car p) s)
              (equal (cdr p) (eqv-class (car p) r s))))
  :props (zfc prod2$prop eqv-class$prop qmap$prop))

(in-theory (disable qmap$comprehension))

(defthmz relation-p-qmap
  (relation-p (qmap r s))
  :props (zfc prod2$prop eqv-class$prop qmap$prop)
  :hints (("Goal" :in-theory (enable relation-p))))

(defthmz funp-qmap
  (funp (qmap r s))
  :props (zfc prod2$prop eqv-class$prop qmap$prop)
  :hints (("Goal" :in-theory (enable funp)
           :use ((:instance acl2::cons-car-cdr
                            (acl2::x (mv-nth 0 (funp-witness (qmap r s)))))
                 (:instance acl2::cons-car-cdr
                            (acl2::x (mv-nth 1 (funp-witness (qmap r s)))))))))

(defthmz apply-qmap
  (implies (in a s)
           (equal (apply (qmap r s) a) (eqv-class a r s)))
  :props (zfc prod2$prop eqv-class$prop qmap$prop)
  :hints (("Goal" :in-theory (disable equal-apply apply-default)
           :use ((:instance apply-intro-lemma
                                   (f (qmap r s))
                                   (p (cons a (eqv-class a r s))))))))

(defthmz domain-qmap-1
  (implies (in x (domain (qmap r s)))
           (in x s))
  :props (zfc prod2$prop domain$prop eqv-class$prop qmap$prop)
  :hints (("Goal" :in-theory (e/d (in-domain-rewrite) (in-cons-apply)))))

(defthmz domain-qmap-2
  (implies (in x s)
           (in x (domain (qmap r s))))
  :props (zfc prod2$prop domain$prop eqv-class$prop qmap$prop)
  :hints (("Goal" :use ((:instance in-car-domain
                                   (p (cons x (eqv-class x r s)))
                                   (r (qmap r s)))))))

(defthmz domain-qmap
  (equal (domain (qmap r s)) s)
  :props (zfc prod2$prop domain$prop eqv-class$prop qmap$prop)
  :hints (("Goal"
           :use ((:instance extensionality (x (domain (qmap r s))) (y s))
                 (:instance domain-qmap-1
                            (x (subset-witness (domain (qmap r s)) s)))
                 (:instance domain-qmap-2
                            (x (subset-witness s (domain (qmap r s)))))))))

(defthmz image-qmap-1
  (implies (in y (image (qmap r s)))
           (in y (quotient r s)))
  :props (zfc prod2$prop domain$prop inverse$prop eqv-class$prop
              quotient$prop qmap$prop)
  :hints (("Goal"
           :in-theory (disable quotient$comprehension)
           :use ((:instance in-image-necc (x y) (f (qmap r s)))
                 (:instance eqv-class-in-quotient
                            (a (apply (inverse (qmap r s)) y)))))))

(defthmz image-qmap-2
  (implies (in y (quotient r s))
           (in y (image (qmap r s))))
  :props (zfc prod2$prop domain$prop inverse$prop eqv-class$prop
              quotient$prop qmap$prop)
  :hints (("Goal"
           :in-theory (disable quotient$comprehension eqv-class$comprehension)
           :use ((:instance in-quotient-witness (c y))
                 (:instance in-image-suff
                            (r (qmap r s))
                            (p (cons (is-eqv-class-witness y r s) y)))))))

(defthmz image-qmap
  (equal (image (qmap r s)) (quotient r s))
  :props (zfc prod2$prop domain$prop inverse$prop eqv-class$prop
              quotient$prop qmap$prop)
  :hints (("Goal"
           :use ((:instance extensionality
                            (x (image (qmap r s))) (y (quotient r s)))
                 (:instance image-qmap-1
                            (y (subset-witness (image (qmap r s))
                                               (quotient r s))))
                 (:instance image-qmap-2
                            (y (subset-witness (quotient r s)
                                               (image (qmap r s)))))))))

(defthmz maps-to-classes-qmap
  (maps-to-classes (qmap r s) r s)
  :props (zfc prod2$prop eqv-class$prop qmap$prop))

(defthmz quotient-map-exists
  (implies (equivalence-on r s) (exists-quotient-map r s))
  :props (zfc prod2$prop domain$prop inverse$prop eqv-class$prop quotient$prop
              qmap$prop)
  :hints (("Goal" :use ((:instance exists-quotient-map-suff
                                   (f (qmap r s)))))))
