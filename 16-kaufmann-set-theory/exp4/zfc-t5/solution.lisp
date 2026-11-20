(in-package "ZF")

(include-book "defs")

;;; General lemmas

(defun-sk agree-on (f1 f2 m)
  (forall x (implies (in x m)
                     (equal (apply f1 x) (apply f2 x)))))

(in-theory (disable agree-on))

(defthmz domain-restrict-subset
  (implies (subset m (domain f))
           (equal (domain (restrict f m)) m))
  :props (zfc domain$prop restrict$prop diff$prop))

(defthmz apply-restricts-when-agree
  (implies (and (funp f1) (funp f2)
                (subset m (domain f1)) (subset m (domain f2))
                (agree-on f1 f2 m)
                (in x m))
           (equal (apply (restrict f1 m) x)
                  (apply (restrict f2 m) x)))
  :props (zfc domain$prop restrict$prop diff$prop)
  :hints (("Goal" :use agree-on-necc)))

(defthmz fn-equal-restricts-when-agree
  (implies (and (funp f1) (funp f2)
                (subset m (domain f1)) (subset m (domain f2))
                (agree-on f1 f2 m))
           (fn-equal (restrict f1 m) (restrict f2 m)))
  :props (zfc domain$prop restrict$prop diff$prop)
  :hints (("Goal"
           :in-theory (disable apply-restrict)
           :expand ((fn-equal (restrict f1 m) (restrict f2 m))))))

(defthmz restrict-equal-when-agree
  (implies (and (funp f1) (funp f2)
                (subset m (domain f1)) (subset m (domain f2))
                (agree-on f1 f2 m))
           (equal (restrict f1 m) (restrict f2 m)))
  :props (zfc domain$prop restrict$prop diff$prop)
  :hints (("Goal"
           :in-theory (disable agree-on)
           :use ((:instance fn-equal-implies-equal
                            (f (restrict f1 m)) (g (restrict f2 m)))))))

;;; Uniqueness

(zsub tr-diff-set (a f1 f2) b a (not (equal (apply f1 b) (apply f2 b))))

(defthmz tr-diff-set-min-agrees
  (implies (and (ordinal-p a)
                (not (equal (tr-diff-set a f1 f2) 0)))
           (agree-on f1 f2 (min-in (tr-diff-set a f1 f2))))
  :props (zfc tr-diff-set$prop)
  :hints (("Goal"
           :in-theory (e/d (ordinal-p) (min-in-1 min-in-2))
           :expand ((agree-on f1 f2 (min-in (tr-diff-set a f1 f2))))
           :use ((:instance min-in-1 (z (tr-diff-set a f1 f2)))
                 (:instance min-in-2
                            (z (tr-diff-set a f1 f2))
                            (a (agree-on-witness f1 f2 (min-in (tr-diff-set a f1 f2)))))))))

(defthm tr-fn-p-forward
  (implies (tr-fn-p f a)
           (and (funp f) (equal (domain f) a)))
  :rule-classes :forward-chaining)

(defthm tr-fn-p-step
  (implies (and (tr-fn-p f a) (in b a))
           (equal (apply f b) (tr-g (restrict f b))))
  :hints (("Goal" :use tr-step-ok-necc)))

(in-theory (disable tr-fn-p tr-step-ok))

(defthmz tr-diff-set-min-props
  (implies (and (ordinal-p a)
                (not (equal (tr-diff-set a f1 f2) 0)))
           (and (in (min-in (tr-diff-set a f1 f2)) a)
                (subset (min-in (tr-diff-set a f1 f2)) a)
                (not (equal (apply f1 (min-in (tr-diff-set a f1 f2)))
                            (apply f2 (min-in (tr-diff-set a f1 f2)))))))
  :props (zfc tr-diff-set$prop)
  :hints (("Goal"
           :in-theory (e/d (ordinal-p) (min-in-1))
           :use ((:instance min-in-1 (z (tr-diff-set a f1 f2))))))
  :rule-classes nil)

(defthmz tr-diff-set-empty
  (implies (and (ordinal-p a) (tr-fn-p f1 a) (tr-fn-p f2 a))
           (equal (tr-diff-set a f1 f2) 0))
  :props (zfc domain$prop restrict$prop diff$prop tr-diff-set$prop)
  :hints (("Goal"
           :in-theory (disable tr-diff-set-min-agrees restrict-equal-when-agree
                               equal-apply tr-fn-p-step)
           :use (tr-diff-set-min-agrees
                 tr-diff-set-min-props
                 (:instance restrict-equal-when-agree
                            (m (min-in (tr-diff-set a f1 f2))))
                 (:instance tr-fn-p-step (f f1) (b (min-in (tr-diff-set a f1 f2))))
                 (:instance tr-fn-p-step (f f2) (b (min-in (tr-diff-set a f1 f2))))))))

(defthmz tr-fn-equal
  (implies (and (ordinal-p a) (tr-fn-p f1 a) (tr-fn-p f2 a))
           (fn-equal f1 f2))
  :props (zfc domain$prop restrict$prop diff$prop tr-diff-set$prop)
  :hints (("Goal"
           :expand ((fn-equal f1 f2))
           :in-theory (disable tr-diff-set-empty tr-diff-set$comprehension tr-fn-p-step)
           :use (tr-diff-set-empty
                 (:instance tr-diff-set$comprehension
                            (b (fn-equal-witness f1 f2)))))))

(defthmz tr-unique
  (implies (and (ordinal-p a) (tr-fn-p f1 a) (tr-fn-p f2 a)) (equal f1 f2))
  :rule-classes nil
  :props (zfc domain$prop restrict$prop diff$prop tr-diff-set$prop)
  :hints (("Goal"
           :use (tr-fn-equal
                 (:instance fn-equal-implies-equal (f f1) (g f2))))))

;;; Existence

(defthmz restrict-restrict-1
  (implies (subset d c)
           (subset (restrict (restrict f c) d)
                   (restrict f d)))
  :props (zfc restrict$prop)
  :hints (("Goal" :expand ((subset (restrict (restrict f c) d)
                                   (restrict f d))))))

(defthmz restrict-restrict-2
  (implies (subset d c)
           (subset (restrict f d)
                   (restrict (restrict f c) d)))
  :props (zfc restrict$prop)
  :hints (("Goal" :expand ((subset (restrict f d)
                                   (restrict (restrict f c) d))))))

(defthmz restrict-restrict
  (implies (subset d c)
           (equal (restrict (restrict f c) d)
                  (restrict f d)))
  :props (zfc restrict$prop)
  :hints (("Goal" :use ((:instance extensionality
                                   (x (restrict (restrict f c) d))
                                   (y (restrict f d)))))))

(defthmz ordinal-in-subset
  (implies (and (ordinal-p b) (in c b))
           (subset c b))
  :hints (("Goal" :in-theory (enable ordinal-p))))

(defthmz tr-fn-p-restrict-step
  (implies (and (ordinal-p b) (tr-fn-p f b) (in c b)
                (in d c))
           (equal (apply (restrict f c) d)
                  (tr-g (restrict (restrict f c) d))))
  :props (zfc domain$prop restrict$prop diff$prop)
  :hints (("Goal"
           :in-theory (disable tr-fn-p-step ordinal-in-subset)
           :use ((:instance tr-fn-p-step (a b) (b d))
                 (:instance ordinal-in-subset (b b) (c c))
                 (:instance ordinal-in-subset (b c) (c d))
                 (:instance ordinals-closure (x b) (y c))))))

(defthmz tr-fn-p-restrict
  (implies (and (ordinal-p b) (tr-fn-p f b) (in c b))
           (tr-fn-p (restrict f c) c))
  :props (zfc domain$prop restrict$prop diff$prop)
  :hints (("Goal"
           :in-theory (e/d (tr-fn-p) (tr-fn-p-restrict-step))
           :expand ((tr-step-ok (restrict f c)))
           :use ((:instance tr-fn-p-restrict-step
                            (d (tr-step-ok-witness (restrict f c))))))))

(zfn tr-f (a) x y a (tr-fn-p y x))

(zfn tr-gfn (a) x y a (equal (equal y (tr-g (apply (tr-f a) x))) t))

(defun-sk tr-exists-below (a)
  (forall b (implies (in b a) (tr-exists b))))

(defthmz tr-f-props
  (implies (and (tr-exists-below a) (in b a))
           (and (in b (domain (tr-f a)))
                (tr-fn-p (apply (tr-f a) b) b)))
  :props (zfc tr-f$prop)
  :hints (("Goal"
           :in-theory (disable tr-exists-below-necc tr-exists)
           :use ((:instance tr-exists-below-necc)
                 (:instance tr-f$domain-2 (x b) (y (tr-exists-witness b)))
                 (:instance tr-f$chooses (x b) (y (apply (tr-f a) b)))
                 (:instance tr-exists (a b))))))

(defthmz domain-tr-gfn
  (equal (domain (tr-gfn a)) a)
  :props (zfc domain$prop diff$prop tr-gfn$prop)
  :hints (("Goal"
           :in-theory (enable extensionality-rewrite)
           :expand ((subset a (domain (tr-gfn a))))
           :use ((:instance tr-gfn$domain-2
                            (x (subset-witness a (domain (tr-gfn a))))
                            (y (tr-g (apply (tr-f a) (subset-witness a (domain (tr-gfn a)))))))))))

(defthmz apply-tr-gfn
  (implies (in b a)
           (equal (apply (tr-gfn a) b)
                  (tr-g (apply (tr-f a) b))))
  :props (zfc domain$prop diff$prop tr-gfn$prop)
  :hints (("Goal"
           :use ((:instance tr-gfn$chooses (x b) (y (apply (tr-gfn a) b)))))))

(defthmz tr-f-coherent
  (implies (and (ordinal-p a) (tr-exists-below a) (in b a) (in c b))
           (equal (apply (tr-f a) c)
                  (restrict (apply (tr-f a) b) c)))
  :props (zfc domain$prop restrict$prop diff$prop tr-diff-set$prop tr-f$prop)
  :hints (("Goal"
           :in-theory (disable tr-f-props tr-fn-p-step ordinal-in-subset equal-apply
                               tr-fn-p-restrict ordinals-closure)
           :use ((:instance tr-f-props)
                 (:instance tr-f-props (b c))
                 (:instance ordinals-closure (x a) (y b))
                 (:instance ordinals-closure (x b) (y c))
                 (:instance transitive-preserves-in-1 (x a) (y b) (z c))
                 (:instance tr-fn-p-restrict (f (apply (tr-f a) b)) (b b) (c c))
                 (:instance tr-unique
                            (a c)
                            (f1 (apply (tr-f a) c))
                            (f2 (restrict (apply (tr-f a) b) c)))))))

(defthmz tr-gfn-agrees-1
  (implies (and (ordinal-p a) (tr-exists-below a) (in b a) (in c b))
           (equal (apply (tr-gfn a) c)
                  (apply (apply (tr-f a) b) c)))
  :props (zfc domain$prop restrict$prop diff$prop tr-diff-set$prop tr-f$prop tr-gfn$prop)
  :hints (("Goal"
           :in-theory (disable tr-f-props tr-fn-p-step equal-apply
                               tr-f-coherent apply-tr-gfn ordinals-closure)
           :use ((:instance tr-f-props)
                 (:instance tr-f-coherent)
                 (:instance apply-tr-gfn (b c))
                 (:instance transitive-preserves-in-1 (x a) (y b) (z c))
                 (:instance ordinals-closure (x a) (y b))
                 (:instance tr-fn-p-step (f (apply (tr-f a) b)) (a b) (b c))))))

(defthmz tr-gfn-agrees
  (implies (and (ordinal-p a) (tr-exists-below a) (in b a))
           (agree-on (tr-gfn a) (apply (tr-f a) b) b))
  :props (zfc domain$prop restrict$prop diff$prop tr-diff-set$prop tr-f$prop tr-gfn$prop)
  :hints (("Goal"
           :expand ((agree-on (tr-gfn a) (apply (tr-f a) b) b))
           :in-theory (disable equal-apply))))

(defthmz restrict-tr-gfn
  (implies (and (ordinal-p a) (tr-exists-below a) (in b a))
           (equal (restrict (tr-gfn a) b)
                  (apply (tr-f a) b)))
  :props (zfc domain$prop restrict$prop diff$prop tr-diff-set$prop tr-f$prop tr-gfn$prop)
  :hints (("Goal"
           :in-theory (disable tr-f-props ordinal-in-subset restrict-equal-when-agree
                               tr-gfn-agrees)
           :use ((:instance tr-f-props)
                 (:instance tr-gfn-agrees)
                 (:instance ordinal-in-subset (b a) (c b))
                 (:instance restrict-equal-when-agree
                            (f1 (tr-gfn a)) (f2 (apply (tr-f a) b)) (m b))
                 (:instance restrict-domain (r (apply (tr-f a) b)))))))

(defthmz tr-gfn-is-tr-fn
  (implies (and (ordinal-p a) (tr-exists-below a))
           (tr-fn-p (tr-gfn a) a))
  :props (zfc domain$prop restrict$prop diff$prop tr-diff-set$prop tr-f$prop tr-gfn$prop)
  :hints (("Goal"
           :in-theory (enable tr-fn-p)
           :expand ((tr-step-ok (tr-gfn a))))))

(defthmz tr-exists-when-below
  (implies (and (ordinal-p a) (tr-exists-below a))
           (tr-exists a))
  :props (zfc domain$prop restrict$prop diff$prop tr-diff-set$prop tr-f$prop tr-gfn$prop)
  :hints (("Goal"
           :in-theory (disable tr-exists)
           :use ((:instance tr-exists-suff (f (tr-gfn a)))))))

(zsub tr-bad (a) b a (not (tr-exists b)))

(defthmz tr-bad-min-below
  (implies (and (ordinal-p a)
                (not (equal (tr-bad a) 0)))
           (tr-exists-below (min-in (tr-bad a))))
  :props (zfc tr-bad$prop)
  :hints (("Goal"
           :in-theory (e/d (ordinal-p) (min-in-1 min-in-2 tr-exists))
           :expand ((tr-exists-below (min-in (tr-bad a))))
           :use ((:instance min-in-1 (z (tr-bad a)))
                 (:instance min-in-2
                            (z (tr-bad a))
                            (a (tr-exists-below-witness (min-in (tr-bad a)))))))))

(defthmz tr-bad-empty
  (implies (ordinal-p a)
           (equal (tr-bad a) 0))
  :props (zfc domain$prop restrict$prop diff$prop tr-diff-set$prop tr-f$prop tr-gfn$prop
              tr-bad$prop)
  :hints (("Goal"
           :in-theory (disable min-in-1 tr-exists tr-bad-min-below tr-exists-when-below)
           :use ((:instance min-in-1 (z (tr-bad a)))
                 tr-bad-min-below
                 (:instance ordinals-closure (x a) (y (min-in (tr-bad a))))
                 (:instance tr-exists-when-below (a (min-in (tr-bad a))))))))

(defthmz tr-existence
  (implies (ordinal-p a) (tr-exists a))
  :props (zfc domain$prop restrict$prop diff$prop tr-diff-set$prop tr-f$prop tr-gfn$prop
              tr-bad$prop)
  :hints (("Goal"
           :in-theory (disable tr-exists tr-bad-empty tr-exists-when-below)
           :expand ((tr-exists-below a))
           :use (tr-bad-empty
                 tr-exists-when-below
                 (:instance tr-bad$comprehension (b (tr-exists-below-witness a)))))))
