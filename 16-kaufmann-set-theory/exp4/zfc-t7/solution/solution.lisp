(in-package "ZF")

(include-book "defs")
(include-book "projects/set-theory/topology/closed-subspace-is-compact" :dir :system)
(include-book "projects/set-theory/topology/finite-intersection-closure" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Theorem 1: continuous-compose
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmz preimage-compose-pointwise
  (implies (and (funp f) (funp g) (subset (image f) (domain g)))
           (equal (in x (preimage (compose g f) v))
                  (in x (preimage f (preimage g v)))))
  :props (zfc prod2$prop domain$prop inverse$prop compose$prop preimage$prop))

(defthmz preimage-compose
  (implies (and (funp f) (funp g) (subset (image f) (domain g)))
           (equal (preimage (compose g f) v)
                  (preimage f (preimage g v))))
  :hints (("Goal" :in-theory (e/d (extensionality-rewrite) (preimage$comprehension))
                  :expand ((subset (preimage (compose g f) v) (preimage f (preimage g v)))
                           (subset (preimage f (preimage g v)) (preimage (compose g f) v)))))
  :props (zfc prod2$prop domain$prop inverse$prop compose$prop preimage$prop))

(defthmz image-compose-subset-union
  (implies (subset (image g) s)
           (subset (image (compose g f)) s))
  :hints (("Goal" :use ((:instance subset-image-compose (g g) (h f))
                        (:instance subset-transitivity (x (image (compose g f))) (y (image g)) (z s)))
           :in-theory (disable subset-image-compose subset-transitivity)))
  :props (zfc prod2$prop domain$prop inverse$prop compose$prop))

(defthmz preimages-open-compose
  (implies (and (continuous f tp1 tp2) (continuous g tp2 tp3))
           (preimages-open (compose g f) tp1 tp3))
  :hints (("Goal" :expand ((preimages-open (compose g f) tp1 tp3))
           :in-theory (disable preimages-open)
           :use ((:instance preimages-open-necc (f g) (tp1 tp2) (tp2 tp3) (v (preimages-open-witness (compose g f) tp1 tp3)))
                 (:instance preimages-open-necc (f f) (tp1 tp1) (tp2 tp2)
                    (v (preimage g (preimages-open-witness (compose g f) tp1 tp3)))))))
  :props (zfc prod2$prop domain$prop inverse$prop compose$prop preimage$prop))

(defthmz continuous-compose
  (implies (and (continuous f tp1 tp2) (continuous g tp2 tp3))
           (continuous (compose g f) tp1 tp3))
  :hints (("Goal" :in-theory (disable preimages-open)
           :use (preimages-open-compose)))
  :props (zfc prod2$prop domain$prop inverse$prop compose$prop preimage$prop))

(in-theory (disable preimages-open))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Theorems 3 and 4: hausdorff-singleton-closed and
;;; compact-subset-of-hausdorff-is-closed.  A set s is closed when every point
;;; outside it lies in an open set disjoint from s.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(zsub avoiders (s tp) w tp (equal (int2 w s) 0))

(defun-sk exists-avoider (y s tp)
  (exists w (and (in w tp) (in y w) (equal (int2 w s) 0))))

(defun-sk all-outside-avoidable (s tp)
  (forall y (implies (and (in y (union tp)) (not (in y s)))
                     (exists-avoider y s tp))))

(in-theory (disable exists-avoider all-outside-avoidable))

(defthmz in-union-avoiders-1
  (implies (in y (union (avoiders s tp)))
           (and (in y (union tp))
                (not (in y s))))
  :hints (("Goal" :expand ((in-in y (avoiders s tp)))
           :use ((:instance int2-non-empty (a y) (x (in-in-witness y (avoiders s tp))) (y s))
                 (:instance in-in-suff (a y) (x tp) (y (in-in-witness y (avoiders s tp)))))
           :in-theory (disable int2-non-empty in-in-suff)))
  :rule-classes nil
  :props (zfc diff$prop avoiders$prop))

(defthmz in-union-avoiders-2
  (implies (and (all-outside-avoidable s tp)
                (in y (union tp))
                (not (in y s)))
           (in y (union (avoiders s tp))))
  :hints (("Goal" :use (all-outside-avoidable-necc
                        (:instance in-in-suff (a y) (x (avoiders s tp)) (y (exists-avoider-witness y s tp))))
           :in-theory (e/d (exists-avoider) (in-in-suff all-outside-avoidable-necc))))
  :rule-classes nil
  :props (zfc diff$prop avoiders$prop))

(defthmz in-diff-iff-in-union-avoiders
  (implies (all-outside-avoidable s tp)
           (equal (in y (diff (union tp) s)) (in y (union (avoiders s tp)))))
  :hints (("Goal" :use (in-union-avoiders-1 in-union-avoiders-2)
                  :in-theory (disable in-union)))
  :props (zfc diff$prop avoiders$prop))

(defthmz diff-is-union-avoiders-1
  (implies (all-outside-avoidable s tp)
           (subset (diff (union tp) s) (union (avoiders s tp))))
  :hints (("Goal" :in-theory (disable in-diff in-union)
                  :expand ((subset (diff (union tp) s) (union (avoiders s tp))))))
  :props (zfc diff$prop avoiders$prop))

(defthmz diff-is-union-avoiders-2
  (implies (all-outside-avoidable s tp)
           (subset (union (avoiders s tp)) (diff (union tp) s)))
  :hints (("Goal" :in-theory (disable in-diff in-union)
                  :expand ((subset (union (avoiders s tp)) (diff (union tp) s)))))
  :props (zfc diff$prop avoiders$prop))

(defthmz diff-is-union-avoiders
  (implies (all-outside-avoidable s tp)
           (equal (diff (union tp) s) (union (avoiders s tp))))
  :hints (("Goal" :use (diff-is-union-avoiders-1 diff-is-union-avoiders-2
                        (:instance extensionality (x (diff (union tp) s)) (y (union (avoiders s tp)))))
                  :in-theory (disable diff-is-union-avoiders-1 diff-is-union-avoiders-2)))
  :props (zfc diff$prop avoiders$prop))

(defthmz subset-avoiders
  (subset (avoiders s tp) tp)
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc avoiders$prop))

(defthmz closed-if-all-outside-avoidable
  (implies (and (tpp tp) (subset s (union tp)) (all-outside-avoidable s tp))
           (closed s tp))
  :hints (("Goal" :in-theory (enable tpp)
           :use ((:instance tpp-union-necc (tp2 (avoiders s tp))))))
  :props (zfc diff$prop avoiders$prop))

;; theorem 3
(defthmz int2-singleton-not-in
  (implies (not (in x w))
           (equal (int2 w (pair x x)) 0))
  :hints (("Goal" :use ((:instance min-in-1 (z (int2 w (pair x x)))))))
  :props (zfc diff$prop))

(defthmz hausdorff-singleton-avoidable
  (implies (and (hausdorff tp) (in x (union tp)) (in y (union tp)) (not (in y (singleton x))))
           (exists-avoider y (singleton x) tp))
  :hints (("Goal" :use ((:instance hausdorff-necc (x x) (y y))
                        (:instance exists-avoider-suff (w (mv-nth 1 (point-point-separable-witness x y tp))) (s (singleton x)))
                        (:instance int2-non-empty (a x) (x (mv-nth 0 (point-point-separable-witness x y tp)))
                                   (y (mv-nth 1 (point-point-separable-witness x y tp)))))
           :in-theory (e/d (point-point-separable) (hausdorff-necc exists-avoider-suff int2-non-empty))))
  :props (zfc diff$prop))

(defthmz hausdorff-singleton-closed
  (implies (and (tpp tp) (hausdorff tp) (in x (union tp)))
           (closed (singleton x) tp))
  :hints (("Goal" :use ((:instance closed-if-all-outside-avoidable (s (singleton x)))
                        (:instance hausdorff-singleton-avoidable (y (all-outside-avoidable-witness (singleton x) tp))))
           :in-theory (e/d (all-outside-avoidable subset) (closed closed-if-all-outside-avoidable hausdorff-singleton-avoidable))))
  :props (zfc diff$prop avoiders$prop))


(zsub seppairs (y tp) p (prod2 tp tp)
      (and (in y (car p)) (equal (int2 (car p) (cdr p)) 0)))

(zsub tracepairs (y s tp) q (prod2 (powerset s) (seppairs y tp))
      (equal (car q) (int2 (cdr (cdr q)) s)))

(defund trace-cover (y s tp) (domain (tracepairs y s tp)))

(defthmz in-tracepairs-elim
  (implies (in (cons u p) (tracepairs y s tp))
           (and (in p (seppairs y tp))
                (consp p)
                (in (car p) tp)
                (in (cdr p) tp)
                (in y (car p))
                (equal (int2 (car p) (cdr p)) 0)
                (equal (int2 (cdr p) s) u)))
  :rule-classes nil
  :props (zfc prod2$prop seppairs$prop tracepairs$prop))

(defthmz in-tracepairs-elim-x
  (implies (and (in (cons u p) (tracepairs y s tp))
                (in x u))
           (in x (cdr p)))
  :hints (("Goal" :use in-tracepairs-elim :in-theory (disable tracepairs$comprehension)))
  :rule-classes nil
  :props (zfc prod2$prop seppairs$prop tracepairs$prop diff$prop))

(defthmz subset-trace-cover-subspace
  (subset (trace-cover y s tp) (subspace s tp))
  :hints (("Goal" :in-theory (e/d (trace-cover) (tracepairs$comprehension))
           :expand ((subset (domain (tracepairs y s tp)) (subspace s tp)))
           :use ((:instance in-tracepairs-elim
                            (u (subset-witness (domain (tracepairs y s tp)) (subspace s tp)))
                            (p (apply (tracepairs y s tp) (subset-witness (domain (tracepairs y s tp)) (subspace s tp)))))
                 (:instance in-subspace-suff
                            (s2 (subset-witness (domain (tracepairs y s tp)) (subspace s tp)))
                            (w (cdr (apply (tracepairs y s tp) (subset-witness (domain (tracepairs y s tp)) (subspace s tp)))))))))
  :props (zfc prod2$prop seppairs$prop tracepairs$prop diff$prop domain$prop subspace-fn$prop))

(defthmz subset-int2-right
  (subset (int2 a b) b)
  :hints (("Goal" :expand ((subset (int2 a b) b))))
  :props (zfc diff$prop))

(defthmz in-union-trace-cover
  (implies (and (hausdorff tp) (subset s (union tp)) (in y (union tp)) (not (in y s)) (in x s))
           (in x (union (trace-cover y s tp))))
  :hints (("Goal" :in-theory (e/d (trace-cover point-point-separable)
                                  (hausdorff-necc in-in-suff in-car-domain in-car-domain-alt))
           :use ((:instance subset-preserves-in-1 (a x) (x s) (y (union tp)))
                 (:instance hausdorff-necc (x y) (y x))
                 (:instance in-car-domain
                            (p (cons (int2 (mv-nth 1 (point-point-separable-witness y x tp)) s)
                                     (cons (mv-nth 0 (point-point-separable-witness y x tp))
                                           (mv-nth 1 (point-point-separable-witness y x tp)))))
                            (r (tracepairs y s tp)))
                 (:instance in-in-suff (a x) (x (domain (tracepairs y s tp)))
                            (y (int2 (mv-nth 1 (point-point-separable-witness y x tp)) s))))))
  :props (zfc prod2$prop seppairs$prop tracepairs$prop diff$prop domain$prop))

(defthmz open-cover-trace-cover
  (implies (and (tpp tp) (hausdorff tp) (subset s (union tp)) (in y (union tp)) (not (in y s)))
           (open-cover (trace-cover y s tp) (subspace s tp)))
  :hints (("Goal" :in-theory (e/d (open-cover) (in-union-trace-cover union-monotone))
           :use ((:instance union-monotone (s1 (trace-cover y s tp)) (s2 (subspace s tp)))
                 (:instance in-union-trace-cover (x (subset-witness s (union (trace-cover y s tp)))))
                 (:instance extensionality (x (union (trace-cover y s tp))) (y s)))
           :expand ((subset s (union (trace-cover y s tp))))))
  :props (zfc prod2$prop seppairs$prop tracepairs$prop diff$prop domain$prop subspace-fn$prop))

(defund tfsc (y s tp)
  (exists-finite-subcover-witness (trace-cover y s tp) (subspace s tp)))

(defthmz tfsc-props
  (implies (and (tpp tp) (hausdorff tp) (subset s (union tp)) (in y (union tp)) (not (in y s))
                (compact (subspace s tp)))
           (and (equal (union (tfsc y s tp)) s)
                (subset (tfsc y s tp) (trace-cover y s tp))
                (finite (tfsc y s tp))))
  :hints (("Goal" :in-theory (e/d (tfsc exists-finite-subcover) (compact-necc open-cover))
           :use (open-cover-trace-cover
                 (:instance compact-necc (c (trace-cover y s tp)) (tp (subspace s tp))))))
  :rule-classes nil
  :props (zfc prod2$prop seppairs$prop tracepairs$prop diff$prop domain$prop subspace-fn$prop))

(defund tg (y s tp)
  (image (restrict (skolem (tracepairs y s tp)) (tfsc y s tp))))

(defund tw (y s tp) (intersection (domain (tg y s tp))))

(defthmz in-tg-implies
  (implies (in p (tg y s tp))
           (and (in p (seppairs y tp))
                (consp p)
                (in (car p) tp)
                (in y (car p))
                (equal (int2 (car p) (cdr p)) 0)))
  :hints (("Goal" :in-theory (e/d (tg restrict$comprehension) (in-image-necc tracepairs$comprehension
                                                                 seppairs$comprehension))
           :use ((:instance in-image-rewrite (x p)
                            (r (restrict (skolem (tracepairs y s tp)) (tfsc y s tp))))
                 (:instance subset-preserves-in-1
                            (a (cons (apply (inverse (restrict (skolem (tracepairs y s tp)) (tfsc y s tp))) p) p))
                            (x (skolem (tracepairs y s tp)))
                            (y (tracepairs y s tp)))
                 (:instance in-tracepairs-elim
                            (u (apply (inverse (restrict (skolem (tracepairs y s tp)) (tfsc y s tp))) p))))))
  :rule-classes nil
  :props (zfc prod2$prop domain$prop inverse$prop seppairs$prop tracepairs$prop skolem$prop restrict$prop))

(defthmz relation-p-tg
  (relation-p (tg y s tp))
  :hints (("Goal" :expand ((relation-p (tg y s tp)))
           :use ((:instance in-tg-implies (p (relation-p-witness (tg y s tp)))))))
  :props (zfc prod2$prop domain$prop inverse$prop seppairs$prop tracepairs$prop skolem$prop restrict$prop))

(defthmz in-domain-tg-implies
  (implies (in a (domain (tg y s tp)))
           (and (in a tp) (in y a)))
  :hints (("Goal" :in-theory (disable in-cons-apply)
           :use ((:instance in-cons-apply (x a) (f (tg y s tp)))
                 (:instance in-tg-implies (p (cons a (apply (tg y s tp) a)))))))
  :props (zfc prod2$prop domain$prop inverse$prop seppairs$prop tracepairs$prop skolem$prop restrict$prop))

(defthmz finite-domain-tg
  (implies (finite (tfsc y s tp))
           (finite (domain (tg y s tp))))
  :hints (("Goal" :in-theory (enable tg)
           :use ((:instance finite-implies-finite-domain (f (tg y s tp))))))
  :props (zfc prod2$prop domain$prop inverse$prop seppairs$prop tracepairs$prop skolem$prop
              zfns-prop phoenix$prop identity-fun$prop compose$prop swap$prop
              restrict$prop rcompose$prop diff$prop))

(defthmz skolem-trace-in-tracepairs
  (implies (and (in u (tfsc y s tp))
                (subset (tfsc y s tp) (trace-cover y s tp)))
           (in (cons u (apply (skolem (tracepairs y s tp)) u)) (tracepairs y s tp)))
  :hints (("Goal" :in-theory (e/d (trace-cover) (skolem-skolemizes tracepairs$comprehension))
           :use ((:instance skolem-skolemizes (x u) (r (tracepairs y s tp)))
                 (:instance subset-preserves-in-1 (a u) (x (tfsc y s tp)) (y (trace-cover y s tp))))))
  :rule-classes nil
  :props (zfc prod2$prop domain$prop inverse$prop seppairs$prop tracepairs$prop skolem$prop))

(defthmz skolem-trace-in-tg
  (implies (and (in u (tfsc y s tp))
                (subset (tfsc y s tp) (trace-cover y s tp)))
           (in (apply (skolem (tracepairs y s tp)) u) (tg y s tp)))
  :hints (("Goal" :in-theory (e/d (tg trace-cover) (in-apply-image in-apply-image-force domain-restrict-3))
           :use ((:instance subset-preserves-in-1 (a u) (x (tfsc y s tp)) (y (trace-cover y s tp)))
                 (:instance domain-restrict-3 (x u) (f (skolem (tracepairs y s tp))) (s (tfsc y s tp)))
                 (:instance in-apply-image
                            (r (restrict (skolem (tracepairs y s tp)) (tfsc y s tp)))
                            (x u)))))
  :props (zfc prod2$prop domain$prop inverse$prop seppairs$prop tracepairs$prop skolem$prop restrict$prop diff$prop))

(defthmz tg-pair-for-x
  (implies (and (in x (union (tfsc y s tp)))
                (subset (tfsc y s tp) (trace-cover y s tp)))
           (and (in (apply (skolem (tracepairs y s tp)) (in-in-witness x (tfsc y s tp))) (tg y s tp))
                (in x (cdr (apply (skolem (tracepairs y s tp)) (in-in-witness x (tfsc y s tp)))))))
  :hints (("Goal" :in-theory (e/d (in-union) (skolem-trace-in-tg))
           :expand ((in-in x (tfsc y s tp)))
           :use ((:instance skolem-trace-in-tg (u (in-in-witness x (tfsc y s tp))))
                 (:instance skolem-trace-in-tracepairs (u (in-in-witness x (tfsc y s tp))))
                 (:instance in-tracepairs-elim-x (u (in-in-witness x (tfsc y s tp)))
                            (p (apply (skolem (tracepairs y s tp)) (in-in-witness x (tfsc y s tp))))))))
  :rule-classes nil
  :props (zfc prod2$prop domain$prop inverse$prop seppairs$prop tracepairs$prop skolem$prop restrict$prop diff$prop))

(defthmz not-in-tw
  (implies (and (in x (union (tfsc y s tp)))
                (subset (tfsc y s tp) (trace-cover y s tp)))
           (not (in x (tw y s tp))))
  :hints (("Goal" :in-theory (e/d (tw intersection$comprehension-improved)
                                  (in-car-domain in-car-domain-alt in-all-necc int2-non-empty))
           :use (tg-pair-for-x
                 (:instance in-tg-implies (p (apply (skolem (tracepairs y s tp)) (in-in-witness x (tfsc y s tp)))))
                 (:instance in-car-domain (p (apply (skolem (tracepairs y s tp)) (in-in-witness x (tfsc y s tp))))
                            (r (tg y s tp)))
                 (:instance in-all-necc (s (domain (tg y s tp)))
                            (y (car (apply (skolem (tracepairs y s tp)) (in-in-witness x (tfsc y s tp))))))
                 (:instance int2-non-empty (a x)
                            (x (car (apply (skolem (tracepairs y s tp)) (in-in-witness x (tfsc y s tp)))))
                            (y (cdr (apply (skolem (tracepairs y s tp)) (in-in-witness x (tfsc y s tp)))))))))
  :props (zfc prod2$prop domain$prop inverse$prop seppairs$prop tracepairs$prop skolem$prop restrict$prop diff$prop
              intersection$prop))

(defthmz in-y-tw
  (implies (and (not (equal (union (tfsc y s tp)) 0))
                (subset (tfsc y s tp) (trace-cover y s tp)))
           (in y (tw y s tp)))
  :hints (("Goal" :in-theory (e/d (tw intersection$comprehension-improved)
                                  (in-car-domain in-car-domain-alt in-domain-tg-implies))
           :expand ((in-all y (domain (tg y s tp))))
           :use ((:instance min-in-1 (z (union (tfsc y s tp))))
                 (:instance tg-pair-for-x (x (min-in (union (tfsc y s tp)))))
                 (:instance in-tg-implies (p (apply (skolem (tracepairs y s tp)) (in-in-witness (min-in (union (tfsc y s tp))) (tfsc y s tp)))))
                 (:instance in-car-domain (p (apply (skolem (tracepairs y s tp)) (in-in-witness (min-in (union (tfsc y s tp))) (tfsc y s tp))))
                            (r (tg y s tp)))
                 (:instance in-domain-tg-implies (a (in-all-witness y (domain (tg y s tp))))))))
  :props (zfc prod2$prop domain$prop inverse$prop seppairs$prop tracepairs$prop skolem$prop restrict$prop diff$prop
              intersection$prop))

(defthmz tw-in-tp
  (implies (and (tpp tp) (finite (tfsc y s tp)))
           (in (tw y s tp) tp))
  :hints (("Goal" :in-theory (e/d (tw) (finite-intersection-closure))
           :expand ((subset (domain (tg y s tp)) tp))
           :use ((:instance finite-intersection-closure (ss (domain (tg y s tp))))
                 (:instance in-domain-tg-implies (a (subset-witness (domain (tg y s tp)) tp))))))
  :props (zfc prod2$prop domain$prop inverse$prop seppairs$prop tracepairs$prop skolem$prop
              zfns-prop phoenix$prop identity-fun$prop compose$prop swap$prop
              restrict$prop rcompose$prop diff$prop intersection$prop))

(defthmz int2-tw-s
  (implies (and (equal (union (tfsc y s tp)) s)
                (subset (tfsc y s tp) (trace-cover y s tp)))
           (equal (int2 (tw y s tp) s) 0))
  :hints (("Goal" :in-theory (disable not-in-tw)
           :use ((:instance min-in-1 (z (int2 (tw y s tp) s)))
                 (:instance not-in-tw (x (min-in (int2 (tw y s tp) s)))))))
  :props (zfc prod2$prop domain$prop inverse$prop seppairs$prop tracepairs$prop skolem$prop restrict$prop diff$prop
              intersection$prop))

(defthmz int2-x-0
  (equal (int2 x 0) 0)
  :hints (("Goal" :use ((:instance min-in-1 (z (int2 x 0))))))
  :props (zfc diff$prop))

(defthmz compact-subset-avoidable
  (implies (and (tpp tp) (hausdorff tp) (subset s (union tp))
                (compact (subspace s tp))
                (in y (union tp)) (not (in y s)))
           (exists-avoider y s tp))
  :hints (("Goal" :cases ((equal s 0)))
          ("Subgoal 2" :in-theory (disable exists-avoider-suff tw-in-tp in-y-tw int2-tw-s)
           :use (tfsc-props tw-in-tp in-y-tw int2-tw-s
                 (:instance exists-avoider-suff (w (tw y s tp)))))
          ("Subgoal 1" :in-theory (disable exists-avoider-suff)
           :use ((:instance exists-avoider-suff (w (union tp))))))
  :props (zfc prod2$prop domain$prop inverse$prop seppairs$prop tracepairs$prop skolem$prop
              zfns-prop phoenix$prop identity-fun$prop compose$prop swap$prop
              restrict$prop rcompose$prop diff$prop intersection$prop subspace-fn$prop))

(defthmz compact-subset-of-hausdorff-is-closed
  (implies (and (tpp tp) (hausdorff tp) (subset s (union tp))
                (compact (subspace s tp)))
           (closed s tp))
  :hints (("Goal" :in-theory (e/d (all-outside-avoidable) (closed closed-if-all-outside-avoidable compact-subset-avoidable))
           :use (closed-if-all-outside-avoidable
                 (:instance compact-subset-avoidable (y (all-outside-avoidable-witness s tp))))))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop subspace-fn$prop
              avoiders$prop seppairs$prop tracepairs$prop skolem$prop
              zfns-prop phoenix$prop identity-fun$prop compose$prop swap$prop
              restrict$prop rcompose$prop intersection$prop))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Theorem 2: continuous-image-of-compact.  Pull back an open cover c of tp2
;;; to the cover of preimages, take a finite subcover, and push it forward by
;;; choosing for each chosen preimage a member of c that it came from.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(zsub prepairs (f c tp1) p (prod2 c tp1) (equal (cdr p) (preimage f (car p))))

(defund pre-cover (f c tp1) (image (prepairs f c tp1)))

(defthmz subset-pre-cover
  (subset (pre-cover f c tp1) tp1)
  :hints (("Goal" :in-theory (enable pre-cover)
           :use ((:instance subset-image (r (prepairs f c tp1)) (a c) (b tp1)))))
  :props (zfc prod2$prop domain$prop inverse$prop prepairs$prop))

(defthmz in-pre-cover-suff
  (implies (and (in v c) (in (preimage f v) tp1))
           (in (preimage f v) (pre-cover f c tp1)))
  :hints (("Goal" :in-theory (enable pre-cover)
           :use ((:instance in-image-suff (p (cons v (preimage f v))) (r (prepairs f c tp1))
                            (y (preimage f v))))))
  :props (zfc prod2$prop domain$prop inverse$prop prepairs$prop))

(defthmz in-union-pre-cover
  (implies (and (continuous f tp1 tp2) (open-cover c tp2)
                (in x (union tp1)))
           (in x (union (pre-cover f c tp1))))
  :hints (("Goal" :in-theory (e/d (in-union) (preimages-open-necc in-in-suff))
           :expand ((in-in (apply f x) c))
           :use ((:instance in-apply-image (r f))
                 (:instance subset-preserves-in-1 (a (apply f x)) (x (image f)) (y (union c)))
                 (:instance preimages-open-necc (v (in-in-witness (apply f x) c)))
                 (:instance in-pre-cover-suff (v (in-in-witness (apply f x) c)))
                 (:instance in-in-suff (a x) (x (pre-cover f c tp1))
                            (y (preimage f (in-in-witness (apply f x) c)))))))
  :props (zfc prod2$prop domain$prop inverse$prop prepairs$prop preimage$prop))

(defthmz open-cover-pre-cover
  (implies (and (continuous f tp1 tp2) (open-cover c tp2))
           (open-cover (pre-cover f c tp1) tp1))
  :hints (("Goal" :in-theory (e/d (open-cover) (continuous in-union-pre-cover union-monotone))
           :use ((:instance extensionality (x (union (pre-cover f c tp1))) (y (union tp1)))
                 (:instance union-monotone (s1 (pre-cover f c tp1)) (s2 tp1))
                 (:instance in-union-pre-cover (x (subset-witness (union tp1) (union (pre-cover f c tp1))))))
           :expand ((subset (union tp1) (union (pre-cover f c tp1))))))
  :props (zfc prod2$prop domain$prop inverse$prop prepairs$prop preimage$prop))

(defund img-cover (f c tp1)
  (image (restrict (skolem (inverse (prepairs f c tp1)))
                   (exists-finite-subcover-witness (pre-cover f c tp1) tp1))))

(defthmz finite-img-cover
  (implies (finite (exists-finite-subcover-witness (pre-cover f c tp1) tp1))
           (finite (img-cover f c tp1)))
  :hints (("Goal" :in-theory (enable img-cover)))
  :props (zfc skolem$prop zfns-prop phoenix$prop identity-fun$prop compose$prop swap$prop
              restrict$prop rcompose$prop diff$prop))

(defthmz in-img-cover-implies
  (implies (in v (img-cover f c tp1))
           (in v c))
  :hints (("Goal" :in-theory (e/d (img-cover restrict$comprehension in-inverse) (in-image-necc))
           :use ((:instance in-image-rewrite (x v)
                            (r (restrict (skolem (inverse (prepairs f c tp1)))
                                         (exists-finite-subcover-witness (pre-cover f c tp1) tp1))))
                 (:instance subset-preserves-in-1
                            (a (cons (apply (inverse (restrict (skolem (inverse (prepairs f c tp1)))
                                         (exists-finite-subcover-witness (pre-cover f c tp1) tp1))) v) v))
                            (x (skolem (inverse (prepairs f c tp1))))
                            (y (inverse (prepairs f c tp1)))))))
  :props (zfc prod2$prop domain$prop inverse$prop prepairs$prop skolem$prop restrict$prop))

;; u in pre-cover: the skolem choice v satisfies u = (preimage f v), v in img-cover
(defthmz in-inverse-prepairs
  (implies (in (cons u v) (inverse (prepairs f c tp1)))
           (and (equal (preimage f v) u)
                (in v c)
                (in u tp1)))
  :rule-classes nil
  :props (zfc prod2$prop inverse$prop prepairs$prop))

(defthmz skolem-prepairs-choice
  (implies (in u (pre-cover f c tp1))
           (equal (preimage f (apply (skolem (inverse (prepairs f c tp1))) u))
                  u))
  :hints (("Goal" :in-theory (e/d (pre-cover image) (skolem-skolemizes in-inverse prepairs$comprehension))
           :use ((:instance skolem-skolemizes (x u) (r (inverse (prepairs f c tp1))))
                 (:instance in-inverse-prepairs (v (apply (skolem (inverse (prepairs f c tp1))) u))))))
  :props (zfc prod2$prop domain$prop inverse$prop prepairs$prop skolem$prop))

(defthmz skolem-prepairs-in-img-cover
  (implies (and (in u (exists-finite-subcover-witness (pre-cover f c tp1) tp1))
                (subset (exists-finite-subcover-witness (pre-cover f c tp1) tp1)
                        (pre-cover f c tp1)))
           (in (apply (skolem (inverse (prepairs f c tp1))) u)
               (img-cover f c tp1)))
  :hints (("Goal" :in-theory (e/d (img-cover pre-cover) (in-apply-image in-apply-image-force domain-restrict-3))
           :use ((:instance domain-restrict-3 (x u) (f (skolem (inverse (prepairs f c tp1))))
                            (s (exists-finite-subcover-witness (pre-cover f c tp1) tp1)))
                 (:instance in-apply-image
                            (r (restrict (skolem (inverse (prepairs f c tp1)))
                                         (exists-finite-subcover-witness (pre-cover f c tp1) tp1)))
                            (x u)))))
  :props (zfc prod2$prop domain$prop inverse$prop prepairs$prop skolem$prop restrict$prop diff$prop))

(defthmz apply-in-skolem-prepairs
  (implies (and (in u (pre-cover f c tp1))
                (in x0 u))
           (in (apply f x0) (apply (skolem (inverse (prepairs f c tp1))) u)))
  :hints (("Goal" :use ((:instance preimage$comprehension (x x0)
                            (v (apply (skolem (inverse (prepairs f c tp1))) u))))
                  :in-theory (disable preimage$comprehension)))
  :props (zfc prod2$prop domain$prop inverse$prop prepairs$prop skolem$prop preimage$prop))

(defthmz apply-when-in-funp
  (implies (and (funp f) (in (cons x y) f))
           (equal (apply f x) y))
  :hints (("Goal" :use ((:instance apply-intro-lemma (p (cons x y)))))))

(defthmz cover-img-cover-1
  (implies (and (funp f)
                (in (cons x0 y) f)
                (in x0 (union (exists-finite-subcover-witness (pre-cover f c tp1) tp1)))
                (subset (exists-finite-subcover-witness (pre-cover f c tp1) tp1) (pre-cover f c tp1)))
           (in y (union (img-cover f c tp1))))
  :hints (("Goal" :in-theory (e/d (in-union) (in-in-suff skolem-prepairs-choice skolem-prepairs-in-img-cover
                                               apply-in-skolem-prepairs))
           :expand ((in-in x0 (exists-finite-subcover-witness (pre-cover f c tp1) tp1)))
           :use ((:instance subset-preserves-in-1 (a (in-in-witness x0 (exists-finite-subcover-witness (pre-cover f c tp1) tp1)))
                            (x (exists-finite-subcover-witness (pre-cover f c tp1) tp1)) (y (pre-cover f c tp1)))
                                  (:instance apply-in-skolem-prepairs (u (in-in-witness x0 (exists-finite-subcover-witness (pre-cover f c tp1) tp1))))
                 (:instance skolem-prepairs-in-img-cover (u (in-in-witness x0 (exists-finite-subcover-witness (pre-cover f c tp1) tp1))))
                 (:instance in-in-suff (a y) (x (img-cover f c tp1))
                            (y (apply (skolem (inverse (prepairs f c tp1))) (in-in-witness x0 (exists-finite-subcover-witness (pre-cover f c tp1) tp1))))))))
  :props (zfc prod2$prop domain$prop inverse$prop prepairs$prop skolem$prop restrict$prop diff$prop preimage$prop))

(defthmz fsc-props
  (implies (and (continuous f tp1 tp2) (open-cover c tp2) (compact tp1))
           (and (equal (union (exists-finite-subcover-witness (pre-cover f c tp1) tp1)) (union tp1))
                (subset (exists-finite-subcover-witness (pre-cover f c tp1) tp1) (pre-cover f c tp1))
                (finite (exists-finite-subcover-witness (pre-cover f c tp1) tp1))))
  :hints (("Goal" :in-theory (e/d (exists-finite-subcover) (compact-necc continuous open-cover))
           :use (open-cover-pre-cover
                 (:instance compact-necc (c (pre-cover f c tp1)) (tp tp1)))))
  :rule-classes nil
  :props (zfc prod2$prop domain$prop inverse$prop prepairs$prop preimage$prop))

(defthmz cover-img-cover-2
  (implies (and (continuous f tp1 tp2) (open-cover c tp2) (compact tp1)
                (in y (image f)))
           (in y (union (img-cover f c tp1))))
  :hints (("Goal" :in-theory (e/d () (cover-img-cover-1 open-cover in-car-domain))
           :use (fsc-props
                 (:instance in-image-rewrite (x y) (r f))
                 (:instance in-car-domain (p (cons (apply (inverse f) y) y)) (r f))
                 (:instance cover-img-cover-1 (x0 (apply (inverse f) y))))))
  :props (zfc prod2$prop domain$prop inverse$prop prepairs$prop skolem$prop restrict$prop diff$prop preimage$prop))

(defthmz subset-img-cover
  (subset (img-cover f c tp1) c)
  :hints (("Goal" :expand ((subset (img-cover f c tp1) c))))
  :props (zfc prod2$prop domain$prop inverse$prop prepairs$prop skolem$prop restrict$prop))

(defthmz union-img-cover
  (implies (and (continuous f tp1 tp2) (open-cover c tp2) (compact tp1)
                (equal (image f) (union tp2)))
           (equal (union (img-cover f c tp1)) (union tp2)))
  :hints (("Goal" :in-theory (e/d (open-cover) (cover-img-cover-2 union-monotone continuous))
           :use ((:instance union-monotone (s1 (img-cover f c tp1)) (s2 c))
                 (:instance cover-img-cover-2 (y (subset-witness (union tp2) (union (img-cover f c tp1)))))
                 (:instance extensionality (x (union (img-cover f c tp1))) (y (union tp2))))
           :expand ((subset (union tp2) (union (img-cover f c tp1))))))
  :props (zfc prod2$prop domain$prop inverse$prop prepairs$prop skolem$prop restrict$prop diff$prop preimage$prop))

(defthmz continuous-image-of-compact
  (implies (and (tpp tp1) (tpp tp2) (compact tp1) (continuous f tp1 tp2)
                (equal (image f) (union tp2)))
           (compact tp2))
  :hints (("Goal" :in-theory (e/d (compact) (continuous union-img-cover finite-img-cover exists-finite-subcover-suff))
           :use ((:instance union-img-cover (c (compact-witness tp2)))
                 (:instance fsc-props (c (compact-witness tp2)))
                 (:instance finite-img-cover (c (compact-witness tp2)))
                 (:instance exists-finite-subcover-suff (c2 (img-cover f (compact-witness tp2) tp1))
                            (c (compact-witness tp2)) (tp tp2)))))
  :props (zfc prod2$prop domain$prop inverse$prop preimage$prop
              prepairs$prop skolem$prop restrict$prop diff$prop
              zfns-prop phoenix$prop identity-fun$prop compose$prop swap$prop rcompose$prop))
