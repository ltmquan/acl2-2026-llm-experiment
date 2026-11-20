(in-package "ZF")

(include-book "defs")
(local (include-book "arithmetic/top-with-meta" :dir :system))
(in-theory (disable has-ball ball-inside metric-open-p dr-valued metric-axioms))

(defthmz in-metric-topology
  (equal (in u (metric-topology d x))
         (and (subset u x) (metric-open-p u d x)))
  :props (zfc metric-topology$prop))

(defthmz ball-inside-self
  (ball-inside x a eps d x)
  :hints (("Goal" :in-theory (enable ball-inside))))

(defthmz metric-open-p-self
  (metric-open-p x d x)
  :hints (("Goal" :in-theory (enable metric-open-p)
           :use ((:instance has-ball-suff (u x) (a (metric-open-p-witness x d x))
                            (eps 1))))))

(defthmz subset-self
  (subset x x)
  :hints (("Goal" :in-theory (enable subset))))

(defthmz x-in-metric-topology
  (in x (metric-topology d x))
  :props (zfc metric-topology$prop))

(defthmz subset-union-metric-topology
  (subset (union (metric-topology d x)) x)
  :props (zfc metric-topology$prop)
  :hints (("Goal" :expand ((subset (union (metric-topology d x)) x)
                           (in-in (subset-witness (union (metric-topology d x)) x)
                                  (metric-topology d x)))
           :in-theory (enable subset-necc))))

(defthmz union-metric-topology
  (equal (union (metric-topology d x)) x)
  :props (zfc metric-topology$prop)
  :hints (("Goal" :in-theory (enable extensionality-rewrite)
           :use ((:instance in-implies-subset-union (x x) (s (metric-topology d x)))))))


;; shrinking/growing radius
(defthmz ball-inside-smaller
  (implies (and (dr-valued d x) (in a x)
                (ball-inside u a e1 d x)
                (rationalp e) (<= e e1))
           (ball-inside u a e d x))
  :hints (("Goal" :expand ((ball-inside u a e d x))
           :in-theory (enable drp)
           :use ((:instance ball-inside-necc (eps e1) (b (ball-inside-witness u a e d x)))
                 (:instance dr-valued-necc (b (ball-inside-witness u a e d x)))
                 (:instance dr-closed-downward-necc (x e) (y e1)
                            (s (apply d (cons a (ball-inside-witness u a e d x))))))))
  :props (zfc))

(defthmz ball-inside-subset
  (implies (and (ball-inside u a e d x) (subset u v))
           (ball-inside v a e d x))
  :hints (("Goal" :expand ((ball-inside v a e d x))
           :use ((:instance ball-inside-necc (eps e) (b (ball-inside-witness v a e d x))))))
  :props (zfc))

(defthmz subset-int2-left
  (subset (int2 u v) u)
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc diff$prop))

(defthmz subset-int2-right
  (subset (int2 u v) v)
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc diff$prop))

(defthmz ball-inside-int2
  (implies (and (ball-inside u a e d x) (ball-inside v a e d x))
           (ball-inside (int2 u v) a e d x))
  :hints (("Goal" :expand ((ball-inside (int2 u v) a e d x))
           :use ((:instance ball-inside-necc (eps e) (b (ball-inside-witness (int2 u v) a e d x)))
                 (:instance ball-inside-necc (u v) (eps e) (b (ball-inside-witness (int2 u v) a e d x))))))
  :props (zfc diff$prop))

(defthmz has-ball-int2
  (implies (and (dr-valued d x) (in a x)
                (has-ball u a d x) (has-ball v a d x))
           (has-ball (int2 u v) a d x))
  :hints (("Goal" :expand ((has-ball u a d x) (has-ball v a d x))
           :cases ((<= (has-ball-witness u a d x) (has-ball-witness v a d x))))
          ("Subgoal 2"
           :use ((:instance has-ball-suff (u (int2 u v)) (eps (has-ball-witness v a d x)))
                 (:instance ball-inside-smaller (e (has-ball-witness v a d x))
                            (e1 (has-ball-witness u a d x)))))
          ("Subgoal 1"
           :use ((:instance has-ball-suff (u (int2 u v)) (eps (has-ball-witness u a d x)))
                 (:instance ball-inside-smaller (u v) (e (has-ball-witness u a d x))
                            (e1 (has-ball-witness v a d x))))))
  :props (zfc diff$prop))

(defthmz subset-transitive-local
  (implies (and (subset a b) (subset b c)) (subset a c))
  :hints (("Goal" :expand ((subset a c))
           :use ((:instance subset-necc (x a) (y b) (a (subset-witness a c)))
                 (:instance subset-necc (x b) (y c) (a (subset-witness a c)))))))

(defthmz metric-open-p-int2
  (implies (and (dr-valued d x) (subset u x)
                (metric-open-p u d x) (metric-open-p v d x))
           (metric-open-p (int2 u v) d x))
  :hints (("Goal" :expand ((metric-open-p (int2 u v) d x))
           :use ((:instance metric-open-p-necc (a (metric-open-p-witness (int2 u v) d x)))
                 (:instance metric-open-p-necc (u v) (a (metric-open-p-witness (int2 u v) d x)))
                 (:instance subset-necc (x u) (y x) (a (metric-open-p-witness (int2 u v) d x))))))
  :props (zfc diff$prop))

(defthmz tpp-int2-metric-topology
  (implies (dr-valued d x)
           (tpp-int2 (metric-topology d x)))
  :hints (("Goal" :expand ((tpp-int2 (metric-topology d x)))
           :use ((:instance subset-transitive-local
                            (a (int2 (mv-nth 0 (tpp-int2-witness (metric-topology d x)))
                                     (mv-nth 1 (tpp-int2-witness (metric-topology d x)))))
                            (b (mv-nth 0 (tpp-int2-witness (metric-topology d x))))
                            (c x)))))
  :props (zfc diff$prop metric-topology$prop))


(defthmz union-subset-x
  (implies (subset tp2 (metric-topology d x))
           (subset (union tp2) x))
  :hints (("Goal" :expand ((subset (union tp2) x)
                           (in-in (subset-witness (union tp2) x) tp2))
           :use ((:instance subset-necc (x tp2) (y (metric-topology d x))
                            (a (in-in-witness (subset-witness (union tp2) x) tp2)))
                 (:instance subset-necc (x (in-in-witness (subset-witness (union tp2) x) tp2))
                            (y x) (a (subset-witness (union tp2) x))))))
  :props (zfc metric-topology$prop))

(defthmz has-ball-union-1
  (implies (and (in y tp2) (has-ball y a d x))
           (has-ball (union tp2) a d x))
  :hints (("Goal" :expand ((has-ball y a d x))
           :use ((:instance has-ball-suff (u (union tp2)) (eps (has-ball-witness y a d x)))
                 (:instance ball-inside-subset (u y) (v (union tp2))
                            (e (has-ball-witness y a d x)))
                 (:instance in-implies-subset-union (x y) (s tp2)))))
  :props (zfc))

(defthmz metric-open-p-union
  (implies (subset tp2 (metric-topology d x))
           (metric-open-p (union tp2) d x))
  :hints (("Goal" :expand ((metric-open-p (union tp2) d x)
                           (in-in (metric-open-p-witness (union tp2) d x) tp2))
           :use ((:instance subset-necc (x tp2) (y (metric-topology d x))
                            (a (in-in-witness (metric-open-p-witness (union tp2) d x) tp2)))
                 (:instance metric-open-p-necc
                            (u (in-in-witness (metric-open-p-witness (union tp2) d x) tp2))
                            (a (metric-open-p-witness (union tp2) d x)))
                 (:instance has-ball-union-1
                            (y (in-in-witness (metric-open-p-witness (union tp2) d x) tp2))
                            (a (metric-open-p-witness (union tp2) d x))))))
  :props (zfc metric-topology$prop))

(defthmz tpp-union-metric-topology
  (tpp-union (metric-topology d x))
  :hints (("Goal" :expand ((tpp-union (metric-topology d x)))))
  :props (zfc metric-topology$prop))

(defthmz metric-topology-is-topology
  (implies (metric-p d x)
           (and (tpp (metric-topology d x))
                (equal (union (metric-topology d x)) x)))
  :hints (("Goal" :in-theory (enable tpp)))
  :props (zfc prod2$prop diff$prop metric-topology$prop))


(defthmz drp-dist
  (implies (and (dr-valued d x) (in a x) (in b x))
           (drp (apply d (cons a b))))
  :hints (("Goal" :use dr-valued-necc)))

(defthmz lt-of-not-in
  (implies (and (drp s) (in r s) (rationalp e) (not (in e s)))
           (< r e))
  :hints (("Goal" :in-theory (enable drp)
           :use ((:instance dr-closed-downward-necc (x e) (y r)))))
  :rule-classes nil)

(defthmz sum-not-in
  (implies (and (drp s1) (drp s2) (rationalp e1) (rationalp e2)
                (not (in e1 s1)) (not (in e2 s2)))
           (not (in (+ e1 e2) (dr+ s1 s2))))
  :hints (("Goal" :expand ((dr-sum-p (+ e1 e2) s1 s2))
           :use ((:instance lt-of-not-in (s s1) (e e1)
                            (r (mv-nth 0 (dr-sum-p-witness (+ e1 e2) s1 s2))))
                 (:instance lt-of-not-in (s s2) (e e2)
                            (r (mv-nth 1 (dr-sum-p-witness (+ e1 e2) s1 s2)))))))
  :props (dr-sum-prop))

(defun-sk near (c a e d)
  (exists e2 (and (rationalp e2) (< e2 e) (not (in e2 (apply d (cons a c)))))))
(in-theory (disable near))

(zsub oball (a e d x) c x (near c a e d))

(defthmz in-oball
  (equal (in c (oball a e d x))
         (and (in c x) (near c a e d)))
  :props (oball$prop))

(defthmz subset-oball
  (subset (oball a e d x) x)
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc oball$prop))

;; triangle: d(a,b) subset d(a,c)+d(c,b)
(defthmz triangle
  (implies (and (metric-axioms d x) (in a x) (in b x) (in c x))
           (subset (apply d (cons a b))
                   (dr+ (apply d (cons a c)) (apply d (cons c b)))))
  :hints (("Goal" :use ((:instance metric-axioms-necc (b c) (c b)))))
  :rule-classes nil)

(defthmz not-in-dist-by-triangle
  (implies (and (metric-p d x) (in a x) (in b x) (in c x)
                (rationalp e1) (rationalp e2)
                (not (in e1 (apply d (cons a c))))
                (not (in e2 (apply d (cons c b)))))
           (not (in (+ e1 e2) (apply d (cons a b)))))
  :hints (("Goal" :use (triangle
                        (:instance sum-not-in (s1 (apply d (cons a c)))
                                   (s2 (apply d (cons c b))))
                        (:instance subset-necc (x (apply d (cons a b)))
                                   (y (dr+ (apply d (cons a c)) (apply d (cons c b))))
                                   (a (+ e1 e2))))))
  :props (dr-sum-prop)
  :rule-classes nil)

(defthmz ball-inside-oball-1
  (implies (and (metric-p d x) (in a x) (in c x) (in b x)
                (rationalp e2) (rationalp eps) (< (+ e2 eps) e)
                (not (in e2 (apply d (cons a c))))
                (not (in eps (apply d (cons c b)))))
           (in b (oball a e d x)))
  :hints (("Goal"
           :in-theory (disable metric-p)
           :use ((:instance not-in-dist-by-triangle (e1 e2) (e2 eps))
                 (:instance near-suff (e2 (+ e2 eps)) (c b)))))
  :props (dr-sum-prop oball$prop))

(defthmz ball-inside-oball
  (implies (and (metric-p d x) (in a x) (in c x)
                (rationalp e2) (rationalp eps) (< (+ e2 eps) e)
                (not (in e2 (apply d (cons a c)))))
           (ball-inside (oball a e d x) c eps d x))
  :hints (("Goal" :expand ((ball-inside (oball a e d x) c eps d x))
           :in-theory (disable metric-p)
           :use ((:instance ball-inside-oball-1
                            (b (ball-inside-witness (oball a e d x) c eps d x))))))
  :props (dr-sum-prop oball$prop))

(defthmz has-ball-oball
  (implies (and (metric-p d x) (in a x) (rationalp e) (in c (oball a e d x)))
           (has-ball (oball a e d x) c d x))
  :hints (("Goal" :expand ((near c a e d))
           :in-theory (disable metric-p in-oball)
           :use ((:instance ball-inside-oball (e2 (near-witness c a e d))
                            (eps (/ (- e (near-witness c a e d)) 2)))
                 (:instance in-oball)
                 (:instance has-ball-suff (u (oball a e d x)) (a c)
                            (eps (/ (- e (near-witness c a e d)) 2))))))
  :props (dr-sum-prop oball$prop))

(defthmz oball-open
  (implies (and (metric-p d x) (in a x) (rationalp e))
           (in (oball a e d x) (metric-topology d x)))
  :hints (("Goal" :in-theory (disable metric-p)
           :expand ((metric-open-p (oball a e d x) d x))))
  :props (dr-sum-prop oball$prop metric-topology$prop))


(defthmz in-r2dr-rewrite
  (equal (in q (r2dr r))
         (and (rationalp q) (< q r)))
  :props (dr-prop0))

(defun pos-pt (s)
  (dr-boundp-witness (subset-witness s (r2dr 0)) s))

(defthmz pos-pt-lemma
  (implies (and (drp s) (subset (r2dr 0) s) (not (equal s (r2dr 0))))
           (and (rationalp (pos-pt s))
                (< 0 (pos-pt s))
                (in (pos-pt s) s)))
  :hints (("Goal" :in-theory (enable drp)
           :use ((:instance dr-max-p-suff (b (subset-witness s (r2dr 0))))
                 (:instance extensionality (x s) (y (r2dr 0)))
                 (:instance subset-criterion (x s) (y (r2dr 0))))
           :expand ((dr-boundp (subset-witness s (r2dr 0)) s))))
  :props (dr-prop0)
  :rule-classes nil)

(defthmz dist-self
  (implies (and (metric-axioms d x) (in a x))
           (equal (apply d (cons a a)) (r2dr 0)))
  :hints (("Goal" :use ((:instance metric-axioms-necc (b a) (c a))))))

(defthmz dist-sym
  (implies (and (metric-axioms d x) (in a x) (in b x))
           (equal (apply d (cons b a)) (apply d (cons a b))))
  :hints (("Goal" :use ((:instance metric-axioms-necc (c a))))))

(defthmz dist-pos
  (implies (and (metric-p d x) (in a x) (in b x) (not (equal a b)))
           (let ((r (pos-pt (apply d (cons a b)))))
             (and (rationalp r) (< 0 r) (in r (apply d (cons a b))))))
  :hints (("Goal" :in-theory (disable pos-pt)
           :use ((:instance pos-pt-lemma (s (apply d (cons a b))))
                 (:instance metric-axioms-necc (c a)))))
  :props (dr-prop0)
  :rule-classes nil)

(defthmz center-in-oball
  (implies (and (metric-p d x) (in a x) (< 0 e))
           (in a (oball a e d x)))
  :hints (("Goal" :use ((:instance near-suff (c a) (e2 0)))))
  :props (dr-prop0 oball$prop))

(defthmz oballs-disjoint-1
  (implies (and (metric-p d x) (in a x) (in b x)
                (rationalp r) (in r (apply d (cons a b)))
                (<= (+ e1 e2) r)
                (in c (oball a e1 d x))
                (in c (oball b e2 d x)))
           nil)
  :hints (("Goal" :in-theory (disable dist-sym)
           :expand ((near c a e1 d) (near c b e2 d))
           :use ((:instance not-in-dist-by-triangle
                            (e1 (near-witness c a e1 d))
                            (e2 (near-witness c b e2 d)))
                 (:instance dist-sym (a c) (b b))
                 (:instance lt-of-not-in (s (apply d (cons a b)))
                            (e (+ (near-witness c a e1 d)
                                  (near-witness c b e2 d)))))))
  :props (dr-sum-prop oball$prop)
  :rule-classes nil)

(defthmz oballs-disjoint
  (implies (and (metric-p d x) (in a x) (in b x)
                (rationalp r) (in r (apply d (cons a b))))
           (equal (int2 (oball a (/ r 2) d x) (oball b (/ r 2) d x)) 0))
  :hints (("Goal" :in-theory (disable metric-p)
           :use ((:instance extensionality (x (int2 (oball a (/ r 2) d x) (oball b (/ r 2) d x)))
                            (y 0))
                 (:instance oballs-disjoint-1 (e1 (/ r 2)) (e2 (/ r 2))
                            (c (subset-witness (int2 (oball a (/ r 2) d x) (oball b (/ r 2) d x)) 0)))
                 (:instance subset-criterion (x (int2 (oball a (/ r 2) d x) (oball b (/ r 2) d x)))
                            (y 0)))))
  :props (dr-sum-prop diff$prop oball$prop))

(defthmz separable-r
  (implies (and (metric-p d x) (in a x) (in b x)
                (rationalp r) (< 0 r) (in r (apply d (cons a b))))
           (point-point-separable a b (metric-topology d x)))
  :hints (("Goal" :in-theory (disable metric-p oball-open center-in-oball oballs-disjoint)
           :use ((:instance oball-open (e (/ r 2)))
                 (:instance oball-open (a b) (e (/ r 2)))
                 (:instance center-in-oball (e (/ r 2)))
                 (:instance center-in-oball (a b) (e (/ r 2)))
                 oballs-disjoint
                 (:instance point-point-separable-suff
                            (x a) (y b) (tp (metric-topology d x))
                            (s1 (oball a (/ r 2) d x))
                            (s2 (oball b (/ r 2) d x))))))
  :props (dr-sum-prop diff$prop metric-topology$prop oball$prop))

(defthmz separable-points
  (implies (and (metric-p d x) (in a x) (in b x) (not (equal a b)))
           (point-point-separable a b (metric-topology d x)))
  :hints (("Goal" :in-theory (disable metric-p pos-pt)
           :use (dist-pos
                 (:instance separable-r (r (pos-pt (apply d (cons a b))))))))
  :props (dr-sum-prop diff$prop metric-topology$prop oball$prop))

(defthmz metric-topology-is-hausdorff
  (implies (metric-p d x) (hausdorff (metric-topology d x)))
  :hints (("Goal" :in-theory (e/d (hausdorff) (metric-p))))
  :props (dr-sum-prop diff$prop metric-topology$prop oball$prop))


(defthmz subset-r2dr-rationals
  (subset (r2dr r) (rationals))
  :hints (("Goal" :in-theory (enable subset)))
  :props (dr-prop0))

(defun qd (a b) (r2dr (abs (- a b))))

(defthmz in-cons-q-dist
  (equal (in (cons k v) (q-dist))
         (and (consp k) (rationalp (car k)) (rationalp (cdr k))
              (equal v (qd (car k) (cdr k)))))
  :props (dr-prop0 q-dist$prop))

(defthmz in-q-dist
  (implies (in p (q-dist))
           (and (consp p) (consp (car p))
                (rationalp (car (car p))) (rationalp (cdr (car p)))
                (equal (cdr p) (qd (car (car p)) (cdr (car p))))))
  :props (dr-prop0 q-dist$prop)
  :rule-classes nil)

(defthmz funp-q-dist
  (funp (q-dist))
  :hints (("Goal" :in-theory (enable funp relation-p)
           :use ((:instance in-q-dist (p (mv-nth 0 (funp-witness (q-dist)))))
                 (:instance in-q-dist (p (mv-nth 1 (funp-witness (q-dist)))))
                 (:instance in-q-dist (p (relation-p-witness (q-dist)))))))
  :props (dr-prop0 q-dist$prop))

(in-theory (disable qd))

(defthmz apply-q-dist
  (implies (and (rationalp a) (rationalp b))
           (equal (apply (q-dist) (cons a b)) (qd a b)))
  :hints (("Goal" :in-theory (disable equal-apply apply-default)
           :use ((:instance apply-intro-lemma (f (q-dist))
                                   (p (cons (cons a b) (qd a b)))))))
  :props (dr-prop0 q-dist$prop))

(defthmz domain-q-dist
  (equal (domain (q-dist)) (prod2 (rationals) (rationals)))
  :hints (("Goal" :in-theory (e/d (in-domain-rewrite) (in-cons-apply))
           :use ((:instance extensionality (x (domain (q-dist))) (y (prod2 (rationals) (rationals))))
                 (:instance subset-criterion (x (domain (q-dist))) (y (prod2 (rationals) (rationals))))
                 (:instance subset-criterion (y (domain (q-dist))) (x (prod2 (rationals) (rationals))))
                 (:instance apply-rewrite (r (q-dist))
                            (x (subset-witness (prod2 (rationals) (rationals)) (domain (q-dist))))
                            (y (qd (car (subset-witness (prod2 (rationals) (rationals)) (domain (q-dist))))
                                   (cdr (subset-witness (prod2 (rationals) (rationals)) (domain (q-dist))))))))))
  :props (dr-prop0 q-dist$prop))


(defthmz dr-valued-q-dist
  (dr-valued (q-dist) (rationals))
  :hints (("Goal" :in-theory (enable dr-valued qd)))
  :props (dr-prop0 q-dist$prop))

(defthmz qd-nonneg
  (implies (and (rationalp a) (rationalp b))
           (subset (r2dr 0) (qd a b)))
  :hints (("Goal" :in-theory (enable subset qd)))
  :props (dr-prop0))

(defthm diff-elt-not-equal
  (implies (and (in q s1) (not (in q s2))) (not (equal s1 s2)))
  :rule-classes nil)

(defthmz r2dr-pos-not-zero-1
  (implies (and (rationalp r) (< 0 r))
           (and (in 0 (r2dr r)) (not (in 0 (r2dr 0)))))
  :props (dr-prop0)
  :rule-classes nil)

(defthmz r2dr-pos-not-zero
  (implies (and (rationalp r) (< 0 r))
           (not (equal (r2dr r) (r2dr 0))))
  :hints (("Goal" :in-theory (disable in-r2dr-rewrite r2dr$comprehension)
           :use (r2dr-pos-not-zero-1)))
  :props (dr-prop0))

(defthmz qd-zero
  (implies (and (rationalp a) (rationalp b))
           (iff (equal (qd a b) (r2dr 0)) (equal a b)))
  :hints (("Goal" :in-theory (enable qd)
           :use ((:instance r2dr-pos-not-zero (r (abs (- a b)))))))
  :props (dr-prop0))

(defthmz qd-sym
  (implies (and (rationalp a) (rationalp b))
           (equal (qd b a) (qd a b)))
  :hints (("Goal" :in-theory (enable qd)
           :cases ((< a b) (= a b)))))

(defthmz qd-triangle-1
  (implies (and (rationalp a) (rationalp b) (rationalp c)
                (rationalp q) (< q (abs (- a c))))
           (in q (dr+ (qd a b) (qd b c))))
  :hints (("Goal" :in-theory (enable qd)
           :use ((:instance dr-sum-p-suff (r q) (dr1 (qd a b)) (dr2 (qd b c))
                            (r1 (- (abs (- a b)) (/ (- (+ (abs (- a b)) (abs (- b c))) q) 2)))
                            (r2 (- (abs (- b c)) (/ (- (+ (abs (- a b)) (abs (- b c))) q) 2)))))))
  :props (dr-sum-prop))

(defthmz qd-triangle
  (implies (and (rationalp a) (rationalp b) (rationalp c))
           (subset (qd a c) (dr+ (qd a b) (qd b c))))
  :hints (("Goal" :expand ((subset (qd a c) (dr+ (qd a b) (qd b c))))
           :in-theory (enable qd)
           :use ((:instance qd-triangle-1 (q (subset-witness (qd a c) (dr+ (qd a b) (qd b c))))))))
  :props (dr-sum-prop))

(defthmz metric-axioms-q-dist
  (metric-axioms (q-dist) (rationals))
  :hints (("Goal" :in-theory (enable metric-axioms)))
  :props (dr-sum-prop q-dist$prop))

(defthmz rationals-metric
  (metric-p (q-dist) (rationals))
  :props (dr-sum-prop q-dist$prop))

