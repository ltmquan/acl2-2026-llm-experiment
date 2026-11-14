(in-package "ZF")

(include-book "defs")
(defthmz eqnum-reflexive (exists-bijection s s)
  :props (zfc identity-fun$prop prod2$prop domain$prop inverse$prop)
  :hints (("Goal" :use ((:instance exists-bijection-suff (fn (identity-fun s)) (s1 s) (s2 s))))))

(defthmz eqnum-symmetric
  (implies (exists-bijection a b) (exists-bijection b a))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal" :expand ((exists-bijection a b))
           :use ((:instance exists-bijection-suff (fn (inverse (exists-bijection-witness a b))) (s1 b) (s2 a))))))

(defthmz eqnum-transitive
  (implies (and (exists-bijection a b) (exists-bijection b c))
           (exists-bijection a c))
  :props (zfc prod2$prop domain$prop inverse$prop compose$prop rcompose$prop)
  :hints (("Goal" :expand ((exists-bijection a b) (exists-bijection b c))
           :in-theory (enable bijection)
           :use ((:instance bijection-compose (f (exists-bijection-witness b c)) (g (exists-bijection-witness a b)))
                 (:instance exists-bijection-suff (fn (compose (exists-bijection-witness b c) (exists-bijection-witness a b))) (s1 a) (s2 c))))))

(defthmz injects-both-ways-implies-eqnum
  (implies (and (injects-into a b) (injects-into b a))
           (exists-bijection a b))
  :props (sbt-prop fun-bij$prop)
  :hints (("Goal" :expand ((injects-into a b) (injects-into b a))
           :use ((:instance schroeder-bernstein (f (injects-into-witness a b)) (g (injects-into-witness b a)) (s1 a) (s2 b))))))

(defthmz in-singleton-powerset
  (implies (in x s) (in (singleton x) (powerset s)))
  :hints (("Goal" :in-theory (enable subset))))

(defthmz singleton-injective
  (implies (equal (pair a a) (pair b b)) (equal a b))
  :hints (("Goal" :use ((:instance in-pair (a a) (x b) (y b))
                        (:instance in-pair (a a) (x a) (y a)))
           :in-theory (disable in-pair)))
  :rule-classes nil)

(zify zsing singleton :dom s :ran (powerset s) :args (s))

(defthmz funp-inverse-zsing
  (funp (inverse (zsing s)))
  :hints (("Goal" :expand ((funp (inverse (zsing s))))
           :in-theory (enable in-inverse zsing$comprehension in-prod2))
          ("Subgoal 2''" :use ((:instance singleton-injective
                               (a (cdr (car (funp-witness (inverse (zsing s))))))
                               (b (cdr (mv-nth 1 (funp-witness (inverse (zsing s))))))))))
  :props (zfc zsing$prop prod2$prop domain$prop inverse$prop))

(defthmz image-zsing
  (subset (image (zsing s)) (powerset s))
  :hints (("Goal" :in-theory (enable subset zsing$comprehension in-prod2)
           :use ((:instance in-image-necc (f (zsing s)) (x (subset-witness (image (zsing s)) (powerset s)))))))
  :props (zfc zsing$prop prod2$prop domain$prop inverse$prop))

(defthmz set-injects-into-powerset (injects-into s (powerset s))
  :props (zfc zsing$prop prod2$prop domain$prop inverse$prop)
  :hints (("Goal" :use ((:instance injects-into-suff (f (zsing s)) (a s) (b (powerset s)))))))

(zsub cantor-d (f s) x s (not (in x (apply (inverse f) x))))

(defthmz cantor-d-in-powerset
  (in (cantor-d f s) (powerset s))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc cantor-d$prop))

(defthmz powerset-does-not-inject-lemma
  (implies (and (injective-funp f) (equal (domain f) (powerset s)) (subset (image f) s))
           nil)
  :rule-classes nil
  :hints (("Goal" :in-theory (disable cantor-d$comprehension apply-inverse-apply)
           :use ((:instance cantor-d$comprehension (x (apply f (cantor-d f s))))
                 (:instance apply-inverse-apply (x (cantor-d f s)))
                 (:instance in-apply-image (r f) (x (cantor-d f s)))
                 (:instance subset-preserves-in-1 (a (apply f (cantor-d f s))) (x (image f)) (y s)))))
  :props (zfc cantor-d$prop prod2$prop domain$prop inverse$prop))

(defthmz powerset-does-not-inject (not (injects-into (powerset s) s))
  :props (zfc prod2$prop domain$prop inverse$prop cantor-d$prop)
  :hints (("Goal" :use ((:instance powerset-does-not-inject-lemma (f (injects-into-witness (powerset s) s)))))))

(defun pig-h (x f n)
  (declare (xargs :guard t))
  (if (equal (apply f x) (+ -1 (nfix n))) (apply f n) (apply f x)))

(defthmz in-plus-1-n
  (implies (and (natp n) (in x n)) (in x (+ 1 n)))
  :hints (("Goal" :in-theory (enable in-natp))))

(defthmz in-n-plus-1-n
  (implies (natp n) (in n (+ 1 n)))
  :hints (("Goal" :in-theory (enable in-natp))))

(defthmz apply-in-codomain
  (implies (and (in x (domain f)) (subset (image f) s))
           (in (apply f x) s))
  :hints (("Goal" :use ((:instance in-apply-image (r f) (x x))
                        (:instance subset-preserves-in-1 (a (apply f x)) (x (image f)) (y s)))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz in-n-minus-1
  (implies (and (natp n) (in a n) (not (equal a (+ -1 n)))) (in a (+ -1 n)))
  :hints (("Goal" :in-theory (enable in-natp))))

(defthmz pig-h-in-range-gen
  (implies (and (in x (domain f)) (in n (domain f)) (not (equal x n)) (natp n) (injective-funp f)
                (subset (image f) n))
           (in (pig-h x f n) (+ -1 n)))
  :hints (("Goal" :in-theory (e/d () (injective-funp injective-funp-is-injective apply-in-codomain apply-rewrite equal-apply))
           :use ((:instance apply-in-codomain (x x) (s n))
                 (:instance apply-in-codomain (x n) (s n))
                 (:instance in-n-minus-1 (a (apply f x)))
                 (:instance in-n-minus-1 (a (apply f n)))
                 (:instance injective-funp-is-injective (x x) (y n)))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz not-in-self
  (not (in x x))
  :hints (("Goal" :use ((:instance in-natp (i x) (j x))))))

(defthmz pig-h-in-range
  (implies (and (in x n) (natp n) (injective-funp f) (equal (domain f) (+ 1 n))
                (subset (image f) n))
           (in (pig-h x f n) (+ -1 n)))
  :hints (("Goal" :in-theory (disable pig-h)
           :use ((:instance pig-h-in-range-gen) in-plus-1-n in-n-plus-1-n not-in-self)))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz pig-h-injective-gen
  (implies (and (in x (domain f)) (in y (domain f)) (in n (domain f))
                (not (equal x n)) (not (equal y n)) (not (equal x y))
                (injective-funp f))
           (not (equal (pig-h x f n) (pig-h y f n))))
  :hints (("Goal" :in-theory (e/d () (injective-funp injective-funp-is-injective apply-rewrite equal-apply))
           :use ((:instance injective-funp-is-injective (x x) (y n))
                 (:instance injective-funp-is-injective (x y) (y n))
                 (:instance injective-funp-is-injective (x x) (y y)))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz pig-h-injective
  (implies (and (in x n) (in y n) (not (equal x y)) (natp n)
                (injective-funp f) (equal (domain f) (+ 1 n)))
           (not (equal (pig-h x f n) (pig-h y f n))))
  :hints (("Goal" :in-theory (disable pig-h)
           :use ((:instance pig-h-injective-gen) in-plus-1-n (:instance in-plus-1-n (x y)) in-n-plus-1-n
                 not-in-self (:instance not-in-self (x y)))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(in-theory (disable pig-h))

(zify pig-g (pig-h x f n) :dom n :ran (+ -1 n)
      :xhyps ((natp n) (injective-funp f) (equal (domain f) (+ 1 n)) (subset (image f) n)))

(defthmz image-pig-g
  (subset (image (pig-g f n)) (+ -1 n))
  :hints (("Goal" :in-theory (enable subset pig-g$comprehension in-prod2)
           :use ((:instance in-image-necc (f (pig-g f n)) (x (subset-witness (image (pig-g f n)) (+ -1 n)))))))
  :props (zfc pig-g$prop prod2$prop domain$prop inverse$prop))

(defthmz funp-inverse-pig-g
  (implies (and (natp n) (injective-funp f) (equal (domain f) (+ 1 n)))
           (funp (inverse (pig-g f n))))
  :hints (("Goal" :expand ((funp (inverse (pig-g f n))))
           :in-theory (e/d (in-inverse pig-g$comprehension in-prod2) (injective-funp)))
          ("Subgoal 2''" :use ((:instance pig-h-injective
                               (x (cdr (car (funp-witness (inverse (pig-g f n))))))
                               (y (cdr (mv-nth 1 (funp-witness (inverse (pig-g f n))))))))))
  :props (zfc pig-g$prop prod2$prop domain$prop inverse$prop))

(defthmz injective-funp-pig-g
  (implies (and (natp n) (injective-funp f) (equal (domain f) (+ 1 n)) (subset (image f) n))
           (injective-funp (pig-g f n)))
  :hints (("Goal" :in-theory (enable injective-funp)))
  :props (zfc pig-g$prop prod2$prop domain$prop inverse$prop))

(defun pig-ind (f n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) f (pig-ind (pig-g f n) (1- n))))

(defthmz pigeon-base
  (implies (and (equal (domain f) 1) (subset (image f) 0)) nil)
  :rule-classes nil
  :hints (("Goal" :use ((:instance apply-in-codomain (x 0) (s 0)))
           :in-theory (disable apply-in-codomain)))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz pigeon-core
  (implies (and (natp n) (injective-funp f) (equal (domain f) (+ 1 n)) (subset (image f) n)) nil)
  :rule-classes nil
  :hints (("Goal" :induct (pig-ind f n) :in-theory (disable injective-funp))
          ("Subgoal *1/1" :use pigeon-base))
  :props (zfc pig-g$prop prod2$prop domain$prop inverse$prop))


(defthmz funp-inverse-restrict
  (implies (funp (inverse f))
           (funp (inverse (restrict f d))))
  :hints (("Goal" :expand ((funp (inverse (restrict f d))))
           :in-theory (enable in-inverse restrict$comprehension)
           :use ((:instance funp-necc (f (inverse f))
                            (p1 (mv-nth 0 (funp-witness (inverse (restrict f d)))))
                            (p2 (mv-nth 1 (funp-witness (inverse (restrict f d)))))))))
  :props (zfc prod2$prop inverse$prop restrict$prop))

(defthmz restrict-injection
  (implies (and (injective-funp f) (subset d (domain f)) (subset (image f) s))
           (and (injective-funp (restrict f d))
                (equal (domain (restrict f d)) d)
                (subset (image (restrict f d)) s)))
  :hints (("Goal" :in-theory (enable int2-when-subset-commuted)))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz no-inject-larger
  (implies (and (natp m) (natp n) (< m n) (injective-funp f) (equal (domain f) n) (subset (image f) m))
           nil)
  :rule-classes nil
  :hints (("Goal" :in-theory (disable restrict-injection injective-funp)
           :use ((:instance restrict-injection (d (+ 1 m)) (s m))
                 (:instance <=-implies-subset-on-natps (i (+ 1 m)) (j n))
                 (:instance pigeon-core (n m) (f (restrict f (+ 1 m)))))))
  :props (zfc pig-g$prop prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz pigeonhole
  (implies (natp n) (not (injects-into (+ 1 n) n)))
  :props (zfc prod2$prop domain$prop inverse$prop pig-g$prop)
  :hints (("Goal" :use ((:instance pigeon-core (f (injects-into-witness (+ 1 n) n)))))))

(defthmz injective-funp-inverse
  (implies (injective-funp f)
           (and (injective-funp (inverse f))
                (equal (domain (inverse f)) (image f))
                (equal (image (inverse f)) (domain f))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz eqnum-naturals-equal
  (implies (and (natp m) (natp n) (exists-bijection m n)) (equal m n))
  :props (zfc prod2$prop domain$prop inverse$prop pig-g$prop restrict$prop diff$prop)
  :rule-classes nil
  :hints (("Goal" :expand ((exists-bijection m n))
           :in-theory (disable injective-funp injective-funp-inverse)
           :use ((:instance no-inject-larger (m n) (n m) (f (exists-bijection-witness m n)))
                 (:instance injective-funp-inverse (f (exists-bijection-witness m n)))
                 (:instance no-inject-larger (m m) (n n) (f (inverse (exists-bijection-witness m n))))))))

(defthmz subset-nat-omega
  (implies (natp n) (subset n (omega)))
  :hints (("Goal" :in-theory (enable subset)
           :use ((:instance in-natp-implies-natp (y (subset-witness n (omega))) (x n))))))

(defthmz omega-no-inject-nat
  (implies (and (injective-funp g) (equal (domain g) (omega)) (natp n) (subset (image g) n))
           nil)
  :rule-classes nil
  :hints (("Goal" :in-theory (disable injective-funp restrict-injection)
           :use ((:instance subset-nat-omega (n (+ 1 n)))
                 (:instance restrict-injection (f g) (d (+ 1 n)) (s n))
                 (:instance pigeon-core (f (restrict g (+ 1 n)))))))
  :props (zfc prod2$prop domain$prop inverse$prop pig-g$prop restrict$prop diff$prop))

(defthmz finite!-omega-nil
  (not (finite! (omega)))
  :hints (("Goal" :in-theory (e/d (finite! bijection injective-funp) (injective-funp-inverse))
           :use ((:instance injective-funp-inverse (f (finite!-witness (omega))))
                 (:instance omega-no-inject-nat (g (inverse (finite!-witness (omega))))
                            (n (domain (finite!-witness (omega))))))))
  :props (zfc prod2$prop domain$prop inverse$prop pig-g$prop restrict$prop diff$prop))

(defthmz omega-not-finite (not (finite (omega)))
  :props (zfc prod2$prop domain$prop inverse$prop pig-g$prop restrict$prop diff$prop)
  :hints (("Goal" :in-theory (enable finite-is-finite!))))

(defthmz finite!-iff-eqnum-to-nat (iff (finite! s) (eqnum-to-nat s))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal" :in-theory (enable finite! bijection)
           :use ((:instance eqnum-to-nat-suff (n (domain (finite!-witness s))))
                 (:instance exists-bijection-suff (fn (finite!-witness s)) (s1 (domain (finite!-witness s))) (s2 s))
                 (:instance finite!-suff (f (exists-bijection-witness (eqnum-to-nat-witness s) s)))))))
(defthmz finite-iff-eqnum-to-nat (iff (finite s) (eqnum-to-nat s))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop restrict$prop)
  :hints (("Goal" :in-theory (enable finite-is-finite!))))

