(in-package "ZF")
(ld "t9.lisp")

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
