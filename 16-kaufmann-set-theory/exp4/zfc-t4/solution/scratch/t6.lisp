(in-package "ZF")
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
