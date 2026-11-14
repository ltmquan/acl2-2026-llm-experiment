(in-package "ZF")
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
