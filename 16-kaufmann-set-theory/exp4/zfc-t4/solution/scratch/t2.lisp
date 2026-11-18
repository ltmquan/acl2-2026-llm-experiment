(in-package "ZF")
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
