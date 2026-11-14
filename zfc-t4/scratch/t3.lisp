(in-package "ZF")
(defthmz injects-both-ways-implies-eqnum
  (implies (and (injects-into a b) (injects-into b a))
           (exists-bijection a b))
  :props (sbt-prop fun-bij$prop)
  :hints (("Goal" :expand ((injects-into a b) (injects-into b a))
           :use ((:instance schroeder-bernstein (f (injects-into-witness a b)) (g (injects-into-witness b a)) (s1 a) (s2 b))))))
