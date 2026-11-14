(in-package "ZF")
(defthmz eqnum-reflexive (exists-bijection s s)
  :props (zfc identity-fun$prop prod2$prop domain$prop inverse$prop)
  :hints (("Goal" :use ((:instance exists-bijection-suff (fn (identity-fun s)) (s1 s) (s2 s))))))
