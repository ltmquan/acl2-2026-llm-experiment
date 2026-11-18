(defthmz eqnum-reflexive (exists-bijection s s))

(defthmz eqnum-symmetric
  (implies (exists-bijection a b) (exists-bijection b a))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz eqnum-transitive
  (implies (and (exists-bijection a b) (exists-bijection b c))
           (exists-bijection a c))
  :props (zfc prod2$prop domain$prop inverse$prop compose$prop))

(defthmz injects-both-ways-implies-eqnum
  (implies (and (injects-into a b) (injects-into b a))
           (exists-bijection a b))
  :props (sbt-prop))

(defthmz set-injects-into-powerset (injects-into s (powerset s)))

(defthmz powerset-does-not-inject (not (injects-into (powerset s) s))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz pigeonhole
  (implies (natp n) (not (injects-into (+ 1 n) n)))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz eqnum-naturals-equal
  (implies (and (natp m) (natp n) (exists-bijection m n)) (equal m n))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz omega-not-finite (not (finite (omega))))

(defthmz finite-iff-eqnum-to-nat (iff (finite s) (eqnum-to-nat s))
  :props (zfc prod2$prop domain$prop inverse$prop))
