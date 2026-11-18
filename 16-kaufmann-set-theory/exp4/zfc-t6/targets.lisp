(defthmz infinite-ramsey-2
  (implies (and (funp c) (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) 2))
           (exists-infinite-homogeneous c))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz infinite-ramsey
  (implies (and (natp r) (funp c) (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) r))
           (exists-infinite-homogeneous c))
  :props (zfc prod2$prop domain$prop inverse$prop))
