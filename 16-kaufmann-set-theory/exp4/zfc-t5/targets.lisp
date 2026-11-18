(defthmz tr-unique
  (implies (and (ordinal-p a) (tr-fn-p f1 a) (tr-fn-p f2 a)) (equal f1 f2))
  :props (zfc domain$prop restrict$prop diff$prop))

(defthmz tr-existence
  (implies (ordinal-p a) (tr-exists a))
  :props (zfc domain$prop restrict$prop diff$prop))
