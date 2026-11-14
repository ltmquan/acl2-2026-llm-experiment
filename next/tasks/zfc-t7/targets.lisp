(defthmz continuous-compose
  (implies (and (continuous f tp1 tp2) (continuous g tp2 tp3))
           (continuous (compose g f) tp1 tp3))
  :props (zfc prod2$prop domain$prop inverse$prop compose$prop preimage$prop))

(defthmz continuous-image-of-compact
  (implies (and (tpp tp1) (tpp tp2) (compact tp1) (continuous f tp1 tp2)
                (equal (image f) (union tp2)))
           (compact tp2))
  :props (zfc prod2$prop domain$prop inverse$prop preimage$prop))

(defthmz hausdorff-singleton-closed
  (implies (and (tpp tp) (hausdorff tp) (in x (union tp)))
           (closed (singleton x) tp))
  :props (zfc diff$prop))

(defthmz compact-subset-of-hausdorff-is-closed
  (implies (and (tpp tp) (hausdorff tp) (subset s (union tp))
                (compact (subspace s tp)))
           (closed s tp))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop subspace-fn$prop))
