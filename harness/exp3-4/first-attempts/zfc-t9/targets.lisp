(defthmz complex-construction-is-field
  (implies (and (fieldp s add mul zero one neg recip)
                (minus-one-not-square s mul neg one))
           (fieldp (prod2 s s) (c-add s add) (c-mul s add mul neg)
                   (cons zero zero) (cons one zero) (c-neg s neg)
                   (c-recip s add mul zero neg recip)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop restrict$prop
              c-add$prop c-mul$prop c-neg$prop c-recip$prop))

(defthmz complex-i-squared
  (implies (fieldp s add mul zero one neg recip)
           (equal (apply2 (c-mul s add mul neg) (cons zero one) (cons zero one))
                  (apply (c-neg s neg) (cons one zero))))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop restrict$prop
              c-mul$prop c-neg$prop))

(defthmz rationals-form-field (rationals-field-witness)
  :props (zfc rationals$prop v$prop prod2$prop domain$prop inverse$prop))
