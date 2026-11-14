(defthmz in-prod-family
  (implies (funp fam)
           (equal (in f (prod-family fam))
                  (and (funp f) (equal (domain f) (domain fam))
                       (choice-fn-p f fam))))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop))

(defthmz prod-family-empty-iff
  (implies (funp fam)
           (iff (equal (prod-family fam) 0)
                (not (nonempty-values fam))))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop))

(defthmz projection-surjective
  (implies (and (funp fam) (nonempty-values fam)
                (in i (domain fam)) (in y (apply fam i)))
           (has-coordinate fam i y))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop))

(defthmz prod-family-binary
  (exists-bijection (prod-family (pair (cons 0 a) (cons 1 b)))
                    (prod2 a b))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop prod-family$prop))
