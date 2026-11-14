(defthmz reduced-product-relation-is-equivalence
  (implies (and (funp fam) (filter-on u (domain fam)))
           (equivalence-on (ultra-rel fam u) (prod-family fam)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop))

(defthmz principal-ultraproduct
  (implies (and (funp fam) (nonempty-values fam) (in i0 (domain fam)))
           (exists-bijection
            (ultraproduct fam (principal-filter i0 (domain fam)))
            (apply fam i0)))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop fun-space$prop
              prod-family$prop agree-set$prop ultra-rel$prop
              principal-filter$prop eqv-class$prop quotient$prop))
