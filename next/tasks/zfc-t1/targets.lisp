(defthmz eqv-class-equal
  (implies (and (equivalence-on r s) (in a s) (in b s))
           (equal (equal (eqv-class a r s) (eqv-class b r s))
                  (in (cons a b) r)))
  :props (zfc prod2$prop eqv-class$prop))

(defthmz quotient-is-partition
  (implies (equivalence-on r s) (partition-p (quotient r s) s))
  :props (zfc prod2$prop diff$prop eqv-class$prop quotient$prop))

(defthmz partition-rel-is-equivalence
  (implies (partition-p p s) (equivalence-on (partition-rel p s) s))
  :props (zfc prod2$prop diff$prop partition-rel$prop))

(defthmz quotient-of-partition-rel
  (implies (partition-p p s) (equal (quotient (partition-rel p s) s) p))
  :props (zfc prod2$prop diff$prop eqv-class$prop quotient$prop partition-rel$prop))

(defthmz partition-rel-of-quotient
  (implies (equivalence-on r s) (equal (partition-rel (quotient r s) s) r))
  :props (zfc prod2$prop diff$prop eqv-class$prop quotient$prop partition-rel$prop))

(defthmz quotient-map-exists
  (implies (equivalence-on r s) (exists-quotient-map r s))
  :props (zfc prod2$prop domain$prop inverse$prop eqv-class$prop quotient$prop))
