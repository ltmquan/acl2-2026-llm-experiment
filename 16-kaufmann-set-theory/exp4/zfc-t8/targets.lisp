(defthmz group-identity-unique
  (implies (and (groupp s op e inv) (in e2 s) (group-identity-p s op e2))
           (equal e2 e))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz group-inverse-unique
  (implies (and (groupp s op e inv) (in x s) (in y s)
                (equal (apply2 op x y) e))
           (equal y (apply inv x)))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz subgroup-is-group
  (implies (and (groupp s op e inv) (subgroup-p h s op e inv))
           (groupp h (restrict op (prod2 h h)) e (restrict inv h)))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz intersection-of-subgroups
  (implies (and (groupp s op e inv) (not (equal hs 0))
                (all-subgroups hs s op e inv))
           (subgroup-p (intersection hs) s op e inv))
  :props (zfc prod2$prop domain$prop inverse$prop intersection$prop))

(defthmz hom-preserves-identity-and-inverse
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (and (equal (apply f e1) e2)
                (implies (in x s1)
                         (equal (apply f (apply inv1 x))
                                (apply inv2 (apply f x))))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz kernel-is-normal-subgroup
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (and (subgroup-p (kernel f s1 e2) s1 op1 e1 inv1)
                (normal-in (kernel f s1 e2) s1 op1 inv1)))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

(defthmz image-is-subgroup
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (subgroup-p (image f) s2 op2 e2 inv2))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz injective-iff-trivial-kernel
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (iff (injective-funp f)
                (equal (kernel f s1 e2) (singleton e1))))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))
