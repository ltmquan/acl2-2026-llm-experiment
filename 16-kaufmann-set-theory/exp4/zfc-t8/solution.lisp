(in-package "ZF")

(include-book "defs")

; ---------------------------------------------------------------------------
; Basic group facts, stated with (groupp s op e inv) as a hypothesis.

(defthmz group-closed
  (implies (and (groupp s op e inv) (in x s) (in y s))
           (in (apply2 op x y) s))
  :hints (("Goal" :in-theory (e/d (apply2) (in-apply-image))
           :use ((:instance in-apply-image (r op) (x (cons x y)))
                 (:instance subset-necc (a (apply op (cons x y)))
                            (x (image op)) (y s)))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthm group-e-in
  (implies (groupp s op e inv) (in e s)))

(defthm group-inv-closed
  (implies (and (groupp s op e inv) (in x s))
           (in (apply inv x) s))
  :hints (("Goal" :use ((:instance group-inverse-p-necc)))))

(defthm group-id-left
  (implies (and (groupp s op e inv) (in x s))
           (equal (apply2 op e x) x))
  :hints (("Goal" :in-theory (disable apply2) :use ((:instance group-identity-p-necc)))))

(defthm group-id-right
  (implies (and (groupp s op e inv) (in x s))
           (equal (apply2 op x e) x))
  :hints (("Goal" :in-theory (disable apply2) :use ((:instance group-identity-p-necc)))))

(defthm group-inv-right
  (implies (and (groupp s op e inv) (in x s))
           (equal (apply2 op x (apply inv x)) e))
  :hints (("Goal" :in-theory (disable apply2) :use ((:instance group-inverse-p-necc)))))

(defthm group-inv-left
  (implies (and (groupp s op e inv) (in x s))
           (equal (apply2 op (apply inv x) x) e))
  :hints (("Goal" :in-theory (disable apply2) :use ((:instance group-inverse-p-necc)))))

(defthm group-assoc
  (implies (and (groupp s op e inv) (in x s) (in y s) (in z s))
           (equal (apply2 op (apply2 op x y) z)
                  (apply2 op x (apply2 op y z))))
  :hints (("Goal" :in-theory (disable apply2) :use ((:instance group-associative-p-necc)))))

(in-theory (disable groupp apply2))

(defthmz group-identity-unique
  (implies (and (groupp s op e inv) (in e2 s) (group-identity-p s op e2))
           (equal e2 e))
  :hints (("Goal" :use ((:instance group-identity-p-necc (e e2) (x e))
                        (:instance group-id-right (x e2)))
           :in-theory (disable group-identity-p-necc group-id-right)))
  :rule-classes nil
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz group-inverse-unique
  (implies (and (groupp s op e inv) (in x s) (in y s)
                (equal (apply2 op x y) e))
           (equal y (apply inv x)))
  :hints (("Goal" :use ((:instance group-assoc (x (apply inv x)) (y x) (z y)))
           :in-theory (disable group-assoc)))
  :rule-classes nil
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz group-inverse-unique-rw
  (implies (and (groupp s op e inv) (in x s) (in y s)
                (equal (apply2 op x y) e))
           (equal (apply inv x) y))
  :hints (("Goal" :use group-inverse-unique))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz group-idempotent-is-e
  (implies (and (groupp s op e inv) (in a s)
                (equal (apply2 op a a) a))
           (equal a e))
  :hints (("Goal" :use ((:instance group-assoc (x (apply inv a)) (y a) (z a)))
           :in-theory (disable group-assoc)))
  :rule-classes nil
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz group-inv-e
  (implies (groupp s op e inv)
           (equal (apply inv e) e))
  :hints (("Goal" :use ((:instance group-inverse-unique-rw (x e) (y e)))
           :in-theory (disable group-inverse-unique-rw)))
  :props (zfc prod2$prop domain$prop inverse$prop))

; x = (x y^-1) y
(defthmz group-right-cancel-e
  (implies (and (groupp s op e inv) (in x s) (in y s)
                (equal (apply2 op x (apply inv y)) e))
           (equal x y))
  :hints (("Goal" :use ((:instance group-assoc (x x) (y (apply inv y)) (z y)))
           :in-theory (disable group-assoc)))
  :rule-classes nil
  :props (zfc prod2$prop domain$prop inverse$prop))

; ---------------------------------------------------------------------------
; Homomorphisms

(defthmz hom-in
  (implies (and (group-hom-p f s1 op1 s2 op2) (in x s1))
           (in (apply f x) s2))
  :hints (("Goal" :use ((:instance in-apply-image (r f))
                        (:instance subset-necc (a (apply f x)) (x (image f)) (y s2)))
           :in-theory (disable in-apply-image subset-necc)))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthm hom-op
  (implies (and (group-hom-p f s1 op1 s2 op2) (in x s1) (in y s1))
           (equal (apply f (apply2 op1 x y))
                  (apply2 op2 (apply f x) (apply f y))))
  :hints (("Goal" :use preserves-op-necc)))

(defthm hom-funp
  (implies (group-hom-p f s1 op1 s2 op2) (funp f)))

(defthm hom-domain
  (implies (group-hom-p f s1 op1 s2 op2) (equal (domain f) s1)))

(defthm hom-image
  (implies (group-hom-p f s1 op1 s2 op2) (subset (image f) s2)))

(in-theory (disable group-hom-p))

(defthmz hom-identity
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (equal (apply f e1) e2))
  :hints (("Goal" :use ((:instance group-idempotent-is-e (s s2) (op op2) (e e2) (inv inv2)
                                   (a (apply f e1)))
                        (:instance hom-op (x e1) (y e1)))
           :in-theory (disable hom-op)))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz hom-inverse
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2)
                (in x s1))
           (equal (apply f (apply inv1 x))
                  (apply inv2 (apply f x))))
  :hints (("Goal" :use ((:instance group-inverse-unique-rw (s s2) (op op2) (e e2) (inv inv2)
                                   (x (apply f x)) (y (apply f (apply inv1 x))))
                        (:instance hom-op (x x) (y (apply inv1 x))))
           :in-theory (disable hom-op group-inverse-unique-rw)))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz hom-preserves-identity-and-inverse
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (and (equal (apply f e1) e2)
                (implies (in x s1)
                         (equal (apply f (apply inv1 x))
                                (apply inv2 (apply f x))))))
  :props (zfc prod2$prop domain$prop inverse$prop))

; ---------------------------------------------------------------------------
; Kernel

(in-theory (disable equal-apply))

(defthmz kernel-subset
  (subset (kernel f s1 e2) s1)
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc kernel$prop))

(defthmz kernel-closed-op
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (closed-under-op (kernel f s1 e2) op1))
  :hints (("Goal" :in-theory (enable closed-under-op)))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

(defthmz kernel-closed-inv
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (closed-under-inv (kernel f s1 e2) inv1))
  :hints (("Goal" :in-theory (enable closed-under-inv)))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

(defthmz kernel-normal
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (normal-in (kernel f s1 e2) s1 op1 inv1))
  :hints (("Goal" :in-theory (enable normal-in)))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

(defthmz kernel-is-normal-subgroup
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (and (subgroup-p (kernel f s1 e2) s1 op1 e1 inv1)
                (normal-in (kernel f s1 e2) s1 op1 inv1)))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

; ---------------------------------------------------------------------------
; Image

(defthmz apply-inverse-in-image
  (implies (and (funp f) (in y (image f)))
           (and (in (apply (inverse f) y) (domain f))
                (equal (apply f (apply (inverse f) y)) y)))
  :hints (("Goal" :use ((:instance in-image-rewrite (x y) (r f))
                        (:instance apply-intro (p (cons (apply (inverse f) y) y))))
           :in-theory (disable in-image-rewrite)))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz image-closed-op
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (closed-under-op (image f) op2))
  :hints (("Goal" :in-theory (enable closed-under-op)
           :use ((:instance hom-op
                            (x (apply (inverse f) (mv-nth 0 (closed-under-op-witness (image f) op2))))
                            (y (apply (inverse f) (mv-nth 1 (closed-under-op-witness (image f) op2)))))
                 (:instance in-apply-image (r f)
                            (x (apply2 op1
                                       (apply (inverse f) (mv-nth 0 (closed-under-op-witness (image f) op2)))
                                       (apply (inverse f) (mv-nth 1 (closed-under-op-witness (image f) op2)))))))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz image-closed-inv
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (closed-under-inv (image f) inv2))
  :hints (("Goal" :in-theory (enable closed-under-inv)
           :use ((:instance hom-inverse
                            (x (apply (inverse f) (closed-under-inv-witness (image f) inv2))))
                 (:instance in-apply-image (r f)
                            (x (apply inv1 (apply (inverse f) (closed-under-inv-witness (image f) inv2))))))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz image-is-subgroup
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (subgroup-p (image f) s2 op2 e2 inv2))
  :hints (("Goal" :use ((:instance in-apply-image (r f) (x e1)))))
  :props (zfc prod2$prop domain$prop inverse$prop))

; ---------------------------------------------------------------------------
; Subgroups

(defthm subgroup-in-s
  (implies (and (subgroup-p h s op e inv) (in x h))
           (in x s))
  :hints (("Goal" :in-theory (enable subset))))

(defthm subgroup-e
  (implies (subgroup-p h s op e inv) (in e h)))

(defthm subgroup-subset
  (implies (subgroup-p h s op e inv) (subset h s)))

(defthm subgroup-op
  (implies (and (subgroup-p h s op e inv) (in x h) (in y h))
           (in (apply2 op x y) h))
  :hints (("Goal" :use closed-under-op-necc)))

(defthm subgroup-inv
  (implies (and (subgroup-p h s op e inv) (in x h))
           (in (apply inv x) h))
  :hints (("Goal" :use closed-under-inv-necc)))

(in-theory (disable subgroup-p))

(defthm all-subgroups-member
  (implies (and (all-subgroups hs s op e inv) (in h hs))
           (subgroup-p h s op e inv))
  :hints (("Goal" :use all-subgroups-necc)))

(in-theory (disable all-subgroups))

(defthm in-all-e
  (implies (all-subgroups hs s op e inv)
           (in-all e hs))
  :hints (("Goal" :expand ((in-all e hs))
           :use ((:instance all-subgroups-member (h (in-all-witness e hs)))))))

(defthm in-all-op
  (implies (and (all-subgroups hs s op e inv) (in-all x hs) (in-all y hs))
           (in-all (apply2 op x y) hs))
  :hints (("Goal" :expand ((in-all (apply2 op x y) hs))
           :use ((:instance all-subgroups-member (h (in-all-witness (apply2 op x y) hs)))))))

(defthm in-all-inv
  (implies (and (all-subgroups hs s op e inv) (in-all x hs))
           (in-all (apply inv x) hs))
  :hints (("Goal" :expand ((in-all (apply inv x) hs))
           :use ((:instance all-subgroups-member (h (in-all-witness (apply inv x) hs)))))))

(defthmz in-all-in-s
  (implies (and (all-subgroups hs s op e inv) (not (equal hs 0)) (in-all x hs))
           (in x s))
  :hints (("Goal" :use ((:instance in-all-necc (s hs) (y (min-in hs)))
                        (:instance all-subgroups-member (h (min-in hs))))
           :in-theory (disable in-all-necc all-subgroups-member))))

(defthmz intersection-of-subgroups
  (implies (and (groupp s op e inv) (not (equal hs 0))
                (all-subgroups hs s op e inv))
           (subgroup-p (intersection hs) s op e inv))
  :hints (("Goal" :in-theory (enable subgroup-p subset closed-under-op closed-under-inv)))
  :props (zfc prod2$prop domain$prop inverse$prop intersection$prop))

; ---------------------------------------------------------------------------
; A subgroup is a group

(defthm group-domain-op
  (implies (groupp s op e inv) (equal (domain op) (prod2 s s)))
  :hints (("Goal" :in-theory (enable groupp))))

(defthm group-domain-inv
  (implies (groupp s op e inv) (equal (domain inv) s))
  :hints (("Goal" :in-theory (enable groupp))))

(defthmz subset-prod2-prod2
  (implies (and (subset a c) (subset b d))
           (subset (prod2 a b) (prod2 c d)))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz sub-apply2-restrict
  (implies (and (groupp s op e inv) (funp op) (subgroup-p h s op e inv)
                (in x h) (in y h))
           (equal (apply2 (restrict op (prod2 h h)) x y)
                  (apply2 op x y)))
  :hints (("Goal" :in-theory (enable apply2)))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz sub-apply-restrict-inv
  (implies (and (groupp s op e inv) (funp inv) (subgroup-p h s op e inv)
                (in x h))
           (equal (apply (restrict inv h) x)
                  (apply inv x)))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz sub-domain-op
  (implies (and (groupp s op e inv) (subgroup-p h s op e inv))
           (equal (domain (restrict op (prod2 h h))) (prod2 h h)))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz sub-domain-inv
  (implies (and (groupp s op e inv) (subgroup-p h s op e inv))
           (equal (domain (restrict inv h)) h))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz sub-apply-op-in
  (implies (and (subgroup-p h s op e inv) (in w (prod2 h h)))
           (in (apply op w) h))
  :hints (("Goal" :use ((:instance subgroup-op (x (car w)) (y (cdr w))))
           :in-theory (e/d (apply2) (subgroup-op))))
  :props (zfc prod2$prop))

(defthmz sub-image-op
  (implies (and (groupp s op e inv) (funp op) (subgroup-p h s op e inv))
           (subset (image (restrict op (prod2 h h))) h))
  :hints (("Goal" :expand ((subset (image (restrict op (prod2 h h))) h))
           :use ((:instance apply-inverse-in-image
                            (f (restrict op (prod2 h h)))
                            (y (subset-witness (image (restrict op (prod2 h h))) h)))
                 (:instance sub-apply-op-in
                            (w (apply (inverse (restrict op (prod2 h h)))
                                      (subset-witness (image (restrict op (prod2 h h))) h)))))
           :in-theory (disable apply-inverse-in-image sub-apply-op-in)))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz sub-identity
  (implies (and (groupp s op e inv) (funp op) (subgroup-p h s op e inv))
           (group-identity-p h (restrict op (prod2 h h)) e))
  :hints (("Goal" :in-theory (enable group-identity-p)))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz sub-assoc
  (implies (and (groupp s op e inv) (funp op) (subgroup-p h s op e inv))
           (group-associative-p h (restrict op (prod2 h h))))
  :hints (("Goal" :in-theory (enable group-associative-p)))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz sub-inverse
  (implies (and (groupp s op e inv) (funp op) (funp inv) (subgroup-p h s op e inv))
           (group-inverse-p h (restrict op (prod2 h h)) e (restrict inv h)))
  :hints (("Goal" :in-theory (e/d (group-inverse-p) (apply-restrict))))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz subgroup-is-group
  (implies (and (groupp s op e inv) (funp op) (funp inv) (subgroup-p h s op e inv))
           (groupp h (restrict op (prod2 h h)) e (restrict inv h)))
  :hints (("Goal" :expand ((groupp h (restrict op (prod2 h h)) e (restrict inv h)))
           :in-theory (disable group-identity-p group-associative-p group-inverse-p)))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

; ---------------------------------------------------------------------------
; Injectivity and the kernel

(defthmz in-fun-pair
  (implies (and (funp f) (in (cons a b) f))
           (and (in a (domain f))
                (equal (apply f a) b)))
  :hints (("Goal" :use ((:instance apply-intro (p (cons a b))))))
  :rule-classes nil
  :props (zfc domain$prop))

(defthmz in-kernel-when-injective
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2)
                (injective-funp f))
           (equal (in x (kernel f s1 e2))
                  (equal x e1)))
  :hints (("Goal" :use ((:instance injective-funp-is-injective (x x) (y e1)))
           :in-theory (disable injective-funp-is-injective injective-funp)))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

(defthmz kernel-when-injective
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2)
                (injective-funp f))
           (equal (kernel f s1 e2) (singleton e1)))
  :hints (("Goal" :in-theory (e/d (extensionality subset) (injective-funp))))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

(defthmz trivial-kernel-cancel
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2)
                (equal (kernel f s1 e2) (singleton e1))
                (in x1 s1) (in x2 s1)
                (equal (apply f x1) (apply f x2)))
           (equal x1 x2))
  :hints (("Goal" :use ((:instance kernel$comprehension
                                   (x (apply2 op1 x1 (apply inv1 x2))))
                        (:instance group-right-cancel-e
                                   (s s1) (op op1) (e e1) (inv inv1)
                                   (x x1) (y x2)))
           :in-theory (disable kernel$comprehension)))
  :rule-classes nil
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

(defthmz inverse-funp-when-trivial-kernel
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2)
                (equal (kernel f s1 e2) (singleton e1)))
           (funp (inverse f)))
  :hints (("Goal"
           :expand ((funp (inverse f)))
           :use ((:instance trivial-kernel-cancel
                            (x1 (cdr (mv-nth 0 (funp-witness (inverse f)))))
                            (x2 (cdr (mv-nth 1 (funp-witness (inverse f))))))
                 (:instance in-fun-pair
                            (a (cdr (mv-nth 0 (funp-witness (inverse f)))))
                            (b (car (mv-nth 0 (funp-witness (inverse f))))))
                 (:instance in-fun-pair
                            (a (cdr (mv-nth 1 (funp-witness (inverse f)))))
                            (b (car (mv-nth 1 (funp-witness (inverse f)))))))))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

(defthmz injective-iff-trivial-kernel
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (iff (injective-funp f)
                (equal (kernel f s1 e2) (singleton e1))))
  :hints (("Goal" :use (kernel-when-injective inverse-funp-when-trivial-kernel)
           :in-theory (disable kernel-when-injective inverse-funp-when-trivial-kernel)))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))
