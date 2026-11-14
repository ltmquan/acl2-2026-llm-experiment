(in-package "ZF")

(include-book "defs")

; NOTE on SUBGROUP-IS-GROUP (from the task's list of theorems): it is NOT
; proved here, because I believe it cannot be proved as stated.  GROUPP does
; not require OP (or INV) to be a function: it only constrains (domain op),
; (image op), and the values chosen by APPLY.  When OP is not functional, APPLY
; picks one of several values via the defchoose function APPLY-BASE, and
; nothing pins that choice down.  Concretely, let S = {0,1}, E = 0,
; INV = {(0,0),(1,1)}, and let OP = graph of addition mod 2 plus one extra
; pair ((0 . 0) . 1).  In a model where APPLY-BASE picks 0 for (apply op
; '(0 . 0)), (groupp s op e inv) holds and H = {0} satisfies SUBGROUP-P.  But
; (restrict op (prod2 h h)) = {((0 . 0) . 0), ((0 . 0) . 1)}, whose image {0,1}
; is not a subset of H, so the conclusion GROUPP fails.  Since ACL2 cannot
; rule that model out, the theorem cannot be proved.
; SUBGROUP-IS-GROUP-WHEN-FUNP, at the end of this file, proves the same
; statement with the extra hypotheses (funp op) and (funp inv).

;;; Basic group facts

(defthmz group-closure
  (implies (and (groupp s op e inv) (in x s) (in y s))
           (in (apply2 op x y) s))
  :hints (("Goal" :in-theory (enable subset)
           :use ((:instance in-apply-image (r op) (x (cons x y))))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthm group-e-in
  (implies (groupp s op e inv) (in e s)))

(defthm group-inv-in
  (implies (and (groupp s op e inv) (in x s)) (in (apply inv x) s))
  :hints (("Goal" :use ((:instance group-inverse-p-necc)))))

(defthm group-left-id
  (implies (and (groupp s op e inv) (in x s)) (equal (apply2 op e x) x))
  :hints (("Goal" :in-theory (disable apply2) :use ((:instance group-identity-p-necc)))))

(defthm group-right-id
  (implies (and (groupp s op e inv) (in x s)) (equal (apply2 op x e) x))
  :hints (("Goal" :in-theory (disable apply2) :use ((:instance group-identity-p-necc)))))

(defthm group-right-inv
  (implies (and (groupp s op e inv) (in x s)) (equal (apply2 op x (apply inv x)) e))
  :hints (("Goal" :in-theory (disable apply2) :use ((:instance group-inverse-p-necc)))))

(defthm group-left-inv
  (implies (and (groupp s op e inv) (in x s)) (equal (apply2 op (apply inv x) x) e))
  :hints (("Goal" :in-theory (disable apply2) :use ((:instance group-inverse-p-necc)))))

(defthm group-assoc
  (implies (and (groupp s op e inv) (in x s) (in y s) (in z s))
           (equal (apply2 op (apply2 op x y) z)
                  (apply2 op x (apply2 op y z))))
  :hints (("Goal" :in-theory (disable apply2) :use ((:instance group-associative-p-necc)))))

(defthm groupp-forward
  (implies (groupp s op e inv)
           (and (equal (domain op) (prod2 s s))
                (subset (image op) s)
                (in e s)
                (equal (domain inv) s)))
  :rule-classes :forward-chaining)

(in-theory (disable groupp apply2))

(defthm group-left-cancel
  (implies (and (groupp s op e inv) (in x s) (in y s) (in z s))
           (equal (equal (apply2 op x y) (apply2 op x z))
                  (equal y z)))
  :hints (("Goal" :use ((:instance group-assoc (x (apply inv x)) (y x) (z y))
                        (:instance group-assoc (x (apply inv x)) (y x) (z z))))))

(defthm group-right-cancel
  (implies (and (groupp s op e inv) (in x s) (in y s) (in z s))
           (equal (equal (apply2 op y x) (apply2 op z x))
                  (equal y z)))
  :hints (("Goal" :in-theory (disable group-assoc)
           :use ((:instance group-assoc (z (apply inv x)) (x y) (y x))
                        (:instance group-assoc (z (apply inv x)) (x z) (y x))))))

(defthm group-right-inverse-unique
  (implies (and (groupp s op e inv) (in x s) (in y s)
                (equal (apply2 op x y) e))
           (equal (apply inv x) y))
  :rule-classes nil
  :hints (("Goal" :use ((:instance group-left-cancel (y (apply inv x)) (z y))))))

(defthm group-left-inverse-unique
  (implies (and (groupp s op e inv) (in x s) (in y s)
                (equal (apply2 op y x) e))
           (equal (apply inv x) y))
  :rule-classes nil
  :hints (("Goal" :use ((:instance group-right-cancel (y (apply inv x)) (z y))))))

(defthm group-inv-e
  (implies (groupp s op e inv) (equal (apply inv e) e))
  :hints (("Goal" :use ((:instance group-right-inverse-unique (x e) (y e))))))

(defthmz group-identity-unique
  (implies (and (groupp s op e inv) (in e2 s) (group-identity-p s op e2))
           (equal e2 e))
  :rule-classes nil
  :hints (("Goal" :use ((:instance group-identity-p-necc (e e2) (x e)))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz group-inverse-unique
  (implies (and (groupp s op e inv) (in x s) (in y s)
                (equal (apply2 op x y) e))
           (equal y (apply inv x)))
  :rule-classes nil
  :hints (("Goal" :use group-right-inverse-unique))
  :props (zfc prod2$prop domain$prop inverse$prop))

;;; Intersection of subgroups

(in-theory (disable closed-under-op closed-under-inv all-subgroups preserves-op
                    normal-in group-identity-p group-inverse-p group-associative-p
                    subgroup-p))

(defthm subgroup-p-forward
  (implies (subgroup-p h s op e inv)
           (and (subset h s) (in e h) (closed-under-op h op) (closed-under-inv h inv)))
  :hints (("Goal" :in-theory (enable subgroup-p)))
  :rule-classes :forward-chaining)

(defthm subgroup-p-intro
  (implies (and (subset h s) (in e h) (closed-under-op h op) (closed-under-inv h inv))
           (subgroup-p h s op e inv))
  :hints (("Goal" :in-theory '(subgroup-p))))

(defthmz in-intersection-of-subgroups
  (implies (and (in x (intersection hs)) (in h hs))
           (in x h))
  :hints (("Goal" :in-theory (enable in-all-necc)))
  :props (zfc intersection$prop))

(defthmz in-intersection-intro
  (implies (and (not (equal hs 0)) (in-all x hs))
           (in x (intersection hs)))
  :props (zfc intersection$prop))

(in-theory (disable intersection$comprehension-improved))

(defthmz intersection-subset
  (implies (and (not (equal hs 0)) (all-subgroups hs s op e inv))
           (subset (intersection hs) s))
  :hints (("Goal" :expand ((subset (intersection hs) s))
           :use ((:instance in-intersection-of-subgroups
                            (x (subset-witness (intersection hs) s))
                            (h (min-in hs)))
                 (:instance all-subgroups-necc (h (min-in hs))))))
  :props (zfc intersection$prop))

(defthmz intersection-e
  (implies (and (not (equal hs 0)) (all-subgroups hs s op e inv))
           (in e (intersection hs)))
  :hints (("Goal" :expand ((in-all e hs))
           :use ((:instance all-subgroups-necc (h (in-all-witness e hs))))))
  :props (zfc intersection$prop))

(defthmz intersection-closed-op-lemma
  (implies (and (not (equal hs 0)) (all-subgroups hs s op e inv)
                (in x (intersection hs)) (in y (intersection hs)))
           (in (apply2 op x y) (intersection hs)))
  :hints (("Goal" :expand ((in-all (apply2 op x y) hs))
           :use ((:instance in-intersection-intro (x (apply2 op x y)))
                 (:instance all-subgroups-necc (h (in-all-witness (apply2 op x y) hs)))
                 (:instance closed-under-op-necc (h (in-all-witness (apply2 op x y) hs)))
                 (:instance in-intersection-of-subgroups (h (in-all-witness (apply2 op x y) hs)))
                 (:instance in-intersection-of-subgroups (x y) (h (in-all-witness (apply2 op x y) hs))))))
  :props (zfc intersection$prop))

(defthmz intersection-closed-inv-lemma
  (implies (and (not (equal hs 0)) (all-subgroups hs s op e inv)
                (in x (intersection hs)))
           (in (apply inv x) (intersection hs)))
  :hints (("Goal" :expand ((in-all (apply inv x) hs))
           :use ((:instance in-intersection-intro (x (apply inv x)))
                 (:instance all-subgroups-necc (h (in-all-witness (apply inv x) hs)))
                 (:instance closed-under-inv-necc (h (in-all-witness (apply inv x) hs)))
                 (:instance in-intersection-of-subgroups (h (in-all-witness (apply inv x) hs))))))
  :props (zfc intersection$prop))

(defthmz intersection-closed-op
  (implies (and (not (equal hs 0)) (all-subgroups hs s op e inv))
           (closed-under-op (intersection hs) op))
  :hints (("Goal" :expand ((closed-under-op (intersection hs) op))))
  :props (zfc intersection$prop))

(defthmz intersection-closed-inv
  (implies (and (not (equal hs 0)) (all-subgroups hs s op e inv))
           (closed-under-inv (intersection hs) inv))
  :hints (("Goal" :expand ((closed-under-inv (intersection hs) inv))))
  :props (zfc intersection$prop))

(defthmz intersection-of-subgroups
  (implies (and (groupp s op e inv) (not (equal hs 0))
                (all-subgroups hs s op e inv))
           (subgroup-p (intersection hs) s op e inv))
  :props (zfc prod2$prop domain$prop inverse$prop intersection$prop))

;;; Homomorphisms

(defthmz hom-apply-in
  (implies (and (group-hom-p f s1 op1 s2 op2) (in x s1))
           (in (apply f x) s2))
  :hints (("Goal" :use ((:instance in-apply-image (r f)))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthm hom-op
  (implies (and (group-hom-p f s1 op1 s2 op2) (in x s1) (in y s1))
           (equal (apply f (apply2 op1 x y))
                  (apply2 op2 (apply f x) (apply f y))))
  :hints (("Goal" :use preserves-op-necc)))

(defthm group-hom-p-forward
  (implies (group-hom-p f s1 op1 s2 op2)
           (and (funp f) (equal (domain f) s1) (subset (image f) s2)))
  :rule-classes :forward-chaining)

(in-theory (disable group-hom-p))

(defthmz hom-identity
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (equal (apply f e1) e2))
  :hints (("Goal" :in-theory (disable hom-op)
           :use ((:instance hom-op (x e1) (y e1))
                 (:instance group-left-cancel (s s2) (op op2) (e e2) (inv inv2)
                            (x (apply f e1)) (y (apply f e1)) (z e2)))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz hom-inverse
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2) (in x s1))
           (equal (apply f (apply inv1 x))
                  (apply inv2 (apply f x))))
  :hints (("Goal" :in-theory (disable hom-op)
           :use ((:instance hom-op (x (apply inv1 x)) (y x))
                 (:instance group-left-inverse-unique (s s2) (op op2) (e e2) (inv inv2)
                            (x (apply f x)) (y (apply f (apply inv1 x)))))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz hom-preserves-identity-and-inverse
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (and (equal (apply f e1) e2)
                (implies (in x s1)
                         (equal (apply f (apply inv1 x))
                                (apply inv2 (apply f x))))))
  :props (zfc prod2$prop domain$prop inverse$prop))

;;; Kernel and image

(in-theory (disable equal-apply))

(defthmz kernel-subset
  (subset (kernel f s1 e2) s1)
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc kernel$prop))

(defthmz kernel-e
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (in e1 (kernel f s1 e2)))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

(defthmz kernel-closed-op-lemma
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2)
                (in x (kernel f s1 e2)) (in y (kernel f s1 e2)))
           (in (apply2 op1 x y) (kernel f s1 e2)))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

(defthmz kernel-closed-inv-lemma
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2)
                (in x (kernel f s1 e2)))
           (in (apply inv1 x) (kernel f s1 e2)))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

(defthmz kernel-normal-lemma
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2)
                (in g s1)
                (in x (kernel f s1 e2)))
           (in (apply2 op1 (apply2 op1 g x) (apply inv1 g)) (kernel f s1 e2)))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

(defthmz kernel-is-normal-subgroup
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (and (subgroup-p (kernel f s1 e2) s1 op1 e1 inv1)
                (normal-in (kernel f s1 e2) s1 op1 inv1)))
  :hints (("Goal" :in-theory (disable kernel$comprehension group-assoc)
           :expand ((closed-under-op (kernel f s1 e2) op1)
                    (closed-under-inv (kernel f s1 e2) inv1)
                    (normal-in (kernel f s1 e2) s1 op1 inv1))))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

;; image

(defthmz image-elim
  (implies (and (group-hom-p f s1 op1 s2 op2) (in y (image f)))
           (and (in (apply (inverse f) y) s1)
                (equal (apply f (apply (inverse f) y)) y)))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz image-intro
  (implies (and (group-hom-p f s1 op1 s2 op2) (in x s1) (equal y (apply f x)))
           (in y (image f)))
  :hints (("Goal" :use ((:instance in-apply-image (r f)))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz image-e
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (in e2 (image f)))
  :hints (("Goal" :use ((:instance image-intro (x e1) (y e2)))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz image-closed-op-lemma
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2)
                (in x (image f)) (in y (image f)))
           (in (apply2 op2 x y) (image f)))
  :hints (("Goal" :use ((:instance image-intro
                                   (x (apply2 op1 (apply (inverse f) x) (apply (inverse f) y)))
                                   (y (apply2 op2 x y)))
                        (:instance hom-op (x (apply (inverse f) x)) (y (apply (inverse f) y)))
                        (:instance image-elim (y x))
                        (:instance image-elim))
           :in-theory (disable hom-op image-elim image-intro)))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz image-closed-inv-lemma
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2)
                (in x (image f)))
           (in (apply inv2 x) (image f)))
  :hints (("Goal" :use ((:instance image-intro
                                   (x (apply inv1 (apply (inverse f) x)))
                                   (y (apply inv2 x)))
                        (:instance hom-inverse (x (apply (inverse f) x)))
                        (:instance image-elim (y x)))
           :in-theory (disable hom-inverse image-elim image-intro)))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz image-is-subgroup
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (subgroup-p (image f) s2 op2 e2 inv2))
  :hints (("Goal" :expand ((closed-under-op (image f) op2)
                           (closed-under-inv (image f) inv2))))
  :props (zfc prod2$prop domain$prop inverse$prop))

;;; Injectivity

(defthmz injective-implies-trivial-kernel
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2)
                (injective-funp f))
           (equal (kernel f s1 e2) (singleton e1)))
  :hints (("Goal" :in-theory (e/d (extensionality-rewrite subset) (injective-funp))
           :use ((:instance injective-funp-is-injective
                            (x (subset-witness (kernel f s1 e2) (pair e1 e1)))
                            (y e1)))))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

(defthmz trivial-kernel-preimage-unique
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2)
                (equal (kernel f s1 e2) (singleton e1))
                (in a s1) (in b s1)
                (equal (apply f a) (apply f b)))
           (equal a b))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable kernel$comprehension group-right-cancel)
           :use ((:instance kernel$comprehension (x (apply2 op1 a (apply inv1 b))))
                 (:instance group-right-cancel (s s1) (op op1) (e e1) (inv inv1)
                            (x (apply inv1 b)) (y a) (z b)))))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

(defthmz in-funp-elim
  (implies (and (funp f) (in p f))
           (and (consp p)
                (in (car p) (domain f))
                (equal (apply f (car p)) (cdr p))))
  :hints (("Goal" :use (apply-intro-lemma
                        (:instance in-car-domain (r f))
                        (:instance relation-p-necc (r f)))))
  :props (zfc domain$prop))

(defthmz trivial-kernel-implies-funp-inverse
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2)
                (equal (kernel f s1 e2) (singleton e1)))
           (funp (inverse f)))
  :hints (("Goal" :expand ((funp (inverse f)))
           :in-theory (e/d (in-inverse) (in-funp-elim))
           :use ((:instance trivial-kernel-preimage-unique
                            (a (cdr (mv-nth 0 (funp-witness (inverse f)))))
                            (b (cdr (mv-nth 1 (funp-witness (inverse f))))))
                 (:instance in-funp-elim
                            (p (cons (cdr (mv-nth 0 (funp-witness (inverse f))))
                                     (car (mv-nth 0 (funp-witness (inverse f)))))))
                 (:instance in-funp-elim
                            (p (cons (cdr (mv-nth 1 (funp-witness (inverse f))))
                                     (car (mv-nth 1 (funp-witness (inverse f))))))))))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

(defthmz injective-iff-trivial-kernel
  (implies (and (groupp s1 op1 e1 inv1) (groupp s2 op2 e2 inv2)
                (group-hom-p f s1 op1 s2 op2))
           (iff (injective-funp f)
                (equal (kernel f s1 e2) (singleton e1))))
  :hints (("Goal" :in-theory (disable singleton)
           :use (injective-implies-trivial-kernel
                 trivial-kernel-implies-funp-inverse)))
  :props (zfc prod2$prop domain$prop inverse$prop kernel$prop))

;;; Subgroup is a group, when op and inv are functions

(defthmz apply2-restrict-prod2
  (implies (and (funp op) (subset (prod2 h h) (domain op)) (in x h) (in y h))
           (equal (apply2 (restrict op (prod2 h h)) x y)
                  (apply2 op x y)))
  :hints (("Goal" :in-theory (enable apply2)))
  :props (zfc prod2$prop domain$prop restrict$prop diff$prop))

(defthmz subset-prod2-prod2
  (implies (subset h s) (subset (prod2 h h) (prod2 s s)))
  :hints (("Goal" :expand ((subset (prod2 h h) (prod2 s s)))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz int2-prod2-subset
  (implies (subset h s)
           (equal (int2 (prod2 s s) (prod2 h h)) (prod2 h h)))
  :hints (("Goal" :use ((:instance extensionality (x (int2 (prod2 s s) (prod2 h h))) (y (prod2 h h))))
           :expand ((subset (int2 (prod2 s s) (prod2 h h)) (prod2 h h))
                    (subset (prod2 h h) (int2 (prod2 s s) (prod2 h h))))))
  :props (zfc prod2$prop diff$prop domain$prop inverse$prop))

(defthmz int2-subset
  (implies (subset h s) (equal (int2 s h) h))
  :hints (("Goal" :use ((:instance extensionality (x (int2 s h)) (y h)))
           :expand ((subset (int2 s h) h) (subset h (int2 s h)))))
  :props (zfc diff$prop))

(defthmz restrict-image-closed-lemma
  (implies (and (funp op) (closed-under-op h op)
                (in y (image (restrict op (prod2 h h)))))
           (in y h))
  :hints (("Goal" :in-theory (e/d (apply2) (in-image-necc in-funp-elim closed-under-op-necc))
           :use ((:instance in-image-necc (x y) (f (restrict op (prod2 h h))))
                 (:instance in-funp-elim (f op)
                            (p (cons (apply (inverse (restrict op (prod2 h h))) y) y)))
                 (:instance closed-under-op-necc
                            (x (car (apply (inverse (restrict op (prod2 h h))) y)))
                            (y (cdr (apply (inverse (restrict op (prod2 h h))) y)))))))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop))

(defthmz sgf-domain-op
  (implies (and (groupp s op e inv) (subgroup-p h s op e inv))
           (equal (domain (restrict op (prod2 h h))) (prod2 h h)))
  :hints (("Goal" :use (groupp-forward int2-prod2-subset)))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz sgf-image-op
  (implies (and (subgroup-p h s op e inv) (funp op))
           (subset (image (restrict op (prod2 h h))) h))
  :hints (("Goal" :expand ((subset (image (restrict op (prod2 h h))) h))))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop))

(defthmz sgf-domain-inv
  (implies (and (groupp s op e inv) (subgroup-p h s op e inv))
           (equal (domain (restrict inv h)) h))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz sgf-apply2
  (implies (and (groupp s op e inv) (subgroup-p h s op e inv) (funp op)
                (in x h) (in y h))
           (equal (apply2 (restrict op (prod2 h h)) x y)
                  (apply2 op x y)))
  :hints (("Goal" :use (groupp-forward subset-prod2-prod2 apply2-restrict-prod2)
           :in-theory (disable apply2-restrict-prod2)))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz sgf-apply-inv
  (implies (and (groupp s op e inv) (subgroup-p h s op e inv) (funp inv)
                (in x h))
           (equal (apply (restrict inv h) x)
                  (apply inv x)))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthm sgf-closed-op
  (implies (and (subgroup-p h s op e inv) (in x h) (in y h))
           (in (apply2 op x y) h))
  :hints (("Goal" :use closed-under-op-necc)))

(defthm sgf-closed-inv
  (implies (and (subgroup-p h s op e inv) (in x h))
           (in (apply inv x) h))
  :hints (("Goal" :use closed-under-inv-necc)))

(defthmz sgf-in-s
  (implies (and (subgroup-p h s op e inv) (in x h)) (in x s))
  :props (zfc))

(defthmz sgf-identity
  (implies (and (groupp s op e inv) (subgroup-p h s op e inv) (funp op))
           (group-identity-p h (restrict op (prod2 h h)) e))
  :hints (("Goal" :expand ((group-identity-p h (restrict op (prod2 h h)) e))))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz sgf-assoc
  (implies (and (groupp s op e inv) (subgroup-p h s op e inv) (funp op))
           (group-associative-p h (restrict op (prod2 h h))))
  :hints (("Goal" :expand ((group-associative-p h (restrict op (prod2 h h))))))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz sgf-inverse
  (implies (and (groupp s op e inv) (subgroup-p h s op e inv) (funp op) (funp inv))
           (group-inverse-p h (restrict op (prod2 h h)) e (restrict inv h)))
  :hints (("Goal" :in-theory (disable apply-restrict)
           :expand ((group-inverse-p h (restrict op (prod2 h h)) e (restrict inv h)))))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz subgroup-is-group-when-funp
  (implies (and (groupp s op e inv) (subgroup-p h s op e inv)
                (funp op) (funp inv))
           (groupp h (restrict op (prod2 h h)) e (restrict inv h)))
  :hints (("Goal" :expand ((groupp h (restrict op (prod2 h h)) e (restrict inv h)))))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop))
