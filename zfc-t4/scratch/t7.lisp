(in-package "ZF")
(defun pig-h (x f n)
  (declare (xargs :guard t))
  (if (equal (apply f x) (+ -1 (nfix n))) (apply f n) (apply f x)))

(defthmz in-plus-1-n
  (implies (and (natp n) (in x n)) (in x (+ 1 n)))
  :hints (("Goal" :in-theory (enable in-natp))))

(defthmz in-n-plus-1-n
  (implies (natp n) (in n (+ 1 n)))
  :hints (("Goal" :in-theory (enable in-natp))))

(defthmz apply-in-codomain
  (implies (and (in x (domain f)) (subset (image f) s))
           (in (apply f x) s))
  :hints (("Goal" :use ((:instance in-apply-image (r f) (x x))
                        (:instance subset-preserves-in-1 (a (apply f x)) (x (image f)) (y s)))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz in-n-minus-1
  (implies (and (natp n) (in a n) (not (equal a (+ -1 n)))) (in a (+ -1 n)))
  :hints (("Goal" :in-theory (enable in-natp))))

(defthmz pig-h-in-range-gen
  (implies (and (in x (domain f)) (in n (domain f)) (not (equal x n)) (natp n) (injective-funp f)
                (subset (image f) n))
           (in (pig-h x f n) (+ -1 n)))
  :hints (("Goal" :in-theory (e/d () (injective-funp injective-funp-is-injective apply-in-codomain apply-rewrite equal-apply))
           :use ((:instance apply-in-codomain (x x) (s n))
                 (:instance apply-in-codomain (x n) (s n))
                 (:instance in-n-minus-1 (a (apply f x)))
                 (:instance in-n-minus-1 (a (apply f n)))
                 (:instance injective-funp-is-injective (x x) (y n)))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz not-in-self
  (not (in x x))
  :hints (("Goal" :use ((:instance in-natp (i x) (j x))))))

(defthmz pig-h-in-range
  (implies (and (in x n) (natp n) (injective-funp f) (equal (domain f) (+ 1 n))
                (subset (image f) n))
           (in (pig-h x f n) (+ -1 n)))
  :hints (("Goal" :in-theory (disable pig-h)
           :use ((:instance pig-h-in-range-gen) in-plus-1-n in-n-plus-1-n not-in-self)))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz pig-h-injective-gen
  (implies (and (in x (domain f)) (in y (domain f)) (in n (domain f))
                (not (equal x n)) (not (equal y n)) (not (equal x y))
                (injective-funp f))
           (not (equal (pig-h x f n) (pig-h y f n))))
  :hints (("Goal" :in-theory (e/d () (injective-funp injective-funp-is-injective apply-rewrite equal-apply))
           :use ((:instance injective-funp-is-injective (x x) (y n))
                 (:instance injective-funp-is-injective (x y) (y n))
                 (:instance injective-funp-is-injective (x x) (y y)))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz pig-h-injective
  (implies (and (in x n) (in y n) (not (equal x y)) (natp n)
                (injective-funp f) (equal (domain f) (+ 1 n)))
           (not (equal (pig-h x f n) (pig-h y f n))))
  :hints (("Goal" :in-theory (disable pig-h)
           :use ((:instance pig-h-injective-gen) in-plus-1-n (:instance in-plus-1-n (x y)) in-n-plus-1-n
                 not-in-self (:instance not-in-self (x y)))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(in-theory (disable pig-h))

(zify pig-g (pig-h x f n) :dom n :ran (+ -1 n)
      :xhyps ((natp n) (injective-funp f) (equal (domain f) (+ 1 n)) (subset (image f) n)))
