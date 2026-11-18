(in-package "ZF")

; Solution: basic ultrafilter theory in ACL2(zfc).  The optional theorem
; (a nonprincipal ultrafilter on omega) is proved by a Bourbaki-Witt style
; "tower" argument: the least tower of filters extending the cofinite filter,
; closed under a choice-based proper-extension map and unions of chains, is a
; chain whose union is an ultrafilter.
(include-book "defs")

(defthmz subset-reflexive
  (subset x x)
  :hints (("Goal" :in-theory (enable subset))))

(defthmz subset-diff-x
  (subset (diff x y) x)
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc diff$prop))

(defthmz subset-int2-x
  (subset (int2 x y) x)
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc diff$prop))

(defthmz subset-int2-y
  (subset (int2 x y) y)
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc diff$prop))

(defthmz pf-upward-closed
  (implies (in a s) (upward-closed (principal-filter a s) s))
  :hints (("Goal" :in-theory (enable upward-closed principal-filter$comprehension)))
  :props (zfc principal-filter$prop))

(defthmz subset-int2-when-subset
  (implies (subset x s) (subset (int2 x y) s))
  :hints (("Goal" :use ((:instance subset-transitivity (x (int2 x y)) (y x) (z s)))))
  :props (zfc diff$prop))

(defthmz in-int2-pf
  (implies (and (in x (principal-filter a s)) (in y (principal-filter a s)))
           (in (int2 x y) (principal-filter a s)))
  :hints (("Goal" :in-theory (enable principal-filter$comprehension)))
  :props (zfc diff$prop principal-filter$prop))

(defthmz pf-int2-closed
  (int2-closed (principal-filter a s))
  :hints (("Goal" :in-theory (enable int2-closed)))
  :props (zfc diff$prop principal-filter$prop))

(defthmz pf-subset-powerset
  (subset (principal-filter a s) (powerset s))
  :hints (("Goal" :in-theory (enable subset principal-filter$comprehension)))
  :props (zfc principal-filter$prop))

(defthmz pf-ultra
  (implies (in a s) (ultra-p (principal-filter a s) s))
  :hints (("Goal" :in-theory (enable ultra-p principal-filter$comprehension)))
  :props (zfc diff$prop principal-filter$prop))

(defthmz principal-filter-is-ultrafilter
  (implies (in a s) (ultrafilter-on (principal-filter a s) s))
  :props (zfc diff$prop principal-filter$prop))

;;; ---------------- ultrafilter-prime

(defthmz subset-int2-union2-diff
  (subset (int2 (union2 x y) (diff s x)) y)
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc diff$prop))

(defthmz filter-member-subset
  (implies (and (filter-on u s) (in x u))
           (subset x s))
  :hints (("Goal" :use ((:instance subset-necc (a x) (x u) (y (powerset s))))
           :in-theory (disable subset-necc)))
  :props (zfc))

(defthmz ultrafilter-prime
  (implies (and (ultrafilter-on u s) (subset x s) (subset y s)
                (in (union2 x y) u))
           (or (in x u) (in y u)))
  :hints (("Goal" :in-theory (disable ultra-p-necc int2-closed-necc upward-closed-necc
                                      ultra-p int2-closed upward-closed)
           :use ((:instance ultra-p-necc)
                 (:instance int2-closed-necc (x (union2 x y)) (y (diff s x)))
                 (:instance upward-closed-necc (x (int2 (union2 x y) (diff s x))) (y y)))))
  :props (zfc diff$prop))

;;; ---------------- ultra implies maximal

(defthmz int2-x-diff-s-x
  (equal (int2 x (diff s x)) 0)
  :hints (("Goal" :use ((:instance int2-commutative (x x) (y (diff s x)))
                        (:instance int2-diff-x-y-y (x s) (y x)))))
  :props (zfc diff$prop))

(defthmz ultra-maximal-subset
  (implies (and (filter-on u s) (ultra-p u s) (filter-on v s) (subset u v))
           (subset v u))
  :hints (("Goal" :expand ((subset v u))
           :in-theory (disable ultra-p-necc int2-closed-necc upward-closed-necc
                               ultra-p int2-closed upward-closed)
           :use ((:instance ultra-p-necc (x (subset-witness v u)))
                 (:instance filter-member-subset (u v) (x (subset-witness v u)))
                 (:instance int2-closed-necc (u v) (x (subset-witness v u))
                            (y (diff s (subset-witness v u)))))))
  :props (zfc diff$prop))

(defthmz ultra-implies-maximal
  (implies (and (filter-on u s) (ultra-p u s))
           (maximal-filter-p u s))
  :hints (("Goal" :expand ((maximal-filter-p u s))
           :in-theory (disable filter-on ultra-p)
           :use ((:instance extensionality (x u) (y (maximal-filter-p-witness u s)))
                 (:instance ultra-maximal-subset (v (maximal-filter-p-witness u s))))))
  :props (zfc diff$prop))

;;; ---------------- maximal implies ultra

(defun-sk meets-in (u x y)
  (exists z (and (in z u) (subset (int2 z x) y))))

(in-theory (disable meets-in))

(zsub ext-filter (u x s) y (powerset s) (meets-in u x y))

(defthmz in-ext-filter
  (equal (in y (ext-filter u x s))
         (and (subset y s) (meets-in u x y)))
  :hints (("Goal" :in-theory (enable ext-filter$comprehension)))
  :props (zfc ext-filter$prop))

(in-theory (disable ext-filter$comprehension))

(defthmz ext-filter-subset-powerset
  (subset (ext-filter u x s) (powerset s))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc ext-filter$prop))

(defthmz s-in-ext-filter
  (implies (in s u) (in s (ext-filter u x s)))
  :hints (("Goal" :use ((:instance meets-in-suff (z s) (y s)))))
  :props (zfc diff$prop ext-filter$prop))

(defthmz subset-z-diff-when-int2-empty
  (implies (and (subset z s) (subset (int2 z x) 0))
           (subset z (diff s x)))
  :hints (("Goal" :expand ((subset z (diff s x)))
           :use ((:instance subset-necc (a (subset-witness z (diff s x))) (x (int2 z x)) (y 0)))
           :in-theory (disable subset-necc)))
  :props (zfc diff$prop))

(defthmz zero-not-in-ext-filter
  (implies (and (filter-on u s) (not (in (diff s x) u)))
           (not (in 0 (ext-filter u x s))))
  :hints (("Goal" :in-theory (disable upward-closed-necc upward-closed int2-closed)
           :expand ((meets-in u x 0))
           :use ((:instance subset-z-diff-when-int2-empty (z (meets-in-witness u x 0)))
                 (:instance upward-closed-necc (x (meets-in-witness u x 0)) (y (diff s x)))
                 (:instance filter-member-subset (x (meets-in-witness u x 0))))))
  :props (zfc diff$prop ext-filter$prop))

(defthmz ext-filter-upward-closed-lemma
  (implies (and (in y1 (ext-filter u x s)) (subset y1 y2) (subset y2 s))
           (in y2 (ext-filter u x s)))
  :hints (("Goal" :expand ((meets-in u x y1))
           :use ((:instance meets-in-suff (z (meets-in-witness u x y1)) (y y2))
                 (:instance subset-transitivity (x (int2 (meets-in-witness u x y1) x))
                            (y y1) (z y2)))))
  :props (zfc diff$prop ext-filter$prop))

(defthmz ext-filter-upward-closed
  (upward-closed (ext-filter u x s) s)
  :hints (("Goal" :in-theory (e/d (upward-closed) (in-ext-filter))))
  :props (zfc diff$prop ext-filter$prop))

(defthmz subset-int2-int2
  (implies (and (subset a c) (subset b d))
           (subset (int2 a b) (int2 c d)))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc diff$prop))

(defthmz int2-int2-x-lemma
  (subset (int2 (int2 z1 z2) x) (int2 (int2 z1 x) (int2 z2 x)))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc diff$prop))

(defthmz ext-filter-int2-closed-lemma
  (implies (and (int2-closed u)
                (in y1 (ext-filter u x s)) (in y2 (ext-filter u x s)))
           (in (int2 y1 y2) (ext-filter u x s)))
  :hints (("Goal" :in-theory (disable int2-closed-necc int2-closed subset-int2-int2
                                      int2-int2-x-lemma)
           :expand ((meets-in u x y1) (meets-in u x y2))
           :use ((:instance meets-in-suff (z (int2 (meets-in-witness u x y1)
                                                   (meets-in-witness u x y2)))
                            (y (int2 y1 y2)))
                 (:instance int2-closed-necc (x (meets-in-witness u x y1))
                            (y (meets-in-witness u x y2)))
                 (:instance int2-int2-x-lemma (z1 (meets-in-witness u x y1))
                            (z2 (meets-in-witness u x y2)))
                 (:instance subset-int2-int2
                            (a (int2 (meets-in-witness u x y1) x))
                            (b (int2 (meets-in-witness u x y2) x))
                            (c y1) (d y2))
                 (:instance subset-transitivity
                            (x (int2 (int2 (meets-in-witness u x y1)
                                           (meets-in-witness u x y2)) x))
                            (y (int2 (int2 (meets-in-witness u x y1) x)
                                     (int2 (meets-in-witness u x y2) x)))
                            (z (int2 y1 y2))))))
  :props (zfc diff$prop ext-filter$prop))

(defthmz ext-filter-int2-closed
  (implies (int2-closed u)
           (int2-closed (ext-filter u x s)))
  :hints (("Goal" :expand ((int2-closed (ext-filter u x s)))
           :in-theory (disable in-ext-filter)))
  :props (zfc diff$prop ext-filter$prop))

(defthmz ext-filter-is-filter
  (implies (and (filter-on u s) (not (in (diff s x) u)))
           (filter-on (ext-filter u x s) s))
  :hints (("Goal" :in-theory (disable upward-closed int2-closed in-ext-filter)))
  :props (zfc diff$prop ext-filter$prop))

(defthmz u-subset-ext-filter
  (implies (filter-on u s)
           (subset u (ext-filter u x s)))
  :hints (("Goal" :expand ((subset u (ext-filter u x s)))
           :in-theory (disable upward-closed int2-closed)
           :use ((:instance meets-in-suff (z (subset-witness u (ext-filter u x s)))
                            (y (subset-witness u (ext-filter u x s))))
                 (:instance filter-member-subset (x (subset-witness u (ext-filter u x s)))))))
  :props (zfc diff$prop ext-filter$prop))

(defthmz x-in-ext-filter
  (implies (and (in s u) (subset x s))
           (in x (ext-filter u x s)))
  :hints (("Goal" :use ((:instance meets-in-suff (z s) (y x)))))
  :props (zfc diff$prop ext-filter$prop))

(defthm filter-on-forward
  (implies (filter-on u s)
           (and (in s u) (not (in 0 u)) (subset u (powerset s))
                (upward-closed u s) (int2-closed u)))
  :rule-classes :forward-chaining)

(defthmz maximal-implies-ultra
  (implies (and (filter-on u s) (maximal-filter-p u s))
           (ultra-p u s))
  :hints (("Goal" :expand ((ultra-p u s))
           :in-theory (disable filter-on maximal-filter-p-necc maximal-filter-p
                               ext-filter-is-filter u-subset-ext-filter x-in-ext-filter)
           :use ((:instance maximal-filter-p-necc (v (ext-filter u (ultra-p-witness u s) s)))
                 (:instance ext-filter-is-filter (x (ultra-p-witness u s)))
                 (:instance u-subset-ext-filter (x (ultra-p-witness u s)))
                 (:instance x-in-ext-filter (x (ultra-p-witness u s))))))
  :props (zfc diff$prop ext-filter$prop))

(defthmz ultra-iff-maximal
  (implies (filter-on u s) (iff (ultra-p u s) (maximal-filter-p u s)))
  :hints (("Goal" :in-theory (disable filter-on ultra-p maximal-filter-p)
           :use (maximal-implies-ultra ultra-implies-maximal)))
  :props (zfc diff$prop ext-filter$prop))

;;; ---------------- finite member implies principal

(defthmz int2-singleton-not-in-lemma
  (implies (not (in a y))
           (subset (int2 y (pair a a)) 0))
  :hints (("Goal" :in-theory (e/d (subset) (subset-x-0))))
  :props (zfc diff$prop)
  :rule-classes nil)

(defthmz int2-singleton-not-in
  (implies (not (in a y))
           (equal (int2 y (pair a a)) 0))
  :hints (("Goal" :use (int2-singleton-not-in-lemma
                        (:instance extensionality (x (int2 y (pair a a))) (y 0)))))
  :props (zfc diff$prop))

(defthmz singleton-in-u-implies-in-pf
  (implies (and (filter-on u s) (in (pair a a) u) (in y u))
           (in y (principal-filter a s)))
  :hints (("Goal" :in-theory (e/d (principal-filter$comprehension)
                                  (int2-closed-necc int2-closed upward-closed))
           :use ((:instance int2-closed-necc (x y) (y (pair a a)))
                 (:instance filter-member-subset (x y)))))
  :props (zfc diff$prop principal-filter$prop))

(defthmz pf-in-u-when-singleton-in-u
  (implies (and (filter-on u s) (in (pair a a) u) (in y (principal-filter a s)))
           (in y u))
  :hints (("Goal" :in-theory (e/d (principal-filter$comprehension)
                                  (upward-closed-necc int2-closed upward-closed))
           :use ((:instance upward-closed-necc (x (pair a a)) (y y)))
           :expand ((subset (pair a a) y))))
  :props (zfc diff$prop principal-filter$prop))

(defthmz singleton-in-u-implies-a-in-s
  (implies (and (filter-on u s) (in (pair a a) u))
           (in a s))
  :hints (("Goal" :in-theory (disable int2-closed upward-closed filter-member-subset)
           :use ((:instance filter-member-subset (x (pair a a)))
                 (:instance subset-necc (a a) (x (pair a a)) (y s)))))
  :props (zfc diff$prop))

(defthmz singleton-in-u-implies-principal
  (implies (and (filter-on u s) (in (pair a a) u))
           (principal-p u s))
  :hints (("Goal" :in-theory (disable filter-on singleton-in-u-implies-in-pf
                                      pf-in-u-when-singleton-in-u)
           :use ((:instance principal-p-suff)
                 (:instance extensionality (x u) (y (principal-filter a s)))
                 (:instance singleton-in-u-implies-in-pf
                            (y (subset-witness u (principal-filter a s))))
                 (:instance pf-in-u-when-singleton-in-u
                            (y (subset-witness (principal-filter a s) u))))
           :expand ((subset u (principal-filter a s))
                    (subset (principal-filter a s) u))))
  :props (zfc diff$prop principal-filter$prop))

(in-theory (disable diff-distributes-over-diff))

(defun find-atom (f x u n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (let ((b (apply f (1- n))))
      (if (and (in b x) (in (pair b b) u))
          b
        (find-atom f (diff x (pair b b)) u (1- n))))))

(defthmz subset-diff-singleton-when-not-in
  (implies (not (in b x))
           (subset x (diff x (pair b b))))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc diff$prop))

(defthmz subset-int2-diff-singleton
  (subset (int2 x (diff s (pair b b))) (diff x (pair b b)))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc diff$prop))

(defthmz subset-diff-when-subset
  (implies (subset x s) (subset (diff x y) s))
  :hints (("Goal" :use ((:instance subset-transitivity (x (diff x y)) (y x) (z s)))))
  :props (zfc diff$prop))

(defthmz singleton-subset
  (implies (in b x) (subset (pair b b) x))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc))

(defthmz diff-singleton-in-u
  (implies (and (ultrafilter-on u s) (in x u)
                (not (and (in b x) (in (pair b b) u))))
           (in (diff x (pair b b)) u))
  :hints (("Goal"
           :in-theory (disable ultra-p-necc int2-closed-necc upward-closed-necc
                               ultra-p int2-closed upward-closed filter-member-subset)
           :cases ((in b x))
           :use ((:instance filter-member-subset (x x))
                 (:instance ultra-p-necc (x (pair b b)))
                 (:instance int2-closed-necc (x x) (y (diff s (pair b b))))
                 (:instance upward-closed-necc (x (int2 x (diff s (pair b b))))
                            (y (diff x (pair b b))))
                 (:instance upward-closed-necc (x x) (y (diff x (pair b b))))
                 (:instance subset-transitivity (x (pair b b)) (y x) (z s)))))
  :props (zfc diff$prop))

(defthm ultrafilter-on-forward
  (implies (ultrafilter-on u s)
           (and (filter-on u s) (ultra-p u s)))
  :rule-classes :forward-chaining)

(defthmz subset-n-1-when-subset-n
  (implies (and (posp n) (subset n d))
           (subset (+ -1 n) d))
  :hints (("Goal" :use ((:instance <=-implies-subset-on-natps (i (+ -1 n)) (j n))
                        (:instance subset-transitivity (x (+ -1 n)) (y n) (z d)))))
  :props (zfc))

(defthmz find-atom-works
  (implies (and (ultrafilter-on u s)
                (in x u)
                (funp f)
                (natp n)
                (subset n (domain f))
                (subset x (image (restrict f n))))
           (and (in (find-atom f x u n) x)
                (in (pair (find-atom f x u n) (find-atom f x u n)) u)))
  :hints (("Goal" :induct (find-atom f x u n)
           :in-theory (disable ultrafilter-on))
          ("Subgoal *1/3" :use ((:instance diff-singleton-in-u (b (apply f (1- n)))))
           :in-theory (disable ultrafilter-on diff-singleton-in-u))
          ("Subgoal *1/1" :use ((:instance extensionality (x x) (y 0)))
           :in-theory (e/d (in-natp) (ultrafilter-on))))
  :props (zfc prod2$prop diff$prop restrict$prop domain$prop inverse$prop))

(defthmz ultrafilter-with-finite-member-is-principal-lemma
  (implies (and (ultrafilter-on u s) (in x u)
                (funp f) (natp (domain f)) (subset x (image f)))
           (principal-p u s))
  :hints (("Goal" :in-theory (disable ultrafilter-on find-atom-works
                                      singleton-in-u-implies-principal)
           :use ((:instance find-atom-works (n (domain f)))
                 (:instance singleton-in-u-implies-principal
                            (a (find-atom f x u (domain f)))))))
  :props (zfc prod2$prop diff$prop restrict$prop domain$prop inverse$prop
              principal-filter$prop))

(defthmz ultrafilter-with-finite-member-is-principal
  (implies (and (ultrafilter-on u s) (in x u) (finite x))
           (principal-p u s))
  :hints (("Goal" :in-theory (disable ultrafilter-on)
           :expand ((finite x))))
  :props (zfc diff$prop principal-filter$prop
              prod2$prop restrict$prop domain$prop inverse$prop))

(defthmz ultrafilter-on-finite-set-is-principal
  (implies (and (ultrafilter-on u s) (finite s))
           (principal-p u s))
  :hints (("Goal" :in-theory (disable ultrafilter-on)
           :use ((:instance ultrafilter-with-finite-member-is-principal (x s)))))
  :props (zfc diff$prop principal-filter$prop
              prod2$prop restrict$prop domain$prop inverse$prop))

;;; ================ optional: nonprincipal ultrafilter on omega

;;; ---- omega is infinite

(defun bnd (f n)
  (if (zp n)
      0
    (max (bnd f (1- n)) (1+ (nfix (apply f (1- n)))))))

(defthm natp-bnd
  (natp (bnd f n))
  :rule-classes :type-prescription)

(defthm bnd-props
  (implies (not (zp n))
           (and (<= (bnd f (1- n)) (bnd f n))
                (implies (natp (apply f (1- n)))
                         (< (apply f (1- n)) (bnd f n)))))
  :rule-classes :linear)

(defthmz subset-bnd-step
  (implies (and (not (zp n))
                (subset (diff x (pair (apply f (1- n)) (apply f (1- n))))
                        (bnd f (1- n)))
                (subset x (omega)))
           (subset x (bnd f n)))
  :hints (("Goal" :expand ((subset x (bnd f n)))
           :in-theory (disable bnd)
           :use ((:instance subset-necc (a (subset-witness x (bnd f n)))
                            (x (diff x (pair (apply f (1- n)) (apply f (1- n)))))
                            (y (bnd f (1- n))))
                 (:instance subset-necc (a (subset-witness x (bnd f n)))
                            (x x) (y (omega)))
                 (:instance <=-implies-subset-on-natps (i (bnd f (1- n))) (j (bnd f n)))
                 (:instance subset-necc (a (subset-witness x (bnd f n)))
                            (x (bnd f (1- n))) (y (bnd f n)))
                 (:instance natp-<-implies-in (i (apply f (1- n))) (j (bnd f n))))))
  :props (zfc diff$prop))

(defun drop-ind (f x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list f x)
    (list f (drop-ind f (diff x (pair (apply f (1- n)) (apply f (1- n)))) (1- n)))))

(defthmz subset-bnd
  (implies (and (funp f)
                (natp n)
                (subset n (domain f))
                (subset x (image (restrict f n)))
                (subset x (omega)))
           (subset x (bnd f n)))
  :hints (("Goal" :induct (drop-ind f x n) :in-theory (disable bnd))
          ("Subgoal *1/1" :use ((:instance extensionality (x x) (y 0)))
           :in-theory (e/d (in-natp) (bnd))))
  :props (zfc prod2$prop diff$prop restrict$prop domain$prop inverse$prop))

(defthmz omega-not-subset-natp
  (implies (natp m) (not (subset (omega) m)))
  :hints (("Goal" :use ((:instance subset-necc (a m) (x (omega)) (y m))
                        (:instance in-irreflexive (x m)))
           :in-theory (disable subset-necc subset-preserves-in-2 subset-preserves-in-1
                               in-irreflexive)))
  :props (zfc))

(defthmz omega-not-finite
  (not (finite (omega)))
  :hints (("Goal" :expand ((finite (omega)))
           :use ((:instance subset-bnd (x (omega))
                            (f (finite-witness (omega)))
                            (n (domain (finite-witness (omega))))))
           :in-theory (disable subset-bnd bnd)))
  :props (zfc prod2$prop diff$prop restrict$prop domain$prop inverse$prop))

;;; ---- finiteness facts

(defthmz finite-0
  (finite 0)
  :hints (("Goal" :use ((:instance finite-suff (f 0) (s 0)))))
  :props (zfc domain$prop inverse$prop))

(defthmz pair-0-0-is-1
  (equal (pair 0 0) 1)
  :hints (("Goal" :use ((:instance n+1-as-union2 (n 0)))))
  :props (zfc))

(defthmz finite-singleton
  (finite (pair a a))
  :hints (("Goal" :use ((:instance finite-suff (f (pair (cons 0 a) (cons 0 a)))
                                   (s (pair a a)))
                        (:instance bijection-singleton (x 0) (y a)))
           :in-theory (disable bijection-singleton)))
  :props (zfc prod2$prop inverse$prop domain$prop))

;;; ---- the cofinite (Frechet) filter on omega

(zsub cof () x (powerset (omega)) (finite (diff (omega) x)))

(defthmz in-cof
  (equal (in x (cof))
         (and (subset x (omega)) (finite (diff (omega) x))))
  :hints (("Goal" :in-theory (enable cof$comprehension)))
  :props (zfc cof$prop))

(in-theory (disable cof$comprehension))

(defthmz diff-x-x-is-0
  (equal (diff x x) 0)
  :hints (("Goal" :use ((:instance subset-implies-diff-is-0 (x x) (y x)))))
  :props (zfc diff$prop))

(defthmz diff-x-0-is-x
  (equal (diff x 0) x)
  :hints (("Goal" :in-theory (enable extensionality-rewrite subset)))
  :props (zfc diff$prop))

(defthmz subset-diff-diff
  (implies (subset x y)
           (subset (diff s y) (diff s x)))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc diff$prop))

(defthmz cof-upward-closed
  (upward-closed (cof) (omega))
  :hints (("Goal" :in-theory (enable upward-closed)
           :use ((:instance subset-preserves-finite
                            (s1 (diff (omega) (mv-nth 0 (upward-closed-witness (cof) (omega)))))
                            (s2 (diff (omega) (mv-nth 1 (upward-closed-witness (cof) (omega)))))))))
  :props (zfc diff$prop cof$prop))

(defthmz cof-int2-closed
  (int2-closed (cof))
  :hints (("Goal" :in-theory (enable int2-closed)))
  :props (zfc diff$prop cof$prop domain$prop prod2$prop shift-domain$prop inverse$prop))

(defthmz cof-subset-powerset
  (subset (cof) (powerset (omega)))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc diff$prop cof$prop))

(defthmz cof-is-filter
  (filter-on (cof) (omega))
  :props (zfc diff$prop cof$prop prod2$prop restrict$prop domain$prop inverse$prop
              shift-domain$prop))

(in-theory (disable ultra-iff-maximal))

;;; ---- pool of filters extending cof, and the extension map

(defmacro defthmzp (name form &rest args)
  `(defthmz ,name ,form
     :props (zfc diff$prop cof$prop prod2$prop restrict$prop domain$prop inverse$prop
                 shift-domain$prop ext-filter$prop fpool$prop principal-filter$prop)
     ,@args))

(zsub fpool () v (powerset (powerset (omega)))
      (and (filter-on v (omega)) (subset (cof) v)))

(defthmz in-fpool
  (equal (in v (fpool))
         (and (filter-on v (omega)) (subset (cof) v)))
  :hints (("Goal" :in-theory (enable fpool$comprehension)))
  :props (zfc fpool$prop))

(in-theory (disable fpool$comprehension filter-on))

(defun gext (v)
  (if (ultra-p v (omega))
      v
    (ext-filter v (ultra-p-witness v (omega)) (omega))))

(defthmzp filter-on-gext
  (implies (filter-on v (omega))
           (filter-on (gext v) (omega)))
  :hints (("Goal" :in-theory (disable ext-filter-is-filter)
           :expand ((ultra-p v (omega)))
           :use ((:instance ext-filter-is-filter (u v) (s (omega))
                            (x (ultra-p-witness v (omega))))))))

(defthmzp subset-gext
  (implies (filter-on v (omega))
           (subset v (gext v)))
  :hints (("Goal" :in-theory (disable u-subset-ext-filter)
           :use ((:instance u-subset-ext-filter (u v) (s (omega))
                            (x (ultra-p-witness v (omega))))))))

(defthmzp gext-in-fpool
  (implies (in v (fpool))
           (in (gext v) (fpool)))
  :hints (("Goal" :in-theory (disable gext subset-gext)
           :use (subset-gext
                 (:instance subset-transitivity (x (cof)) (y v) (z (gext v)))))))

(defthmzp gext-proper-when-not-ultra
  (implies (and (filter-on v (omega)) (not (ultra-p v (omega))))
           (not (subset (gext v) v)))
  :hints (("Goal" :in-theory (disable x-in-ext-filter)
           :expand ((ultra-p v (omega)))
           :use ((:instance x-in-ext-filter (u v) (s (omega))
                            (x (ultra-p-witness v (omega))))
                 (:instance subset-necc (a (ultra-p-witness v (omega)))
                            (x (gext v)) (y v))))))

(in-theory (disable gext))

;;; ---- unions of chains

(defun-sk chain-p (c)
  (forall (a b) (implies (and (in a c) (in b c))
                         (or (subset a b) (subset b a)))))

(defthmz in-implies-subset-union-rewrite
  (implies (in v c) (subset v (union c)))
  :hints (("Goal" :expand ((subset v (union c)))
           :use ((:instance in-in-suff (y v) (a (subset-witness v (union c))) (x c)))))
  :props (zfc))

(defthmz in-union-chain-fpool-subset
  (implies (and (subset c (fpool)) (in y (union c)))
           (subset y (omega)))
  :hints (("Goal" :use ((:instance filter-member-subset (u (in-in-witness y c)) (x y) (s (omega))))
           :in-theory (e/d (in-in) (filter-member-subset))))
  :props (zfc fpool$prop))

(defthmz in-union-intro
  (implies (and (in x v) (in v c)) (in x (union c)))
  :hints (("Goal" :use ((:instance in-in-suff (y v) (a x) (x c)))))
  :props (zfc))

(defthmz in-union-elim
  (implies (in x (union c))
           (and (in x (in-in-witness x c))
                (in (in-in-witness x c) c)))
  :hints (("Goal" :in-theory (enable in-in)))
  :props (zfc))

(in-theory (disable in-union))

(defthmzp union-chain-subset-powerset
  (implies (subset c (fpool))
           (subset (union c) (powerset (omega))))
  :hints (("Goal" :expand ((subset (union c) (powerset (omega)))))))

(defthmzp omega-in-union-chain
  (implies (and (subset c (fpool)) (not (equal c 0)))
           (in (omega) (union c)))
  :hints (("Goal" :use ((:instance in-union-intro (x (omega)) (v (min-in c)))
                        (:instance subset-necc (a (min-in c)) (x c) (y (fpool))))
           :in-theory (disable in-union-intro subset-necc))))

(defthmzp zero-not-in-union-chain
  (implies (subset c (fpool))
           (not (in 0 (union c))))
  :hints (("Goal" :use ((:instance in-union-elim (x 0))
                        (:instance subset-necc (a (in-in-witness 0 c)) (x c) (y (fpool))))
           :in-theory (disable in-union-elim subset-necc))))

(defthmzp union-chain-upward-closed-lemma
  (implies (and (subset c (fpool)) (in x (union c)) (subset x y) (subset y (omega)))
           (in y (union c)))
  :hints (("Goal" :use ((:instance in-union-elim (x x))
                        (:instance subset-necc (a (in-in-witness x c)) (x c) (y (fpool)))
                        (:instance upward-closed-necc (u (in-in-witness x c)) (s (omega)))
                        (:instance in-union-intro (x y) (v (in-in-witness x c))))
           :in-theory (disable in-union-elim subset-necc upward-closed-necc in-union-intro
                               upward-closed))))

(defthmzp union-chain-upward-closed
  (implies (subset c (fpool))
           (upward-closed (union c) (omega)))
  :hints (("Goal" :expand ((upward-closed (union c) (omega))))))

(defthmzp union-chain-int2-lemma
  (implies (and (subset c (fpool)) (chain-p c)
                (in x (union c)) (in y (union c)))
           (in (int2 x y) (union c)))
  :hints (("Goal" :use ((:instance in-union-elim (x x))
                        (:instance in-union-elim (x y))
                        (:instance chain-p-necc (a (in-in-witness x c)) (b (in-in-witness y c)))
                        (:instance subset-necc (a (in-in-witness x c)) (x c) (y (fpool)))
                        (:instance subset-necc (a (in-in-witness y c)) (x c) (y (fpool)))
                        (:instance subset-necc (a x) (x (in-in-witness x c)) (y (in-in-witness y c)))
                        (:instance subset-necc (a y) (x (in-in-witness y c)) (y (in-in-witness x c)))
                        (:instance int2-closed-necc (u (in-in-witness x c)))
                        (:instance int2-closed-necc (u (in-in-witness y c)))
                        (:instance in-union-intro (x (int2 x y)) (v (in-in-witness x c)))
                        (:instance in-union-intro (x (int2 x y)) (v (in-in-witness y c))))
           :in-theory (disable in-union-elim subset-necc int2-closed-necc in-union-intro
                               chain-p-necc chain-p int2-closed upward-closed
                               subset-preserves-in-1 subset-preserves-in-2))))

(defthmzp union-chain-int2-closed
  (implies (and (subset c (fpool)) (chain-p c))
           (int2-closed (union c)))
  :hints (("Goal" :expand ((int2-closed (union c)))
           :in-theory (disable chain-p))))

(defthmzp cof-subset-union-chain
  (implies (and (subset c (fpool)) (not (equal c 0)))
           (subset (cof) (union c)))
  :hints (("Goal" :use ((:instance subset-necc (a (min-in c)) (x c) (y (fpool)))
                        (:instance subset-transitivity (x (cof)) (y (min-in c)) (z (union c))))
           :in-theory (disable subset-necc))))

(defthmzp union-chain-in-fpool
  (implies (and (subset c (fpool)) (chain-p c) (not (equal c 0)))
           (in (union c) (fpool)))
  :hints (("Goal" :in-theory (e/d (filter-on) (chain-p upward-closed int2-closed)))))

;;; ---- towers

(defun-sk g-closed (tw)
  (forall v (implies (in v tw) (in (gext v) tw))))

(defun-sk chain-closed (tw)
  (forall c (implies (and (subset c tw) (chain-p c) (not (equal c 0)))
                     (in (union c) tw))))

(defun tower-p (tw)
  (and (subset tw (fpool))
       (in (cof) tw)
       (g-closed tw)
       (chain-closed tw)))

(defun-sk in-all-towers (v)
  (forall tw (implies (tower-p tw) (in v tw))))

(in-theory (disable g-closed chain-closed in-all-towers))

(zsub mtower () v (fpool) (in-all-towers v))

(defthmz in-mtower
  (equal (in v (mtower))
         (and (in v (fpool)) (in-all-towers v)))
  :hints (("Goal" :in-theory (enable mtower$comprehension)))
  :props (zfc mtower$prop))

(in-theory (disable mtower$comprehension))

(defmacro defthmzq (name form &rest args)
  `(defthmz ,name ,form
     :props (zfc diff$prop cof$prop prod2$prop restrict$prop domain$prop inverse$prop
                 shift-domain$prop ext-filter$prop fpool$prop principal-filter$prop
                 mtower$prop)
     ,@args))

(defthmzq mtower-subset-fpool
  (subset (mtower) (fpool))
  :hints (("Goal" :in-theory (enable subset))))

(defthmzq cof-in-fpool
  (in (cof) (fpool))
  :hints (("Goal" :in-theory (enable filter-on))))

(defthmzq cof-in-mtower
  (in (cof) (mtower))
  :hints (("Goal" :in-theory (enable in-all-towers))))

(defthmzq mtower-g-closed-lemma
  (implies (in v (mtower))
           (in (gext v) (mtower)))
  :hints (("Goal" :expand ((in-all-towers (gext v)))
           :use ((:instance in-all-towers-necc (tw (in-all-towers-witness (gext v))))
                 (:instance g-closed-necc (tw (in-all-towers-witness (gext v)))))
           :in-theory (disable in-all-towers-necc g-closed-necc))))

(defthmzq mtower-g-closed
  (g-closed (mtower))
  :hints (("Goal" :in-theory (enable g-closed))))

(defthmzq subset-subset-mtower-tower
  (implies (and (subset c (mtower)) (tower-p tw))
           (subset c tw))
  :hints (("Goal" :expand ((subset c tw))
           :use ((:instance subset-necc (a (subset-witness c tw)) (x c) (y (mtower)))
                 (:instance in-all-towers-necc (v (subset-witness c tw))))
           :in-theory (disable subset-necc in-all-towers-necc tower-p))))

(defthmzq subset-mtower-fpool
  (implies (subset c (mtower)) (subset c (fpool)))
  :hints (("Goal" :use ((:instance subset-transitivity (x c) (y (mtower)) (z (fpool)))))))

(defthmzq mtower-chain-closed-lemma
  (implies (and (subset c (mtower)) (chain-p c) (not (equal c 0)))
           (in (union c) (mtower)))
  :hints (("Goal" :expand ((in-all-towers (union c)))
           :use ((:instance subset-subset-mtower-tower (tw (in-all-towers-witness (union c))))
                 (:instance chain-closed-necc (tw (in-all-towers-witness (union c)))))
           :in-theory (disable chain-closed-necc subset-subset-mtower-tower chain-p))))

(defthmzq mtower-chain-closed
  (chain-closed (mtower))
  :hints (("Goal" :in-theory (e/d (chain-closed) (chain-p)))))

(defthmzq mtower-is-tower
  (tower-p (mtower)))

(defthmzq mtower-least
  (implies (tower-p tw) (subset (mtower) tw))
  :hints (("Goal" :in-theory (disable tower-p))))

(in-theory (disable tower-p))

;;; ---- extreme points

(defun-sk extreme-p (c)
  (forall x (implies (and (in x (mtower)) (subset x c) (not (equal x c)))
                     (subset (gext x) c))))

(in-theory (disable extreme-p))

(zsub mc (c) x (mtower) (or (subset x c) (subset (gext c) x)))

(defmacro defthmzr (name form &rest args)
  `(defthmz ,name ,form
     :props (zfc diff$prop cof$prop prod2$prop restrict$prop domain$prop inverse$prop
                 shift-domain$prop ext-filter$prop fpool$prop principal-filter$prop
                 mtower$prop mc$prop)
     ,@args))

(defthmzr in-mc
  (equal (in x (mc c))
         (and (in x (mtower)) (or (subset x c) (subset (gext c) x))))
  :hints (("Goal" :in-theory (enable mc$comprehension))))

(in-theory (disable mc$comprehension))

(defthmzq in-mtower-implies-filter
  (implies (in v (mtower))
           (and (filter-on v (omega)) (subset (cof) v) (in v (fpool))))
  :hints (("Goal" :use ((:instance subset-necc (a v) (x (mtower)) (y (fpool))))
           :in-theory (disable subset-necc))))

(defthmzr mc-subset-mtower
  (subset (mc c) (mtower))
  :hints (("Goal" :in-theory (enable subset))))

(defthmzr mc-subset-fpool
  (subset (mc c) (fpool))
  :hints (("Goal" :use ((:instance subset-transitivity (x (mc c)) (y (mtower)) (z (fpool)))))))

(defthmzr cof-in-mc
  (implies (in c (mtower))
           (in (cof) (mc c))))

(defthmzr mc-g-closed-lemma
  (implies (and (in c (mtower)) (extreme-p c) (in v (mc c)))
           (in (gext v) (mc c)))
  :hints (("Goal" :cases ((equal v c))
           :use ((:instance extreme-p-necc (x v))
                 (:instance subset-gext (v v))
                 (:instance subset-transitivity (x (gext c)) (y v) (z (gext v))))
           :in-theory (disable extreme-p-necc subset-gext))))

(defthmzr mc-g-closed
  (implies (and (in c (mtower)) (extreme-p c))
           (g-closed (mc c)))
  :hints (("Goal" :expand ((g-closed (mc c))) :in-theory (disable in-mc))))

(defthmzr union-mc-lemma
  (implies (and (subset cc (mc c)) (not (subset (union cc) c)))
           (subset (gext c) (union cc)))
  :hints (("Goal"
           :use ((:instance in-union-elim (x (subset-witness (union cc) c)) (c cc))
                 (:instance subset-necc (a (in-in-witness (subset-witness (union cc) c) cc))
                            (x cc) (y (mc c)))
                 (:instance subset-necc (a (subset-witness (union cc) c))
                            (x (in-in-witness (subset-witness (union cc) c) cc)) (y c))
                 (:instance in-implies-subset-union-rewrite
                            (v (in-in-witness (subset-witness (union cc) c) cc)) (c cc))
                 (:instance subset-transitivity (x (gext c))
                            (y (in-in-witness (subset-witness (union cc) c) cc))
                            (z (union cc))))
           :expand ((subset (union cc) c))
           :in-theory (disable in-union-elim subset-necc in-implies-subset-union-rewrite
                               subset-preserves-in-1 subset-preserves-in-2))))

(defthmzr subset-mc-mtower
  (implies (subset cc (mc c)) (subset cc (mtower)))
  :hints (("Goal" :use ((:instance subset-transitivity (x cc) (y (mc c)) (z (mtower)))))))

(defthmzr mc-chain-closed-lemma
  (implies (and (subset cc (mc c)) (chain-p cc) (not (equal cc 0)))
           (in (union cc) (mc c)))
  :hints (("Goal" :use (union-mc-lemma
                        (:instance mtower-chain-closed-lemma (c cc)))
           :in-theory (disable union-mc-lemma mtower-chain-closed-lemma chain-p))))

(defthmzr mc-chain-closed
  (chain-closed (mc c))
  :hints (("Goal" :expand ((chain-closed (mc c))) :in-theory (disable chain-p in-mc))))

(defthmzr mc-is-tower
  (implies (and (in c (mtower)) (extreme-p c))
           (tower-p (mc c)))
  :hints (("Goal" :in-theory (e/d (tower-p) (in-mc)))))

(defthmzr extreme-comparable
  (implies (and (in c (mtower)) (extreme-p c) (in x (mtower)))
           (or (subset x c) (subset (gext c) x)))
  :hints (("Goal" :use (mc-is-tower
                        (:instance mtower-least (tw (mc c)))
                        (:instance subset-necc (a x) (x (mtower)) (y (mc c))))
           :in-theory (disable mc-is-tower mtower-least subset-necc)))
  :rule-classes nil)

(zsub eset () c (mtower) (extreme-p c))

(defmacro defthmzs (name form &rest args)
  `(defthmz ,name ,form
     :props (zfc diff$prop cof$prop prod2$prop restrict$prop domain$prop inverse$prop
                 shift-domain$prop ext-filter$prop fpool$prop principal-filter$prop
                 mtower$prop mc$prop eset$prop)
     ,@args))

(defthmzs in-eset
  (equal (in c (eset))
         (and (in c (mtower)) (extreme-p c)))
  :hints (("Goal" :in-theory (enable eset$comprehension))))

(in-theory (disable eset$comprehension))

(defthmzs eset-subset-fpool
  (subset (eset) (fpool))
  :hints (("Goal" :in-theory (enable subset))))

(defthmzs cof-extreme
  (extreme-p (cof))
  :hints (("Goal" :expand ((extreme-p (cof)))
           :use ((:instance extensionality (x (extreme-p-witness (cof))) (y (cof)))))))

(defthmzs gext-extreme
  (implies (and (in c (mtower)) (extreme-p c))
           (extreme-p (gext c)))
  :hints (("Goal" :expand ((extreme-p (gext c)))
           :cases ((equal (extreme-p-witness (gext c)) c))
           :use ((:instance extreme-comparable (x (extreme-p-witness (gext c))))
                 (:instance extensionality (x (extreme-p-witness (gext c))) (y (gext c)))
                 (:instance extreme-p-necc (x (extreme-p-witness (gext c))))
                 (:instance subset-gext (v c))
                 (:instance subset-transitivity (x (gext (extreme-p-witness (gext c))))
                            (y c) (z (gext c))))
           :in-theory (disable extreme-p-necc subset-gext))))

(defthmzs eset-g-closed
  (g-closed (eset))
  :hints (("Goal" :expand ((g-closed (eset))))))

(defthmzs union-eset-extreme
  (implies (and (subset cc (eset)) (not (equal cc 0)) (chain-p cc)
                (in x (mtower)) (subset x (union cc)) (not (equal x (union cc))))
           (subset (gext x) (union cc)))
  :hints (("Goal"
           :use ((:instance extensionality (x x) (y (union cc)))
                 (:instance in-union-elim (x (subset-witness (union cc) x)) (c cc))
                 (:instance subset-necc (a (in-in-witness (subset-witness (union cc) x) cc))
                            (x cc) (y (eset)))
                 (:instance extreme-comparable
                            (c (in-in-witness (subset-witness (union cc) x) cc)) (x x))
                 (:instance subset-gext (v (in-in-witness (subset-witness (union cc) x) cc)))
                 (:instance subset-transitivity
                            (x (in-in-witness (subset-witness (union cc) x) cc))
                            (y (gext (in-in-witness (subset-witness (union cc) x) cc)))
                            (z x))
                 (:instance subset-necc (a (subset-witness (union cc) x))
                            (x (in-in-witness (subset-witness (union cc) x) cc)) (y x))
                 (:instance extreme-p-necc
                            (c (in-in-witness (subset-witness (union cc) x) cc)) (x x))
                 (:instance in-implies-subset-union-rewrite
                            (v (in-in-witness (subset-witness (union cc) x) cc)) (c cc))
                 (:instance subset-transitivity (x (gext x))
                            (y (in-in-witness (subset-witness (union cc) x) cc))
                            (z (union cc))))
           :expand ((subset (union cc) x))
           :in-theory (disable in-union-elim subset-necc in-implies-subset-union-rewrite
                               subset-preserves-in-1 subset-preserves-in-2 subset-gext
                               extreme-p-necc chain-p))))

(defthmzs subset-eset-mtower
  (implies (subset cc (eset)) (subset cc (mtower)))
  :hints (("Goal" :expand ((subset cc (mtower)))
           :use ((:instance subset-necc (a (subset-witness cc (mtower))) (x cc) (y (eset))))
           :in-theory (disable subset-necc))))

(defthmzs eset-chain-closed-lemma
  (implies (and (subset cc (eset)) (chain-p cc) (not (equal cc 0)))
           (in (union cc) (eset)))
  :hints (("Goal" :expand ((extreme-p (union cc)))
           :use ((:instance mtower-chain-closed-lemma (c cc))
                 (:instance union-eset-extreme (x (extreme-p-witness (union cc)))))
           :in-theory (disable union-eset-extreme mtower-chain-closed-lemma chain-p))))

(defthmzs eset-chain-closed
  (chain-closed (eset))
  :hints (("Goal" :expand ((chain-closed (eset))) :in-theory (disable chain-p in-eset))))

(defthmzs cof-in-eset
  (in (cof) (eset)))

(defthmzs eset-is-tower
  (tower-p (eset))
  :hints (("Goal" :in-theory (e/d (tower-p) (in-eset)))))

(defthmzs all-extreme
  (implies (in c (mtower)) (extreme-p c))
  :hints (("Goal" :use ((:instance mtower-least (tw (eset)))
                        (:instance subset-necc (a c) (x (mtower)) (y (eset))))
           :in-theory (disable mtower-least subset-necc))))

(defthmzs mtower-is-chain
  (chain-p (mtower))
  :hints (("Goal" :expand ((chain-p (mtower)))
           :use ((:instance extreme-comparable
                            (c (mv-nth 1 (chain-p-witness (mtower))))
                            (x (mv-nth 0 (chain-p-witness (mtower)))))
                 (:instance subset-gext (v (mv-nth 1 (chain-p-witness (mtower)))))
                 (:instance subset-transitivity
                            (x (mv-nth 1 (chain-p-witness (mtower))))
                            (y (gext (mv-nth 1 (chain-p-witness (mtower)))))
                            (z (mv-nth 0 (chain-p-witness (mtower))))))
           :in-theory (disable subset-gext))))

;;; ---- the union of the least tower is a nonprincipal ultrafilter

(defthmzs mtower-not-empty
  (not (equal (mtower) 0))
  :hints (("Goal" :use cof-in-mtower :in-theory (disable cof-in-mtower))))

(defthmzs union-mtower-in-mtower
  (in (union (mtower)) (mtower))
  :hints (("Goal" :use ((:instance mtower-chain-closed-lemma (c (mtower))))
           :in-theory (disable mtower-chain-closed-lemma))))

(defthmzs union-mtower-ultra
  (ultra-p (union (mtower)) (omega))
  :hints (("Goal" :use ((:instance gext-proper-when-not-ultra (v (union (mtower))))
                        (:instance mtower-g-closed-lemma (v (union (mtower))))
                        (:instance in-implies-subset-union-rewrite
                                   (v (gext (union (mtower)))) (c (mtower))))
           :in-theory (disable gext-proper-when-not-ultra mtower-g-closed-lemma
                               in-implies-subset-union-rewrite))))

(defthmz subset-diff-diff-singleton
  (subset (diff s (diff s (pair a a))) (pair a a))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc diff$prop))

(defthmzs cofinite-singleton-complement
  (in (diff (omega) (pair a a)) (cof))
  :hints (("Goal" :use ((:instance subset-preserves-finite
                                   (s1 (pair a a))
                                   (s2 (diff (omega) (diff (omega) (pair a a)))))))))

(defthmzs union-mtower-not-principal
  (not (principal-p (union (mtower)) (omega)))
  :hints (("Goal" :expand ((principal-p (union (mtower)) (omega)))
           :use ((:instance cofinite-singleton-complement
                            (a (principal-p-witness (union (mtower)) (omega))))
                 (:instance in-mtower-implies-filter (v (union (mtower))))
                 (:instance subset-necc
                            (a (diff (omega) (pair (principal-p-witness (union (mtower)) (omega))
                                                   (principal-p-witness (union (mtower)) (omega)))))
                            (x (cof)) (y (union (mtower)))))
           :in-theory (e/d (principal-filter$comprehension)
                           (cofinite-singleton-complement in-mtower-implies-filter
                                                          subset-necc)))))

(defthmz nonprincipal-ultrafilter-exists
  (exists-nonprincipal-ultrafilter (omega))
  :hints (("Goal" :use ((:instance exists-nonprincipal-ultrafilter-suff
                                   (u (union (mtower))) (s (omega)))
                        (:instance in-mtower-implies-filter (v (union (mtower)))))
           :in-theory (disable in-mtower-implies-filter)))
  :props (zfc diff$prop principal-filter$prop
              cof$prop prod2$prop restrict$prop domain$prop inverse$prop
              shift-domain$prop ext-filter$prop fpool$prop mtower$prop mc$prop eset$prop))
