(in-package "ZF")

(include-book "defs")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 1: a finite set of naturals is bounded.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun maxf (f d)
  (if (zp d)
      0
    (max (nfix (apply f (1- d)))
         (maxf f (1- d)))))

(defthm natp-maxf
  (natp (maxf f d))
  :hints (("Goal" :in-theory (enable natp)))
  :rule-classes :type-prescription)

(defthm maxf-bound
  (implies (and (natp j) (natp d) (< j d))
           (<= (nfix (apply f j)) (maxf f d)))
  :hints (("Goal" :in-theory (enable natp)))
  :rule-classes nil)

(defun finite-bound (s)
  (let ((f (finite-witness s)))
    (maxf f (domain f))))

(defthmz finite-bounded
  (implies (and (finite s) (in x s) (natp x))
           (<= x (finite-bound s)))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal"
           :in-theory (enable finite in-natp)
           :use ((:instance maxf-bound
                            (f (finite-witness s))
                            (d (domain (finite-witness s)))
                            (j (apply (inverse (finite-witness s)) x)))
                 (:instance in-image-implies-in-apply-inverse-domain
                            (r (finite-witness s))
                            (y x)
                            (d (domain (finite-witness s))))
                 (:instance apply-apply-inverse (f (finite-witness s)))))))

(in-theory (disable finite-bound))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 2: stages, represented as lists of (element . color) pairs.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun in-stage (n lst c)
  (if (endp lst)
      (natp n)
    (and (in-stage n (cdr lst) c)
         (< (caar lst) n)
         (equal (apply c (cons (caar lst) n)) (cdar lst)))))

(defthm in-stage-natp
  (implies (in-stage n lst c)
           (natp n))
  :rule-classes :forward-chaining)

(defun-sk stage-above (m lst c)
  (exists n (and (in-stage n lst c) (< m n))))

(defun-sk stage-unbounded (lst c)
  (forall m (implies (natp m) (stage-above m lst c))))

(defun pick (lst c)
  (stage-above-witness 0 lst c))

(defthm pick-in-stage
  (implies (stage-unbounded lst c)
           (in-stage (pick lst c) lst c))
  :hints (("Goal" :use ((:instance stage-unbounded-necc (m 0))))))

(defun-sk some-good-color (a lst c r)
  (exists k (and (natp k) (< k r)
                 (stage-unbounded (cons (cons a k) lst) c))))

(defun max-bound (j a lst c)
  (if (zp j)
      0
    (max (nfix (stage-unbounded-witness (cons (cons a (1- j)) lst) c))
         (max-bound (1- j) a lst c))))

(defthm max-bound-ge
  (implies (and (natp k) (natp j) (< k j))
           (<= (nfix (stage-unbounded-witness (cons (cons a k) lst) c))
               (max-bound j a lst c)))
  :hints (("Goal" :in-theory (enable natp)))
  :rule-classes nil)

(defthm natp-max-bound
  (natp (max-bound j a lst c))
  :hints (("Goal" :in-theory (enable natp)))
  :rule-classes :type-prescription)

(defthmz color-in-range
  (implies (and (natp a) (natp n) (natp r)
                (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) r))
           (and (natp (apply c (cons a n)))
                (< (apply c (cons a n)) r)))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal"
           :use ((:instance in-apply-image (r c) (x (cons a n)))
                 (:instance in-natp (i (apply c (cons a n))) (j r))
                 (:instance subset-necc (a (apply c (cons a n)))
                            (x (image c)) (y r)))))
  :rule-classes nil)

(defthmz pigeonhole-stage
  (implies (and (stage-unbounded lst c)
                (in-stage a lst c)
                (natp r)
                (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) r))
           (some-good-color a lst c r))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal"
           :in-theory (disable stage-unbounded stage-above max-bound)
           :use
           ((:instance stage-unbounded-necc
                       (m (max a (max-bound r a lst c))))
            (:instance color-in-range
                       (n (stage-above-witness (max a (max-bound r a lst c))
                                               lst c)))
            (:instance some-good-color-suff
                       (k (apply c
                                 (cons a
                                       (stage-above-witness
                                        (max a (max-bound r a lst c))
                                        lst c)))))
            (:instance max-bound-ge
                       (j r)
                       (k (apply c
                                 (cons a
                                       (stage-above-witness
                                        (max a (max-bound r a lst c))
                                        lst c)))))
            (:instance stage-unbounded
                       (lst (cons (cons a
                                        (apply c
                                               (cons a
                                                     (stage-above-witness
                                                      (max a (max-bound r a lst c))
                                                      lst c))))
                                  lst)))
            (:instance stage-above-suff
                       (n (stage-above-witness (max a (max-bound r a lst c))
                                               lst c))
                       (m (stage-unbounded-witness
                           (cons (cons a
                                       (apply c
                                              (cons a
                                                    (stage-above-witness
                                                     (max a (max-bound r a lst c))
                                                     lst c))))
                                 lst)
                           c))
                       (lst (cons (cons a
                                        (apply c
                                               (cons a
                                                     (stage-above-witness
                                                      (max a (max-bound r a lst c))
                                                      lst c))))
                                  lst)))
            (:instance stage-above
                       (m (max a (max-bound r a lst c))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 3: the sequence of elements and colors.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun build (i c r)
  (if (zp i)
      nil
    (let* ((lst (build (1- i) c r))
           (a (pick lst c)))
      (cons (cons a (some-good-color-witness a lst c r))
            lst))))

(defthm stage-unbounded-nil
  (stage-unbounded nil c)
  :hints (("Goal"
           :in-theory (enable natp)
           :use ((:instance stage-above-suff
                            (lst nil)
                            (m (stage-unbounded-witness nil c))
                            (n (+ 1 (stage-unbounded-witness nil c))))))))

(defthmz build-unbounded
  (implies (and (natp r)
                (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) r))
           (stage-unbounded (build i c r) c))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal" :induct (build i c r)
           :in-theory (disable stage-unbounded pick))
          ("Subgoal *1/2"
           :use ((:instance pigeonhole-stage
                            (lst (build (1- i) c r))
                            (a (pick (build (1- i) c r) c)))
                 (:instance some-good-color
                            (lst (build (1- i) c r))
                            (a (pick (build (1- i) c r) c)))))))

(defun elt-at (i c r)
  (pick (build i c r) c))

(defun color-at (i c r)
  (some-good-color-witness (elt-at i c r) (build i c r) c r))

(defthmz color-at-range
  (implies (and (natp r)
                (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) r))
           (and (natp (color-at i c r))
                (< (color-at i c r) r)))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal"
           :in-theory (disable stage-unbounded pick)
           :use ((:instance pigeonhole-stage
                            (lst (build i c r))
                            (a (pick (build i c r) c)))
                 (:instance build-unbounded)
                 (:instance some-good-color
                            (lst (build i c r))
                            (a (pick (build i c r) c)))))))

(defthmz elt-in-stage
  (implies (and (natp r)
                (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) r))
           (in-stage (elt-at i c r) (build i c r) c))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal"
           :in-theory (disable stage-unbounded pick)
           :use ((:instance build-unbounded)))))

(defthm stage-mono
  (implies (and (natp i) (natp j) (<= i j)
                (in-stage n (build j c r) c))
           (in-stage n (build i c r) c))
  :hints (("Goal" :induct (build j c r)
           :in-theory (e/d (natp) (pick)))))

(defthm in-stage-build-plus-1
  (implies (and (natp i)
                (in-stage n (build (+ 1 i) c r) c))
           (and (< (elt-at i c r) n)
                (equal (apply c (cons (elt-at i c r) n))
                       (color-at i c r))))
  :hints (("Goal" :expand ((build (+ 1 i) c r))
           :in-theory (disable pick)))
  :rule-classes nil)

(defthmz elt-strict
  (implies (and (natp r)
                (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) r)
                (natp i) (natp j) (< i j))
           (and (< (elt-at i c r) (elt-at j c r))
                (equal (apply c (cons (elt-at i c r) (elt-at j c r)))
                       (color-at i c r))))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal"
           :in-theory (disable elt-at color-at build)
           :use ((:instance elt-in-stage (i j))
                 (:instance stage-mono (i (+ 1 i)) (n (elt-at j c r)))
                 (:instance in-stage-build-plus-1 (n (elt-at j c r)))))))

(defthmz elt-natp
  (implies (and (natp r)
                (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) r))
           (natp (elt-at i c r)))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal"
           :in-theory (disable elt-at build elt-in-stage)
           :use ((:instance elt-in-stage)
                 (:instance in-stage-natp
                            (n (elt-at i c r))
                            (lst (build i c r)))))))

(defthmz elt-ge-index
  (implies (and (natp r)
                (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) r)
                (natp i))
           (<= i (elt-at i c r)))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal" :induct (natp-induction i)
           :in-theory (e/d (natp) (elt-at color-at build elt-strict elt-natp)))
          ("Subgoal *1/2"
           :use ((:instance elt-strict (i (1- i)) (j i))
                 (:instance elt-natp (i (1- i)))
                 (:instance elt-natp)))
          ("Subgoal *1/1"
           :use ((:instance elt-natp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 4: some color occurs infinitely often.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun-sk color-above (m k c r)
  (exists i (and (natp i) (< m i) (equal (color-at i c r) k))))

(defun-sk color-infinite (k c r)
  (forall m (implies (natp m) (color-above m k c r))))

(defun-sk some-infinite-color (c r)
  (exists k (and (natp k) (< k r) (color-infinite k c r))))

(defun max-bound2 (j c r)
  (if (zp j)
      0
    (max (nfix (color-infinite-witness (1- j) c r))
         (max-bound2 (1- j) c r))))

(defthm max-bound2-ge
  (implies (and (natp k) (natp j) (< k j))
           (<= (nfix (color-infinite-witness k c r))
               (max-bound2 j c r)))
  :hints (("Goal" :in-theory (enable natp)))
  :rule-classes nil)

(defthm natp-max-bound2
  (natp (max-bound2 j c r))
  :hints (("Goal" :in-theory (enable natp)))
  :rule-classes :type-prescription)

(defthmz pigeonhole-colors
  (implies (and (natp r)
                (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) r))
           (some-infinite-color c r))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal"
           :in-theory (e/d (natp)
                           (color-infinite color-above max-bound2 color-at))
           :use
           ((:instance color-at-range (i (+ 1 (max-bound2 r c r))))
            (:instance some-infinite-color-suff
                       (k (color-at (+ 1 (max-bound2 r c r)) c r)))
            (:instance max-bound2-ge
                       (j r)
                       (k (color-at (+ 1 (max-bound2 r c r)) c r)))
            (:instance color-infinite
                       (k (color-at (+ 1 (max-bound2 r c r)) c r)))
            (:instance color-above-suff
                       (i (+ 1 (max-bound2 r c r)))
                       (k (color-at (+ 1 (max-bound2 r c r)) c r))
                       (m (color-infinite-witness
                           (color-at (+ 1 (max-bound2 r c r)) c r)
                           c r)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Part 5: the homogeneous set.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun-sk hom-index (x c r k)
  (exists i (and (natp i)
                 (equal (color-at i c r) k)
                 (equal (elt-at i c r) x))))

(zsub hom-set (c r k)
      x
      (omega)
      (hom-index x c r k))

(defthmz subset-hom-set-omega
  (subset (hom-set c r k) (omega))
  :props (zfc hom-set$prop)
  :hints (("Goal" :in-theory (enable subset))))

(defthmz homogeneous-hom-set
  (implies (and (natp r)
                (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) r))
           (homogeneous (hom-set c r k) c k))
  :props (zfc prod2$prop domain$prop inverse$prop hom-set$prop)
  :hints (("Goal"
           :in-theory (disable elt-at color-at hom-index)
           :expand ((homogeneous (hom-set c r k) c k)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (hom-index) (elt-at color-at))))
          (and stable-under-simplificationp
               (let ((m '(mv-nth 0 (homogeneous-witness (hom-set c r k) c k)))
                     (n '(mv-nth 1 (homogeneous-witness (hom-set c r k) c k))))
                 `(:use ((:instance elt-strict
                                    (i (hom-index-witness ,m c r k))
                                    (j (hom-index-witness ,n c r k)))
                         (:instance elt-strict
                                    (j (hom-index-witness ,m c r k))
                                    (i (hom-index-witness ,n c r k)))))))))

(defthmz hom-set-not-finite
  (implies (and (natp r)
                (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) r)
                (color-infinite k c r))
           (not (finite (hom-set c r k))))
  :props (zfc prod2$prop domain$prop inverse$prop hom-set$prop)
  :hints (("Goal"
           :in-theory (disable elt-at color-at hom-index color-infinite
                               color-above elt-ge-index elt-natp
                               finite-bounded hom-index-suff)
           :use ((:instance color-infinite-necc
                            (m (finite-bound (hom-set c r k))))
                 (:instance color-above
                            (m (finite-bound (hom-set c r k))))
                 (:instance hom-index-suff
                            (i (color-above-witness
                                (finite-bound (hom-set c r k)) k c r))
                            (x (elt-at (color-above-witness
                                        (finite-bound (hom-set c r k)) k c r)
                                       c r)))
                 (:instance elt-ge-index
                            (i (color-above-witness
                                (finite-bound (hom-set c r k)) k c r)))
                 (:instance elt-natp
                            (i (color-above-witness
                                (finite-bound (hom-set c r k)) k c r)))
                 (:instance finite-bounded
                            (s (hom-set c r k))
                            (x (elt-at (color-above-witness
                                        (finite-bound (hom-set c r k)) k c r)
                                       c r)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Main theorems.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmz infinite-ramsey
  (implies (and (natp r) (funp c) (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) r))
           (exists-infinite-homogeneous c))
  :props (zfc prod2$prop domain$prop inverse$prop hom-set$prop)
  :hints (("Goal"
           :in-theory (disable some-infinite-color color-infinite)
           :use ((:instance pigeonhole-colors)
                 (:instance some-infinite-color)
                 (:instance exists-infinite-homogeneous-suff
                            (h (hom-set c r (some-infinite-color-witness c r)))
                            (k (some-infinite-color-witness c r)))
                 (:instance homogeneous-hom-set
                            (k (some-infinite-color-witness c r)))
                 (:instance hom-set-not-finite
                            (k (some-infinite-color-witness c r)))))))

(defthmz infinite-ramsey-2
  (implies (and (funp c) (equal (domain c) (prod2 (omega) (omega)))
                (subset (image c) 2))
           (exists-infinite-homogeneous c))
  :props (zfc prod2$prop domain$prop inverse$prop hom-set$prop)
  :hints (("Goal" :use ((:instance infinite-ramsey (r 2))))))
