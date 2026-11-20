(in-package "ACL2")

(include-book "defs")

(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (defthm pi-nonzero (not (equal (acl2-pi) 0))
  :hints (("Goal" :use pi-between-2-4 :in-theory (disable pi-between-2-4)))))

(local (defthm sqrt-3-nonneg (and (realp (acl2-sqrt 3)) (<= 0 (acl2-sqrt 3)))
  :hints (("Goal" :use ((:instance sqrt->-0 (x 3))) :in-theory (disable sqrt->-0)))))

(defthm six-phase-midpoint-row
  (implies (and (realp vmax) (realp alpha))
           (and (equal (vdc-closed vmax (* 2/6 (acl2-pi)) alpha)
                       (* (/ 3 (acl2-pi)) vmax (acl2-cosine alpha)))
                (equal (vrms-ratio-closed (* 2/6 (acl2-pi)) alpha)
                       (acl2-sqrt (+ 1 (* (/ (* 3 (acl2-sqrt 3)) (* 2 (acl2-pi)))
                                          (acl2-cosine (* 2 alpha)))))))))

(local (defthm sqrt-1/2
  (equal (acl2-sqrt 1/2) (/ (acl2-sqrt 2) 2))
  :hints (("Goal" :use ((:instance y-=-sqrt (x 1/2) (y (/ (acl2-sqrt 2) 2)))
                        (:instance sqrt-sqrt (x 2))
                        (:instance sqrt->-0 (x 2)))
           :in-theory (disable y-=-sqrt sqrt-sqrt sqrt->-0)))))

(local (defthm sqrt-3*sqrt-2
  (equal (* (acl2-sqrt 3) (acl2-sqrt 2)) (acl2-sqrt 6))
  :hints (("Goal" :use ((:instance sqrt-* (x 3) (y 2)))
           :in-theory (disable sqrt-*)))))

(local (defthm sqrt-2*sqrt-3
  (equal (* (acl2-sqrt 2) (acl2-sqrt 3)) (acl2-sqrt 6))
  :hints (("Goal" :use ((:instance sqrt-* (x 3) (y 2)))
           :in-theory (disable sqrt-*)))))

(local (defthm sqrt-3*sqrt-3
  (equal (* (acl2-sqrt 3) (acl2-sqrt 3)) 3)
  :hints (("Goal" :use ((:instance sqrt-sqrt (x 3))) :in-theory (disable sqrt-sqrt)))))

(local (defthm assoc-helper
  (implies (equal (* a a) 3)
           (equal (* a (* a b)) (* 3 b)))
  :rule-classes nil))

(local (defthm sqrt-3*sqrt-6
  (equal (* (acl2-sqrt 3) (acl2-sqrt 6)) (* 3 (acl2-sqrt 2)))
  :hints (("Goal" :use ((:instance assoc-helper (a (acl2-sqrt 3)) (b (acl2-sqrt 2))))
           :in-theory (union-theories '(sqrt-3*sqrt-2 sqrt-3*sqrt-3) (theory 'minimal-theory))))))

(local (defthm pi/12-split
  (equal (+ (* 1/3 x) (- (* 1/4 x))) (* 1/12 x))))

(defthm sine-pi/12
  (equal (acl2-sine (* 1/12 (acl2-pi))) (/ (- (acl2-sqrt 6) (acl2-sqrt 2)) 4))
  :hints (("Goal" :use (
                        (:instance sine-of-sums (x (* 1/3 (acl2-pi))) (y (- (* 1/4 (acl2-pi))))))
           :in-theory (disable sine-of-sums cosine-of-sums))))

(defthm cosine-pi/12
  (equal (acl2-cosine (* 1/12 (acl2-pi))) (/ (+ (acl2-sqrt 6) (acl2-sqrt 2)) 4))
  :hints (("Goal" :use (
                        (:instance cosine-of-sums (x (* 1/3 (acl2-pi))) (y (- (* 1/4 (acl2-pi))))))
           :in-theory (disable sine-of-sums cosine-of-sums))))

(defthm twelve-pulse-peak
  (equal (* 2 (acl2-sqrt 3) (acl2-cosine (* 1/12 (acl2-pi))))
         (/ (+ (* 3 (acl2-sqrt 2)) (acl2-sqrt 6)) 2)))

(local (defthm sin*cos-pi/12
  (equal (* (acl2-sine (* 1/12 (acl2-pi))) (acl2-cosine (* 1/12 (acl2-pi)))) 1/4)
  :hints (("Goal" :use ((:instance sine-2x (x (* 1/12 (acl2-pi)))))
           :in-theory (disable sine-2x sine-pi/12 cosine-pi/12)))))

(local (defthm sin*cos-pi/12-b
  (equal (* (acl2-sine (* 1/12 (acl2-pi))) (acl2-cosine (* 1/12 (acl2-pi))) x) (* 1/4 x))
  :hints (("Goal" :use sin*cos-pi/12
           :in-theory (disable sin*cos-pi/12 sine-pi/12 cosine-pi/12)))))

(local (defthm cos*sin-pi/12-b
  (equal (* (acl2-cosine (* 1/12 (acl2-pi))) (acl2-sine (* 1/12 (acl2-pi))) x) (* 1/4 x))
  :hints (("Goal" :use sin*cos-pi/12
           :in-theory (disable sin*cos-pi/12 sine-pi/12 cosine-pi/12)))))

(local (defthm cos*sin-pi/12
  (equal (* (acl2-cosine (* 1/12 (acl2-pi))) (acl2-sine (* 1/12 (acl2-pi)))) 1/4)
  :hints (("Goal" :use sin*cos-pi/12
           :in-theory (disable sin*cos-pi/12 sine-pi/12 cosine-pi/12)))))

(defthm twelve-pulse-row
  (implies (and (realp vmax) (realp alpha))
           (and (equal (vdc-closed (* 2 (acl2-sqrt 3) (acl2-cosine (* 1/12 (acl2-pi))) vmax)
                                   (* 1/6 (acl2-pi)) alpha)
                       (* (/ (* 6 (acl2-sqrt 3)) (acl2-pi)) vmax (acl2-cosine alpha)))
                (equal (vrms-ratio-closed (* 1/6 (acl2-pi)) alpha)
                       (acl2-sqrt (+ 1 (* (/ 3 (acl2-pi)) (acl2-cosine (* 2 alpha))))))))
  :hints (("Goal" :in-theory (disable sine-pi/12 cosine-pi/12 twelve-pulse-peak))))

;;; ---------------- constant angles ----------------

(local (defthm split-2/3 (equal (+ (* 1/2 x) (* 1/6 x)) (* 2/3 x))))
(local (defthm split-4/3 (equal (+ x (* 1/3 x)) (* 4/3 x))))
(local (defthm split-5/3 (equal (+ (* 2 x) (- (* 1/3 x))) (* 5/3 x))))

(local (defthm sine-2pi/3 (equal (acl2-sine (* 2/3 (acl2-pi))) (/ (acl2-sqrt 3) 2))
  :hints (("Goal" :use ((:instance sin-pi/2+x (x (* 1/6 (acl2-pi)))))
           :in-theory (disable sin-pi/2+x sine-of-sums cosine-of-sums)))))
(local (defthm cosine-2pi/3 (equal (acl2-cosine (* 2/3 (acl2-pi))) -1/2)
  :hints (("Goal" :use ((:instance cos-pi/2+x (x (* 1/6 (acl2-pi)))))
           :in-theory (disable cos-pi/2+x sine-of-sums cosine-of-sums)))))
(local (defthm sine-4pi/3 (equal (acl2-sine (* 4/3 (acl2-pi))) (- (/ (acl2-sqrt 3) 2)))
  :hints (("Goal" :use ((:instance sin-pi+x (x (* 1/3 (acl2-pi)))))
           :in-theory (disable sin-pi+x sine-of-sums cosine-of-sums)))))
(local (defthm cosine-4pi/3 (equal (acl2-cosine (* 4/3 (acl2-pi))) -1/2)
  :hints (("Goal" :use ((:instance cos-pi+x (x (* 1/3 (acl2-pi)))))
           :in-theory (disable cos-pi+x sine-of-sums cosine-of-sums)))))
(local (defthm sine-5pi/3 (equal (acl2-sine (* 5/3 (acl2-pi))) (- (/ (acl2-sqrt 3) 2)))
  :hints (("Goal" :use ((:instance sin-2pi-x (x (* 1/3 (acl2-pi)))))
           :in-theory (disable sin-2pi-x sine-of-sums cosine-of-sums)))))
(local (defthm cosine-5pi/3 (equal (acl2-cosine (* 5/3 (acl2-pi))) 1/2)
  :hints (("Goal" :use ((:instance cos-2pi-x (x (* 1/3 (acl2-pi)))))
           :in-theory (disable cos-2pi-x sine-of-sums cosine-of-sums)))))

;;; ---------------- sign facts ----------------

(local (defthm sin-nonneg
  (implies (and (realp x) (<= 0 x) (<= x (* 1/2 (acl2-pi))))
           (<= 0 (acl2-sine x)))
  :hints (("Goal" :cases ((equal x 0) (equal x (* 1/2 (acl2-pi))))
           :use sine-positive-in-0-pi/2
           :in-theory (disable sine-positive-in-0-pi/2)))))

(local (defthm cos-nonneg
  (implies (and (realp x) (<= (- (* 1/2 (acl2-pi))) x) (<= x (* 1/2 (acl2-pi))))
           (<= 0 (acl2-cosine x)))
  :hints (("Goal" :cases ((equal x 0) (< 0 x))
           :use (cosine-positive-in-0-pi/2
                 (:instance cosine-positive-in-0-pi/2 (x (- x))))
           :in-theory (disable cosine-positive-in-0-pi/2)))))

(local (defthm scale-le
  (implies (and (realp v) (<= 0 v) (realp a) (realp b) (<= a b))
           (<= (* v a) (* v b)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil))

;;; ---------------- bounds on the other five phases ----------------

(defmacro th-hyps ()
  '(and (realp theta)
        (<= (- (* 1/6 (acl2-pi))) theta) (<= theta (* 1/6 (acl2-pi)))))

(local (defthm bound-1
  (implies (th-hyps)
           (<= (acl2-cosine (+ theta (- (* 1/3 (acl2-pi))))) (acl2-cosine theta)))
  :hints (("Goal" :use ((:instance sin-nonneg (x (+ (* 1/6 (acl2-pi)) (- theta)))))
           :in-theory (disable sin-nonneg)))))

(local (defthm bound-2
  (implies (th-hyps)
           (<= (acl2-cosine (+ theta (- (* 2/3 (acl2-pi))))) (acl2-cosine theta)))
  :hints (("Goal" :use ((:instance sin-nonneg (x (+ (* 1/6 (acl2-pi)) (- theta))))
                        (:instance cos-nonneg (x theta)))
           :in-theory (disable sin-nonneg cos-nonneg)))))

(local (defthm bound-3
  (implies (th-hyps)
           (<= (acl2-cosine (+ theta (- (acl2-pi)))) (acl2-cosine theta)))
  :hints (("Goal" :use ((:instance cos-nonneg (x theta)))
           :in-theory (disable cos-nonneg)))))

(local (defthm bound-4
  (implies (th-hyps)
           (<= (acl2-cosine (+ theta (- (* 4/3 (acl2-pi))))) (acl2-cosine theta)))
  :hints (("Goal" :use ((:instance sin-nonneg (x (+ (* 1/6 (acl2-pi)) theta)))
                        (:instance cos-nonneg (x theta)))
           :in-theory (disable sin-nonneg cos-nonneg)))))

(local (defthm bound-5
  (implies (th-hyps)
           (<= (acl2-cosine (+ theta (- (* 5/3 (acl2-pi))))) (acl2-cosine theta)))
  :hints (("Goal" :use ((:instance sin-nonneg (x (+ (* 1/6 (acl2-pi)) theta))))
           :in-theory (disable sin-nonneg)))))

;;; ---------------- the envelope on the central pulse ----------------

(local (defthm envelope6-pulse
  (implies (and (th-hyps) (realp v) (<= 0 v))
           (equal (envelope6 theta v 0) (* v (acl2-cosine theta))))
  :hints (("Goal"
           :expand ((envelope6 theta v 0) (envelope6 theta v 1) (envelope6 theta v 2)
                    (envelope6 theta v 3) (envelope6 theta v 4) (envelope6 theta v 5))
           :use (bound-1 bound-2 bound-3 bound-4 bound-5
                 (:instance scale-le (a (acl2-cosine (+ theta (- (* 1/3 (acl2-pi))))))
                            (b (acl2-cosine theta)))
                 (:instance scale-le (a (acl2-cosine (+ theta (- (* 2/3 (acl2-pi))))))
                            (b (acl2-cosine theta)))
                 (:instance scale-le (a (acl2-cosine (+ theta (- (acl2-pi)))))
                            (b (acl2-cosine theta)))
                 (:instance scale-le (a (acl2-cosine (+ theta (- (* 4/3 (acl2-pi))))))
                            (b (acl2-cosine theta)))
                 (:instance scale-le (a (acl2-cosine (+ theta (- (* 5/3 (acl2-pi))))))
                            (b (acl2-cosine theta))))
           :in-theory (disable cosine-of-sums sine-of-sums cos-pi+x cos-pi-x
                               cos-2pi-x cos-2pi+x bound-1 bound-2 bound-3 bound-4 bound-5)))))

(defthm six-phase-midpoint-output-pulse
  (implies (and (realp vmax) (<= 0 vmax) (realp theta)
                (<= (- (* 1/6 (acl2-pi))) theta) (<= theta (* 1/6 (acl2-pi))))
           (equal (six-phase-midpoint-output theta vmax) (* vmax (acl2-cosine theta)))))

;;; ---------------- twelve-pulse ----------------

(local (defthm cos-sum-pair
  (equal (+ (acl2-cosine (+ u (* 1/12 (acl2-pi))))
            (acl2-cosine (+ u (- (* 1/12 (acl2-pi))))))
         (* 2 (acl2-cosine (* 1/12 (acl2-pi))) (acl2-cosine u)))
  :hints (("Goal" :in-theory (disable sine-pi/12 cosine-pi/12 twelve-pulse-peak)))
  :rule-classes nil))

(local (defthm twelve-helper-1
  (implies (acl2-numberp theta)
           (equal (+ (+ theta (- (* 1/12 (acl2-pi)))) (* 1/12 (acl2-pi))) theta))))

(local (defthm twelve-helper-2
  (equal (+ (+ theta (- (* 1/12 (acl2-pi)))) (- (* 1/12 (acl2-pi))))
         (+ theta (- (* 1/6 (acl2-pi)))))))

(local (defthm cos-pair-theta
  (implies (realp theta)
           (equal (+ (acl2-cosine theta) (acl2-cosine (+ theta (- (* 1/6 (acl2-pi))))))
                  (* 2 (acl2-cosine (* 1/12 (acl2-pi)))
                     (acl2-cosine (+ theta (- (* 1/12 (acl2-pi))))))))
  :hints (("Goal" :use ((:instance cos-sum-pair (u (+ theta (- (* 1/12 (acl2-pi)))))))
           :in-theory (union-theories '(twelve-helper-1 twelve-helper-2)
                                      (theory 'minimal-theory))))))

(local (defthm combine-0
  (implies (and (equal e1 (* s v a)) (equal e2 (* s v b)) (equal b (- (* 2 c d) a)))
           (equal (+ e1 e2) (* 2 s c v d)))
  :rule-classes nil))

(local (defthm combine-helper
  (implies (and (equal e1 (* s v a)) (equal e2 (* s v b)) (equal (+ a b) (* 2 c d))
                (acl2-numberp b))
           (equal (+ e1 e2) (* 2 s c v d)))
  :hints (("Goal" :use combine-0))
  :rule-classes nil))

(defthm twelve-pulse-series-output-pulse
  (implies (and (realp vmax) (<= 0 vmax) (realp theta)
                (<= 0 theta) (<= theta (* 1/6 (acl2-pi))))
           (equal (twelve-pulse-series-output theta vmax)
                  (* 2 (acl2-sqrt 3) (acl2-cosine (* 1/12 (acl2-pi))) vmax
                     (acl2-cosine (- theta (* 1/12 (acl2-pi)))))))
  :hints (("Goal" :use ((:instance envelope6-pulse (v (* (acl2-sqrt 3) vmax)))
                        (:instance envelope6-pulse (v (* (acl2-sqrt 3) vmax))
                                   (theta (- theta (* 1/6 (acl2-pi)))))
                        cos-pair-theta
                        (:instance combine-helper
                                   (e1 (envelope6 theta (* (acl2-sqrt 3) vmax) 0))
                                   (e2 (envelope6 (- theta (* 1/6 (acl2-pi))) (* (acl2-sqrt 3) vmax) 0))
                                   (s (acl2-sqrt 3)) (v vmax)
                                   (a (acl2-cosine theta))
                                   (b (acl2-cosine (- theta (* 1/6 (acl2-pi)))))
                                   (c (acl2-cosine (* 1/12 (acl2-pi))))
                                   (d (acl2-cosine (- theta (* 1/12 (acl2-pi)))))))
           :in-theory (disable envelope6 envelope6-pulse cos-pair-theta cosine-of-sums
                               sine-of-sums sine-pi/12 cosine-pi/12 twelve-pulse-peak))))
