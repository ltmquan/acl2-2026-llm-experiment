(defthm six-phase-midpoint-row
  (implies (and (realp vmax) (realp alpha))
           (and (equal (vdc-closed vmax (* 2/6 (acl2-pi)) alpha)
                       (* (/ 3 (acl2-pi)) vmax (acl2-cosine alpha)))
                (equal (vrms-ratio-closed (* 2/6 (acl2-pi)) alpha)
                       (acl2-sqrt (+ 1 (* (/ (* 3 (acl2-sqrt 3)) (* 2 (acl2-pi)))
                                          (acl2-cosine (* 2 alpha)))))))))

(defthm sine-pi/12
  (equal (acl2-sine (* 1/12 (acl2-pi))) (/ (- (acl2-sqrt 6) (acl2-sqrt 2)) 4)))

(defthm twelve-pulse-peak
  (equal (* 2 (acl2-sqrt 3) (acl2-cosine (* 1/12 (acl2-pi))))
         (/ (+ (* 3 (acl2-sqrt 2)) (acl2-sqrt 6)) 2)))

(defthm twelve-pulse-row
  (implies (and (realp vmax) (realp alpha))
           (and (equal (vdc-closed (* 2 (acl2-sqrt 3) (acl2-cosine (* 1/12 (acl2-pi))) vmax)
                                   (* 1/6 (acl2-pi)) alpha)
                       (* (/ (* 6 (acl2-sqrt 3)) (acl2-pi)) vmax (acl2-cosine alpha)))
                (equal (vrms-ratio-closed (* 1/6 (acl2-pi)) alpha)
                       (acl2-sqrt (+ 1 (* (/ 3 (acl2-pi)) (acl2-cosine (* 2 alpha)))))))))

(defthm six-phase-midpoint-output-pulse
  (implies (and (realp vmax) (<= 0 vmax) (realp theta)
                (<= (- (* 1/6 (acl2-pi))) theta) (<= theta (* 1/6 (acl2-pi))))
           (equal (six-phase-midpoint-output theta vmax) (* vmax (acl2-cosine theta)))))

(defthm twelve-pulse-series-output-pulse
  (implies (and (realp vmax) (<= 0 vmax) (realp theta)
                (<= 0 theta) (<= theta (* 1/6 (acl2-pi))))
           (equal (twelve-pulse-series-output theta vmax)
                  (* 2 (acl2-sqrt 3) (acl2-cosine (* 1/12 (acl2-pi))) vmax
                     (acl2-cosine (- theta (* 1/12 (acl2-pi))))))))
