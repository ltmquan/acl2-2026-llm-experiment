(include-book "nonstd/nsa/trig" :dir :system)
(include-book "nonstd/integrals/integrable-functions" :dir :system)
(include-book "nonstd/integrals/make-partition" :dir :system)

(defun sa (x) (if (equal x 0) 1 (/ (acl2-sine x) x)))

;; ---- 4a: exact-value layer (closed-form master equations, as given)
(defun vdc-closed (vm tt alpha) (* vm (sa (/ tt 2)) (acl2-cosine alpha)))
(defun vrms-ratio-closed (tt alpha)          ; V_RMS / V_mRMS
  (acl2-sqrt (+ 1 (* (sa tt) (acl2-cosine (* 2 alpha))))))

;; six-phase midpoint: q = 6, T = 2pi/6, Vm = Vmax
(skip-proofs
(defthm six-phase-midpoint-row
  (implies (and (realp vmax) (realp alpha))
           (and (equal (vdc-closed vmax (* 2/6 (acl2-pi)) alpha)
                       (* (/ 3 (acl2-pi)) vmax (acl2-cosine alpha)))
                (equal (vrms-ratio-closed (* 2/6 (acl2-pi)) alpha)
                       (acl2-sqrt (+ 1 (* (/ (* 3 (acl2-sqrt 3)) (* 2 (acl2-pi)))
                                          (acl2-cosine (* 2 alpha))))))))))
;; twelve-pulse (two series six-pulse bridges, 30 deg apart): T = pi/6,
;; Vm = 2 sqrt(3) cos(pi/12) Vmax
(skip-proofs
(defthm sine-pi/12
  (equal (acl2-sine (* 1/12 (acl2-pi)))
         (/ (- (acl2-sqrt 6) (acl2-sqrt 2)) 4))))
(skip-proofs
(defthm twelve-pulse-peak
  (equal (* 2 (acl2-sqrt 3) (acl2-cosine (* 1/12 (acl2-pi))))
         (/ (+ (* 3 (acl2-sqrt 2)) (acl2-sqrt 6)) 2))))
(skip-proofs
(defthm twelve-pulse-row
  (implies (and (realp vmax) (realp alpha))
           (and (equal (vdc-closed (* 2 (acl2-sqrt 3) (acl2-cosine (* 1/12 (acl2-pi))) vmax)
                                   (* 1/6 (acl2-pi)) alpha)
                       (* (/ (* 6 (acl2-sqrt 3)) (acl2-pi)) vmax (acl2-cosine alpha)))
                (equal (vrms-ratio-closed (* 1/6 (acl2-pi)) alpha)
                       (acl2-sqrt (+ 1 (* (/ 3 (acl2-pi)) (acl2-cosine (* 2 alpha))))))))))

;; waveform part of 4a: envelope of six cosines spaced pi/3 apart
(defun envelope6 (theta vpk k)
  (declare (xargs :measure (nfix (- 6 k))))
  (if (or (not (natp k)) (>= k 5))
      (* vpk (acl2-cosine (- theta (* 5/3 (acl2-pi)))))
    (max (* vpk (acl2-cosine (- theta (* k 1/3 (acl2-pi)))))
         (envelope6 theta vpk (1+ k)))))
(defun six-phase-midpoint-output (theta vmax) (envelope6 theta vmax 0))
(defun three-phase-bridge-output (theta vmax) (envelope6 theta (* (acl2-sqrt 3) vmax) 0))
(defun twelve-pulse-series-output (theta vmax)
  (+ (three-phase-bridge-output theta vmax)
     (three-phase-bridge-output (- theta (* 1/6 (acl2-pi))) vmax)))
(skip-proofs
(defthm six-phase-midpoint-output-pulse
  (implies (and (realp vmax) (<= 0 vmax) (realp theta)
                (<= (- (* 1/6 (acl2-pi))) theta) (<= theta (* 1/6 (acl2-pi))))
           (equal (six-phase-midpoint-output theta vmax)
                  (* vmax (acl2-cosine theta))))))
(skip-proofs
(defthm twelve-pulse-series-output-pulse
  (implies (and (realp vmax) (<= 0 vmax) (realp theta)
                (<= 0 theta) (<= theta (* 1/6 (acl2-pi))))
           (equal (twelve-pulse-series-output theta vmax)
                  (* 2 (acl2-sqrt 3) (acl2-cosine (* 1/12 (acl2-pi))) vmax
                     (acl2-cosine (- theta (* 1/12 (acl2-pi)))))))))

;; ---- 4b: integral-based master theorem
(defun map-cos (p) (if (consp p) (cons (acl2-cosine (car p)) (map-cos (cdr p))) nil))
(defun riemann-cos (p) (dotprod (deltas p) (map-cos (cdr p))))
(defun map-cos-sq (p) (if (consp p) (cons (expt (acl2-cosine (car p)) 2) (map-cos-sq (cdr p))) nil))
(defun riemann-cos-sq (p) (dotprod (deltas p) (map-cos-sq (cdr p))))
(skip-proofs
 (defun-std strict-int-cos (a b)
   (if (and (realp a) (realp b) (< a b))
       (standard-part (riemann-cos (make-small-partition a b)))
     0)))
(defun int-cos (a b) (if (<= a b) (strict-int-cos a b) (- (strict-int-cos b a))))
(skip-proofs
 (defun-std strict-int-cos-sq (a b)
   (if (and (realp a) (realp b) (< a b))
       (standard-part (riemann-cos-sq (make-small-partition a b)))
     0)))
(defun int-cos-sq (a b) (if (<= a b) (strict-int-cos-sq a b) (- (strict-int-cos-sq b a))))

;; average and RMS of the pulse train Vm*cos(theta) over the window [alpha-T/2, alpha+T/2]
(defun vdc-integral (vm tt alpha)
  (* vm (/ tt) (int-cos (- alpha (/ tt 2)) (+ alpha (/ tt 2)))))
(defun vrms-integral (vm tt alpha)
  (acl2-sqrt (* (expt vm 2) (/ tt) (int-cos-sq (- alpha (/ tt 2)) (+ alpha (/ tt 2))))))

(skip-proofs
(defthm master-theorem-vdc
  (implies (and (realp vm) (realp tt) (< 0 tt) (realp alpha))
           (equal (vdc-integral vm tt alpha)
                  (* vm (sa (/ tt 2)) (acl2-cosine alpha))))))
(skip-proofs
(defthm master-theorem-vrms
  (implies (and (realp vm) (<= 0 vm) (realp tt) (< 0 tt) (realp alpha))
           (equal (vrms-integral vm tt alpha)
                  (* (/ vm (acl2-sqrt 2))
                     (acl2-sqrt (+ 1 (* (sa tt) (acl2-cosine (* 2 alpha))))))))))
(cw "ALL-OK~%")
