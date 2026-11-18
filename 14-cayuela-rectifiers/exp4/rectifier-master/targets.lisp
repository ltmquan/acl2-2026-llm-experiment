(defthm master-theorem-vdc
  (implies (and (realp vm) (realp tt) (< 0 tt) (realp alpha))
           (equal (vdc-integral vm tt alpha) (* vm (sa (/ tt 2)) (acl2-cosine alpha)))))

(defthm master-theorem-vrms
  (implies (and (realp vm) (<= 0 vm) (realp tt) (< 0 tt) (realp alpha))
           (equal (vrms-integral vm tt alpha)
                  (* (/ vm (acl2-sqrt 2))
                     (acl2-sqrt (+ 1 (* (sa tt) (acl2-cosine (* 2 alpha)))))))))

(defthm three-phase-midpoint-row
  (implies (and (realp vmax) (<= 0 vmax) (realp alpha))
           (and (equal (vdc-integral vmax (* 2/3 (acl2-pi)) alpha)
                       (* (/ (* 3 (acl2-sqrt 3)) (* 2 (acl2-pi))) vmax (acl2-cosine alpha)))
                (equal (vrms-integral vmax (* 2/3 (acl2-pi)) alpha)
                       (* (/ vmax (acl2-sqrt 2))
                          (acl2-sqrt (+ 1 (* (/ (* 3 (acl2-sqrt 3)) (* 4 (acl2-pi)))
                                             (acl2-cosine (* 2 alpha))))))))))

(defthm three-phase-bridge-row
  (implies (and (realp vmax) (<= 0 vmax) (realp alpha))
           (and (equal (vdc-integral (* (acl2-sqrt 3) vmax) (* 1/3 (acl2-pi)) alpha)
                       (* (/ (* 3 (acl2-sqrt 3)) (acl2-pi)) vmax (acl2-cosine alpha)))
                (equal (vrms-integral (* (acl2-sqrt 3) vmax) (* 1/3 (acl2-pi)) alpha)
                       (* (/ (* (acl2-sqrt 3) vmax) (acl2-sqrt 2))
                          (acl2-sqrt (+ 1 (* (/ (* 3 (acl2-sqrt 3)) (* 2 (acl2-pi)))
                                             (acl2-cosine (* 2 alpha))))))))))
