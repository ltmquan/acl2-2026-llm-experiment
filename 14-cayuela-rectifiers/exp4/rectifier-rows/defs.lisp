(in-package "ACL2")

(include-book "nonstd/nsa/trig" :dir :system)
(include-book "nonstd/nsa/sqrt" :dir :system)

(defun sa (x) (if (equal x 0) 1 (/ (acl2-sine x) x)))

(defun vdc-closed (vm tt alpha) (* vm (sa (/ tt 2)) (acl2-cosine alpha)))

(defun vrms-ratio-closed (tt alpha)
  (acl2-sqrt (+ 1 (* (sa tt) (acl2-cosine (* 2 alpha))))))

(defun envelope6 (theta vpk k)
  (declare (xargs :measure (nfix (- 6 k))))
  (if (or (not (natp k)) (>= k 5))
      (* vpk (acl2-cosine (- theta (* 5/3 (acl2-pi)))))
    (max (* vpk (acl2-cosine (- theta (* k 1/3 (acl2-pi)))))
         (envelope6 theta vpk (1+ k)))))

(defun six-phase-midpoint-output (theta vmax) (envelope6 theta vmax 0))

(defun three-phase-bridge-output (theta vmax)
  (envelope6 theta (* (acl2-sqrt 3) vmax) 0))

(defun twelve-pulse-series-output (theta vmax)
  (+ (three-phase-bridge-output theta vmax)
     (three-phase-bridge-output (- theta (* 1/6 (acl2-pi))) vmax)))
