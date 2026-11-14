Prove the theorems below in ACL2(r). `sa` is the sampling function sin(x)/x. `envelope6` is the maximum of
six cosines 60° apart, and the `-output` functions are rectifier output waveforms built from it.

1. Create /work/defs.lisp containing exactly the text between the tags.
defs.lisp holds the definitions the theorems use. Do not modify these files.

<defs.lisp>
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
</defs.lisp>

2. Write /work/solution.lisp. It must (include-book "defs") and then prove every theorem in <theorems>, each
as a `defthm` with exactly the name and statement given. You may add your own definitions and lemmas, and any
`:rule-classes` and hints.

<theorems>
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
</theorems>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
Books are certified with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
/work/solution.lisp must certify with `cert.pl --acl2 acl2r`.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done.
When you are done, run `submit fw-rectifier-rows`, which saves /work. Then print a short summary: the files you
wrote, and for each theorem whether it is proved.
