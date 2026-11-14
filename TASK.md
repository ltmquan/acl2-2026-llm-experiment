Prove the theorems below in ACL2(r). `sa` is the sampling function sin(x)/x. `int-cos` and `int-cos-sq`
are definite integrals of cos and cos², and `vdc-integral` and `vrms-integral` are the average and RMS of
V·cos θ over the window [α − T/2, α + T/2].

1. Create /work/defs.lisp containing exactly the text between the tags.
defs.lisp holds the definitions the theorems use. Do not modify these files.

<defs.lisp>
(in-package "ACL2")

(include-book "nonstd/nsa/trig" :dir :system)
(include-book "nonstd/nsa/sqrt" :dir :system)
(include-book "nonstd/integrals/integrable-functions" :dir :system)
(include-book "nonstd/integrals/make-partition" :dir :system)

(defun sa (x) (if (equal x 0) 1 (/ (acl2-sine x) x)))

(defun map-cos (p) (if (consp p) (cons (acl2-cosine (car p)) (map-cos (cdr p))) nil))
(defun riemann-cos (p) (dotprod (deltas p) (map-cos (cdr p))))

(defun map-cos-sq (p)
  (if (consp p) (cons (expt (acl2-cosine (car p)) 2) (map-cos-sq (cdr p))) nil))
(defun riemann-cos-sq (p) (dotprod (deltas p) (map-cos-sq (cdr p))))
</defs.lisp>

2. Write /work/solution.lisp. It must (include-book "defs") and then prove every theorem in <theorems>, each
as a `defthm` with exactly the name and statement given. You may add your own definitions and lemmas, and any
`:rule-classes` and hints.

3. Admit these definitions in /work/solution.lisp, after including defs and before the theorems, with exactly
these names, formals and bodies. You may add declarations and hints to them, and your own events before them.

<definitions-to-admit>
(defun-std strict-int-cos (a b)
  (if (and (realp a) (realp b) (< a b))
      (standard-part (riemann-cos (make-small-partition a b)))
    0))

(defun int-cos (a b) (if (<= a b) (strict-int-cos a b) (- (strict-int-cos b a))))

(defun-std strict-int-cos-sq (a b)
  (if (and (realp a) (realp b) (< a b))
      (standard-part (riemann-cos-sq (make-small-partition a b)))
    0))

(defun int-cos-sq (a b) (if (<= a b) (strict-int-cos-sq a b) (- (strict-int-cos-sq b a))))

(defun vdc-integral (vm tt alpha)
  (* vm (/ tt) (int-cos (- alpha (/ tt 2)) (+ alpha (/ tt 2)))))

(defun vrms-integral (vm tt alpha)
  (acl2-sqrt (* (expt vm 2) (/ tt) (int-cos-sq (- alpha (/ tt 2)) (+ alpha (/ tt 2))))))
</definitions-to-admit>

<theorems>
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
</theorems>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
Books are certified with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
/work/solution.lisp must certify with `cert.pl --acl2 acl2r`.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done.
When you are done, run `submit fw-rectifier-master`, which saves /work. Then print a short summary: the files you
wrote, and for each theorem whether it is proved.
