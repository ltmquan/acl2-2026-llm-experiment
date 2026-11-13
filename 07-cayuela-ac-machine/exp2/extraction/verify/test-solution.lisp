; Test solution with real proofs (hints ported from the authors' books),
; used only to check target matching with check-exp2.py.
; cert_param: (uses-acl2r)
(in-package "ACL2")
(include-book "defs")

(local (defthm collapse-s3
  (implies (and (real/rationalp ra) (real/rationalp ia) (real/rationalp s3)
                (equal (* s3 s3) 3))
           (equal (cadd (cscale (* 2/3 (dotp (cplx ra ia) (e0))) (e0))
                  (cadd (cscale (* 2/3 (dotp (cplx ra ia) (e1 s3))) (e1 s3))
                        (cscale (* 2/3 (dotp (cplx ra ia) (e2 s3))) (e2 s3))))
                  (cplx ra ia)))
  :hints (("Goal" :nonlinearp t))))

(local (defthm sqrt-3-squared-nv
  (equal (* (acl2-sqrt 3) (acl2-sqrt 3)) 3)
  :hints (("Goal" :use (:instance sqrt-=-y (x 3) (y (acl2-sqrt 3)))))))

(defthm MAIN-1
  (implies (and (realp ra) (realp ia))
           (equal (cadd (cscale (* 2/3 (dotp (cplx ra ia) (e0))) (e0))
                  (cadd (cscale (* 2/3 (dotp (cplx ra ia) (e1 (acl2-sqrt 3))))
                                (e1 (acl2-sqrt 3)))
                        (cscale (* 2/3 (dotp (cplx ra ia) (e2 (acl2-sqrt 3))))
                                (e2 (acl2-sqrt 3)))))
                  (cplx ra ia)))
  :hints (("Goal" :use ((:instance collapse-s3 (s3 (acl2-sqrt 3)))
                        sqrt-3-squared-nv)
                  :in-theory (disable collapse-s3))))

(defthm MAIN-2
  (equal (imz (torque-W i-s i-r eps))
         (crossp i-s (cmul i-r (eiz eps)))))

(local (defthm real-square->=-0
  (implies (realp a) (>= (* a a) 0))
  :rule-classes :linear
  :hints (("Goal" :cases ((<= a 0)))
          ("Subgoal 2" :nonlinearp t)
          ("Subgoal 1" :nonlinearp t))))

(local (defthm quadratic-always-positive
  (implies (realp x) (> (+ (* x x) x 1) 0))
  :hints (("Goal" :use ((:instance real-square->=-0 (a (+ x 1/2))))
                  :nonlinearp t))))

(local (defthm expt-b-3-reduction
  (implies (and (realp b) (equal (expt b 2) 3/4))
           (equal (expt b 3) (* b 3/4)))
  :hints (("Goal" :nonlinearp t))))

(local (defthm expt-b-4-reduction
  (implies (and (realp b) (equal (expt b 2) 3/4))
           (equal (expt b 4) 9/16))
  :hints (("Goal" :nonlinearp t))))

(defthm MAIN-3
  (implies (and (g-realpairp A) (g-realpairp omega)
                (equal (g-c+ (g-cplx 1 0) (g-c+ omega (g-c* omega omega)))
                       (g-cplx 0 0)))
           (equal (g-collapse-sum A omega) A))
  :hints (("Goal"
           :use ((:instance quadratic-always-positive (x (car omega)))))
          ("Subgoal 2" :nonlinearp t)
          ("Subgoal 1" :nonlinearp t)))

(local (defthm sqrt-3-squared
  (equal (* (acl2-sqrt 3) (acl2-sqrt 3)) 3)))

(local (defthm expt-2-is-times
  (implies (acl2-numberp x) (equal (expt x 2) (* x x)))))
(local (in-theory (disable expt-2-is-times)))

(local (defthm sqrt-3-squared-expt
  (equal (expt (acl2-sqrt 3) 2) 3)
  :hints (("Goal" :use ((:instance expt-2-is-times (x (acl2-sqrt 3)))
                        sqrt-3-squared)))))

(local (defthm gamma-split
  (equal (g-gamma-val) (+ (* 1/3 (acl2-pi)) (* 1/3 (acl2-pi))))))
(local (in-theory (disable g-gamma-val)))

(local (defthm cos-gamma-val
  (equal (acl2-cosine (g-gamma-val)) -1/2)
  :hints (("Goal" :in-theory (enable g-gamma-val)
           :use ((:instance cosine-of-sums (x (* 1/3 (acl2-pi))) (y (* 1/3 (acl2-pi))))
                 cosine-pi/3 sine-pi/3 sqrt-3-squared-expt)))))

(local (defthm sin-gamma-val
  (equal (acl2-sine (g-gamma-val)) (/ (acl2-sqrt 3) 2))
  :hints (("Goal" :in-theory (enable g-gamma-val)
           :use ((:instance sine-of-sums (x (* 1/3 (acl2-pi))) (y (* 1/3 (acl2-pi))))
                 cosine-pi/3 sine-pi/3)))))

(local (defthm omega-real-closed-form
  (equal (g-omega-real) (g-cplx -1/2 (/ (acl2-sqrt 3) 2)))
  :hints (("Goal" :in-theory (enable g-omega-real)
           :use (cos-gamma-val sin-gamma-val)))))

(local (defthm omega-real-satisfies-cubic
  (equal (g-c+ (g-cplx 1 0) (g-c+ (g-omega-real) (g-c* (g-omega-real) (g-omega-real))))
         (g-cplx 0 0))
  :hints (("Goal" :in-theory (enable g-c+ g-c* g-cplx)
           :use (omega-real-closed-form sqrt-3-squared-expt)))))

(local (defthm realpairp-omega-real
  (g-realpairp (g-omega-real))
  :hints (("Goal" :in-theory (enable g-omega-real)))))

(defthm MAIN-4
  (implies (g-realpairp A)
           (equal (g-collapse-sum A (g-omega-real)) A))
  :hints (("Goal" :use ((:instance MAIN-3 (omega (g-omega-real)))
                        omega-real-satisfies-cubic
                        realpairp-omega-real)
                  :in-theory (disable MAIN-3))))
