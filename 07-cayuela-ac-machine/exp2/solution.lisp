(in-package "ACL2")
(include-book "defs")

;; ---------- MAIN-1 ----------
(defthm sqrt3-sq
  (equal (* (acl2-sqrt 3) (acl2-sqrt 3)) 3)
  :hints (("Goal" :use ((:instance sqrt-sqrt (x 3))))))

(defthm expt-2-to-times
  (implies (acl2-numberp x) (equal (expt x 2) (* x x)))
  :rule-classes nil
  :hints (("Goal" :expand ((expt x 2) (expt x 1) (expt x 0))
           :in-theory (union-theories '((:e zip) (:e binary-+) (:e <) fix
                                        unicity-of-1 commutativity-of-*)
                                      (theory 'minimal-theory)))))

(defthm sqrt3-expt
  (equal (expt (acl2-sqrt 3) 2) 3)
  :hints (("Goal" :use (sqrt3-sq (:instance expt-2-to-times (x (acl2-sqrt 3))))
           :in-theory (union-theories '((:type-prescription acl2-sqrt))
                                      (theory 'minimal-theory)))))

(defthm sqrt3-num (acl2-numberp (acl2-sqrt 3)))

(defthm MAIN-1
  (implies (and (realp ra) (realp ia))
           (equal (cadd (cscale (* 2/3 (dotp (cplx ra ia) (e0))) (e0))
                  (cadd (cscale (* 2/3 (dotp (cplx ra ia) (e1 (acl2-sqrt 3))))
                                (e1 (acl2-sqrt 3)))
                        (cscale (* 2/3 (dotp (cplx ra ia) (e2 (acl2-sqrt 3))))
                                (e2 (acl2-sqrt 3)))))
                  (cplx ra ia))))

;; ---------- MAIN-2 ----------
(defthm MAIN-2
  (equal (imz (torque-W i-s i-r eps))
         (crossp i-s (cmul i-r (eiz eps)))))

;; ---------- MAIN-3 ----------
(defthm sq-nonneg
  (implies (realp y) (<= 0 (* y y)))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t :cases ((< y 0) (<= 0 y)))))

(defthm no-real-root
  (implies (realp c) (not (equal (+ 1 c (* c c)) 0)))
  :hints (("Goal" :use ((:instance sq-nonneg (y (+ c 1/2)))))))

(defthm c-from-hyp
  (implies (and (realp c) (realp s)
                (equal (+ 1 c (- (* c c) (* s s))) 0)
                (equal (+ s (* 2 c s)) 0))
           (and (equal c -1/2) (equal (* s s) 3/4)))
  :rule-classes nil
  :hints (("Goal" :cases ((equal s 0))
           :use ((:instance no-real-root)))))

(defthm collapse-poly
  (implies (and (acl2-numberp a) (acl2-numberp b) (acl2-numberp s)
                (equal (* s s) 3/4))
           (equal (g-collapse-sum (cons a b) (cons -1/2 s))
                  (cons a b)))
  :hints (("Goal" :in-theory (enable g-omega-pow))))

(defthm MAIN-3
  (implies (and (g-realpairp A) (g-realpairp omega)
                (equal (g-c+ (g-cplx 1 0) (g-c+ omega (g-c* omega omega)))
                       (g-cplx 0 0)))
           (equal (g-collapse-sum A omega) A))
  :hints (("Goal"
           :in-theory (disable g-collapse-sum collapse-poly)
           :use ((:instance c-from-hyp (c (car omega)) (s (cdr omega)))
                 (:instance collapse-poly (a (car A)) (b (cdr A))
                            (s (cdr omega)))))))

;; ---------- MAIN-4 ----------
(defthm two-thirds-pi
  (equal (* 2/3 (acl2-pi)) (+ (acl2-pi) (- (* 1/3 (acl2-pi)))))
  :rule-classes nil)

(defthm cos-2pi/3
  (equal (acl2-cosine (* 2/3 (acl2-pi))) -1/2)
  :hints (("Goal" :use (two-thirds-pi
                        (:instance cos-pi-x (x (* 1/3 (acl2-pi)))))
           :in-theory (union-theories '(cosine-pi/3 (:e unary--))
                                      (theory 'minimal-theory)))))

(defthm sin-2pi/3
  (equal (acl2-sine (* 2/3 (acl2-pi))) (/ (acl2-sqrt 3) 2))
  :hints (("Goal" :use (two-thirds-pi
                        (:instance sin-pi-x (x (* 1/3 (acl2-pi)))))
           :in-theory (union-theories '(sine-pi/3)
                                      (theory 'minimal-theory)))))

(defthm MAIN-4
  (implies (g-realpairp A)
           (equal (g-collapse-sum A (g-omega-real)) A))
  :hints (("Goal" :in-theory (disable g-collapse-sum collapse-poly)
           :use ((:instance collapse-poly (a (car A)) (b (cdr A))
                            (s (/ (acl2-sqrt 3) 2)))))))
