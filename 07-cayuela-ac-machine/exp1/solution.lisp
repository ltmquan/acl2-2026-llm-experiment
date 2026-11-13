(in-package "ACL2")

(include-book "nonstd/nsa/complex-polar" :dir :system)
(local (include-book "arithmetic/realp" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; Planar vector (a,b) <-> complex number a + jb.
;; Planar dot product.
(defun dot (x y)
  (+ (* (realpart x) (realpart y))
     (* (imagpart x) (imagpart y))))

;; e^{j theta}
(defun e^j (theta)
  (acl2-exp (* #c(0 1) theta)))

;; gamma = 2 pi / 3
(defun gam ()
  (* 2/3 (acl2-pi)))

;; Summand (2/3) (A . e^{jn gamma}) e^{jn gamma}
(defun term (a n)
  (* 2/3 (dot a (e^j (* n (gam)))) (e^j (* n (gam)))))

;; Sum_{n=0}^{k} term(a,n)
(defun sum-terms (a k)
  (if (zp k)
      (term a 0)
    (+ (term a k) (sum-terms a (1- k)))))

;;; ---------------- lemmas ----------------

(local (in-theory (disable acl2-sine acl2-cosine acl2-exp (gam))))

(local
 (defthm real-cs
   (and (realp (acl2-cosine (gam)))
        (realp (acl2-sine (gam))))
   :hints (("Goal" :in-theory (disable gam)))))

(local
 (defthm cos-2pi
   (equal (acl2-cosine (* 2 (acl2-pi))) 1)
   :hints (("Goal" :use ((:instance cosine-of-sums (x (acl2-pi)) (y (acl2-pi))))
            :in-theory (disable cosine-of-sums)))))

(local
 (defthm three-gam
   (equal (+ (gam) (+ (gam) (gam))) (* 2 (acl2-pi)))))

(local
 (defthm cos-3gam
   (equal (acl2-cosine (+ (gam) (+ (gam) (gam)))) 1)
   :hints (("Goal" :in-theory (disable gam cosine-of-sums sine-of-sums)))))

(local
 (defthm cubic-alg
   (implies (and (realp c) (realp s) (equal (* s s) (- 1 (* c c))))
            (equal (- (* c (- (* c c) (* s s)))
                      (* s (+ (* s c) (* c s))))
                   (+ (* 4 c c c) (* -3 c))))
   :rule-classes nil))

(local
 (defthm sin-sq-gam
   (equal (* (acl2-sine (gam)) (acl2-sine (gam)))
          (- 1 (* (acl2-cosine (gam)) (acl2-cosine (gam)))))
   :hints (("Goal" :use ((:instance sin**2+cos**2 (x (gam))))
            :in-theory (disable sin**2+cos**2)))
   :rule-classes nil))

(local
 (defthm cubic
   (equal (+ (* 4 (acl2-cosine (gam)) (acl2-cosine (gam)) (acl2-cosine (gam)))
             (* -3 (acl2-cosine (gam))))
          1)
   :hints (("Goal" :use (cos-3gam
                         sin-sq-gam
                         (:instance cubic-alg (c (acl2-cosine (gam))) (s (acl2-sine (gam)))))
            :in-theory (e/d (cosine-of-sums sine-of-sums)
                            (sin**2+cos**2 cos-3gam three-gam))))))

(local
 (defthm cos-neg
   (< (acl2-cosine (gam)) 0)
   :hints (("Goal" :use ((:instance cosine-negative-in-pi/2-pi (x (gam))))
            :in-theory (disable cosine-negative-in-pi/2-pi)))))

(local
 (defthm factor-id
   (implies (realp c)
            (equal (+ (* 4 c c c) (* -3 c) -1)
                   (* (- c 1) (* (+ (* 2 c) 1) (+ (* 2 c) 1)))))
   :rule-classes nil))

(local
 (defthm zero-prod
   (implies (and (acl2-numberp x) (acl2-numberp y))
            (equal (equal (* x y) 0)
                   (or (equal x 0) (equal y 0))))))

(local
 (defthm cubic-root
   (implies (and (realp c) (< c 0) (equal (+ (* 4 c c c) (* -3 c)) 1))
            (equal c -1/2))
   :hints (("Goal" :use (factor-id
                         (:instance zero-prod (x (- c 1))
                                    (y (* (+ (* 2 c) 1) (+ (* 2 c) 1))))
                         (:instance zero-prod (x (+ (* 2 c) 1))
                                    (y (+ (* 2 c) 1))))
            :in-theory (disable zero-prod)))
   :rule-classes nil))

(local
 (defthm cos-gam
   (equal (acl2-cosine (gam)) -1/2)
   :hints (("Goal" :use ((:instance cubic-root (c (acl2-cosine (gam)))) cubic)
            :in-theory (disable gam cubic)))))

(local
 (defthm sin-gam-sq
   (equal (* (acl2-sine (gam)) (acl2-sine (gam))) 3/4)
   :hints (("Goal" :use ((:instance sin**2+cos**2 (x (gam))))
            :in-theory (disable gam sin**2+cos**2)))))

(local
 (defthm complex-parts
   (implies (and (realp x) (realp y))
            (and (equal (realpart (+ x (* #c(0 1) y))) x)
                 (equal (imagpart (+ x (* #c(0 1) y))) y)))
   :hints (("Goal" :use ((:instance complex-definition))
            :in-theory (disable complex-definition realpart-+ imagpart-+)))))

(local
 (defthm e^j-cs
   (equal (e^j x) (+ (acl2-cosine x) (* #c(0 1) (acl2-sine x))))
   :rule-classes nil))

(local
 (defthm e^j-0 (equal (e^j 0) 1)))

(local
 (defthm e^j-1
   (equal (e^j (gam))
          (complex -1/2 (acl2-sine (gam))))
   :hints (("Goal" :use ((:instance e^j-cs (x (gam)))
                         (:instance complex-definition (x -1/2) (y (acl2-sine (gam)))))
            :in-theory (disable gam e^j complex-definition)))))

(local
 (defthm two-gam (equal (* 2 (gam)) (+ (gam) (gam)))))

(local
 (defthm neg-halves
   (implies (acl2-numberp x)
            (equal (+ (- (* 1/2 x)) (- (* 1/2 x))) (- x)))))

(local
 (defthm e^j-2
   (equal (e^j (* 2 (gam)))
          (complex -1/2 (- (acl2-sine (gam)))))
   :hints (("Goal" :use ((:instance e^j-cs (x (+ (gam) (gam))))
                         (:instance cosine-of-sums (x (gam)) (y (gam)))
                         (:instance sine-of-sums (x (gam)) (y (gam)))
                         (:instance complex-definition (x -1/2) (y (- (acl2-sine (gam))))))
            :in-theory (disable e^j gam cosine-of-sums sine-of-sums complex-definition)))))

(local (in-theory (disable e^j gam two-gam)))

(local
 (defthm scale-complex
   (implies (and (realp r) (realp x) (realp y))
            (equal (* r (complex x y)) (complex (* r x) (* r y))))
   :hints (("Goal" :use ((:instance complex-definition)
                         (:instance complex-definition (x (* r x)) (y (* r y))))
            :in-theory (disable complex-definition)))
   :rule-classes nil))

(local
 (defthm scale-parts
   (implies (realp r)
            (and (equal (realpart (* r z)) (* r (realpart z)))
                 (equal (imagpart (* r z)) (* r (imagpart z)))))
   :hints (("Goal" :cases ((acl2-numberp z)))
           ("Subgoal 1" :use ((:instance scale-complex (x (realpart z)) (y (imagpart z))))))))

(local
 (defthm scale-parts-right
   (implies (realp r)
            (and (equal (realpart (* z r)) (* r (realpart z)))
                 (equal (imagpart (* z r)) (* r (imagpart z)))))
   :hints (("Goal" :use scale-parts :in-theory (disable scale-parts)))))

(local
 (defthm parts-equal
   (implies (and (acl2-numberp x) (acl2-numberp y)
                 (equal (realpart x) (realpart y))
                 (equal (imagpart x) (imagpart y)))
            (equal x y))
   :hints (("Goal" :use ((:instance realpart-imagpart-elim (x x))
                         (:instance realpart-imagpart-elim (x y)))))
   :rule-classes nil))

(local
 (defthm real-dot (realp (dot x y))))

(local
 (defthm sin-gam-sq-x
   (equal (* (acl2-sine (gam)) (* (acl2-sine (gam)) x)) (* 3/4 x))
   :hints (("Goal" :use ((:instance associativity-of-* (x (acl2-sine (gam)))
                                    (y (acl2-sine (gam))) (z x)))
            :in-theory (disable associativity-of-*)))))

(local
 (defthm term-parts
   (and (equal (realpart (term a n))
               (* 2/3 (dot a (e^j (* n (gam)))) (realpart (e^j (* n (gam))))))
        (equal (imagpart (term a n))
               (* 2/3 (dot a (e^j (* n (gam)))) (imagpart (e^j (* n (gam)))))))
   :hints (("Goal" :in-theory (disable dot)
            :use ((:instance scale-parts (r (* 2/3 (dot a (e^j (* n (gam))))))
                             (z (e^j (* n (gam))))))))))

(local
 (defthm sum-terms-2
   (equal (sum-terms a 2) (+ (term a 2) (+ (term a 1) (term a 0))))))

(local (in-theory (disable term sum-terms)))

(local
 (defthm sum-parts
   (and (equal (realpart (sum-terms a 2)) (realpart a))
        (equal (imagpart (sum-terms a 2)) (imagpart a)))
   :hints (("Goal" :in-theory (enable dot)))))

(defthm main
  (implies (acl2-numberp a)
           (equal (sum-terms a 2) a))
  :hints (("Goal" :use ((:instance parts-equal (x (sum-terms a 2)) (y a)))
           :in-theory (disable sum-terms))))
