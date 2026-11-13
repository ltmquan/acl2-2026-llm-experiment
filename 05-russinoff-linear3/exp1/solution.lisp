(in-package "ACL2")

;;; ===================================================================
;;; The field F
;;; ===================================================================

(encapsulate
  (((fp *) => *)
   ((f0) => *)
   ((f1) => *)
   ((fadd * *) => *)
   ((fmul * *) => *)
   ((fneg *) => *)
   ((finv *) => *))

  (local (defun fp (x) (rationalp x)))
  (local (defun f0 () 0))
  (local (defun f1 () 1))
  (local (defun fadd (x y) (+ x y)))
  (local (defun fmul (x y) (* x y)))
  (local (defun fneg (x) (- x)))
  (local (defun finv (x) (/ x)))

  (defthm fp-booleanp (booleanp (fp x)) :rule-classes :type-prescription)
  (defthm fp-f0 (fp (f0)))
  (defthm fp-f1 (fp (f1)))
  (defthm fp-fadd (implies (and (fp x) (fp y)) (fp (fadd x y))))
  (defthm fp-fmul (implies (and (fp x) (fp y)) (fp (fmul x y))))
  (defthm fp-fneg (implies (fp x) (fp (fneg x))))
  (defthm fp-finv (implies (and (fp x) (not (equal x (f0)))) (fp (finv x))))

  (defthm fadd-comm
    (implies (and (fp x) (fp y)) (equal (fadd x y) (fadd y x))))
  (defthm fadd-assoc
    (implies (and (fp x) (fp y) (fp z))
             (equal (fadd (fadd x y) z) (fadd x (fadd y z)))))
  (defthm fadd-f0 (implies (fp x) (equal (fadd (f0) x) x)))
  (defthm fadd-fneg (implies (fp x) (equal (fadd x (fneg x)) (f0))))

  (defthm fmul-comm
    (implies (and (fp x) (fp y)) (equal (fmul x y) (fmul y x))))
  (defthm fmul-assoc
    (implies (and (fp x) (fp y) (fp z))
             (equal (fmul (fmul x y) z) (fmul x (fmul y z)))))
  (defthm fmul-f1 (implies (fp x) (equal (fmul (f1) x) x)))
  (defthm fmul-finv
    (implies (and (fp x) (not (equal x (f0))))
             (equal (fmul x (finv x)) (f1))))

  (defthm fmul-fadd-distrib
    (implies (and (fp x) (fp y) (fp z))
             (equal (fmul x (fadd y z)) (fadd (fmul x y) (fmul x z)))))

  (defthm f0-not-f1 (not (equal (f0) (f1)))))

;;; Total ("fixed") versions of the field operations, used for F^n.

(defun ffix (x) (if (fp x) x (f0)))
(defun f+ (x y) (fadd (ffix x) (ffix y)))
(defun f* (x y) (fmul (ffix x) (ffix y)))
(defun f- (x) (fneg (ffix x)))

(defthm fp-ffix (fp (ffix x)))
(defthm ffix-when-fp (implies (fp x) (equal (ffix x) x)))
(in-theory (disable ffix))
(defthm fp-f+ (fp (f+ x y)))
(defthm fp-f* (fp (f* x y)))
(defthm fp-f- (fp (f- x)))

(defthm f+-ffix-1 (equal (f+ (ffix x) y) (f+ x y)))
(defthm f+-ffix-2 (equal (f+ x (ffix y)) (f+ x y)))
(defthm f*-ffix-1 (equal (f* (ffix x) y) (f* x y)))
(defthm f*-ffix-2 (equal (f* x (ffix y)) (f* x y)))
(defthm f--ffix (equal (f- (ffix x)) (f- x)))

(defthm f+-comm (equal (f+ x y) (f+ y x)))
(defthm f+-assoc (equal (f+ (f+ x y) z) (f+ x (f+ y z))))
(defthm f+-comm-2 (equal (f+ x (f+ y z)) (f+ y (f+ x z)))
  :hints (("Goal" :in-theory (disable f+ f+-assoc)
           :use ((:instance f+-assoc (x x) (y y) (z z))
                 (:instance f+-assoc (x y) (y x) (z z))
                 (:instance f+-comm (x x) (y y))))))
(defthm f+-f0-1 (equal (f+ (f0) x) (ffix x)))
(defthm f+-f0-2 (equal (f+ x (f0)) (ffix x))
  :hints (("Goal" :in-theory (disable f+ f+-f0-1)
           :use ((:instance f+-comm (x x) (y (f0))) f+-f0-1))))
(defthm f+-f- (equal (f+ x (f- x)) (f0)))

(defthm f*-comm (equal (f* x y) (f* y x)))
(defthm f*-assoc (equal (f* (f* x y) z) (f* x (f* y z))))
(defthm f*-comm-2 (equal (f* x (f* y z)) (f* y (f* x z)))
  :hints (("Goal" :in-theory (disable f* f*-assoc)
           :use ((:instance f*-assoc (x x) (y y) (z z))
                 (:instance f*-assoc (x y) (y x) (z z))
                 (:instance f*-comm (x x) (y y))))))
(defthm f*-f1-1 (equal (f* (f1) x) (ffix x)))
(defthm f*-f1-2 (equal (f* x (f1)) (ffix x))
  :hints (("Goal" :in-theory (disable f* f*-f1-1)
           :use ((:instance f*-comm (x x) (y (f1))) f*-f1-1))))
(defthm f*-f+-distrib-1 (equal (f* x (f+ y z)) (f+ (f* x y) (f* x z))))
(defthm f*-f+-distrib-2 (equal (f* (f+ y z) x) (f+ (f* y x) (f* z x)))
  :hints (("Goal" :in-theory (disable f* f+ f*-f+-distrib-1)
           :use ((:instance f*-comm (x x) (y (f+ y z)))
                 (:instance f*-comm (x x) (y y))
                 (:instance f*-comm (x x) (y z))
                 f*-f+-distrib-1))))

(in-theory (disable f+ f* f-))

;; cancellation: a + b = a + c implies b = c
(defthm f+-cancel-lemma (equal (f+ (f- a) (f+ a b)) (ffix b))
  :hints (("Goal" :in-theory (disable f+-assoc f+-comm-2)
           :use ((:instance f+-assoc (x (f- a)) (y a) (z b))
                 (:instance f+-comm (x (f- a)) (y a))))))

(defthm f+-x-x-means-0
  (implies (equal (f+ y y) (ffix y)) (equal (ffix y) (f0)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f+-cancel-lemma (a y) (b y)))
           :in-theory (disable f+-cancel-lemma))))

(defthm f*-f0-1 (equal (f* (f0) x) (f0))
  :hints (("Goal" :use ((:instance f+-x-x-means-0 (y (f* (f0) x)))
                        (:instance f*-f+-distrib-2 (x x) (y (f0)) (z (f0))))
           :in-theory (disable f*-f+-distrib-2 f*-f+-distrib-1))))
(defthm f*-f0-2 (equal (f* x (f0)) (f0))
  :hints (("Goal" :use ((:instance f*-comm (x x) (y (f0)))))))

(defthm ffix-f0 (equal (ffix (f0)) (f0)) :hints (("Goal" :in-theory (enable ffix))))
(defthm ffix-f1 (equal (ffix (f1)) (f1)) :hints (("Goal" :in-theory (enable ffix))))

;; uniqueness of additive inverse: a + b = 0 implies a = -b
(defthm f+-zero-means-neg
  (implies (equal (f+ a b) (f0)) (equal (ffix a) (f- b)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f+-cancel-lemma (a b) (b a)))
           :in-theory (disable f+-cancel-lemma))))

(defthm f*-f--1 (equal (f* (f- x) y) (f- (f* x y)))
  :hints (("Goal" :use ((:instance f+-zero-means-neg (a (f* (f- x) y)) (b (f* x y)))
                        (:instance f*-f+-distrib-2 (x y) (y (f- x)) (z x))
                        (:instance f+-comm (x (f- x)) (y x)))
           :in-theory (disable f*-f+-distrib-2 f*-f+-distrib-1))))

(defthm f*-finv
  (implies (and (fp a) (not (equal a (f0))))
           (equal (f* (finv a) a) (f1)))
  :hints (("Goal" :in-theory (enable f* ffix))))

(defthm f*-finv-2
  (implies (and (fp a) (not (equal a (f0))))
           (equal (f* a (f* (finv a) x)) (ffix x)))
  :hints (("Goal" :use ((:instance f*-assoc (x a) (y (finv a)) (z x))
                        (:instance f*-comm (x a) (y (finv a))))
           :in-theory (disable f*-assoc f*-comm-2))))

(defthm f*-finv-3
  (implies (and (fp a) (not (equal a (f0))))
           (equal (f* (finv a) (f* a x)) (ffix x)))
  :hints (("Goal" :use ((:instance f*-assoc (x (finv a)) (y a) (z x)))
           :in-theory (disable f*-assoc f*-comm-2))))
;;; ===================================================================
;;; Lists of scalars and the coordinate space F^n
;;; ===================================================================

(defun f-listp (l)
  (if (consp l) (and (fp (car l)) (f-listp (cdr l))) (null l)))

(defun all-f0 (l)
  (if (consp l) (and (equal (car l) (f0)) (all-f0 (cdr l))) t))

(defun zeros (n) (if (zp n) nil (cons (f0) (zeros (1- n)))))

(defun fv+ (u v n)
  (if (zp n) nil (cons (f+ (car u) (car v)) (fv+ (cdr u) (cdr v) (1- n)))))

(defun fv* (c u n)
  (if (zp n) nil (cons (f* c (car u)) (fv* c (cdr u) (1- n)))))

(defun fvp (v n) (and (f-listp v) (equal (len v) n)))

(defun fvp-listp (vs n)
  (if (consp vs) (and (fvp (car vs) n) (fvp-listp (cdr vs) n)) t))

(defun flc (cs vs n)
  (if (endp vs) (zeros n)
    (fv+ (fv* (car cs) (car vs) n) (flc (cdr cs) (cdr vs) n) n)))

(defthm car-fv+ (implies (not (zp n)) (equal (car (fv+ u v n)) (f+ (car u) (car v)))))
(defthm cdr-fv+ (equal (cdr (fv+ u v n)) (fv+ (cdr u) (cdr v) (1- n))))
(defthm consp-fv+ (equal (consp (fv+ u v n)) (not (zp n))))
(defthm car-fv* (implies (not (zp n)) (equal (car (fv* c u n)) (f* c (car u)))))
(defthm cdr-fv* (equal (cdr (fv* c u n)) (fv* c (cdr u) (1- n))))
(defthm consp-fv* (equal (consp (fv* c u n)) (not (zp n))))
(defthm car-zeros (implies (not (zp n)) (equal (car (zeros n)) (f0))))
(defthm cdr-zeros (equal (cdr (zeros n)) (zeros (1- n))))
(defthm consp-zeros (equal (consp (zeros n)) (not (zp n))))

(defthm f-listp-zeros (f-listp (zeros n)))
(defthm len-zeros (equal (len (zeros n)) (nfix n)))
(defthm f-listp-fv+ (f-listp (fv+ u v n)))
(defthm len-fv+ (equal (len (fv+ u v n)) (nfix n)))
(defthm f-listp-fv* (f-listp (fv* c u n)))
(defthm len-fv* (equal (len (fv* c u n)) (nfix n)))
(defthm f-listp-flc (f-listp (flc cs vs n)))
(defthm len-flc (equal (len (flc cs vs n)) (nfix n)))

(defthm fv+-comm (equal (fv+ u v n) (fv+ v u n)))
(defthm fv+-assoc (equal (fv+ (fv+ u v n) w n) (fv+ u (fv+ v w n) n)))
(defthm fv+-comm-2 (equal (fv+ u (fv+ v w n) n) (fv+ v (fv+ u w n) n)))
(defthm fv*-fv+ (equal (fv* c (fv+ u v n) n) (fv+ (fv* c u n) (fv* c v n) n)))
(defthm fv*-fv* (equal (fv* c (fv* d u n) n) (fv* (f* c d) u n)))
(defthm fv*-f+ (equal (fv* (f+ c d) u n) (fv+ (fv* c u n) (fv* d u n) n)))
(defthm fv*-f0 (equal (fv* (f0) u n) (zeros n)))
(defthm fv*-zeros (equal (fv* c (zeros n) n) (zeros n)))
(defthm fv+-zeros-zeros (equal (fv+ (zeros n) (zeros n) n) (zeros n)))
(defthm fv*-f1 (implies (fvp u n) (equal (fv* (f1) u n) u)))

(defthm flc-zeros
  (implies (equal m (len vs))
           (equal (flc (zeros m) vs n) (zeros n))))

;;; first nonzero coordinate

(defun first-nonzero (v)
  (cond ((endp v) nil)
        ((not (equal (car v) (f0))) 0)
        (t (let ((r (first-nonzero (cdr v)))) (and r (1+ r))))))

(defthm first-nonzero-props
  (implies (first-nonzero v)
           (and (natp (first-nonzero v))
                (< (first-nonzero v) (len v))
                (not (equal (nth (first-nonzero v) v) (f0)))))
  :rule-classes ((:rewrite) (:linear :corollary
                                     (implies (first-nonzero v)
                                              (< (first-nonzero v) (len v))))))

(defthm no-first-nonzero
  (implies (and (not (first-nonzero v)) (f-listp v))
           (equal v (zeros (len v))))
  :rule-classes nil)

;;; removing a coordinate

(defun remove-nth (j v)
  (if (endp v) nil
    (if (zp j) (cdr v) (cons (car v) (remove-nth (1- j) (cdr v))))))

(defthm f-listp-remove-nth (implies (f-listp v) (f-listp (remove-nth j v))))
(defthm len-remove-nth
  (implies (and (natp j) (< j (len v)))
           (equal (len (remove-nth j v)) (1- (len v)))))

(defun ind-juvn (j u v n)
  (if (or (zp n) (zp j)) (list u v)
    (ind-juvn (1- j) (cdr u) (cdr v) (1- n))))

(defun ind-jun (j u n)
  (if (or (zp n) (zp j)) (list j u)
    (ind-jun (1- j) (cdr u) (1- n))))

(defthm remove-nth-fv+
  (implies (and (natp j) (< j n) (natp n))
           (equal (remove-nth j (fv+ u v n))
                  (fv+ (remove-nth j u) (remove-nth j v) (1- n))))
  :hints (("Goal" :induct (ind-juvn j u v n))))

(defthm remove-nth-fv*
  (implies (and (natp j) (< j n) (natp n))
           (equal (remove-nth j (fv* c u n))
                  (fv* c (remove-nth j u) (1- n))))
  :hints (("Goal" :induct (ind-jun j u n))))

(defthm remove-nth-zeros
  (implies (and (natp j) (< j n) (natp n))
           (equal (remove-nth j (zeros n)) (zeros (1- n))))
  :hints (("Goal" :induct (ind-jun j u n))))

(defthm nth-fv+
  (implies (and (natp j) (< j n) (natp n))
           (equal (nth j (fv+ u v n)) (f+ (nth j u) (nth j v))))
  :hints (("Goal" :induct (ind-juvn j u v n))))

(defthm nth-fv*
  (implies (and (natp j) (< j n) (natp n))
           (equal (nth j (fv* c u n)) (f* c (nth j u))))
  :hints (("Goal" :induct (ind-jun j u n) :expand ((fv* c u n)))))

(defthm nth-zeros
  (implies (and (natp j) (< j n) (natp n))
           (equal (nth j (zeros n)) (f0)))
  :hints (("Goal" :induct (ind-jun j u n) :expand ((zeros n)))))

(defthm zeros-from-nth-and-remove
  (implies (and (f-listp x) (equal (len x) n) (natp j) (< j n)
                (equal (nth j x) (f0))
                (equal (remove-nth j x) (zeros (1- n))))
           (equal x (zeros n)))
  :rule-classes nil
  :hints (("Goal" :induct (ind-jun j x n))))

;;; elimination

(defun elim-coef (w j a) (f- (f* (nth j w) (finv a))))

(defun elim-list (ws v j a n)
  (if (endp ws) nil
    (cons (fv+ (car ws) (fv* (elim-coef (car ws) j a) v n) n)
          (elim-list (cdr ws) v j a n))))

(defun coefs (ws j a)
  (if (endp ws) nil (cons (elim-coef (car ws) j a) (coefs (cdr ws) j a))))

(defun remove-nth-list (j vs)
  (if (endp vs) nil (cons (remove-nth j (car vs)) (remove-nth-list j (cdr vs)))))

(defun sdot (ds ks)
  (if (endp ks) (f0) (f+ (f* (car ds) (car ks)) (sdot (cdr ds) (cdr ks)))))

(defthm len-remove-nth-list (equal (len (remove-nth-list j vs)) (len vs)))
(defthm len-elim-list (equal (len (elim-list ws v j a n)) (len ws)))

(defthm flc-elim-list
  (equal (flc ds (elim-list ws v j a n) n)
         (fv+ (flc ds ws n) (fv* (sdot ds (coefs ws j a)) v n) n)))

(defun all-nth-zero (j vs)
  (if (endp vs) t (and (equal (nth j (car vs)) (f0)) (all-nth-zero j (cdr vs)))))

(defthm all-nth-zero-elim-list
  (implies (and (natp j) (< j n) (natp n) (fp a) (not (equal a (f0)))
                (equal (nth j v) a))
           (all-nth-zero j (elim-list ws v j a n))))

(defthm nth-flc-zero
  (implies (and (all-nth-zero j vs) (natp j) (< j n) (natp n))
           (equal (nth j (flc ds vs n)) (f0))))

(defthm remove-nth-flc
  (implies (and (natp j) (< j n) (natp n))
           (equal (remove-nth j (flc ds vs n))
                  (flc ds (remove-nth-list j vs) (1- n)))))

(defthm fvp-listp-elim-list
  (implies (natp n) (fvp-listp (elim-list ws v j a n) n)))

(defthm fvp-listp-remove-nth-list
  (implies (and (fvp-listp vs n) (natp j) (< j n))
           (fvp-listp (remove-nth-list j vs) (1- n))))

(defthm flc-elim-zero-a
  (implies (and (natp j) (< j n) (natp n) (fp a) (not (equal a (f0)))
                (equal (nth j v) a)
                (equal (flc ds (remove-nth-list j (elim-list ws v j a n)) (1- n))
                       (zeros (1- n))))
           (equal (flc ds (elim-list ws v j a n) n) (zeros n)))
  :hints (("Goal" :use ((:instance zeros-from-nth-and-remove
                                   (x (flc ds (elim-list ws v j a n) n))))
           :in-theory (disable flc-elim-list))))

(defthm flc-elim-zero
  (implies (and (natp j) (< j n) (natp n) (fp a) (not (equal a (f0)))
                (equal (nth j v) a)
                (equal (flc ds (remove-nth-list j (elim-list ws v j a n)) (1- n))
                       (zeros (1- n))))
           (equal (fv+ (flc ds ws n) (fv* (sdot ds (coefs ws j a)) v n) n)
                  (zeros n)))
  :hints (("Goal" :use flc-elim-zero-a
           :in-theory (disable flc-elim-zero-a remove-nth-flc))))
;;; The dependence-coefficient function (Gaussian elimination)

(defun fdep (vs n)
  (declare (xargs :measure (len vs)))
  (if (endp vs) nil
    (let* ((v (car vs)) (j (first-nonzero v)))
      (if (not j)
          (cons (f1) (zeros (len (cdr vs))))
        (let* ((a (nth j v))
               (ds (fdep (remove-nth-list j (elim-list (cdr vs) v j a n))
                         (1- n))))
          (cons (sdot ds (coefs (cdr vs) j a)) ds))))))

(defthm f-listp-fdep (f-listp (fdep vs n)))
(defthm len-fdep (equal (len (fdep vs n)) (len vs)))

(defthm fp-nth
  (implies (and (f-listp v) (natp j) (< j (len v)))
           (fp (nth j v))))

(defthm fv*-of-zero-vector
  (implies (and (fvp v n) (not (first-nonzero v)))
           (equal (fv* c v n) (zeros n)))
  :hints (("Goal" :use ((:instance no-first-nonzero)))))

(in-theory (disable zeros))

(defthm fvp-listp-cdr (implies (fvp-listp vs n) (fvp-listp (cdr vs) n)))

(defthm fdep-nontrivial
  (implies (and (fvp-listp vs n) (natp n) (< n (len vs)))
           (not (all-f0 (fdep vs n))))
  :hints (("Goal" :induct (fdep vs n))))

(defthm fdep-lincomb-zero
  (implies (and (fvp-listp vs n) (natp n) (< n (len vs)))
           (equal (flc (fdep vs n) vs n) (zeros n)))
  :hints (("Goal" :induct (fdep vs n))))
;;; ===================================================================
;;; A generic finite-dimensional vector space G over F
;;; (used to prove facts once, then functionally instantiated for V, W)
;;; ===================================================================

(encapsulate
  (((gp *) => *)
   ((g0) => *)
   ((gneg *) => *)
   ((gadd * *) => *)
   ((gmul * *) => *)
   ((gbasis) => *)
   ((gcoord *) => *))

  (local (defun gp (x) (fp x)))
  (local (defun g0 () (f0)))
  (local (defun gneg (x) (fneg x)))
  (local (defun gadd (x y) (fadd x y)))
  (local (defun gmul (c x) (fmul c x)))
  (local (defun gbasis () (list (f1))))
  (local (defun gcoord (x) (list x)))

  (defun gp-listp (l)
    (if (consp l) (and (gp (car l)) (gp-listp (cdr l))) (null l)))

  (defun glc (cs xs)
    (if (endp xs) (g0)
      (gadd (gmul (car cs) (car xs)) (glc (cdr cs) (cdr xs)))))

  (defthm gp-booleanp (booleanp (gp x)) :rule-classes :type-prescription)
  (defthm gp-g0 (gp (g0)))
  (defthm gp-gneg (implies (gp x) (gp (gneg x))))
  (defthm gp-gadd (implies (and (gp x) (gp y)) (gp (gadd x y))))
  (defthm gp-gmul (implies (and (fp c) (gp x)) (gp (gmul c x))))

  (defthm gadd-comm
    (implies (and (gp x) (gp y)) (equal (gadd x y) (gadd y x))))
  (defthm gadd-assoc
    (implies (and (gp x) (gp y) (gp z))
             (equal (gadd (gadd x y) z) (gadd x (gadd y z)))))
  (defthm gadd-g0 (implies (gp x) (equal (gadd (g0) x) x)))
  (defthm gadd-gneg (implies (gp x) (equal (gadd x (gneg x)) (g0))))

  (defthm gmul-gadd
    (implies (and (fp c) (gp x) (gp y))
             (equal (gmul c (gadd x y)) (gadd (gmul c x) (gmul c y)))))
  (defthm gmul-fadd
    (implies (and (fp a) (fp b) (gp x))
             (equal (gmul (fadd a b) x) (gadd (gmul a x) (gmul b x)))))
  (defthm gmul-fmul
    (implies (and (fp a) (fp b) (gp x))
             (equal (gmul (fmul a b) x) (gmul a (gmul b x)))))
  (defthm gmul-f1 (implies (gp x) (equal (gmul (f1) x) x)))

  (defthm gbasis-dim-posp (posp (len (gbasis))) :rule-classes :type-prescription)
  (defthm gp-listp-gbasis (gp-listp (gbasis)))
  (defthm gcoord-type
    (implies (gp x)
             (and (f-listp (gcoord x))
                  (equal (len (gcoord x)) (len (gbasis))))))
  (defthm glc-gcoord
    (implies (gp x) (equal (glc (gcoord x) (gbasis)) x))
    :hints (("Goal" :in-theory (disable (:executable-counterpart glc))
             :use ((:instance fmul-comm (x x) (y (f1)))
                          (:instance fadd-comm (x x) (y (f0)))))))
  (defthm gbasis-independent
    (implies (and (f-listp cs)
                  (equal (len cs) (len (gbasis)))
                  (equal (glc cs (gbasis)) (g0)))
             (all-f0 cs))
    :rule-classes nil
    :hints (("Goal" :in-theory (disable (:executable-counterpart glc))
             :use ((:instance fmul-comm (x (car cs)) (y (f1)))
                   (:instance fadd-comm (x (car cs)) (y (f0))))))))

(in-theory (disable (:executable-counterpart glc)
                    (:executable-counterpart gp-listp)
                    (:executable-counterpart zeros)
                    (:executable-counterpart flc)))

;;; group lemmas

(defthm gadd-g0-right (implies (gp x) (equal (gadd x (g0)) x))
  :hints (("Goal" :use ((:instance gadd-comm (y (g0)))))))

(defthm gadd-zero-means-neg
  (implies (and (gp a) (gp b) (equal (gadd a b) (g0)))
           (equal a (gneg b)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance gadd-assoc (x a) (y b) (z (gneg b)))))))

(defthm gadd-idem-means-zero
  (implies (and (gp y) (equal (gadd y y) y))
           (equal y (g0)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance gadd-assoc (x y) (y y) (z (gneg y)))))))

(defthm gmul-f0 (implies (gp x) (equal (gmul (f0) x) (g0)))
  :hints (("Goal" :use ((:instance gadd-idem-means-zero (y (gmul (f0) x)))
                        (:instance gmul-fadd (a (f0)) (b (f0)))))))

(defthm gmul-g0 (implies (fp c) (equal (gmul c (g0)) (g0)))
  :hints (("Goal" :use ((:instance gadd-idem-means-zero (y (gmul c (g0))))
                        (:instance gmul-gadd (x (g0)) (y (g0)))))))

(defthm gmul-fneg
  (implies (and (fp c) (gp x))
           (equal (gmul (fneg c) x) (gneg (gmul c x))))
  :hints (("Goal" :use ((:instance gadd-zero-means-neg (a (gmul (fneg c) x)) (b (gmul c x)))
                        (:instance gmul-fadd (a (fneg c)) (b c))
                        (:instance fadd-comm (x (fneg c)) (y c))))))

(defthm g-solve-1
  (implies (and (fp c) (not (equal c (f0))) (gp y) (gp z))
           (equal (gmul (finv c) (gadd (gmul c y) z))
                  (gadd y (gmul (finv c) z))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance gmul-gadd (c (finv c)) (x (gmul c y)) (y z))
                        (:instance gmul-fmul (a (finv c)) (b c) (x y))
                        (:instance fmul-comm (x (finv c)) (y c)))
           :in-theory (disable gmul-gadd gmul-fmul gadd-comm))))

(defthm g-solve
  (implies (and (fp c) (not (equal c (f0))) (gp y) (gp z)
                (equal (gadd (gmul c y) z) (g0)))
           (equal (gmul (fneg (finv c)) z) y))
  :rule-classes nil
  :hints (("Goal" :use (g-solve-1
                        (:instance gadd-zero-means-neg (a y) (b (gmul (finv c) z)))
                        (:instance gmul-fneg (c (finv c)) (x z)))
           :in-theory (disable gmul-fneg gadd-comm))))

;;; linear combinations

(defthm gp-glc
  (implies (and (f-listp cs) (equal (len cs) (len xs)) (gp-listp xs))
           (gp (glc cs xs))))

(defthm glc-zeros
  (implies (and (gp-listp bs) (equal m (len bs)))
           (equal (glc (zeros m) bs) (g0)))
  :hints (("Goal" :in-theory (enable zeros))))

(defun ind-abn (as as2 bs n)
  (if (endp bs) (list as as2 n)
    (ind-abn (cdr as) (cdr as2) (cdr bs) (1- n))))

(defthm glc-fv*
  (implies (and (fp c) (f-listp as) (equal (len as) n) (equal (len bs) n)
                (gp-listp bs))
           (equal (glc (fv* c as n) bs)
                  (gmul c (glc as bs))))
  :hints (("Goal" :in-theory (enable f* ffix) :induct (ind-abn as as bs n))))

(defthm gadd-4
  (implies (and (gp a) (gp b) (gp c) (gp d))
           (equal (gadd (gadd a b) (gadd c d))
                  (gadd (gadd a c) (gadd b d))))
  :hints (("Goal" :use ((:instance gadd-assoc (x a) (y b) (z (gadd c d)))
                        (:instance gadd-assoc (x b) (y c) (z d))
                        (:instance gadd-comm (x b) (y c))
                        (:instance gadd-assoc (x c) (y b) (z d))
                        (:instance gadd-assoc (x a) (y c) (z (gadd b d))))
           :in-theory (disable gadd-assoc))))

(defthm glc-fv+
  (implies (and (f-listp as) (f-listp as2)
                (equal (len as) n) (equal (len as2) n) (equal (len bs) n)
                (gp-listp bs))
           (equal (glc (fv+ as as2 n) bs)
                  (gadd (glc as bs) (glc as2 bs))))
  :hints (("Goal" :in-theory (enable f+ ffix) :induct (ind-abn as as2 bs n))))

(defun gcoords (xs)
  (if (endp xs) nil (cons (gcoord (car xs)) (gcoords (cdr xs)))))

(defthm fvp-listp-gcoords
  (implies (gp-listp xs) (fvp-listp (gcoords xs) (len (gbasis)))))
(defthm len-gcoords (equal (len (gcoords xs)) (len xs)))

(defthm glc-transfer
  (implies (and (gp-listp xs) (f-listp cs) (equal (len cs) (len xs)))
           (equal (glc (flc cs (gcoords xs) (len (gbasis))) (gbasis))
                  (glc cs xs))))

(defun gdep (xs) (fdep (gcoords xs) (len (gbasis))))

(defthm gdep-correct
  (implies (and (gp-listp xs) (< (len (gbasis)) (len xs)))
           (and (f-listp (gdep xs))
                (equal (len (gdep xs)) (len xs))
                (not (all-f0 (gdep xs)))
                (equal (glc (gdep xs) xs) (g0))))
  :hints (("Goal" :use ((:instance glc-transfer (cs (gdep xs))))
           :in-theory (disable glc-transfer))))
;;; ===================================================================
;;; The vector space V
;;; ===================================================================

(encapsulate
  (((vp *) => *)
   ((v0) => *)
   ((vneg *) => *)
   ((vadd * *) => *)
   ((vmul * *) => *)
   ((vbasis) => *)
   ((vcoord *) => *))

  (local (defun vp (x) (fp x)))
  (local (defun v0 () (f0)))
  (local (defun vneg (x) (fneg x)))
  (local (defun vadd (x y) (fadd x y)))
  (local (defun vmul (c x) (fmul c x)))
  (local (defun vbasis () (list (f1))))
  (local (defun vcoord (x) (list x)))

  (defun vp-listp (l)
    (if (consp l) (and (vp (car l)) (vp-listp (cdr l))) (null l)))

  (defun vlc (cs xs)
    (if (endp xs) (v0)
      (vadd (vmul (car cs) (car xs)) (vlc (cdr cs) (cdr xs)))))

  (defthm vp-booleanp (booleanp (vp x)) :rule-classes :type-prescription)
  (defthm vp-v0 (vp (v0)))
  (defthm vp-vneg (implies (vp x) (vp (vneg x))))
  (defthm vp-vadd (implies (and (vp x) (vp y)) (vp (vadd x y))))
  (defthm vp-vmul (implies (and (fp c) (vp x)) (vp (vmul c x))))

  (defthm vadd-comm
    (implies (and (vp x) (vp y)) (equal (vadd x y) (vadd y x))))
  (defthm vadd-assoc
    (implies (and (vp x) (vp y) (vp z))
             (equal (vadd (vadd x y) z) (vadd x (vadd y z)))))
  (defthm vadd-v0 (implies (vp x) (equal (vadd (v0) x) x)))
  (defthm vadd-vneg (implies (vp x) (equal (vadd x (vneg x)) (v0))))

  (defthm vmul-vadd
    (implies (and (fp c) (vp x) (vp y))
             (equal (vmul c (vadd x y)) (vadd (vmul c x) (vmul c y)))))
  (defthm vmul-fadd
    (implies (and (fp a) (fp b) (vp x))
             (equal (vmul (fadd a b) x) (vadd (vmul a x) (vmul b x)))))
  (defthm vmul-fmul
    (implies (and (fp a) (fp b) (vp x))
             (equal (vmul (fmul a b) x) (vmul a (vmul b x)))))
  (defthm vmul-f1 (implies (vp x) (equal (vmul (f1) x) x)))

  (defthm vbasis-dim-posp (posp (len (vbasis))) :rule-classes :type-prescription)
  (defthm vp-listp-vbasis (vp-listp (vbasis)))
  (defthm vcoord-type
    (implies (vp x)
             (and (f-listp (vcoord x))
                  (equal (len (vcoord x)) (len (vbasis))))))
  (defthm vlc-vcoord
    (implies (vp x) (equal (vlc (vcoord x) (vbasis)) x))
    :hints (("Goal" :in-theory (disable (:executable-counterpart vlc))
             :use ((:instance fmul-comm (x x) (y (f1)))
                          (:instance fadd-comm (x x) (y (f0)))))))
  (defthm vbasis-independent
    (implies (and (f-listp cs)
                  (equal (len cs) (len (vbasis)))
                  (equal (vlc cs (vbasis)) (v0)))
             (all-f0 cs))
    :hints (("Goal" :in-theory (disable (:executable-counterpart vlc))
             :use ((:instance fmul-comm (x (car cs)) (y (f1)))
                   (:instance fadd-comm (x (car cs)) (y (f0))))))))

(in-theory (disable (:executable-counterpart vlc)
                    (:executable-counterpart vp-listp)
                    (:executable-counterpart zeros)
                    (:executable-counterpart flc)))

;;; ===================================================================
;;; The vector space W
;;; ===================================================================

(encapsulate
  (((wp *) => *)
   ((w0) => *)
   ((wneg *) => *)
   ((wadd * *) => *)
   ((wmul * *) => *)
   ((wbasis) => *)
   ((wcoord *) => *))

  (local (defun wp (x) (fp x)))
  (local (defun w0 () (f0)))
  (local (defun wneg (x) (fneg x)))
  (local (defun wadd (x y) (fadd x y)))
  (local (defun wmul (c x) (fmul c x)))
  (local (defun wbasis () (list (f1))))
  (local (defun wcoord (x) (list x)))

  (defun wp-listp (l)
    (if (consp l) (and (wp (car l)) (wp-listp (cdr l))) (null l)))

  (defun wlc (cs xs)
    (if (endp xs) (w0)
      (wadd (wmul (car cs) (car xs)) (wlc (cdr cs) (cdr xs)))))

  (defthm wp-booleanp (booleanp (wp x)) :rule-classes :type-prescription)
  (defthm wp-w0 (wp (w0)))
  (defthm wp-wneg (implies (wp x) (wp (wneg x))))
  (defthm wp-wadd (implies (and (wp x) (wp y)) (wp (wadd x y))))
  (defthm wp-wmul (implies (and (fp c) (wp x)) (wp (wmul c x))))

  (defthm wadd-comm
    (implies (and (wp x) (wp y)) (equal (wadd x y) (wadd y x))))
  (defthm wadd-assoc
    (implies (and (wp x) (wp y) (wp z))
             (equal (wadd (wadd x y) z) (wadd x (wadd y z)))))
  (defthm wadd-w0 (implies (wp x) (equal (wadd (w0) x) x)))
  (defthm wadd-wneg (implies (wp x) (equal (wadd x (wneg x)) (w0))))

  (defthm wmul-wadd
    (implies (and (fp c) (wp x) (wp y))
             (equal (wmul c (wadd x y)) (wadd (wmul c x) (wmul c y)))))
  (defthm wmul-fadd
    (implies (and (fp a) (fp b) (wp x))
             (equal (wmul (fadd a b) x) (wadd (wmul a x) (wmul b x)))))
  (defthm wmul-fmul
    (implies (and (fp a) (fp b) (wp x))
             (equal (wmul (fmul a b) x) (wmul a (wmul b x)))))
  (defthm wmul-f1 (implies (wp x) (equal (wmul (f1) x) x)))

  (defthm wbasis-dim-posp (posp (len (wbasis))) :rule-classes :type-prescription)
  (defthm wp-listp-wbasis (wp-listp (wbasis)))
  (defthm wcoord-type
    (implies (wp x)
             (and (f-listp (wcoord x))
                  (equal (len (wcoord x)) (len (wbasis))))))
  (defthm wlc-wcoord
    (implies (wp x) (equal (wlc (wcoord x) (wbasis)) x))
    :hints (("Goal" :in-theory (disable (:executable-counterpart wlc))
             :use ((:instance fmul-comm (x x) (y (f1)))
                          (:instance fadd-comm (x x) (y (f0)))))))
  (defthm wbasis-independent
    (implies (and (f-listp cs)
                  (equal (len cs) (len (wbasis)))
                  (equal (wlc cs (wbasis)) (w0)))
             (all-f0 cs))
    :hints (("Goal" :in-theory (disable (:executable-counterpart wlc))
             :use ((:instance fmul-comm (x (car cs)) (y (f1)))
                   (:instance fadd-comm (x (car cs)) (y (f0))))))))

(in-theory (disable (:executable-counterpart wlc)
                    (:executable-counterpart wp-listp)
                    (:executable-counterpart zeros)
                    (:executable-counterpart flc)))

(in-theory (disable (:executable-counterpart vlc)
                    (:executable-counterpart vp-listp)
                    (:executable-counterpart wlc)
                    (:executable-counterpart wp-listp)))

(defun vcoords (xs)
  (if (endp xs) nil (cons (vcoord (car xs)) (vcoords (cdr xs)))))
(defun vdep (xs) (fdep (vcoords xs) (len (vbasis))))
(defun wcoords (xs)
  (if (endp xs) nil (cons (wcoord (car xs)) (wcoords (cdr xs)))))
(defun wdep (xs) (fdep (wcoords xs) (len (wbasis))))

;;; Facts about V and W obtained from the generic space G

(defthm vp-vlc
  (implies (and (f-listp cs) (equal (len cs) (len xs)) (vp-listp xs))
           (vp (vlc cs xs)))
  :hints (("Goal" :use ((:functional-instance gp-glc (gp-listp vp-listp) (gp vp) (g0 v0) (gneg vneg) (gadd vadd) (gmul vmul) (gbasis vbasis) (gcoord vcoord) (glc vlc) (gcoords vcoords) (gdep vdep))))))

(defthm wp-wlc
  (implies (and (f-listp cs) (equal (len cs) (len xs)) (wp-listp xs))
           (wp (wlc cs xs)))
  :hints (("Goal" :use ((:functional-instance gp-glc (gp-listp wp-listp) (gp wp) (g0 w0) (gneg wneg) (gadd wadd) (gmul wmul) (gbasis wbasis) (gcoord wcoord) (glc wlc) (gcoords wcoords) (gdep wdep))))))

(defthm vdep-correct
  (implies (and (vp-listp xs) (< (len (vbasis)) (len xs)))
           (and (f-listp (vdep xs))
                (equal (len (vdep xs)) (len xs))
                (not (all-f0 (vdep xs)))
                (equal (vlc (vdep xs) xs) (v0))))
  :hints (("Goal" :use ((:functional-instance gdep-correct (gp-listp vp-listp) (gp vp) (g0 v0) (gneg vneg) (gadd vadd) (gmul vmul) (gbasis vbasis) (gcoord vcoord) (glc vlc) (gcoords vcoords) (gdep vdep))))))

(defthm wdep-correct
  (implies (and (wp-listp xs) (< (len (wbasis)) (len xs)))
           (and (f-listp (wdep xs))
                (equal (len (wdep xs)) (len xs))
                (not (all-f0 (wdep xs)))
                (equal (wlc (wdep xs) xs) (w0))))
  :hints (("Goal" :use ((:functional-instance gdep-correct (gp-listp wp-listp) (gp wp) (g0 w0) (gneg wneg) (gadd wadd) (gmul wmul) (gbasis wbasis) (gcoord wcoord) (glc wlc) (gcoords wcoords) (gdep wdep))))))

(defthm wmul-f0 (implies (wp x) (equal (wmul (f0) x) (w0)))
  :hints (("Goal" :use ((:functional-instance gmul-f0 (gp-listp wp-listp) (gp wp) (g0 w0) (gneg wneg) (gadd wadd) (gmul wmul) (gbasis wbasis) (gcoord wcoord) (glc wlc) (gcoords wcoords) (gdep wdep))))))

(defthm wmul-w0 (implies (fp c) (equal (wmul c (w0)) (w0)))
  :hints (("Goal" :use ((:functional-instance gmul-g0 (gp-listp wp-listp) (gp wp) (g0 w0) (gneg wneg) (gadd wadd) (gmul wmul) (gbasis wbasis) (gcoord wcoord) (glc wlc) (gcoords wcoords) (gdep wdep))))))

(defthm w-solve
  (implies (and (fp c) (not (equal c (f0))) (wp y) (wp z)
                (equal (wadd (wmul c y) z) (w0)))
           (equal (wmul (fneg (finv c)) z) y))
  :rule-classes nil
  :hints (("Goal" :use ((:functional-instance g-solve (gp-listp wp-listp) (gp wp) (g0 w0) (gneg wneg) (gadd wadd) (gmul wmul) (gbasis wbasis) (gcoord wcoord) (glc wlc) (gcoords wcoords) (gdep wdep))))))

;;; ===================================================================
;;; The linear transformation T : V -> W
;;; ===================================================================

(encapsulate
  (((lt *) => *))
  (local (defun lt (x) (declare (ignore x)) (w0)))
  (defthm wp-lt (implies (vp x) (wp (lt x))))
  (defthm lt-v0 (equal (lt (v0)) (w0)))
  (defthm lt-vadd
    (implies (and (vp x) (vp y))
             (equal (lt (vadd x y)) (wadd (lt x) (lt y)))))
  (defthm lt-vmul
    (implies (and (fp c) (vp x))
             (equal (lt (vmul c x)) (wmul c (lt x))))))

(defun-sk injective ()
  (forall x (implies (and (vp x) (equal (lt x) (w0)))
                     (equal x (v0)))))

(defun-sk preimage (y)
  (exists x (and (vp x) (equal (lt x) y))))

(defun-sk surjective ()
  (forall y (implies (wp y) (preimage y))))

(defun dim-v () (len (vbasis)))
(defun dim-w () (len (wbasis)))

;;; ===================================================================
;;; Proof
;;; ===================================================================

(defun tmap (xs) (if (endp xs) nil (cons (lt (car xs)) (tmap (cdr xs)))))

(defthm len-tmap (equal (len (tmap xs)) (len xs)))
(defthm wp-listp-tmap (implies (vp-listp xs) (wp-listp (tmap xs))))

(defthm wlc-tmap
  (implies (and (vp-listp xs) (f-listp cs) (equal (len cs) (len xs)))
           (equal (wlc cs (tmap xs)) (lt (vlc cs xs)))))

(defthm t-basis-indep
  (implies (and (injective) (f-listp cs) (equal (len cs) (len (vbasis)))
                (equal (wlc cs (tmap (vbasis))) (w0)))
           (all-f0 cs))
  :hints (("Goal" :use ((:instance injective-necc (x (vlc cs (vbasis))))
                        (:instance vbasis-independent))
           :in-theory (disable injective-necc))))

(defthm inj-dim-le
  (implies (injective) (<= (len (vbasis)) (len (wbasis))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance wdep-correct (xs (tmap (vbasis))))
                        (:instance t-basis-indep (cs (wdep (tmap (vbasis))))))
           :in-theory (disable wdep-correct t-basis-indep wdep))))

(defun prelist (ys)
  (if (endp ys) nil (cons (preimage-witness (car ys)) (prelist (cdr ys)))))

(defthm surj-witness-props
  (implies (and (surjective) (wp y))
           (and (vp (preimage-witness y))
                (equal (lt (preimage-witness y)) y)))
  :hints (("Goal" :use ((:instance surjective-necc))
           :in-theory (disable surjective-necc surjective))))

(defthm prelist-props
  (implies (and (surjective) (wp-listp ys))
           (and (vp-listp (prelist ys))
                (equal (len (prelist ys)) (len ys))
                (equal (tmap (prelist ys)) ys)))
  :hints (("Goal" :induct (prelist ys)
           :in-theory (disable surjective preimage))))

(defthm surj-dim-le
  (implies (surjective) (<= (len (wbasis)) (len (vbasis))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance vdep-correct (xs (prelist (wbasis))))
                        (:instance wlc-tmap (cs (vdep (prelist (wbasis))))
                                   (xs (prelist (wbasis))))
                        (:instance wbasis-independent (cs (vdep (prelist (wbasis))))))
           :in-theory (disable vdep-correct wlc-tmap vdep))))

(defthm part3-core
  (implies (and (injective) (wp y) (f-listp cs)
                (equal (len cs) (1+ (len (vbasis))))
                (not (all-f0 cs))
                (equal (wlc cs (cons y (tmap (vbasis)))) (w0)))
           (preimage y))
  :rule-classes nil
  :hints (("Goal" :cases ((equal (car cs) (f0))))
          ("Subgoal 2"
           :use ((:instance w-solve (c (car cs)) (y y)
                            (z (wlc (cdr cs) (tmap (vbasis)))))
                 (:instance preimage-suff
                            (x (vmul (fneg (finv (car cs)))
                                     (vlc (cdr cs) (vbasis)))))))
          ("Subgoal 1"
           :use ((:instance t-basis-indep (cs (cdr cs)))))))

(defthm inj-eqdim-preimage
  (implies (and (injective) (equal (len (vbasis)) (len (wbasis))) (wp y))
           (preimage y))
  :rule-classes nil
  :hints (("Goal" :use ((:instance wdep-correct (xs (cons y (tmap (vbasis)))))
                        (:instance part3-core (cs (wdep (cons y (tmap (vbasis)))))))
           :in-theory (disable wdep-correct wdep preimage))))

(defthm inj-eqdim-surj
  (implies (and (injective) (equal (len (vbasis)) (len (wbasis))))
           (surjective))
  :rule-classes nil
  :hints (("Goal" :use ((:instance inj-eqdim-preimage (y (surjective-witness))))
           :in-theory (disable preimage))))

(defthm main
  (implies (injective)
           (and (<= (dim-v) (dim-w))
                (iff (surjective) (equal (dim-v) (dim-w)))))
  :hints (("Goal" :use (inj-dim-le surj-dim-le inj-eqdim-surj)
           :in-theory (disable injective surjective))))
