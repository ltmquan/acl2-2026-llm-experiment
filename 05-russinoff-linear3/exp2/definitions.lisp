(in-package "DM")

;; Authors' definitions from ACL2 master books/projects/linear/vectors.lisp (Part III).
;; LOCAL events are proof support copied from master books/projects/linear/support/vectors.lisp;
;; they are needed only to admit the lin encapsulate (c*w0), sbasis0-aux (termination hint) and the
;; sbasis1 encapsulate (slistnp-sbasis0, flistnp-scoords0, sbasis0-spans, vindepp-sbasis0).
;; Each event is preceded by its source location.  LOCAL events are not exported.

;;; ===== from projects/linear/vectors.lisp =====
;;; projects/linear/vectors.lisp, lines 3-3
(include-book "projects/linear/reduction" :dir :system)

;; vectors.lisp:16
;;; projects/linear/vectors.lisp, lines 16-90
(encapsulate (((vp *) => *)        ;vector recognizer
              ((v+ * *) => *)      ;vector addition
	      ((v0) => *)          ;zero vector
	      ((v- *) => *)        ;additive inverse
	      ((v* * *) => *)      ;scalar multiplication
	      ((vbasis0) => *)     ;canonical basis
	      ((vcoords0 *) => *)) ;coordinates relative ro basis
  (local (defun vp (x) (fp x)))
  (local (defun v+ (x y) (f+ x y)))
  (local (defun v0 () (f0)))
  (local (defun v- (x) (f- x)))
  (local (defun v* (c x) (f* c x)))
  (local (defun vbasis0 () (list (f1))))
  (local (defun vcoords0 (x) (list x)))
  (defthm vp-v0
    (vp (v0)))
  (defthm vp-v-
    (implies (vp x) (vp (v- x))))
  ;; Vector addition:
  (defthm v+closed (implies (and (vp x) (vp y)) (vp (v+ x y))))
  (defthmd v+comm
    (implies (and (vp x) (vp y)) (equal (v+ x y) (v+ y x)))
    :hints (("Goal" :use (f+comm))))
  (defthmd v+assoc
    (implies (and (vp x) (vp y) (vp z)) (equal (v+ x (v+ y z)) (v+ (v+ x y) z)))
    :hints (("Goal" :use (f+assoc))))
  (defthm v+id
    (implies (vp x) (equal (v+ x (v0)) x)))
  (defthm v+inv
    (implies (vp x) (equal (v+ x (v- x)) (v0))))
  ;; Scalar multiplication:
  (defthm v*closed
    (implies (and (fp c) (vp x)) (vp (v* c x))))
  (defthm v*id
    (implies (vp x) (equal (v* (f1) x) x)))
  (defthmd v*assoc
    (implies (and (fp c) (fp d) (vp x)) (equal (v* c (v* d x)) (v* (f* c d) x)))
    :hints (("Goal" :use ((:instance f*assoc (x c) (y d) (z x))))))
  (defthmd vdistf
    (implies (and (fp c) (fp d) (vp x)) (equal (v+ (v* c x) (v* d x)) (v* (f+ c d) x)))
    :hints (("Goal" :use ((:instance fdist-comm (x c) (y d) (z x))))))
  (defthmd vdistv
    (implies (and (fp c) (vp x) (vp y)) (equal (v+ (v* c x) (v* c y)) (v* c (v+ x y))))
    :hints (("Goal" :use ((:instance fdist-comm (x c) (y x) (z y))))))
  ;; List of vectors:
  (defun vlistnp (x n)
    (if (zp n)
        (null x)
      (and (consp x)
           (vp (car x))
	   (vlistnp (cdr x) (1- n)))))
  ;; Linear combination of a list of vectors:
  (defun vcomb (flist vlist)
    (if (consp flist)
        (v+ (v* (car flist) (car vlist))
	    (vcomb (cdr flist) (cdr vlist)))
      (v0)))
  ;; Basis and coordinates:
  (defun vdim () (len (vbasis0)))
  (defthmd posp-vdim
    (posp (vdim)))
  (in-theory (disable (vdim) (vlistnp) (vcomb)))
  (defthm vlistnp-basis0
    (vlistnp (vbasis0) (vdim)))
  (defthm flistnp-vcoords0
    (implies (vp x) (flistnp (vcoords0 x) (vdim))))
  (defthm vbasis0-spans
    (implies (vp x)
             (equal (vcomb (vcoords0 x) (vbasis0))
		    x)))
  (defthmd vbasis0-lin-indep
    (implies (and (flistnp c (vdim))
                  (equal (vcomb c (vbasis0)) (v0)))
	     (equal (flistn0 (vdim)) c)))
  (in-theory (disable vdim)))

;; support/vectors.lisp:90
;;; ===== from projects/linear/support/vectors.lisp =====
;;; projects/linear/support/vectors.lisp, lines 90-92 (wrapped in local)
(local
 (defthm v+id-comm
  (implies (vp x) (equal (v+ (v0) x) x))
  :hints (("Goal" :use ((:instance v+comm (y (v0))))))))

;; support/vectors.lisp:94
;;; projects/linear/support/vectors.lisp, lines 94-96 (wrapped in local)
(local
 (defthm v+inv-comm
  (implies (vp x) (equal (v+ (v- x) x) (v0)))
  :hints (("Goal" :use ((:instance v+comm (y (v- x))))))))

;; support/vectors.lisp:98
;;; projects/linear/support/vectors.lisp, lines 98-101 (wrapped in local)
(local
 (defthm f0*v0
  (implies (vp x) (equal (v* (f0) x) (v0)))
  :hints (("Goal" :use ((:instance vdistf (c (f1)) (d (f0)))
			(:instance v+assoc (x (v- x)) (y x) (z (v* (f0) x))))))))

;; support/vectors.lisp:103
;;; projects/linear/support/vectors.lisp, lines 103-106 (wrapped in local)
(local
 (defthm c*v0
  (implies (fp c) (equal (v* c (v0)) (v0)))
  :hints (("Goal" :use ((:instance vdistv (x (v0)) (y (v0)))
			(:instance v+assoc (x (v- (v* c (v0)))) (y (v* c (v0))) (z (v* c (v0)))))))))

;; support/vectors.lisp:120
;;; ===== from projects/linear/vectors.lisp =====
;;; projects/linear/vectors.lisp, lines 115-117 (wrapped in local)
(local
 (defthm vp-vcomb
  (implies (and (flistnp c n) (vlistnp l n))
	   (vp (vcomb c l)))))

;; support/vectors.lisp:124
;;; ===== from projects/linear/support/vectors.lisp =====
;;; projects/linear/support/vectors.lisp, lines 124-127 (wrapped in local)
(local
 (defthm len-vlistnp
  (implies (and (natp n) (vlistnp x n))
           (equal (len x) n))
  :hints (("Goal" :induct (nthcdr n x)))))

;; support/vectors.lisp:129
;;; projects/linear/support/vectors.lisp, lines 129-132 (wrapped in local)
(local
 (defun vp-nth-vlistnp-induct (x n j)
  (if (zp j)
      (list x n j)
    (list (vp-nth-vlistnp-induct (cdr x) (1- n) (1- j))))))

;; support/vectors.lisp:134
;;; projects/linear/support/vectors.lisp, lines 134-137 (wrapped in local)
(local
 (defthm vp-nth-vlistnp
  (implies (and (vlistnp x n) (natp n) (natp j) (< j n))
           (vp (nth j x)))
  :hints (("Goal" :induct (vp-nth-vlistnp-induct x n j)))))

;; support/vectors.lisp:139
;;; projects/linear/support/vectors.lisp, lines 139-148 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd hack-1
  (implies (and (fp x0) (fp y0) (vp l0) (vp lx) (vp ly))
	   (equal (v+ (v* (f+ x0 y0) l0) (v+ lx ly))
		  (v+ (v+ (v* x0 l0) lx) (v+ (v* y0 l0) ly))))
  :hints (("Goal" :use ((:instance v+assoc (x (v+ (v* x0 l0) lx)) (y (v* y0 l0)) (z ly))
			(:instance v+assoc (x (v* x0 l0)) (y lx) (z (v* y0 l0)))
			(:instance v+comm (x lx) (y (v* y0 l0)))
			(:instance v+assoc (x (v* x0 l0)) (y (v* y0 l0)) (z lx))
			(:instance v+assoc (x (v+ (v* x0 l0) (v* y0 l0))) (y lx) (z ly))
			(:instance vdistf (c x0) (d y0) (x l0)))))))

;; support/vectors.lisp:150
;;; projects/linear/support/vectors.lisp, lines 150-155 (wrapped in local)
(local
 (defthmd vcomb-add
  (implies (and (natp n) (vlistnp l n) (flistnp x n) (flistnp y n))
	   (equal (vcomb (flist-add x y) l)
		  (v+ (vcomb x l) (vcomb y l))))
  :hints (("Subgoal *1/6" :use ((:instance hack-1 (x0 (car x)) (y0 (car y)) (l0 (car l))
					   (lx (VCOMB (CDR X) (CDR L))) (ly (VCOMB (CDR y) (CDR L)))))))))

;; support/vectors.lisp:157
;;; projects/linear/support/vectors.lisp, lines 157-162 (wrapped in local)
(local
 (defthmd vcomb-scalar-mul
  (implies (and (natp n) (vlistnp l n) (flistnp x n) (fp c))
	   (equal (vcomb (flist-scalar-mul c x) l)
		  (v* c (vcomb x l))))
  :hints (("Subgoal *1/5" :use ((:instance v*assoc (d (car x)) (x (car l)))
				(:instance vdistv (x (v* (car x) (car l))) (y (VCOMB (CDR X) (CDR L)))))))))

;; support/vectors.lisp:174
;;; projects/linear/support/vectors.lisp, lines 174-180 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vcoords0-unique-1
  (implies (and (natp n) (flistnp x n) (flistnp y n) (vlistnp l n)
		(= (vcomb x l) (vcomb y l)))
	   (equal (vcomb (flist-add x (flist-scalar-mul (f- (f1)) y)) l)
		  (v0)))
  :hints (("Goal" :in-theory (enable vcomb-add vcomb-scalar-mul)
	          :use ((:instance vdistf (c (f1)) (d (f- (f1))) (x (vcomb x l))))))))

;; support/vectors.lisp:182
;;; projects/linear/support/vectors.lisp, lines 182-190 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vcoords0-unique-2
  (implies (and (flistnp x (vdim)) (flistnp y (vdim))
		(= (vcomb x (vbasis0)) (vcomb y (vbasis0))))
	   (equal (flist-add x (flist-scalar-mul (f- (f1)) y))
		  (flistn0 (vdim))))
  :hints (("Goal" :in-theory (enable vdim)
                  :use (vlistnp-basis0
		        (:instance vcoords0-unique-1 (n (vdim)) (l (vbasis0)))
                        (:instance vbasis0-lin-indep (c (flist-add x (flist-scalar-mul (f- (f1)) y)))))))))

;; support/vectors.lisp:192
;;; projects/linear/support/vectors.lisp, lines 192-197 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthm vcoords0-unique-3
  (implies (and (fp x) (fp y) (= (f+ x (f* (f- (f1)) y)) (f0)))
	   (equal x y))
  :rule-classes ()
  :hints (("Goal" :use ((:instance f+assoc (y (f* (f- (f1)) y)) (z y))
                        (:instance fdist-comm (x (f- (f1))) (y (f1)) (z y)))))))

;; support/vectors.lisp:199
;;; projects/linear/support/vectors.lisp, lines 199-205 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthm vcoords0-unique-4
  (implies (and (natp n) (flistnp x n) (flistnp y n)
	        (equal (flist-add x (flist-scalar-mul (f- (f1)) y))
		       (flistn0 n)))
	   (equal x y))
  :rule-classes ()
  :hints (("Subgoal *1/7" :use ((:instance vcoords0-unique-3 (x (car x)) (y (car y))))))))

;; support/vectors.lisp:207
;;; projects/linear/support/vectors.lisp, lines 207-212 (wrapped in local)
(local
 (defthmd vcoords0-unique
  (implies (and (vp x) (flistnp c (vdim))
		(equal (vcomb c (vbasis0)) x))
	   (equal (vcoords0 x) c))
  :hints (("Goal" :use ((:instance vcoords0-unique-4 (n (vdim)) (x c) (y (vcoords0 x)))
                        (:instance vcoords0-unique-2 (x c) (y (vcoords0 x))))))))

;; support/vectors.lisp:216
;;; projects/linear/support/vectors.lisp, lines 216-220 (wrapped in local)
(local
 (defthm vcomb-flistn0
  (implies (vlistnp l n)
           (equal (vcomb (flistn0 n) l)
	          (v0)))
  :hints (("Goal" :induct (nthcdr n l)))))

;; support/vectors.lisp:222
;;; projects/linear/support/vectors.lisp, lines 222-225 (wrapped in local)
(local
 (defthm vcoords0-v0
  (equal (vcoords0 (v0))
         (flistn0 (vdim)))
  :hints (("Goal" :use ((:instance vcoords0-unique (x (v0)) (c (flistn0 (vdim)))))))))

;; vectors.lisp:186
;;; ===== from projects/linear/vectors.lisp =====
;;; projects/linear/vectors.lisp, lines 186-190
(defun vcoord-mat (l)
  (if (consp l)
      (cons (vcoords0 (car l))
	    (vcoord-mat (cdr l)))
    ()))

;; support/vectors.lisp:258
;;; ===== from projects/linear/support/vectors.lisp =====
;;; projects/linear/support/vectors.lisp, lines 258-258 (wrapped in local)
(local
 (in-theory (enable fmatp)))

;; support/vectors.lisp:260
;;; projects/linear/support/vectors.lisp, lines 260-263 (wrapped in local)
(local
 (defthm fmatp-vcoord-mat
  (implies (vlistnp l m)
           (fmatp (vcoord-mat l) m (vdim)))
  :hints (("Goal" :induct (nthcdr m l)))))

;; support/vectors.lisp:280
;;; projects/linear/support/vectors.lisp, lines 280-287 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vcoords0-vcomb-1
  (implies (and (vlistnp l 1) (flistnp c 1) (natp j) (< j (vdim)))
           (equal (nth j (car (fmat* (list c) (vcoord-mat l))))
	          (f* (car c) (nth j (vcoords0 (car l))))))
  :hints (("Goal" :use ((:instance fmat*-entry (i 0) (m 1) (n 1) (p (vdim)) (a (list c)) (b (vcoord-mat l)))
                        (:instance fp-flistnp (i j) (n (vdim)) (x (vcoords0 (car l)))))
                  :in-theory (disable (fdot))
                  :expand ((flistnp c 1) (vlistnp l 1))))))

;; support/vectors.lisp:289
;;; projects/linear/support/vectors.lisp, lines 289-294 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vcoords0-vcomb-2
  (implies (and (vlistnp l 1) (flistnp c 1) (natp j) (< j (vdim)))
           (equal (nth j (flist-scalar-mul (car c) (vcoords0 (car l))))
	          (nth j (car (fmat* (list c) (vcoord-mat l))))))
  :hints (("Goal" :use (vcoords0-vcomb-1
                        (:instance nth-flist-scalar-mul (c (car c)) (x (vcoords0 (car l))) (n (vdim)) (i j)))))))

;; support/vectors.lisp:296
;;; projects/linear/support/vectors.lisp, lines 296-306 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vcoords0-vcomb-3
  (implies (and (vlistnp l 1) (flistnp c 1))
           (equal (car (fmat* (list c) (vcoord-mat l)))
	          (flist-scalar-mul (car c) (vcoords0 (car l)))))
  :hints (("Goal" :use (posp-vdim
                        (:instance nth-diff-diff (x (car (fmat* (list c) (vcoord-mat l))))
                                                 (y (flist-scalar-mul (car c) (vcoords0 (car l)))))
			(:instance vcoords0-vcomb-2 (j (nth-diff (car (fmat* (list c) (vcoord-mat l)))
			                                        (flist-scalar-mul (car c) (vcoords0 (car l))))))
			(:instance fmatp-fmat* (m 1) (n 1) (p (vdim)) (a (list c)) (b (vcoord-mat l))))
		  :expand ((fmatp (fmat* (list c) (vcoord-mat l)) 1 (vdim)))))))

;; support/vectors.lisp:308
;;; projects/linear/support/vectors.lisp, lines 308-312 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vcoords0-vcomb-4
  (implies (and (vlistnp l 1) (flistnp c 1))
           (equal (vcomb (car (fmat* (list c) (vcoord-mat l))) (vbasis0))
	          (vcomb c l)))
  :hints (("Goal" :use (posp-vdim) :in-theory (enable vcomb-scalar-mul vcoords0-vcomb-3)))))

;; support/vectors.lisp:325
;;; projects/linear/support/vectors.lisp, lines 325-330 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vcoords0-vcomb-5
  (implies (and (posp m) (vlistnp l m) (flistnp c m) (natp j) (< j (vdim)))
           (let ((a (vcoord-mat l)))
	     (equal (nth j (car (fmat* (list c) a)))
	            (f+ (f* (car c) (entry 0 j a)) (fdot (cdr c) (col j (cdr a)))))))
  :hints (("Goal" :use ((:instance fmat*-entry (i 0) (m 1) (n m) (p (vdim)) (a (list c)) (b (vcoord-mat l))))))))

;; support/vectors.lisp:338
;;; projects/linear/support/vectors.lisp, lines 338-353 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vcoords0-vcomb-6
  (implies (and (natp m) (> m 1) (vlistnp l m) (flistnp c m) (posp (vdim)) (natp j) (< j (vdim)))
           (let ((a (vcoord-mat l)))
	     (equal (nth j (flist-add (flist-scalar-mul (car c) (car a))
	                              (car (fmat* (list (cdr c)) (cdr a)))))
		    (f+ (f* (car c) (nth j (car a)))
		        (entry 0 j (fmat* (list (cdr c)) (cdr a)))))))
  :hints (("Goal" :in-theory (disable fmatp-vcoord-mat)
                  :expand ((FLISTNP (CAR (VCOORD-MAT L)) (VDIM)))
                  :use (fmatp-vcoord-mat
                        (:instance nth-flist-add (x (flist-scalar-mul (car c) (car (vcoord-mat l))))
                                                 (y (car (fmat* (list (cdr c)) (cdr (vcoord-mat l)))))
						 (i j) (n (vdim)))
			(:instance nth-flist-scalar-mul (i j) (n (vdim)) (c (car c)) (x (vcoords0 (car l))))
                        (:instance flist-scalar-mul (c (car c)) (x (car (vcoord-mat l))))			
			(:instance fmatp-fmat* (m 1) (n (1- m)) (p (vdim)) (a (LIST (CDR C))) (b (CDR (VCOORD-MAT L)))))))))

;; support/vectors.lisp:355
;;; projects/linear/support/vectors.lisp, lines 355-364 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vcoords0-vcomb-7
  (implies (and (natp m) (> m 1) (vlistnp l m) (flistnp c m) (posp (vdim)) (natp j) (< j (vdim)))
           (let ((a (vcoord-mat l)))
	     (equal (nth j (flist-add (flist-scalar-mul (car c) (car a))
	                              (car (fmat* (list (cdr c)) (cdr a)))))
		    (nth j (car (fmat* (list c) a))))))
  :hints (("Goal" :in-theory (disable fmatp-vcoord-mat)
                  :use (vcoords0-vcomb-5 vcoords0-vcomb-6 fmatp-vcoord-mat
                        (:instance fmat*-entry (m 1) (n (1- m)) (p (vdim))
			                       (a (list (cdr c))) (b (cdr (vcoord-mat l))) (i 0)))))))

;; support/vectors.lisp:366
;;; projects/linear/support/vectors.lisp, lines 366-385 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vcoords0-vcomb-8
  (implies (and (natp m) (> m 1) (vlistnp l m) (flistnp c m) (posp (vdim)))
           (let ((a (vcoord-mat l)))
	     (equal (flist-add (flist-scalar-mul (car c) (car a))
	                       (car (fmat* (list (cdr c)) (cdr a))))
		    (car (fmat* (list c) a)))))
  :hints (("Goal" :in-theory (disable fmatp-vcoord-mat)
                  :use (fmatp-vcoord-mat
		        (:instance vcoords0-vcomb-7 (j (nth-diff (flist-add (flist-scalar-mul (car c) (car (vcoord-mat l)))
	                                                                   (car (fmat* (list (cdr c)) (cdr (vcoord-mat l)))))
						                (car (fmat* (list c) (vcoord-mat l))))))
			(:instance nth-diff-diff (x (flist-add (flist-scalar-mul (car c) (car (vcoord-mat l)))
	                                                       (car (fmat* (list (cdr c)) (cdr (vcoord-mat l))))))
						 (y (car (fmat* (list c) (vcoord-mat l)))))
			(:instance flistnp-row (a (FMAT* (LIST C) (VCOORD-MAT L))) (i 0) (m 1) (n (vdim)))
			(:instance flistnp-flist-add (x (FLIST-SCALAR-MUL (CAR C) (CAR (VCOORD-MAT L))))
                                                     (y (CAR (FMAT* (LIST (CDR C)) (CDR (VCOORD-MAT L)))))
						     (n (vdim)))
			(:instance fmatp-fmat* (m 1) (n m) (p (vdim)) (a (list c)) (b (vcoord-mat l)))
                        (:instance fmatp-fmat* (m 1) (n (1- m)) (p (vdim)) (a (LIST (CDR C))) (b (CDR (VCOORD-MAT L)))))))))

;; support/vectors.lisp:397
;;; projects/linear/support/vectors.lisp, lines 397-413 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vcoords0-vcomb-9
  (implies (and (natp m) (> m 1) (vlistnp l m) (flistnp c m) (posp (vdim)))
           (let ((a (vcoord-mat l)))
	     (equal (vcomb (flist-add (flist-scalar-mul (car c) (car a))
	                              (car (fmat* (list (cdr c)) (cdr a))))
			   (vbasis0))
		    (v+ (v* (car c) (vcomb (car a) (vbasis0)))
		        (vcomb (car (fmat* (list (cdr c)) (cdr a))) (vbasis0))))))
  :hints (("Goal" :in-theory (e/d (vcomb-scalar-mul) (fmatp-vcoord-mat))
                  :use (fmatp-vcoord-mat
		        (:instance vcomb-add (x (flist-scalar-mul (car c) (car (vcoord-mat l))))
			                     (y (car (fmat* (list (cdr c)) (cdr (vcoord-mat l)))))
					     (n (vdim)) (l (vbasis0)))
			(:instance flistnp-row (a (FMAT* (LIST C) (VCOORD-MAT L))) (i 0) (m 1) (n (vdim)))
			(:instance flistnp-flist-scalar-mul (c (car c)) (x (car (vcoord-mat l))) (n (vdim)))
			(:instance fmatp-fmat* (m 1) (n m) (p (vdim)) (a (list c)) (b (vcoord-mat l)))
                        (:instance fmatp-fmat* (m 1) (n (1- m)) (p (vdim)) (a (LIST (CDR C))) (b (CDR (VCOORD-MAT L)))))))))

;; support/vectors.lisp:415
;;; projects/linear/support/vectors.lisp, lines 415-424 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vcoords0-vcomb-10
  (implies (and (natp m) (> m 1) (vlistnp l m) (flistnp c m) (posp (vdim)))
           (let ((a (vcoord-mat l)))
	     (implies (equal (vcomb (car (fmat* (list (cdr c)) (cdr a))) (vbasis0))
	                     (vcomb (cdr c) (cdr l)))
	              (equal (vcomb (flist-add (flist-scalar-mul (car c) (car a))
	                                       (car (fmat* (list (cdr c)) (cdr a))))
			            (vbasis0))
		             (vcomb c l)))))
  :hints (("Goal" :use (vcoords0-vcomb-9)))))

;; support/vectors.lisp:426
;;; projects/linear/support/vectors.lisp, lines 426-433 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vcoords0-vcomb-11
  (implies (and (natp m) (> m 1) (vlistnp l m) (flistnp c m) (posp (vdim)))
           (let ((a (vcoord-mat l)))
	     (implies (equal (vcomb (car (fmat* (list (cdr c)) (cdr a))) (vbasis0))
	                     (vcomb (cdr c) (cdr l)))
	              (equal (vcomb (car (fmat* (list c) a)) (vbasis0))
		             (vcomb c l)))))
  :hints (("Goal" :use (vcoords0-vcomb-10 vcoords0-vcomb-8)))))

;; support/vectors.lisp:435
;;; projects/linear/support/vectors.lisp, lines 435-440 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vcoords0-vcomb-12
  (implies (and (posp m) (vlistnp l m) (flistnp c m) (posp (vdim)))
           (equal (vcomb (car (fmat* (list c) (vcoord-mat l))) (vbasis0))
		  (vcomb c l)))
  :hints (("Subgoal *1/5" :use (vcoords0-vcomb-4 vcoords0-vcomb-11))
          ("Subgoal *1/2" :use (vcoords0-vcomb-4)))))

;; support/vectors.lisp:442
;;; projects/linear/support/vectors.lisp, lines 442-448 (wrapped in local)
(local
 (defthmd vcoords0-vcomb
  (implies (and (posp m) (vlistnp l m) (flistnp c m))
	   (equal (vcoords0 (vcomb c l))
		  (car (fmat* (list c) (vcoord-mat l)))))
  :hints (("Goal" :use (posp-vdim vcoords0-vcomb-12
			(:instance fmatp-fmat* (m 1) (n m) (p (vdim)) (a (list c)) (b (vcoord-mat l)))
                        (:instance vcoords0-unique (x (vcomb c l)) (c (car (fmat* (list c) (vcoord-mat l))))))))))

;; vectors.lisp:247
;;; ===== from projects/linear/vectors.lisp =====
;;; projects/linear/vectors.lisp, lines 247-250
(defund vindepp (l)
  (or (null l)
      (equal (row-rank (vcoord-mat l))
             (len l))))

;; vectors.lisp:252
;;; projects/linear/vectors.lisp, lines 252-253
(defund vdepp (l)
  (not (vindepp l)))

;; vectors.lisp:258
;;; projects/linear/vectors.lisp, lines 258-259
(defun vdep-coeffs (l)
  (nth (1- (len l)) (row-reduce-mat (vcoord-mat l))))

;; support/vectors.lisp:466
;;; ===== from projects/linear/support/vectors.lisp =====
;;; projects/linear/support/vectors.lisp, lines 466-466 (wrapped in local)
(local
 (in-theory (enable fmat*)))

;; support/vectors.lisp:468
;;; ===== from projects/linear/vectors.lisp =====
;;; projects/linear/vectors.lisp, lines 261-264 (wrapped in local)
(local
 (defthmd fmat*-nth
  (implies (and (fmatp a m n) (fmatp b n p) (posp m) (natp n) (natp p) (natp i) (< i m))
           (equal (car (fmat* (list (nth i a)) b))
	          (nth i (fmat* a b))))))

;; support/vectors.lisp:483
;;; ===== from projects/linear/support/vectors.lisp =====
;;; projects/linear/support/vectors.lisp, lines 483-494 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vdepp-vcomb-v0-1
  (implies (and (posp m) (vlistnp l m) (vdepp l) (posp (vdim)))
	   (let ((c (vdep-coeffs l)))
             (equal (vcoords0 (vcomb c l))
	            (nth (1- m) (row-reduce (vcoord-mat l))))))
  :hints (("Goal" :in-theory (e/d (row-ops-mat-row-reduce) (fmat* fmatp-vcoord-mat))
                  :use (fmatp-vcoord-mat
                        (:instance vcoords0-vcomb (c (vdep-coeffs l)))
			(:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))
			(:instance flistnp-row (a (row-reduce-mat (vcoord-mat l))) (n m) (i (1- m)))
			(:instance fmat*-nth (i (1- m)) (n m) (p (vdim)) (b (vcoord-mat l))
			                     (a (row-reduce-mat (vcoord-mat l)))))))))

;; support/vectors.lisp:496
;;; projects/linear/support/vectors.lisp, lines 496-508 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vdepp-vcomb-v0-2
  (implies (and (posp m) (vlistnp l m) (vdepp l) (posp (vdim)))
  	   (equal (nth (1- m) (row-reduce (vcoord-mat l)))
	          (flistn0 (vdim))))
  :hints (("Goal" :in-theory (enable vindepp vdepp)
                  :use (vdepp-vcomb-v0-1
		        (:instance num-nonzero-rows-nonzero (a (row-reduce (vcoord-mat l))) (n (vdim)) (i (1- m)))
			(:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))
			(:instance flistnp-row (a (row-reduce-mat (vcoord-mat l))) (n m) (i (1- m)))
		        (:instance flist0p-flistn0-len (x (vcoords0 (vcomb (vdep-coeffs l) l))))
			(:instance fmatp-row-reduce (a (vcoord-mat l)) (n (vdim)))
			(:instance row-rank<=m (a (vcoord-mat l)) (n (vdim)))
                        (:instance row-echelon-p-row-reduce (n (vdim)) (a (vcoord-mat l))))))))

;; support/vectors.lisp:510
;;; projects/linear/support/vectors.lisp, lines 510-515 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vdepp-vcomb-v0-3
  (implies (and (posp m) (vlistnp l m) (vdepp l) (posp (vdim)))
	   (let ((c (vdep-coeffs l)))
  	     (equal (vcoords0 (vcomb c l))
	            (flistn0 (vdim)))))
  :hints (("Goal" :use (vdepp-vcomb-v0-1 vdepp-vcomb-v0-2)))))

;; support/vectors.lisp:517
;;; projects/linear/support/vectors.lisp, lines 517-527 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vdepp-vcomb-v0-4
  (implies (and (posp m) (vlistnp l m) (vdepp l) (posp (vdim)))
	   (let ((c (vdep-coeffs l)))
	     (and (flistnp c m)
	          (not (equal c (flistn0 m))))))
  :hints (("Goal" :use ((:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))
			(:instance flistnp-row (a (row-reduce-mat (vcoord-mat l))) (n m) (i (1- m)))
			(:instance fmatp-row-reduce (a (vcoord-mat l)) (n (vdim)))
			(:instance invertiblep-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))
			(:instance invertiblep-fdet-not-zero (a (row-reduce-mat (vcoord-mat l))) (n m))
			(:instance fdet-row-0 (a (row-reduce-mat (vcoord-mat l))) (n m) (k (1- m))))))))

;; support/vectors.lisp:529
;;; projects/linear/support/vectors.lisp, lines 529-532 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vdepp-vcomb-v0-5
  (implies (and (natp n) (vlistnp b n))
           (equal (vcomb (flistn0 n) b)
	          (v0)))))

;; support/vectors.lisp:534
;;; projects/linear/support/vectors.lisp, lines 534-544 (wrapped in local)
(local
 (defthmd vdepp-vcomb-v0
  (implies (and (posp m) (vlistnp l m) (vdepp l))
	   (let ((c (vdep-coeffs l)))
	     (and (flistnp c m)
		  (not (equal c (flistn0 m)))
		  (equal (vcomb c l) (v0)))))
  :hints (("Goal" :in-theory (disable vbasis0-spans)
                  :use (vdepp-vcomb-v0-3 vdepp-vcomb-v0-4 posp-vdim
                        (:instance vdepp-vcomb-v0-5 (n (vdim)) (b (vbasis0)))
			(:instance vbasis0-spans (x (vcomb (vdep-coeffs l) l)))
		        (:instance flist0p-flistn0-len (x (vcoords0 (vcomb (vdep-coeffs l) l)))))))))

;; support/vectors.lisp:563
;;; projects/linear/support/vectors.lisp, lines 563-578 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd row-echelon-p-vindepp-1
  (implies (and (posp m)
		(posp n)
		(fmatp r m n)
		(row-echelon-p r)
		(= (row-rank r) m)
		(flistnp c m)
		(natp i)
		(< i m)
		(dlistp l)
		(sublistp l (ninit m)))
	   (equal (fdot-select l c (col (nth i (lead-inds r)) r))
	          (if (member i l) (nth i c) (f0))))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :use ((:instance nth-col-lead-inds (a r) (k (car l)))
	                        (:instance member-ninit (n m) (x (car l))))))))

;; support/vectors.lisp:580
;;; projects/linear/support/vectors.lisp, lines 580-600 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd row-echelon-p-vindepp-2
  (implies (and (posp m)
		(posp n)
		(fmatp r m n)
		(row-echelon-p r)
		(= (row-rank r) m)
		(flistnp c m)
		(natp i)
		(< i m))
	   (equal (fdot c (col (nth i (lead-inds r)) r))
	          (nth i c)))
  :hints (("Goal" :in-theory (e/d (row-rank) (member-sublist))
                  :use ((:instance len-lead-inds-num-nonzero-rows (a r))
		        (:instance sublistp-lead-inds-ninit (a r))
		        (:instance row-echelon-p-vindepp-1 (l (ninit m)))
			(:instance member-ninit (x i) (n m))
			(:instance row-reduce-row-echelon-p (a r))
			(:instance member-ninit (x (nth i (lead-inds r))))
			(:instance member-sublist (x (nth i (lead-inds r))) (l (lead-inds r)) (m (ninit n)))
                        (:instance fdot-select-ninit (n m) (x c) (y (col (nth i (lead-inds r)) r)))
			(:instance flistnp-col (a r) (j (nth i (lead-inds r)))))))))

;; support/vectors.lisp:602
;;; projects/linear/support/vectors.lisp, lines 602-615 (wrapped in local)
(local
 (defthmd entry-fmat*-row-echelon-p
  (implies (and (posp m) (posp n) (fmatp r m n)
                (row-echelon-p r) (= (row-rank r) m)
		(flistnp c m)
		(natp i)
		(< i m))
	   (equal (nth (nth i (lead-inds r)) (car (fmat* (list c) r)))
	          (nth i c)))
  :hints (("Goal" :in-theory (e/d (row-rank) (fmat*))
                  :use (row-echelon-p-vindepp-2
		        (:instance len-lead-inds-num-nonzero-rows (a r))
			(:instance row-reduce-row-echelon-p (a r))
			(:instance nth-lead-inds-bound (a r) (k i))
                        (:instance fmat*-entry (i 0) (j (nth i (lead-inds r))) (m 1) (n m) (p n) (a (list c)) (b r)))))))

;; support/vectors.lisp:619
;;; projects/linear/support/vectors.lisp, lines 619-628 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd row-echelon-p-vindepp-3
  (implies (and (posp m)
		(posp n)
		(fmatp r m n)
		(flistnp c m)
		(equal (car (fmat* (list c) r)) (flistn0 n))
		(natp j)
		(< j n))
	   (equal (nth j (car (fmat* (list c) r)))
	          (f0)))))

;; support/vectors.lisp:630
;;; projects/linear/support/vectors.lisp, lines 630-645 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd row-echelon-p-vindepp-4
  (implies (and (posp m)
		(posp n)
		(fmatp r m n)
		(row-echelon-p r)
		(= (row-rank r) m)
		(flistnp c m)
		(equal (car (fmat* (list c) r)) (flistn0 n))
		(natp i)
		(< i m))
	   (equal (nth i c) (f0)))
  :hints (("Goal" :in-theory (enable len-lead-inds-num-nonzero-rows)
                  :use (entry-fmat*-row-echelon-p
                        (:instance nth-lead-inds-bound (a r) (k i))
			(:instance row-reduce-row-echelon-p (a r))
                        (:instance row-echelon-p-vindepp-3 (j (nth i (lead-inds r)))))))))

;; support/vectors.lisp:647
;;; projects/linear/support/vectors.lisp, lines 647-658 (wrapped in local)
(local
 (defthm row-echelon-p-vindepp
  (implies (and (posp m)
		(posp n)
		(fmatp r m n)
		(row-echelon-p r)
		(= (row-rank r) m)
		(flistnp c m)
		(equal (car (fmat* (list c) r)) (flistn0 n)))
	   (equal c (flistn0 m)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance nth-diff-diff (x c) (y (flistn0 m)))
                        (:instance row-echelon-p-vindepp-4 (i (nth-diff c (flistn0 m)))))))))

;; support/vectors.lisp:668
;;; projects/linear/support/vectors.lisp, lines 668-677 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vindepp-vcomb-v0-1
  (implies (and (posp (vdim))
                (posp m)
                (vlistnp l m)
		(vindepp l)
		(flistnp c m)
		(equal (vcomb c l) (v0)))
	   (equal (car (fmat* (list c) (vcoord-mat l)))
	          (flistn0 (vdim))))
  :hints (("Goal" :use (vcoords0-vcomb vcoords0-v0)))))

;; support/vectors.lisp:679
;;; projects/linear/support/vectors.lisp, lines 679-697 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vindepp-vcomb-v0-2
  (implies (and (posp (vdim))
                (posp m)
                (vlistnp l m)
		(vindepp l)
		(flistnp c m))
	   (let* ((a (vcoord-mat l))
	          (r (row-reduce a))
		  (p (row-reduce-mat a)))
	     (equal (fmat* (fmat* (list c) (inverse-mat p)) r)
	            (fmat* (list c) (fmat* (inverse-mat p) r)))))
  :hints (("Goal" :in-theory (e/d (fmatp) (fmatp-vcoord-mat))
                  :use (fmatp-vcoord-mat
		        (:instance fmat*-assoc (m 1) (n m) (p m) (q (vdim)) (a (list c))
                                               (b (inverse-mat (row-reduce-mat (vcoord-mat l))))
					       (c (row-reduce (vcoord-mat l))))
			(:instance invertiblep-sufficient (a (row-reduce-mat (vcoord-mat l))) (n m))
			(:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))
			(:instance fmatp-row-reduce (a (vcoord-mat l)) (n (vdim))))))))

;; support/vectors.lisp:699
;;; projects/linear/support/vectors.lisp, lines 699-720 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vindepp-vcomb-v0-3
  (implies (and (posp (vdim))
                (posp m)
                (vlistnp l m)
		(vindepp l)
		(flistnp c m))
	   (let* ((a (vcoord-mat l))
	          (r (row-reduce a))
		  (p (row-reduce-mat a)))
	     (equal (fmat* (inverse-mat p) r)
	            a)))
  :hints (("Goal" :in-theory (e/d (fmatp) (fmatp-vcoord-mat))
                  :use (fmatp-vcoord-mat
		        (:instance fmat*-assoc (n m) (p m) (q (vdim))
                                               (a (inverse-mat (row-reduce-mat (vcoord-mat l))))
                                               (b (row-reduce-mat (vcoord-mat l)))
					       (c (vcoord-mat l)))
			(:instance id-fmat-left (a (vcoord-mat l)) (n (vdim)))
			(:instance invertiblep-sufficient (a (row-reduce-mat (vcoord-mat l))) (n m))
			(:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))
			(:instance row-ops-mat-row-reduce (a (vcoord-mat l)) (n (vdim)))
			(:instance fmatp-row-reduce (a (vcoord-mat l)) (n (vdim))))))))

;; support/vectors.lisp:742
;;; projects/linear/support/vectors.lisp, lines 742-754 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vindepp-vcomb-v0-4
  (implies (and (posp (vdim))
                (posp m)
                (vlistnp l m)
		(vindepp l)
		(flistnp c m)
		(equal (vcomb c l) (v0)))
	   (let* ((a (vcoord-mat l))
	          (r (row-reduce a))
		  (p (row-reduce-mat a)))
	     (equal (car (fmat* (fmat* (list c) (inverse-mat p)) r))
	            (flistn0 (vdim)))))
  :hints (("Goal" :use (vindepp-vcomb-v0-1 vindepp-vcomb-v0-2 vindepp-vcomb-v0-3)))))

;; support/vectors.lisp:756
;;; projects/linear/support/vectors.lisp, lines 756-770 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthm vindepp-vcomb-v0-5
  (implies (and (posp (vdim))
                (posp m)
                (vlistnp l m)
		(vindepp l)
		(flistnp c m)
		(equal (vcomb c l) (v0)))
	   (let* ((a (vcoord-mat l))
		  (p (row-reduce-mat a)))
	     (equal (list (car (fmat* (list c) (inverse-mat p))))
	            (fmat* (list c) (inverse-mat p)))))
  :hints (("Goal" :in-theory (disable fmatp-vcoord-mat)
                  :use (fmatp-vcoord-mat
			(:instance fmatp-fmat* (m 1) (n m) (p m) (a (list c)) (b (inverse-mat (row-reduce-mat (vcoord-mat l)))))
			(:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim))))))))

;; support/vectors.lisp:772
;;; projects/linear/support/vectors.lisp, lines 772-792 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthm vindepp-vcomb-v0-6
  (implies (and (posp (vdim))
                (posp m)
                (vlistnp l m)
		(vindepp l)
		(flistnp c m)
		(equal (vcomb c l) (v0)))
	   (let* ((a (vcoord-mat l))
		  (p (row-reduce-mat a)))
	     (equal (fmat* (list c) (inverse-mat p))
	            (list (flistn0 m)))))
  :hints (("Goal" :in-theory (e/d (row-echelon-p-row-reduce row-reduce-row-echelon-p vindepp) (fmatp-vcoord-mat fmat*))
                  :use (vindepp-vcomb-v0-4 vindepp-vcomb-v0-5 fmatp-vcoord-mat
                        (:instance row-echelon-p-vindepp
			  (c (car (fmat* (list c) (inverse-mat (row-reduce-mat (vcoord-mat l))))))
			  (r (row-reduce (vcoord-mat l)))
                          (n (vdim)))
			(:instance invertiblep-sufficient (a (row-reduce-mat (vcoord-mat l))) (n m))
			(:instance fmatp-row-reduce (a (vcoord-mat l)) (n (vdim)))
			(:instance fmatp-fmat* (m 1) (n m) (p m) (a (list c)) (b (inverse-mat (row-reduce-mat (vcoord-mat l)))))
			(:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim))))))))

;; support/vectors.lisp:794
;;; projects/linear/support/vectors.lisp, lines 794-812 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthm vindepp-vcomb-v0-7
  (implies (and (posp (vdim))
                (posp m)
                (vlistnp l m)
		(vindepp l)
		(flistnp c m)
 		(equal (vcomb c l) (v0)))
	   (let* ((a (vcoord-mat l))
		  (p (row-reduce-mat a)))
	     (equal (car (fmat* (list (flistn0 m)) p))
	            c)))
  :hints (("Goal" :in-theory (disable fmatp-vcoord-mat fmat*)
                  :use (vindepp-vcomb-v0-6 fmatp-vcoord-mat
			(:instance invertiblep-sufficient (a (row-reduce-mat (vcoord-mat l))) (n m))
			(:instance id-fmat-right (m 1) (n m) (a (list c)))
			(:instance fmat*-assoc (m 1) (n m) (p m) (q m)
			                       (a (list c)) (b (inverse-mat (row-reduce-mat (vcoord-mat l))))
					       (c (row-reduce-mat (vcoord-mat l))))
			(:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim))))))))

;; support/vectors.lisp:814
;;; projects/linear/support/vectors.lisp, lines 814-822 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthm vindepp-vcomb-v0-8
  (implies (and (posp m)
		(flistnp c m)
 		(fmatp p m m)
		(natp j)
		(< j m))
	   (equal (nth j (car (fmat* (list (flistn0 m)) p)))
		  (f0)))
  :hints (("Goal" :use ((:instance fmat*-entry (a (list (flistn0 m))) (b p) (m 1) (n m) (p m) (i 0)))))))

;; support/vectors.lisp:824
;;; projects/linear/support/vectors.lisp, lines 824-838 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthm vindepp-vcomb-v0-9
  (implies (and (posp (vdim))
                (posp m)
                (vlistnp l m)
		(vindepp l)
		(flistnp c m)
 		(equal (vcomb c l) (v0))
		(natp j)
		(< j m))
	   (equal (nth j c)
		  (f0)))
  :hints (("Goal" :in-theory (disable fmatp-vcoord-mat fmat*)
                  :use (vindepp-vcomb-v0-7 fmatp-vcoord-mat
			(:instance fmatp-row-reduce-mat (a (vcoord-mat l)) (n (vdim)))
                        (:instance vindepp-vcomb-v0-8 (p (row-reduce-mat (vcoord-mat l)))))))))

;; support/vectors.lisp:840
;;; projects/linear/support/vectors.lisp, lines 840-850 (wrapped in local)
(local
 (defthm vindepp-vcomb-v0
  (implies (and (natp m)
		(vlistnp l m)
		(vindepp l)
		(flistnp c m)
		(equal (vcomb c l) (v0)))
	   (equal c (flistn0 m)))
  :rule-classes ()
  :hints (("Goal" :use (posp-vdim
                        (:instance nth-diff-diff (x c) (y (flistn0 m)))
                        (:instance vindepp-vcomb-v0-9 (j (nth-diff c (flistn0 m)))))))))

;; support/vectors.lisp:854
;;; ===== from projects/linear/vectors.lisp =====
;;; projects/linear/vectors.lisp, lines 355-358 (wrapped in local)
(local
 (defthm vcomb-funit
  (implies (and (natp n) (natp j) (< j n) (vlistnp l n))
           (equal (vcomb (funit j n) l)
	          (nth j l)))))

;; support/vectors.lisp:859
;;; ===== from projects/linear/support/vectors.lisp =====
;;; projects/linear/support/vectors.lisp, lines 859-870 (wrapped in local)
(local
 (defthm nth-vindepp-not-v0
  (implies (and (natp m)
		(vlistnp l m)
		(vindepp l)
		(natp j)
		(< j m))
	   (not (equal (nth j l) (v0))))
  :hints (("Goal" :in-theory (enable vdepp)
                  :use (posp-vdim
		        (:instance vcomb-funit (n m))
		        (:instance vindepp-vcomb-v0 (c (funit j m)))
			(:instance nth-funit (n m) (i j)))))))

;; support/vectors.lisp:872
;;; projects/linear/support/vectors.lisp, lines 872-879 (wrapped in local)
(local
 (defthm v0-not-member-vindepp
  (implies (and (natp m)
		(vlistnp l m)
		(vindepp l))
	   (not (member (v0) l)))
  :hints (("Goal" :use (posp-vdim
                        (:instance nth-vindepp-not-v0 (j (index (v0) l)))
                        (:instance ind<len (x (v0))))))))

;; support/vectors.lisp:883
;;; projects/linear/support/vectors.lisp, lines 883-887 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vdepp-v0-1
  (implies (and (vp x) (flistnp c 1) (equal (vcomb c (list x)) (v0)) (not (equal c (flistn0 1))))
           (and (fp (car c))
	        (not (equal (car c) (f0)))
	        (equal (v* (car c) x) (v0))))))

;; support/vectors.lisp:889
;;; projects/linear/support/vectors.lisp, lines 889-894 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vdepp-v0-2
  (implies (and (vp x) (flistnp c 1) (equal (vcomb c (list x)) (v0)) (not (equal c (flistn0 1))))
           (and (fp (car c))
	        (not (equal (car c) (f0)))
	        (equal (v0) x)))
  :hints (("Goal" :use (vdepp-v0-1 (:instance v*assoc (c (f/ (car c))) (d (car c))))))))

;; support/vectors.lisp:896
;;; projects/linear/support/vectors.lisp, lines 896-900 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vdepp-v0-3
  (implies (and (vp x) (vdepp (list x)))
           (equal (v0) x))
  :hints (("Goal" :use ((:instance vdepp-vcomb-v0 (m 1) (l (list x)))
                        (:instance vdepp-v0-2 (c (vdep-coeffs (list x)))))))))

;; support/vectors.lisp:902
;;; projects/linear/support/vectors.lisp, lines 902-908 (wrapped in local)
(local
 (defthmd vdepp-v0
  (implies (vp x)
           (iff (vdepp (list x))
                (equal (v0) x)))
  :hints (("Goal" :in-theory (enable vdepp)
                  :use (vdepp-v0-3
                        (:instance v0-not-member-vindepp (m 1) (l (list x))))))))

;; support/vectors.lisp:912
;;; projects/linear/support/vectors.lisp, lines 912-917 (wrapped in local)
(local
 (defthmd vdepp-if->-vdim
  (implies (and (natp m) (> m (vdim))
		(vlistnp l m))
	   (vdepp l))
  :hints (("Goal" :in-theory (enable vdepp vindepp)
                  :use (posp-vdim (:instance row-rank<=n (a (vcoord-mat l)) (n (vdim))))))))

;; vectors.lisp:409
;;; ===== from projects/linear/vectors.lisp =====
;;; projects/linear/vectors.lisp, lines 409-413
(defund vcoords (x l)
  (if (null l)
      ()
    (let ((c (vdep-coeffs (cons x l))))
      (flist-scalar-mul (f- (f/ (car c))) (cdr c)))))

;; support/vectors.lisp:952
;;; ===== from projects/linear/support/vectors.lisp =====
;;; projects/linear/support/vectors.lisp, lines 952-959 (wrapped in local)
(local
 (defthmd vdepp-vcomb-1
  (implies (and (vlistnp l n) (posp n) (vp x) (vindepp l) (vdepp (cons x l)) (posp (vdim)))
           (let ((c (vdep-coeffs (cons x l))))
	     (and (flistnp c (1+ n))
		  (not (equal (car c) (f0)))
	          (equal (vcomb c (cons x l)) (v0)))))
  :hints (("Goal" :use ((:instance vdepp-vcomb-v0 (m (1+ n)) (l (cons x l)))
                        (:instance vindepp-vcomb-v0 (m n) (c (cdr (vdep-coeffs (cons x l))))))))))

;; support/vectors.lisp:961
;;; projects/linear/support/vectors.lisp, lines 961-967 (wrapped in local)
(local
 (defthmd hack-2
  (implies (and (vp x) (vp d) (fp c) (not (= c (f0))) (= (v+ (v* c x) d) (v0)))
           (equal (v* (f- (f/ c)) d) x))
  :hints (("Goal" :use ((:instance vdistv (c (f/ c)) (x (v* c x)) (y d))
                        (:instance v*assoc (c (f/ c)) (d c))
			(:instance v+assoc (y (v* (f/ c) d)) (z (v* (f- (f/ c)) d)))
			(:instance vdistf (c (f/ c)) (d (f- (f/ c))) (x d)))))))

;; support/vectors.lisp:969
;;; projects/linear/support/vectors.lisp, lines 969-975 (wrapped in local)
(local
 (defthmd vdepp-vcomb-2
  (implies (and (vlistnp l n) (posp n) (vp x) (vindepp l) (vdepp (cons x l)))
           (and (flistnp (vcoords x l) n)
	        (equal (vcomb (vcoords x l) l) x)))
  :hints (("Goal" :in-theory (enable vcomb-scalar-mul vcoords)
                  :use (vdepp-vcomb-1 posp-vdim
		        (:instance hack-2 (c (CAR (VDEP-COEFFS (CONS X L)))) (d (VCOMB (CDR (VDEP-COEFFS (CONS X L))) L))))))))

;; support/vectors.lisp:977
;;; projects/linear/support/vectors.lisp, lines 977-982 (wrapped in local)
(local
 (defthmd vdepp-vcomb
  (implies (and (vlistnp l n) (natp n) (vp x) (vindepp l) (vdepp (cons x l)))
           (and (flistnp (vcoords x l) n)
	        (equal (vcomb (vcoords x l) l) x)))
  :hints (("Goal" :in-theory (enable vcomb-scalar-mul vcoords)
                  :use (vdepp-v0 vdepp-vcomb-2)))))

;; vectors.lisp:477
;;; ===== from projects/linear/vectors.lisp =====
;;; projects/linear/vectors.lisp, lines 477-479
(defund vbasisp (l)
  (and (vlistnp l (vdim))
       (vindepp l)))

;; vectors.lisp:582
;;; projects/linear/vectors.lisp, lines 582-584
(defund vunspanned (l)
  (nth (car (free-inds (row-reduce (vcoord-mat l)) (vdim)))
       (vbasis0)))

;; vectors.lisp:617
;;; projects/linear/vectors.lisp, lines 617-621
(defun extend-to-basis (l)
  (declare (xargs :measure (nfix (- (vdim) (len l)))))
  (if (and (vlistnp l (len l)) (vindepp l) (< (len l) (vdim)))
      (extend-to-basis (cons (vunspanned l) l))
    l))

;; vectors.lisp:641
;;; projects/linear/vectors.lisp, lines 641-715
(encapsulate (((wp *) => *)        ;vector recognizer
              ((w+ * *) => *)      ;vector addition
	      ((w0) => *)          ;zero vector
	      ((w- *) => *)        ;additive inverse
	      ((w* * *) => *)      ;scalar multiplication
	      ((wbasis0) => *)     ;canonical basis
	      ((wcoords0 *) => *)) ;coordinates relative ro basis
  (local (defun wp (x) (fp x)))
  (local (defun w+ (x y) (f+ x y)))
  (local (defun w0 () (f0)))
  (local (defun w- (x) (f- x)))
  (local (defun w* (c x) (f* c x)))
  (local (defun wbasis0 () (list (f1))))
  (local (defun wcoords0 (x) (list x)))
  (defthm wp-w0
    (wp (w0)))
  (defthm wp-w-
    (implies (wp x) (wp (w- x))))
  ;; Vector addition:
  (defthm w+closed (implies (and (wp x) (wp y)) (wp (w+ x y))))
  (defthmd w+comm
    (implies (and (wp x) (wp y)) (equal (w+ x y) (w+ y x)))
    :hints (("Goal" :use (f+comm))))
  (defthmd w+assoc
    (implies (and (wp x) (wp y) (wp z)) (equal (w+ x (w+ y z)) (w+ (w+ x y) z)))
    :hints (("Goal" :use (f+assoc))))
  (defthm w+id
    (implies (wp x) (equal (w+ x (w0)) x)))
  (defthm w+inv
    (implies (wp x) (equal (w+ x (w- x)) (w0))))
  ;; Scalar multiplication:
  (defthm w*closed
    (implies (and (fp c) (wp x)) (wp (w* c x))))
  (defthm w*id
    (implies (wp x) (equal (w* (f1) x) x)))
  (defthmd w*assoc
    (implies (and (fp c) (fp d) (wp x)) (equal (w* c (w* d x)) (w* (f* c d) x)))
    :hints (("Goal" :use ((:instance f*assoc (x c) (y d) (z x))))))
  (defthmd wdistf
    (implies (and (fp c) (fp d) (wp x)) (equal (w+ (w* c x) (w* d x)) (w* (f+ c d) x)))
    :hints (("Goal" :use ((:instance fdist-comm (x c) (y d) (z x))))))
  (defthmd wdistw
    (implies (and (fp c) (wp x) (wp y)) (equal (w+ (w* c x) (w* c y)) (w* c (w+ x y))))
    :hints (("Goal" :use ((:instance fdist-comm (x c) (y x) (z y))))))
  ;; List of vectors:
  (defun wlistnp (x n)
    (if (zp n)
        (null x)
      (and (consp x)
           (wp (car x))
	   (wlistnp (cdr x) (1- n)))))
  ;; Linear combination of a list of vectors:
  (defun wcomb (flist wlist)
    (if (consp flist)
        (w+ (w* (car flist) (car wlist))
	    (wcomb (cdr flist) (cdr wlist)))
      (w0)))
  ;; Basis and coordinates:
  (defun wdim () (len (wbasis0)))
  (defthmd posp-wdim
    (posp (wdim)))
  (in-theory (disable (wdim) (wlistnp) (wcomb)))
  (defthm wlistnp-basis0
    (wlistnp (wbasis0) (wdim)))
  (defthm flistnp-wcoords0
    (implies (wp x) (flistnp (wcoords0 x) (wdim))))
  (defthm wbasis0-spans
    (implies (wp x)
             (equal (wcomb (wcoords0 x) (wbasis0))
		    x)))
  (defthmd wbasis0-lin-indep
    (implies (and (flistnp c (wdim))
                  (equal (wcomb c (wbasis0)) (w0)))
	     (equal (flistn0 (wdim)) c)))
  (in-theory (disable wdim)))

;; support/vectors.lisp:1601
;;; ===== from projects/linear/support/vectors.lisp =====
;;; projects/linear/support/vectors.lisp, lines 1601-1603 (wrapped in local)
(local
 (defthm w+id-comm
  (implies (wp x) (equal (w+ (w0) x) x))
  :hints (("Goal" :use ((:instance w+comm (y (w0))))))))

;; support/vectors.lisp:1605
;;; projects/linear/support/vectors.lisp, lines 1605-1607 (wrapped in local)
(local
 (defthm w+inv-comm
  (implies (wp x) (equal (w+ (w- x) x) (w0)))
  :hints (("Goal" :use ((:instance w+comm (y (w- x))))))))

;; support/vectors.lisp:1614
;;; projects/linear/support/vectors.lisp, lines 1614-1617 (wrapped in local)
(local
 (defthm c*w0
  (implies (fp c) (equal (w* c (w0)) (w0)))
  :hints (("Goal" :use ((:instance wdistw (x (w0)) (y (w0)))
			(:instance w+assoc (x (w- (w* c (w0)))) (y (w* c (w0))) (z (w* c (w0)))))))))

;; vectors.lisp:789
;;; ===== from projects/linear/vectors.lisp =====
;;; projects/linear/vectors.lisp, lines 789-793
(defun wcoord-mat (l)
  (if (consp l)
      (cons (wcoords0 (car l))
	    (wcoord-mat (cdr l)))
    ()))

;; vectors.lisp:804
;;; projects/linear/vectors.lisp, lines 804-807
(defund windepp (l)
  (or (null l)
      (equal (row-rank (wcoord-mat l))
             (len l))))

;; vectors.lisp:1010
;;; projects/linear/vectors.lisp, lines 1010-1023
(encapsulate (((lin *) => *))
  (local (defun lin (x) (declare (ignore x)) (w0)))
  (defthm lin-val
    (implies (vp x) (wp (lin x))))
  (defthm lin-v0
    (equal (lin (v0)) (w0)))
  (defthm lin-v+
    (implies (and (vp x) (vp y))
             (equal (lin (v+ x y))
	            (w+ (lin x) (lin y)))))
  (defthm lin-v*
    (implies (and (fp c) (vp x))
             (equal (lin (v* c x))
	            (w* c (lin x))))))

;; vectors.lisp:1027
;;; projects/linear/vectors.lisp, lines 1027-1031
(defun lin-list (l)
  (if (consp l)
      (cons (lin (car l))
            (lin-list (cdr l)))
    ()))

;; vectors.lisp:1051
;;; projects/linear/vectors.lisp, lines 1051-1052
(defund lin-mat ()
  (wcoord-mat (lin-list (vbasis0))))

;; vectors.lisp:1054
;;; projects/linear/vectors.lisp, lines 1054-1054
(in-theory (disable (lin-mat)))

;; vectors.lisp:1075
;;; projects/linear/vectors.lisp, lines 1075-1078
(defun-sk lin-injective-p ()
  (forall (x)
    (implies (and (vp x) (equal (lin x) (w0)))
             (equal x (v0)))))

;; vectors.lisp:1093
;;; projects/linear/vectors.lisp, lines 1093-1095
(defchoose lin-preimage x (y)
  (and (vp x)
       (equal (lin x) y)))

;; vectors.lisp:1097
;;; projects/linear/vectors.lisp, lines 1097-1102
(defun-sk lin-surjective-p ()
  (forall (y)
    (implies (wp y)
             (and (vp (lin-preimage y))
	          (equal (lin (lin-preimage y))
		         y)))))

;; vectors.lisp:1118
;;; projects/linear/vectors.lisp, lines 1118-1118
(in-theory (disable lin-injective-p lin-surjective-p))

;; vectors.lisp:1194
;;; projects/linear/vectors.lisp, lines 1194-1196
(defund lin-inv (y)
  (vcomb (car (fmat* (list (wcoords0 y)) (inverse-mat (lin-mat))))
         (vbasis0)))

;; vectors.lisp:1254
;;; projects/linear/vectors.lisp, lines 1254-1263
(encapsulate (((sp *) => *))
  (local (defun sp (x) (vp x)))
  ;; Subset:
  (defthm sp-vp (implies (sp x) (vp x)))
  ;; Zero vector:
  (defthm sp-v0 (sp (v0)))
  ;; Closure:
  (defthm sp-v- (implies (sp x) (sp (v- x))))    
  (defthm s+closed (implies (and (sp x) (sp y)) (sp (v+ x y))))  
  (defthm s*closed (implies (and (fp c) (sp x)) (sp (v* c x)))))

;; vectors.lisp:1267
;;; projects/linear/vectors.lisp, lines 1267-1272
(defun slistnp (x n)
  (if (zp n)
      (null x)
    (and (consp x)
         (sp (car x))
         (slistnp (cdr x) (1- n)))))

;; support/vectors.lisp:3606
;;; projects/linear/vectors.lisp, lines 1274-1276 (wrapped in local)
(local
 (defthm slistnp-vlistnp
  (implies (slistnp x n)
           (vlistnp x n))))

;; vectors.lisp:1278
;;; projects/linear/vectors.lisp, lines 1278-1279
(defchoose sunspanned x (l)
  (and (sp x) (vindepp (cons x l))))

;; vectors.lisp:1281
;;; projects/linear/vectors.lisp, lines 1281-1290
(defun sbasis0-aux (l)
  (declare (xargs :measure (nfix (- (vdim) (len l)))
                  :hints (("Goal" :in-theory (enable vdepp)
		                  :use ((:instance vdepp-if->-vdim
				         (m (1+ (len l)))
				         (l (cons (sunspanned l) l))))))))
  (let ((x (sunspanned l)))
    (if (and (slistnp l (len l)) (sp x) (vindepp (cons x l)))
        (sbasis0-aux (cons x l))
      l)))

;; vectors.lisp:1292
;;; projects/linear/vectors.lisp, lines 1292-1293
(defund sbasis0 ()
  (sbasis0-aux ()))

;; vectors.lisp:1295
;;; projects/linear/vectors.lisp, lines 1295-1295
(defun sdim () (len (sbasis0)))

;; support/vectors.lisp:3633
;;; ===== from projects/linear/support/vectors.lisp =====
;;; projects/linear/support/vectors.lisp, lines 3633-3636 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd slistnp-sbasis0-aux
  (implies (slistnp l (len l))
           (let ((b (sbasis0-aux l)))
	     (slistnp b (len b))))))

;; support/vectors.lisp:3638
;;; projects/linear/support/vectors.lisp, lines 3638-3641 (wrapped in local)
(local
 (defthmd slistnp-sbasis0
  (slistnp (sbasis0) (sdim))
  :hints (("Goal" :in-theory (enable sbasis0)
                  :use ((:instance slistnp-sbasis0-aux (l ())))))))

;; support/vectors.lisp:3643
;;; projects/linear/support/vectors.lisp, lines 3643-3647 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vindepp-sbasis0-aux
  (implies (and (slistnp l (len l)) (vindepp l))
           (let ((b (sbasis0-aux l)))
             (and (slistnp b (len b))
	          (vindepp b))))))

;; support/vectors.lisp:3649
;;; projects/linear/support/vectors.lisp, lines 3649-3653 (wrapped in local)
(local
 (defthm vindepp-sbasis0
  (and (slistnp (sbasis0) (sdim))
       (vindepp (sbasis0)))
  :hints (("Goal" :in-theory (enable sbasis0)
                  :use ((:instance vindepp-sbasis0-aux (l ())))))))

;; support/vectors.lisp:3665
;;; projects/linear/support/vectors.lisp, lines 3665-3668 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vdepp-cons-sbasis0-aux-1
  (implies (and (slistnp l (len l)) (vindepp l))
           (let ((x (sunspanned (sbasis0-aux l))))
	     (not (and (sp x) (vindepp (cons x (sbasis0-aux l)))))))))

;; support/vectors.lisp:3670
;;; projects/linear/support/vectors.lisp, lines 3670-3675 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd vdepp-cons-sbasis0-aux
  (implies (and (slistnp l (len l)) (vindepp l) (sp x))
           (vdepp (cons x (sbasis0-aux l))))
  :hints (("Goal" :in-theory (enable vdepp)
                  :use (vdepp-cons-sbasis0-aux-1
		        (:instance sunspanned (l (sbasis0-aux l))))))))

;; support/vectors.lisp:3677
;;; projects/linear/support/vectors.lisp, lines 3677-3681 (wrapped in local)
(local
 (defthmd vdepp-cons-sbasis0
  (implies (sp x)
           (vdepp (cons x (sbasis0))))
  :hints (("Goal" :in-theory (enable sbasis0 vdepp)
                  :use (:instance vdepp-cons-sbasis0-aux (l ()))))))

;; support/vectors.lisp:3685
;;; projects/linear/support/vectors.lisp, lines 3685-3687 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthm true-listp-sbasis0-aux
  (implies (true-listp l)
           (true-listp (sbasis0-aux l)))))

;; support/vectors.lisp:3689
;;; projects/linear/support/vectors.lisp, lines 3689-3691 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd true-listp-sbasis0
  (true-listp (sbasis0))
  :hints (("Goal" :in-theory (enable sbasis0)))))

;; support/vectors.lisp:3693
;;; projects/linear/support/vectors.lisp, lines 3693-3695 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd hack-5
  (implies (and (true-listp l) l)
           (> (len l) 0))))

;; support/vectors.lisp:3697
;;; projects/linear/support/vectors.lisp, lines 3697-3701 (wrapped in local)
(local
 (defthmd sdim-0-nil
  (iff (null (sbasis0))
       (equal (sdim) 0))           
  :hints (("Goal" :use (true-listp-sbasis0
                        (:instance hack-5 (l (sbasis0))))))))

;; support/vectors.lisp:3703
;;; projects/linear/support/vectors.lisp, lines 3703-3705 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd consp-sbasis0-1
  (implies (consp l)
           (consp (sbasis0-aux l)))))

;; support/vectors.lisp:3707
;;; projects/linear/support/vectors.lisp, lines 3707-3712 (the authors' local-defthm(d), written as (local (defthm(d) ...)))
(local
 (defthmd consp-sbasis0-2
  (iff (consp (sbasis0))
       (let ((x (sunspanned ())))
         (and (sp x) (vindepp (list x)))))
  :hints (("Goal" :in-theory (enable sbasis0)
                  :use ((:instance consp-sbasis0-1 (l (list (sunspanned ())))))))))

;; support/vectors.lisp:3721
;;; projects/linear/support/vectors.lisp, lines 3721-3725 (wrapped in local)
(local
 (defthmd not-v0-posp-sdim
  (implies (and (sp x) (not (equal x (v0))))
           (posp (sdim)))
  :hints (("Goal" :use (vdepp-v0 sdim-0-nil consp-sbasis0-2
                        (:instance sunspanned (l ())))))))

;; vectors.lisp:1297
;;; ===== from projects/linear/vectors.lisp =====
;;; projects/linear/vectors.lisp, lines 1297-1297
(in-theory (disable (slistnp) (sbasis0-aux) (sbasis0) (sdim)))

;; vectors.lisp:1336
;;; projects/linear/vectors.lisp, lines 1336-1337
(defund scoords0 (x)
  (vcoords x (sbasis0)))

;; support/vectors.lisp:3734
;;; ===== from projects/linear/support/vectors.lisp =====
;;; projects/linear/support/vectors.lisp, lines 3734-3739 (wrapped in local)
(local
 (defthm flistnp-scoords0
  (implies (sp x)
           (flistnp (scoords0 x) (sdim)))
  :hints (("Goal" :in-theory (enable sdim scoords0)
                  :use (vdepp-cons-sbasis0 vindepp-sbasis0
		        (:instance vdepp-vcomb (l (sbasis0)) (n (sdim))))))))

;; support/vectors.lisp:3741
;;; projects/linear/support/vectors.lisp, lines 3741-3747 (wrapped in local)
(local
 (defthm sbasis0-spans
  (implies (sp x)
           (equal (vcomb (scoords0 x) (sbasis0))
                  x))
  :hints (("Goal" :in-theory (enable sdim scoords0)
                  :use (vdepp-cons-sbasis0 vindepp-sbasis0 not-v0-posp-sdim
		        (:instance vdepp-vcomb (l (sbasis0)) (n (sdim))))))))

;; vectors.lisp:1376
;;; ===== from projects/linear/vectors.lisp =====
;;; projects/linear/vectors.lisp, lines 1376-1393
(encapsulate (((sbasis1) => *) ((scoords1 *) => *))
  (local (defun sbasis1 () (sbasis0)))
  (local (defun scoords1 (x) (scoords0 x)))
  (defun sdim1 () (len (sbasis1)))
  (defthmd slistnp-sbasis1
    (slistnp (sbasis1) (sdim1))
    :hints (("Goal" :in-theory (enable sdim) :use (slistnp-sbasis0))))
  (defthmd flistnp-scoords1
    (implies (and (posp (sdim)) (sp x)) (flistnp (scoords1 x) (sdim1)))
    :hints (("Goal" :use (flistnp-scoords0))))
  (defthmd sbasis1-spans
    (implies (and (posp (sdim)) (sp x))
             (equal (vcomb (scoords1 x) (sbasis1))
                    x))
    :hints (("Goal" :use (sbasis0-spans))))
  (defthm vindepp-sbasis1
    (vindepp (sbasis1))
    :hints (("Goal" :use (vindepp-sbasis0)))))

;; vectors.lisp:1441
;;; projects/linear/vectors.lisp, lines 1441-1443
(defund in-kernel-p (x)
  (and (vp x)
       (equal (lin x) (w0))))

;; vectors.lisp:1467
;;; projects/linear/vectors.lisp, lines 1467-1472
(defun klistnp (x n)
  (if (zp n)
      (null x)
    (and (consp x)
         (in-kernel-p (car x))
         (klistnp (cdr x) (1- n)))))

;; vectors.lisp:1515
;;; projects/linear/vectors.lisp, lines 1515-1522
(defund kbasis-coord (i j)
  (let* ((ar (row-reduce (transpose-mat (lin-mat))))
	 (l (lead-inds ar)))
    (if (member i l)
        (f- (entry (index i l) j ar))
      (if (= i j)
          (f1)
        (f0)))))

;; vectors.lisp:1530
;;; projects/linear/vectors.lisp, lines 1530-1534
(defun kbasis-coords-aux (i j)
  (if (posp i)
      (append (kbasis-coords-aux (1- i) j)
              (list (kbasis-coord (1- i) j)))
    ()))

;; vectors.lisp:1536
;;; projects/linear/vectors.lisp, lines 1536-1536
(defund kbasis-coords (j) (kbasis-coords-aux (vdim) j))

;; vectors.lisp:1553
;;; projects/linear/vectors.lisp, lines 1553-1557
(defun kbasis-aux (f)
  (if (consp f)
      (cons (vcomb (kbasis-coords (car f)) (vbasis0))
            (kbasis-aux (cdr f)))
    ()))

;; vectors.lisp:1559
;;; projects/linear/vectors.lisp, lines 1559-1561
(defund kbasis ()
  (let ((ar (row-reduce (transpose-mat (lin-mat)))))
    (kbasis-aux (free-inds ar (vdim)))))

;; vectors.lisp:1563
;;; projects/linear/vectors.lisp, lines 1563-1563
(in-theory (disable (kbasis)))

;; vectors.lisp:1565
;;; projects/linear/vectors.lisp, lines 1565-1565
(defund kdim () (len (kbasis)))

;; vectors.lisp:1567
;;; projects/linear/vectors.lisp, lines 1567-1567
(in-theory (disable (kdim)))

;; vectors.lisp:1675
;;; projects/linear/vectors.lisp, lines 1675-1679
(defun kcoords-aux (x f)
  (if (consp f)
      (cons (nth (car f) (vcoords0 x))
            (kcoords-aux x (cdr f)))
    ()))

;; vectors.lisp:1681
;;; projects/linear/vectors.lisp, lines 1681-1684
(defund kcoords (x)
   (let* ((ar (row-reduce (transpose-mat (lin-mat))))
          (f (free-inds ar (vdim))))
     (kcoords-aux x f)))

;; vectors.lisp:1719
;;; projects/linear/vectors.lisp, lines 1719-1721
(defund in-image-p (x)
  (let ((p (lin-preimage x)))
    (and (vp p) (equal (lin p) x))))

;; vectors.lisp:1753
;;; projects/linear/vectors.lisp, lines 1753-1753
(defun idim () (- (vdim) (kdim)))

;; vectors.lisp:1764
;;; projects/linear/vectors.lisp, lines 1764-1767
(defund extend-kbasis ()
  (if (posp (kdim))
      (extend-to-basis (kbasis))
    (vbasis0)))

;; vectors.lisp:1769
;;; projects/linear/vectors.lisp, lines 1769-1769
(in-theory (disable (extend-kbasis)))

;; vectors.lisp:1776
;;; projects/linear/vectors.lisp, lines 1776-1779
(defun firstn (n l)
  (if (zp n)
      ()
    (cons (car l) (firstn (1- n) (cdr l)))))

;; vectors.lisp:1781
;;; projects/linear/vectors.lisp, lines 1781-1782
(defund ibasis ()
  (lin-list (firstn (idim) (extend-kbasis))))

;; vectors.lisp:1784
;;; projects/linear/vectors.lisp, lines 1784-1784
(in-theory (disable (ibasis)))

;; vectors.lisp:1789
;;; projects/linear/vectors.lisp, lines 1789-1794
(defun ilistnp (x n)
  (if (zp n)
      (null x)
    (and (consp x)
         (in-image-p (car x))
         (ilistnp (cdr x) (1- n)))))

;; vectors.lisp:1828
;;; projects/linear/vectors.lisp, lines 1828-1829
(defund icoords (x)
  (firstn (idim) (vcoords (lin-preimage x) (extend-kbasis))))

