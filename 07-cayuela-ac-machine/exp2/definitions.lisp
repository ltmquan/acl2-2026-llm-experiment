; Given definitions for: P. O. Cayuela, "Mechanized Verification of
; Complex-to-Vector Derivations in a Three-Phase AC Machine Model"
; (ACL2 Workshop 2026).  Logic: ACL2(r) (certify with saved_acl2r).
;
; Part A (targets MAIN-1, MAIN-2) is copied verbatim from the authors'
; books 00-complex-vectors.lisp, 01-euler-identities.lisp,
; 02-roots-of-unity.lisp and 05-torque-sign-correction.lisp.
;
; Part B (targets MAIN-3, MAIN-4) is copied from the authors'
; 06-generic-omega-collapse-acl2r.lisp, which re-declares CPLXP, RE,
; CPLX, CSCALE with the same names as Part A.  So that both parts can
; live in one world, EVERY function of Part B carries the prefix G-
; (g-cplxp g-re g-im g-cplx g-realpairp g-c+ g-c* g-cscale g-vdot
; g-omega-pow g-collapse-sum g-gamma-val g-omega-real); apart from this
; renaming the definitions are verbatim, except G-GAMMA-VAL (see README).

; cert_param: (uses-acl2r)

(in-package "ACL2")
;;; ===== from cayuela-ac-machine/00-complex-vectors.lisp =====
;;; cayuela-ac-machine/00-complex-vectors.lisp, lines 22-22
(include-book "arithmetic-5/top" :dir :system)
;;; ===== from cayuela-ac-machine/06-generic-omega-collapse-acl2r.lisp =====
;;; cayuela-ac-machine/06-generic-omega-collapse-acl2r.lisp, lines 25-25
(include-book "nonstd/nsa/trig" :dir :system)

; =====================================================================
; Part A.  00-complex-vectors.lisp
; =====================================================================

; A complex number / 2D vector is represented as (cons re im).
; Cross-product convention: A x B := Im(A B*) = b*c - a*d.
;;; ===== from cayuela-ac-machine/00-complex-vectors.lisp =====
;;; cayuela-ac-machine/00-complex-vectors.lisp, lines 27-29
(defun cplxp (z)
  (declare (xargs :guard t))
  (and (consp z) (acl2-numberp (car z)) (acl2-numberp (cdr z))))
;;; cayuela-ac-machine/00-complex-vectors.lisp, lines 30-32
(defun cplx (re im)
  (declare (xargs :guard (and (acl2-numberp re) (acl2-numberp im))))
  (cons re im))
;;; cayuela-ac-machine/00-complex-vectors.lisp, lines 33-33
(defun re (z) (declare (xargs :guard (consp z))) (car z))
;;; cayuela-ac-machine/00-complex-vectors.lisp, lines 34-34
(defun imz (z) (declare (xargs :guard (consp z))) (cdr z))
;;; cayuela-ac-machine/00-complex-vectors.lisp, lines 35-37
(defun cconj (z)
  (declare (xargs :guard (cplxp z)))
  (cplx (re z) (- (imz z))))
;;; cayuela-ac-machine/00-complex-vectors.lisp, lines 38-40
(defun cadd (z w)
  (declare (xargs :guard (and (cplxp z) (cplxp w))))
  (cplx (+ (re z) (re w)) (+ (imz z) (imz w))))
;;; cayuela-ac-machine/00-complex-vectors.lisp, lines 44-46
(defun cscale (k z)
  (declare (xargs :guard (and (acl2-numberp k) (cplxp z))))
  (cplx (* k (re z)) (* k (imz z))))
;;; cayuela-ac-machine/00-complex-vectors.lisp, lines 47-50
(defun cmul (z w)
  (declare (xargs :guard (and (cplxp z) (cplxp w))))
  (cplx (- (* (re z) (re w)) (* (imz z) (imz w)))
        (+ (* (re z) (imz w)) (* (imz z) (re w)))))
;;; cayuela-ac-machine/00-complex-vectors.lisp, lines 51-53
(defun dotp (z w)
  (declare (xargs :guard (and (cplxp z) (cplxp w))))
  (+ (* (re z) (re w)) (* (imz z) (imz w))))
;;; cayuela-ac-machine/00-complex-vectors.lisp, lines 54-56
(defun crossp (z w)
  (declare (xargs :guard (and (cplxp z) (cplxp w))))
  (- (* (imz z) (re w)) (* (re z) (imz w))))

; =====================================================================
; Part A.  01-euler-identities.lisp
; =====================================================================

; cosine/sine are introduced by ENCAPSULATE as functions CONSTRAINED to
; satisfy standard trigonometric facts (the constraints below are part
; of the authors' definition).
;;; ===== from cayuela-ac-machine/01-euler-identities.lisp =====
;;; cayuela-ac-machine/01-euler-identities.lisp, lines 24-41
(encapsulate
 (((cosine *) => *) ((sine *) => *))
 (local (defun cosine (x) (declare (ignore x)) 1))
 (local (defun sine (x) (declare (ignore x)) 0))
 (defthm pythagorean-cos-sin
   (equal (+ (* (cosine x) (cosine x)) (* (sine x) (sine x))) 1))
 (defthm cosine-even
   (equal (cosine (- x)) (cosine x)))
 (defthm sine-odd
   (equal (sine (- x)) (- (sine x))))
 (defthm cosine-difference
   (equal (cosine (- x y))
          (+ (* (cosine x) (cosine y)) (* (sine x) (sine y)))))
 (defthm sine-difference
   (equal (sine (- x y))
          (- (* (sine x) (cosine y)) (* (cosine x) (sine y)))))
 (defthm acl2-numberp-cosine (acl2-numberp (cosine x)))
 (defthm acl2-numberp-sine (acl2-numberp (sine x))))

; e^{j theta} := cplx(cos theta, sin theta)
;;; cayuela-ac-machine/01-euler-identities.lisp, lines 44-46
(defun eiz (theta)
  (declare (xargs :guard t))
  (cplx (cosine theta) (sine theta)))

; =====================================================================
; Part A.  02-roots-of-unity.lisp
; =====================================================================

; The three cube roots of unity e^{j n gamma}, gamma = 2*pi/3, n=0,1,2,
; with s3 standing for sqrt(3).
;;; ===== from cayuela-ac-machine/02-roots-of-unity.lisp =====
;;; cayuela-ac-machine/02-roots-of-unity.lisp, lines 22-22
(defun e0 () (declare (xargs :guard t)) (cplx 1 0))
;;; cayuela-ac-machine/02-roots-of-unity.lisp, lines 23-25
(defun e1 (s3)
  (declare (xargs :guard (acl2-numberp s3)))
  (cplx (- (/ 1 2)) (/ s3 2)))
;;; cayuela-ac-machine/02-roots-of-unity.lisp, lines 26-28
(defun e2 (s3)
  (declare (xargs :guard (acl2-numberp s3)))
  (cplx (- (/ 1 2)) (- (/ s3 2))))

; =====================================================================
; Part A.  05-torque-sign-correction.lisp
; =====================================================================

; W = i_S * conj(i_R * E),  E = e^{j eps}  =>  W = i_S i_R* e^{-j eps}
;;; ===== from cayuela-ac-machine/05-torque-sign-correction.lisp =====
;;; cayuela-ac-machine/05-torque-sign-correction.lisp, lines 24-26
(defun torque-W (i-s i-r eps)
  (declare (xargs :guard (and (cplxp i-s) (cplxp i-r))))
  (cmul i-s (cconj (cmul i-r (eiz eps)))))

; =====================================================================
; Part B.  06-generic-omega-collapse-acl2r.lisp  (all names prefixed G-)
; =====================================================================

;;; ===== from cayuela-ac-machine/06-generic-omega-collapse-acl2r.lisp =====
;;; cayuela-ac-machine/06-generic-omega-collapse-acl2r.lisp, lines 30-32 (renamed with prefix G-)
(defun g-cplxp (u)
  (declare (xargs :guard t))
  (and (consp u) (acl2-numberp (car u)) (acl2-numberp (cdr u))))
;;; cayuela-ac-machine/06-generic-omega-collapse-acl2r.lisp, lines 33-33 (renamed with prefix G-)
(defun g-re (u) (declare (xargs :guard (consp u))) (car u))
;;; cayuela-ac-machine/06-generic-omega-collapse-acl2r.lisp, lines 34-34 (renamed with prefix G-)
(defun g-im (u) (declare (xargs :guard (consp u))) (cdr u))
;;; cayuela-ac-machine/06-generic-omega-collapse-acl2r.lisp, lines 35-37 (renamed with prefix G-)
(defun g-cplx (a b)
  (declare (xargs :guard (and (acl2-numberp a) (acl2-numberp b))))
  (cons a b))

;;; cayuela-ac-machine/06-generic-omega-collapse-acl2r.lisp, lines 39-41 (renamed with prefix G-)
(defun g-realpairp (u)
  (declare (xargs :guard t))
  (and (consp u) (realp (g-re u)) (realp (g-im u))))

;;; cayuela-ac-machine/06-generic-omega-collapse-acl2r.lisp, lines 43-45 (renamed with prefix G-)
(defun g-c+ (u v)
  (declare (xargs :guard (and (g-cplxp u) (g-cplxp v))))
  (g-cplx (+ (g-re u) (g-re v)) (+ (g-im u) (g-im v))))
;;; cayuela-ac-machine/06-generic-omega-collapse-acl2r.lisp, lines 49-51 (renamed with prefix G-)
(defun g-cscale (k u)
  (declare (xargs :guard (and (acl2-numberp k) (g-cplxp u))))
  (g-cplx (* k (g-re u)) (* k (g-im u))))

;;; cayuela-ac-machine/06-generic-omega-collapse-acl2r.lisp, lines 53-56 (renamed with prefix G-)
(defun g-c* (u v)
  (declare (xargs :guard (and (g-cplxp u) (g-cplxp v))))
  (g-cplx (- (* (g-re u) (g-re v)) (* (g-im u) (g-im v)))
          (+ (* (g-re u) (g-im v)) (* (g-im u) (g-re v)))))

;;; cayuela-ac-machine/06-generic-omega-collapse-acl2r.lisp, lines 58-60 (renamed with prefix G-)
(defun g-vdot (u v)
  (declare (xargs :guard (and (g-cplxp u) (g-cplxp v))))
  (+ (* (g-re u) (g-re v)) (* (g-im u) (g-im v))))

; omega^n
;;; cayuela-ac-machine/06-generic-omega-collapse-acl2r.lisp, lines 66-69 (renamed with prefix G-)
(defun g-omega-pow (omega n)
  (declare (xargs :guard (and (g-cplxp omega) (natp n))
                  :verify-guards nil))
  (if (zp n) (g-cplx 1 0) (g-c* omega (g-omega-pow omega (1- n)))))

;;; cayuela-ac-machine/06-generic-omega-collapse-acl2r.lisp: the authors' cplxp-of-omega-pow, renamed with prefix G- and made local
(local
 (defthm g-cplxp-of-g-omega-pow
   (implies (g-cplxp omega) (g-cplxp (g-omega-pow omega n)))))

;;; cayuela-ac-machine/06-generic-omega-collapse-acl2r.lisp, lines 74-74 (renamed with prefix G-)
(verify-guards g-omega-pow)

; sum_{n=0}^{2} (2/3)(A . omega^n) omega^n
;;; cayuela-ac-machine/06-generic-omega-collapse-acl2r.lisp, lines 76-80 (renamed with prefix G-)
(defun g-collapse-sum (A omega)
  (declare (xargs :guard (and (g-cplxp A) (g-cplxp omega))))
  (g-c+ (g-cscale (* 2/3 (g-vdot A (g-omega-pow omega 0))) (g-omega-pow omega 0))
        (g-c+ (g-cscale (* 2/3 (g-vdot A (g-omega-pow omega 1))) (g-omega-pow omega 1))
              (g-cscale (* 2/3 (g-vdot A (g-omega-pow omega 2))) (g-omega-pow omega 2)))))

; gamma = 2*pi/3
;;; cayuela-ac-machine/06-generic-omega-collapse-acl2r.lisp, lines 143-143 (body written neutrally; see README)
(defun g-gamma-val () (* 2/3 (acl2-pi)))

; omega = e^{j 2pi/3}
;;; cayuela-ac-machine/06-generic-omega-collapse-acl2r.lisp, lines 157-157 (renamed with prefix G-)
(defun g-omega-real () (g-cplx (acl2-cosine (g-gamma-val)) (acl2-sine (g-gamma-val))))
