;; tests.lisp -- tests for DEF-FTC-INTEGRAL (certify with cert.pl --acl2 acl2r)

(in-package "ACL2")

(include-book "def-ftc-integral")
(include-book "std/testing/must-fail" :dir :system)

;; Concrete endpoint checks only need the interval predicates to evaluate.
(local (in-theory (enable interval-definition-theory)))

;;; ------------------------------------------------------------------
;;; (a) f(x) = x^2, F(x) = x^3/3 on the whole real line; no theorems.
;;; ------------------------------------------------------------------

(def-ftc-integral sq
  :integrand      (lambda (x) (* x x))
  :antiderivative (lambda (x) (/ (* x x x) 3))
  :domain         (interval nil nil))

(defthm int-sq-0-3
  (equal (int-sq 0 3) 9)
  :hints (("Goal" :use ((:instance int-sq-ftc (a 0) (b 3)))
           :in-theory (disable int-sq))))

(defthm int-sq--1-2
  (equal (int-sq -1 2) 3)
  :hints (("Goal" :use ((:instance int-sq-ftc (a -1) (b 2)))
           :in-theory (disable int-sq))))

;; reversed bounds
(defthm int-sq-3-0
  (equal (int-sq 3 0) -9)
  :hints (("Goal" :use ((:instance int-sq-ftc (a 3) (b 0)))
           :in-theory (disable int-sq))))

;;; ------------------------------------------------------------------
;;; (b) f = acl2-cosine, F = acl2-sine on the real line; no theorems.
;;; ------------------------------------------------------------------

(def-ftc-integral cosine
  :integrand      acl2-cosine
  :antiderivative acl2-sine
  :domain         (interval nil nil))

(defthm int-cosine-0-1
  (equal (int-cosine 0 1) (acl2-sine 1))
  :hints (("Goal" :use ((:instance int-cosine-ftc (a 0) (b 1)))
           :in-theory (disable int-cosine))))

(defthm int-cosine-0-pi
  (equal (int-cosine 0 (acl2-pi)) 0)
  :hints (("Goal" :use ((:instance int-cosine-ftc (a 0) (b (acl2-pi))))
           :in-theory (disable int-cosine))))

;;; ------------------------------------------------------------------
;;; (c) f(x) = 1/x^2, F(x) = -1/x on [1, oo); no theorems.
;;; ------------------------------------------------------------------

(def-ftc-integral invsq
  :integrand      (lambda (x) (/ (* x x)))
  :antiderivative (lambda (x) (- (/ x)))
  :domain         (interval 1 nil))

(defthm int-invsq-1-2
  (equal (int-invsq 1 2) 1/2)
  :hints (("Goal" :use ((:instance int-invsq-ftc (a 1) (b 2)))
           :in-theory (disable int-invsq))))

(defthm int-invsq-2-4
  (equal (int-invsq 2 4) 1/4)
  :hints (("Goal" :use ((:instance int-invsq-ftc (a 2) (b 4)))
           :in-theory (disable int-invsq))))

;;; ------------------------------------------------------------------
;;; (d) f = acl2-ln, F(x) = x ln x - x on [1, oo); theorems supplied.
;;; ------------------------------------------------------------------

(encapsulate
  ()
  (local (defderivative xlnx-raw-derivative (- (* x (acl2-ln x)) x)))

  (defthm xlnx-derivative
    (implies (and (standardp x)
                  (inside-interval-p x (interval 1 nil))
                  (inside-interval-p x1 (interval 1 nil))
                  (i-close x x1)
                  (not (= x x1)))
             (i-close (/ (- (- (* x (acl2-ln x)) x)
                            (- (* x1 (acl2-ln x1)) x1))
                         (- x x1))
                      (acl2-ln x)))
    :hints (("Goal" :use ((:instance xlnx-raw-derivative (y x1)))))))

(defthm ln-continuous-on-1-oo
  (implies (and (standardp x)
                (inside-interval-p x (interval 1 nil))
                (i-close x x1)
                (inside-interval-p x1 (interval 1 nil)))
           (i-close (acl2-ln x) (acl2-ln x1)))
  :hints (("Goal" :use ((:instance elem-acl2-ln-continuous (y x1))))))

(def-ftc-integral xlnx
  :integrand      acl2-ln
  :antiderivative (lambda (x) (- (* x (acl2-ln x)) x))
  :domain         (interval 1 nil)
  :derivative-thm xlnx-derivative
  :continuity-thm ln-continuous-on-1-oo)

(local
 (defthm ln-1
   (equal (acl2-ln 1) 0)
   :hints (("Goal" :use ((:instance uniqueness-of-ln (y 1) (x 0)))))))

(defthm int-xlnx-1-2
  (equal (int-xlnx 1 2) (- (* 2 (acl2-ln 2)) 1))
  :hints (("Goal" :use ((:instance int-xlnx-ftc (a 1) (b 2)))
           :in-theory (disable int-xlnx))))

;; The same integral, with the obligations proved automatically.
(def-ftc-integral ln
  :integrand      acl2-ln
  :antiderivative (lambda (x) (- (* x (acl2-ln x)) x))
  :domain         (interval 1 nil))

(defthm int-ln-1-2
  (equal (int-ln 1 2) (- (* 2 (acl2-ln 2)) 1))
  :hints (("Goal" :use ((:instance int-ln-ftc (a 1) (b 2)))
           :in-theory (disable int-ln))))

;;; ------------------------------------------------------------------
;;; (e) A wrong antiderivative must be rejected.
;;; ------------------------------------------------------------------

(must-fail
 (def-ftc-integral bad
   :integrand      (lambda (x) (* x x))
   :antiderivative (lambda (x) (* x x))
   :domain         (interval nil nil)))

;;; ------------------------------------------------------------------
;;; Further tests
;;; ------------------------------------------------------------------

;; Function symbols for both, on a bounded closed interval.
(defun poly3 (x) (+ (* 3 x x) (* 2 x) 1))
(defun poly3-anti (x) (+ (* x x x) (* x x) x))

(def-ftc-integral poly3
  :integrand      poly3
  :antiderivative poly3-anti
  :domain         (interval 0 10))

(defthm int-poly3-0-2
  (equal (int-poly3 0 2) 14)
  :hints (("Goal" :use ((:instance int-poly3-ftc (a 0) (b 2)))
           :in-theory (disable int-poly3))))

;; Wrong antiderivative (off by a factor) for a transcendental integrand.
(must-fail
 (def-ftc-integral bad-cos
   :integrand      acl2-cosine
   :antiderivative (lambda (x) (* 2 (acl2-sine x)))
   :domain         (interval nil nil)))

;; Wrong supplied derivative theorem.
(must-fail
 (def-ftc-integral bad-thm
   :integrand      (lambda (x) (* x x))
   :antiderivative (lambda (x) (/ (* x x x) 3))
   :domain         (interval nil nil)
   :derivative-thm int-sq-0-3))

;; Degenerate domain.
(must-fail
 (def-ftc-integral bad-dom
   :integrand      (lambda (x) (* x x))
   :antiderivative (lambda (x) (/ (* x x x) 3))
   :domain         (interval 1 1)))

;; :HINTS are passed to the macro's own obligations: here the antiderivative
;; is a disabled function, so its realness and the identification of the
;; computed derivative need it enabled.
(defun my-sq (x) (* x x))
(in-theory (disable my-sq))

(must-fail
 (def-ftc-integral mysq-nohints
   :integrand      (lambda (x) (* 2 x))
   :antiderivative my-sq
   :domain         (interval nil nil)))

(def-ftc-integral mysq
  :integrand      (lambda (x) (* 2 x))
  :antiderivative my-sq
  :domain         (interval nil nil)
  :hints          (("Goal" :in-theory (enable my-sq))))

(defthm int-mysq-1-3
  (equal (int-mysq 1 3) 8)
  :hints (("Goal" :use ((:instance int-mysq-ftc (a 1) (b 3)))
           :in-theory (e/d (my-sq) (int-mysq)))))

;; A supplied derivative theorem with other variable names, for a lambda
;; integrand whose formal is not X.
(encapsulate
  ()
  (local (defderivative cube-raw (* x x x)))
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm cube-deriv
    (implies (and (standardp u)
                  (inside-interval-p u (interval 0 nil))
                  (inside-interval-p v (interval 0 nil))
                  (i-close u v)
                  (not (= u v)))
             (i-close (/ (- (* u u u) (* v v v)) (- u v)) (* 3 u u)))
    :hints (("Goal" :use ((:instance cube-raw (x u) (y v)))))))

(def-ftc-integral cube
  :integrand      (lambda (z) (* 3 z z))
  :antiderivative (lambda (z) (* z z z))
  :domain         (interval 0 nil)
  :derivative-thm cube-deriv)

(defthm int-cube-0-2
  (equal (int-cube 0 2) 8)
  :hints (("Goal" :use ((:instance int-cube-ftc (a 0) (b 2)))
           :in-theory (disable int-cube))))

;; Square root, arctangent, product rule and chain rule, all automatic.
(def-ftc-integral half-inv-sqrt
  :integrand      (lambda (x) (/ 1/2 (acl2-sqrt x)))
  :antiderivative acl2-sqrt
  :domain         (interval 1 nil))

(def-ftc-integral atan-deriv
  :integrand      (lambda (x) (/ (+ 1 (* x x))))
  :antiderivative acl2-atan
  :domain         (interval nil nil))

(def-ftc-integral x-sin
  :integrand      (lambda (x) (+ (acl2-sine x) (* x (acl2-cosine x))))
  :antiderivative (lambda (x) (* x (acl2-sine x)))
  :domain         (interval nil nil))

(def-ftc-integral cos-2x
  :integrand      (lambda (x) (* 2 (acl2-cosine (* 2 x))))
  :antiderivative (lambda (x) (acl2-sine (* 2 x)))
  :domain         (interval nil nil))

(defthm int-cos-2x-0-0
  (equal (int-cos-2x 0 0) 0)
  :hints (("Goal" :use ((:instance int-cos-2x-ftc (a 0) (b 0)))
           :in-theory (disable int-cos-2x))))
