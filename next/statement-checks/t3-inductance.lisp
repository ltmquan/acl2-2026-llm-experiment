(include-book "nonstd/nsa/trig" :dir :system)
(include-book "nonstd/integrals/integrable-functions" :dir :system)
(include-book "nonstd/integrals/make-partition" :dir :system)

(defun winding-gamma () (* 2/3 (acl2-pi)))
(defun inductance-integrand (x m n)
  (* (acl2-cosine (- x (* m (winding-gamma))))
     (acl2-cosine (- x (* n (winding-gamma))))))

;; right-endpoint Riemann sum of the integrand over partition p
(defun map-inductance-integrand (p m n)
  (if (consp p)
      (cons (inductance-integrand (car p) m n)
            (map-inductance-integrand (cdr p) m n))
    nil))
(defun riemann-inductance-integrand (p m n)
  (dotprod (deltas p) (map-inductance-integrand (cdr p) m n)))

;; Form A: Riemann-sum (limit) form, no new integral operator needed
(skip-proofs
(defthm inductance-integral-riemann-form
  (implies (and (integerp m) (integerp n)
                (partitionp p)
                (equal (car p) 0)
                (equal (car (last p)) (* 2 (acl2-pi)))
                (i-small (mesh p)))
           (i-close (riemann-inductance-integrand p m n)
                    (* (acl2-pi) (acl2-cosine (* (- m n) (winding-gamma))))))))

;; Form B: as a definite integral (defun-std, standard parameters transferred)
(skip-proofs
 (defun-std int-inductance-integrand (a b m n)
   (if (and (realp a) (realp b) (< a b) (realp m) (realp n))
       (standard-part (riemann-inductance-integrand (make-small-partition a b) m n))
     0)))
(skip-proofs
(defthm inductance-integral-value
  (implies (and (integerp m) (integerp n))
           (equal (int-inductance-integrand 0 (* 2 (acl2-pi)) m n)
                  (* (acl2-pi) (acl2-cosine (* (- m n) (winding-gamma))))))))
(cw "ALL-OK~%")
