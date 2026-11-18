(defthm inductance-integral-riemann-form
  (implies (and (integerp m) (integerp n)
                (partitionp p)
                (equal (car p) 0)
                (equal (car (last p)) (* 2 (acl2-pi)))
                (i-small (mesh p)))
           (i-close (riemann-inductance-integrand p m n)
                    (* (acl2-pi) (acl2-cosine (* (- m n) (winding-gamma)))))))

(defthm inductance-integral-value
  (implies (and (integerp m) (integerp n))
           (equal (int-inductance-integrand 0 (* 2 (acl2-pi)) m n)
                  (* (acl2-pi) (acl2-cosine (* (- m n) (winding-gamma)))))))
