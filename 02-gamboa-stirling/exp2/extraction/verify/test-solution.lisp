(in-package "ACL2")

(include-book "defs")

; Only for target matching: each proof fails immediately (:by nil).

(defthm MAIN-1
  (implies (and (natp n)
                (i-large n))
           (i-close (/ (factorial n)
                       (* (acl2-sqrt (* 2 (acl2-pi)))
                          (expt n n)
                          (/ (acl2-exp n))
                          (acl2-sqrt n)))
                    1))
  :hints (("Goal" :by nil)))

(defthm MAIN-2
  (implies (and (posp n)
                (i-large n))
           (i-close (acl2-ln (factorial n))
                    (+ (acl2-ln (expt n n))
                       (- n)
                       (acl2-ln (acl2-sqrt (* 2 (acl2-pi) n))))))
  :hints (("Goal" :by nil)))

(defthm MAIN-3
  (implies (and (natp n)
                (i-large n))
           (equal (standard-part (wallis-product n))
                  (/ (acl2-pi) 2)))
  :hints (("Goal" :by nil)))
