(in-package "ACL2")

(include-book "arithmetic/factorial" :dir :system)
(include-book "nonstd/nsa/exp" :dir :system)
(include-book "nonstd/nsa/sqrt" :dir :system)

(defun stirling-ratio (n)
  (/ (factorial n) (* (acl2-sqrt n) (expt n n) (/ (acl2-exp n)))))
