(in-package "ACL2")
(include-book "nonstd/nsa/nsa" :dir :system)
(defthm t2 (equal (+ x 0) (fix x)) :rule-classes nil)
