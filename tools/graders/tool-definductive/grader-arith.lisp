; Arithmetic lemma for grade-r3-paper (FILL for the Section 5.2 flag theorem).
; arithmetic-3 is included locally, so that its names (e.g. TREE) do not clash
; with the paper's predicates.
(in-package "ACL2")
(local (include-book "arithmetic-3/top" :dir :system))
(defthmd grader-arith-lemma
  (implies (and (integerp x)
                (not (integerp (* 1/2 x))))
           (integerp (+ -1/2 (* 1/2 x)))))
