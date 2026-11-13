; V3 (part 1): MAIN-1 and MAIN-2 from the authors' development.
; Includes the authors' books 00-05 + 09 (via 09-nonvacuity-acl2r), then
; includes defs.lisp.  Every Part-A event of defs.lisp is then REDUNDANT with
; the authors' identical event (else the include-book would fail), and the
; Part-B (G-) functions are new names.  The targets are then proved by :use
; of the authors' theorems.
; cert_param: (uses-acl2r)
(in-package "ACL2")
(include-book "authors/09-nonvacuity-acl2r")
(include-book "defs")

(defthm MAIN-1
  (implies (and (realp ra) (realp ia))
           (equal (cadd (cscale (* 2/3 (dotp (cplx ra ia) (e0))) (e0))
                  (cadd (cscale (* 2/3 (dotp (cplx ra ia) (e1 (acl2-sqrt 3))))
                                (e1 (acl2-sqrt 3)))
                        (cscale (* 2/3 (dotp (cplx ra ia) (e2 (acl2-sqrt 3))))
                                (e2 (acl2-sqrt 3)))))
                  (cplx ra ia)))
  :hints (("Goal" :use eq33-35-collapse-concrete :in-theory nil)))

(defthm MAIN-2
  (equal (imz (torque-W i-s i-r eps))
         (crossp i-s (cmul i-r (eiz eps))))
  :hints (("Goal" :use eq-im-w-is-crossp :in-theory nil)))
