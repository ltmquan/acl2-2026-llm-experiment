; V2: admit every target under skip-proofs on top of defs (verification only).
; cert_param: (uses-acl2r)
(in-package "ACL2")
(include-book "defs")

; MAIN-1.  Authors: eq33-35-collapse-concrete, 09-nonvacuity-acl2r.lisp:38.
; Three-phase collapse lemma (eqs. 33-35) with s3 = sqrt(3):
; sum_{n=0}^{2} (2/3)(A . e^{jn 2pi/3}) e^{jn 2pi/3} = A for every real vector A.
(skip-proofs
(defthm MAIN-1
  (implies (and (realp ra) (realp ia))
           (equal (cadd (cscale (* 2/3 (dotp (cplx ra ia) (e0))) (e0))
                  (cadd (cscale (* 2/3 (dotp (cplx ra ia) (e1 (acl2-sqrt 3))))
                                (e1 (acl2-sqrt 3)))
                        (cscale (* 2/3 (dotp (cplx ra ia) (e2 (acl2-sqrt 3))))
                                (e2 (acl2-sqrt 3)))))
                  (cplx ra ia)))))

; MAIN-2.  Authors: eq-im-w-is-crossp, 05-torque-sign-correction.lisp:44
; (restated as torque-exponent-sign-is-plus, 05:53).
; Torque-exponent sign: Im(i_S i_R* e^{-j eps}) = i_S x (i_R e^{+j eps}).
(skip-proofs
(defthm MAIN-2
  (equal (imz (torque-W i-s i-r eps))
         (crossp i-s (cmul i-r (eiz eps))))))

; MAIN-3.  Authors: trinary-collapse-lemma, 06-generic-omega-collapse-acl2r.lisp:108
; (functions renamed with prefix G-).
; Generic collapse lemma: for any real pair omega with 1+omega+omega^2 = 0,
; sum_{n=0}^{2} (2/3)(A . omega^n) omega^n = A for every real pair A.
(skip-proofs
(defthm MAIN-3
  (implies (and (g-realpairp A) (g-realpairp omega)
                (equal (g-c+ (g-cplx 1 0) (g-c+ omega (g-c* omega omega)))
                       (g-cplx 0 0)))
           (equal (g-collapse-sum A omega) A))))

; MAIN-4.  Authors: trinary-collapse-CONCRETE, 06-generic-omega-collapse-acl2r.lisp:184
; (functions renamed with prefix G-; gamma written as 2/3*pi).
; The collapse lemma holds unconditionally for omega = e^{j 2pi/3}.
(skip-proofs
(defthm MAIN-4
  (implies (g-realpairp A)
           (equal (g-collapse-sum A (g-omega-real)) A))))

