(in-package "DM")

; Target theorems for russinoff-linear3 (Russinoff, "A Formalization of Elementary Linear
; Algebra: Part III").  Source: ACL2 master books/projects/linear/vectors.lisp (line numbers
; refer to that file).  All definitions are in defs.lisp (package "DM").

; MAIN-1: injection-dim-<= (vectors.lisp:1135) and injection-surjection-dim-= (vectors.lisp:1152).
; If the linear map lin : V -> W is injective then dim V <= dim W, and lin is then surjective
; iff dim V = dim W.
(defthm MAIN-1
  (and (implies (lin-injective-p)
                (<= (vdim) (wdim)))
       (implies (lin-injective-p)
                (iff (lin-surjective-p)
                     (equal (vdim) (wdim))))))

; MAIN-2: lin-lin-inv (vectors.lisp:1235).
; If lin is bijective, the constructive (matrix-based) inverse lin-inv is a right inverse of lin
; on W: for every y in W, (lin-inv y) is in V and lin maps it to y.
(defthm MAIN-2
  (implies (and (lin-injective-p)
                (lin-surjective-p)
                (wp y))
           (let ((x (lin-inv y)))
             (and (vp x)
                  (equal (lin x) y)))))

; MAIN-3: vbasisp-extend-to-basis (vectors.lisp:625).
; Every nonempty linearly independent list of vectors is extended by extend-to-basis to a basis of V.
(defthm MAIN-3
  (implies (and (vlistnp l n) (posp n) (vindepp l))
           (vbasisp (extend-to-basis l))))

; MAIN-4: sdim-well-defined (vectors.lisp:1426).
; The dimension of a subspace S is well defined: any linearly independent spanning list sbasis1 of S
; has the same length as the constructed basis sbasis0.
(defthm MAIN-4
  (= (sdim1) (sdim)))

; MAIN-5: klistnp-kbasis (vectors.lisp:1608), vindepp-kbasis (vectors.lisp:1670),
; flistnp-kcoords (vectors.lisp:1688), kbasis-spans (vectors.lisp:1710).
; kbasis is a list of kdim kernel vectors, linearly independent, and every kernel vector x is the
; linear combination of kbasis with the kdim coordinates (kcoords x): kbasis is a basis of the kernel.
(defthm MAIN-5
  (and (klistnp (kbasis) (kdim))
       (vindepp (kbasis))
       (implies (in-kernel-p x)
                (flistnp (kcoords x) (kdim)))
       (implies (in-kernel-p x)
                (equal (vcomb (kcoords x) (kbasis)) x))))

; MAIN-6: ilistnp-ibasis (vectors.lisp:1800), ibasis-lin-indep (vectors.lisp:1823),
; flistnp-icoords (vectors.lisp:1831), ibasis-spans (vectors.lisp:1866).
; ibasis is a list of idim = vdim - kdim image vectors, linearly independent in W, and every image
; vector x is the linear combination of ibasis with the idim coordinates (icoords x): ibasis is a
; basis of the image (rank-nullity).
(defthm MAIN-6
  (and (ilistnp (ibasis) (idim))
       (windepp (ibasis))
       (implies (in-image-p x)
                (flistnp (icoords x) (idim)))
       (implies (in-image-p x)
                (equal (wcomb (icoords x) (ibasis)) x))))
