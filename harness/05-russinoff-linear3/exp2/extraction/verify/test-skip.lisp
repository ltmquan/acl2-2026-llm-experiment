(in-package "DM")
; V2: every target is admissible (well-formed) over defs.lisp.  skip-proofs is used ONLY here.
(include-book "defs")

(skip-proofs
(defthm MAIN-1
  (and (implies (lin-injective-p)
                (<= (vdim) (wdim)))
       (implies (lin-injective-p)
                (iff (lin-surjective-p)
                     (equal (vdim) (wdim)))))))

(skip-proofs
(defthm MAIN-2
  (implies (and (lin-injective-p)
                (lin-surjective-p)
                (wp y))
           (let ((x (lin-inv y)))
             (and (vp x)
                  (equal (lin x) y))))))

(skip-proofs
(defthm MAIN-3
  (implies (and (vlistnp l n) (posp n) (vindepp l))
           (vbasisp (extend-to-basis l)))))

(skip-proofs
(defthm MAIN-4
  (= (sdim1) (sdim))))

(skip-proofs
(defthm MAIN-5
  (and (klistnp (kbasis) (kdim))
       (vindepp (kbasis))
       (implies (in-kernel-p x)
                (flistnp (kcoords x) (kdim)))
       (implies (in-kernel-p x)
                (equal (vcomb (kcoords x) (kbasis)) x)))))

(skip-proofs
(defthm MAIN-6
  (and (ilistnp (ibasis) (idim))
       (windepp (ibasis))
       (implies (in-image-p x)
                (flistnp (icoords x) (idim)))
       (implies (in-image-p x)
                (equal (wcomb (icoords x) (ibasis)) x)))))
