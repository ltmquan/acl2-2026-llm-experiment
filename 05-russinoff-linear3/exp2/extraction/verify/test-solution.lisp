(in-package "DM")

; Test solution for check-exp2.py (run against the MASTER image, see README): include defs,
; then the authors' master book (all Part III definitions must be redundant with defs.lisp),
; then prove the targets by :use of the authors' theorems.
(include-book "defs")
(include-book "projects/linear/vectors" :dir :system)

(defthm MAIN-1
  (and (implies (lin-injective-p)
                (<= (vdim) (wdim)))
       (implies (lin-injective-p)
                (iff (lin-surjective-p)
                     (equal (vdim) (wdim)))))
  :hints (("Goal" :use (injection-dim-<= injection-surjection-dim-=))))

(defthm MAIN-2
  (implies (and (lin-injective-p)
                (lin-surjective-p)
                (wp y))
           (let ((x (lin-inv y)))
             (and (vp x)
                  (equal (lin x) y))))
  :hints (("Goal" :use (lin-lin-inv))))

(defthm MAIN-3
  (implies (and (vlistnp l n) (posp n) (vindepp l))
           (vbasisp (extend-to-basis l)))
  :hints (("Goal" :use (vbasisp-extend-to-basis))))

(defthm MAIN-4
  (= (sdim1) (sdim))
  :hints (("Goal" :use (sdim-well-defined))))

(defthm MAIN-5
  (and (klistnp (kbasis) (kdim))
       (vindepp (kbasis))
       (implies (in-kernel-p x)
                (flistnp (kcoords x) (kdim)))
       (implies (in-kernel-p x)
                (equal (vcomb (kcoords x) (kbasis)) x)))
  :hints (("Goal" :use (klistnp-kbasis vindepp-kbasis flistnp-kcoords kbasis-spans))))

(defthm MAIN-6
  (and (ilistnp (ibasis) (idim))
       (windepp (ibasis))
       (implies (in-image-p x)
                (flistnp (icoords x) (idim)))
       (implies (in-image-p x)
                (equal (wcomb (icoords x) (ibasis)) x)))
  :hints (("Goal" :use (ilistnp-ibasis ibasis-lin-indep flistnp-icoords ibasis-spans))))
