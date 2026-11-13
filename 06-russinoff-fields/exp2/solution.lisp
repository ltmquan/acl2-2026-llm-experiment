(in-package "DM")

(include-book "defs")

;;;;;;;;;;;;;;;;;;;; part 1 ;;;;;;;;;;;;;;;;;;;;
(encapsulate ()


;;;; ===================== Base fields =====================

(local (include-book "projects/numbers/fermat" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

(defthm zerop-f0-sym (not (zerop 'f0)))

(local
 (defthm member-ninit-iff
   (implies (posp n)
            (iff (member-equal x (ninit n))
                 (and (natp x) (< x n))))
   :hints (("Goal" :use member-ninit))))

(local (defthm primep-int
         (implies (primep p) (and (integerp p) (>= p 2)))
         :hints (("Goal" :in-theory (enable primep)))
         :rule-classes :forward-chaining))

(local
 (defthm fermat-inst
   (implies (and (primep p) (natp x) (< 0 x) (< x p))
            (equal (mod (* x (mod (expt x (+ -2 p)) p)) p) 1))
   :hints (("Goal" :use ((:instance fermat (m x)))
                   :in-theory (e/d (divides) ())))))

(defthm field-axioms-p-rational
  (field-axioms-p 0)
  :hints (("Goal" :in-theory (enable field-axioms-p fadd-closed-p fmul-closed-p fadd-comm-p fmul-comm-p fadd-assoc-p fmul-assoc-p feltp-fone-p
                    fone-fzero-p feltp-fzero-p fzero-id-p fone-id-p fadd-fneg-p feltp-fneg-p feltp-frecip-p
		    fmul-frecip-p fdistrib-p feltp beltp fadd fmul fneg frecip fzero fone badd bmul bneg brecip bzero bone))))

(local (in-theory (enable fadd-closed-p fmul-closed-p fadd-comm-p fmul-comm-p fadd-assoc-p fmul-assoc-p feltp-fone-p
                    fone-fzero-p feltp-fzero-p fzero-id-p fone-id-p fadd-fneg-p feltp-fneg-p feltp-frecip-p
		    fmul-frecip-p fdistrib-p feltp beltp fadd fmul fneg frecip fzero fone badd bmul bneg brecip bzero bone)))
(local (defthm f0-1 (fadd-comm-p 'f0) :hints (("Goal" :use ((:instance f+comm (x (mv-nth 0 (fadd-comm-p-witness 'f0))) (y (mv-nth 1 (fadd-comm-p-witness 'f0)))))))))
(local (defthm f0-2 (fmul-comm-p 'f0) :hints (("Goal" :use ((:instance f*comm (x (mv-nth 0 (fmul-comm-p-witness 'f0))) (y (mv-nth 1 (fmul-comm-p-witness 'f0)))))))))
(local (defthm f0-3 (fadd-assoc-p 'f0) :hints (("Goal" :use ((:instance f+assoc (x (mv-nth 0 (fadd-assoc-p-witness 'f0))) (y (mv-nth 1 (fadd-assoc-p-witness 'f0))) (z (mv-nth 2 (fadd-assoc-p-witness 'f0)))))))))
(local (defthm f0-4 (fmul-assoc-p 'f0) :hints (("Goal" :use ((:instance f*assoc (x (mv-nth 0 (fmul-assoc-p-witness 'f0))) (y (mv-nth 1 (fmul-assoc-p-witness 'f0))) (z (mv-nth 2 (fmul-assoc-p-witness 'f0)))))))))
(local (in-theory (disable fadd-comm-p fmul-comm-p fadd-assoc-p fmul-assoc-p)))
(defthm field-axioms-p-f0
  (field-axioms-p 'f0)
  :hints (("Goal" :in-theory (enable field-axioms-p))))

(local (in-theory (enable fadd-comm-p fmul-comm-p fadd-assoc-p fmul-assoc-p)))
(defthm field-axioms-p-prime
  (implies (primep p) (field-axioms-p p))
  :hints (("Goal" :in-theory (enable field-axioms-p fadd-closed-p fmul-closed-p fadd-comm-p fmul-comm-p fadd-assoc-p fmul-assoc-p feltp-fone-p
                    fone-fzero-p feltp-fzero-p fzero-id-p fone-id-p fadd-fneg-p feltp-fneg-p feltp-frecip-p
		    fmul-frecip-p fdistrib-p feltp beltp fadd fmul fneg frecip fzero fone badd bmul bneg brecip bzero bone))))

(defthm field-axioms-p-fbasep
  (implies (fbasep f) (field-axioms-p f))
  :hints (("Goal" :in-theory (enable fbasep))))

)

;;;;;;;;;;;;;;;;;;;; part 2 ;;;;;;;;;;;;;;;;;;;;

(local (include-book "arithmetic/top-with-meta" :dir :system))

;;;; ===================== Generic field lemmas =====================

(in-theory (disable fmul))

(defmacro fap (f) `(field-axioms-p ,f))

(defthm fap-feltp-fadd
  (implies (and (fap f) (feltp x f) (feltp y f)) (feltp (fadd x y f) f))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use fadd-closed-p-necc)))

(defthm fap-feltp-fmul
  (implies (and (fap f) (feltp x f) (feltp y f)) (feltp (fmul x y f) f))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use fmul-closed-p-necc)))

(defthm fap-fadd-comm
  (implies (and (fap f) (feltp x f) (feltp y f)) (equal (fadd x y f) (fadd y x f)))
  :rule-classes ((:rewrite :loop-stopper ((x y))))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use fadd-comm-p-necc)))

(defthm fap-fmul-comm
  (implies (and (fap f) (feltp x f) (feltp y f)) (equal (fmul x y f) (fmul y x f)))
  :rule-classes ((:rewrite :loop-stopper ((x y))))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use fmul-comm-p-necc)))

(defthm fap-fadd-assoc
  (implies (and (fap f) (feltp x f) (feltp y f) (feltp z f))
           (equal (fadd (fadd x y f) z f) (fadd x (fadd y z f) f)))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use fadd-assoc-p-necc)))

(defthm fap-fmul-assoc
  (implies (and (fap f) (feltp x f) (feltp y f) (feltp z f))
           (equal (fmul (fmul x y f) z f) (fmul x (fmul y z f) f)))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use fmul-assoc-p-necc)))

(defthm fap-feltp-fzero
  (implies (fap f) (feltp (fzero f) f))
  :hints (("Goal" :in-theory (enable field-axioms-p feltp-fzero-p))))

(defthm fap-feltp-fone
  (implies (fap f) (feltp (fone f) f))
  :hints (("Goal" :in-theory (enable field-axioms-p feltp-fone-p))))

(defthm fap-fone-fzero
  (implies (fap f) (not (equal (fone f) (fzero f))))
  :hints (("Goal" :in-theory (enable field-axioms-p fone-fzero-p))))

(defthm fap-fzero-id
  (implies (and (fap f) (feltp x f)) (equal (fadd (fzero f) x f) x))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use fzero-id-p-necc)))

(defthm fap-fone-id
  (implies (and (fap f) (feltp x f)) (equal (fmul (fone f) x f) x))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use fone-id-p-necc)))

(defthm fap-feltp-fneg
  (implies (and (fap f) (feltp x f)) (feltp (fneg x f) f))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use feltp-fneg-p-necc)))

(defthm fap-fadd-fneg
  (implies (and (fap f) (feltp x f)) (equal (fadd x (fneg x f) f) (fzero f)))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use fadd-fneg-p-necc)))

(defthm fap-feltp-frecip
  (implies (and (fap f) (feltp x f) (not (equal x (fzero f)))) (feltp (frecip x f) f))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use feltp-frecip-p-necc)))

(defthm fap-fmul-frecip
  (implies (and (fap f) (feltp x f) (not (equal x (fzero f))))
           (equal (fmul x (frecip x f) f) (fone f)))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use fmul-frecip-p-necc)))

(defthm fap-fdistrib
  (implies (and (fap f) (feltp x f) (feltp y f) (feltp z f))
           (equal (fmul x (fadd y z f) f) (fadd (fmul x y f) (fmul x z f) f)))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use fdistrib-p-necc)))

(in-theory (disable field-axioms-p))

;; derived

(defthm fap-fzero-id-r
  (implies (and (fap f) (feltp x f)) (equal (fadd x (fzero f) f) x))
  :hints (("Goal" :use ((:instance fap-fadd-comm (y (fzero f)))))))

(defthm fap-fone-id-r
  (implies (and (fap f) (feltp x f)) (equal (fmul x (fone f) f) x))
  :hints (("Goal" :use ((:instance fap-fmul-comm (y (fone f)))))))

(defthm fap-fadd-comm2
  (implies (and (fap f) (feltp x f) (feltp y f) (feltp z f))
           (equal (fadd x (fadd y z f) f) (fadd y (fadd x z f) f)))
  :rule-classes ((:rewrite :loop-stopper ((x y))))
  :hints (("Goal" :use ((:instance fap-fadd-assoc)
                        (:instance fap-fadd-assoc (x y) (y x)))
           :in-theory (disable fap-fadd-assoc))))

(defthm fap-fmul-comm2
  (implies (and (fap f) (feltp x f) (feltp y f) (feltp z f))
           (equal (fmul x (fmul y z f) f) (fmul y (fmul x z f) f)))
  :rule-classes ((:rewrite :loop-stopper ((x y))))
  :hints (("Goal" :use ((:instance fap-fmul-assoc)
                        (:instance fap-fmul-assoc (x y) (y x)))
           :in-theory (disable fap-fmul-assoc))))

(defthm fap-fdistrib-r
  (implies (and (fap f) (feltp x f) (feltp y f) (feltp z f))
           (equal (fmul (fadd y z f) x f) (fadd (fmul y x f) (fmul z x f) f)))
  :hints (("Goal" :use ((:instance fap-fmul-comm (y (fadd y z f)))
                        (:instance fap-fmul-comm (x y) (y x))
                        (:instance fap-fmul-comm (x z) (y x)))
           :in-theory (disable fap-fmul-comm))))

(defthm fap-fneg-fadd-r
  (implies (and (fap f) (feltp x f)) (equal (fadd (fneg x f) x f) (fzero f)))
  :hints (("Goal" :use ((:instance fap-fadd-comm (y (fneg x f)))))))

(defthm fap-fadd-cancel-lemma
  (implies (and (fap f) (feltp x f) (feltp y f) (feltp z f)
                (equal (fadd x y f) (fadd x z f)))
           (equal y z))
  :hints (("Goal" :use ((:instance fap-fadd-assoc (x (fneg x f)) (y x) (z y))
                        (:instance fap-fadd-assoc (x (fneg x f)) (y x) (z z)))
           :in-theory (disable fap-fadd-assoc)))
  :rule-classes nil)

(defthm fap-fadd-cancel
  (implies (and (fap f) (feltp x f) (feltp y f) (feltp z f))
           (equal (equal (fadd x y f) (fadd x z f)) (equal y z)))
  :hints (("Goal" :use fap-fadd-cancel-lemma)))

(defthm fap-fadd-cancel-r
  (implies (and (fap f) (feltp x f) (feltp y f) (feltp z f))
           (equal (equal (fadd y x f) (fadd z x f)) (equal y z)))
  :hints (("Goal" :use (fap-fadd-cancel-lemma
                        (:instance fap-fadd-comm (y z))))))

(defthm fap-fadd-self-cancel
  (implies (and (fap f) (feltp x f) (feltp y f))
           (equal (equal (fadd x y f) x) (equal y (fzero f))))
  :hints (("Goal" :use ((:instance fap-fadd-cancel-lemma (z (fzero f)))))))

(defthm fap-fadd-self-cancel-r
  (implies (and (fap f) (feltp x f) (feltp y f))
           (equal (equal (fadd y x f) x) (equal y (fzero f))))
  :hints (("Goal" :use ((:instance fap-fadd-cancel-lemma (z (fzero f)))))))

(defthm fap-fmul-fzero
  (implies (and (fap f) (feltp x f)) (equal (fmul x (fzero f) f) (fzero f)))
  :hints (("Goal" :use ((:instance fap-fdistrib (y (fzero f)) (z (fzero f)))
                        (:instance fap-fadd-self-cancel (x (fmul x (fzero f) f)) (y (fmul x (fzero f) f))))
           :in-theory (disable fap-fdistrib fap-fadd-self-cancel))))

(defthm fap-fmul-fzero-l
  (implies (and (fap f) (feltp x f)) (equal (fmul (fzero f) x f) (fzero f)))
  :hints (("Goal" :use ((:instance fap-fmul-comm (y (fzero f)))))))

(defthm fap-fneg-unique
  (implies (and (fap f) (feltp x f) (feltp y f))
           (equal (equal (fadd x y f) (fzero f)) (equal y (fneg x f))))
  :hints (("Goal" :use ((:instance fap-fadd-cancel-lemma (z (fneg x f)))))))

(defthm fap-fneg-unique-r
  (implies (and (fap f) (feltp x f) (feltp y f))
           (equal (equal (fadd y x f) (fzero f)) (equal y (fneg x f))))
  :hints (("Goal" :use ((:instance fap-fneg-unique) (:instance fap-fadd-comm))
           :in-theory (disable fap-fneg-unique fap-fadd-comm))))

(defthm fap-fneg-fzero
  (implies (fap f) (equal (fneg (fzero f) f) (fzero f)))
  :hints (("Goal" :use ((:instance fap-fneg-unique (x (fzero f)) (y (fzero f)))))))

(defthm fap-fneg-fneg
  (implies (and (fap f) (feltp x f)) (equal (fneg (fneg x f) f) x))
  :hints (("Goal" :use ((:instance fap-fneg-unique (x (fneg x f)) (y x))))))

(defthm fap-fneg-zero-iff
  (implies (and (fap f) (feltp x f)) (equal (equal (fneg x f) (fzero f)) (equal x (fzero f))))
  :hints (("Goal" :use ((:instance fap-fneg-fneg)) :in-theory (disable fap-fneg-fneg))))

(defthm fap-fneg-fadd
  (implies (and (fap f) (feltp x f) (feltp y f))
           (equal (fneg (fadd x y f) f) (fadd (fneg x f) (fneg y f) f)))
  :hints (("Goal" :use ((:instance fap-fneg-unique (x (fadd x y f)) (y (fadd (fneg x f) (fneg y f) f))))
           :in-theory (disable fap-fneg-unique fap-fneg-unique-r))))

(defthm fap-fmul-fneg
  (implies (and (fap f) (feltp x f) (feltp y f))
           (equal (fmul x (fneg y f) f) (fneg (fmul x y f) f)))
  :hints (("Goal" :use ((:instance fap-fneg-unique (x (fmul x y f)) (y (fmul x (fneg y f) f)))
                        (:instance fap-fdistrib (z (fneg y f))))
           :in-theory (disable fap-fneg-unique fap-fneg-unique-r fap-fdistrib))))

(defthm fap-fmul-fneg-l
  (implies (and (fap f) (feltp x f) (feltp y f))
           (equal (fmul (fneg y f) x f) (fneg (fmul y x f) f)))
  :hints (("Goal" :use ((:instance fap-fmul-comm (y (fneg y f))) (:instance fap-fmul-comm))
           :in-theory (disable fap-fmul-comm))))

(defthm fap-frecip-nonzero
  (implies (and (fap f) (feltp x f) (not (equal x (fzero f))))
           (not (equal (frecip x f) (fzero f))))
  :hints (("Goal" :use (fap-fmul-frecip) :in-theory (disable fap-fmul-frecip))))

(defthm fap-fmul-frecip-l
  (implies (and (fap f) (feltp x f) (not (equal x (fzero f))))
           (equal (fmul (frecip x f) x f) (fone f)))
  :hints (("Goal" :use (fap-fmul-frecip (:instance fap-fmul-comm (y (frecip x f))))
           :in-theory (disable fap-fmul-frecip fap-fmul-comm))))

(defthm fap-integral-lemma
  (implies (and (fap f) (feltp x f) (feltp y f) (not (equal x (fzero f)))
                (equal (fmul x y f) (fzero f)))
           (equal y (fzero f)))
  :hints (("Goal" :use ((:instance fap-fmul-assoc (x (frecip x f)) (y x) (z y)))
           :in-theory (disable fap-fmul-assoc)))
  :rule-classes nil)

(defthm fap-fmul-zero-iff
  (implies (and (fap f) (feltp x f) (feltp y f))
           (equal (equal (fmul x y f) (fzero f))
                  (or (equal x (fzero f)) (equal y (fzero f)))))
  :hints (("Goal" :use (fap-integral-lemma (:instance fap-integral-lemma (x y) (y x))))))

(defthm fap-fmul-cancel-lemma
  (implies (and (fap f) (feltp x f) (feltp y f) (feltp z f) (not (equal x (fzero f)))
                (equal (fmul x y f) (fmul x z f)))
           (equal y z))
  :hints (("Goal" :use ((:instance fap-fmul-assoc (x (frecip x f)) (y x) (z y))
                        (:instance fap-fmul-assoc (x (frecip x f)) (y x) (z z)))
           :in-theory (disable fap-fmul-assoc)))
  :rule-classes nil)

(defthm fap-fmul-cancel
  (implies (and (fap f) (feltp x f) (feltp y f) (feltp z f) (not (equal x (fzero f))))
           (equal (equal (fmul x y f) (fmul x z f)) (equal y z)))
  :hints (("Goal" :use fap-fmul-cancel-lemma)))

(defthm fap-frecip-fone
  (implies (fap f) (equal (frecip (fone f) f) (fone f)))
  :hints (("Goal" :use ((:instance fap-fmul-frecip (x (fone f))))
           :in-theory (disable fap-fmul-frecip))))

(defthm fap-fadd-fneg-cancel-1
  (implies (and (fap f) (feltp x f) (feltp y f))
           (equal (fadd x (fadd (fneg x f) y f) f) y))
  :hints (("Goal" :use ((:instance fap-fadd-assoc (y (fneg x f)) (z y))) :in-theory (disable fap-fadd-assoc))))

(defthm fap-fadd-fneg-cancel-2
  (implies (and (fap f) (feltp x f) (feltp y f))
           (equal (fadd (fneg x f) (fadd x y f) f) y))
  :hints (("Goal" :use ((:instance fap-fadd-assoc (x (fneg x f)) (y x) (z y))) :in-theory (disable fap-fadd-assoc))))

(defthm fap-fadd-fneg-cancel-3
  (implies (and (fap f) (feltp x f) (feltp y f))
           (equal (fadd x (fadd y (fneg x f) f) f) y))
  :hints (("Goal" :use ((:instance fap-fadd-comm2 (y y) (z (fneg x f)))) :in-theory (disable fap-fadd-comm2))))

(defthm fap-fadd-fneg-cancel-4
  (implies (and (fap f) (feltp x f) (feltp y f))
           (equal (fadd (fneg x f) (fadd y x f) f) y))
  :hints (("Goal" :use ((:instance fap-fadd-comm2 (x (fneg x f)) (y y) (z x))) :in-theory (disable fap-fadd-comm2))))

(defthm fap-fadd-fneg-cancel-5
  (implies (and (fap f) (feltp x f) (feltp y f) (feltp z f))
           (equal (fadd x (fadd y (fadd z (fneg x f) f) f) f) (fadd y z f)))
  :hints (("Goal" :use ((:instance fap-fadd-comm2 (x x) (y y) (z (fadd z (fneg x f) f))))
           :in-theory (disable fap-fadd-comm2))))

(defthm fap-fadd-fneg-cancel-6
  (implies (and (fap f) (feltp x f) (feltp y f) (feltp z f))
           (equal (fadd (fneg x f) (fadd y (fadd z x f) f) f) (fadd y z f)))
  :hints (("Goal" :use ((:instance fap-fadd-comm2 (x (fneg x f)) (y y) (z (fadd z x f))))
           :in-theory (disable fap-fadd-comm2))))

(defthm fap-frecip-cancel-1
  (implies (and (fap f) (feltp x f) (feltp y f) (not (equal x (fzero f))))
           (equal (fmul x (fmul (frecip x f) y f) f) y))
  :hints (("Goal" :use ((:instance fap-fmul-assoc (y (frecip x f)) (z y))) :in-theory (disable fap-fmul-assoc))))

(defthm fap-frecip-cancel-2
  (implies (and (fap f) (feltp x f) (feltp y f) (not (equal x (fzero f))))
           (equal (fmul (frecip x f) (fmul x y f) f) y))
  :hints (("Goal" :use ((:instance fap-fmul-assoc (x (frecip x f)) (y x) (z y))) :in-theory (disable fap-fmul-assoc))))

(defthm fap-frecip-cancel-3
  (implies (and (fap f) (feltp x f) (feltp y f) (not (equal x (fzero f))))
           (equal (fmul x (fmul y (frecip x f) f) f) y))
  :hints (("Goal" :use ((:instance fap-fmul-comm2 (x x) (y y) (z (frecip x f)))) :in-theory (disable fap-fmul-comm2))))

(defthm fap-frecip-cancel-4
  (implies (and (fap f) (feltp x f) (feltp y f) (not (equal x (fzero f))))
           (equal (fmul (frecip x f) (fmul y x f) f) y))
  :hints (("Goal" :use ((:instance fap-fmul-comm2 (x (frecip x f)) (y y) (z x))) :in-theory (disable fap-fmul-comm2))))

;;;;;;;;;;;;;;;;;;;; part 3 ;;;;;;;;;;;;;;;;;;;;


;;;; ===================== Coefficients & extensionality =====================

(defthm len-zero-iff-1 (equal (equal 0 (len x)) (not (consp x))))
(defthm len-zero-iff-2 (equal (equal (len x) 0) (not (consp x))))

(defun pco (l i f)
  (if (consp l)
      (if (equal (nfix i) (len (cdr l)))
          (car l)
        (pco (cdr l) i f))
    (fzero f)))

(defthm pco-not-natp
  (implies (not (natp i)) (equal (pco l i f) (pco l 0 f))))

(defthm feltp-pco
  (implies (and (fap f) (feltsp l f)) (feltp (pco l i f) f)))

(defthm pco-beyond
  (implies (>= (nfix i) (len l)) (equal (pco l i f) (fzero f))))

(defthm pco-top
  (implies (consp l) (equal (pco l (len (cdr l)) f) (car l))))

(defthm feltsp-true-listp
  (implies (feltsp l f) (true-listp l))
  :rule-classes :forward-chaining)

(defthm polyp-forward
  (implies (polyp p f) (and (feltsp p f) (consp p)))
  :hints (("Goal" :in-theory (enable polyp)))
  :rule-classes :forward-chaining)

(defthm polyp-feltsp
  (implies (polyp p f) (feltsp p f))
  :hints (("Goal" :in-theory (enable polyp))))

(defthm polyp-feltsp-cdr
  (implies (polyp p f) (feltsp (cdr p) f))
  :hints (("Goal" :in-theory (enable polyp))))

(defthm polyp-consp
  (implies (polyp p f) (consp p))
  :hints (("Goal" :in-theory (enable polyp))))

(defthm polyp-car-nonzero
  (implies (and (polyp p f) (consp (cdr p))) (not (equal (car p) (fzero f))))
  :hints (("Goal" :in-theory (enable polyp))))

(defthm feltp-car-feltsp
  (implies (and (feltsp l f) (consp l)) (feltp (car l) f)))

(defthm polyp-intro
  (implies (and (feltsp p f) (consp p)
                (or (not (consp (cdr p))) (not (equal (car p) (fzero f)))))
           (polyp p f))
  :hints (("Goal" :in-theory (enable polyp))))

;; witness for extensionality

(defun pwit (p q)
  (if (consp p)
      (if (equal (car p) (car q))
          (pwit (cdr p) (cdr q))
        (len (cdr p)))
    0))

(defthm pwit-bound
  (implies (and (equal (len p) (len q)) (true-listp p) (true-listp q) (not (equal p q)))
           (< (pwit p q) (len p)))
  :rule-classes :linear)

(defthm natp-pwit (natp (pwit p q)) :rule-classes :type-prescription)

(defthm pwit-lemma
  (implies (and (equal (len p) (len q)) (true-listp p) (true-listp q) (not (equal p q)))
           (not (equal (pco p (pwit p q) f) (pco q (pwit p q) f)))))

(defund pwitness (p q)
  (cond ((> (len p) (len q)) (len (cdr p)))
        ((> (len q) (len p)) (len (cdr q)))
        (t (pwit p q))))

(defthm natp-pwitness (natp (pwitness p q))
  :hints (("Goal" :in-theory (enable pwitness)))
  :rule-classes :type-prescription)

(defthm poly-ext
  (implies (and (polyp p f) (polyp q f)
                (equal (pco p (pwitness p q) f) (pco q (pwitness p q) f)))
           (equal p q))
  :hints (("Goal" :in-theory (enable pwitness)
           :use ((:instance pwit-lemma)
                 (:instance polyp-car-nonzero (p p))
                 (:instance polyp-car-nonzero (p q)))
           :cases ((> (len p) (len q)) (> (len q) (len p)))))
  :rule-classes nil)

(defmacro ext-hint (a b)
  `(:use ((:instance poly-ext (p ,a) (q ,b)))))

;;; pstrip

(defthm pco-pstrip
  (equal (pco (pstrip l f) i f) (pco l i f))
  :hints (("Goal" :induct (pstrip l f))))

(defthm feltsp-pstrip
  (implies (feltsp l f) (feltsp (pstrip l f) f)))

(defthm consp-pstrip
  (implies (consp l) (consp (pstrip l f))))

(defthm polyp-pstrip
  (implies (and (feltsp l f) (consp l)) (polyp (pstrip l f) f))
  :hints (("Goal" :in-theory (enable polyp))))

(defthm polyp-pstrip-cdr
  (implies (and (polyp p f) (consp (cdr p))) (polyp (pstrip (cdr p) f) f)))

(defthm len-pstrip
  (<= (len (pstrip l f)) (len l))
  :rule-classes :linear)

(defthm pstrip-polyp
  (implies (polyp p f) (equal (pstrip p f) p))
  :hints (("Goal" :expand ((pstrip p f)) :in-theory (enable polyp))))

;;; faddl

(defun faddl-induct (x y)
  (declare (xargs :measure (+ (len x) (len y))))
  (if (> (len x) (len y))
      (faddl-induct (cdr x) y)
    (if (> (len y) (len x))
        (faddl-induct x (cdr y))
      (if (consp x) (faddl-induct (cdr x) (cdr y)) t))))

(defthm len-faddl
  (equal (len (faddl x y f)) (max (len x) (len y)))
  :hints (("Goal" :induct (faddl-induct x y))))

(defthm len-faddl-cdr-1
  (implies (< (len y) (len x)) (equal (len (faddl (cdr x) y f)) (len (cdr x)))))
(defthm len-faddl-cdr-2
  (implies (< (len x) (len y)) (equal (len (faddl x (cdr y) f)) (len (cdr y)))))
(defthm len-faddl-cdr-3
  (implies (equal (len x) (len y)) (equal (len (faddl (cdr x) (cdr y) f)) (len (cdr x)))))

(defthm consp-faddl
  (implies (or (consp x) (consp y)) (consp (faddl x y f)))
  :hints (("Goal" :use len-faddl :expand ((len x) (len y)) :in-theory (disable len-faddl))))

(defthm feltsp-faddl
  (implies (and (fap f) (feltsp x f) (feltsp y f)) (feltsp (faddl x y f) f))
  :hints (("Goal" :induct (faddl-induct x y))))

(defthm pco-faddl
  (implies (and (fap f) (feltsp x f) (feltsp y f))
           (equal (pco (faddl x y f) i f) (fadd (pco x i f) (pco y i f) f)))
  :hints (("Goal" :induct (faddl-induct x y))))

;;; padd

(defthm polyp-padd
  (implies (and (fap f) (feltsp x f) (feltsp y f) (or (consp x) (consp y)))
           (polyp (padd x y f) f))
  :hints (("Goal" :in-theory (enable padd))))

(defthm consp-padd
  (implies (or (consp x) (consp y)) (consp (padd x y f)))
  :hints (("Goal" :in-theory (enable padd))))

(defthm polyp-padd-2
  (implies (and (fap f) (polyp x f) (polyp y f))
           (polyp (padd x y f) f)))

(defthm feltsp-padd
  (implies (and (fap f) (feltsp x f) (feltsp y f)) (feltsp (padd x y f) f))
  :hints (("Goal" :in-theory (enable padd))))

(defthm pco-padd
  (implies (and (fap f) (feltsp x f) (feltsp y f))
           (equal (pco (padd x y f) i f) (fadd (pco x i f) (pco y i f) f)))
  :hints (("Goal" :in-theory (enable padd))))

(defthm len-padd
  (<= (len (padd x y f)) (max (len x) (len y)))
  :hints (("Goal" :in-theory (enable padd)))
  :rule-classes :linear)

(defthm len-padd-1
  (implies (<= (len y) (len x)) (<= (len (padd x y f)) (len x)))
  :hints (("Goal" :use len-padd :in-theory (disable len-padd)))
  :rule-classes :linear)

(defthm len-padd-2
  (implies (<= (len x) (len y)) (<= (len (padd x y f)) (len y)))
  :hints (("Goal" :use len-padd :in-theory (disable len-padd)))
  :rule-classes :linear)

(defthm len-padd-bound
  (implies (and (< (len x) n) (< (len y) n)) (< (len (padd x y f)) n))
  :hints (("Goal" :use len-padd :in-theory (disable len-padd))))

;;; pzero, pone

(defthm polyp-pzero
  (implies (fap f) (polyp (pzero f) f))
  :hints (("Goal" :in-theory (enable pzero polyp))))

(defthm polyp-pone
  (implies (fap f) (polyp (pone f) f))
  :hints (("Goal" :in-theory (enable pone polyp))))

(defthm pco-pzero
  (equal (pco (pzero f) i f) (fzero f))
  :hints (("Goal" :in-theory (enable pzero))))

(defthm pco-pone
  (equal (pco (pone f) i f) (if (zp i) (fone f) (fzero f)))
  :hints (("Goal" :in-theory (enable pone))))

(defthm len-pzero (equal (len (pzero f)) 1) :hints (("Goal" :in-theory (enable pzero))))
(defthm len-pone (equal (len (pone f)) 1) :hints (("Goal" :in-theory (enable pone))))
(defthm car-pzero (equal (car (pzero f)) (fzero f)) :hints (("Goal" :in-theory (enable pzero))))
(defthm car-pone (equal (car (pone f)) (fone f)) :hints (("Goal" :in-theory (enable pone))))
(defthm consp-pzero (consp (pzero f)) :hints (("Goal" :in-theory (enable pzero))))
(defthm consp-pone (consp (pone f)) :hints (("Goal" :in-theory (enable pone))))
(defthm cdr-pzero (equal (cdr (pzero f)) nil) :hints (("Goal" :in-theory (enable pzero))))
(defthm cdr-pone (equal (cdr (pone f)) nil) :hints (("Goal" :in-theory (enable pone))))

(defthm pone-not-pzero
  (implies (fap f) (not (equal (pone f) (pzero f))))
  :hints (("Goal" :in-theory (enable pone pzero))))

;;; padd laws

(defthm padd-comm
  (implies (and (fap f) (polyp x f) (polyp y f))
           (equal (padd x y f) (padd y x f)))
  :hints (("Goal" :use ((:instance poly-ext (p (padd x y f)) (q (padd y x f))))))
  :rule-classes ((:rewrite :loop-stopper ((x y)))))

(defthm padd-assoc
  (implies (and (fap f) (polyp x f) (polyp y f) (polyp z f))
           (equal (padd (padd x y f) z f) (padd x (padd y z f) f)))
  :hints (("Goal" :use ((:instance poly-ext (p (padd (padd x y f) z f)) (q (padd x (padd y z f) f)))))))

(defthm padd-comm2
  (implies (and (fap f) (polyp x f) (polyp y f) (polyp z f))
           (equal (padd x (padd y z f) f) (padd y (padd x z f) f)))
  :hints (("Goal" :use ((:instance poly-ext (p (padd x (padd y z f) f)) (q (padd y (padd x z f) f))))))
  :rule-classes ((:rewrite :loop-stopper ((x y)))))

(defthm padd-pzero
  (implies (and (fap f) (polyp x f))
           (equal (padd (pzero f) x f) x))
  :hints (("Goal" :use ((:instance poly-ext (p (padd (pzero f) x f)) (q x))))))

(defthm padd-pzero-r
  (implies (and (fap f) (polyp x f))
           (equal (padd x (pzero f) f) x))
  :hints (("Goal" :use ((:instance poly-ext (p (padd x (pzero f) f)) (q x))))))

;;; pneg

(defthm len-pneg (equal (len (pneg x f)) (len x))
  :hints (("Goal" :induct (len x))))

(defthm feltsp-pneg
  (implies (and (fap f) (feltsp x f)) (feltsp (pneg x f) f))
  :hints (("Goal" :induct (len x))))

(defthm pco-pneg
  (implies (and (fap f) (feltsp x f))
           (equal (pco (pneg x f) i f) (fneg (pco x i f) f)))
  :hints (("Goal" :induct (len x))))

(defthm polyp-pneg
  (implies (and (fap f) (polyp x f)) (polyp (pneg x f) f))
  :hints (("Goal" :in-theory (enable polyp)
           :expand ((pneg x f)))))

(defthm padd-pneg
  (implies (and (fap f) (polyp x f))
           (equal (padd x (pneg x f) f) (pzero f)))
  :hints (("Goal" :use ((:instance poly-ext (p (padd x (pneg x f) f)) (q (pzero f)))))))

(defthm padd-pneg-l
  (implies (and (fap f) (polyp x f))
           (equal (padd (pneg x f) x f) (pzero f)))
  :hints (("Goal" :use ((:instance poly-ext (p (padd (pneg x f) x f)) (q (pzero f)))))))

(defthm padd-pneg-cancel
  (implies (and (fap f) (polyp x f) (polyp y f))
           (equal (padd x (padd (pneg x f) y f) f) y))
  :hints (("Goal" :use ((:instance poly-ext (p (padd x (padd (pneg x f) y f) f)) (q y))))))

(defthm padd-pneg-cancel-2
  (implies (and (fap f) (polyp x f) (polyp y f))
           (equal (padd (pneg x f) (padd x y f) f) y))
  :hints (("Goal" :use ((:instance poly-ext (p (padd (pneg x f) (padd x y f) f)) (q y))))))

(defthm padd-pneg-cancel-3
  (implies (and (fap f) (polyp x f) (polyp y f))
           (equal (padd x (padd y (pneg x f) f) f) y))
  :hints (("Goal" :use ((:instance poly-ext (p (padd x (padd y (pneg x f) f) f)) (q y))))))

(defthm padd-pneg-cancel-4
  (implies (and (fap f) (polyp x f) (polyp y f))
           (equal (padd (pneg x f) (padd y x f) f) y))
  :hints (("Goal" :use ((:instance poly-ext (p (padd (pneg x f) (padd y x f) f)) (q y))))))

(defthm padd-pneg-cancel-5
  (implies (and (fap f) (polyp x f) (polyp y f) (polyp z f))
           (equal (padd x (padd y (padd z (pneg x f) f) f) f) (padd y z f)))
  :hints (("Goal" :use ((:instance poly-ext (p (padd x (padd y (padd z (pneg x f) f) f) f)) (q (padd y z f)))))))

(defthm padd-pneg-cancel-6
  (implies (and (fap f) (polyp x f) (polyp y f) (polyp z f))
           (equal (padd (pneg x f) (padd y (padd z x f) f) f) (padd y z f)))
  :hints (("Goal" :use ((:instance poly-ext (p (padd (pneg x f) (padd y (padd z x f) f) f)) (q (padd y z f)))))))

(defthm pneg-pneg
  (implies (and (fap f) (polyp x f)) (equal (pneg (pneg x f) f) x))
  :hints (("Goal" :use ((:instance poly-ext (p (pneg (pneg x f) f)) (q x))))))

(defthm pneg-padd
  (implies (and (fap f) (polyp x f) (polyp y f))
           (equal (pneg (padd x y f) f) (padd (pneg x f) (pneg y f) f)))
  :hints (("Goal" :use ((:instance poly-ext (p (pneg (padd x y f) f)) (q (padd (pneg x f) (pneg y f) f)))))))

(defthm pneg-pzero
  (implies (fap f) (equal (pneg (pzero f) f) (pzero f)))
  :hints (("Goal" :in-theory (enable pzero))))

(defthm padd-cancel
  (implies (and (fap f) (polyp x f) (polyp y f) (polyp z f))
           (equal (equal (padd x y f) (padd x z f)) (equal y z)))
  :hints (("Goal" :use ((:instance padd-pneg-cancel-2 (y y))
                        (:instance padd-pneg-cancel-2 (y z)))
           :in-theory (disable padd-pneg-cancel-2 padd-comm padd-comm2 padd-pneg-cancel))))

(defthm padd-cancel-r
  (implies (and (fap f) (polyp x f) (polyp y f) (polyp z f))
           (equal (equal (padd y x f) (padd z x f)) (equal y z)))
  :hints (("Goal" :use ((:instance padd-cancel))
           :in-theory (disable padd-cancel))))

(defthm padd-zero-iff
  (implies (and (fap f) (polyp x f) (polyp y f))
           (equal (equal (padd x y f) (pzero f)) (equal y (pneg x f))))
  :hints (("Goal" :use ((:instance padd-cancel (z (pneg x f))))
           :in-theory (disable padd-cancel))))

(defthm padd-self-iff
  (implies (and (fap f) (polyp x f) (polyp y f))
           (equal (equal (padd x y f) x) (equal y (pzero f))))
  :hints (("Goal" :use ((:instance padd-cancel (z (pzero f))))
           :in-theory (disable padd-cancel))))

;;; cmul

(defthm feltsp-cmul
  (implies (and (fap f) (feltp c f) (feltsp p f)) (feltsp (cmul c p f) f))
  :hints (("Goal" :induct (len p))))

(defthm len-cmul
  (implies (not (equal c (fzero f))) (equal (len (cmul c p f)) (len p)))
  :hints (("Goal" :induct (len p))))

(defthm pco-cmul
  (implies (and (fap f) (feltp c f) (feltsp p f))
           (equal (pco (cmul c p f) i f) (fmul c (pco p i f) f)))
  :hints (("Goal" :induct (len p))))

(defthm consp-cmul
  (implies (consp q) (consp (cmul c q f)))
  :hints (("Goal" :expand ((cmul c q f)))))

(defthm car-cmul
  (implies (and (not (equal c (fzero f))) (consp p))
           (equal (car (cmul c p f)) (fmul c (car p) f))))

(defthm polyp-cmul
  (implies (and (fap f) (feltp c f) (polyp p f)) (polyp (cmul c p f) f))
  :hints (("Goal" :in-theory (enable polyp)
           :expand ((cmul c p f)))))

(defthm cmul-fone
  (implies (and (fap f) (polyp p f)) (equal (cmul (fone f) p f) p))
  :hints (("Goal" :use ((:instance poly-ext (p (cmul (fone f) p f)) (q p))))))

(defthm cmul-fzero
  (equal (cmul (fzero f) p f) (pzero f))
  :hints (("Goal" :in-theory (enable pzero))))

(defthm cmul-pzero
  (implies (and (fap f) (feltp c f)) (equal (cmul c (pzero f) f) (pzero f)))
  :hints (("Goal" :use ((:instance poly-ext (p (cmul c (pzero f) f)) (q (pzero f)))))))

(defthm cmul-cmul
  (implies (and (fap f) (feltp c f) (feltp d f) (polyp p f))
           (equal (cmul c (cmul d p f) f) (cmul (fmul c d f) p f)))
  :hints (("Goal" :use ((:instance poly-ext (p (cmul c (cmul d p f) f)) (q (cmul (fmul c d f) p f)))))))

(defthm cmul-padd
  (implies (and (fap f) (feltp c f) (polyp p f) (polyp q f))
           (equal (cmul c (padd p q f) f) (padd (cmul c p f) (cmul c q f) f)))
  :hints (("Goal" :use ((:instance poly-ext (p (cmul c (padd p q f) f)) (q (padd (cmul c p f) (cmul c q f) f)))))))

(defthm cmul-pneg
  (implies (and (fap f) (feltp c f) (polyp p f))
           (equal (cmul c (pneg p f) f) (pneg (cmul c p f) f)))
  :hints (("Goal" :use ((:instance poly-ext (p (cmul c (pneg p f) f)) (q (pneg (cmul c p f) f)))))))

;;; pshift

(defthm len-append-x (equal (len (append a b)) (+ (len a) (len b))))

(defthm pco-append-zero
  (equal (pco (append l (list z)) i f)
         (if (zp i) z (pco l (1- i) f))))

(defthm len-pshift
  (equal (len (pshift p k f)) (+ (len p) (nfix k))))

(defthm feltsp-append
  (implies (and (feltsp a f) (feltsp b f)) (feltsp (append a b) f)))

(defthm feltsp-pshift
  (implies (and (fap f) (feltsp p f)) (feltsp (pshift p k f) f)))

(defthm pco-pshift
  (equal (pco (pshift p k f) i f)
         (if (< (nfix i) (nfix k)) (fzero f) (pco p (- (nfix i) (nfix k)) f)))
  :hints (("Goal" :induct (pshift p k f))))

(defthm car-pshift
  (implies (consp p) (equal (car (pshift p k f)) (car p))))

(defthm consp-pshift
  (implies (consp p) (consp (pshift p k f))))

(defthm polyp-pshift
  (implies (and (fap f) (polyp p f) (not (equal p (pzero f))))
           (polyp (pshift p k f) f))
  :hints (("Goal" :in-theory (enable polyp pzero)
           :cases ((consp (cdr p))))))

;;; monomial

(defthm pco-monomial
  (equal (pco (monomial c k f) i f)
         (if (equal (nfix i) (nfix k)) c (fzero f))))

(defthm len-monomial (equal (len (monomial c k f)) (1+ (nfix k))))

(defthm feltsp-monomial
  (implies (and (fap f) (feltp c f)) (feltsp (monomial c k f) f)))

(defthm car-monomial (equal (car (monomial c k f)) c))

(defthm polyp-monomial
  (implies (and (fap f) (feltp c f) (not (equal c (fzero f))))
           (polyp (monomial c k f) f))
  :hints (("Goal" :in-theory (e/d (pzero) (polyp-pshift))
           :use ((:instance polyp-pshift (p (list c)))))))

(in-theory (disable monomial))

;;;;;;;;;;;;;;;;;;;; part 4 ;;;;;;;;;;;;;;;;;;;;


;;;; ===================== Convolution & pmul =====================

(defun conv (l q i f)
  (if (consp l)
      (fadd (if (<= (len (cdr l)) (nfix i))
                (fmul (car l) (pco q (- (nfix i) (len (cdr l))) f) f)
              (fzero f))
            (conv (cdr l) q i f)
            f)
    (fzero f)))

(defthm monomial-nfix
  (equal (monomial c (nfix k) f) (monomial c k f))
  :hints (("Goal" :in-theory (enable monomial))))

(defthm conv-nfix
  (equal (conv l q (nfix i) f) (conv l q i f)))

(defthm conv-not-natp
  (implies (not (natp i)) (equal (conv l q i f) (conv l q 0 f))))

(defthm feltp-conv
  (implies (and (fap f) (feltsp l f) (feltsp q f)) (feltp (conv l q i f) f)))

(defthm conv-pstrip
  (implies (and (fap f) (feltsp l f) (feltsp q f))
           (equal (conv (pstrip l f) q i f) (conv l q i f))))

(defun csum (l q i j f)
  (if (zp j)
      (fmul (pco l 0 f) (pco q i f) f)
    (fadd (fmul (pco l j f) (pco q (- i j) f) f) (csum l q i (1- j) f) f)))

(defthm feltp-csum
  (implies (and (fap f) (feltsp l f) (feltsp q f)) (feltp (csum l q i j f) f)))

(defthm csum-nil
  (implies (and (fap f) (feltsp q f)) (equal (csum nil q i j f) (fzero f))))

(defthm csum-cons
  (implies (and (fap f) (feltp a f) (feltsp l f) (feltsp q f) (natp i) (natp j) (<= j i))
           (equal (csum (cons a l) q i j f)
                  (fadd (if (<= (len l) j) (fmul a (pco q (- i (len l)) f) f) (fzero f))
                        (csum l q i j f) f)))
  :hints (("Goal" :induct (csum l q i j f))))

(defthm conv-csum
  (implies (and (fap f) (feltsp l f) (feltsp q f) (natp i))
           (equal (conv l q i f) (csum l q i i f)))
  :hints (("Goal" :induct (len l)))
  :rule-classes nil)

(defthm csum-faddl
  (implies (and (fap f) (feltsp x f) (feltsp y f) (feltsp q f))
           (equal (csum (faddl x y f) q i j f)
                  (fadd (csum x q i j f) (csum y q i j f) f))))

(defthm conv-pstrip-r
  (equal (conv l (pstrip q f) i f) (conv l q i f)))

(defthm conv-faddl
  (implies (and (fap f) (feltsp x f) (feltsp y f) (feltsp q f))
           (equal (conv (faddl x y f) q i f)
                  (fadd (conv x q i f) (conv y q i f) f)))
  :hints (("Goal" :use ((:instance conv-csum (l (faddl x y f)) (i (nfix i)))
                        (:instance conv-csum (l x) (i (nfix i)))
                        (:instance conv-csum (l y) (i (nfix i)))
                        (:instance conv-nfix (l (faddl x y f)))
                        (:instance conv-nfix (l x))
                        (:instance conv-nfix (l y)))
           :in-theory (disable conv-nfix))))

(defthm conv-padd-l
  (implies (and (fap f) (feltsp x f) (feltsp y f) (feltsp q f))
           (equal (conv (padd x y f) q i f)
                  (fadd (conv x q i f) (conv y q i f) f)))
  :hints (("Goal" :in-theory (enable padd))))

(defthm conv-padd-r
  (implies (and (fap f) (feltsp l f) (feltsp x f) (feltsp y f))
           (equal (conv l (padd x y f) i f)
                  (fadd (conv l x i f) (conv l y i f) f))))

(defthm conv-pneg-l
  (implies (and (fap f) (feltsp l f) (feltsp q f))
           (equal (conv (pneg l f) q i f) (fneg (conv l q i f) f))))

(defthm conv-pneg-r
  (implies (and (fap f) (feltsp l f) (feltsp q f))
           (equal (conv l (pneg q f) i f) (fneg (conv l q i f) f))))

(defthm conv-cmul-l
  (implies (and (fap f) (feltp c f) (feltsp l f) (feltsp q f))
           (equal (conv (cmul c l f) q i f) (fmul c (conv l q i f) f)))
  :hints (("Goal" :induct (len l))))

(defthm conv-cmul-r
  (implies (and (fap f) (feltp c f) (feltsp l f) (feltsp q f))
           (equal (conv l (cmul c q f) i f) (fmul c (conv l q i f) f))))

(defthm conv-append-zero
  (implies (and (fap f) (feltsp l f) (feltsp q f))
           (equal (conv (append l (list (fzero f))) q i f)
                  (if (zp i) (fzero f) (conv l q (1- i) f)))))

(defthm conv-pshift-l
  (implies (and (fap f) (feltsp l f) (feltsp q f))
           (equal (conv (pshift l k f) q i f)
                  (if (< (nfix i) (nfix k)) (fzero f) (conv l q (- (nfix i) (nfix k)) f))))
  :hints (("Goal" :induct (pshift l k f))))

(defthm conv-pzero-l
  (implies (and (fap f) (feltsp q f))
           (equal (conv (pzero f) q i f) (fzero f)))
  :hints (("Goal" :in-theory (enable pzero))))

(defthm conv-pzero-r
  (implies (and (fap f) (feltsp l f))
           (equal (conv l (pzero f) i f) (fzero f))))

(defthm conv-pone-l
  (implies (and (fap f) (feltsp q f))
           (equal (conv (pone f) q i f) (pco q i f)))
  :hints (("Goal" :in-theory (enable pone))))

(defthm conv-monomial-l
  (implies (and (fap f) (feltp c f) (feltsp q f))
           (equal (conv (monomial c k f) q i f)
                  (if (< (nfix i) (nfix k)) (fzero f) (fmul c (pco q (- (nfix i) (nfix k)) f) f))))
  :hints (("Goal" :in-theory (enable monomial))))

(defthm csum-monomial-r
  (implies (and (fap f) (feltp c f) (feltsp l f) (natp i) (natp j) (natp k) (<= j i))
           (equal (csum l (monomial c k f) i j f)
                  (if (and (<= k i) (<= (- i k) j)) (fmul (pco l (- i k) f) c f) (fzero f))))
  :hints (("Goal" :induct (csum l q i j f))))

(defthm conv-monomial-r
  (implies (and (fap f) (feltp c f) (feltsp l f))
           (equal (conv l (monomial c k f) i f)
                  (if (< (nfix i) (nfix k)) (fzero f) (fmul (pco l (- (nfix i) (nfix k)) f) c f))))
  :hints (("Goal" :use ((:instance conv-csum (q (monomial c k f)) (i (nfix i)))
                        (:instance conv-nfix (q (monomial c k f)))
                        (:instance csum-monomial-r (i (nfix i)) (j (nfix i)) (k (nfix k)))
                        (:instance monomial-nfix))
           :in-theory (disable conv-nfix csum-monomial-r monomial-nfix))))

(defthm conv-beyond
  (implies (and (fap f) (feltsp l f) (feltsp q f)
                (<= (+ (len l) (len q)) (+ 1 (nfix i))))
           (equal (conv l q i f) (fzero f))))

(defthm conv-top
  (implies (and (fap f) (feltsp p f) (feltsp q f) (consp p) (consp q))
           (equal (conv p q (+ (len (cdr p)) (len (cdr q))) f)
                  (fmul (car p) (car q) f)))
  :hints (("Goal" :expand ((conv p q (+ (len (cdr p)) (len (cdr q))) f)))))

;;; pmul basics

(defthm pmul-pzero-l (equal (pmul (pzero f) q f) (pzero f)))
(defthm pmul-pzero-r (equal (pmul p (pzero f) f) (pzero f)))

(defun len-induct (p f)
  (declare (xargs :measure (len p)))
  (if (and (consp p) (consp (cdr p)))
      (len-induct (pstrip (cdr p) f) f)
    t))

(defthm polyp-pmul-and-pco
  (implies (and (fap f) (polyp p f) (polyp q f))
           (and (polyp (pmul p q f) f)
                (equal (pco (pmul p q f) i f) (conv p q i f))))
  :hints (("Goal" :induct (len-induct p f) :expand ((pmul p q f)))))

(defthm polyp-pmul
  (implies (and (fap f) (polyp p f) (polyp q f)) (polyp (pmul p q f) f)))

(defthm pco-pmul
  (implies (and (fap f) (polyp p f) (polyp q f))
           (equal (pco (pmul p q f) i f) (conv p q i f))))

(defthm consp-pmul
  (implies (and (fap f) (polyp p f) (polyp q f)) (consp (pmul p q f)))
  :hints (("Goal" :use ((:instance polyp-consp (p (pmul p q f))) (:instance polyp-pmul)))))

(in-theory (disable pmul))

(defthm pmul-padd-l
  (implies (and (fap f) (polyp x f) (polyp y f) (polyp q f))
           (equal (pmul (padd x y f) q f) (padd (pmul x q f) (pmul y q f) f)))
  :hints (("Goal" :use ((:instance poly-ext (p (pmul (padd x y f) q f)) (q (padd (pmul x q f) (pmul y q f) f)))))))

(defthm pmul-padd-r
  (implies (and (fap f) (polyp x f) (polyp y f) (polyp q f))
           (equal (pmul q (padd x y f) f) (padd (pmul q x f) (pmul q y f) f)))
  :hints (("Goal" :use ((:instance poly-ext (p (pmul q (padd x y f) f)) (q (padd (pmul q x f) (pmul q y f) f)))))))

(defthm pmul-pneg-l
  (implies (and (fap f) (polyp x f) (polyp q f))
           (equal (pmul (pneg x f) q f) (pneg (pmul x q f) f)))
  :hints (("Goal" :use ((:instance poly-ext (p (pmul (pneg x f) q f)) (q (pneg (pmul x q f) f)))))))

(defthm pmul-pneg-r
  (implies (and (fap f) (polyp x f) (polyp q f))
           (equal (pmul q (pneg x f) f) (pneg (pmul q x f) f)))
  :hints (("Goal" :use ((:instance poly-ext (p (pmul q (pneg x f) f)) (q (pneg (pmul q x f) f)))))))

(defthm pmul-cmul-l
  (implies (and (fap f) (feltp c f) (polyp x f) (polyp q f))
           (equal (pmul (cmul c x f) q f) (cmul c (pmul x q f) f)))
  :hints (("Goal" :use ((:instance poly-ext (p (pmul (cmul c x f) q f)) (q (cmul c (pmul x q f) f)))))))

(defthm pmul-cmul-r
  (implies (and (fap f) (feltp c f) (polyp x f) (polyp q f))
           (equal (pmul q (cmul c x f) f) (cmul c (pmul q x f) f)))
  :hints (("Goal" :use ((:instance poly-ext (p (pmul q (cmul c x f) f)) (q (cmul c (pmul q x f) f)))))))

(defthm pmul-pone-l
  (implies (and (fap f) (polyp q f)) (equal (pmul (pone f) q f) q))
  :hints (("Goal" :use ((:instance poly-ext (p (pmul (pone f) q f)) (q q))))))

(defthm conv-pone-r
  (implies (and (fap f) (feltsp l f))
           (equal (conv l (pone f) i f) (pco l i f))))

(defthm pmul-pone-r
  (implies (and (fap f) (polyp q f)) (equal (pmul q (pone f) f) q))
  :hints (("Goal" :use ((:instance poly-ext (p (pmul q (pone f) f)) (q q))))))

;; splitting off the leading term

(defthm pco-split
  (implies (consp p)
           (equal (pco p j f)
                  (if (equal (nfix j) (len (cdr p))) (car p) (pco (cdr p) j f))))
  :rule-classes nil)

(defthmd conv-split-r
  (implies (and (fap f) (feltsp l f) (feltsp p f) (consp p))
           (equal (conv l p i f)
                  (fadd (conv l (monomial (car p) (len (cdr p)) f) i f)
                        (conv l (cdr p) i f) f)))
  :hints (("Goal" :induct (conv l p i f))
          ("Subgoal *1/1" :use ((:instance pco-split (j (+ (nfix i) (- (len (cdr l))))))))))

(defthm pmul-split-l
  (implies (and (fap f) (polyp p f) (polyp q f) (consp (cdr p)))
           (equal (pmul p q f)
                  (padd (pmul (monomial (car p) (len (cdr p)) f) q f)
                        (pmul (pstrip (cdr p) f) q f) f)))
  :hints (("Goal" :use ((:instance poly-ext (p (pmul p q f)) (q (padd (pmul (monomial (car p) (len (cdr p)) f) q f)
                                  (pmul (pstrip (cdr p) f) q f) f))))
           :expand ((conv p q (pwitness (pmul p q f)
                                       (padd (pmul (monomial (car p) (len (cdr p)) f) q f)
                                             (pmul (pstrip (cdr p) f) q f) f)) f))))
  :rule-classes nil)

(defthm pmul-split-r
  (implies (and (fap f) (polyp p f) (polyp q f) (consp (cdr p)))
           (equal (pmul q p f)
                  (padd (pmul q (monomial (car p) (len (cdr p)) f) f)
                        (pmul q (pstrip (cdr p) f) f) f)))
  :hints (("Goal" :use ((:instance poly-ext (p (pmul q p f)) (q (padd (pmul q (monomial (car p) (len (cdr p)) f) f)
                                  (pmul q (pstrip (cdr p) f) f) f)))
                        (:instance conv-split-r (l q)
                                   (i (pwitness (pmul q p f) (padd (pmul q (monomial (car p) (len (cdr p)) f) f)
                                                                   (pmul q (pstrip (cdr p) f) f) f)))))
           :in-theory (disable padd-comm)))
  :rule-classes nil)

(defthm pmul-comm-mono
  (implies (and (fap f) (feltp c f) (not (equal c (fzero f))) (polyp q f))
           (equal (pmul (monomial c k f) q f) (pmul q (monomial c k f) f)))
  :hints (("Goal" :use ((:instance poly-ext (p (pmul (monomial c k f) q f)) (q (pmul q (monomial c k f) f)))))))

(defthm const-poly-monomial
  (implies (and (polyp p f) (not (consp (cdr p))))
           (equal (monomial (car p) 0 f) p))
  :hints (("Goal" :in-theory (enable monomial polyp))))

(defthm pmul-comm
  (implies (and (fap f) (polyp p f) (polyp q f))
           (equal (pmul p q f) (pmul q p f)))
  :hints (("Goal" :induct (len-induct p f))
          ("Subgoal *1/2" :use ((:instance pmul-comm-mono (c (car p)) (k 0)))
                          :cases ((equal p (pzero f))))
          ("Subgoal *1/2.2" :in-theory (enable pzero polyp))
          ("Subgoal *1/1" :use (pmul-split-l pmul-split-r
                                (:instance pmul-comm-mono (c (car p)) (k (len (cdr p)))))))
  :rule-classes ((:rewrite :loop-stopper ((p q)))))

(defthm pmul-monomial
  (implies (and (fap f) (feltp c f) (not (equal c (fzero f))) (polyp q f))
           (equal (pmul (monomial c k f) q f) (pstrip (pshift (cmul c q f) k f) f)))
  :hints (("Goal" :use ((:instance poly-ext (p (pmul (monomial c k f) q f)) (q (pstrip (pshift (cmul c q f) k f) f)))))))

(defthm pmul-assoc-mono
  (implies (and (fap f) (feltp c f) (not (equal c (fzero f))) (polyp q f) (polyp r f))
           (equal (pmul (pmul (monomial c k f) q f) r f)
                  (pmul (monomial c k f) (pmul q r f) f)))
  :hints (("Goal" :use ((:instance poly-ext (p (pmul (pmul (monomial c k f) q f) r f)) (q (pmul (monomial c k f) (pmul q r f) f))))
           :in-theory (disable pmul-comm))))

(defthm poly-decomp
  (implies (and (fap f) (polyp p f) (consp (cdr p)))
           (equal (padd (monomial (car p) (len (cdr p)) f) (pstrip (cdr p) f) f) p))
  :hints (("Goal" :use ((:instance poly-ext (p (padd (monomial (car p) (len (cdr p)) f) (pstrip (cdr p) f) f)) (q p))
                        (:instance pco-split (j (pwitness (padd (monomial (car p) (len (cdr p)) f) (pstrip (cdr p) f) f) p)))))))

(defthm assoc-step-gen
  (implies (and (fap f) (polyp a f) (polyp b f) (polyp q f) (polyp r f)
                (equal pp (padd a b f))
                (equal (pmul (pmul a q f) r f) (pmul a (pmul q r f) f))
                (equal (pmul (pmul b q f) r f) (pmul b (pmul q r f) f)))
           (equal (pmul (pmul pp q f) r f) (pmul pp (pmul q r f) f)))
  :hints (("Goal" :in-theory (disable pmul-comm pmul-monomial)))
  :rule-classes nil)

(defthm pmul-assoc
  (implies (and (fap f) (polyp p f) (polyp q f) (polyp r f))
           (equal (pmul (pmul p q f) r f) (pmul p (pmul q r f) f)))
  :hints (("Goal" :induct (len-induct p f) :in-theory (disable pmul-comm pmul-monomial))
          ("Subgoal *1/2" :use ((:instance pmul-assoc-mono (c (car p)) (k 0)))
                          :cases ((equal p (pzero f))))
          ("Subgoal *1/2.2" :in-theory (enable pzero polyp))
          ("Subgoal *1/1" :use ((:instance assoc-step-gen (pp p) (a (monomial (car p) (len (cdr p)) f))
                                           (b (pstrip (cdr p) f)))
                                (:instance pmul-assoc-mono (c (car p)) (k (len (cdr p))))))))

(defthm pmul-comm2
  (implies (and (fap f) (polyp p f) (polyp q f) (polyp r f))
           (equal (pmul p (pmul q r f) f) (pmul q (pmul p r f) f)))
  :hints (("Goal" :use ((:instance pmul-assoc)
                        (:instance pmul-assoc (p q) (q p))
                        (:instance pmul-comm (q q)))
           :in-theory (disable pmul-assoc pmul-comm)))
  :rule-classes ((:rewrite :loop-stopper ((p q)))))

;;; degree of product

(defthm pco-nonzero-bound
  (implies (and (polyp r f) (not (equal (pco r d f) (fzero f))))
           (< (nfix d) (len r)))
  :rule-classes nil)

(defthm car-nonzero-poly
  (implies (and (polyp g f) (not (equal g (pzero f))))
           (not (equal (car g) (fzero f))))
  :hints (("Goal" :in-theory (enable polyp pzero))))

(defthm polyp-top-nonzero
  (implies (and (polyp r f) (consp (cdr r)))
           (not (equal (pco r (len (cdr r)) f) (fzero f))))
  :hints (("Goal" :use ((:instance pco-top (l r))) :in-theory (disable pco-top))))

(defthm pmul-nonzero-len
  (implies (and (fap f) (polyp p f) (polyp q f)
                (not (equal p (pzero f))) (not (equal q (pzero f))))
           (equal (len (cdr (pmul p q f))) (+ (len (cdr p)) (len (cdr q)))))
  :hints (("Goal" :use ((:instance pco-nonzero-bound (r (pmul p q f))
                                   (d (+ (len (cdr p)) (len (cdr q)))))
                        (:instance polyp-top-nonzero (r (pmul p q f)))
                        (:instance conv-beyond (l p) (q q) (i (len (cdr (pmul p q f))))))
           :in-theory (disable polyp-top-nonzero conv-beyond)
           :do-not-induct t))
  :rule-classes nil)

(defthm pmul-nonzero-props
  (implies (and (fap f) (polyp p f) (polyp q f)
                (not (equal p (pzero f))) (not (equal q (pzero f))))
           (and (equal (len (pmul p q f)) (+ -1 (len p) (len q)))
                (equal (car (pmul p q f)) (fmul (car p) (car q) f))))
  :hints (("Goal" :use ((:instance pmul-nonzero-len)
                        (:instance pco-top (l (pmul p q f))))
           :in-theory (disable pco-top)
           :do-not-induct t)))

(defthm len-pmul
  (implies (and (fap f) (polyp p f) (polyp q f)
                (not (equal p (pzero f))) (not (equal q (pzero f))))
           (equal (len (pmul p q f)) (+ -1 (len p) (len q)))))

(defthm car-pmul
  (implies (and (fap f) (polyp p f) (polyp q f)
                (not (equal p (pzero f))) (not (equal q (pzero f))))
           (equal (car (pmul p q f)) (fmul (car p) (car q) f))))

(defthm const-zero-pzero
  (implies (and (polyp r f) (not (consp (cdr r))) (equal (car r) (fzero f)))
           (equal r (pzero f)))
  :hints (("Goal" :in-theory (enable polyp pzero)))
  :rule-classes nil)

(defthm pmul-zero-iff
  (implies (and (fap f) (polyp p f) (polyp q f))
           (equal (equal (pmul p q f) (pzero f))
                  (or (equal p (pzero f)) (equal q (pzero f)))))
  :hints (("Goal" :use ((:instance pmul-nonzero-props)
                        (:instance car-nonzero-poly (g p))
                        (:instance car-nonzero-poly (g q))
                        (:instance const-zero-pzero (r p))
                        (:instance const-zero-pzero (r q)))
           :in-theory (disable pmul-nonzero-props len-pmul car-pmul car-nonzero-poly))))

(in-theory (disable pmul-monomial cmul pmul-comm-mono pmul-assoc-mono))

;;;;;;;;;;;;;;;;;;;; part 5 ;;;;;;;;;;;;;;;;;;;;


;;;; ===================== Division =====================

(defthm len-cons-x (equal (len (cons a b)) (+ 1 (len b))))
(defthm len-atom-x (implies (not (consp x)) (equal (len x) 0)))
(defthm len-consp-pos (implies (consp x) (< 0 (len x))) :rule-classes :linear)
(defthm len-cdr-x (implies (consp x) (equal (len (cdr x)) (+ -1 (len x)))))
(defthm len-1-x (implies (and (consp x) (not (consp (cdr x)))) (equal (len x) 1)))
(defthm len-cdr-consp (implies (consp (cdr x)) (< 1 (len x))) :rule-classes :linear
  :hints (("Goal" :expand ((len x) (len (cdr x))))))
(in-theory (disable len))
(in-theory (enable (:induction len)))

(defthm len-padd-pneg-cancel
  (implies (and (fap f) (polyp a f) (polyp b f)
                (equal (len a) (len b)) (equal (car a) (car b)) (consp (cdr a)))
           (< (len (padd a (pneg b f) f)) (len a)))
  :hints (("Goal" :use ((:instance polyp-top-nonzero (r (padd a (pneg b f) f)))
                        (:instance pco-top (l a))
                        (:instance pco-top (l b)))
           :in-theory (disable polyp-top-nonzero pco-top)
           :cases ((equal (len (cdr (padd a (pneg b f) f))) (len (cdr a))))))
  :rule-classes :linear)

(defthm feltp-car-poly
  (implies (polyp p f) (feltp (car p) f))
  :hints (("Goal" :in-theory (enable polyp))))

(defthm nonconst-not-pzero
  (implies (consp (cdr p)) (not (equal p (pzero f))))
  :hints (("Goal" :in-theory (enable pzero))))

(defthm car-not-pzero
  (implies (not (equal (car p) (fzero f))) (not (equal p (pzero f))))
  :hints (("Goal" :in-theory (enable pzero))))

(defthm consp-cdr-from-len
  (implies (and (consp (cdr y)) (<= (len y) (len x))) (consp (cdr x)))
  :rule-classes nil)

(defthm quot-coef-props
  (implies (and (fap f) (polyp x f) (polyp y f) (<= (len y) (len x)) (consp (cdr y)))
           (and (feltp (fmul (car x) (frecip (car y) f) f) f)
                (not (equal (fmul (car x) (frecip (car y) f) f) (fzero f)))
                (equal (fmul (fmul (car x) (frecip (car y) f) f) (car y) f) (car x))
                (polyp (monomial (fmul (car x) (frecip (car y) f) f) k f) f)))
  :hints (("Goal" :use consp-cdr-from-len)))

(defthm div-step-facts
  (implies (and (fap f) (polyp x f) (polyp y f) (consp (cdr y)) (>= (len x) (len y))
                (equal k (+ (len x) (- (len y)))))
           (and (polyp (pmul (monomial (fmul (car x) (frecip (car y) f) f)
                                       k f) y f) f)
                (equal (len (pmul (monomial (fmul (car x) (frecip (car y) f) f)
                                            k f) y f))
                       (len x))
                (equal (car (pmul (monomial (fmul (car x) (frecip (car y) f) f)
                                            k f) y f))
                       (car x))))
  :hints (("Goal" :use ((:instance quot-coef-props)
                        (:instance len-pmul (p (monomial (fmul (car x) (frecip (car y) f) f)
                                                         k f)) (q y))
                        (:instance car-pmul (p (monomial (fmul (car x) (frecip (car y) f) f)
                                                         k f)) (q y)))
           :in-theory (disable quot-coef-props len-pmul car-pmul pmul-monomial)
           :do-not-induct t)))

(defthm div-step-len
  (implies (and (fap f) (polyp x f) (polyp y f) (consp (cdr y)) (>= (len x) (len y))
                (equal k (+ (len x) (- (len y)))))
           (< (len (padd x (pneg (pmul (monomial (fmul (car x) (frecip (car y) f) f)
                                                 k f)
                                       y f) f) f))
              (len x)))
  :hints (("Goal" :use ((:instance len-padd-pneg-cancel
                                   (a x)
                                   (b (pmul (monomial (fmul (car x) (frecip (car y) f) f)
                                                      k f)
                                            y f)))
                        (:instance div-step-facts))
           :in-theory (disable len-padd-pneg-cancel div-step-facts pmul-monomial)
           :do-not-induct t))
  :rule-classes :linear)

(defun div-induct (x y f)
  (declare (xargs :measure (len x)))
  (if (or (not (consp (cdr y))) (< (len x) (len y)))
      t
    (let* ((c (fmul (car x) (frecip (car y) f) f))
           (m (monomial c (+ (len x) (- (len y))) f))
           (x1 (padd x (pneg (pmul m y f) f) f)))
      (if (< (len x1) (len x))
          (div-induct x1 y f)
        t))))


(defthm pdivide-correct
  (implies (and (fap f) (polyp x f) (polyp y f) (consp (cdr y)))
           (and (polyp (mv-nth 0 (pdivide x y f)) f)
                (polyp (mv-nth 1 (pdivide x y f)) f)
                (< (len (mv-nth 1 (pdivide x y f))) (len y))
                (equal (padd (pmul (mv-nth 0 (pdivide x y f)) y f)
                             (mv-nth 1 (pdivide x y f)) f)
                       x)))
  :hints (("Goal" :induct (div-induct x y f)
           :in-theory (disable pmul-comm)
           :expand ((pdivide x y f)))))

(defthm polyp-prem
  (implies (and (fap f) (polyp x f) (polyp y f) (consp (cdr y)))
           (polyp (prem x y f) f))
  :hints (("Goal" :use ((:instance pdivide-correct)) :do-not-induct t :in-theory (e/d (prem) (mv-nth pdivide-correct)))))

(defthm polyp-pquot
  (implies (and (fap f) (polyp x f) (polyp y f) (consp (cdr y)))
           (polyp (pquot x y f) f))
  :hints (("Goal" :use ((:instance pdivide-correct)) :do-not-induct t :in-theory (e/d (pquot) (mv-nth pdivide-correct)))))

(defthm len-prem
  (implies (and (fap f) (polyp x f) (polyp y f) (consp (cdr y)))
           (< (len (prem x y f)) (len y)))
  :hints (("Goal" :use ((:instance pdivide-correct)) :do-not-induct t :in-theory (e/d (prem) (mv-nth pdivide-correct))))
  :rule-classes :linear)

(defthm prem-pquot
  (implies (and (fap f) (polyp x f) (polyp y f) (consp (cdr y)))
           (equal (padd (pmul (pquot x y f) y f) (prem x y f) f) x))
  :hints (("Goal" :use ((:instance pdivide-correct)) :do-not-induct t :in-theory (e/d (prem pquot) (mv-nth pdivide-correct)))))

(defthm padd-move
  (implies (and (fap f) (polyp a f) (polyp b f) (polyp c f) (polyp d f)
                (equal (padd a b f) (padd c d f)))
           (equal (padd a (pneg c f) f) (padd d (pneg b f) f)))
  :hints (("Goal" :use ((:instance padd-cancel (x (padd b c f)) (y (padd a (pneg c f) f))
                                   (z (padd d (pneg b f) f))))
           :in-theory (disable padd-cancel)))
  :rule-classes nil)

(defthm len-padd-pneg-bound
  (implies (and (fap f) (polyp a f) (polyp b f))
           (<= (len (padd a (pneg b f) f)) (max (len a) (len b))))
  :rule-classes :linear)

(defthm pmul-diff
  (implies (and (fap f) (polyp q1 f) (polyp q2 f) (polyp y f))
           (equal (pmul (padd q1 (pneg q2 f) f) y f)
                  (padd (pmul q1 y f) (pneg (pmul q2 y f) f) f)))
  :rule-classes nil)

(defthm diff-zero
  (implies (and (fap f) (polyp q1 f) (polyp q2 f) (equal (padd q1 (pneg q2 f) f) (pzero f)))
           (equal q1 q2))
  :hints (("Goal" :use ((:instance padd-zero-iff (x q1) (y (pneg q2 f)))
                        (:instance pneg-pneg (x q1)) (:instance pneg-pneg (x q2)))
           :in-theory (disable padd-zero-iff pneg-pneg padd-comm)))
  :rule-classes nil)

(defthm div-unique-q
  (implies (and (fap f) (polyp y f) (consp (cdr y))
                (polyp q1 f) (polyp r1 f) (polyp q2 f) (polyp r2 f)
                (< (len r1) (len y)) (< (len r2) (len y))
                (equal (padd (pmul q1 y f) r1 f) (padd (pmul q2 y f) r2 f)))
           (equal q1 q2))
  :hints (("Goal" :use ((:instance padd-move (a (pmul q1 y f)) (b r1) (c (pmul q2 y f)) (d r2))
                        (:instance pmul-diff)
                        (:instance diff-zero)
                        (:instance len-pmul (p (padd q1 (pneg q2 f) f)) (q y))
                        (:instance len-padd-pneg-bound (a r2) (b r1)))
           :in-theory (disable len-pmul len-padd-pneg-bound padd-comm padd-comm2 padd-assoc pmul-padd-l pmul-pneg-l
                               pmul-padd-r pmul-pneg-r padd-zero-iff padd-cancel padd-cancel-r pmul-comm)
           :do-not-induct t))
  :rule-classes nil)

(defthm div-unique
  (implies (and (fap f) (polyp y f) (consp (cdr y))
                (polyp q1 f) (polyp r1 f) (polyp q2 f) (polyp r2 f)
                (< (len r1) (len y)) (< (len r2) (len y))
                (equal (padd (pmul q1 y f) r1 f) (padd (pmul q2 y f) r2 f)))
           (and (equal q1 q2) (equal r1 r2)))
  :hints (("Goal" :use (div-unique-q)))
  :rule-classes nil)

(defthm prem-unique
  (implies (and (fap f) (polyp y f) (consp (cdr y))
                (polyp q f) (polyp r f) (< (len r) (len y)))
           (and (equal (prem (padd (pmul q y f) r f) y f) r)
                (equal (pquot (padd (pmul q y f) r f) y f) q)))
  :hints (("Goal" :use ((:instance div-unique (q1 q) (r1 r)
                                   (q2 (pquot (padd (pmul q y f) r f) y f))
                                   (r2 (prem (padd (pmul q y f) r f) y f))))
           :in-theory (disable prem-pquot)
           :do-not-induct t)
          ("Goal'" :use ((:instance prem-pquot (x (padd (pmul q y f) r f)))))))

(defthm prem-small
  (implies (and (fap f) (polyp y f) (consp (cdr y)) (polyp r f) (< (len r) (len y)))
           (equal (prem r y f) r))
  :hints (("Goal" :use ((:instance prem-unique (q (pzero f)))))))

(defthm prem-multiple
  (implies (and (fap f) (polyp y f) (consp (cdr y)) (polyp q f))
           (equal (prem (pmul q y f) y f) (pzero f)))
  :hints (("Goal" :use ((:instance prem-unique (r (pzero f)))))))

(defthm prem-padd
  (implies (and (fap f) (polyp y f) (consp (cdr y)) (polyp a f) (polyp b f))
           (equal (prem (padd a b f) y f) (padd (prem a y f) (prem b y f) f)))
  :hints (("Goal" :use ((:instance prem-unique (q (padd (pquot a y f) (pquot b y f) f))
                                   (r (padd (prem a y f) (prem b y f) f)))
                        (:instance prem-pquot (x a))
                        (:instance prem-pquot (x b))
                        (:instance len-padd (x (prem a y f)) (y (prem b y f)))
                        (:instance len-prem (x a))
                        (:instance len-prem (x b)))
           :in-theory (disable prem-unique prem-pquot len-padd len-prem))))

(defthm prem-shift
  (implies (and (fap f) (polyp y f) (consp (cdr y)) (polyp k f) (polyp r f))
           (equal (prem (padd (pmul k y f) r f) y f) (prem r y f)))
  :hints (("Goal" :in-theory (disable pmul-comm padd-comm))))

(defthm pmul-swap-y
  (implies (and (fap f) (polyp q f) (polyp y f) (polyp b f))
           (equal (pmul (pmul q y f) b f) (pmul (pmul q b f) y f)))
  :rule-classes nil)

(defthm prem-pmul-aux
  (implies (and (fap f) (polyp y f) (consp (cdr y)) (polyp q f) (polyp r f) (polyp b f)
                (equal a (padd (pmul q y f) r f)))
           (equal (prem (pmul a b f) y f) (prem (pmul r b f) y f)))
  :hints (("Goal" :use ((:instance pmul-swap-y))
           :in-theory (disable pmul-comm pmul-assoc padd-comm pmul-comm2 padd-comm2)))
  :rule-classes nil)

(defthm prem-pmul-prem-l
  (implies (and (fap f) (polyp y f) (consp (cdr y)) (polyp a f) (polyp b f))
           (equal (prem (pmul (prem a y f) b f) y f) (prem (pmul a b f) y f)))
  :hints (("Goal" :use ((:instance prem-pmul-aux (q (pquot a y f)) (r (prem a y f)))
                        (:instance prem-pquot (x a)))
           :in-theory (disable prem-pquot pmul-comm padd-comm))))

(defthm prem-pmul-prem-r
  (implies (and (fap f) (polyp y f) (consp (cdr y)) (polyp a f) (polyp b f))
           (equal (prem (pmul b (prem a y f) f) y f) (prem (pmul b a f) y f)))
  :hints (("Goal" :use ((:instance prem-pmul-prem-l)
                        (:instance pmul-comm (p b) (q (prem a y f)))
                        (:instance pmul-comm (p b) (q a)))
           :in-theory (disable prem-pmul-prem-l pmul-comm))))

(defthm prem-prem
  (implies (and (fap f) (polyp y f) (consp (cdr y)) (polyp a f))
           (equal (prem (prem a y f) y f) (prem a y f))))

(defthm div-step-len-c
  (implies (and (fap f) (polyp x f) (polyp y f) (consp (cdr y)) (>= (len x) (len y))
                (equal k (+ (len x) (- (len y)))))
           (< (len (padd x (pneg (pmul y (monomial (fmul (car x) (frecip (car y) f) f) k f) f) f) f))
              (len x)))
  :hints (("Goal" :use ((:instance div-step-len))
           :in-theory (disable div-step-len)))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;; part 6 ;;;;;;;;;;;;;;;;;;;;


;;;; ===================== GCD, Bezout, inverses =====================

(defun gcd-induct (p q f)
  (declare (xargs :measure (+ (len p) (len q))))
  (if (equal p (pzero f))
      t
    (if (or (equal q (pzero f)) (pconstp p))
        t
      (if (pconstp q)
          t
        (if (>= (degree p) (degree q))
            (let* ((c (fmul (car p) (frecip (car q) f) f))
                   (a (monomial c (- (degree p) (degree q)) f))
                   (pnew (padd p (pneg (pmul a q f) f) f)))
              (if (< (len pnew) (len p))
                  (gcd-induct pnew q f)
                t))
          (let* ((c (fmul (car q) (frecip (car p) f) f))
                 (a (monomial c (- (degree q) (degree p)) f))
                 (qnew (padd q (pneg (pmul a p f) f) f)))
            (if (< (len qnew) (len q))
                (gcd-induct p qnew f)
              t)))))))

(defun gcd-cof (p q f)
  (declare (xargs :measure (+ (len p) (len q))))
  (if (equal p (pzero f))
      (cons (pzero f) (pone f))
    (if (equal q (pzero f))
        (cons (pone f) (pzero f))
      (if (pconstp p)
          (cons (pone f) (cmul (frecip (car p) f) q f))
        (if (pconstp q)
            (cons (cmul (frecip (car q) f) p f) (pone f))
          (if (>= (degree p) (degree q))
              (let* ((c (fmul (car p) (frecip (car q) f) f))
                     (a (monomial c (- (degree p) (degree q)) f))
                     (pnew (padd p (pneg (pmul a q f) f) f)))
                (if (< (len pnew) (len p))
                    (let ((r (gcd-cof pnew q f)))
                      (cons (padd (car r) (pmul a (cdr r) f) f) (cdr r)))
                  nil))
            (let* ((c (fmul (car q) (frecip (car p) f) f))
                   (a (monomial c (- (degree q) (degree p)) f))
                   (qnew (padd q (pneg (pmul a p f) f) f)))
              (if (< (len qnew) (len q))
                  (let ((r (gcd-cof p qnew f)))
                    (cons (car r) (padd (cdr r) (pmul a (car r) f) f)))
                nil))))))))

(defthm monomial-c-nonzero
  (implies (and (fap f) (polyp x f) (polyp y f) (consp (cdr x)) (consp (cdr y)))
           (and (feltp (fmul (car x) (frecip (car y) f) f) f)
                (not (equal (fmul (car x) (frecip (car y) f) f) (fzero f))))))

(defthm gcd-polyp
  (implies (and (fap f) (polyp p f) (polyp q f))
           (and (polyp (pgcd-aux p q f) f)
                (polyp (r$-aux p q f) f)
                (polyp (s$-aux p q f) f)
                (polyp (car (gcd-cof p q f)) f)
                (polyp (cdr (gcd-cof p q f)) f)))
  :hints (("Goal" :induct (gcd-induct p q f)
           :expand ((pgcd-aux p q f) (r$-aux p q f) (s$-aux p q f) (gcd-cof p q f)))))

(defthm bezout
  (implies (and (fap f) (polyp p f) (polyp q f))
           (equal (padd (pmul (r$-aux p q f) p f) (pmul (s$-aux p q f) q f) f)
                  (pgcd-aux p q f)))
  :hints (("Goal" :induct (gcd-induct p q f)
           :expand ((pgcd-aux p q f) (r$-aux p q f) (s$-aux p q f)))))

(defthm pmul-const-r
  (implies (and (fap f) (polyp q f) (polyp p f) (not (consp (cdr p))))
           (equal (pmul q p f) (cmul (car p) q f)))
  :hints (("Goal" :use ((:instance const-poly-monomial))
           :in-theory (disable const-poly-monomial)
           :cases ((equal (car p) (fzero f))))
          ("Subgoal 2" :use ((:instance poly-ext (p (pmul q (monomial (car p) 0 f) f)) (q (cmul (car p) q f)))))
          ("Subgoal 1" :use ((:instance const-zero-pzero (r p))))))

(defthm cmul-pone-const
  (implies (and (fap f) (polyp p f) (not (consp (cdr p))))
           (equal (cmul (car p) (pone f) f) p))
  :hints (("Goal" :use ((:instance poly-ext (p (cmul (car p) (pone f) f)) (q p))))))

(defthm gcd-cof-correct
  (implies (and (fap f) (polyp p f) (polyp q f))
           (and (equal (pmul (car (gcd-cof p q f)) (pgcd-aux p q f) f) p)
                (equal (pmul (cdr (gcd-cof p q f)) (pgcd-aux p q f) f) q)))
  :hints (("Goal" :induct (gcd-induct p q f)
           :expand ((pgcd-aux p q f) (gcd-cof p q f)))))

;;;;;;;;;;;;;;;;;;;; part 7 ;;;;;;;;;;;;;;;;;;;;


;;;; ===================== Irreducible => gcd constant; MAIN-1 =====================

(defthm reduciblep-intro
  (implies (and (polyp q f) (monicp q f) (> (degree q) 0) (< (degree q) (degree p))
                (pdivides q p f))
           (reduciblep p f))
  :hints (("Goal" :use ((:instance pfactor)) :in-theory (enable reduciblep))))

(defthm car-cmul-recip
  (implies (and (fap f) (polyp g f) (not (equal g (pzero f))))
           (equal (car (cmul (frecip (car g) f) g f)) (fone f)))
  :hints (("Goal" :in-theory (enable polyp pzero)
           :cases ((equal (car g) (fzero f))))))

(defthm cmul-recip-cmul
  (implies (and (fap f) (polyp g f) (not (equal g (pzero f))))
           (equal (cmul (car g) (cmul (frecip (car g) f) g f) f) g)))

(defthm gcd-nonzero
  (implies (and (fap f) (polyp m f) (polyp x f) (not (equal x (pzero f))))
           (not (equal (pgcd-aux x m f) (pzero f))))
  :hints (("Goal" :use ((:instance gcd-cof-correct (p x) (q m)))
           :in-theory (disable gcd-cof-correct))))

(defund monic-of (g f) (cmul (frecip (car g) f) g f))

(defthm monic-of-props
  (implies (and (fap f) (polyp g f) (not (equal g (pzero f))))
           (and (polyp (monic-of g f) f)
                (monicp (monic-of g f) f)
                (equal (len (monic-of g f)) (len g))
                (equal (cmul (car g) (monic-of g f) f) g)))
  :hints (("Goal" :in-theory (enable monic-of monicp))))

(defthm pmul-k-g
  (implies (and (fap f) (polyp g f) (not (equal g (pzero f))) (polyp k f))
           (equal (pmul (cmul (car g) k f) (monic-of g f) f) (pmul k g f)))
  :hints (("Goal" :use ((:instance pmul-cmul-r (c (car g)) (x (monic-of g f)) (q k))
                        (:instance monic-of-props))
           :in-theory (disable pmul-cmul-r monic-of-props pmul-comm))))

(defthm divides-monic-of
  (implies (and (fap f) (polyp g f) (not (equal g (pzero f))) (consp (cdr g))
                (polyp k f) (equal m (pmul k g f)))
           (pdivides (monic-of g f) m f))
  :hints (("Goal" :in-theory (e/d (pdivides) (monic-of-props pmul-cmul-l pmul-comm prem-multiple))
           :use ((:instance monic-of-props)
                 (:instance prem-multiple (y (monic-of g f)) (q (cmul (car g) k f)))))))

(defthm gcd-const-lemma
  (implies (and (fap f) (polyp m f) (consp (cdr m)) (not (reduciblep m f))
                (polyp x f) (not (equal x (pzero f))) (< (len x) (len m)))
           (and (not (consp (cdr (pgcd-aux x m f))))
                (not (equal (pgcd-aux x m f) (pzero f)))))
  :hints (("Goal" :use ((:instance gcd-cof-correct (p x) (q m))
                        (:instance gcd-nonzero)
                        (:instance reduciblep-intro (p m) (q (monic-of (pgcd-aux x m f) f)))
                        (:instance divides-monic-of (g (pgcd-aux x m f)) (k (cdr (gcd-cof x m f))))
                        (:instance monic-of-props (g (pgcd-aux x m f)))
                        (:instance len-pmul (p (car (gcd-cof x m f))) (q (pgcd-aux x m f)))
                        (:instance len-pmul (p (cdr (gcd-cof x m f))) (q (pgcd-aux x m f)))
                        (:instance gcd-polyp (p x) (q m))
                        (:instance polyp-consp (p (car (gcd-cof x m f))))
                        (:instance polyp-consp (p (cdr (gcd-cof x m f)))))
           :in-theory (disable gcd-cof-correct reduciblep-intro divides-monic-of monic-of-props len-pmul gcd-cof
                               gcd-nonzero pmul-zero-iff)
           :do-not-induct t)))

(defthm gcd-const-props
  (implies (and (fap f) (polyp m f) (consp (cdr m)) (not (reduciblep m f))
                (polyp x f) (not (equal x (pzero f))) (< (len x) (len m)))
           (equal (cmul (frecip (car (pgcd-aux x m f)) f) (pgcd-aux x m f) f) (pone f)))
  :hints (("Goal" :use ((:instance gcd-const-lemma)
                        (:instance gcd-polyp (p x) (q m))
                        (:instance car-nonzero-poly (g (pgcd-aux x m f)))
                        (:instance poly-ext (p (cmul (frecip (car (pgcd-aux x m f)) f) (pgcd-aux x m f) f)) (q (pone f))))
           :in-theory (disable gcd-const-lemma gcd-polyp car-nonzero-poly))))

(defthm prem-multiple-2
  (implies (and (fap f) (polyp y f) (consp (cdr y)) (polyp q f))
           (equal (prem (pmul y q f) y f) (pzero f)))
  :hints (("Goal" :use ((:instance prem-multiple) (:instance pmul-comm (p y)))
           :in-theory (disable prem-multiple pmul-comm))))

(defthm prem-pneg
  (implies (and (fap f) (polyp y f) (consp (cdr y)) (polyp a f))
           (equal (prem (pneg a f) y f) (pneg (prem a y f) f)))
  :hints (("Goal" :use ((:instance prem-padd (a a) (b (pneg a f))))
           :in-theory (disable prem-padd))))

(defthm sum-to-diff
  (implies (and (fap f) (polyp a f) (polyp b f) (polyp c f) (equal (padd a b f) c))
           (equal a (padd c (pneg b f) f)))
  :rule-classes nil)

(defthm bezout-normalized
  (implies (and (fap f) (polyp m f) (consp (cdr m)) (not (reduciblep m f))
                (polyp x f) (not (equal x (pzero f))) (< (len x) (len m)))
           (equal (padd (pmul x (r$ x m f) f) (pmul m (s$ x m f) f) f) (pone f)))
  :hints (("Goal" :in-theory (e/d (r$ s$) (bezout gcd-const-props cmul-padd))
           :use ((:instance bezout (p x) (q m))
                 (:instance gcd-const-props)
                 (:instance cmul-padd (c (frecip (car (pgcd-aux x m f)) f))
                            (p (pmul (r$-aux x m f) x f)) (q (pmul (s$-aux x m f) m f)))))))

(defthm r$-polyp
  (implies (and (fap f) (polyp m f) (polyp x f) (not (equal x (pzero f))))
           (and (polyp (r$ x m f) f) (polyp (s$ x m f) f)))
  :hints (("Goal" :in-theory (enable r$ s$) :expand ((r$ x m f) (s$ x m f))
           :use ((:instance gcd-nonzero) (:instance gcd-polyp (p x) (q m))))))

(defthm prem-one-minus
  (implies (and (fap f) (polyp m f) (consp (cdr m)) (polyp s f)
                (equal a (padd (pone f) (pneg (pmul m s f) f) f)))
           (equal (prem a m f) (pone f)))
  :rule-classes nil)

(defthm r$-props
  (implies (and (fap f) (polyp m f) (consp (cdr m)) (not (reduciblep m f))
                (polyp x f) (not (equal x (pzero f))) (< (len x) (len m)))
           (and (polyp (r$ x m f) f)
                (equal (prem (pmul x (r$ x m f) f) m f) (pone f))))
  :hints (("Goal" :use ((:instance bezout-normalized)
                        (:instance sum-to-diff (a (pmul x (r$ x m f) f)) (b (pmul m (s$ x m f) f)) (c (pone f)))
                        (:instance prem-one-minus (s (s$ x m f)) (a (pmul x (r$ x m f) f))))
           :in-theory (disable bezout-normalized))))

;;; field operations of an extension

(defthm feltp-cons
  (implies (consp f)
           (equal (feltp x f) (and (polyp x (cdr f)) (< (len x) (len (car f))))))
  :hints (("Goal" :in-theory (enable feltp))))

(defthm fadd-cons (implies (consp f) (equal (fadd x y f) (padd x y (cdr f))))
  :hints (("Goal" :in-theory (enable fadd))))
(defthm fmul-cons (implies (consp f) (equal (fmul x y f) (prem (pmul x y (cdr f)) (car f) (cdr f))))
  :hints (("Goal" :in-theory (enable fmul))))
(defthm fneg-cons (implies (consp f) (equal (fneg x f) (pneg x (cdr f))))
  :hints (("Goal" :in-theory (enable fneg))))
(defthm frecip-cons (implies (consp f) (equal (frecip x f) (prem (r$ x (car f) (cdr f)) (car f) (cdr f))))
  :hints (("Goal" :in-theory (enable frecip))))
(defthm fzero-cons (implies (consp f) (equal (fzero f) (pzero (cdr f))))
  :hints (("Goal" :in-theory (enable fzero pzero))))
(defthm fone-cons (implies (consp f) (equal (fone f) (pone (cdr f))))
  :hints (("Goal" :in-theory (enable fone pone))))

(defmacro ext-hyps (f)
  `(and (consp ,f) (fap (cdr ,f)) (polyp (car ,f) (cdr ,f)) (not (reduciblep (car ,f) (cdr ,f)))
        (consp (cdr (car ,f)))))

(defthm ext-fadd-closed (implies (ext-hyps f) (fadd-closed-p f))
  :hints (("Goal" :in-theory (enable fadd-closed-p))))
(defthm ext-fmul-closed (implies (ext-hyps f) (fmul-closed-p f))
  :hints (("Goal" :in-theory (enable fmul-closed-p))))
(defthm ext-fadd-comm (implies (ext-hyps f) (fadd-comm-p f))
  :hints (("Goal" :in-theory (enable fadd-comm-p))))
(defthm ext-fmul-comm (implies (ext-hyps f) (fmul-comm-p f))
  :hints (("Goal" :in-theory (enable fmul-comm-p))))
(defthm ext-fadd-assoc (implies (ext-hyps f) (fadd-assoc-p f))
  :hints (("Goal" :in-theory (enable fadd-assoc-p))))
(defthm ext-fmul-assoc (implies (ext-hyps f) (fmul-assoc-p f))
  :hints (("Goal" :in-theory (e/d (fmul-assoc-p) (prem-pmul-prem-l prem-pmul-prem-r))
           :use ((:instance prem-pmul-prem-l (y (car f)) (f (cdr f))
                            (a (pmul (mv-nth 0 (fmul-assoc-p-witness f)) (mv-nth 1 (fmul-assoc-p-witness f)) (cdr f)))
                            (b (mv-nth 2 (fmul-assoc-p-witness f))))
                 (:instance prem-pmul-prem-r (y (car f)) (f (cdr f))
                            (a (pmul (mv-nth 1 (fmul-assoc-p-witness f)) (mv-nth 2 (fmul-assoc-p-witness f)) (cdr f)))
                            (b (mv-nth 0 (fmul-assoc-p-witness f))))))))
(defthm ext-feltp-fzero (implies (ext-hyps f) (feltp-fzero-p f))
  :hints (("Goal" :in-theory (enable feltp-fzero-p))))
(defthm ext-feltp-fone (implies (ext-hyps f) (feltp-fone-p f))
  :hints (("Goal" :in-theory (enable feltp-fone-p))))
(defthm ext-fone-fzero (implies (ext-hyps f) (fone-fzero-p f))
  :hints (("Goal" :in-theory (enable fone-fzero-p))))
(defthm ext-fzero-id (implies (ext-hyps f) (fzero-id-p f))
  :hints (("Goal" :in-theory (enable fzero-id-p))))
(defthm ext-fone-id (implies (ext-hyps f) (fone-id-p f))
  :hints (("Goal" :in-theory (enable fone-id-p))))
(defthm ext-feltp-fneg (implies (ext-hyps f) (feltp-fneg-p f))
  :hints (("Goal" :in-theory (enable feltp-fneg-p))))
(defthm ext-fadd-fneg (implies (ext-hyps f) (fadd-fneg-p f))
  :hints (("Goal" :in-theory (enable fadd-fneg-p))))
(defthm ext-feltp-frecip (implies (ext-hyps f) (feltp-frecip-p f))
  :hints (("Goal" :in-theory (enable feltp-frecip-p))))
(defthm ext-fmul-frecip (implies (ext-hyps f) (fmul-frecip-p f))
  :hints (("Goal" :in-theory (enable fmul-frecip-p))))
(defthm ext-fdistrib (implies (ext-hyps f) (fdistrib-p f))
  :hints (("Goal" :in-theory (enable fdistrib-p))))

(defthm ext-fap
  (implies (ext-hyps f) (fap f))
  :hints (("Goal" :in-theory (enable field-axioms-p))))

(defthm consp-cdr-len
  (implies (< 1 (len x)) (consp (cdr x)))
  :hints (("Goal" :in-theory (enable len))))

(defun cdr-induct (f) (if (consp f) (cdr-induct (cdr f)) t))

(defthm MAIN-1
  (implies (fieldp f) (field-axioms-p f))
  :hints (("Goal" :induct (cdr-induct f) :in-theory (enable fieldp irreduciblep))))

;;;;;;;;;;;;;;;;;;;; part 8 ;;;;;;;;;;;;;;;;;;;;


;;;; ===================== Evaluation, roots, MAIN-2 =====================

(defthm feltp-fpower
  (implies (and (fap f) (feltp x f)) (feltp (fpower x n f) f))
  :hints (("Goal" :in-theory (disable fmul))))

(in-theory (disable fpower))

(defthm fpower-0 (equal (fpower x 0 f) (fone f)) :hints (("Goal" :in-theory (enable fpower))))
(defthm fpower-succ
  (implies (natp n) (equal (fpower x (+ 1 n) f) (fmul x (fpower x n f) f)))
  :hints (("Goal" :in-theory (enable fpower))))

(defun pev (l x f)
  (if (consp l)
      (fadd (fmul (car l) (fpower x (len (cdr l)) f) f)
            (pev (cdr l) x f) f)
    (fzero f)))

(defthm feltp-pev
  (implies (and (fap f) (feltsp l f) (feltp x f)) (feltp (pev l x f) f)))

(defthm pev-pstrip
  (implies (and (fap f) (feltsp l f) (feltp x f))
           (equal (pev (pstrip l f) x f) (pev l x f))))

(defthm peval-pev
  (implies (and (fap f) (polyp p f) (feltp x f))
           (equal (peval p x f) (pev p x f)))
  :hints (("Goal" :induct (len-induct p f) :expand ((peval p x f)))
          ("Subgoal *1/2" :expand ((pev p x f) (pev (cdr p) x f)))))

(defthm pev-faddl
  (implies (and (fap f) (feltsp a f) (feltsp b f) (feltp x f))
           (equal (pev (faddl a b f) x f) (fadd (pev a x f) (pev b x f) f)))
  :hints (("Goal" :induct (faddl-induct a b) :do-not (quote (eliminate-destructors generalize)))))

(defthm pev-padd
  (implies (and (fap f) (feltsp a f) (feltsp b f) (feltp x f))
           (equal (pev (padd a b f) x f) (fadd (pev a x f) (pev b x f) f)))
  :hints (("Goal" :in-theory (enable padd))))

(defthm pev-pneg
  (implies (and (fap f) (feltsp a f) (feltp x f))
           (equal (pev (pneg a f) x f) (fneg (pev a x f) f))))

(defthm pev-cmul
  (implies (and (fap f) (feltp c f) (feltsp a f) (feltp x f))
           (equal (pev (cmul c a f) x f) (fmul c (pev a x f) f)))
  :hints (("Goal" :induct (len a) :in-theory (enable cmul))))

(defthm pev-append-zero
  (implies (and (fap f) (feltsp a f) (feltp x f))
           (equal (pev (append a (list (fzero f))) x f) (fmul x (pev a x f) f))))

(defthm pev-pshift
  (implies (and (fap f) (feltsp a f) (feltp x f))
           (equal (pev (pshift a k f) x f) (fmul (fpower x k f) (pev a x f) f)))
  :hints (("Goal" :induct (pshift a k f))
          ("Subgoal *1/1" :in-theory (enable fpower))
          ("Subgoal *1/2" :use ((:instance fpower-succ (n (1- k)))))))

(defthm pev-monomial
  (implies (and (fap f) (feltp c f) (feltp x f))
           (equal (pev (monomial c k f) x f) (fmul (fpower x k f) c f)))
  :hints (("Goal" :in-theory (enable monomial))))

(defthm pev-subst-padd
  (implies (and (fap f) (feltsp a f) (feltsp b f) (feltp x f) (equal r (padd a b f)))
           (equal (pev r x f) (fadd (pev a x f) (pev b x f) f)))
  :rule-classes nil)

(defthm pev-subst-cmul
  (implies (and (fap f) (feltp c f) (feltsp a f) (feltp x f) (equal r (cmul c a f)))
           (equal (pev r x f) (fmul c (pev a x f) f)))
  :rule-classes nil)

(defthm pev-pmul-monomial
  (implies (and (fap f) (feltp c f) (not (equal c (fzero f))) (polyp q f) (feltp x f))
           (equal (pev (pmul (monomial c k f) q f) x f)
                  (fmul c (fmul (fpower x k f) (pev q x f) f) f)))
  :hints (("Goal" :in-theory (enable pmul-monomial))))

(defthm pev-pmul
  (implies (and (fap f) (polyp p f) (polyp q f) (feltp x f))
           (equal (pev (pmul p q f) x f) (fmul (pev p x f) (pev q x f) f)))
  :hints (("Goal" :induct (len-induct p f) :in-theory (disable pmul-comm))
          ("Subgoal *1/2" :use ((:instance pmul-const-r (q q) (p p))
                                (:instance pmul-comm (p p) (q q))
                                (:instance pev-subst-cmul (c (car p)) (a q) (r (pmul p q f))))
                          :expand ((pev p x f)))
          ("Subgoal *1/1" :use (pmul-split-l
                                (:instance pev-subst-padd (r (pmul p q f))
                                           (a (pmul (monomial (car p) (len (cdr p)) f) q f))
                                           (b (pmul (pstrip (cdr p) f) q f))))
                          :expand ((pev p x f)))))

(defthm pev-pzero
  (implies (fap f) (equal (pev (pzero f) x f) (fzero f)))
  :hints (("Goal" :in-theory (enable pzero))))

(defthm pev-pone
  (implies (fap f) (equal (pev (pone f) x f) (fone f)))
  :hints (("Goal" :in-theory (enable pone))))

;;; linear factor

(defund lin (r f) (list (fone f) (fneg r f)))

(defthm lin-props
  (implies (and (fap f) (feltp r f))
           (and (polyp (lin r f) f)
                (monicp (lin r f) f)
                (equal (len (lin r f)) 2)
                (consp (cdr (lin r f)))))
  :hints (("Goal" :in-theory (enable lin polyp monicp len))))

(defthm pev-lin
  (implies (and (fap f) (feltp r f) (feltp x f))
           (equal (pev (lin r f) x f) (fadd x (fneg r f) f)))
  :hints (("Goal" :in-theory (enable lin len))))

(defthm pev-const
  (implies (and (fap f) (polyp r f) (not (consp (cdr r))) (feltp x f))
           (equal (pev r x f) (car r)))
  :hints (("Goal" :in-theory (enable polyp) :expand ((pev r x f)))))


(defthm factor-core
  (implies (and (fap f) (feltp r f) (polyp q f) (polyp rr f) (not (consp (cdr rr)))
                (equal p (padd (pmul q (lin r f) f) rr f))
                (equal (pev p r f) (fzero f)))
           (equal rr (pzero f)))
  :hints (("Goal" :use ((:instance const-zero-pzero (r rr)))
           :in-theory (disable pmul-comm)))
  :rule-classes nil)

(defthm factor-theorem
  (implies (and (fap f) (polyp p f) (feltp r f) (equal (pev p r f) (fzero f)))
           (pdivides (lin r f) p f))
  :hints (("Goal" :in-theory (e/d (pdivides) (prem-pquot len-prem))
           :use ((:instance prem-pquot (x p) (y (lin r f)))
                 (:instance len-prem (x p) (y (lin r f)))
                 (:instance factor-core (q (pquot p (lin r f) f)) (rr (prem p (lin r f) f)))))))

;;; factorization

(defun plist-prod (l f)
  (if (consp l) (pmul (car l) (plist-prod (cdr l) f) f) (pone f)))

(defun sum-deg (l)
  (if (consp l) (+ (degree (car l)) (sum-deg (cdr l))) 0))

(defun good-factors (l f)
  (if (consp l)
      (and (polyp (car l) f) (monicp (car l) f) (>= (degree (car l)) 1)
           (or (< (degree (car l)) 2) (not (reduciblep (car l) f)))
           (good-factors (cdr l) f))
    t))

(defthm good-factors-append
  (equal (good-factors (append a b) f) (and (good-factors a f) (good-factors b f))))

(defthm sum-deg-append
  (equal (sum-deg (append a b)) (+ (sum-deg a) (sum-deg b))))

(defthm polyp-plist-prod
  (implies (and (fap f) (good-factors l f)) (polyp (plist-prod l f) f)))

(defthm plist-prod-append
  (implies (and (fap f) (good-factors a f) (good-factors b f))
           (equal (plist-prod (append a b) f) (pmul (plist-prod a f) (plist-prod b f) f))))

(defthm pfactor-props
  (implies (reduciblep p f)
           (and (polyp (pfactor p f) f) (monicp (pfactor p f) f)
                (> (degree (pfactor p f)) 0) (< (degree (pfactor p f)) (degree p))
                (pdivides (pfactor p f) p f)))
  :hints (("Goal" :in-theory (enable reduciblep))))

(defthm pquot-exact
  (implies (and (fap f) (polyp p f) (polyp d f) (consp (cdr d)) (pdivides d p f))
           (equal (pmul (pquot p d f) d f) p))
  :hints (("Goal" :in-theory (enable pdivides) :use ((:instance prem-pquot (x p) (y d))))))

(defthm pquot-props
  (implies (and (fap f) (polyp p f) (monicp p f) (polyp d f) (monicp d f) (consp (cdr d))
                (pdivides d p f))
           (and (polyp (pquot p d f) f)
                (monicp (pquot p d f) f)
                (equal (len (pquot p d f)) (+ 1 (len p) (- (len d))))))
  :hints (("Goal" :use ((:instance pquot-exact)
                        (:instance len-pmul (p (pquot p d f)) (q d))
                        (:instance car-pmul (p (pquot p d f)) (q d)))
           :in-theory (e/d (monicp) (pquot-exact len-pmul car-pmul pmul-zero-iff)))))

(defthm factorization-props
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (and (good-factors (factorization p f) f)
                (equal (plist-prod (factorization p f) f) p)
                (equal (sum-deg (factorization p f)) (degree p))))
  :hints (("Goal" :induct (factorization p f))
          ("Subgoal *1/1" :use ((:instance pfactor-props)
                                (:instance pquot-props (d (pfactor p f)))
                                (:instance pquot-exact (d (pfactor p f)))
                                (:instance consp-cdr-len (x (pfactor p f))))
                          :in-theory (disable pfactor-props pquot-props pquot-exact))))

;;; proots-aux

(defun lin-root-in (x l f)
  (if (consp l)
      (or (and (equal (degree (car l)) 1) (equal x (fneg (cadar l) f)))
          (lin-root-in x (cdr l) f))
    nil))

(defthm member-proots-aux
  (iff (member x (proots-aux l f)) (lin-root-in x l f)))

(defthm len-proots-aux
  (implies (good-factors l f)
           (<= (len (proots-aux l f)) (sum-deg l))))

(defthm lin-root-in-root
  (implies (and (fap f) (good-factors l f) (lin-root-in x l f))
           (and (feltp x f)
                (equal (pev (plist-prod l f) x f) (fzero f))))
  :hints (("Goal" :in-theory (enable polyp monicp))))

(defthm pev-deg1
  (implies (and (fap f) (polyp d f) (monicp d f) (equal (len d) 2) (feltp x f))
           (equal (pev d x f) (fadd x (cadr d) f)))
  :hints (("Goal" :in-theory (enable monicp polyp len)
           :expand ((pev d x f) (pev (cdr d) x f) (pev (cddr d) x f)))))

(defthm feltp-cadr-poly
  (implies (and (polyp d f) (consp (cdr d))) (feltp (cadr d) f))
  :hints (("Goal" :in-theory (enable polyp))))

(defthm root-of-good-factor
  (implies (and (fap f) (polyp d f) (monicp d f) (>= (degree d) 1)
                (or (< (degree d) 2) (not (reduciblep d f)))
                (feltp x f) (equal (pev d x f) (fzero f)))
           (and (equal (degree d) 1) (equal x (fneg (cadr d) f))))
  :hints (("Goal" :cases ((< (degree d) 2)))
          ("Subgoal 2" :use ((:instance factor-theorem (p d) (r x))
                             (:instance reduciblep-intro (p d) (q (lin x f)))))
          ("Subgoal 1" :use ((:instance pev-deg1) (:instance consp-cdr-len (x d)))))
  :rule-classes nil)

(defthm root-lin-root-in
  (implies (and (fap f) (good-factors l f) (feltp x f)
                (equal (pev (plist-prod l f) x f) (fzero f)))
           (lin-root-in x l f))
  :hints (("Goal" :induct (len l) :in-theory (disable pev))
          ("Subgoal *1/1" :use ((:instance root-of-good-factor (d (car l)))))))

(defthm MAIN-2
  (implies (and (fieldp f) (polyp p f)
                (monicp p f) (>= (degree p) 1))
           (and (<= (len (proots p f))
                    (degree p))
                (iff (member x (proots p f))
                     (prootp x p f))))
  :hints (("Goal" :in-theory (e/d (proots prootp) (factorization-props lin-root-in-root root-lin-root-in))
           :use ((:instance factorization-props)
                 (:instance lin-root-in-root (l (factorization p f)))
                 (:instance root-lin-root-in (l (factorization p f)))))))

;;;;;;;;;;;;;;;;;;;; part 9 ;;;;;;;;;;;;;;;;;;;;


;;;; ===================== Towers and lifting =====================

(defthm fieldp-fap (implies (fieldp f) (fap f)) :hints (("Goal" :use MAIN-1)))

(defthm fieldp-cdr
  (implies (and (fieldp e) (consp e))
           (and (fieldp (cdr e))
                (polyp (car e) (cdr e))
                (monicp (car e) (cdr e))
                (not (reduciblep (car e) (cdr e)))
                (consp (car e))
                (consp (cdr (car e)))
                (consp (cddr (car e)))))
  :hints (("Goal" :in-theory (enable fieldp irreduciblep))))

(defthm extends-fieldp
  (implies (and (fieldp e) (extends e f)) (fieldp f))
  :rule-classes (:rewrite :forward-chaining))

(defthm extends-len
  (implies (extends e f) (<= (len f) (len e)))
  :rule-classes :linear)

(defthm extends-cdr
  (implies (and (extends e f) (not (equal e f))) (extends (cdr e) f)))

(defthm extends-not-equal-consp
  (implies (and (extends e f) (not (equal e f))) (consp e)))

(defthm extends-equal-len
  (implies (and (extends e f) (equal (len e) (len f))) (equal e f))
  :rule-classes nil)

(defthm fliftn-0 (equal (fliftn x 0) x))

(defthm flift-same (equal (flift x f f) x) :hints (("Goal" :in-theory (enable flift))))

(defthm flift-cons
  (implies (and (extends e f) (not (equal e f)))
           (equal (flift x f e) (list (flift x f (cdr e)))))
  :hints (("Goal" :in-theory (enable flift)
           :use ((:instance extends-len (e (cdr e))))
           :expand ((fliftn x (+ (len e) (- (len f))))))))

(defun ext-induct (e f)
  (if (and (consp e) (not (equal e f))) (ext-induct (cdr e) f) t))

(defmacro tower (e f) `(and (fieldp ,e) (extends ,e ,f)))

(defthm feltp-flift
  (implies (and (tower e f) (feltp x f)) (feltp (flift x f e) e))
  :hints (("Goal" :induct (ext-induct e f))
          ("Subgoal *1/1" :in-theory (enable polyp))))

(defthm flift-inj
  (implies (tower e f)
           (equal (equal (flift x f e) (flift y f e)) (equal x y)))
  :hints (("Goal" :induct (ext-induct e f))))

(defthm flift-fzero
  (implies (tower e f) (equal (flift (fzero f) f e) (fzero e)))
  :hints (("Goal" :induct (ext-induct e f))
          ("Subgoal *1/1" :in-theory (enable pzero))))

(defthm flift-fone
  (implies (tower e f) (equal (flift (fone f) f e) (fone e)))
  :hints (("Goal" :induct (ext-induct e f))
          ("Subgoal *1/1" :in-theory (enable pone))))

(defthm flift-zero-iff
  (implies (tower e f)
           (equal (equal (flift x f e) (fzero e)) (equal x (fzero f))))
  :hints (("Goal" :use ((:instance flift-inj (y (fzero f)))) :in-theory (disable flift-inj))))

(defthm padd-singletons
  (implies (and (fap f) (feltp a f) (feltp b f))
           (equal (padd (list a) (list b) f) (list (fadd a b f))))
  :hints (("Goal" :in-theory (enable padd))))

(defthm pmul-singletons
  (implies (and (fap f) (feltp a f) (feltp b f))
           (equal (pmul (list a) (list b) f) (list (fmul a b f))))
  :hints (("Goal" :use ((:instance pmul-const-r (q (list a)) (p (list b))))
           :in-theory (e/d (polyp pzero cmul) (pmul-const-r)))))

(defthm flift-fadd
  (implies (and (tower e f) (feltp x f) (feltp y f))
           (equal (flift (fadd x y f) f e) (fadd (flift x f e) (flift y f e) e)))
  :hints (("Goal" :induct (ext-induct e f))))

(defthm flift-fmul
  (implies (and (tower e f) (feltp x f) (feltp y f))
           (equal (flift (fmul x y f) f e) (fmul (flift x f e) (flift y f e) e)))
  :hints (("Goal" :induct (ext-induct e f))
          ("Subgoal *1/1" :use ((:instance prem-small (f (cdr e)) (y (car e))
                                           (r (list (flift (fmul x y f) f (cdr e)))))
                                (:instance feltp-flift (e (cdr e)) (x (fmul x y f))))
                          :in-theory (enable polyp len))))

(defthm flift-fneg
  (implies (and (tower e f) (feltp x f))
           (equal (flift (fneg x f) f e) (fneg (flift x f e) e)))
  :hints (("Goal" :induct (ext-induct e f))))

(defthm flift-frecip
  (implies (and (tower e f) (feltp x f) (not (equal x (fzero f))))
           (equal (flift (frecip x f) f e) (frecip (flift x f e) e)))
  :hints (("Goal" :use ((:instance fap-fmul-cancel-lemma (f e) (x (flift x f e))
                                   (y (flift (frecip x f) f e)) (z (frecip (flift x f e) e)))
                        (:instance extends-fieldp))
           :in-theory (disable flift-fmul))
          ("Goal'" :use ((:instance flift-fmul (y (frecip x f)))))))

;;; plift

(defthm len-plift (equal (len (plift p f e)) (len p)))

(defthm feltsp-plift
  (implies (and (tower e f) (feltsp p f)) (feltsp (plift p f e) e)))

(defthm car-plift (equal (car (plift p f e)) (if (consp p) (flift (car p) f e) nil)))

(defthm polyp-plift
  (implies (and (tower e f) (polyp p f)) (polyp (plift p f e) e))
  :hints (("Goal" :in-theory (enable polyp) :expand ((plift p f e)))))

(defthm monicp-plift
  (implies (and (tower e f) (monicp p f) (consp p)) (monicp (plift p f e) e))
  :hints (("Goal" :in-theory (enable monicp))))

(defthm pco-plift
  (implies (tower e f)
           (equal (pco (plift p f e) i e) (flift (pco p i f) f e))))

(defthm conv-plift
  (implies (and (tower e f) (feltsp p f) (feltsp q f))
           (equal (conv (plift p f e) (plift q f e) i e) (flift (conv p q i f) f e)))
  :hints (("Goal" :in-theory (disable flift-zero-iff))))

(defthm plift-pmul
  (implies (and (tower e f) (polyp p f) (polyp q f))
           (equal (plift (pmul p q f) f e) (pmul (plift p f e) (plift q f e) e)))
  :hints (("Goal" :use ((:instance extends-fieldp)
                        (:instance poly-ext (f e) (p (plift (pmul p q f) f e))
                                   (q (pmul (plift p f e) (plift q f e) e)))))))

(defthm plift-cmul
  (implies (and (tower e f) (feltp c f) (polyp p f))
           (equal (plift (cmul c p f) f e) (cmul (flift c f e) (plift p f e) e)))
  :hints (("Goal" :use ((:instance extends-fieldp)
                        (:instance poly-ext (f e) (p (plift (cmul c p f) f e))
                                   (q (cmul (flift c f e) (plift p f e) e)))))))

(defthm plift-pstrip
  (implies (tower e f)
           (equal (plift (pstrip l f) f e) (pstrip (plift l f e) e))))

;;;;;;;;;;;;;;;;;;;; part 10 ;;;;;;;;;;;;;;;;;;;;
(in-theory (e/d (len) (len-cons-x len-atom-x len-consp-pos len-cdr-x len-1-x len-cdr-consp consp-cdr-len)))


;;;; ===================== Vectors over a field & linear dependence =====================

(defun vecp (v n f)
  (if (zp n)
      (null v)
    (and (consp v) (feltp (car v) f) (vecp (cdr v) (1- n) f))))

(defun vecsp (w n f)
  (if (consp w) (and (vecp (car w) n f) (vecsp (cdr w) n f)) t))

(defun zvec (n f) (if (zp n) nil (cons (fzero f) (zvec (1- n) f))))

(defun zerovp (c f)
  (if (consp c) (and (equal (car c) (fzero f)) (zerovp (cdr c) f)) t))

(defun vadd (u v f)
  (if (consp u) (cons (fadd (car u) (car v) f) (vadd (cdr u) (cdr v) f)) nil))

(defun vscale (c v f)
  (if (consp v) (cons (fmul c (car v) f) (vscale c (cdr v) f)) nil))

(defun vlin (c w n f)
  (if (consp w)
      (vadd (vscale (car c) (car w) f) (vlin (cdr c) (cdr w) n f) f)
    (zvec n f)))

(defun heads (w) (if (consp w) (cons (car (car w)) (heads (cdr w))) nil))
(defun tails (w) (if (consp w) (cons (cdr (car w)) (tails (cdr w))) nil))

(defun dot (c h f)
  (if (consp h) (fadd (fmul (car c) (car h) f) (dot (cdr c) (cdr h) f) f) (fzero f)))

(defun zeros (k f) (if (zp k) nil (cons (fzero f) (zeros (1- k) f))))

(defthm feltsp-vscale (implies (and (fap f) (feltp c f) (feltsp a f)) (feltsp (vscale c a f) f)))
(defthm feltsp-vadd (implies (and (fap f) (feltsp a f) (feltsp b f) (equal (len a) (len b))) (feltsp (vadd a b f) f)))
(defthm vecp-len (implies (vecp v n f) (equal (len v) (nfix n))))
(defthm vecp-feltsp (implies (vecp v n f) (feltsp v f)))
(defthm vecp-vadd (implies (and (fap f) (vecp u n f) (vecp v n f)) (vecp (vadd u v f) n f)))
(defthm vecp-vscale (implies (and (fap f) (feltp c f) (vecp v n f)) (vecp (vscale c v f) n f)))
(defthm vecp-zvec (implies (fap f) (vecp (zvec n f) n f)))
(defthm vecp-vlin
  (implies (and (fap f) (feltsp c f) (equal (len c) (len w)) (vecsp w n f)) (vecp (vlin c w n f) n f)))

(defthm vadd-zvec (implies (and (fap f) (feltsp v f) (equal (len v) (nfix n))) (equal (vadd (zvec n f) v f) v)))
(defthm vadd-zvec-r (implies (and (fap f) (feltsp v f) (equal (len v) (nfix n))) (equal (vadd v (zvec n f) f) v)))
(defthm vadd-comm
  (implies (and (fap f) (feltsp u f) (feltsp v f) (equal (len u) (len v))) (equal (vadd u v f) (vadd v u f)))
  :rule-classes nil)
(defthm vadd-assoc
  (implies (and (fap f) (feltsp u f) (feltsp v f) (feltsp w f) (equal (len u) (len v)) (equal (len v) (len w)))
           (equal (vadd (vadd u v f) w f) (vadd u (vadd v w f) f))))
(defthm vscale-vadd
  (implies (and (fap f) (feltp c f) (feltsp u f) (feltsp v f) (equal (len u) (len v)))
           (equal (vscale c (vadd u v f) f) (vadd (vscale c u f) (vscale c v f) f))))
(defthm vscale-fadd
  (implies (and (fap f) (feltp a f) (feltp b f) (vecp v n f))
           (equal (vadd (vscale a v f) (vscale b v f) f) (vscale (fadd a b f) v f))))
(defthm vscale-zero (implies (and (fap f) (vecp v n f)) (equal (vscale (fzero f) v f) (zvec n f))))
(defthm vscale-zvec (implies (and (fap f) (feltp c f)) (equal (vscale c (zvec n f) f) (zvec n f))))

;; split head/tail

(defthm vecsp-tails (implies (and (vecsp w n f) (not (zp n))) (vecsp (tails w) (1- n) f)))
(defthm feltsp-heads (implies (and (vecsp w n f) (not (zp n))) (feltsp (heads w) f)))
(defthm len-heads (equal (len (heads w)) (len w)))
(defthm len-tails (equal (len (tails w)) (len w)))
(defthm feltp-dot (implies (and (fap f) (feltsp c f) (feltsp h f) (equal (len c) (len h))) (feltp (dot c h f) f)))

(defthmd vlin-split
  (implies (and (fap f) (feltsp c f) (equal (len c) (len w)) (vecsp w n f) (not (zp n)))
           (equal (vlin c w n f)
                  (cons (dot c (heads w) f) (vlin c (tails w) (1- n) f)))))

(defthm vlin-zero-n
  (implies (and (vecsp w 0 f) (equal (len c) (len w))) (equal (vlin c w 0 f) nil)))

;; elimination

(defun elim (w a tt f)
  (if (consp w)
      (cons (vadd (cdr (car w)) (vscale (fneg (fmul (car (car w)) (frecip a f) f) f) tt f) f)
            (elim (cdr w) a tt f))
    nil))

(defthm vecsp-elim
  (implies (and (fap f) (vecsp w n f) (not (zp n)) (feltp a f) (not (equal a (fzero f))) (vecp tt (1- n) f))
           (vecsp (elim w a tt f) (1- n) f)))

(defthm len-elim (equal (len (elim w a tt f)) (len w)))

(defthm list-ext
  (implies (and (true-listp a) (true-listp b) (equal (len a) (len b))
                (equal (pco a (pwit a b) f) (pco b (pwit a b) f)))
           (equal a b))
  :hints (("Goal" :use pwit-lemma))
  :rule-classes nil)

(defthm true-listp-vadd (true-listp (vadd a b f)))
(defthm true-listp-vscale (true-listp (vscale c a f)))
(defthm len-vadd (equal (len (vadd a b f)) (len a)))
(defthm len-vscale (equal (len (vscale c a f)) (len a)))

(defthm pco-vadd
  (implies (and (fap f) (feltsp a f) (feltsp b f) (equal (len a) (len b)))
           (equal (pco (vadd a b f) i f) (fadd (pco a i f) (pco b i f) f))))

(defthm pco-vscale
  (implies (and (fap f) (feltp c f) (feltsp a f))
           (equal (pco (vscale c a f) i f) (fmul c (pco a i f) f))))

(defthm pco-zvec
  (equal (pco (zvec n f) i f) (fzero f)))

(defun dotc (c w i f)
  (if (consp w) (fadd (fmul (car c) (pco (car w) i f) f) (dotc (cdr c) (cdr w) i f) f) (fzero f)))

(defthm feltp-dotc
  (implies (and (fap f) (feltsp c f) (equal (len c) (len w)) (vecsp w n f))
           (feltp (dotc c w i f) f)))

(defthm feltsp-vlin
  (implies (and (fap f) (feltsp c f) (equal (len c) (len w)) (vecsp w n f)) (feltsp (vlin c w n f) f))
  :hints (("Goal" :use vecp-vlin :in-theory (disable vecp-vlin))))
(defthm len-vlin
  (implies (and (fap f) (feltsp c f) (equal (len c) (len w)) (vecsp w n f)) (equal (len (vlin c w n f)) (nfix n)))
  :hints (("Goal" :use vecp-vlin :in-theory (disable vecp-vlin))))

(defthm pco-vlin
  (implies (and (fap f) (feltsp c f) (equal (len c) (len w)) (vecsp w n f))
           (equal (pco (vlin c w n f) i f) (dotc c w i f))))

(defthm feltp-dotc-elim
  (implies (and (fap f) (vecsp w n f) (not (zp n)) (feltp a f) (not (equal a (fzero f))) (vecp tt (1- n) f)
                (feltsp c f) (equal (len c) (len w)))
           (feltp (dotc c (elim w a tt f) i f) f))
  :hints (("Goal" :use ((:instance feltp-dotc (w (elim w a tt f)) (n (1- n))))
           :in-theory (disable feltp-dotc))))

(defthm feltp-dotc-tails
  (implies (and (fap f) (vecsp w n f) (not (zp n)) (feltsp c f) (equal (len c) (len w)))
           (feltp (dotc c (tails w) i f) f))
  :hints (("Goal" :use ((:instance feltp-dotc (w (tails w)) (n (1- n))))
           :in-theory (disable feltp-dotc))))

(defthm dotc-elim
  (implies (and (fap f) (vecsp w n f) (not (zp n)) (feltp a f) (not (equal a (fzero f))) (vecp tt (1- n) f)
                (feltsp c f) (equal (len c) (len w)))
           (equal (dotc c (elim w a tt f) i f)
                  (fadd (dotc c (tails w) i f)
                        (fmul (fneg (fmul (dot c (heads w) f) (frecip a f) f) f) (pco tt i f) f) f)))
  :hints (("Goal" :induct (vlin c w n f))))

(defthm vlin-elim
  (implies (and (fap f) (vecsp w n f) (not (zp n)) (feltp a f) (not (equal a (fzero f))) (vecp tt (1- n) f)
                (feltsp c f) (equal (len c) (len w)))
           (equal (vlin c (elim w a tt f) (1- n) f)
                  (vadd (vlin c (tails w) (1- n) f)
                        (vscale (fneg (fmul (dot c (heads w) f) (frecip a f) f) f) tt f) f)))
  :hints (("Goal" :use ((:instance list-ext (a (vlin c (elim w a tt f) (1- n) f))
                                   (b (vadd (vlin c (tails w) (1- n) f)
                                            (vscale (fneg (fmul (dot c (heads w) f) (frecip a f) f) f) tt f) f)))))))

;; rotation

(defun first-nz (w f)
  (if (consp w) (if (equal (car (car w)) (fzero f)) (1+ (first-nz (cdr w) f)) 0) 0))

(defun all-heads-zero (w f)
  (if (consp w) (and (equal (car (car w)) (fzero f)) (all-heads-zero (cdr w) f)) t))

(defthm first-nz-bound
  (implies (not (all-heads-zero w f)) (< (first-nz w f) (len w)))
  :rule-classes :linear)

(defun rot (w) (append (cdr w) (list (car w))))
(defun unrot (c) (cons (car (last c)) (butlast c 1)))

(defthm first-nz-rot
  (implies (and (consp w) (equal (car (car w)) (fzero f)) (not (all-heads-zero w f)))
           (equal (first-nz (rot w) f) (1- (first-nz w f))))
  :hints (("Goal" :induct (first-nz w f))))

(defthm all-heads-zero-append
  (equal (all-heads-zero (append a b) f) (and (all-heads-zero a f) (all-heads-zero b f))))

(defthm len-rot (implies (consp w) (equal (len (rot w)) (len w))))

(defthm vecsp-append (equal (vecsp (append a b) n f) (and (vecsp a n f) (vecsp b n f))))

(defthm vecsp-rot (implies (and (consp w) (vecsp w n f)) (vecsp (rot w) n f)))

(defthm vlin-append
  (implies (and (fap f) (vecsp a n f) (vecsp b n f) (feltsp c f) (feltsp d f) (equal (len c) (len a))
                (equal (len d) (len b)))
           (equal (vlin (append c d) (append a b) n f)
                  (vadd (vlin c a n f) (vlin d b n f) f)))
  :hints (("Goal" :induct (vlin c a n f))))

(defthm butlast-append-last
  (implies (and (consp c) (true-listp c)) (equal (append (butlast c 1) (list (car (last c)))) c))
  :hints (("Goal" :induct (len c))))

(defthm feltsp-take-x
  (implies (and (feltsp c f) (<= (nfix n) (len c))) (feltsp (take n c) f))
  :hints (("Goal" :induct (take n c) :in-theory (enable take len))))

(defthm feltsp-butlast (implies (feltsp c f) (feltsp (butlast c 1) f)))
(defthm feltp-car-last (implies (and (feltsp c f) (consp c)) (feltp (car (last c)) f)))
(defthm len-butlast-1 (implies (consp c) (equal (len (butlast c 1)) (1- (len c)))))

(defthm vlin-unrot-aux
  (implies (and (fap f) (vecsp w n f) (consp w) (feltsp c1 f) (feltp z f) (equal (len c1) (len (cdr w))))
           (equal (vlin (cons z c1) w n f)
                  (vlin (append c1 (list z)) (append (cdr w) (list (car w))) n f)))
  :hints (("Goal" :use ((:instance vlin-append (c c1) (d (list z)) (a (cdr w)) (b (list (car w))))
                        (:instance vadd-comm (u (vscale z (car w) f)) (v (vlin c1 (cdr w) n f))))
           :in-theory (disable vlin-append)
           :do-not-induct t))
  :rule-classes nil)

(defthm vlin-unrot
  (implies (and (fap f) (vecsp w n f) (consp w) (feltsp c f) (equal (len c) (len w)))
           (equal (vlin (unrot c) w n f) (vlin c (rot w) n f)))
  :hints (("Goal" :use ((:instance vlin-unrot-aux (c1 (butlast c 1)) (z (car (last c))))
                        (:instance butlast-append-last))
           :in-theory (disable butlast-append-last butlast)
           :do-not-induct t)))

(defthm zerovp-append
  (equal (zerovp (append a b) f) (and (zerovp a f) (zerovp b f))))

(defthm zerovp-unrot
  (implies (and (consp c) (true-listp c) (not (zerovp c f))) (not (zerovp (unrot c) f)))
  :hints (("Goal" :use ((:instance butlast-append-last)
                        (:instance zerovp-append (a (butlast c 1)) (b (list (car (last c))))))
           :in-theory (disable butlast-append-last zerovp-append butlast)
           :do-not-induct t)))

(defthm feltsp-zeros (implies (fap f) (feltsp (zeros k f) f)))
(defthm len-zeros (equal (len (zeros k f)) (nfix k)))

;; the dependency function

(defun dep (w n f)
  (declare (xargs :measure (+ (* (1+ (len w)) (nfix n)) (first-nz w f))))
  (cond ((zp n) (cons (fone f) (zeros (1- (len w)) f)))
        ((not (consp w)) nil)
        ((all-heads-zero w f) (dep (tails w) (1- n) f))
        ((equal (car (car w)) (fzero f)) (unrot (dep (rot w) n f)))
        (t (let* ((a (car (car w)))
                  (c2 (dep (elim (cdr w) a (cdr (car w)) f) (1- n) f)))
             (cons (fneg (fmul (dot c2 (heads (cdr w)) f) (frecip a f) f) f) c2)))))

(defthm dot-zero-heads
  (implies (and (fap f) (feltsp c f) (equal (len c) (len w)) (all-heads-zero w f) (vecsp w n f) (not (zp n)))
           (equal (dot c (heads w) f) (fzero f)))
  :hints (("Goal" :induct (vlin c w n f))))

(defund dep-ok (c w n f)
  (and (feltsp c f) (equal (len c) (len w)) (not (zerovp c f))
       (equal (vlin c w n f) (zvec n f))))

(defthm zvec-zero-n (equal (zvec 0 f) nil))

(defthm vlin-nil-vecs
  (implies (vecsp w 0 f) (equal (vlin c w 0 f) nil))
  :hints (("Goal" :induct (vlin c w 0 f))))

(defthm dep-b1
  (implies (and (fap f) (< 0 (len w)) (vecsp w 0 f))
           (dep-ok (cons (fone f) (zeros (1- (len w)) f)) w 0 f))
  :hints (("Goal" :in-theory (enable dep-ok))))

(defthm dep-b2
  (implies (and (fap f) (not (zp n)) (vecsp w n f) (all-heads-zero w f)
                (dep-ok c (tails w) (1- n) f))
           (dep-ok c w n f))
  :hints (("Goal" :in-theory (enable dep-ok) :use ((:instance vlin-split)))))

(defthm len-unrot (implies (consp c) (equal (len (unrot c)) (len c))))
(defthm feltsp-unrot (implies (and (feltsp c f) (consp c)) (feltsp (unrot c) f)))

(defthm dep-b3
  (implies (and (fap f) (consp w) (vecsp w n f) (dep-ok c (rot w) n f))
           (dep-ok (unrot c) w n f))
  :hints (("Goal" :in-theory (e/d (dep-ok) (rot unrot vlin-split)) :cases ((consp c)) :do-not-induct t)))

(defthm vlin-cons-c
  (equal (vlin (cons a c) w n f)
         (if (consp w) (vadd (vscale a (car w) f) (vlin c (cdr w) n f) f) (zvec n f))))

(defthm dep-b4-gen
  (implies (and (fap f) (not (zp n)) (consp w) (vecsp w n f)
                (not (equal (car (car w)) (fzero f)))
                (equal c0 (fneg (fmul (dot c2 (heads (cdr w)) f) (frecip (car (car w)) f) f) f))
                (dep-ok c2 (elim (cdr w) (car (car w)) (cdr (car w)) f) (1- n) f))
           (dep-ok (cons c0 c2) w n f))
  :hints (("Goal" :in-theory (e/d (dep-ok) (vlin-elim vlin))
           :do-not-induct t
           :use ((:instance vlin-split (c c2) (w (cdr w)))
                 (:instance vlin-elim (w (cdr w)) (a (car (car w))) (tt (cdr (car w))) (c c2))
                 (:instance vadd-comm (u (vscale c0 (cdr (car w)) f))
                            (v (vlin c2 (tails (cdr w)) (1- n) f))))))
  :rule-classes nil)

(defthm dep-b4
  (implies (and (fap f) (not (zp n)) (consp w) (vecsp w n f)
                (not (equal (car (car w)) (fzero f)))
                (dep-ok c2 (elim (cdr w) (car (car w)) (cdr (car w)) f) (1- n) f))
           (dep-ok (cons (fneg (fmul (dot c2 (heads (cdr w)) f) (frecip (car (car w)) f) f) f) c2)
                   w n f))
  :hints (("Goal" :use ((:instance dep-b4-gen (c0 (fneg (fmul (dot c2 (heads (cdr w)) f) (frecip (car (car w)) f) f) f)))))))

(defthm dep-correct-ok
  (implies (and (fap f) (natp n) (vecsp w n f) (< n (len w)))
           (dep-ok (dep w n f) w n f))
  :hints (("Goal" :induct (dep w n f) :in-theory (disable rot unrot))))

(defthm dep-correct
  (implies (and (fap f) (natp n) (vecsp w n f) (< n (len w)))
           (and (feltsp (dep w n f) f)
                (equal (len (dep w n f)) (len w))
                (not (zerovp (dep w n f) f))
                (equal (vlin (dep w n f) w n f) (zvec n f))))
  :hints (("Goal" :use dep-correct-ok :in-theory (e/d (dep-ok) (dep-correct-ok)))))

;;;;;;;;;;;;;;;;;;;; part 11 ;;;;;;;;;;;;;;;;;;;;
(in-theory (e/d (len-cons-x len-atom-x len-consp-pos len-cdr-x len-1-x len-cdr-consp consp-cdr-len) (len)))
(in-theory (enable (:induction len)))


;;;; ===================== Coordinates and MAIN-3 =====================

(defthm len-pos-consp (implies (< 0 (len x)) (consp x)) :hints (("Goal" :in-theory (enable len))))

(defthm zeros-zvec (equal (zeros k f) (zvec k f)))

(defund pad (y d g) (append (zvec (- (nfix d) (len y)) g) y))

(defun expand (l d g)
  (if (consp l) (append (pad (car l) d g) (expand (cdr l) d g)) nil))

(defun coords-l (l e f)
  (if (and (consp e) (not (equal e f)))
      (coords-l (expand l (1- (len (car e))) (cdr e)) (cdr e) f)
    l))

(defthm vecp-append
  (implies (and (vecp a n f) (vecp b m f) (natp n) (natp m))
           (vecp (append a b) (+ n m) f)))

(defthm vecp-zvec-2 (implies (fap f) (vecp (zvec n f) (nfix n) f)))

(defthm vecp-feltsp-len
  (implies (and (feltsp l f) (equal (len l) n)) (vecp l n f)))

(defthm vecp-pad
  (implies (and (fap g) (polyp y g) (<= (len y) d) (natp d))
           (vecp (pad y d g) d g))
  :hints (("Goal" :use ((:instance vecp-append (a (zvec (- d (len y)) g)) (b y) (f g)
                                   (n (- d (len y))) (m (len y))))
           :in-theory (e/d (pad) (vecp-append)))))

(defthm vecp-expand
  (implies (and (consp e) (fap (cdr e)) (feltsp l e) (equal d (1- (len (car e)))))
           (vecp (expand l d (cdr e)) (* (len l) d) (cdr e)))
  :hints (("Goal" :induct (expand l d (cdr e)))
          ("Subgoal *1/1" :use ((:instance vecp-append (a (pad (car l) d (cdr e))) (b (expand (cdr l) d (cdr e)))
                                           (f (cdr e)) (n d) (m (* (len (cdr l)) d))))
                          :in-theory (disable vecp-append))))

(defthm edegree-natp
  (implies (tower e f) (posp (edegree e f)))
  :hints (("Goal" :induct (ext-induct e f)))
  :rule-classes :type-prescription)

(defthm vecp-coords-l
  (implies (and (tower e f) (feltsp l e))
           (vecp (coords-l l e f) (* (len l) (edegree e f)) f))
  :hints (("Goal" :induct (coords-l l e f))
          ("Subgoal *1/1" :use ((:instance vecp-expand (d (1- (len (car e)))))))))

;;; pc on equal-length lists

(defthm pco-append-zvec
  (equal (pco (append (zvec k g) y) i g) (pco y i g)))

(defthm pco-pad (equal (pco (pad y d g) i g) (pco y i g)) :hints (("Goal" :in-theory (enable pad))))
(defthm feltsp-zvec (implies (fap f) (feltsp (zvec k f) f)))
(defthm true-listp-faddl (true-listp (faddl x y f)) :hints (("Goal" :induct (faddl-induct x y))))
(defthm true-listp-pstrip (implies (true-listp l) (true-listp (pstrip l f))))
(defthm true-listp-padd (true-listp (padd x y f)) :hints (("Goal" :in-theory (enable padd))))
(defthm true-listp-cmul (implies (true-listp y) (true-listp (cmul c y f))) :hints (("Goal" :in-theory (enable cmul))))
(defthm feltsp-pad (implies (and (fap g) (feltsp y g)) (feltsp (pad y d g) g)) :hints (("Goal" :in-theory (enable pad) :do-not-induct t)))
(defthm true-listp-pad (implies (true-listp y) (true-listp (pad y d g))) :hints (("Goal" :in-theory (enable pad))))



(defthm len-zvec (equal (len (zvec k f)) (nfix k)))


(defthm len-cmul-bound
  (<= (len (cmul c y g)) (max 1 (len y)))
  :hints (("Goal" :in-theory (enable cmul len) :induct (len y)))
  :rule-classes :linear)

(defthm len-pad
  (implies (and (natp d) (<= (len y) d)) (equal (len (pad y d g)) d))
  :hints (("Goal" :in-theory (enable pad))))

(defthm pad-padd
  (implies (and (fap g) (polyp y g) (polyp z g) (<= (len y) d) (<= (len z) d) (natp d))
           (equal (pad (padd y z g) d g) (vadd (pad y d g) (pad z d g) g)))
  :hints (("Goal" :use ((:instance list-ext (f g) (a (pad (padd y z g) d g)) (b (vadd (pad y d g) (pad z d g) g)))
                        (:instance len-padd (x y) (y z) (f g)))
           :in-theory (disable pad len-padd)
           :do-not-induct t)))

(defthm pad-cmul
  (implies (and (fap g) (feltp c g) (polyp y g) (<= (len y) d) (natp d))
           (equal (pad (cmul c y g) d g) (vscale c (pad y d g) g)))
  :hints (("Goal" :use ((:instance list-ext (f g) (a (pad (cmul c y g) d g)) (b (vscale c (pad y d g) g)))
                        (:instance len-cmul-bound (c c) (y y)))
           :in-theory (disable pad len-cmul-bound)
           :do-not-induct t)))

(defthm vadd-append
  (implies (equal (len a) (len c))
           (equal (vadd (append a b) (append c d) f) (append (vadd a c f) (vadd b d f)))))

(defthm vscale-append
  (equal (vscale x (append a b) f) (append (vscale x a f) (vscale x b f))))

(defthm expand-vadd
  (implies (and (consp e) (fap (cdr e)) (feltsp u e) (feltsp v e) (equal (len u) (len v))
                (equal d (1- (len (car e)))))
           (equal (expand (vadd u v e) d (cdr e))
                  (vadd (expand u d (cdr e)) (expand v d (cdr e)) (cdr e))))
  :hints (("Goal" :induct (vadd u v e))))

(defthm prem-cmul-small
  (implies (and (fap g) (feltp a g) (polyp y g) (polyp m g) (consp (cdr m)) (< (len y) (len m)))
           (equal (prem (cmul a y g) m g) (cmul a y g)))
  :hints (("Goal" :use ((:instance prem-small (f g) (y m) (r (cmul a y g)))
                        (:instance len-cmul-bound (c a)))
           :in-theory (disable prem-small len-cmul-bound))))

(defthm fmul-lift-cons
  (implies (and (consp e) (fap (cdr e)) (polyp (car e) (cdr e)) (consp (cdr (car e)))
                (feltp a (cdr e)) (feltp y e))
           (equal (fmul (list a) y e) (cmul a y (cdr e))))
  :hints (("Goal" :use ((:instance pmul-const-r (f (cdr e)) (q y) (p (list a)))
                        (:instance pmul-comm (f (cdr e)) (p y) (q (list a))))
           :in-theory (e/d (polyp) (pmul-const-r pmul-comm)))))

(defthm expand-vscale
  (implies (and (consp e) (fap (cdr e)) (polyp (car e) (cdr e)) (consp (cdr (car e)))
                (feltsp v e) (feltp a (cdr e))
                (equal d (1- (len (car e)))))
           (equal (expand (vscale (list a) v e) d (cdr e))
                  (vscale a (expand v d (cdr e)) (cdr e)))))

(defthm feltsp-expand
  (implies (and (consp e) (fap (cdr e)) (feltsp l e) (equal d (1- (len (car e)))))
           (feltsp (expand l d (cdr e)) (cdr e)))
  :hints (("Goal" :use vecp-expand :in-theory (disable vecp-expand))))

(defthm len-expand
  (implies (and (consp e) (fap (cdr e)) (feltsp l e) (equal d (1- (len (car e)))))
           (equal (len (expand l d (cdr e))) (* (len l) d)))
  :hints (("Goal" :use vecp-expand :in-theory (disable vecp-expand))))

(defun coords2-induct (u v e f)
  (if (and (consp e) (not (equal e f)))
      (coords2-induct (expand u (1- (len (car e))) (cdr e)) (expand v (1- (len (car e))) (cdr e)) (cdr e) f)
    (list u v)))

(defthm coords-vadd
  (implies (and (tower e f) (feltsp u e) (feltsp v e) (equal (len u) (len v)))
           (equal (coords-l (vadd u v e) e f)
                  (vadd (coords-l u e f) (coords-l v e f) f)))
  :hints (("Goal" :induct (coords2-induct u v e f) :expand ((coords-l (vadd u v e) e f) (coords-l u e f) (coords-l v e f)))))

(defthm coords-vscale
  (implies (and (tower e f) (feltsp v e) (feltp a f))
           (equal (coords-l (vscale (flift a f e) v e) e f)
                  (vscale a (coords-l v e f) f)))
  :hints (("Goal" :induct (coords-l v e f))))

(defthm zerovp-zvec-1 (zerovp (zvec n f) f))
(defthm zerovp-pad
  (equal (zerovp (pad y d g) g) (zerovp y g))
  :hints (("Goal" :in-theory (enable pad))))

(defthm polyp-zerovp
  (implies (polyp y g) (equal (zerovp y g) (equal y (pzero g))))
  :hints (("Goal" :in-theory (enable polyp pzero))))

(defthm zerovp-expand
  (implies (and (consp e) (feltsp l e) (zerovp (expand l d (cdr e)) (cdr e)))
           (zerovp l e)))

(defthm coords-zero
  (implies (and (tower e f) (feltsp l e) (zerovp (coords-l l e f) f))
           (zerovp l e))
  :hints (("Goal" :induct (coords-l l e f))))

(defthm zerovp-zvec (zerovp (zvec n f) f))

;;; single elements

(defun cv (y e f) (coords-l (list y) e f))

(defun cvs (l e f) (if (consp l) (cons (cv (car l) e f) (cvs (cdr l) e f)) nil))

(defun powl (k x e)
  (if (zp k) nil (cons (fpower x (1- k) e) (powl (1- k) x e))))

(defthm feltsp-powl (implies (and (fap e) (feltp x e)) (feltsp (powl k x e) e)))
(defthm len-powl (equal (len (powl k x e)) (nfix k)))
(defthm len-cvs (equal (len (cvs l e f)) (len l)))

(defthm vecp-cv
  (implies (and (tower e f) (feltp y e)) (vecp (cv y e f) (edegree e f) f))
  :hints (("Goal" :use ((:instance vecp-coords-l (l (list y)))))))

(in-theory (disable cv))

(defthm vecsp-cvs
  (implies (and (tower e f) (feltsp l e)) (vecsp (cvs l e f) (edegree e f) f))
  :hints (("Goal" :induct (len l))))

(defthm cv-fadd
  (implies (and (tower e f) (feltp y e) (feltp z e))
           (equal (cv (fadd y z e) e f) (vadd (cv y e f) (cv z e f) f)))
  :hints (("Goal" :in-theory (enable cv) :use ((:instance coords-vadd (u (list y)) (v (list z)))))))

(defthm cv-fmul
  (implies (and (tower e f) (feltp y e) (feltp a f))
           (equal (cv (fmul (flift a f e) y e) e f) (vscale a (cv y e f) f)))
  :hints (("Goal" :in-theory (enable cv) :use ((:instance coords-vscale (v (list y)))))))

(defthm cv-zero
  (implies (and (tower e f) (feltp y e) (zerovp (cv y e f) f))
           (equal y (fzero e)))
  :hints (("Goal" :in-theory (e/d (cv) (coords-l coords-zero)) :do-not-induct t
           :use ((:instance coords-zero (l (list y))))))
  :rule-classes nil)

(defthm cv-fzero
  (implies (tower e f) (equal (cv (fzero e) e f) (zvec (edegree e f) f)))
  :hints (("Goal" :use ((:instance cv-fmul (y (fzero e)) (a (fzero f)))
                        (:instance vecp-cv (y (fzero e)))
                        (:instance vscale-zero (v (cv (fzero e) e f)) (n (edegree e f))))
           :in-theory (disable cv-fmul vecp-cv vscale-zero) :do-not-induct t)))

(defthm feltsp-cv (implies (and (tower e f) (feltp y e)) (feltsp (cv y e f) f))
  :hints (("Goal" :use vecp-cv :in-theory (disable vecp-cv))))
(defthm len-cv (implies (and (tower e f) (feltp y e)) (equal (len (cv y e f)) (edegree e f)))
  :hints (("Goal" :use vecp-cv :in-theory (disable vecp-cv))))

(defthm vadd-comm-rw
  (implies (and (fap f) (feltsp u f) (feltsp v f) (equal (len u) (len v)))
           (equal (vadd u v f) (vadd v u f)))
  :hints (("Goal" :use vadd-comm))
  :rule-classes ((:rewrite :loop-stopper ((u v)))))

(defthm cv-pev
  (implies (and (tower e f) (feltsp c f) (feltp x e))
           (equal (cv (pev (plift c f e) x e) e f)
                  (vlin c (cvs (powl (len c) x e) e f) (edegree e f) f)))
  :hints (("Goal" :induct (len c))))

;;; existence of a polynomial

(defthm pstrip-pzero-zerovp
  (implies (and (consp l) (equal (pstrip l f) (pzero f))) (zerovp l f))
  :hints (("Goal" :in-theory (enable pzero))))

(defthm pev-plift-zero
  (implies (and (tower e f) (feltp x e))
           (equal (pev (plift (dep (cvs (powl (1+ (edegree e f)) x e) e f) (edegree e f) f) f e) x e)
                  (fzero e)))
  :hints (("Goal" :use ((:instance cv-zero (y (pev (plift (dep (cvs (powl (1+ (edegree e f)) x e) e f) (edegree e f) f) f e) x e)))
                        (:instance dep-correct (w (cvs (powl (1+ (edegree e f)) x e) e f)) (n (edegree e f)))
                        (:instance cv-pev (c (dep (cvs (powl (1+ (edegree e f)) x e) e f) (edegree e f) f)))
                        (:instance vecsp-cvs (l (powl (1+ (edegree e f)) x e)))
                        (:instance extends-fieldp))
           :in-theory (disable dep-correct cv-pev vecsp-cvs dep powl cvs)
           :do-not-induct t)))

(defund wpoly0 (x e f) (pstrip (dep (cvs (powl (1+ (edegree e f)) x e) e f) (edegree e f) f) f))

(defthm wpoly0-props
  (implies (and (tower e f) (feltp x e))
           (and (polyp (wpoly0 x e f) f)
                (not (equal (wpoly0 x e f) (pzero f)))
                (<= (len (wpoly0 x e f)) (1+ (edegree e f)))
                (equal (pev (plift (wpoly0 x e f) f e) x e) (fzero e))))
  :hints (("Goal" :use ((:instance dep-correct (w (cvs (powl (1+ (edegree e f)) x e) e f)) (n (edegree e f)))
                        (:instance vecsp-cvs (l (powl (1+ (edegree e f)) x e)))
                        (:instance extends-fieldp)
                        (:instance pev-plift-zero)
                        (:instance pstrip-pzero-zerovp (l (dep (cvs (powl (1+ (edegree e f)) x e) e f) (edegree e f) f))))
           :in-theory (e/d (wpoly0) (dep-correct pstrip-pzero-zerovp pev-plift-zero vecsp-cvs dep powl cvs))
           :do-not-induct t)))

(defthm wpoly0-nonconst
  (implies (and (tower e f) (feltp x e))
           (consp (cdr (wpoly0 x e f))))
  :hints (("Goal" :use ((:instance wpoly0-props)
                        (:instance extends-fieldp)
                        (:instance flift-zero-iff (x (car (wpoly0 x e f)))))
           :in-theory (e/d (polyp pzero) (wpoly0-props flift-zero-iff))
           :expand ((plift (wpoly0 x e f) f e)
                    (pev (plift (wpoly0 x e f) f e) x e)))))

(defund wpoly (x e f)
  (cmul (frecip (car (wpoly0 x e f)) f) (wpoly0 x e f) f))

(defthm wpoly-props
  (implies (and (tower e f) (feltp x e))
           (and (polyp (wpoly x e f) f)
                (monicp (wpoly x e f) f)
                (>= (degree (wpoly x e f)) 1)
                (<= (degree (wpoly x e f)) (edegree e f))
                (equal (pev (plift (wpoly x e f) f e) x e) (fzero e))))
  :hints (("Goal" :in-theory (e/d (wpoly monicp) (wpoly0-props wpoly0-nonconst))
           :use ((:instance wpoly0-props) (:instance wpoly0-nonconst) (:instance extends-fieldp)))))

;;; root of some irreducible factor

(defun root-factor (l x e f)
  (if (consp l)
      (if (equal (pev (plift (car l) f e) x e) (fzero e))
          (car l)
        (root-factor (cdr l) x e f))
    nil))

(defthm root-factor-props
  (implies (and (tower e f) (feltp x e) (good-factors l f)
                (equal (pev (plift (plist-prod l f) f e) x e) (fzero e)))
           (and (member-equal (root-factor l x e f) l)
                (equal (pev (plift (root-factor l x e f) f e) x e) (fzero e))))
  :hints (("Goal" :induct (root-factor l x e f))
          ("Subgoal *1/2" :use ((:instance extends-fieldp)))
          ("Subgoal *1/1" :use ((:instance extends-fieldp)))))

(defthm good-factors-member
  (implies (and (good-factors l f) (member-equal d l))
           (and (polyp d f) (monicp d f) (>= (degree d) 1)
                (or (< (degree d) 2) (not (reduciblep d f)))
                (<= (degree d) (sum-deg l)))))

(defthm deg1-irreducible
  (implies (< (degree d) 2) (not (reduciblep d f)))
  :hints (("Goal" :in-theory (enable reduciblep))))

(defthm MAIN-3
  (implies (and (extensionp e f)
                (feltp x e))
           (algebraic-witness x e f))
  :hints (("Goal" :use ((:instance algebraic-witness-suff
                                   (p (root-factor (factorization (wpoly x e f) f) x e f)))
                        (:instance root-factor-props (l (factorization (wpoly x e f) f)))
                        (:instance factorization-props (p (wpoly x e f)))
                        (:instance good-factors-member (l (factorization (wpoly x e f) f))
                                   (d (root-factor (factorization (wpoly x e f) f) x e f)))
                        (:instance deg1-irreducible (d (root-factor (factorization (wpoly x e f) f) x e f)))
                        (:instance wpoly-props))
           :in-theory (e/d (irreduciblep prootp)
                           (algebraic-witness-suff root-factor-props factorization-props good-factors-member
                                                   deg1-irreducible wpoly-props)))))

;;;;;;;;;;;;;;;;;;;; part 12 ;;;;;;;;;;;;;;;;;;;;


;;;; ===================== Embeddings, MAIN-4 =====================

(local (include-book "ordinals/lexicographic-book" :dir :system))

(defthm feltp-peval
  (implies (and (fap f) (feltsp l f) (consp l) (feltp x f))
           (feltp (peval l x f) f))
  :hints (("Goal" :induct (peval l x f))))

(defthm embed-nil (implies (not (consp phi)) (equal (embed x phi k f) (flift x f k)))
  :hints (("Goal" :expand ((embed x phi k f)))))
(defthm embed-consp (implies (consp phi) (equal (embed x phi k f) (peval (pembed x (cdr phi) k f) (car phi) k)))
  :hints (("Goal" :expand ((embed x phi k f)))))
(defthm pembed-cons (equal (pembed (cons a l) phi k f) (cons (embed a phi k f) (pembed l phi k f)))
  :hints (("Goal" :expand ((pembed (cons a l) phi k f)))))
(defthm pembed-atom (implies (not (consp l)) (equal (pembed l phi k f) nil))
  :hints (("Goal" :expand ((pembed l phi k f)))))
(defthm peval-singleton (equal (peval (list a) x f) a))

(defun ext-phi-induct (e f phi)
  (if (and (consp e) (not (equal e f))) (ext-phi-induct (cdr e) f (cdr phi)) phi))

(defthm len-pembed (equal (len (pembed l phi k f)) (len l))
  :hints (("Goal" :induct (len l) :in-theory (enable len))))
(defthm consp-pembed (equal (consp (pembed l phi k f)) (consp l)) :hints (("Goal" :expand ((pembed l phi k f)))))

(defthm feltsp-pembed-base
  (implies (and (tower k f) (feltsp l f)) (feltsp (pembed l nil k f) k))
  :hints (("Goal" :induct (len l) :expand ((pembed l nil k f) (embed (car l) nil k f)))))

(defun emb-induct (e f l phi)
  (declare (xargs :measure (list (len e) (len l))
                  :well-founded-relation l<))
  (if (consp l)
      (if (and (consp e) (not (equal e f)))
          (list (emb-induct e f (cdr l) phi)
                (emb-induct (cdr e) f (car l) (cdr phi)))
        (emb-induct e f (cdr l) phi))
    phi))

(defthm feltsp-pembed
  (implies (and (tower e f) (tower k f) (embeddingp phi e k f) (feltsp l e))
           (feltsp (pembed l phi k f) k))
  :hints (("Goal" :induct (emb-induct e f l phi)
           :in-theory (enable embeddingp prootp)
           :expand ((embed (car l) phi k f) (pembed l phi k f)))))


(defthm embed-fone
  (implies (and (tower e f) (tower k f) (embeddingp phi e k f))
           (equal (embed (fone e) phi k f) (fone k)))
  :hints (("Goal" :induct (ext-phi-induct e f phi) :in-theory (enable embeddingp pone))))

(defthm car-pembed
  (implies (consp l) (equal (car (pembed l phi k f)) (embed (car l) phi k f))))

(defthm pembed-poly-props
  (implies (and (tower e f) (tower k f) (consp e) (not (equal e f))
                (embeddingp (cdr phi) (cdr e) k f))
           (and (polyp (pembed (car e) (cdr phi) k f) k)
                (monicp (pembed (car e) (cdr phi) k f) k)
                (equal (len (pembed (car e) (cdr phi) k f)) (len (car e)))))
  :hints (("Goal"
           :use ((:instance fieldp-cdr)
                 (:instance feltsp-pembed (e (cdr e)) (phi (cdr phi)) (l (car e)))
                 (:instance embed-fone (e (cdr e)) (phi (cdr phi))))
           :in-theory (e/d (polyp monicp) (fieldp-cdr feltsp-pembed embed-fone)))))

;;; combinatorics

(defun dcdrs (l)
  (if (consp l)
      (if (member-equal (cdar l) (dcdrs (cdr l)))
          (dcdrs (cdr l))
        (cons (cdar l) (dcdrs (cdr l))))
    nil))

(defthm dlistp-dcdrs (dlistp (dcdrs l)))

(defthm member-dcdrs
  (implies (member-equal x l) (member-equal (cdr x) (dcdrs l))))

(defthm all-embeddingp-dcdrs
  (implies (and (all-embeddingp l e k f) (not (equal e f)))
           (all-embeddingp (dcdrs l) (cdr e) k f))
  :hints (("Goal" :in-theory (enable embeddingp))))

(defun pairs-with (rs tl)
  (if (consp rs) (cons (cons (car rs) tl) (pairs-with (cdr rs) tl)) nil))

(defun all-pairs (ts e k f)
  (if (consp ts)
      (append (pairs-with (proots (pembed (car e) (car ts) k f) k) (car ts))
              (all-pairs (cdr ts) e k f))
    nil))

(defthm len-pairs-with (equal (len (pairs-with rs tl)) (len rs)))

(defthm member-pairs-with
  (implies (member-equal a rs) (member-equal (cons a tl) (pairs-with rs tl))))

(defthm member-append-x
  (iff (member-equal x (append a b)) (or (member-equal x a) (member-equal x b))))

(defthm member-all-pairs
  (implies (and (member-equal tl ts) (member-equal a (proots (pembed (car e) tl k f) k)))
           (member-equal (cons a tl) (all-pairs ts e k f))))

(defthm embeddingp-step
  (implies (and (embeddingp phi e k f) (not (equal e f)))
           (and (consp phi)
                (prootp (car phi) (pembed (car e) (cdr phi) k f) k)
                (embeddingp (cdr phi) (cdr e) k f)))
  :hints (("Goal" :in-theory (enable embeddingp))))

(defthm car-in-proots
  (implies (and (tower e f) (tower k f) (consp e) (not (equal e f))
                (embeddingp phi e k f))
           (member-equal (car phi) (proots (pembed (car e) (cdr phi) k f) k)))
  :hints (("Goal" :use ((:instance MAIN-2 (f k) (p (pembed (car e) (cdr phi) k f)) (x (car phi)))
                        (:instance pembed-poly-props)
                        (:instance fieldp-cdr))
           :in-theory (disable MAIN-2 pembed-poly-props fieldp-cdr))))

(defthm sublistp-all-pairs
  (implies (and (tower e f) (tower k f) (consp e) (not (equal e f))
                (all-embeddingp l e k f) (sublistp l l0))
           (sublistp l (all-pairs (dcdrs l0) e k f)))
  :hints (("Goal" :induct (sublistp l l0))
          ("Subgoal *1/1" :use ((:instance member-all-pairs (ts (dcdrs l0)) (tl (cdr (car l))) (a (car (car l))))
                                (:instance car-in-proots (phi (car l))))
                          :in-theory (disable member-all-pairs car-in-proots))))

(defthm len-all-pairs
  (implies (and (tower e f) (tower k f) (consp e) (not (equal e f))
                (all-embeddingp ts (cdr e) k f))
           (<= (len (all-pairs ts e k f)) (* (degree (car e)) (len ts))))
  :hints (("Goal" :induct (all-pairs ts e k f))
          ("Subgoal *1/1" :use ((:instance MAIN-2 (f k) (p (pembed (car e) (car ts) k f)))
                                (:instance pembed-poly-props (phi (cons nil (car ts))))
                                (:instance fieldp-cdr))
                          :in-theory (disable MAIN-2 pembed-poly-props fieldp-cdr))))

(defthm sublistp-refl (sublistp l l))

(defthm embeddingp-base
  (implies (embeddingp phi f k f) (equal phi nil))
  :hints (("Goal" :in-theory (enable embeddingp)))
  :rule-classes nil)

(defthm base-len
  (implies (and (dlistp l) (all-embeddingp l f k f)) (<= (len l) 1))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :use ((:instance embeddingp-base (phi (car l)))
                                (:instance embeddingp-base (phi (cadr l))))
                          :expand ((all-embeddingp (cdr l) f k f)))))

(defun m4-induct (e f l)
  (if (and (consp e) (not (equal e f))) (m4-induct (cdr e) f (dcdrs l)) l))

(defthm MAIN-4
  (implies (and (extensionp e f) (extensionp k f)
                (dlistp l) (all-embeddingp l e k f))
           (<= (len l) (edegree e f)))
  :hints (("Goal" :induct (m4-induct e f l) :do-not-induct t)
          ("Subgoal *1/1" :use ((:instance sublistp-all-pairs (l0 l))
                                (:instance sublistp-<=-len (m (all-pairs (dcdrs l) e k f)))
                                (:instance len-all-pairs (ts (dcdrs l)))
                                (:instance fieldp-cdr)
                                (:instance extends-fieldp (e k)))
                          :nonlinearp t
                          :in-theory (disable sublistp-all-pairs len-all-pairs fieldp-cdr))))
