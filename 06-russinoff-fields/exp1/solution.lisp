;;; Fields in ACL2: base fields (Q, F_p, generic F0) and simple extensions.
;;;
;;; A field is described by a descriptor:
;;;   (:q)          the rational field Q
;;;   (:fp p)       the field of integers modulo the prime p
;;;   (:f0)         the generic field F0 (constrained functions)
;;;   (:ext f p)    the simple extension of the field f obtained by adjoining a
;;;                 root of the monic irreducible polynomial p over f with
;;;                 deg(p) >= 2.
;;; Polynomials over f are lists of coefficients, constant term first.
;;; Elements of (:ext f p) are the polynomials of degree < deg(p), represented
;;; as coefficient lists of length exactly deg(p); addition is polynomial
;;; addition and multiplication is polynomial multiplication modulo p.
;;; The field structure: FEP (element recognizer), FADD, FMUL, FZERO, FONE,
;;; FNEG, FINV.  FIELDP recognizes fields.  MAIN: every field satisfies the
;;; field axioms.

(in-package "ACL2")

(include-book "kestrel/prime-fields/prime-fields" :dir :system)

;;; ---------------------------------------------------------------------------
;;; The generic field F0
;;; ---------------------------------------------------------------------------

(encapsulate
  (((f0p *) => *)
   ((f0add * *) => *)
   ((f0mul * *) => *)
   ((f0zero) => *)
   ((f0one) => *)
   ((f0neg *) => *)
   ((f0inv *) => *))
  (local (defun f0p (x) (rationalp x)))
  (local (defun f0add (x y) (+ x y)))
  (local (defun f0mul (x y) (* x y)))
  (local (defun f0zero () 0))
  (local (defun f0one () 1))
  (local (defun f0neg (x) (- x)))
  (local (defun f0inv (x) (/ x)))
  (defthm f0p-f0add (implies (and (f0p x) (f0p y)) (f0p (f0add x y))))
  (defthm f0p-f0mul (implies (and (f0p x) (f0p y)) (f0p (f0mul x y))))
  (defthm f0p-f0zero (f0p (f0zero)))
  (defthm f0p-f0one (f0p (f0one)))
  (defthm f0p-f0neg (implies (f0p x) (f0p (f0neg x))))
  (defthm f0p-f0inv (implies (and (f0p x) (not (equal x (f0zero)))) (f0p (f0inv x))))
  (defthm f0add-comm (implies (and (f0p x) (f0p y)) (equal (f0add x y) (f0add y x))))
  (defthm f0mul-comm (implies (and (f0p x) (f0p y)) (equal (f0mul x y) (f0mul y x))))
  (defthm f0add-assoc (implies (and (f0p x) (f0p y) (f0p z))
                               (equal (f0add (f0add x y) z) (f0add x (f0add y z)))))
  (defthm f0mul-assoc (implies (and (f0p x) (f0p y) (f0p z))
                               (equal (f0mul (f0mul x y) z) (f0mul x (f0mul y z)))))
  (defthm f0-distrib (implies (and (f0p x) (f0p y) (f0p z))
                              (equal (f0mul x (f0add y z)) (f0add (f0mul x y) (f0mul x z)))))
  (defthm f0add-zero (implies (f0p x) (equal (f0add x (f0zero)) x)))
  (defthm f0mul-one (implies (f0p x) (equal (f0mul x (f0one)) x)))
  (defthm f0add-neg (implies (f0p x) (equal (f0add x (f0neg x)) (f0zero))))
  (defthm f0mul-inv (implies (and (f0p x) (not (equal x (f0zero))))
                             (equal (f0mul x (f0inv x)) (f0one))))
  (defthm f0-zero-not-one (not (equal (f0zero) (f0one)))))

;;; ---------------------------------------------------------------------------
;;; Field descriptors:  (:Q)   (:FP p)   (:F0)   (:EXT f p)
;;; ---------------------------------------------------------------------------

(defun fdepth (f)
  (if (and (consp f) (eq (car f) :ext))
      (+ 1 (fdepth (cadr f)))
    0))

(defun last1 (x)
  (cond ((atom x) nil)
        ((atom (cdr x)) (car x))
        (t (last1 (cdr x)))))

(defun butlast1 (x)
  (cond ((atom x) nil)
        ((atom (cdr x)) nil)
        (t (cons (car x) (butlast1 (cdr x))))))

(defun fkind (f) (if (consp f) (car f) nil))

(defmacro fmeas (f) `(make-ord 2 (+ 1 (fdepth ,f)) 0))
(defmacro vmeas (f tier n) `(make-ord 2 (+ 1 (fdepth ,f)) (make-ord 1 ,tier (nfix ,n))))

(mutual-recursion

 (defun fep (f x)
   (declare (xargs :measure (fmeas f)))
   (case (fkind f)
     (:q (rationalp x))
     (:fp (pfield::fep x (cadr f)))
     (:f0 (f0p x))
     (:ext (vecp (cadr f) (- (len (caddr f)) 1) x))
     (otherwise nil)))

 (defun fadd (f x y)
   (declare (xargs :measure (fmeas f)))
   (case (fkind f)
     (:q (+ (rfix x) (rfix y)))
     (:fp (pfield::add x y (cadr f)))
     (:f0 (f0add x y))
     (:ext (vadd (cadr f) x y))
     (otherwise nil)))

 (defun fmul (f x y)
   (declare (xargs :measure (fmeas f)))
   (case (fkind f)
     (:q (* (rfix x) (rfix y)))
     (:fp (pfield::mul x y (cadr f)))
     (:f0 (f0mul x y))
     (:ext (vapply (cadr f) (caddr f) x y))
     (otherwise nil)))

 (defun fneg (f x)
   (declare (xargs :measure (fmeas f)))
   (case (fkind f)
     (:q (- (rfix x)))
     (:fp (pfield::neg x (cadr f)))
     (:f0 (f0neg x))
     (:ext (vneg (cadr f) x))
     (otherwise nil)))

 (defun fzero (f)
   (declare (xargs :measure (fmeas f)))
   (case (fkind f)
     (:q 0)
     (:fp 0)
     (:f0 (f0zero))
     (:ext (vzero (cadr f) (- (len (caddr f)) 1)))
     (otherwise nil)))

 (defun fone (f)
   (declare (xargs :measure (fmeas f)))
   (case (fkind f)
     (:q 1)
     (:fp 1)
     (:f0 (f0one))
     (:ext (cons (fone (cadr f)) (vzero (cadr f) (- (len (caddr f)) 2))))
     (otherwise nil)))

 ;; vectors of length n over b
 (defun vecp (b n x)
   (declare (xargs :measure (vmeas b 1 n)))
   (if (zp n)
       (equal x nil)
     (and (consp x)
          (fep b (car x))
          (vecp b (- n 1) (cdr x)))))

 (defun vzero (b n)
   (declare (xargs :measure (vmeas b 1 n)))
   (if (zp n)
       nil
     (cons (fzero b) (vzero b (- n 1)))))

 (defun vadd (b x y)
   (declare (xargs :measure (vmeas b 1 (len x))))
   (cond ((atom x) y)
         ((atom y) x)
         (t (cons (fadd b (car x) (car y))
                  (vadd b (cdr x) (cdr y))))))

 (defun vneg (b x)
   (declare (xargs :measure (vmeas b 1 (len x))))
   (if (atom x)
       nil
     (cons (fneg b (car x)) (vneg b (cdr x)))))

 (defun vscale (b c x)
   (declare (xargs :measure (vmeas b 1 (len x))))
   (if (atom x)
       nil
     (cons (fmul b c (car x)) (vscale b c (cdr x)))))

 ;; multiplication by the indeterminate, modulo the monic polynomial p
 (defun vtimesx (b p v)
   (declare (xargs :measure (vmeas b 2 0)))
   (if (atom v)
       nil
     (butlast1 (vadd b
                     (cons (fzero b) v)
                     (vneg b (vscale b (last1 v) p))))))

 ;; (vapply b p a v) = a(X) * v  mod p, where a is a polynomial and v is a
 ;; residue vector (polynomials are lists of coefficients, constant first)
 (defun vapply (b p a v)
   (declare (xargs :measure (vmeas b 3 (len a))))
   (if (atom a)
       (vzero b (- (len p) 1))
     (vadd b
           (vscale b (car a) v)
           (vtimesx b p (vapply b p (cdr a) v)))))
 )
;;; ---------------------------------------------------------------------------
;;; Structural (length) facts about the vector operations; no axioms needed
;;; ---------------------------------------------------------------------------

(in-theory (disable fep fadd fmul fneg fzero fone vecp vzero vadd vneg vscale
                    vtimesx vapply))

(defun ind1 (x) (if (atom x) nil (ind1 (cdr x))))
(defun ind2 (x y) (if (or (atom x) (atom y)) (list x y) (ind2 (cdr x) (cdr y))))
(defun ind3 (x y z) (if (or (atom x) (atom y) (atom z)) (list x y z)
                      (ind3 (cdr x) (cdr y) (cdr z))))
(defun indn (n x) (if (zp n) x (indn (- n 1) (cdr x))))

(defun polyp (b x)
  (if (atom x)
      (equal x nil)
    (and (fep b (car x))
         (polyp b (cdr x)))))

(defthm polyp-true-listp (implies (polyp b x) (true-listp x)) :rule-classes :forward-chaining)

(defthm vecp-is-polyp
  (equal (vecp b n x)
         (and (polyp b x) (equal (len x) (nfix n))))
  :hints (("Goal" :induct (indn n x) :in-theory (enable vecp))))

(defthm vzero-opener
  (implies (not (zp n))
           (equal (vzero b n) (cons (fzero b) (vzero b (- n 1)))))
  :hints (("Goal" :in-theory (enable vzero))))
(defthm vzero-zp
  (implies (zp n) (equal (vzero b n) nil))
  :hints (("Goal" :in-theory (enable vzero))))
(defthm vadd-cons
  (equal (vadd b (cons a x) (cons c y)) (cons (fadd b a c) (vadd b x y)))
  :hints (("Goal" :in-theory (enable vadd))))
(defthm vadd-atom1 (implies (atom x) (equal (vadd b x y) y))
  :hints (("Goal" :in-theory (enable vadd))))
(defthm vadd-atom2 (implies (and (consp x) (atom y)) (equal (vadd b x y) x))
  :hints (("Goal" :in-theory (enable vadd))))
(defthm vneg-cons (equal (vneg b (cons a x)) (cons (fneg b a) (vneg b x)))
  :hints (("Goal" :in-theory (enable vneg))))
(defthm vneg-atom (implies (atom x) (equal (vneg b x) nil))
  :hints (("Goal" :in-theory (enable vneg))))
(defthm vscale-cons (equal (vscale b c (cons a x)) (cons (fmul b c a) (vscale b c x)))
  :hints (("Goal" :in-theory (enable vscale))))
(defthm vscale-atom (implies (atom x) (equal (vscale b c x) nil))
  :hints (("Goal" :in-theory (enable vscale))))
(defthm vtimesx-def
  (equal (vtimesx b p v)
         (if (atom v)
             nil
           (butlast1 (vadd b (cons (fzero b) v) (vneg b (vscale b (last1 v) p))))))
  :hints (("Goal" :in-theory (enable vtimesx))))
(defthm vapply-cons
  (equal (vapply b p (cons a x) v)
         (vadd b (vscale b a v) (vtimesx b p (vapply b p x v))))
  :hints (("Goal" :in-theory (enable vapply))))
(defthm vapply-atom
  (implies (atom a) (equal (vapply b p a v) (vzero b (- (len p) 1))))
  :hints (("Goal" :in-theory (enable vapply))))

(defthm len-vzero (equal (len (vzero b n)) (nfix n)) :hints (("Goal" :induct (indn n x))))
(defthm consp-vzero (equal (consp (vzero b n)) (not (zp n))) :hints (("Goal" :induct (indn n x))))
(defthm len-vadd (equal (len (vadd b x y)) (max (len x) (len y)))
  :hints (("Goal" :induct (ind2 x y) :in-theory (enable vadd))))
(defthm len-vneg (equal (len (vneg b x)) (len x)) :hints (("Goal" :induct (ind1 x))))
(defthm len-vscale (equal (len (vscale b c x)) (len x)) :hints (("Goal" :induct (ind1 x))))
(defthm consp-vadd (equal (consp (vadd b x y)) (or (consp x) (consp y)))
  :hints (("Goal" :induct (ind2 x y) :in-theory (enable vadd))))
(defthm consp-vneg (equal (consp (vneg b x)) (consp x)) :hints (("Goal" :induct (ind1 x))))
(defthm consp-vscale (equal (consp (vscale b c x)) (consp x)) :hints (("Goal" :induct (ind1 x))))
(defthm len-butlast1 (equal (len (butlast1 x)) (if (consp x) (- (len x) 1) 0)))

(defthm len-vtimesx
  (equal (len (vtimesx b p v))
         (if (consp v) (- (max (+ 1 (len v)) (len p)) 1) 0)))

(defthm len-vapply
  (implies (and (equal (len v) (- (len p) 1))
                (<= 2 (len p)))
           (equal (len (vapply b p a v)) (- (len p) 1)))
  :hints (("Goal" :induct (ind1 a))))

;;; one, padding, trimming, remainder

(defun vone (b n)
  (if (zp n) nil (cons (fone b) (vzero b (- n 1)))))

(defthm len-vone (equal (len (vone b n)) (nfix n)))

(defun pad (b x n)
  (append x (vzero b (- (nfix n) (len x)))))

(defun trim (b x)
  (if (atom x)
      nil
    (let ((r (trim b (cdr x))))
      (if (and (atom r) (equal (car x) (fzero b)))
          nil
        (cons (car x) r)))))

(defthm len-trim (<= (len (trim b x)) (len x)) :rule-classes :linear)

(defthm trim-vzero
  (equal (trim b (vzero b n)) nil)
  :hints (("Goal" :induct (indn n x))))

(defthm trim-append-vzero
  (equal (trim b (append x (vzero b n))) (trim b x))
  :hints (("Goal" :induct (ind1 x)
           :expand ((trim b (append x (vzero b n))) (trim b x)))))

;; remainder of a modulo the monic polynomial q (Horner's scheme)
(defun pmod (b a q)
  (vapply b q a (vone b (- (len q) 1))))

;; the corresponding quotient
(defun pquot (b a q)
  (if (atom a)
      nil
    (cons (last1 (pmod b (cdr a) q))
          (pquot b (cdr a) q))))

(defthm len-pmod
  (implies (<= 2 (len q))
           (equal (len (pmod b a q)) (- (len q) 1))))

(in-theory (disable pmod))
;;; ---------------------------------------------------------------------------
;;; Divisibility, reducibility, and the multiplicative inverse
;;; ---------------------------------------------------------------------------

(defun vzerop (b x)
  (if (atom x)
      t
    (and (equal (car x) (fzero b))
         (vzerop b (cdr x)))))

;; q divides a  iff  the remainder of a modulo q is zero
(defun pdivides (b q a)
  (vzerop b (pmod b a q)))

;; q is a monic polynomial over b (coefficients listed from the constant term up)
(defun monicp (b q)
  (and (polyp b q)
       (consp q)
       (equal (last1 q) (fone b))))

;; degree of a nonempty coefficient list
(defun deg (q) (- (len q) 1))

;; p is reducible over b if it has a non-constant monic divisor of lesser degree
(defun-sk reducible (b p)
  (exists q (and (monicp b q)
                 (< 0 (deg q))
                 (< (deg q) (deg p))
                 (pdivides b q p))))

(defun irreducible (b p) (not (reducible b p)))

(defthmd atom-trim-is-vzerop
  (equal (atom (trim b x)) (vzerop b x)))

(defthm len-trim-pmod
  (implies (consp (cdr x))
           (< (len (trim b (pmod b p (vscale b c x))))
              (len x)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance len-trim (x (pmod b p (vscale b c x))))
                        (:instance len-pmod (a p) (q (vscale b c x))))
           :expand ((len x) (len (cdr x)))
           :in-theory (disable len-trim len-pmod))))

(in-theory (disable trim))

(mutual-recursion
 (defun finv (f x)
   (declare (xargs :measure (make-ord 1 (+ 1 (fdepth f)) 0)
                   :hints (("Goal" :use ((:instance atom-trim-is-vzerop (x g)))))))
   (case (fkind f)
     (:q (/ (rfix x)))
     (:fp (pfield::inv x (cadr f)))
     (:f0 (f0inv x))
     (:ext (inv-search (cadr f) (caddr f) x (vone (cadr f) (- (len (caddr f)) 1))))
     (otherwise nil)))

 ;; Invariant: g = s * u  (mod p), g nonzero.  Each step replaces g by the
 ;; remainder of p modulo the monic multiple of g (lower degree), until g is a
 ;; nonzero constant c; then c^{-1} s is the inverse of u.
 (defun inv-search (b p g s)
   (declare (xargs :measure (make-ord 1 (+ 1 (fdepth b)) (len (trim b g)))))
   (let ((tg (trim b g)))
     (if (atom tg)
         s
       (let ((c (last1 tg)))
         (if (atom (cdr tg))
             (vscale b (finv b c) s)
           (let* ((g1 (vscale b (finv b c) tg))
                  (r (pmod b p g1)))
             (if (vzerop b r)
                 s
               (inv-search b p (pad b r (- (len p) 1))
                           (vapply b p (vscale b (fneg b (finv b c)) (pquot b p g1))
                                   s))))))))))
;;; the field axioms, as a single predicate on a field descriptor

(defun axioms-body (f x y z)
  (and (fep f (fzero f))
         (fep f (fone f))
         (not (equal (fzero f) (fone f)))
         (implies (and (fep f x) (fep f y))
                  (and (fep f (fadd f x y))
                       (fep f (fmul f x y))
                       (equal (fadd f x y) (fadd f y x))
                       (equal (fmul f x y) (fmul f y x))))
         (implies (fep f x)
                  (and (fep f (fneg f x))
                       (equal (fadd f x (fzero f)) x)
                       (equal (fmul f x (fone f)) x)
                       (equal (fadd f x (fneg f x)) (fzero f))))
         (implies (and (fep f x) (not (equal x (fzero f))))
                  (and (fep f (finv f x))
                       (equal (fmul f x (finv f x)) (fone f))))
         (implies (and (fep f x) (fep f y) (fep f z))
                  (and (equal (fadd f (fadd f x y) z) (fadd f x (fadd f y z)))
                       (equal (fmul f (fmul f x y) z) (fmul f x (fmul f y z)))
                       (equal (fmul f x (fadd f y z))
                              (fadd f (fmul f x y) (fmul f x z)))))))

(defun-sk field-axioms (f)
  (forall (x y z) (axioms-body f x y z))
  :rewrite :direct)

(in-theory (disable field-axioms))

(in-theory (enable fep fadd fmul fneg fzero fone finv))

(defthm axioms-body-q
  (axioms-body '(:q) x y z))

(defthm axioms-body-f0
  (axioms-body '(:f0) x y z)
  :hints (("Goal" :in-theory (disable f0add-comm f0mul-comm f0add-assoc f0mul-assoc
                                      f0-distrib f0add-zero f0mul-one f0add-neg f0mul-inv)
           :use (f0add-comm f0mul-comm f0add-assoc f0mul-assoc
                 f0-distrib f0add-zero f0mul-one f0add-neg f0mul-inv))))

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(defthm axioms-body-fp
  (implies (dm::primep p)
           (axioms-body (list :fp p) x y z))
  :hints (("Goal" :in-theory (enable pfield::mul-of-add-arg2))))

(in-theory (disable axioms-body))

(defthm field-axioms-q
  (field-axioms '(:q))
  :hints (("Goal" :in-theory (enable field-axioms))))

(defthm field-axioms-f0
  (field-axioms '(:f0))
  :hints (("Goal" :in-theory (enable field-axioms))))

(defthm field-axioms-fp
  (implies (dm::primep p)
           (field-axioms (list :fp p)))
  :hints (("Goal" :in-theory (enable field-axioms))))
;;; ---------------------------------------------------------------------------
;;; Consequences of the field axioms for an arbitrary field descriptor b
;;; ---------------------------------------------------------------------------

(in-theory (disable fep fadd fmul fneg fzero fone vecp vzero vadd vneg vscale
                    vtimesx vapply finv inv-search))

(defthm b-fep-zero (implies (field-axioms b) (fep b (fzero b))) :hints (("Goal" :use ((:instance field-axioms-necc (f b)))
     :in-theory (e/d (axioms-body) (field-axioms-necc)))))
(defthm b-fep-one (implies (field-axioms b) (fep b (fone b))) :hints (("Goal" :use ((:instance field-axioms-necc (f b)))
     :in-theory (e/d (axioms-body) (field-axioms-necc)))))
(defthm b-zero-not-one (implies (field-axioms b) (not (equal (fzero b) (fone b))))
  :hints (("Goal" :use ((:instance field-axioms-necc (f b)))
     :in-theory (e/d (axioms-body) (field-axioms-necc)))))
(defthm b-one-not-zero (implies (field-axioms b) (not (equal (fone b) (fzero b))))
  :hints (("Goal" :use ((:instance field-axioms-necc (f b)))
     :in-theory (e/d (axioms-body) (field-axioms-necc)))))
(defthm b-fep-add (implies (and (field-axioms b) (fep b x) (fep b y)) (fep b (fadd b x y)))
  :hints (("Goal" :use ((:instance field-axioms-necc (f b)))
     :in-theory (e/d (axioms-body) (field-axioms-necc)))))
(defthm b-fep-mul (implies (and (field-axioms b) (fep b x) (fep b y)) (fep b (fmul b x y)))
  :hints (("Goal" :use ((:instance field-axioms-necc (f b)))
     :in-theory (e/d (axioms-body) (field-axioms-necc)))))
(defthm b-fep-neg (implies (and (field-axioms b) (fep b x)) (fep b (fneg b x)))
  :hints (("Goal" :use ((:instance field-axioms-necc (f b)))
     :in-theory (e/d (axioms-body) (field-axioms-necc)))))
(defthm b-fep-inv (implies (and (field-axioms b) (fep b x) (not (equal x (fzero b))))
                           (fep b (finv b x)))
  :hints (("Goal" :use ((:instance field-axioms-necc (f b)))
     :in-theory (e/d (axioms-body) (field-axioms-necc)))))
(defthm b-add-comm (implies (and (field-axioms b) (fep b x) (fep b y))
                            (equal (fadd b x y) (fadd b y x)))
  :hints (("Goal" :use ((:instance field-axioms-necc (f b)))
     :in-theory (e/d (axioms-body) (field-axioms-necc)))))
(defthm b-mul-comm (implies (and (field-axioms b) (fep b x) (fep b y))
                            (equal (fmul b x y) (fmul b y x)))
  :hints (("Goal" :use ((:instance field-axioms-necc (f b)))
     :in-theory (e/d (axioms-body) (field-axioms-necc)))))
(defthm b-add-assoc (implies (and (field-axioms b) (fep b x) (fep b y) (fep b z))
                             (equal (fadd b (fadd b x y) z) (fadd b x (fadd b y z))))
  :hints (("Goal" :use ((:instance field-axioms-necc (f b)))
     :in-theory (e/d (axioms-body) (field-axioms-necc)))))
(defthm b-mul-assoc (implies (and (field-axioms b) (fep b x) (fep b y) (fep b z))
                             (equal (fmul b (fmul b x y) z) (fmul b x (fmul b y z))))
  :hints (("Goal" :use ((:instance field-axioms-necc (f b)))
     :in-theory (e/d (axioms-body) (field-axioms-necc)))))
(defthm b-distrib (implies (and (field-axioms b) (fep b x) (fep b y) (fep b z))
                           (equal (fmul b x (fadd b y z))
                                  (fadd b (fmul b x y) (fmul b x z))))
  :hints (("Goal" :use ((:instance field-axioms-necc (f b)))
     :in-theory (e/d (axioms-body) (field-axioms-necc)))))
(defthm b-add-zero (implies (and (field-axioms b) (fep b x))
                            (equal (fadd b x (fzero b)) x))
  :hints (("Goal" :use ((:instance field-axioms-necc (f b)))
     :in-theory (e/d (axioms-body) (field-axioms-necc)))))
(defthm b-mul-one (implies (and (field-axioms b) (fep b x))
                           (equal (fmul b x (fone b)) x))
  :hints (("Goal" :use ((:instance field-axioms-necc (f b)))
     :in-theory (e/d (axioms-body) (field-axioms-necc)))))
(defthm b-add-neg (implies (and (field-axioms b) (fep b x))
                           (equal (fadd b x (fneg b x)) (fzero b)))
  :hints (("Goal" :use ((:instance field-axioms-necc (f b)))
     :in-theory (e/d (axioms-body) (field-axioms-necc)))))
(defthm b-mul-inv (implies (and (field-axioms b) (fep b x) (not (equal x (fzero b))))
                           (equal (fmul b x (finv b x)) (fone b)))
  :hints (("Goal" :use ((:instance field-axioms-necc (f b)))
     :in-theory (e/d (axioms-body) (field-axioms-necc)))))

;;; derived facts

(defthm b-zero-add (implies (and (field-axioms b) (fep b x))
                            (equal (fadd b (fzero b) x) x))
  :hints (("Goal" :use ((:instance b-add-comm (x x) (y (fzero b))))
           :in-theory (disable b-add-comm))))

(defthm b-one-mul (implies (and (field-axioms b) (fep b x))
                           (equal (fmul b (fone b) x) x))
  :hints (("Goal" :use ((:instance b-mul-comm (x x) (y (fone b))))
           :in-theory (disable b-mul-comm))))

(defthm b-neg-add (implies (and (field-axioms b) (fep b x))
                           (equal (fadd b (fneg b x) x) (fzero b)))
  :hints (("Goal" :use ((:instance b-add-comm (x x) (y (fneg b x))))
           :in-theory (disable b-add-comm))))

(defthm b-add-comm2 (implies (and (field-axioms b) (fep b x) (fep b y) (fep b z))
                             (equal (fadd b x (fadd b y z)) (fadd b y (fadd b x z))))
  :hints (("Goal" :use ((:instance b-add-assoc (x x) (y y) (z z))
                        (:instance b-add-assoc (x y) (y x) (z z))
                        (:instance b-add-comm (x x) (y y)))
           :in-theory (disable b-add-assoc b-add-comm))))

(defthm b-mul-comm2 (implies (and (field-axioms b) (fep b x) (fep b y) (fep b z))
                             (equal (fmul b x (fmul b y z)) (fmul b y (fmul b x z))))
  :hints (("Goal" :use ((:instance b-mul-assoc (x x) (y y) (z z))
                        (:instance b-mul-assoc (x y) (y x) (z z))
                        (:instance b-mul-comm (x x) (y y)))
           :in-theory (disable b-mul-assoc b-mul-comm))))

(defthm b-add-neg-cancel (implies (and (field-axioms b) (fep b x) (fep b y))
                                  (equal (fadd b x (fadd b (fneg b x) y)) y))
  :hints (("Goal" :use ((:instance b-add-assoc (x x) (y (fneg b x)) (z y)))
           :in-theory (disable b-add-assoc b-add-comm2))))

(defthm b-neg-add-cancel (implies (and (field-axioms b) (fep b x) (fep b y))
                                  (equal (fadd b (fneg b x) (fadd b x y)) y))
  :hints (("Goal" :use ((:instance b-add-assoc (x (fneg b x)) (y x) (z y)))
           :in-theory (disable b-add-assoc b-add-comm2))))

;; uniqueness of additive inverses
(defthmd b-neg-unique
  (implies (and (field-axioms b) (fep b x) (fep b y)
                (equal (fadd b x y) (fzero b)))
           (equal (fneg b x) y))
  :hints (("Goal" :use ((:instance b-neg-add-cancel (x x) (y y)))
           :in-theory (disable b-neg-add-cancel))))

(defthm b-distrib2 (implies (and (field-axioms b) (fep b x) (fep b y) (fep b z))
                            (equal (fmul b (fadd b y z) x)
                                   (fadd b (fmul b y x) (fmul b z x))))
  :hints (("Goal" :use ((:instance b-mul-comm (x x) (y (fadd b y z)))
                        (:instance b-mul-comm (x x) (y y))
                        (:instance b-mul-comm (x x) (y z)))
           :in-theory (disable b-mul-comm b-mul-comm2))))

(defthm b-mul-zero (implies (and (field-axioms b) (fep b x))
                            (equal (fmul b x (fzero b)) (fzero b)))
  :hints (("Goal" :use ((:instance b-distrib (x x) (y (fzero b)) (z (fzero b)))
                        (:instance b-neg-add-cancel (x (fmul b x (fzero b)))
                                   (y (fmul b x (fzero b)))))
           :in-theory (disable b-distrib b-neg-add-cancel b-add-comm b-add-comm2))))

(defthm b-zero-mul (implies (and (field-axioms b) (fep b x))
                            (equal (fmul b (fzero b) x) (fzero b)))
  :hints (("Goal" :use ((:instance b-mul-comm (x x) (y (fzero b))))
           :in-theory (disable b-mul-comm))))

(defthm b-neg-neg (implies (and (field-axioms b) (fep b x))
                           (equal (fneg b (fneg b x)) x))
  :hints (("Goal" :use ((:instance b-neg-unique (x (fneg b x)) (y x))))))

(defthm b-neg-zero (implies (field-axioms b)
                            (equal (fneg b (fzero b)) (fzero b)))
  :hints (("Goal" :use ((:instance b-neg-unique (x (fzero b)) (y (fzero b)))))))

(defthm b-neg-of-add (implies (and (field-axioms b) (fep b x) (fep b y))
                              (equal (fneg b (fadd b x y))
                                     (fadd b (fneg b x) (fneg b y))))
  :hints (("Goal" :use ((:instance b-neg-unique (x (fadd b x y))
                                   (y (fadd b (fneg b x) (fneg b y))))))))

(defthm b-mul-neg-left (implies (and (field-axioms b) (fep b x) (fep b y))
                                (equal (fmul b (fneg b x) y)
                                       (fneg b (fmul b x y))))
  :hints (("Goal" :use ((:instance b-neg-unique (x (fmul b x y))
                                   (y (fmul b (fneg b x) y)))
                        (:instance b-distrib2 (x y) (y x) (z (fneg b x))))
           :in-theory (disable b-distrib2))))

(defthm b-mul-neg-right (implies (and (field-axioms b) (fep b x) (fep b y))
                                 (equal (fmul b x (fneg b y))
                                        (fneg b (fmul b x y))))
  :hints (("Goal" :use ((:instance b-mul-comm (x x) (y (fneg b y)))
                        (:instance b-mul-comm (x x) (y y)))
           :in-theory (disable b-mul-comm b-mul-comm2))))

;; cancellation for addition
(defthmd b-add-cancel
  (implies (and (field-axioms b) (fep b x) (fep b y) (fep b z))
           (equal (equal (fadd b x y) (fadd b x z))
                  (equal y z)))
  :hints (("Goal" :use ((:instance b-neg-add-cancel (x x) (y y))
                        (:instance b-neg-add-cancel (x x) (y z)))
           :in-theory (disable b-neg-add-cancel b-add-comm b-add-comm2))))

(defthm b-inv-mul (implies (and (field-axioms b) (fep b x) (not (equal x (fzero b))))
                           (equal (fmul b (finv b x) x) (fone b)))
  :hints (("Goal" :use ((:instance b-mul-comm (x x) (y (finv b x))))
           :in-theory (disable b-mul-comm))))

(defthm b-mul-inv-cancel (implies (and (field-axioms b) (fep b x) (fep b y)
                                       (not (equal x (fzero b))))
                                  (equal (fmul b (finv b x) (fmul b x y)) y))
  :hints (("Goal" :use ((:instance b-mul-assoc (x (finv b x)) (y x) (z y)))
           :in-theory (disable b-mul-assoc b-mul-comm2 b-mul-comm))))
;;; ---------------------------------------------------------------------------
;;; Vector algebra over a base field b satisfying the axioms
;;; ---------------------------------------------------------------------------

(defthm vadd-consp
  (implies (and (consp x) (consp y))
           (equal (vadd b x y) (cons (fadd b (car x) (car y)) (vadd b (cdr x) (cdr y)))))
  :hints (("Goal" :in-theory (enable vadd))))
(defthm vneg-consp
  (implies (consp x) (equal (vneg b x) (cons (fneg b (car x)) (vneg b (cdr x)))))
  :hints (("Goal" :in-theory (enable vneg))))
(defthm vscale-consp
  (implies (consp x) (equal (vscale b c x) (cons (fmul b c (car x)) (vscale b c (cdr x)))))
  :hints (("Goal" :in-theory (enable vscale))))

(defthm polyp-cons (equal (polyp b (cons a x)) (and (fep b a) (polyp b x))))
(defthm polyp-vadd (implies (and (field-axioms b) (polyp b x) (polyp b y)) (polyp b (vadd b x y)))
  :hints (("Goal" :induct (ind2 x y))))
(defthm polyp-vneg (implies (and (field-axioms b) (polyp b x)) (polyp b (vneg b x)))
  :hints (("Goal" :induct (ind1 x))))
(defthm polyp-vscale (implies (and (field-axioms b) (fep b c) (polyp b x)) (polyp b (vscale b c x)))
  :hints (("Goal" :induct (ind1 x))))
(defthm polyp-vzero (implies (field-axioms b) (polyp b (vzero b n)))
  :hints (("Goal" :induct (indn n x))))
(defthm polyp-butlast1 (implies (polyp b x) (polyp b (butlast1 x))))
(defthm fep-last1 (implies (and (polyp b x) (consp x)) (fep b (last1 x))))
(defthm polyp-append (implies (and (polyp b x) (polyp b y)) (polyp b (append x y))))
(defthm polyp-vtimesx (implies (and (field-axioms b) (polyp b p) (polyp b v))
                               (polyp b (vtimesx b p v))))
(defthm vapply-consp
  (implies (consp a)
           (equal (vapply b p a v)
                  (vadd b (vscale b (car a) v) (vtimesx b p (vapply b p (cdr a) v)))))
  :hints (("Goal" :in-theory (enable vapply))))
(defthm polyp-vapply (implies (and (field-axioms b) (polyp b p) (polyp b v) (polyp b a))
                              (polyp b (vapply b p a v)))
  :hints (("Goal" :induct (ind1 a))))
(defthm polyp-vone (implies (field-axioms b) (polyp b (vone b n))))
(defthm polyp-pad (implies (and (field-axioms b) (polyp b x)) (polyp b (pad b x n))))
(defthm polyp-trim (implies (polyp b x) (polyp b (trim b x)))
  :hints (("Goal" :in-theory (enable trim))))
(defthm polyp-pmod (implies (and (field-axioms b) (polyp b q) (polyp b a))
                            (polyp b (pmod b a q)))
  :hints (("Goal" :in-theory (enable pmod))))

;;; additive group

(defthm vadd-comm
  (implies (and (field-axioms b) (polyp b x) (polyp b y))
           (equal (vadd b x y) (vadd b y x)))
  :hints (("Goal" :induct (ind2 x y))))

(defthm vadd-assoc
  (implies (and (field-axioms b) (polyp b x) (polyp b y) (polyp b z))
           (equal (vadd b (vadd b x y) z) (vadd b x (vadd b y z))))
  :hints (("Goal" :induct (ind3 x y z))))

(defthm vadd-comm2
  (implies (and (field-axioms b) (polyp b x) (polyp b y) (polyp b z))
           (equal (vadd b x (vadd b y z)) (vadd b y (vadd b x z))))
  :hints (("Goal" :use ((:instance vadd-assoc (x x) (y y) (z z))
                        (:instance vadd-assoc (x y) (y x) (z z))
                        (:instance vadd-comm (x x) (y y)))
           :in-theory (disable vadd-assoc vadd-comm))))

(defthm vadd-vzero
  (implies (and (field-axioms b) (polyp b x) (<= (nfix n) (len x)))
           (equal (vadd b x (vzero b n)) x))
  :hints (("Goal" :induct (indn n x))))

(defthm vzero-vadd
  (implies (and (field-axioms b) (polyp b x) (<= (nfix n) (len x)))
           (equal (vadd b (vzero b n) x) x))
  :hints (("Goal" :induct (indn n x))))

(defthm vadd-vneg
  (implies (and (field-axioms b) (polyp b x))
           (equal (vadd b x (vneg b x)) (vzero b (len x))))
  :hints (("Goal" :induct (ind1 x))))

(defthm vneg-vadd-same
  (implies (and (field-axioms b) (polyp b x))
           (equal (vadd b (vneg b x) x) (vzero b (len x))))
  :hints (("Goal" :induct (ind1 x))))

(defthm vneg-vneg (implies (and (field-axioms b) (polyp b x)) (equal (vneg b (vneg b x)) x))
  :hints (("Goal" :induct (ind1 x))))
(defthm vneg-vzero (implies (field-axioms b) (equal (vneg b (vzero b n)) (vzero b n)))
  :hints (("Goal" :induct (indn n x))))
(defthm vneg-of-vadd
  (implies (and (field-axioms b) (polyp b x) (polyp b y))
           (equal (vneg b (vadd b x y)) (vadd b (vneg b x) (vneg b y))))
  :hints (("Goal" :induct (ind2 x y))))

;;; scalar multiplication

(defthm vscale-of-vadd
  (implies (and (field-axioms b) (fep b c) (polyp b x) (polyp b y))
           (equal (vscale b c (vadd b x y)) (vadd b (vscale b c x) (vscale b c y))))
  :hints (("Goal" :induct (ind2 x y))))
(defthm vscale-of-fadd
  (implies (and (field-axioms b) (fep b c) (fep b d) (polyp b x))
           (equal (vscale b (fadd b c d) x) (vadd b (vscale b c x) (vscale b d x))))
  :hints (("Goal" :induct (ind1 x))))
(defthm vscale-vscale
  (implies (and (field-axioms b) (fep b c) (fep b d) (polyp b x))
           (equal (vscale b c (vscale b d x)) (vscale b (fmul b c d) x)))
  :hints (("Goal" :induct (ind1 x))))
(defthm vscale-one
  (implies (and (field-axioms b) (polyp b x)) (equal (vscale b (fone b) x) x))
  :hints (("Goal" :induct (ind1 x))))
(defthm vscale-zero
  (implies (and (field-axioms b) (polyp b x)) (equal (vscale b (fzero b) x) (vzero b (len x))))
  :hints (("Goal" :induct (ind1 x))))
(defthm vscale-vzero
  (implies (and (field-axioms b) (fep b c)) (equal (vscale b c (vzero b n)) (vzero b n)))
  :hints (("Goal" :induct (indn n x))))
(defthm vscale-vneg
  (implies (and (field-axioms b) (fep b c) (polyp b x))
           (equal (vscale b c (vneg b x)) (vneg b (vscale b c x))))
  :hints (("Goal" :induct (ind1 x))))
(defthm vscale-fneg
  (implies (and (field-axioms b) (fep b c) (polyp b x))
           (equal (vscale b (fneg b c) x) (vneg b (vscale b c x))))
  :hints (("Goal" :induct (ind1 x))))

;;; butlast1 / last1

(defthm butlast1-singleton (implies (atom x) (equal (butlast1 (cons a x)) nil)))
(defthm last1-singleton (implies (atom x) (equal (last1 (cons a x)) a)))
(defthm butlast1-atom (implies (atom x) (equal (butlast1 x) nil)))

(defthm butlast1-cons (implies (consp x) (equal (butlast1 (cons a x)) (cons a (butlast1 x)))))
(defthm last1-cons (implies (consp x) (equal (last1 (cons a x)) (last1 x))))
(in-theory (disable butlast1 last1))

(defthm butlast1-vadd
  (implies (equal (len x) (len y))
           (equal (butlast1 (vadd b x y)) (vadd b (butlast1 x) (butlast1 y))))
  :hints (("Goal" :induct (ind2 x y) :expand ((butlast1 x) (butlast1 y) (last1 x) (last1 y)))))
(defthm last1-vadd
  (implies (and (equal (len x) (len y)) (consp x))
           (equal (last1 (vadd b x y)) (fadd b (last1 x) (last1 y))))
  :hints (("Goal" :induct (ind2 x y) :expand ((butlast1 x) (butlast1 y) (last1 x) (last1 y)))))
(defthm butlast1-vneg (equal (butlast1 (vneg b x)) (vneg b (butlast1 x)))
  :hints (("Goal" :induct (ind1 x) :expand ((butlast1 x) (last1 x)))))
(defthm last1-vneg (implies (consp x) (equal (last1 (vneg b x)) (fneg b (last1 x))))
  :hints (("Goal" :induct (ind1 x) :expand ((butlast1 x) (last1 x)))))
(defthm butlast1-vscale (equal (butlast1 (vscale b c x)) (vscale b c (butlast1 x)))
  :hints (("Goal" :induct (ind1 x) :expand ((butlast1 x) (last1 x)))))
(defthm last1-vscale (implies (consp x) (equal (last1 (vscale b c x)) (fmul b c (last1 x))))
  :hints (("Goal" :induct (ind1 x) :expand ((butlast1 x) (last1 x)))))
(defthm butlast1-vzero (equal (butlast1 (vzero b n)) (vzero b (- (nfix n) 1)))
  :hints (("Goal" :induct (indn n x)
           :expand ((butlast1 (cons (fzero b) (vzero b (+ -1 n))))))))
(defthm last1-vzero (implies (not (zp n)) (equal (last1 (vzero b n)) (fzero b)))
  :hints (("Goal" :induct (indn n x)
           :expand ((last1 (cons (fzero b) (vzero b (+ -1 n))))))))
;;; ---------------------------------------------------------------------------
;;; Multiplication by X modulo q
;;; ---------------------------------------------------------------------------

(in-theory (disable vadd-consp vneg-consp vscale-consp vzero-opener))

(defthm consp-when-len-pos (implies (< 0 (len x)) (consp x)))
(defthm len-pos-when-consp (implies (consp x) (< 0 (len x))) :rule-classes :linear)

(defun vshift (b v) (cons (fzero b) (butlast1 v)))

(defthm len-vshift (equal (len (vshift b v)) (+ 1 (len (butlast1 v)))))
(defthm polyp-vshift (implies (and (field-axioms b) (polyp b v)) (polyp b (vshift b v))))

(defthm vtimesx-as-shift
  (implies (and (field-axioms b) (polyp b q) (polyp b v) (consp v)
                (equal (len q) (+ 1 (len v))))
           (equal (vtimesx b q v)
                  (vadd b (vshift b v) (vneg b (vscale b (last1 v) (butlast1 q)))))))

(defthm vshift-vadd
  (implies (and (field-axioms b) (polyp b v) (polyp b w) (equal (len v) (len w)))
           (equal (vshift b (vadd b v w)) (vadd b (vshift b v) (vshift b w)))))
(defthm vshift-vscale
  (implies (and (field-axioms b) (fep b c) (polyp b v))
           (equal (vshift b (vscale b c v)) (vscale b c (vshift b v)))))
(defthm vshift-vneg
  (implies (and (field-axioms b) (polyp b v))
           (equal (vshift b (vneg b v)) (vneg b (vshift b v)))))
(defthm vshift-vzero
  (implies (and (field-axioms b) (not (zp n)))
           (equal (vshift b (vzero b n)) (vzero b n)))
  :hints (("Goal" :in-theory (enable vzero-opener))))

(in-theory (disable vshift vtimesx-def))

(defthm len-vtimesx-vec
  (implies (and (consp v) (equal (len q) (+ 1 (len v))))
           (equal (len (vtimesx b q v)) (len v)))
  :hints (("Goal" :in-theory (enable vtimesx-def))))
(defthm consp-vtimesx
  (equal (consp (vtimesx b q v)) (and (consp v) (consp (cdr (vadd b (cons (fzero b) v) (vneg b (vscale b (last1 v) q)))))))
  :hints (("Goal" :in-theory (enable vtimesx-def butlast1))))
(defthm vtimesx-atom (implies (atom v) (equal (vtimesx b q v) nil))
  :hints (("Goal" :in-theory (enable vtimesx-def))))

(defthm vtimesx-vadd
  (implies (and (field-axioms b) (polyp b q) (polyp b v) (polyp b w) (consp v)
                (equal (len q) (+ 1 (len v))) (equal (len w) (len v)))
           (equal (vtimesx b q (vadd b v w))
                  (vadd b (vtimesx b q v) (vtimesx b q w)))))

(defthm vtimesx-vscale
  (implies (and (field-axioms b) (polyp b q) (polyp b v) (fep b c) (consp v)
                (equal (len q) (+ 1 (len v))))
           (equal (vtimesx b q (vscale b c v))
                  (vscale b c (vtimesx b q v)))))

(defthm vtimesx-vneg
  (implies (and (field-axioms b) (polyp b q) (polyp b v) (consp v)
                (equal (len q) (+ 1 (len v))))
           (equal (vtimesx b q (vneg b v))
                  (vneg b (vtimesx b q v)))))

(defthm vtimesx-vzero
  (implies (and (field-axioms b) (polyp b q) (not (zp n)) (equal (len q) (+ 1 n)))
           (equal (vtimesx b q (vzero b n)) (vzero b n))))
;;; ---------------------------------------------------------------------------
;;; a(X) * v  mod p
;;; ---------------------------------------------------------------------------

(in-theory (disable vtimesx-as-shift))

(defthm vapply-vzero-left
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p))
                (polyp b v) (equal (len v) (+ -1 (len p))))
           (equal (vapply b p (vzero b k) v) (vzero b (+ -1 (len p)))))
  :hints (("Goal" :induct (indn k x) :expand ((vzero b k)))))

(defthm vapply-vzero-right
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p)) (polyp b a))
           (equal (vapply b p a (vzero b (+ -1 (len p)))) (vzero b (+ -1 (len p)))))
  :hints (("Goal" :induct (ind1 a))))

(defthm vapply-vadd-right
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p)) (polyp b a)
                (polyp b v) (equal (len v) (+ -1 (len p)))
                (polyp b w) (equal (len w) (+ -1 (len p))))
           (equal (vapply b p a (vadd b v w))
                  (vadd b (vapply b p a v) (vapply b p a w))))
  :hints (("Goal" :induct (ind1 a))))

(defthm vapply-vscale-right
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p)) (polyp b a) (fep b c)
                (polyp b v) (equal (len v) (+ -1 (len p))))
           (equal (vapply b p a (vscale b c v))
                  (vscale b c (vapply b p a v))))
  :hints (("Goal" :induct (ind1 a))))

(defthm vapply-vtimesx-right
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p)) (polyp b a)
                (polyp b v) (equal (len v) (+ -1 (len p))))
           (equal (vapply b p a (vtimesx b p v))
                  (vtimesx b p (vapply b p a v))))
  :hints (("Goal" :induct (ind1 a))))

(defthm vapply-vadd-left
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p)) (polyp b x) (polyp b y)
                (polyp b v) (equal (len v) (+ -1 (len p))))
           (equal (vapply b p (vadd b x y) v)
                  (vadd b (vapply b p x v) (vapply b p y v))))
  :hints (("Goal" :induct (ind2 x y) :expand ((vadd b x y)))))

(defthm vapply-vscale-left
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p)) (polyp b a) (fep b c)
                (polyp b v) (equal (len v) (+ -1 (len p))))
           (equal (vapply b p (vscale b c a) v)
                  (vscale b c (vapply b p a v))))
  :hints (("Goal" :induct (ind1 a) :expand ((vscale b c a)))))

(defthm vapply-vneg-left
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p)) (polyp b a)
                (polyp b v) (equal (len v) (+ -1 (len p))))
           (equal (vapply b p (vneg b a) v)
                  (vneg b (vapply b p a v))))
  :hints (("Goal" :induct (ind1 a) :expand ((vneg b a)))))

(defthm vapply-cons-zero
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p)) (polyp b a)
                (polyp b v) (equal (len v) (+ -1 (len p))))
           (equal (vapply b p (cons (fzero b) a) v)
                  (vtimesx b p (vapply b p a v)))))

(defthm vapply-butlast1
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p)) (polyp b a)
                (consp a) (equal (last1 a) (fzero b))
                (polyp b v) (equal (len v) (+ -1 (len p))))
           (equal (vapply b p (butlast1 a) v)
                  (vapply b p a v)))
  :hints (("Goal" :induct (ind1 a) :in-theory (enable butlast1 last1))))
;;; ---------------------------------------------------------------------------
;;; Commutativity, associativity, identity; reduction modulo q
;;; ---------------------------------------------------------------------------

(defthm len-append-local (equal (len (append x y)) (+ (len x) (len y))))

;; L: multiplication by X modulo q, seen through vapply over modulus p
(defthm vapply-l-step1
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p))
                (polyp b q) (polyp b v) (fep b c)
                (polyp b w) (equal (len w) (+ -1 (len p))))
           (equal (vapply b p (vadd b (cons (fzero b) v) (vneg b (vscale b c q))) w)
                  (vadd b (vtimesx b p (vapply b p v w))
                        (vneg b (vscale b c (vapply b p q w)))))))

(defthm vapply-l-step2
  (implies (and (field-axioms b)
                (polyp b q) (polyp b v) (consp v)
                (equal (len q) (+ 1 (len v)))
                (equal (last1 q) (fone b)))
           (equal (last1 (vadd b (cons (fzero b) v) (vneg b (vscale b (last1 v) q))))
                  (fzero b))))

(defthmd vapply-vtimesx-left
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p))
                (polyp b q) (polyp b v) (consp v)
                (equal (len q) (+ 1 (len v)))
                (equal (last1 q) (fone b))
                (polyp b w) (equal (len w) (+ -1 (len p))))
           (equal (vapply b p (vtimesx b q v) w)
                  (vadd b (vtimesx b p (vapply b p v w))
                        (vneg b (vscale b (last1 v) (vapply b p q w))))))
  :hints (("Goal" :expand ((vtimesx b q v))
           :in-theory (disable butlast1-vadd vapply-butlast1 vapply-l-step1 vapply-l-step2
                               vapply-consp vapply-cons)
           :use (vapply-l-step2
                 (:instance vapply-l-step1 (c (last1 v)))
                 (:instance vapply-butlast1 (v w)
                            (a (vadd b (cons (fzero b) v)
                                     (vneg b (vscale b (last1 v) q)))))))))

;; C: polynomials in X commute as operators
(defthm vapply-vzero-right-gen
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p)) (polyp b a)
                (equal n (+ -1 (len p))))
           (equal (vapply b p a (vzero b n)) (vzero b n))))

(defthmd vapply-commute
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p))
                (polyp b u) (polyp b v)
                (polyp b w) (equal (len w) (+ -1 (len p))))
           (equal (vapply b p u (vapply b p v w))
                  (vapply b p v (vapply b p u w))))
  :hints (("Goal" :induct (ind1 u))))

;; E: a(X) * 1 = a for short a
(defthm last1-append (implies (consp z) (equal (last1 (append a z)) (last1 z)))
  :hints (("Goal" :in-theory (enable last1))))
(defthm butlast1-append (implies (consp z) (equal (butlast1 (append a z)) (append a (butlast1 z))))
  :hints (("Goal" :in-theory (enable butlast1))))

(defthm vtimesx-last-zero
  (implies (and (field-axioms b) (polyp b q) (polyp b v) (consp v)
                (equal (len q) (+ 1 (len v)))
                (equal (last1 v) (fzero b)))
           (equal (vtimesx b q v) (vshift b v)))
  :hints (("Goal" :in-theory (enable vtimesx-as-shift))))

(defthm vapply-vone-right-0
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p))
                (polyp b a) (<= (len a) (+ -1 (len p))))
           (equal (vapply b p a (vone b (+ -1 (len p))))
                  (pad b a (+ -1 (len p)))))
  :hints (("Goal" :induct (ind1 a) :in-theory (enable vshift vone))))

(in-theory (disable vone))

(defthm vapply-vone-right
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p))
                (equal n (+ -1 (len p)))
                (polyp b a) (<= (len a) n))
           (equal (vapply b p a (vone b n))
                  (pad b a n))))

(defthm vapply-vone-right-vec
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p))
                (equal n (+ -1 (len p)))
                (polyp b a) (equal (len a) n))
           (equal (vapply b p a (vone b n)) a))
  :hints (("Goal" :use vapply-vone-right-0 :in-theory (disable vapply-vone-right-0))))

;; F: commutativity on residues
(defthmd vapply-comm-vec
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p))
                (polyp b u) (equal (len u) (+ -1 (len p)))
                (polyp b v) (equal (len v) (+ -1 (len p))))
           (equal (vapply b p u v) (vapply b p v u)))
  :hints (("Goal" :use ((:instance vapply-commute (u u) (v v) (w (vone b (+ -1 (len p))))))
           :in-theory (disable vapply-vone-right vapply-consp vapply-cons))))

;; G: associativity
(defthmd vapply-assoc
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p))
                (polyp b u)
                (polyp b v) (equal (len v) (+ -1 (len p)))
                (polyp b w) (equal (len w) (+ -1 (len p))))
           (equal (vapply b p (vapply b p u v) w)
                  (vapply b p u (vapply b p v w))))
  :hints (("Goal" :use ((:instance vapply-comm-vec (u (vapply b p u v)) (v w))
                        (:instance vapply-commute (u u) (v w) (w v))
                        (:instance vapply-comm-vec (u v) (v w)))
           :in-theory (disable vapply-consp vapply-cons))))

;; H: 1 * v = v
(defthm vapply-vone-left
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p)) (not (zp k))
                (polyp b v) (equal (len v) (+ -1 (len p))))
           (equal (vapply b p (vone b k) v) v))
  :hints (("Goal" :in-theory (enable vone))))
;;; ---------------------------------------------------------------------------
;;; p(X) = 0 in the quotient; the division identity
;;; ---------------------------------------------------------------------------

(defthm b-add-self
  (implies (and (field-axioms b) (fep b x) (fep b y))
           (equal (equal (fadd b x y) x) (equal y (fzero b))))
  :hints (("Goal" :use ((:instance b-add-cancel (x x) (y y) (z (fzero b)))))))

(defthm vadd-self-cancel
  (implies (and (field-axioms b) (polyp b x) (polyp b y) (equal (len y) (len x)))
           (equal (equal (vadd b x y) x) (equal y (vzero b (len x)))))
  :hints (("Goal" :induct (ind2 x y) :in-theory (enable vadd-consp vzero-opener))))

(defthm vadd-self-cancel-2
  (implies (and (field-axioms b) (polyp b x) (polyp b y) (equal (len y) (len x)))
           (equal (equal (vadd b y x) x) (equal y (vzero b (len x)))))
  :hints (("Goal" :use vadd-self-cancel :in-theory (disable vadd-self-cancel))))

(defthm vneg-equal-vzero
  (implies (and (field-axioms b) (polyp b x))
           (equal (equal (vneg b x) (vzero b n))
                  (equal x (vzero b n))))
  :hints (("Goal" :use ((:instance vneg-vneg (x x)))
           :in-theory (disable vneg-vneg))))

(defun vlastone (b n)
  (append (vzero b (- n 1)) (list (fone b))))

(defthm vlastone-props
  (implies (and (field-axioms b) (posp n))
           (and (polyp b (vlastone b n))
                (equal (len (vlastone b n)) n)
                (consp (vlastone b n))
                (equal (last1 (vlastone b n)) (fone b))))
  :hints (("Goal" :in-theory (enable last1))))

(in-theory (disable vlastone))

(defthm vapply-modulus-step
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p))
                (equal (last1 p) (fone b))
                (polyp b e) (equal (len e) (+ -1 (len p))) (equal (last1 e) (fone b))
                (polyp b w) (equal (len w) (+ -1 (len p))))
           (equal (vtimesx b p (vapply b p e w))
                  (vadd b (vtimesx b p (vapply b p e w))
                        (vneg b (vapply b p p w)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance vapply-vtimesx-left (q p) (v e) (w w))
                        (:instance vapply-comm-vec (u (vtimesx b p e)) (v w))
                        (:instance vapply-comm-vec (u w) (v e)))
           :in-theory (disable vapply-consp vapply-cons))))

(defthm vapply-modulus
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p))
                (equal (last1 p) (fone b))
                (polyp b w) (equal (len w) (+ -1 (len p))))
           (equal (vapply b p p w) (vzero b (+ -1 (len p)))))
  :hints (("Goal" :use ((:instance vapply-modulus-step (e (vlastone b (+ -1 (len p)))))
                        (:instance vneg-vneg (x (vapply b p p w))))
           :in-theory (disable vapply-consp vapply-cons vneg-vneg))))

;;; reduction modulo q

(defthm pmod-cons
  (equal (pmod b (cons a x) q)
         (vadd b (vscale b a (vone b (- (len q) 1))) (vtimesx b q (pmod b x q))))
  :hints (("Goal" :in-theory (enable pmod))))
(defthmd pmod-consp
  (implies (consp a)
           (equal (pmod b a q)
                  (vadd b (vscale b (car a) (vone b (- (len q) 1)))
                        (vtimesx b q (pmod b (cdr a) q)))))
  :hints (("Goal" :in-theory (enable pmod))))
(defthm pmod-atom
  (implies (atom a) (equal (pmod b a q) (vzero b (- (len q) 1))))
  :hints (("Goal" :in-theory (enable pmod))))
(defthm polyp-pquot
  (implies (and (field-axioms b) (polyp b q) (<= 2 (len q)) (polyp b a))
           (polyp b (pquot b a q))))

(defthm vadd-vneg-cancel-right
  (implies (and (field-axioms b) (polyp b x) (polyp b y) (equal (len x) (len y)))
           (equal (vadd b (vadd b x (vneg b y)) y) x))
  :hints (("Goal" :in-theory (disable vadd-comm vadd-comm2))))

(defthmd vapply-vtimesx-left+
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p))
                (polyp b q) (polyp b v) (consp v)
                (equal (len q) (+ 1 (len v)))
                (equal (last1 q) (fone b))
                (polyp b w) (equal (len w) (+ -1 (len p))))
           (equal (vadd b (vapply b p (vtimesx b q v) w)
                        (vscale b (last1 v) (vapply b p q w)))
                  (vtimesx b p (vapply b p v w))))
  :hints (("Goal" :use ((:instance vapply-vtimesx-left)
                        (:instance vadd-vneg-cancel-right
                                   (x (vtimesx b p (vapply b p v w)))
                                   (y (vscale b (last1 v) (vapply b p q w)))))
           :in-theory (disable vapply-consp vapply-cons vadd-assoc vadd-comm vadd-comm2
                               vadd-vneg-cancel-right))))

(defthm vtimesx-vapply-pmod
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p))
                (polyp b q) (<= 2 (len q)) (equal (last1 q) (fone b))
                (polyp b x) (polyp b w) (equal (len w) (+ -1 (len p))))
           (equal (vtimesx b p (vapply b p (pmod b x q) w))
                  (vadd b (vapply b p (vtimesx b q (pmod b x q)) w)
                        (vscale b (last1 (pmod b x q)) (vapply b p q w)))))
  :hints (("Goal" :use ((:instance vapply-vtimesx-left+ (v (pmod b x q))))
           :in-theory (disable vapply-vtimesx-left+ vapply-consp vapply-cons))))

(defthm pmod-division-step
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p))
                (polyp b q) (<= 2 (len q)) (equal (last1 q) (fone b))
                (fep b c) (polyp b x) (polyp b qq)
                (polyp b w) (equal (len w) (+ -1 (len p)))
                (equal aa (vadd b (vapply b p (pmod b x q) w)
                                (vapply b p qq (vapply b p q w)))))
           (equal (vadd b (vscale b c w) (vtimesx b p aa))
                  (vadd b (vscale b c w)
                        (vadd b (vapply b p (vtimesx b q (pmod b x q)) w)
                              (vadd b (vscale b (last1 (pmod b x q)) (vapply b p q w))
                                    (vtimesx b p (vapply b p qq (vapply b p q w))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable vapply-consp vapply-cons))))

(defthmd pmod-division
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p))
                (polyp b q) (<= 2 (len q)) (equal (last1 q) (fone b))
                (polyp b a) (polyp b w) (equal (len w) (+ -1 (len p))))
           (equal (vapply b p a w)
                  (vadd b (vapply b p (pquot b a q) (vapply b p q w))
                        (vapply b p (pmod b a q) w))))
  :hints (("Goal" :induct (ind1 a)
           :in-theory (e/d (pmod-consp) (vapply-consp vapply-cons))
           :expand ((vapply b p a w) (pquot b a q)
                    (:free (x y v) (vapply b p (cons x y) v))))
          ("Subgoal *1/2" :use ((:instance pmod-division-step (c (car a)) (x (cdr a))
                                           (qq (pquot b (cdr a) q))
                                           (aa (vapply b p (cdr a) w)))))))
;;; ---------------------------------------------------------------------------
;;; Correctness of the inverse search
;;; ---------------------------------------------------------------------------

(in-theory (disable finv inv-search vapply-consp vapply-cons))

(defthm pad-trim
  (implies (polyp b x)
           (equal (pad b (trim b x) (len x)) x))
  :hints (("Goal" :induct (ind1 x) :in-theory (enable trim vzero-opener))))

(defthm last1-trim-nonzero
  (implies (consp (trim b x))
           (not (equal (last1 (trim b x)) (fzero b))))
  :hints (("Goal" :induct (ind1 x) :in-theory (enable trim last1))))

(defthm vzerop-means-vzero
  (implies (and (polyp b x) (vzerop b x))
           (equal x (vzero b (len x))))
  :rule-classes nil
  :hints (("Goal" :induct (ind1 x) :in-theory (enable vzero-opener))))

(defthm vzerop-vzero (vzerop b (vzero b n))
  :hints (("Goal" :induct (indn n x) :in-theory (enable vzero-opener))))

(defthm vscale-vone
  (implies (and (field-axioms b) (fep b c) (not (zp n)))
           (equal (vscale b c (vone b n)) (cons c (vzero b (- n 1)))))
  :hints (("Goal" :in-theory (enable vone))))

(defthm vscale-append
  (equal (vscale b c (append x y)) (append (vscale b c x) (vscale b c y)))
  :hints (("Goal" :induct (ind1 x))))

(defthm pad-vscale
  (implies (and (field-axioms b) (fep b c))
           (equal (pad b (vscale b c x) n) (vscale b c (pad b x n)))))

(defthm vneg-unique
  (implies (and (field-axioms b) (polyp b x) (polyp b y) (equal (len x) (len y))
                (equal (vadd b x y) (vzero b (len x))))
           (equal (vneg b x) y))
  :rule-classes nil
  :hints (("Goal" :induct (ind2 x y)
           :in-theory (enable vadd-consp vneg-consp vzero-opener))
          ("Subgoal *1/2" :use ((:instance b-neg-unique (x (car x)) (y (car y)))))))

(defthm len-trim-pos
  (implies (consp (trim b x)) (<= 1 (len x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :expand ((trim b x)))))

(defthm len-pad (equal (len (pad b x n)) (max (len x) (nfix n))))

;; the key step: the new remainder is a multiple of g
(defthm inv-step-key0
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p)) (equal (last1 p) (fone b))
                (polyp b tg) (consp (cdr tg)) (<= (len tg) (+ -1 (len p)))
                (fep b ci) (equal (fmul b ci (last1 tg)) (fone b)))
           (equal (pad b (pmod b p (vscale b ci tg)) (+ -1 (len p)))
                  (vapply b p (vscale b (fneg b ci) (pquot b p (vscale b ci tg)))
                          (pad b tg (+ -1 (len p))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance pmod-division (a p) (q (vscale b ci tg))
                            (w (vone b (+ -1 (len p)))))
                 (:instance vneg-unique
                            (x (vscale b ci (vapply b p (pquot b p (vscale b ci tg))
                                                    (pad b tg (+ -1 (len p))))))
                            (y (pad b (pmod b p (vscale b ci tg)) (+ -1 (len p))))))
           :in-theory (disable pad)
           :expand ((len tg) (len (cdr tg))))))

(defthm fep-finv-last1-trim
  (implies (and (field-axioms b) (polyp b g) (consp (trim b g)))
           (fep b (finv b (last1 (trim b g))))))

(defthm inv-step-key
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p)) (equal (last1 p) (fone b))
                (polyp b g) (equal (len g) (+ -1 (len p)))
                (consp (cdr (trim b g))))
           (let* ((tg (trim b g))
                  (ci (finv b (last1 tg)))
                  (g1 (vscale b ci tg)))
             (equal (pad b (pmod b p g1) (+ -1 (len p)))
                    (vapply b p (vscale b (fneg b ci) (pquot b p g1)) g))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance inv-step-key0 (tg (trim b g))
                                   (ci (finv b (last1 (trim b g)))))
                        (:instance pad-trim (x g))
                        (:instance len-trim (x g)))
           :in-theory (disable pad pad-trim len-trim))))
(defun inv-ind (b p g s)
  (declare (xargs :measure (len (trim b g))
                  :hints (("Goal" :use ((:instance atom-trim-is-vzerop (x g)))))))
  (let ((tg (trim b g)))
    (if (atom tg)
        s
      (let ((c (last1 tg)))
        (if (atom (cdr tg))
            s
          (let* ((g1 (vscale b (finv b c) tg))
                 (r (pmod b p g1)))
            (if (vzerop b r)
                s
              (inv-ind b p (pad b r (- (len p) 1))
                       (vapply b p (vscale b (fneg b (finv b c)) (pquot b p g1))
                               s)))))))))

(defthm inv-search-opener
  (equal (inv-search b p g s)
         (let ((tg (trim b g)))
           (if (atom tg)
               s
             (let ((c (last1 tg)))
               (if (atom (cdr tg))
                   (vscale b (finv b c) s)
                 (let* ((g1 (vscale b (finv b c) tg))
                        (r (pmod b p g1)))
                   (if (vzerop b r)
                       s
                     (inv-search b p (pad b r (- (len p) 1))
                                 (vapply b p (vscale b (fneg b (finv b c)) (pquot b p g1))
                                         s)))))))))
  :rule-classes nil
  :hints (("Goal" :expand ((inv-search b p g s)))))

;; irreducibility rules out the degenerate branch
(defthm irreducible-pmod-nonzero
  (implies (and (field-axioms b) (polyp b p) (irreducible b p)
                (polyp b g) (equal (len g) (+ -1 (len p)))
                (consp (cdr (trim b g))))
           (not (vzerop b (pmod b p (vscale b (finv b (last1 (trim b g))) (trim b g))))))
  :hints (("Goal" :use ((:instance reducible-suff
                                   (q (vscale b (finv b (last1 (trim b g))) (trim b g))))
                        (:instance len-trim (x g)))
           :in-theory (disable len-trim)
           :expand ((len (trim b g)) (len (cdr (trim b g)))))))

(in-theory (disable irreducible reducible))

;; the constant case
(defthm inv-base-case
  (implies (and (field-axioms b) (polyp b g) (consp (trim b g)) (not (consp (cdr (trim b g)))))
           (equal g (vscale b (last1 (trim b g)) (vone b (len g)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance pad-trim (x g)))
           :in-theory (e/d (last1 vone) (pad-trim)))))

(defun inv-inv (b p s u g) (equal (vapply b p s u) g))
(in-theory (disable inv-inv))

(defthm inv-case-const
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p))
                (polyp b u) (equal (len u) (+ -1 (len p)))
                (polyp b s) (equal (len s) (+ -1 (len p)))
                (polyp b g) (equal (len g) (+ -1 (len p)))
                (inv-inv b p s u g)
                (consp (trim b g)) (not (consp (cdr (trim b g)))))
           (equal (vapply b p (vscale b (finv b (last1 (trim b g))) s) u)
                  (vone b (+ -1 (len p)))))
  :hints (("Goal" :use (inv-base-case) :in-theory (enable vone inv-inv) :do-not-induct t)))

(defthm vzerop-pad
  (equal (vzerop b (pad b x n)) (vzerop b x))
  :hints (("Goal" :use ((:instance atom-trim-is-vzerop (x (pad b x n)))
                        (:instance atom-trim-is-vzerop (x x))))))

(defthm inv-step-props
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p)) (equal (last1 p) (fone b))
                (irreducible b p)
                (polyp b u) (equal (len u) (+ -1 (len p)))
                (polyp b s) (equal (len s) (+ -1 (len p)))
                (polyp b g) (equal (len g) (+ -1 (len p)))
                (inv-inv b p s u g)
                (consp (cdr (trim b g))))
           (let* ((tg (trim b g))
                  (ci (finv b (last1 tg)))
                  (g1 (vscale b ci tg))
                  (g2 (pad b (pmod b p g1) (- (len p) 1)))
                  (s2 (vapply b p (vscale b (fneg b ci) (pquot b p g1)) s)))
             (and (polyp b g2)
                  (equal (len g2) (+ -1 (len p)))
                  (polyp b s2)
                  (equal (len s2) (+ -1 (len p)))
                  (inv-inv b p s2 u g2)
                  (not (vzerop b g2)))))
  :hints (("Goal" :use (inv-step-key
                        irreducible-pmod-nonzero
                        (:instance len-trim (x g))
                        (:instance len-pmod (a p) (q (vscale b (finv b (last1 (trim b g))) (trim b g))))
                        (:instance vapply-assoc
                                   (u (vscale b (fneg b (finv b (last1 (trim b g))))
                                              (pquot b p (vscale b (finv b (last1 (trim b g))) (trim b g)))))
                                   (v s) (w u))
                        (:instance atom-trim-is-vzerop
                                   (x (pad b (pmod b p (vscale b (finv b (last1 (trim b g))) (trim b g)))
                                           (- (len p) 1))))
                        (:instance atom-trim-is-vzerop
                                   (x (pmod b p (vscale b (finv b (last1 (trim b g))) (trim b g))))))
           :in-theory (e/d (inv-inv) (len-trim len-pmod pad irreducible-pmod-nonzero))
           :expand ((len (trim b g)) (len (cdr (trim b g)))))))

(in-theory (disable inv-inv))

(defthm inv-search-correct-0
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p)) (equal (last1 p) (fone b))
                (irreducible b p)
                (polyp b u) (equal (len u) (+ -1 (len p)))
                (polyp b s) (equal (len s) (+ -1 (len p)))
                (polyp b g) (equal (len g) (+ -1 (len p)))
                (inv-inv b p s u g)
                (not (vzerop b g)))
           (and (polyp b (inv-search b p g s))
                (equal (len (inv-search b p g s)) (+ -1 (len p)))
                (equal (vapply b p (inv-search b p g s) u) (vone b (+ -1 (len p))))))
  :hints (("Goal" :induct (inv-ind b p g s) :in-theory (disable pad))
          ("Subgoal *1/4" :use (inv-search-opener inv-step-props))
          ("Subgoal *1/3" :use (inv-search-opener irreducible-pmod-nonzero))
          ("Subgoal *1/2" :use (inv-search-opener inv-case-const))
          ("Subgoal *1/1" :use (inv-search-opener
                                (:instance atom-trim-is-vzerop (x g))))))
;;; ---------------------------------------------------------------------------
;;; Simple extensions satisfy the field axioms
;;; ---------------------------------------------------------------------------

(defthm ext-fep (equal (fep (list :ext b p) x) (vecp b (- (len p) 1) x))
  :hints (("Goal" :in-theory (enable fep))))
(defthm ext-fadd (equal (fadd (list :ext b p) x y) (vadd b x y))
  :hints (("Goal" :in-theory (enable fadd))))
(defthm ext-fmul (equal (fmul (list :ext b p) x y) (vapply b p x y))
  :hints (("Goal" :in-theory (enable fmul))))
(defthm ext-fneg (equal (fneg (list :ext b p) x) (vneg b x))
  :hints (("Goal" :in-theory (enable fneg))))
(defthm ext-fzero (equal (fzero (list :ext b p)) (vzero b (- (len p) 1)))
  :hints (("Goal" :in-theory (enable fzero))))
(defthm ext-fone (implies (<= 2 (len p))
                          (equal (fone (list :ext b p)) (vone b (- (len p) 1))))
  :hints (("Goal" :in-theory (enable fone vone))))
(defthm ext-finv (equal (finv (list :ext b p) x)
                        (inv-search b p x (vone b (- (len p) 1))))
  :hints (("Goal" :in-theory (enable finv))))

(defthm vzero-not-vone
  (implies (and (field-axioms b) (not (zp n)))
           (not (equal (vzero b n) (vone b n))))
  :hints (("Goal" :in-theory (enable vone vzero-opener))))

(defthm polyp-len-vone
  (implies (field-axioms b)
           (and (polyp b (vone b n)) (equal (len (vone b n)) (nfix n)))))

(defthm ext-inverse
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p)) (equal (last1 p) (fone b))
                (irreducible b p)
                (polyp b x) (equal (len x) (+ -1 (len p)))
                (not (equal x (vzero b (+ -1 (len p))))))
           (let ((y (inv-search b p x (vone b (+ -1 (len p))))))
             (and (polyp b y)
                  (equal (len y) (+ -1 (len p)))
                  (equal (vapply b p x y) (vone b (+ -1 (len p)))))))
  :hints (("Goal" :use ((:instance inv-search-correct-0 (g x) (u x) (s (vone b (+ -1 (len p)))))
                        (:instance vzerop-means-vzero)
                        (:instance vapply-comm-vec (u x) (v (inv-search b p x (vone b (+ -1 (len p)))))))
           :in-theory (e/d (inv-inv) (inv-search-correct-0)))))

(defthm axioms-body-ext
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p)) (equal (last1 p) (fone b))
                (irreducible b p))
           (axioms-body (list :ext b p) x y z))
  :hints (("Goal" :in-theory (e/d (axioms-body) (ext-inverse))
           :use ((:instance ext-inverse)
                 (:instance vapply-comm-vec (u x) (v y))
                 (:instance vapply-assoc (u x) (v y) (w z))))))

(defthm field-axioms-ext
  (implies (and (field-axioms b) (polyp b p) (<= 2 (len p)) (equal (last1 p) (fone b))
                (irreducible b p))
           (field-axioms (list :ext b p)))
  :hints (("Goal" :in-theory (enable field-axioms))))

;;; ---------------------------------------------------------------------------
;;; Fields: base fields and simple extensions
;;; ---------------------------------------------------------------------------

(defun fieldp (f)
  (cond ((equal f '(:q)) t)
        ((equal f '(:f0)) t)
        ((and (consp f) (eq (car f) :fp))
         (and (equal f (list :fp (cadr f)))
              (dm::primep (cadr f))))
        ((and (consp f) (eq (car f) :ext))
         (let ((b (cadr f)) (p (caddr f)))
           (and (equal f (list :ext b p))
                (fieldp b)
                (monicp b p)
                (<= 2 (deg p))
                (irreducible b p))))
        (t nil)))

(defthm fieldp-field-axioms
  (implies (fieldp f) (field-axioms f))
  :hints (("Goal" :induct (fieldp f))))

;;; ---------------------------------------------------------------------------
;;; Main theorem: every field satisfies the field axioms
;;; ---------------------------------------------------------------------------

(defthm main
  (implies (fieldp f)
           (and (fep f (fzero f))
                (fep f (fone f))
                (not (equal (fzero f) (fone f)))
                (implies (and (fep f x) (fep f y))
                         (and (fep f (fadd f x y))
                              (fep f (fmul f x y))
                              (equal (fadd f x y) (fadd f y x))
                              (equal (fmul f x y) (fmul f y x))))
                (implies (fep f x)
                         (and (fep f (fneg f x))
                              (equal (fadd f x (fzero f)) x)
                              (equal (fmul f x (fone f)) x)
                              (equal (fadd f x (fneg f x)) (fzero f))))
                (implies (and (fep f x) (not (equal x (fzero f))))
                         (and (fep f (finv f x))
                              (equal (fmul f x (finv f x)) (fone f))))
                (implies (and (fep f x) (fep f y) (fep f z))
                         (and (equal (fadd f (fadd f x y) z) (fadd f x (fadd f y z)))
                              (equal (fmul f (fmul f x y) z) (fmul f x (fmul f y z)))
                              (equal (fmul f x (fadd f y z))
                                     (fadd f (fmul f x y) (fmul f x z)))))))
  :rule-classes nil
  :hints (("Goal" :use (fieldp-field-axioms
                        (:instance field-axioms-necc (f f) (x x) (y y) (z z)))
           :in-theory (union-theories '(axioms-body) (theory 'minimal-theory)))))
