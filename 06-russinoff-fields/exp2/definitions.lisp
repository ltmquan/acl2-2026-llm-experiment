;; Definitions for the "russinoff-fields" targets, extracted VERBATIM from
;; ACL2 master books/projects/fields/{extensions,vectors,polynomials,embeddings}.lisp
;; (David M. Russinoff).  All theorems have been removed; the only lemmas kept are
;; LOCAL ones needed to admit peval and factorization.  See README.md for deviations.
;; The DM package is defined by cert.acl2 (projects/numbers/portcullis).

(in-package "DM")
;;; ===== from projects/fields/extensions.lisp =====
;;; projects/fields/extensions.lisp, lines 6-6
(include-book "projects/groups/groups" :dir :system)
;;; projects/fields/extensions.lisp, lines 7-7
(include-book "projects/linear/field" :dir :system)

;; ---- verbatim: extensions.lisp:34-79 ----
;;; projects/fields/extensions.lisp, lines 34-37
(defund fbasep (f)
  (or (zerop f)       ;the rational field is encoded as 0
      (primep f)      ;the prime field of order p is encoded as p
      (equal f 'f0))) ;the generic field is encoded as the symbol f0

;; Recognizer of base field elements:

;;; projects/fields/extensions.lisp, lines 41-44
(defund beltp (x f)
  (cond ((zerop f) (rationalp x))
        ((primep f) (member x (ninit f)))
	(t (fp x))))

;; Base field operations:

;;; projects/fields/extensions.lisp, lines 48-51
(defund badd (x y f)
  (cond ((zerop f) (+ x y))
        ((primep f) (mod (+ x y) f))
	(t (f+ x y))))

;;; projects/fields/extensions.lisp, lines 53-56
(defund bmul (x y f)
  (cond ((zerop f) (* x y))
        ((primep f) (mod (* x y) f))
	(t (f* x y))))

;; Additive and multiplicative identities:

;;; projects/fields/extensions.lisp, lines 60-61
(defund bzero (f)
  (if (integerp f) 0 (f0)))

;;; projects/fields/extensions.lisp, lines 63-64
(defund bone (f)
  (if (integerp f) 1 (f1)))

;; Additive and multiplicative inverses:

;;; projects/fields/extensions.lisp, lines 68-71
(defund bneg (x f)
  (cond ((zerop f) (- x))
        ((primep f) (mod (- x) f))
	(t (f- x))))

;;; projects/fields/extensions.lisp, lines 73-77
(defund brecip (x f)
  (cond ((zerop f) (/ x))
	;the following is inspired by Fermat's Theorem (see "../numbers/fermat"):
        ((primep f) (mod (expt x (- f 2)) f))
	(t (f/ x))))

;;; projects/fields/extensions.lisp, lines 79-79
(in-theory (disable (fbasep) (beltp) (badd) (bmul) (bzero) (bone) (bneg) (brecip)))

;; ---- verbatim: extensions.lisp:178-229 ----
;;; projects/fields/extensions.lisp, lines 178-181
(defund fzero (f)
  (if (consp f)
      (list (fzero (cdr f)))
    (bzero f)))

;;; projects/fields/extensions.lisp, lines 183-186
(defund fone (f)
  (if (consp f)
      (list (fone (cdr f)))
    (bone f)))

;; Additive and multiplicative identities of the polynomial ring over f:

;;; projects/fields/extensions.lisp, lines 190-191
(defund pzero (f)
  (list (fzero f)))

;;; projects/fields/extensions.lisp, lines 193-194
(defund pone (f)
  (list (fone f)))

;; Monic polynomial:

;;; projects/fields/extensions.lisp, lines 198-199
(defund monicp (p f)
  (equal (car p) (fone f)))

;; Constant polynomial:

;;; projects/fields/extensions.lisp, lines 203-204
(defun pconstp (p)
  (not (consp (cdr p))))

;; Degree of a polynomial:

;;; projects/fields/extensions.lisp, lines 208-209
(defun degree (p)
  (1- (len p)))

;; The following function strips leading zeroes of a list of field elements, i.e., converts it to a
;; polynomial, except that it does not alter the zero polynomial (pzero f):
    
;;; projects/fields/extensions.lisp, lines 214-217
(defun pstrip (l f)
  (if (and (consp l) (consp (cdr l)) (equal (car l) (fzero f)))
      (pstrip (cdr l) f)
    l))

;; Append k zeroes to a list of field elements, i.e., multiply a polynomial by X^k:

;;; projects/fields/extensions.lisp, lines 221-224
(defun pshift (p k f)
  (if (zp k)
      p
    (pshift (append p (list (fzero f))) (1- k) f)))

;; The monomial c * X^k:

;;; projects/fields/extensions.lisp, lines 228-229
(defun monomial (c k f)
  (pshift (list c) k f))

;; ---- verbatim: extensions.lisp:259-486 ----
;;; projects/fields/extensions.lisp, lines 259-486
(encapsulate ()

(local (include-book "ordinals/lexicographic-book" :dir :system))

(set-well-founded-relation acl2::l<)

(mutual-recursion

  ;; Recognizer of an element of f, which is a polynomial over (cdr f):
  
  (defund feltp (x f)
    (declare (xargs :measure (list (len f) 0 0)))
    (if (consp f)
        (and (polyp x (cdr f))
             (< (degree x) (degree (car f))))
      (beltp x f)))

  ;; A generalized polynomial is a proper list of field elements:

  (defun feltsp (l f)
    (declare (xargs :measure (list (len f) 1 (len l))))
    (if (consp l)
        (and (feltp (car l) f)
             (feltsp (cdr l) f))
      (null l)))

  ;; A polynomial is a non-nil generalized polynomial with either degree 0 or a non-zero leading coefficient:

  (defund polyp (p f)
    (declare (xargs :measure (list (len f) 2 0)))
    (and (feltsp p f)
         (consp p)
         (or (null (cdr p))
             (not (equal (car p) (fzero f))))))

  ;; Addition of field elements:

  (defund fadd (x y f)
    (declare (xargs :measure (list (len f) 2 0)))
    (if (consp f)
        (padd x y (cdr f))
      (badd x y f)))

  ;; Additive inverse of a field element:

  (defund fneg (x f)
    (declare (xargs :measure (list (len f) 2 0)))
    (if (consp f)
        (pneg x (cdr f))
      (bneg x f)))

  ;; Additive inverse of a polynomial::

  (defun pneg (x f)
    (declare (xargs :measure (list (len f) 3 (len x))))
    (if (consp x)
        (cons (fneg (car x) f)
              (pneg (cdr x) f))
      ()))

  ;; Addition of generalized polynomials:

  (defun faddl (x y f)
    (declare (xargs :measure (list (len f) 3 (+ (len x) (len y)))))
    (if (> (len x) (len y))
        (cons (car x) (faddl (cdr x) y f))
      (if (> (len y) (len x))
          (cons (car y) (faddl x (cdr y) f))
	(if (consp x)
            (cons (fadd (car x) (car y) f)
                  (faddl (cdr x) (cdr y) f))
          ()))))

   ;; Addition of polynomials:

  (defund padd (p q f)
    (declare (xargs :measure (list (len f) 4 0)))
    (pstrip (faddl p q f) f))

  ;; Multiplication of field elements:

  (defun fmul (x y f)
    (declare (xargs :measure (list (len f) 4 0)))
    (if (consp f)
        (prem (pmul x y (cdr f)) (car f) (cdr f))
      (bmul x y f)))

  ;; Multiplication of a polynomial by a field element:

  (defun cmul (x p f)
    (declare (xargs :measure (list (len f) 5 (len p))))
    (if (equal x (fzero f))
        (list (fzero f))
      (if (consp p)
          (cons (fmul x (car p) f)
	        (cmul x (cdr p) f))
        ())))

  ;; Multiplication of polynomials:

  (defun pmul (p q f)
    (declare (xargs :measure (list (len f) 6 (len p))))
    (if (or (equal p (pzero f)) (equal q (pzero f)))
        (pzero f)
      (if (consp p)
          (if (consp (cdr p))
              (padd (pshift (cmul (car p) q f) (degree p) f)
                    (pmul (pstrip (cdr p) f) q f)
	            f)
	    (cmul (car p) q f))
        ())))

  ;; Reciprocal:

  (defund frecip (x f)
    (declare (xargs :measure (list (len f) 6 0)))
    (if (consp f)
        (prem (r$ x (car f) (cdr f)) (car f) (cdr f))
      (brecip x f)))

  ;; Greatest common divisor:

  (defun pgcd-aux (p q f)
    (declare (xargs :measure (list (len f) 7 (+ (len p) (len q)))))
    (if (equal p (pzero f))
        q
      (if (or (equal q (pzero f)) (pconstp p))
          p
        (if (pconstp q)
            q
          (if (>= (degree p) (degree q))
              (let* ((c (fmul (car p) (frecip (car q) f) f))
	             (a (monomial c (- (degree p) (degree q)) f))
	             (pnew (padd p (pneg (pmul a q f) f) f)))
                (and (< (len pnew) (len p))
	             (pgcd-aux pnew q f)))
 	    (let* ((c (fmul (car q) (frecip (car p) f) f))
	           (a (monomial c (- (degree q) (degree p)) f))
	           (qnew (padd q (pneg (pmul a p f) f) f)))
	      (and (< (len qnew) (len q))
	           (pgcd-aux p qnew f))))))))

  (defun r$-aux (p q f)
    (declare (xargs :measure (list (len f) 7 (+ (len p) (len q)))))
    (if (equal p (pzero f))
        (pzero f)
      (if (or (equal q (pzero f)) (pconstp p))
          (pone f)
        (if (pconstp q)
            (pzero f)
          (if (>= (degree p) (degree q))
              (let* ((c (fmul (car p) (frecip (car q) f) f))
	             (a (monomial c (- (degree p) (degree q)) f))
	             (pnew (padd p (pneg (pmul a q f) f) f)))
                (and (< (len pnew) (len p))
	             (r$-aux pnew q f)))
 	    (let* ((c (fmul (car q) (frecip (car p) f) f))
	           (a (monomial c (- (degree q) (degree p)) f))
	           (qnew (padd q (pneg (pmul a p f) f) f)))
	      (and (< (len qnew) (len q))
	           (padd (r$-aux p qnew f)
	                 (pneg (pmul a (s$-aux p qnew f) f) f)
		         f))))))))
	            
  (defun s$-aux (p q f)
    (declare (xargs :measure (list (len f) 7 (+ (len p) (len q)))))
    (if (equal p (pzero f))
        (pone f)
      (if (or (equal q (pzero f)) (pconstp p))
          (pzero f)
        (if (pconstp q)
            (pone f)
          (if (>= (degree p) (degree q))
              (let* ((c (fmul (car p) (frecip (car q) f) f))
	             (a (monomial c (- (degree p) (degree q)) f))
	             (pnew (padd p (pneg (pmul a q f) f) f)))
                (and (< (len pnew) (len p))
	             (padd (s$-aux pnew q f)
	                   (pneg (pmul a (r$-aux pnew q f) f) f)
		           f)))
 	    (let* ((c (fmul (car q) (frecip (car p) f) f))
	           (a (monomial c (- (degree q) (degree p)) f))
	           (qnew (padd q (pneg (pmul a p f) f) f)))
	      (and (< (len qnew) (len q))
	           (s$-aux p qnew f))))))))

  (defund pgcd (p q f)
    (declare (xargs :measure (list (len f) 8 0)))
    (let ((g (pgcd-aux p q f)))
      (cmul (frecip (car g) f) g f)))

  (defund r$ (p q f)
    (declare (xargs :measure (list (len f) 8 0)))
    (let ((g (pgcd-aux p q f))
          (r (r$-aux p q f)))
      (cmul (frecip (car g) f) r f)))

  (defund s$ (p q f)
    (declare (xargs :measure (list (len f) 8 0)))
    (let ((g (pgcd-aux p q f))
          (s (s$-aux p q f)))
      (cmul (frecip (car g) f) s f)))

  ;; Division of polynomials:

  (defun pdivide (x y f)
    (declare (xargs :measure (list (len f) 7 (len x))))
    (if (pconstp y)
        (mv (cmul (frecip (car y) f) x f) (pzero f))
      (if (< (degree x) (degree y))
          (mv (pzero f) x)
        (let* ((c (fmul (car x) (frecip (car y) f) f))
               (m (monomial c (- (degree x) (degree y)) f))
	       (x1 (padd x (pneg (pmul m y f) f) f)))
	  (if (< (len x1) (len x))
              (mv-let (q r) (pdivide x1 y f)
	        (mv (padd q m f) r))
            (mv () ()))))))

  (defund pquot (x y f)
    (declare (xargs :measure (list (len f) 8 0)))
    (mv-nth 0 (mv-list 2 (pdivide x y f))))

  (defund prem (x y f)
    (declare (xargs :measure (list (len f) 8 0)))
    (mv-nth 1 (mv-list 2 (pdivide x y f))))

))

;; ---- verbatim: extensions.lisp:493-527 ----
;;; projects/fields/extensions.lisp, lines 493-494
(defund pdivides (q p f)
  (equal (prem p q f) (pzero f)))

;; If p has a non-constant divisor of lesser degree, then it has a monic divisor q of the same lesser 
;; degree.  In this case, such a divisor is returned by the following function and p is said to be
;; reducible:

;;; projects/fields/extensions.lisp, lines 500-505
(defchoose pfactor q (p f)
  (and (polyp q f)
       (monicp q f)
       (> (degree q) 0)
       (< (degree q) (degree p))
       (pdivides q p f)))

;;; projects/fields/extensions.lisp, lines 507-513
(defund reduciblep (p f)
  (let ((q (pfactor p f)))
    (and (polyp q f)
         (monicp q f)
         (> (degree q) 0)
         (< (degree q) (degree p))
         (pdivides q p f))))
       
;;; projects/fields/extensions.lisp, lines 515-516
(defund irreduciblep (p f)
  (not (reduciblep p f)))

;; We can now formally define our notion of a field extension:

;;; projects/fields/extensions.lisp, lines 520-527
(defund fieldp (f)
  (if (consp f)
      (and (fieldp (cdr f))
           (polyp (car f) (cdr f))
           (monicp (car f) (cdr f))
	   (irreduciblep (car f) (cdr f))
	   (>= (degree (car f)) 2))
    (fbasep f)))

;; ---- verbatim: extensions.lisp:650-740 ----
;;; projects/fields/extensions.lisp, lines 650-653
(defun-sk fadd-closed-p (f)
  (forall (x y)
    (implies (and (feltp x f) (feltp y f))
             (feltp (fadd x y f) f))))

;;; projects/fields/extensions.lisp, lines 655-658
(defun-sk fmul-closed-p (f)
  (forall (x y)
    (implies (and (feltp x f) (feltp y f))
             (feltp (fmul x y f) f))))

;; Commutativity:

;;; projects/fields/extensions.lisp, lines 662-665
(defun-sk fadd-comm-p (f)
  (forall (x y)
    (implies (and (feltp x f) (feltp y f))
             (equal (fadd x y f) (fadd y x f)))))

;;; projects/fields/extensions.lisp, lines 667-670
(defun-sk fmul-comm-p (f)
  (forall (x y)
    (implies (and (feltp x f) (feltp y f))
             (equal (fmul x y f) (fmul y x f)))))

;; Associativity:

;;; projects/fields/extensions.lisp, lines 674-678
(defun-sk fadd-assoc-p (f)
  (forall (x y z)
    (implies (and (feltp x f) (feltp y f) (feltp z f))
             (equal (fadd (fadd x y f) z f)
                    (fadd x (fadd y z f) f)))))

;;; projects/fields/extensions.lisp, lines 680-684
(defun-sk fmul-assoc-p (f)
  (forall (x y z)
    (implies (and (feltp x f) (feltp y f) (feltp z f))
             (equal (fmul (fmul x y f) z f)
                    (fmul x (fmul y z f) f)))))

;; Identities

;;; projects/fields/extensions.lisp, lines 688-689
(defun feltp-fzero-p (f)
  (feltp (fzero f) f))

;;; projects/fields/extensions.lisp, lines 691-692
(defun feltp-fone-p (f)
  (feltp (fone f) f))

;;; projects/fields/extensions.lisp, lines 694-695
(defun fone-fzero-p (f)
  (not (equal (fzero f) (fone f))))

;;; projects/fields/extensions.lisp, lines 697-701
(defun-sk fzero-id-p (f)
  (forall (x)
    (implies (feltp x f)
             (equal (fadd (fzero f) x f)
                    x))))

;;; projects/fields/extensions.lisp, lines 703-707
(defun-sk fone-id-p (f)
  (forall (x)
    (implies (feltp x f)
             (equal (fmul (fone f) x f)
                    x))))

;; Inverses:

;;; projects/fields/extensions.lisp, lines 711-714
(defun-sk feltp-fneg-p (f)
  (forall (x)
    (implies (feltp x f)
             (feltp (fneg x f) f))))

;;; projects/fields/extensions.lisp, lines 716-720
(defun-sk fadd-fneg-p (f)
  (forall (x)
    (implies (feltp x f)
             (equal (fadd x (fneg x f) f)
                    (fzero f)))))

;;; projects/fields/extensions.lisp, lines 722-725
(defun-sk feltp-frecip-p (f)
  (forall (x)
    (implies (and (feltp x f) (not (equal x (fzero f))))
             (feltp (frecip x f) f))))

;;; projects/fields/extensions.lisp, lines 727-731
(defun-sk fmul-frecip-p (f)
  (forall (x)
    (implies (and (feltp x f) (not (equal x (fzero f))))
             (equal (fmul x (frecip x f) f)
                    (fone f)))))

;; Distributivity:

;;; projects/fields/extensions.lisp, lines 735-739
(defun-sk fdistrib-p (f)
  (forall (x y z)
    (implies (and (feltp x f) (feltp y f) (feltp z f))
             (equal (fmul x (fadd y z f) f)
                    (fadd (fmul x y f) (fmul x z f) f)))))


;; ---- verbatim: extensions.lisp:831-847 ----
;;; projects/fields/extensions.lisp, lines 831-847
(defund field-axioms-p (f)
  (and (fadd-closed-p f)
       (fmul-closed-p f)
       (fadd-comm-p f)
       (fmul-comm-p f)
       (fadd-assoc-p f)
       (fmul-assoc-p f)
       (feltp-fzero-p f)
       (feltp-fone-p f)
       (fone-fzero-p f)
       (fzero-id-p f)
       (fone-id-p f)
       (feltp-fneg-p f)
       (fadd-fneg-p f)
       (feltp-frecip-p f)
       (fmul-frecip-p f)
       (fdistrib-p f)))

;; ---- verbatim: extensions.lisp:923-925 ----
;;; projects/fields/extensions.lisp, lines 923-925
(in-theory (disable fadd-closed-p fmul-closed-p fadd-comm-p fmul-comm-p fadd-assoc-p fmul-assoc-p feltp-fone-p 
                    fone-fzero-p feltp-fzero-p fzero-id-p fone-id-p fadd-fneg-p feltp-fneg-p feltp-frecip-p
		    fmul-frecip-p fdistrib-p))

;; ---- verbatim: extensions.lisp:1117-1117 ----
;;; projects/fields/extensions.lisp, lines 1117-1117
(in-theory (disable (fzero) (fone)))

;; ---- verbatim: extensions.lisp:3613-3619 ----
;;; projects/fields/extensions.lisp, lines 3613-3616
(defun extends (e f)
  (or (equal e f)
      (and (consp e)
           (extends (cdr e) f))))

;;; projects/fields/extensions.lisp, lines 3618-3619
(defun extensionp (e f)
  (and (fieldp f) (fieldp e) (extends e f)))

;; ---- verbatim: extensions.lisp:3632-3638 ----
;;; projects/fields/extensions.lisp, lines 3632-3635
(defun fliftn (x n)
  (if (zp n)
      x
    (list (fliftn x (1- n)))))

;;; projects/fields/extensions.lisp, lines 3637-3638
(defund flift (x f e)
  (fliftn x (- (len e) (len f))))

;; ---- verbatim: extensions.lisp:3712-3715 ----
;;; projects/fields/extensions.lisp, lines 3712-3715
(defun plift (p f e)
  (if (consp p)
      (cons (flift (car p) f e) (plift (cdr p) f e))
    ()))

;; ---- verbatim: vectors.lisp:284-288 ----
;;; ===== from projects/fields/vectors.lisp =====
;;; projects/fields/vectors.lisp, lines 284-288
(defun edegree (e f)
  (if (equal e f)
      1
    (and (consp e)
         (* (degree (car e)) (edegree (cdr e) f)))))

;; ---- verbatim: polynomials.lisp:22-25 ----
;;; ===== from projects/fields/polynomials.lisp =====
;;; projects/fields/polynomials.lisp, lines 22-25
(defun fpower (x n f)
  (if (zp n)
      (fone f)
    (fmul x (fpower x (1- n) f) f)))

;; ---- local lemma (authors' statement, extensions.lisp:1682) used by the peval termination hint ----
;;; ===== from projects/fields/extensions.lisp =====
;;; projects/fields/extensions.lisp, lines 1682-1683 (wrapped in local)
(local (defthmd len-pstrip
  (<= (len (pstrip x f)) (len x))))

;; ---- verbatim: polynomials.lisp:62-70 ----
;;; ===== from projects/fields/polynomials.lisp =====
;;; projects/fields/polynomials.lisp, lines 62-70
(defun peval (p x f)
  (declare (xargs :measure (len p) :hints (("Goal" :use ((:instance len-pstrip (x (cdr p))))))))
  (if (consp p)
      (if (pconstp p)
          (car p)
	(fadd (fmul (car p) (fpower x (degree p) f) f)
	      (peval (pstrip (cdr p) f) x f)
	      f))
    ()))

;; ---- verbatim: polynomials.lisp:174-176 ----
;;; projects/fields/polynomials.lisp, lines 174-176
(defund prootp (x p f)
  (and (feltp x f)
       (equal (peval p x f) (fzero f))))

;; ---- local lemmas for the termination proof of factorization (DEVIATION: the authors'
;; hint :use (reduciblep-product) is replaced; see README.md) ----
;;; not from the authors' sources
(local (defthm len-pstrip-linear
  (<= (len (pstrip x f)) (len x))
  :rule-classes :linear))

;;; not from the authors' sources
(local (defun faddl-induct (x y)
  (declare (xargs :measure (+ (len x) (len y))))
  (if (> (len x) (len y))
      (faddl-induct (cdr x) y)
    (if (> (len y) (len x))
        (faddl-induct x (cdr y))
      (if (consp x)
          (faddl-induct (cdr x) (cdr y))
        ())))))

;;; not from the authors' sources
(local (defthm len-faddl
  (equal (len (faddl x y f)) (max (len x) (len y)))
  :hints (("Goal" :induct (faddl-induct x y)))))

;;; not from the authors' sources
(local (defthm len-append-local
  (equal (len (append x y)) (+ (len x) (len y)))))

;;; not from the authors' sources
(local (defthm len-pshift
  (equal (len (pshift p k f)) (+ (len p) (nfix k)))))

;;; not from the authors' sources
(local (defun pdivide-induct (x y f)
  (declare (xargs :measure (len x)))
  (if (pconstp y)
      t
    (if (< (degree x) (degree y))
        t
      (let* ((c (fmul (car x) (frecip (car y) f) f))
             (m (monomial c (- (degree x) (degree y)) f))
             (x1 (padd x (pneg (pmul m y f) f) f)))
        (if (< (len x1) (len x))
            (pdivide-induct x1 y f)
          t))))))

;;; not from the authors' sources
(local (defthm len-padd-bound
  (<= (len (padd p q f)) (max (len p) (len q)))
  :hints (("Goal" :in-theory (enable padd)))
  :rule-classes nil))

;;; not from the authors' sources
(local (defthm len-monomial
  (equal (len (monomial c k f)) (1+ (nfix k)))))

;;; not from the authors' sources
(local (defthm len-pdivide-quot-bound
  (implies (not (pconstp y))
           (<= (len (mv-nth 0 (pdivide x y f)))
               (max 1 (1- (len x)))))
  :hints (("Goal" :induct (pdivide-induct x y f)
                  :expand ((pdivide x y f))
                  :in-theory (e/d (pzero) (monomial)))
          ("Subgoal *1/2"
           :use ((:instance len-padd-bound
                  (p (mv-nth 0 (pdivide (padd x (pneg (pmul (monomial (fmul (car x) (frecip (car y) f) f)
                                                                      (- (degree x) (degree y)) f)
                                                            y f)
                                                      f)
                                              f)
                                        y f)))
                  (q (monomial (fmul (car x) (frecip (car y) f) f) (- (degree x) (degree y)) f))))))))

;;; not from the authors' sources
(local (defthm len-pquot-bound
  (implies (and (polyp d f) (> (degree d) 0) (>= (degree p) 2))
           (< (len (pquot p d f)) (len p)))
  :hints (("Goal" :in-theory (enable pquot polyp)
                  :use ((:instance len-pdivide-quot-bound (x p) (y d)))))))

;; ---- verbatim: polynomials.lisp:290-296, except the termination hint ----
;;; projects/fields/polynomials.lisp, lines 290-296 (termination hint changed; see README)
(defun factorization (p f)
  (declare (xargs :measure (len p) :hints (("Goal" :in-theory (enable reduciblep)))))
  (if (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 2) (reduciblep p f))
      (let ((d (pfactor p f)))
        (append (factorization d f)
                (factorization (pquot p d f) f)))
    (list p)))

;; ---- verbatim: polynomials.lisp:467-478 ----
;;; projects/fields/polynomials.lisp, lines 467-475
(defun proots-aux (l f)
  (if (consp l)
      (let ((d (proots-aux (cdr l) f))
            (r (fneg (cadar l) f)))
        (if (and (= (degree (car l)) 1)
	         (not (member r d)))
            (cons r d)
	  d))
    ()))

;;; projects/fields/polynomials.lisp, lines 477-478
(defund proots (p f)
  (proots-aux (factorization p f) f))

;; ---- embeddings.lisp needs the well-founded relation l< ----
;;; ===== from projects/fields/extensions.lisp =====
;;; projects/fields/extensions.lisp, lines 261-261
(local (include-book "ordinals/lexicographic-book" :dir :system))

;; ---- verbatim: embeddings.lisp:41-68 ----
;;; ===== from projects/fields/embeddings.lisp =====
;;; projects/fields/embeddings.lisp, lines 41-61
(mutual-recursion

  (defund embed (x phi k f)
    (declare (xargs :measure (list (len phi) (acl2-count x))
; Matt K. addition after bug fix to require well-founded relations to match for
; a redundant definition:
                    :well-founded-relation l<))
    (if (consp phi)
        (peval (pembed x (cdr phi) k f) (car phi) k)
      (flift x f k)))

  (defun pembed (p phi k f)
    (declare (xargs :measure (list (len phi) (acl2-count p))
; Matt K. addition after bug fix to require well-founded relations to match for
; a redundant definition:
                    :well-founded-relation l<))
    (if (consp p)
        (cons (embed (car p) phi k f)
              (pembed (cdr p) phi k f))
      ()))
)

;;; projects/fields/embeddings.lisp, lines 63-68
(defund embeddingp (phi e k f)
  (if (equal e f)
      (null phi)
    (and (consp phi)
	 (prootp (car phi) (pembed (car e) (cdr phi) k f) k)
	 (embeddingp (cdr phi) (cdr e) k f))))

;;----------------------------------------------------------------------------------------------------------
;; NEW (not in the authors' files): neutral predicates used by MAIN-3 and MAIN-4.
;;----------------------------------------------------------------------------------------------------------

;; x is a root of the lift to e of some monic irreducible polynomial p over f with
;; 1 <= degree(p) <= [e:f].  (Neutral existential form of polynomials.lisp:630, prootp-min-poly.)

;;; not from the authors' sources
(defun-sk algebraic-witness (x e f)
  (exists p
    (and (polyp p f)
         (monicp p f)
         (irreduciblep p f)
         (>= (degree p) 1)
         (<= (degree p) (edegree e f))
         (prootp x (plift p f e) e))))

;; Every member of l is an embedding of e in k over f.

;;; not from the authors' sources
(defun all-embeddingp (l e k f)
  (if (consp l)
      (and (embeddingp (car l) e k f)
           (all-embeddingp (cdr l) e k f))
    t))
