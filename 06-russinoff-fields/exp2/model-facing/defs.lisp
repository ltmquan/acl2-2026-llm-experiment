(in-package "DM")

(include-book "projects/groups/groups" :dir :system)

(include-book "projects/linear/field" :dir :system)

(skip-proofs
(defund fbasep (f)
  (or (zerop f)       ;the rational field is encoded as 0
      (primep f)      ;the prime field of order p is encoded as p
      (equal f 'f0))))

(skip-proofs
(defund beltp (x f)
  (cond ((zerop f) (rationalp x))
        ((primep f) (member x (ninit f)))
	(t (fp x)))))

(skip-proofs
(defund badd (x y f)
  (cond ((zerop f) (+ x y))
        ((primep f) (mod (+ x y) f))
	(t (f+ x y)))))

(skip-proofs
(defund bmul (x y f)
  (cond ((zerop f) (* x y))
        ((primep f) (mod (* x y) f))
	(t (f* x y)))))

(skip-proofs
(defund bzero (f)
  (if (integerp f) 0 (f0))))

(skip-proofs
(defund bone (f)
  (if (integerp f) 1 (f1))))

(skip-proofs
(defund bneg (x f)
  (cond ((zerop f) (- x))
        ((primep f) (mod (- x) f))
	(t (f- x)))))

(skip-proofs
(defund brecip (x f)
  (cond ((zerop f) (/ x))
        ((primep f) (mod (expt x (- f 2)) f))
	(t (f/ x)))))

(in-theory (disable (fbasep) (beltp) (badd) (bmul) (bzero) (bone) (bneg) (brecip)))

(skip-proofs
(defund fzero (f)
  (if (consp f)
      (list (fzero (cdr f)))
    (bzero f))))

(skip-proofs
(defund fone (f)
  (if (consp f)
      (list (fone (cdr f)))
    (bone f))))

(skip-proofs
(defund pzero (f)
  (list (fzero f))))

(skip-proofs
(defund pone (f)
  (list (fone f))))

(skip-proofs
(defund monicp (p f)
  (equal (car p) (fone f))))

(skip-proofs
(defun pconstp (p)
  (not (consp (cdr p)))))

(skip-proofs
(defun degree (p)
  (1- (len p))))

(skip-proofs
(defun pstrip (l f)
  (if (and (consp l) (consp (cdr l)) (equal (car l) (fzero f)))
      (pstrip (cdr l) f)
    l)))

(skip-proofs
(defun pshift (p k f)
  (if (zp k)
      p
    (pshift (append p (list (fzero f))) (1- k) f))))

(skip-proofs
(defun monomial (c k f)
  (pshift (list c) k f)))

(skip-proofs
(encapsulate ()

(local (include-book "ordinals/lexicographic-book" :dir :system))

(set-well-founded-relation acl2::l<)

(mutual-recursion

  
  (defund feltp (x f)
    (declare (xargs :measure (list (len f) 0 0)))
    (if (consp f)
        (and (polyp x (cdr f))
             (< (degree x) (degree (car f))))
      (beltp x f)))


  (defun feltsp (l f)
    (declare (xargs :measure (list (len f) 1 (len l))))
    (if (consp l)
        (and (feltp (car l) f)
             (feltsp (cdr l) f))
      (null l)))


  (defund polyp (p f)
    (declare (xargs :measure (list (len f) 2 0)))
    (and (feltsp p f)
         (consp p)
         (or (null (cdr p))
             (not (equal (car p) (fzero f))))))


  (defund fadd (x y f)
    (declare (xargs :measure (list (len f) 2 0)))
    (if (consp f)
        (padd x y (cdr f))
      (badd x y f)))


  (defund fneg (x f)
    (declare (xargs :measure (list (len f) 2 0)))
    (if (consp f)
        (pneg x (cdr f))
      (bneg x f)))


  (defun pneg (x f)
    (declare (xargs :measure (list (len f) 3 (len x))))
    (if (consp x)
        (cons (fneg (car x) f)
              (pneg (cdr x) f))
      ()))


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


  (defund padd (p q f)
    (declare (xargs :measure (list (len f) 4 0)))
    (pstrip (faddl p q f) f))


  (defun fmul (x y f)
    (declare (xargs :measure (list (len f) 4 0)))
    (if (consp f)
        (prem (pmul x y (cdr f)) (car f) (cdr f))
      (bmul x y f)))


  (defun cmul (x p f)
    (declare (xargs :measure (list (len f) 5 (len p))))
    (if (equal x (fzero f))
        (list (fzero f))
      (if (consp p)
          (cons (fmul x (car p) f)
	        (cmul x (cdr p) f))
        ())))


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


  (defund frecip (x f)
    (declare (xargs :measure (list (len f) 6 0)))
    (if (consp f)
        (prem (r$ x (car f) (cdr f)) (car f) (cdr f))
      (brecip x f)))


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

)))

(skip-proofs
(defund pdivides (q p f)
  (equal (prem p q f) (pzero f))))

(skip-proofs
(defchoose pfactor q (p f)
  (and (polyp q f)
       (monicp q f)
       (> (degree q) 0)
       (< (degree q) (degree p))
       (pdivides q p f))))

(skip-proofs
(defund reduciblep (p f)
  (let ((q (pfactor p f)))
    (and (polyp q f)
         (monicp q f)
         (> (degree q) 0)
         (< (degree q) (degree p))
         (pdivides q p f)))))

(skip-proofs
(defund irreduciblep (p f)
  (not (reduciblep p f))))

(skip-proofs
(defund fieldp (f)
  (if (consp f)
      (and (fieldp (cdr f))
           (polyp (car f) (cdr f))
           (monicp (car f) (cdr f))
	   (irreduciblep (car f) (cdr f))
	   (>= (degree (car f)) 2))
    (fbasep f))))

(skip-proofs
(defun-sk fadd-closed-p (f)
  (forall (x y)
    (implies (and (feltp x f) (feltp y f))
             (feltp (fadd x y f) f)))))

(skip-proofs
(defun-sk fmul-closed-p (f)
  (forall (x y)
    (implies (and (feltp x f) (feltp y f))
             (feltp (fmul x y f) f)))))

(skip-proofs
(defun-sk fadd-comm-p (f)
  (forall (x y)
    (implies (and (feltp x f) (feltp y f))
             (equal (fadd x y f) (fadd y x f))))))

(skip-proofs
(defun-sk fmul-comm-p (f)
  (forall (x y)
    (implies (and (feltp x f) (feltp y f))
             (equal (fmul x y f) (fmul y x f))))))

(skip-proofs
(defun-sk fadd-assoc-p (f)
  (forall (x y z)
    (implies (and (feltp x f) (feltp y f) (feltp z f))
             (equal (fadd (fadd x y f) z f)
                    (fadd x (fadd y z f) f))))))

(skip-proofs
(defun-sk fmul-assoc-p (f)
  (forall (x y z)
    (implies (and (feltp x f) (feltp y f) (feltp z f))
             (equal (fmul (fmul x y f) z f)
                    (fmul x (fmul y z f) f))))))

(skip-proofs
(defun feltp-fzero-p (f)
  (feltp (fzero f) f)))

(skip-proofs
(defun feltp-fone-p (f)
  (feltp (fone f) f)))

(skip-proofs
(defun fone-fzero-p (f)
  (not (equal (fzero f) (fone f)))))

(skip-proofs
(defun-sk fzero-id-p (f)
  (forall (x)
    (implies (feltp x f)
             (equal (fadd (fzero f) x f)
                    x)))))

(skip-proofs
(defun-sk fone-id-p (f)
  (forall (x)
    (implies (feltp x f)
             (equal (fmul (fone f) x f)
                    x)))))

(skip-proofs
(defun-sk feltp-fneg-p (f)
  (forall (x)
    (implies (feltp x f)
             (feltp (fneg x f) f)))))

(skip-proofs
(defun-sk fadd-fneg-p (f)
  (forall (x)
    (implies (feltp x f)
             (equal (fadd x (fneg x f) f)
                    (fzero f))))))

(skip-proofs
(defun-sk feltp-frecip-p (f)
  (forall (x)
    (implies (and (feltp x f) (not (equal x (fzero f))))
             (feltp (frecip x f) f)))))

(skip-proofs
(defun-sk fmul-frecip-p (f)
  (forall (x)
    (implies (and (feltp x f) (not (equal x (fzero f))))
             (equal (fmul x (frecip x f) f)
                    (fone f))))))

(skip-proofs
(defun-sk fdistrib-p (f)
  (forall (x y z)
    (implies (and (feltp x f) (feltp y f) (feltp z f))
             (equal (fmul x (fadd y z f) f)
                    (fadd (fmul x y f) (fmul x z f) f))))))

(skip-proofs
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
       (fdistrib-p f))))

(in-theory (disable fadd-closed-p fmul-closed-p fadd-comm-p fmul-comm-p fadd-assoc-p fmul-assoc-p feltp-fone-p 
                    fone-fzero-p feltp-fzero-p fzero-id-p fone-id-p fadd-fneg-p feltp-fneg-p feltp-frecip-p
		    fmul-frecip-p fdistrib-p))

(in-theory (disable (fzero) (fone)))

(skip-proofs
(defun extends (e f)
  (or (equal e f)
      (and (consp e)
           (extends (cdr e) f)))))

(skip-proofs
(defun extensionp (e f)
  (and (fieldp f) (fieldp e) (extends e f))))

(skip-proofs
(defun fliftn (x n)
  (if (zp n)
      x
    (list (fliftn x (1- n))))))

(skip-proofs
(defund flift (x f e)
  (fliftn x (- (len e) (len f)))))

(skip-proofs
(defun plift (p f e)
  (if (consp p)
      (cons (flift (car p) f e) (plift (cdr p) f e))
    ())))

(skip-proofs
(defun edegree (e f)
  (if (equal e f)
      1
    (and (consp e)
         (* (degree (car e)) (edegree (cdr e) f))))))

(skip-proofs
(defun fpower (x n f)
  (if (zp n)
      (fone f)
    (fmul x (fpower x (1- n) f) f))))

(skip-proofs
(defun peval (p x f)
  (declare (xargs :measure (len p) ))
  (if (consp p)
      (if (pconstp p)
          (car p)
	(fadd (fmul (car p) (fpower x (degree p) f) f)
	      (peval (pstrip (cdr p) f) x f)
	      f))
    ())))

(skip-proofs
(defund prootp (x p f)
  (and (feltp x f)
       (equal (peval p x f) (fzero f)))))

(skip-proofs
(defun factorization (p f)
  (declare (xargs :measure (len p) ))
  (if (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 2) (reduciblep p f))
      (let ((d (pfactor p f)))
        (append (factorization d f)
                (factorization (pquot p d f) f)))
    (list p))))

(skip-proofs
(defun proots-aux (l f)
  (if (consp l)
      (let ((d (proots-aux (cdr l) f))
            (r (fneg (cadar l) f)))
        (if (and (= (degree (car l)) 1)
	         (not (member r d)))
            (cons r d)
	  d))
    ())))

(skip-proofs
(defund proots (p f)
  (proots-aux (factorization p f) f)))

(local (include-book "ordinals/lexicographic-book" :dir :system))

(skip-proofs
(mutual-recursion

  (defund embed (x phi k f)
    (declare (xargs :measure (list (len phi) (acl2-count x))
                    :well-founded-relation l<))
    (if (consp phi)
        (peval (pembed x (cdr phi) k f) (car phi) k)
      (flift x f k)))

  (defun pembed (p phi k f)
    (declare (xargs :measure (list (len phi) (acl2-count p))
                    :well-founded-relation l<))
    (if (consp p)
        (cons (embed (car p) phi k f)
              (pembed (cdr p) phi k f))
      ()))
))

(skip-proofs
(defund embeddingp (phi e k f)
  (if (equal e f)
      (null phi)
    (and (consp phi)
	 (prootp (car phi) (pembed (car e) (cdr phi) k f) k)
	 (embeddingp (cdr phi) (cdr e) k f)))))

(skip-proofs
(defun-sk algebraic-witness (x e f)
  (exists p
    (and (polyp p f)
         (monicp p f)
         (irreduciblep p f)
         (>= (degree p) 1)
         (<= (degree p) (edegree e f))
         (prootp x (plift p f e) e)))))

(skip-proofs
(defun all-embeddingp (l e k f)
  (if (consp l)
      (and (embeddingp (car l) e k f)
           (all-embeddingp (cdr l) e k f))
    t)))
