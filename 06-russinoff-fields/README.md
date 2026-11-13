# 06 — Fields

**Paper:** David M. Russinoff, *A Formal Theory of Algebraic Field Extensions*. PDF: `source/paper.pdf`. **Logic:** ACL2.

The paper represents fields as ACL2 objects: a base field is Q, F_p or a generic field F0, and a simple extension is a pair (p . f) with p a monic irreducible polynomial over f of degree ≥ 2. Field and polynomial-ring operations form one large mutual recursion. The paper proves that every such field satisfies the field axioms, then develops polynomial roots and factorization (#roots ≤ degree), minimal polynomials (via Part III linear algebra), and field embeddings with a bound on their number.

**Authors' ACL2 books:** `source/authors-books/` (copy). From ACL2 master, `books/projects/fields/`.

## Experiment 1 — the model wrote the definitions, the statement and the proof

The model received only `exp1/prompt.txt` (below). Its answer is `exp1/solution.lisp`; it certifies, and its last
event is `MAIN`.

**To review:** do the definitions and `MAIN` in `exp1/solution.lisp` state the theorem in the prompt?

<details>
<summary>Experiment 1 prompt (exp1/prompt.txt)</summary>

```text
Formalize the definitions and the theorem below in ACL2, and prove the theorem.

<definitions>
A generic field F0 is defined through seven functions: a predicate that recognizes an element of the field; the field operations of addition and multiplication; the additive and multiplicative identities; and the additive and multiplicative inverse operators. Nothing is assumed about these functions except that they satisfy the usual field axioms.

The theory of fields rests on two fundamental notions: base field and simple field extension. The fields of the rational numbers and of the integers modulo a prime are both base fields. Along with the rational and prime fields, the generic field F0 is included as a base field. Q, F_p, and F0 denote the rational field, the field of order p, and the generic field, respectively.

A simple extension of a field f is constructed by the usual process of adjoining a root of an irreducible monic polynomial p over f of degree at least 2. The elements of such an extension are the polynomials over f of degree less than that of p; the field operations are polynomial addition and multiplication modulo p. A field is recursively defined to be either a base field or a simple extension of a field. The term field is reserved for these objects.

A polynomial is monic if its leading coefficient is the multiplicative identity of f. A polynomial p over f is reducible if it has a non-constant monic divisor of lesser degree; otherwise p is irreducible.

The functions of primary interest are those that characterize the structure of a field f: a predicate that recognizes an element of f; the field operations of addition and multiplication; the additive and multiplicative identities; and the additive and multiplicative inverses.
</definitions>

<theorem>
If f is a field, then f satisfies the field axioms, i.e., the properties corresponding to the constraints on the field F0. In particular, for every nonzero element x of f, the product of x and its multiplicative inverse is the multiplicative identity of f.
</theorem>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
Put your work in /work/solution.lisp; it must certify with `cert.pl` (add `--acl2 acl2r` for ACL2(r)), and its last
event must be the theorem, named MAIN.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done. When you are done, print the final contents of /work/solution.lisp.
```

</details>

## Experiment 2 — the model proved the authors' statements

The model received `exp2/prompt.txt` (below): the authors' definitions and the target theorems. Its answer is
`exp2/solution.lisp`; it certifies and proves every target with exactly the given statement.

- `exp2/definitions.lisp`: the definitions, with a comment before each form giving where in the authors'
  sources it comes from.
- `exp2/targets.lisp`: the target theorems, with the authors' theorem names in comments.

| Target | Authors' theorem(s) | Meaning |
|---|---|---|
| MAIN-1 | `field-axioms-p-fieldp` (extensions.lisp:2585) | every `fieldp` object satisfies all 16 field axioms |
| MAIN-2 | `len-proots-bound` ∧ `member-proots` (polynomials.lisp:484, 502) | a non-constant monic p over f has at most deg p roots, and `(proots p f)` lists exactly its roots |
| MAIN-3 | `prootp-min-poly`, neutral form (polynomials.lisp:630) | every x in an extension e of f is a root of (the lift of) a monic irreducible p over f with 1 ≤ deg p ≤ [e:f] |
| MAIN-4 | `all-embeddings` ∧ `len-embeddings`, neutral form (embeddings.lisp:644, 653) | every duplicate-free list of embeddings of e in k over f has length ≤ [e:f] |

<details>
<summary>Experiment 2 prompt (exp2/prompt.txt)</summary>

```text
Prove the theorems below in ACL2.

1. Create /work/defs.lisp, /work/cert.acl2, each containing exactly the text between its tags. defs.lisp holds the definitions the theorems use. Do not modify these files. Some definitions in defs.lisp are admitted with skip-proofs: their admissibility has been checked separately, and cert.acl2 permits skip-proofs so that books including defs.lisp can be certified. Your own files must not use skip-proofs: your solution will be checked against fully proved definitions without that permission.

<defs.lisp>
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
</defs.lisp>

<cert.acl2>
(include-book "projects/numbers/portcullis" :dir :system)
; cert-flags: ? t :skip-proofs-okp t
</cert.acl2>

2. Write /work/solution.lisp. It must (include-book "defs") and then prove every theorem in <theorems>, each with exactly the name and statement given (MAIN-1, MAIN-2, MAIN-3, MAIN-4). You may add your own definitions and lemmas before them.

<theorems>
(in-package "DM")


(defthm MAIN-1
  (implies (fieldp f) (field-axioms-p f)))

(defthm MAIN-2
  (implies (and (fieldp f) (polyp p f)
                (monicp p f) (>= (degree p) 1))
           (and (<= (len (proots p f))
                    (degree p))
                (iff (member x (proots p f))
                     (prootp x p f)))))

(defthm MAIN-3
  (implies (and (extensionp e f)
                (feltp x e))
           (algebraic-witness x e f)))

(defthm MAIN-4
  (implies (and (extensionp e f) (extensionp k f)
                (dlistp l) (all-embeddingp l e k f))
           (<= (len l) (edegree e f))))
</theorems>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
/work/solution.lisp must certify with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done. When you are done, print the final contents of /work/solution.lisp.
```

</details>
