# 06 — Fields

**Paper:** David M. Russinoff, *A Formal Theory of Algebraic Field Extensions* (ACL2 Workshop 2026). PDF in `source/paper.pdf`.
**Logic:** ACL2.

## The paper

The paper represents fields as ACL2 objects: a base field is Q, F_p or a generic field F0, and a
simple extension is a pair (p . f) with p a monic irreducible polynomial over f of degree ≥ 2. Field and
polynomial-ring operations form one large mutual recursion. The paper proves that every such field satisfies
the field axioms, then develops polynomial roots and factorization (#roots ≤ degree), minimal polynomials (via
Part III linear algebra), and field embeddings with a bound on their number.

**Contribution.** Mainly a library and representation technique (fields and embeddings as first-order
objects), with standard algebra theorems proved along the way.

**Authors' ACL2 books.** In the ACL2 community books on master, added after 8.7: `books/projects/fields/`
(commit 1d2b39a424). A copy is in `source/authors-books/` (it also contains `galois.lisp`, a later Galois-theory
development not described in this paper).

## Files

```
06-russinoff-fields/
  README.md
  source/
    paper.pdf
    authors-books/        the authors' ACL2 books (copy)
  exp1/
    prompt.txt            the exact prompt sent to the model
    solution.lisp         the model's final /work/solution.lisp
    audit.txt             transcript audit (tools/audit.py)
    review.md             short factual review of the run
  exp2/
    prompt.txt            the exact prompt sent to the model
    definitions.lisp      the definitions, annotated with their source locations (comments only)
    targets.lisp          the target theorems (the authors' names in comments)
    checker/              the exact files the checker certifies against (hashes below)
    model-facing/         the definitions file the model was given (see below)
    extraction/           how definitions.lisp was built and verified (NOTES.md, scripts, logs)
    solution.lisp         the model's final /work/solution.lisp
    audit.txt
    review.md
```

## Results

| | Experiment 1 (English → ACL2) | Experiment 2 (ACL2 statements) |
|---|---|---|
| Result | proved (certified) | all 4 target(s) proved (certified, statements matched) |
| Model time | 38 min | 1 h 57 min |
| Tool calls | 91 | 237 |
| Certification time of solution.lisp (ACL2 8.7) | 2.6 s | 750.5 s |
| Audit | CLEAN | CLEAN |
| solution.lisp: lines / definitions / theorems | 1541 / 58 / 230 | 3101 / 58 / 552 |

Authors' development (for scale): 6 files without `galois.lisp`, 24,094 lines, 486 definitions, 1,616 theorems.

*Model time* runs from when the model received the prompt to the end of its run (setup not included).
Certification time is for `solution.lisp` alone, with its dependencies already certified, on our build
(experiment 2: against `exp2/checker/`). Sizes are counted with `tools/sizes.py` (definitions = `defun`,
`define`, `defun-sk`, `defmacro`, … and encapsulated functions; theorems = `defthm`, `defrule`, …, local
ones included). Both experiments: first attempt, Claude Opus 5.5 at medium effort.

## Experiment 1: English definitions and theorem

**Theorem given:** If f is a field (a tower of simple algebraic extensions over Q, F_p or the generic field F0), then f satisfies the field axioms; in particular every nonzero element has a multiplicative inverse. Composed from §3.

### Statement rewrites (paper text → prompt)

The definitions and theorem were copied from the paper as close to verbatim as possible. Every edit:

**THEOREM IS COMPOSED (flag).** The paper has no single English statement. Sources: the first sentence of §3 (p. 5), plus the "In particular" clause taken from §3's `fmul-frecip-**`, "the defining property of the multiplicative inverse" (pp. 6–7).

#### Sources
- F0: §1 p.1. Base fields and Q/F_p/F0: §2 pp.2–3. Extension and recursive definition: §2 ¶1 p.2 (degree ≥ 2 from the fieldp code, p.5). "Field reserved": §1 p.2. Monic: p.4. Reducible: p.5. Structure list: p.3.

#### Edits (original → edited)
1. "The first defines a generic field through seven constrained functions: (fp x), a predicate…; … The exported constraints on these functions correspond to the usual field axioms." → "A generic field F0 is defined through seven functions: … Nothing is assumed about these functions except that they satisfy the usual field axioms." The ACL2 names and "encapsulation" are removed.
2. "Our theory" → "The theory". "Since we are interested in number fields and finite fields," is deleted.
3. "we shall include the generic field described in Section 1 as a base field, for two reasons: …" → "the generic field F0 is included as a base field." The motivation is cut.
4. "we shall informally refer to … as Q, Fp, and F0" → "Q, F_p, and F0 denote …".
5. Added "of degree at least 2". It is stated only in the `fieldp` code.
6. "A field will be recursively defined" → "is recursively defined". Added "The term field is reserved for these objects." (from §1).
7. Monic: "(i.e., with leading coefficient (fone f))" → a full sentence.
8. "If a polynomial p has a non-constant monic divisor of lesser degree, then the following function returns such a divisor and p is said to be reducible" → "A polynomial p over f is reducible if …; otherwise p is irreducible." The `defchoose` is removed.
9. The structure bullet list is turned into prose, without ACL2 names.
10. Theorem: "Our next objective is to prove that if f satisfies the predicate fieldp, then f satisfies the field axioms, i.e., …F0, and the polynomials over f satisfy the axioms for a commutative ring with unity." → "If f is a field, then f satisfies the field axioms, i.e., …F0." The ring clause is dropped because it is a supporting result. "In particular …" is added (composed).

**Omitted on purpose:**
- the encodings (0, a prime, `'f0`, (p . f));
- polynomials as coefficient lists with leading-zero stripping;
- the Bézout-based inverse in an extension, which is both an encoding and a proof hint.

### Prompt

<details>
<summary>Experiment 1 prompt (also in exp1/prompt.txt)</summary>

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

## Experiment 2: the authors' ACL2 definitions and statements

### Targets

| Target | Authors' theorem(s) | Meaning |
|---|---|---|
| MAIN-1 | `field-axioms-p-fieldp` (extensions.lisp:2585) | every `fieldp` object satisfies all 16 field axioms |
| MAIN-2 | `len-proots-bound` ∧ `member-proots` (polynomials.lisp:484, 502) | a non-constant monic p over f has at most deg p roots, and `(proots p f)` lists exactly its roots |
| MAIN-3 | `prootp-min-poly`, neutral form (polynomials.lisp:630) | every x in an extension e of f is a root of (the lift of) a monic irreducible p over f with 1 ≤ deg p ≤ [e:f] |
| MAIN-4 | `all-embeddings` ∧ `len-embeddings`, neutral form (embeddings.lisp:644, 653) | every duplicate-free list of embeddings of e in k over f has length ≤ [e:f] |

### How the definitions were extracted

`definitions.lisp` is assembled from verbatim line ranges of master `extensions.lisp`,
`vectors.lisp`, `polynomials.lisp` and `embeddings.lisp`, plus the 8.7 books `projects/groups/groups` and
`projects/linear/field`. It contains the 21-function mutual recursion, `fieldp`, the 16 axiom predicates,
`field-axioms-p`, polynomial evaluation, roots and factorization, `edegree`, the lifting functions and
embeddings. Local lemmas are purely syntactic length facts needed for termination. Two predicates are new (not
by the authors): `algebraic-witness` (for MAIN-3) and `all-embeddingp` (for MAIN-4).

The general procedure, and how each package was checked, is in [`../EXPERIMENT-2.md`](../EXPERIMENT-2.md);
the full notes for this paper are in `exp2/extraction/NOTES.md`.

**What the model saw.** The checker's `definitions.lisp` needs local lemmas to admit some definitions. Those
lemmas can contain parts of the proofs, so the model was given `exp2/model-facing/defs.lisp`
instead: local lemmas and hints removed, comments removed, and each definition wrapped in `skip-proofs`, with
`exp2/model-facing/cert.acl2` allowing `skip-proofs` for that one book. The model's own solution could not use
`skip-proofs`, and the checker certifies it against the fully proved `checker/defs.lisp`. A dump of every
name each version introduces (formals, body, guard, measure, constraints, macro bodies) was identical for the
two versions (`tools/world-dump.lsp`).

Checker files:

| File | SHA-256 |
|---|---|
| `exp2/checker/cert.acl2` | `e39b0ab97ce3526d595a9df27a4e5a4fe42bdbbc2e6eef70ed6a782d17901975` |
| `exp2/checker/defs.lisp` | `31fdd442fa69360e77e32dc00d02c894f9baae30e7a1e7b3162ca818cb533b6e` |

`exp2/definitions.lisp` differs from `exp2/checker/defs.lisp` only in comments
(`tools/check-comments-only.py`).

### Statement rewrites (authors' ACL2 → targets)

- **MAIN-3 and MAIN-4 are neutral restatements.** The authors' statements use the constructive `min-poly` and
  `embeddings`, which would reveal the proof. MAIN-3 says instead that a suitable polynomial exists
  (`defun-sk algebraic-witness`); MAIN-4 bounds the length of any duplicate-free list of embeddings. Both were
  proved from the authors' theorems on master.
- **The termination hint of `factorization` is changed.** The authors' hint uses `reduciblep-product`, which
  needs most of the MAIN-1 theory; we prove the needed length bound locally instead. Measure and body are
  unchanged.
- MAIN-2 conjoins two authors' theorems with the same hypotheses. `defthmd` became `defthm`, hints dropped.
- Package DM, with `cert.acl2` loading `projects/numbers/portcullis`.

### Prompt

<details>
<summary>Experiment 2 prompt (also in exp2/prompt.txt)</summary>

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

## Notes for reviewers

**Experiment 2.**
- The model ended its first turn while waiting for a certification and was woken by its own `Monitor` tool
  (a local wait loop); it was not prompted by anyone. The audit therefore uses the whole transcript as the run.
- The final message claims the given `defs.lisp` had an unbalanced paren. It did not: the model dropped a paren
  when writing the file from the prompt. The checker uses its own copy, so this does not matter.

