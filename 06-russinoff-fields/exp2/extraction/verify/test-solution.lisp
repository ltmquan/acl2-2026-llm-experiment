(in-package "DM")
(include-book "defs")
(skip-proofs (progn

;; Target theorems for russinoff-fields (D. M. Russinoff, "A Formal Theory of Algebraic
;; Field Extensions").  Symbols are in the DM package (defined by cert.acl2).

;; MAIN-1. Authors' name: field-axioms-p-fieldp, extensions.lisp:2585 (defthmd).
;; Every field object recognized by fieldp satisfies all 16 field axioms.
(defthm MAIN-1
  (implies (fieldp f) (field-axioms-p f)))

;; MAIN-2. Authors' names: len-proots-bound, polynomials.lisp:484, and member-proots,
;; polynomials.lisp:502 (both defthmd; same hypotheses, conjoined here).
;; A non-constant monic polynomial over f has at most (degree p) distinct roots, and
;; (proots p f) lists exactly its roots.
(defthm MAIN-2
  (implies (and (fieldp f) (polyp p f)
                (monicp p f) (>= (degree p) 1))
           (and (<= (len (proots p f))
                    (degree p))
                (iff (member x (proots p f))
                     (prootp x p f)))))

;; MAIN-3. Authors' name: prootp-min-poly, polynomials.lisp:630 (defthmd), restated in
;; neutral existential form (defun-sk algebraic-witness, defs.lisp) instead of naming
;; the witness min-poly.  Every element x of an extension e of f is a root of (the lift
;; to e of) a monic irreducible polynomial over f of degree between 1 and [e:f].
(defthm MAIN-3
  (implies (and (extensionp e f)
                (feltp x e))
           (algebraic-witness x e f)))

;; MAIN-4. Authors' names: all-embeddings, embeddings.lisp:644, and len-embeddings,
;; embeddings.lisp:653 (both defthmd), restated in neutral form without the constructed
;; enumeration (embeddings e k f): any duplicate-free list of embeddings of e in k over f
;; has length at most the degree [e:f].
(defthm MAIN-4
  (implies (and (extensionp e f) (extensionp k f)
                (dlistp l) (all-embeddingp l e k f))
           (<= (len l) (edegree e f))))
))
