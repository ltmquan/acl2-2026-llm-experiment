(in-package "DM")
;; V3 (faithfulness): prove the targets from the authors' own development on the ACL2
;; master build.  The two NEW predicates are copied verbatim from defs.lisp.
(include-book "projects/fields/embeddings" :dir :system)

(defun-sk algebraic-witness (x e f)
  (exists p
    (and (polyp p f)
         (monicp p f)
         (irreduciblep p f)
         (>= (degree p) 1)
         (<= (degree p) (edegree e f))
         (prootp x (plift p f e) e))))

;; Every member of l is an embedding of e in k over f.

(defun all-embeddingp (l e k f)
  (if (consp l)
      (and (embeddingp (car l) e k f)
           (all-embeddingp (cdr l) e k f))
    t))

;; MAIN-1 from field-axioms-p-fieldp (extensions.lisp:2585)
(defthm MAIN-1
  (implies (fieldp f) (field-axioms-p f))
  :hints (("Goal" :use (field-axioms-p-fieldp))))

;; MAIN-2 from len-proots-bound (polynomials.lisp:484) and member-proots (:502)
(defthm MAIN-2
  (implies (and (fieldp f) (polyp p f)
                (monicp p f) (>= (degree p) 1))
           (and (<= (len (proots p f))
                    (degree p))
                (iff (member x (proots p f))
                     (prootp x p f))))
  :hints (("Goal" :use (len-proots-bound member-proots))))

;; MAIN-3 from prootp-min-poly (polynomials.lisp:630) via algebraic-witness-suff
(defthm MAIN-3
  (implies (and (extensionp e f)
                (feltp x e))
           (algebraic-witness x e f))
  :hints (("Goal" :use (prootp-min-poly
                        (:instance algebraic-witness-suff (p (min-poly x e f)))))))

;; MAIN-4 from all-embeddings (embeddings.lisp:644), len-embeddings (:653) and
;; sublistp-<=-len (groups/lists)
(defthm all-embeddingp-sublistp-embeddings
  (implies (and (extensionp e f) (extensionp k f) (all-embeddingp l e k f))
           (sublistp l (embeddings e k f)))
  :hints (("Goal" :in-theory (enable all-embeddings))))

(defthm MAIN-4
  (implies (and (extensionp e f) (extensionp k f)
                (dlistp l) (all-embeddingp l e k f))
           (<= (len l) (edegree e f)))
  :hints (("Goal" :use (len-embeddings
                        (:instance sublistp-<=-len (m (embeddings e k f)))))))
