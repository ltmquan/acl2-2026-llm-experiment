#!/bin/bash
# Assemble defs.lisp from verbatim line ranges of the authors' master files.
SRC=$1; OUT=$2
X=$SRC/extensions.lisp; V=$SRC/vectors.lisp; P=$SRC/polynomials.lisp; E=$SRC/embeddings.lisp
r() { echo ";; ---- verbatim: $(basename $1):$2-$3 ----"; sed -n "$2,$3p" $1; echo; }
{
cat <<'H'
;; Definitions for the "russinoff-fields" targets, extracted VERBATIM from
;; ACL2 master books/projects/fields/{extensions,vectors,polynomials,embeddings}.lisp
;; (David M. Russinoff).  All theorems have been removed; the only lemmas kept are
;; LOCAL ones needed to admit peval and factorization.  See README.md for deviations.
;; The DM package is defined by cert.acl2 (projects/numbers/portcullis).

(in-package "DM")
(include-book "projects/groups/groups" :dir :system)
(include-book "projects/linear/field" :dir :system)

H
r $X 34 79
r $X 178 229
r $X 259 486
r $X 493 527
r $X 650 740
r $X 831 847
r $X 923 925
r $X 1117 1117
r $X 3613 3619
r $X 3632 3638
r $X 3712 3715
r $V 284 288
r $P 22 25
cat <<'H'
;; ---- local lemma (authors' statement, extensions.lisp:1682) used by the peval termination hint ----
(local (defthmd len-pstrip
  (<= (len (pstrip x f)) (len x))))

H
r $P 62 70
r $P 174 176
cat <<'H'
;; ---- local lemmas for the termination proof of factorization (DEVIATION: the authors'
;; hint :use (reduciblep-product) is replaced; see README.md) ----
(local (defthm len-pstrip-linear
  (<= (len (pstrip x f)) (len x))
  :rule-classes :linear))

(local (defun faddl-induct (x y)
  (declare (xargs :measure (+ (len x) (len y))))
  (if (> (len x) (len y))
      (faddl-induct (cdr x) y)
    (if (> (len y) (len x))
        (faddl-induct x (cdr y))
      (if (consp x)
          (faddl-induct (cdr x) (cdr y))
        ())))))

(local (defthm len-faddl
  (equal (len (faddl x y f)) (max (len x) (len y)))
  :hints (("Goal" :induct (faddl-induct x y)))))

(local (defthm len-append-local
  (equal (len (append x y)) (+ (len x) (len y)))))

(local (defthm len-pshift
  (equal (len (pshift p k f)) (+ (len p) (nfix k)))))

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

(local (defthm len-padd-bound
  (<= (len (padd p q f)) (max (len p) (len q)))
  :hints (("Goal" :in-theory (enable padd)))
  :rule-classes nil))

(local (defthm len-monomial
  (equal (len (monomial c k f)) (1+ (nfix k)))))

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

(local (defthm len-pquot-bound
  (implies (and (polyp d f) (> (degree d) 0) (>= (degree p) 2))
           (< (len (pquot p d f)) (len p)))
  :hints (("Goal" :in-theory (enable pquot polyp)
                  :use ((:instance len-pdivide-quot-bound (x p) (y d)))))))

;; ---- verbatim: polynomials.lisp:290-296, except the termination hint ----
(defun factorization (p f)
  (declare (xargs :measure (len p) :hints (("Goal" :in-theory (enable reduciblep)))))
  (if (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 2) (reduciblep p f))
      (let ((d (pfactor p f)))
        (append (factorization d f)
                (factorization (pquot p d f) f)))
    (list p)))

H
r $P 467 478
cat <<'H'
;; ---- embeddings.lisp needs the well-founded relation l< ----
(local (include-book "ordinals/lexicographic-book" :dir :system))

H
r $E 41 68
cat <<'H'
;;----------------------------------------------------------------------------------------------------------
;; NEW (not in the authors' files): neutral predicates used by MAIN-3 and MAIN-4.
;;----------------------------------------------------------------------------------------------------------

;; x is a root of the lift to e of some monic irreducible polynomial p over f with
;; 1 <= degree(p) <= [e:f].  (Neutral existential form of polynomials.lisp:630, prootp-min-poly.)

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
H
} > $OUT
