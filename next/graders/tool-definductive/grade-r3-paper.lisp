; Grader book for tool-definductive, requirement 3 (paper part):
; the paper's Section 5 theorems, with the hints the paper shows, on the
; paper's examples defined by the model's tool (grade-r2).  Where the paper
; elides parts of a hint ("...") or of a definition, or shows no hint, the
; fill used here is marked FILL and listed in NOTES.md.  Names of theorems that
; the paper gives twice (r*-of-f) or that would clash are suffixed -paper/-fi.

(in-package "ACL2")

(include-book "grade-r2")

; FILL: the elided "..." in enable lists includes the definitions of the
; generated validity functions (any generated function whose name ends in
; -VALIDP), so that implementations that split validity into helper functions
; (as the authors' implementation does) are not penalized.
(grader-validp-theory grader-rtc-validp grader-before-rtc grader-after-rtc)
(grader-validp-theory grader-eo-validp grader-before-eo grader-after-eo)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Section 5.1

; "proves by rewriting with r*-base and r*-trans"
; FILL: enable r*-base and r*-trans (in case the tool disables them).
(grader-try r3p-trans-base-right
  (defthm trans-base-right (implies (and (r* x y) (r y z)) (r* x z))
    :hints (("Goal" :in-theory (enable r*-base r*-trans)))))

; Footnote 11: "needs a :use hint with r*-base".
(grader-try r3p-trans-base-left
  (defthm trans-base-left (implies (and (r x y) (r* y z)) (r* x z))
    :hints (("Goal" :use r*-base :in-theory (enable r*-trans)))))

; Section 5.4: "given ... a function f that preserves r".
; FILL: f is introduced by an encapsulate whose only constraint is r-of-f.
(encapsulate
  (((f *) => *))
  (local (defun f (x) x))
  (defthm r-of-f (implies (r x y) (r (f x) (f y)))))

; Section 5.5 (proved first, and with :rule-classes nil, so that the two
; proofs of r*-of-f are independent).
(grader-try r3p-r*-of-f-fi
  (defthm r*-of-f-fi (implies (r* a b) (r* (f a) (f b)))
    :hints (("Goal"
             :use (:functional-instance r*-alt-when-r*
                                        (r*-alt (lambda (a b) (r* (f a) (f b)))))
             :in-theory (enable r*-base r*-refl r*-trans)))
    :rule-classes nil))

; Section 5.4.
; FILL for "...": r-of-f, r*-when-proof-validp, and the validity definitions.
(grader-try r3p-r*-of-f
  (defthm r*-of-f-paper (implies (r* a b) (r* (f a) (f b)))
    :hints (("Goal" :induct (r* a b) ; inference rule induction
             :in-theory (union-theories
                         (enable r*-base r*-refl r*-trans r-of-f r*-when-proof-validp)
                         (theory 'grader-rtc-validp))
             :expand ((r* a b) (r*-proof-validp (r*-proof a b) a b))))
    :rule-classes nil))

; Section 5.1, even-and-odd: "proves from odd-from-even and even-from-odd".
; FILL: :use of the two rules (even-from-odd instantiated at (1+ n)).
(grader-try r3p-even-add-2
  (defthm even-add-2 (implies (even n) (even (+ 2 n)))
    :hints (("Goal" :use (odd-from-even (:instance even-from-odd (n (1+ n))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Section 5.3 (before 5.2 here, because natp-when-even-proof-validp is used to
; fill the elided hints of even-of-pred-when-odd).
; FILL: the paper shows no hints; the validity definitions are enabled.

(grader-try r3p-natp-when-even/odd-proof-validp
  (defthm-even-proof-validp-clique-flag
    (defthm natp-when-even-proof-validp
      (implies (even-proof-validp proof n) (natp n))
      :flag even-proof-validp)
    (defthm natp-when-odd-proof-validp
      (implies (odd-proof-validp proof n) (natp n))
      :flag odd-proof-validp)
    :hints (("Goal" :in-theory (union-theories (current-theory :here)
                                               (theory 'grader-eo-validp))))))

; "from which it follows, opening the definitions of even and odd"
(grader-try r3p-natp-when-even/odd
  (defthm natp-when-even/odd (implies (or (even n) (odd n)) (natp n))
    :hints (("Goal" :in-theory (enable even odd natp-when-even-proof-validp
                                       natp-when-odd-proof-validp)))))

; Section 5.1 (moved after 5.3: the base case needs natp-when-even/odd).
; "proves by induction on m, corresponding to the composition of m
; applications of even-add-2".
; FILL: the induction scheme and the :use of even-add-2.
(defun grader-dec-induct (m)
  (if (zp m) m (grader-dec-induct (1- m))))

(grader-try r3p-even-add-double
  (defthm even-add-double (implies (and (natp m) (even n)) (even (+ (* 2 m) n)))
    :hints (("Goal" :induct (grader-dec-induct m))
            '(:use (:instance even-add-2 (n (+ (* 2 (1- m)) n)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Section 5.2

; FILL: the "..." result in the impossible branch; :verify-guards nil, because
; the guards of the paper's definitions need return-type theorems that the
; paper omits.
(mutual-recursion
 (defun proof-for-even (n) ; proof tree that n is even
   (declare (xargs :guard (and (natp n) (evenp n))))
   (declare (xargs :verify-guards nil))
   (b* (((when (zp n)) (even-proof-zero)) ; base case
        (odd-proof (proof-for-odd (1- n)))) ; proof tree that n-1 is odd
     (make-even-proof-from-odd :n (1- n) :premise1-proof odd-proof)))
 (defun proof-for-odd (n) ; proof tree that n is odd
   (declare (xargs :guard (and (natp n) (oddp n))))
   (declare (xargs :verify-guards nil))
   (b* (((when (zp n)) (make-odd-proof-from-even :n 0 :premise1-proof (even-proof-zero))) ; impossible -- result is irrelevant
        (even-proof (proof-for-even (1- n)))) ; proof tree that n-1 is even
     (make-odd-proof-from-even :n (1- n) :premise1-proof even-proof))))

; FILL: the flag function (the paper only uses its macro), return types, and
; an arithmetic lemma.
(make-flag proof-for-even/odd-flag proof-for-even)

(defthm grader-proofp-of-proof-for-even/odd
  (and (even-proofp (proof-for-even n))
       (odd-proofp (proof-for-odd n)))
  :hints (("Goal" :expand ((proof-for-even n) (proof-for-odd n)))))

(include-book "grader-arith") ; grader-arith-lemma

(grader-try r3p-proof-for-even/odd
  (defthm-proof-for-even/odd-flag ; flag event for the mutual recursion above
    (defthm even-proof-validp-of-proof-for-even
      (implies (and (natp n) (evenp n)) (even-proof-validp (proof-for-even n) n))
      :flag proof-for-even)
    (defthm odd-proof-validp-of-proof-for-odd
      (implies (and (natp n) (oddp n)) (odd-proof-validp (proof-for-odd n) n))
      :flag proof-for-odd)
    :hints (("Goal" :in-theory (union-theories
                                (enable proof-for-even proof-for-odd grader-arith-lemma)
                                (theory 'grader-eo-validp))))))

(grader-try r3p-even-when-evenp
  (defthm even-when-evenp (implies (and (natp n) (evenp n)) (even n))
    :hints
    (("Goal" :use (:instance even-when-proof-validp (proof (proof-for-even n)))))))

(grader-try r3p-odd-when-oddp
  (defthm odd-when-oddp (implies (and (natp n) (oddp n)) (odd n))
    :hints
    (("Goal" :use (:instance odd-when-proof-validp (proof (proof-for-odd n)))))))

; FILL for the two "...": expand the validity of the witness, enable odd, the
; validity definitions and natp-when-even-proof-validp.
(grader-try r3p-even-of-pred-when-odd
  (defthm even-of-pred-when-odd (implies (odd n) (even (1- n)))
    :hints (("Goal"
             :use (:instance even-when-proof-validp
                             (proof (odd-proof-from-even->premise1-proof (odd-proof n)))
                             (n (1- n)))
             :expand ((odd-proof-validp (odd-proof n) n))
             :in-theory (union-theories (enable odd natp-when-even-proof-validp)
                                        (theory 'grader-eo-validp))))))

(grader-final)
