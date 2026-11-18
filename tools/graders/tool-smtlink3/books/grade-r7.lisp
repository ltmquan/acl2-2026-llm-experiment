; tool-smtlink3 grader, requirement 7 (supplementary check; grade.py also checks examples.lisp).
; The alist goal of Section 5.7, verbatim, proved with a :smtlink hint whose translation theory
; contains the two translation theorems the paper names.  The paper does not give the full hint, so
; we try (a) minimal-theory plus the two theorems and (b) the current theory plus the two theorems,
; each on "Goal" (the goal is trivial for ACL2 itself, so the hint must fire before simplification;
; grade.py also requires that Z3 was called while this book was certified).
; The function names int-sym-alist-p, int-sym-array-select/store, int-sym-array-from-al are the
; paper's, read in the ACL2 package.
(in-package "ACL2")
(include-book "grader-common" :ttags :all)

(make-event
 '(:or
   (defthm grader-alist-to-array
     (implies (and (integerp k1)
                   (integerp k2)
                   (symbolp v1)
                   (symbolp v2)
                   (int-sym-alist-p al))
              (equal (assoc-equal k1
                                  (cons (cons k1 v1)
                                        (cons (cons k2 v2) al)))
                     (cons k1 v1)))
     :hints (("Goal" :smtlink
              (:translation-theory
               (union-theories
                (theory 'minimal-theory)
                '(int-sym-top-down-translation-of-assoc-equal
                  int-sym-top-down-translation-of-acons))))))
   (defthm grader-alist-to-array
     (implies (and (integerp k1)
                   (integerp k2)
                   (symbolp v1)
                   (symbolp v2)
                   (int-sym-alist-p al))
              (equal (assoc-equal k1
                                  (cons (cons k1 v1)
                                        (cons (cons k2 v2) al)))
                     (cons k1 v1)))
     :hints (("Goal" :smtlink
              (:translation-theory
               (enable int-sym-top-down-translation-of-assoc-equal
                       int-sym-top-down-translation-of-acons)))))))
