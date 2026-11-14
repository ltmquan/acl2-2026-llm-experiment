; Smtlink 3 (reimplementation) -- examples from the paper

(in-package "ACL2")
(include-book "smtlink" :ttags ((:smtlink)))
(include-book "std/testing/must-fail" :dir :system)

; ----------------------------------------------------------------------
; Section 5: the running example (a system of nonlinear inequalities),
; with the translation theory of Section 5.4 (the RATIONAL-+, RATIONAL-*,
; ... encapsulate is in smt-theory.lisp).

(defun x^2-y^2 (x y)
  (- (* x x) (* y y)))

(defthm poly-ineq-example
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (<= (+ (* (/ 9 8) x x) (* y y)) 1)
                (<= (x^2-y^2 x y) 1))
           (< y
              (- (* 3 (- x (/ 17 8)) (- x (/ 17 8)))
                 3)))
  :hints (("Goal''" :smtlink
           (:translation-theory
            (union-theories
             (theory 'minimal-theory)
             '(smt::return-of-rational-+
               smt::return-of-rational--
               smt::return-of-rational-*
               smt::return-of-rational-/
               smt::return-of-rational-<
               smt::specialize-binary-rational-operators
               smt::specialize-unary-rational--
               smt::specialize-unary-rational-/))))))

; The same goal with its hypotheses permuted: type inference treats each
; disjunct of the clause separately, so Smtlink does not depend on the order
; of the hypotheses.

(defthm poly-ineq-example-permuted
  (implies (and (<= (x^2-y^2 x y) 1)
                (<= (+ (* (/ 9 8) x x) (* y y)) 1)
                (real/rationalp y)
                (real/rationalp x))
           (< y
              (- (* 3 (- x (/ 17 8)) (- x (/ 17 8)))
                 3)))
  :hints (("Goal''" :smtlink
           (:translation-theory
            (union-theories
             (theory 'minimal-theory)
             '(smt::return-of-rational-+
               smt::return-of-rational--
               smt::return-of-rational-*
               smt::return-of-rational-/
               smt::return-of-rational-<
               smt::specialize-binary-rational-operators
               smt::specialize-unary-rational--
               smt::specialize-unary-rational-/))))))

; A false variant of the goal: (x, y) = (0, 0) satisfies the hypotheses,
; but 0 < 3 (0 - 17/8)^2 - 30 is false.  Z3 answers sat, so the proof fails.

(must-fail
 (defthm poly-ineq-example-false
   (implies (and (real/rationalp x)
                 (real/rationalp y)
                 (<= (+ (* (/ 9 8) x x) (* y y)) 1)
                 (<= (x^2-y^2 x y) 1))
            (< y
               (- (* 3 (- x (/ 17 8)) (- x (/ 17 8)))
                  30)))
   :hints (("Goal''" :smtlink
            (:translation-theory
             (union-theories
              (theory 'minimal-theory)
              '(smt::return-of-rational-+
                smt::return-of-rational--
                smt::return-of-rational-*
                smt::return-of-rational-/
                smt::return-of-rational-<
                smt::specialize-binary-rational-operators
                smt::specialize-unary-rational--
                smt::specialize-unary-rational-/)))))))

; ----------------------------------------------------------------------
; Section 4.1: a type-terse goal.  There is no type hypothesis for X; type
; inference (using the rewriter) infers it from (= x (* 2 y)).

(defun foo (x y)
  (<= (* y y) (* x x)))

(defthm type-terse-example
  (implies (and (integerp y)
                (= x (* 2 y)))
           (foo x y))
  :hints (("Goal" :smtlink
           (:translation-theory
            (union-theories
             (theory 'minimal-theory)
             (cons 'foo smt::*rational-translation-rules*))))))

; ----------------------------------------------------------------------
; Section 4.1: the :hypothesize hint.  Type inference cannot see that x is
; rational (it would have to open the definition of POS-RATP in a
; hypothesis), so the user adds the hypothesis (rationalp x).  Smtlink
; generates the subgoal that the negation of the goal implies (rationalp x),
; which ACL2 proves by opening POS-RATP.

(defun pos-ratp (x)
  (and (rationalp x) (< 0 x)))

(defthm hypothesize-example
  (implies (and (pos-ratp x)
                (rationalp y))
           (<= (* 2 x y) (+ (* x x) (* y y))))
  :hints (("Goal" :smtlink
           (:hypothesize ((rationalp x))
            :translation-theory
            (union-theories (theory 'minimal-theory)
                            smt::*rational-translation-rules*)))))

; ----------------------------------------------------------------------
; Section 5.7: from alists to arrays.
;
; A simple theory of alists from integers to symbols, and of arrays from
; integers to "int-sym pairs" (a cons of an integer and a symbol, or nil).

(defun int-sym-alist-p (x)
  (if (atom x)
      (null x)
    (and (consp (car x))
         (integerp (caar x))
         (symbolp (cdar x))
         (int-sym-alist-p (cdr x)))))

(defun int-sym-pair-p (x)
  (or (null x)
      (and (consp x)
           (integerp (car x))
           (symbolp (cdr x)))))

(defthm int-sym-pair-p-of-cons
  (implies (and (integerp k)
                (symbolp v))
           (int-sym-pair-p (cons k v))))

(defun int-sym-array-p (x)
  (if (atom x)
      (null x)
    (and (consp (car x))
         (integerp (caar x))
         (int-sym-pair-p (cdar x))
         (int-sym-array-p (cdr x)))))

(defun int-sym-array-select (a k)
  (cdr (assoc-equal k a)))

(defun int-sym-array-store (a k v)
  (cons (cons k v) a))

(defun int-sym-array-from-al (al)
  (if (atom al)
      nil
    (cons (cons (caar al) (car al))
          (int-sym-array-from-al (cdr al)))))

(defthm int-sym-array-p-of-int-sym-array-from-al
  (implies (int-sym-alist-p al)
           (int-sym-array-p (int-sym-array-from-al al))))

; Registering the array theory proves the read-over-write and typing
; theorems that justify translating INT-SYM-ARRAY-SELECT and
; INT-SYM-ARRAY-STORE to the SMT-LIB select and store.

(smt::def-smt-array :recognizer int-sym-array-p
                    :key-p integerp
                    :val-p int-sym-pair-p
                    :select int-sym-array-select
                    :store int-sym-array-store)

(in-theory (disable int-sym-array-select int-sym-array-store
                    int-sym-array-from-al))

; The translation theory: the two translation theorems of Section 5.7.

(defthmd int-sym-top-down-translation-of-assoc-equal
  (implies (int-sym-alist-p al)
           (equal (assoc-equal k al)
                  (int-sym-array-select (int-sym-array-from-al al)
                                        k)))
  :hints (("Goal" :in-theory (enable int-sym-array-select
                                     int-sym-array-from-al))))

(defthmd int-sym-top-down-translation-of-acons
  (implies (and (integerp k)
                (symbolp v))
           (equal (int-sym-array-from-al (cons (cons k v) al))
                  (int-sym-array-store (int-sym-array-from-al al)
                                       k
                                       (cons k v))))
  :hints (("Goal" :in-theory (enable int-sym-array-store
                                     int-sym-array-from-al))))

(defthm alist-to-array-example
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
               int-sym-top-down-translation-of-acons))
            :types (symbolp int-sym-alist-p int-sym-pair-p
                            int-sym-array-p)))))
