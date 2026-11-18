; Smtlink 3 (reimplementation) -- the SMT theory of real arithmetic
;
; Section 5.4 of the paper: an encapsulation that constrains a clique of
; functions representing the SMT real theory.  The trusted clause processor
; translates these function symbols to the corresponding SMT-LIB operators
; (+, -, *, /, <).  The specialization theorems (disabled) and the
; return-type theorems form translation theories that the user can give to
; the :translation-theory argument of the :smtlink hint.

(in-package "SMT")

(encapsulate
  (((rational-+ * *) => *)
   ((rational-- *) => *)
   ((rational-* * *) => *)
   ((rational-/ *) => *)
   ((rational-< * *) => *))

  (local
   (defun rational-+ (x y)
     (binary-+ x y)))

  (local
   (defun rational-- (x)
     (unary-- x)))

  (local
   (defun rational-* (x y)
     (binary-* x y)))

  (local
   (defun rational-/ (x)
     (unary-/ x)))

  (local
   (defun rational-< (x y)
     (< x y)))

  (defthm return-of-rational-+
    (implies (and (rationalp x)
                  (rationalp y))
             (rationalp (rational-+ x y)))
    :rule-classes (:rewrite :type-prescription))

  (defthm return-of-rational--
    (implies (rationalp x)
             (rationalp (rational-- x)))
    :rule-classes (:rewrite :type-prescription))

  (defthm return-of-rational-*
    (implies (and (rationalp x)
                  (rationalp y))
             (rationalp (rational-* x y)))
    :rule-classes (:rewrite :type-prescription))

  (defthm return-of-rational-/
    (implies (rationalp x)
             (rationalp (rational-/ x)))
    :rule-classes (:rewrite :type-prescription))

  (defthm return-of-rational-<
    (implies (and (rationalp x)
                  (rationalp y))
             (booleanp (rational-< x y)))
    :rule-classes (:rewrite :type-prescription))

  (defthmd specialize-binary-rational-operators
    (implies (and (rationalp x)
                  (rationalp y))
             (and (equal (binary-+ x y)
                         (rational-+ x y))
                  (equal (binary-* x y)
                         (rational-* x y))
                  (equal (< x y)
                         (rational-< x y)))))

  (defthmd specialize-unary-rational--
    (implies (rationalp x)
             (equal (unary-- x)
                    (rational-- x))))

  (defthmd specialize-unary-rational-/
    (implies (and (rationalp x)
                  (not (= x 0)))
             (equal (unary-/ x)
                    (rational-/ x)))))

; A convenient name for the translation theory of the paper's running
; example.

(defconst *rational-translation-rules*
  '(return-of-rational-+
    return-of-rational--
    return-of-rational-*
    return-of-rational-/
    return-of-rational-<
    specialize-binary-rational-operators
    specialize-unary-rational--
    specialize-unary-rational-/))
