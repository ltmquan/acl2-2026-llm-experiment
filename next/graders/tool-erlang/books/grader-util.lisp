; tool-erlang grader: helpers to find the paper's names in whatever package the model used.
; (Not a requirement by itself.)
(in-package "ACL2")

(defun grader-pkgs (pkgs)
  (declare (xargs :mode :program))
  (cond ((endp pkgs) nil)
        ((member-equal (car pkgs) '("KEYWORD" "ACL2-INPUT-CHANNEL" "ACL2-OUTPUT-CHANNEL"))
         (grader-pkgs (cdr pkgs)))
        (t (cons (car pkgs) (grader-pkgs (cdr pkgs))))))

(defun grader-syms (name pkgs)
  ;; the symbols named NAME in each package, without duplicates
  (declare (xargs :mode :program))
  (if (endp pkgs) nil
    (add-to-set-eq (intern$ name (car pkgs)) (grader-syms name (cdr pkgs)))))

(defun grader-fns1 (syms w)
  (declare (xargs :mode :program))
  (cond ((endp syms) nil)
        ((function-symbolp (car syms) w) (cons (car syms) (grader-fns1 (cdr syms) w)))
        (t (grader-fns1 (cdr syms) w))))

(defun grader-fns (name w)
  ;; all function symbols named NAME (any package)
  (declare (xargs :mode :program))
  (let ((syms (grader-syms name (grader-pkgs (strip-cars (global-val 'known-package-alist w))))))
    (grader-fns1 syms w)))

(defun grader-macros1 (syms w)
  (declare (xargs :mode :program))
  (cond ((endp syms) nil)
        ((getpropc (car syms) 'macro-body nil w) (cons (car syms) (grader-macros1 (cdr syms) w)))
        (t (grader-macros1 (cdr syms) w))))

(defun grader-macros (name w)
  (declare (xargs :mode :program))
  (grader-macros1 (grader-syms name (grader-pkgs (strip-cars (global-val 'known-package-alist w)))) w))

(defun grader-logic-fn (name w)
  ;; the unique logic-mode function named NAME, or nil
  (declare (xargs :mode :program))
  (let ((fns (grader-fns name w)))
    (and (consp fns) (null (cdr fns))
         (not (eq (symbol-class (car fns) w) :program))
         (car fns))))

(defun grader-all-logic-fns (names w)
  (declare (xargs :mode :program))
  (or (endp names) (and (grader-logic-fn (car names) w) (grader-all-logic-fns (cdr names) w))))

(defun grader-missing (names w)
  (declare (xargs :mode :program))
  (cond ((endp names) nil)
        ((grader-logic-fn (car names) w) (grader-missing (cdr names) w))
        (t (cons (car names) (grader-missing (cdr names) w)))))

; (grader-require-fns ("NAME" ...)) : every name is a unique logic-mode function
(defmacro grader-require-fns (names)
  `(assert-event (grader-all-logic-fns ',names (w state))
                 :msg (msg "Missing or non-logic-mode (or ambiguous) function among ~x0: ~x1"
                           ',names (grader-missing ',names (w state)))))

(defun grader-thms1 (syms w)
  (declare (xargs :mode :program))
  (cond ((endp syms) nil)
        ((getpropc (car syms) 'theorem nil w) (cons (car syms) (grader-thms1 (cdr syms) w)))
        (t (grader-thms1 (cdr syms) w))))

(defun grader-thms (name w)
  ;; all theorem names (defthm/defthmd) named NAME, any package
  (declare (xargs :mode :program))
  (grader-thms1 (grader-syms name (grader-pkgs (strip-cars (global-val 'known-package-alist w)))) w))

; (grader-require-thms ("NAME" ...)) : every name is a theorem (in exactly one package)
(defmacro grader-require-thms (names)
  `(assert-event (grader-all-thms ',names (w state))
                 :msg (msg "Missing (or ambiguous) theorem among ~x0" ',names)))

(defun grader-all-thms (names w)
  (declare (xargs :mode :program))
  (or (endp names)
      (and (equal (len (grader-thms (car names) w)) 1)
           (grader-all-thms (cdr names) w))))

(defun grader-print-thms (names w)
  ;; print each named theorem's formula, for the person checking CHECKLIST items
  (declare (xargs :mode :program))
  (if (endp names) nil
    (prog2$ (cw "~%GRADER-THEOREM ~s0:~%~x1~%" (car names)
                (getpropc (car (grader-thms (car names) w)) 'theorem nil w))
            (grader-print-thms (cdr names) w))))
