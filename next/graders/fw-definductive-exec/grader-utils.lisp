; Grader utilities for fw-definductive-exec (copied from tool-definductive, plus GRADER-EXEC-CLEAN).
; Generic: does not include the model's book.  Every check records its result
; in the table GRADER-FAILS and prints a line "GRADER-PASS <label>" or
; "GRADER-FAIL <label>: <reason>", so that one failure does not mask others.
; GRADER-FINAL, at the end of each grader book, makes certification fail if
; any check failed.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "centaur/fty/portcullis" :dir :system)
(include-book "std/util/bstar" :dir :system)



(defun grader-msg-alist (args chars)
  (declare (xargs :mode :program))
  (if (or (atom args) (atom chars))
      nil
    (acons (car chars) (car args) (grader-msg-alist (cdr args) (cdr chars)))))

(defun grader-fail-events (label msg args)
  (declare (xargs :mode :program))
  `(progn (value-triple
           (cw "~%GRADER-FAIL ~x0: ~@1~%" ',label
               ',(cons msg (grader-msg-alist args '(#\0 #\1 #\2 #\3 #\4)))))
          (table grader-fails ',label t)))

(defun grader-pass-event (label)
  (declare (xargs :mode :program))
  `(value-triple (cw "~%GRADER-PASS ~x0~%" ',label)))

; Try some events; if they fail, record the failure (the events are then not
; admitted).

(defmacro grader-try (label &rest events)
  `(make-event
    '(:or (progn ,@events ,(grader-pass-event label))
          ,(grader-fail-events label "events failed: ~x0"
                               (list (if (and (consp (car events))
                                              (consp (cdar events)))
                                         (list (caar events) (cadar events))
                                       (car events)))))))

; Assert that a form (which may use STATE and (W STATE)) is non-nil.

(defmacro grader-assert (label form &optional (msg '"assertion failed"))
  `(make-event
    (if ,form
        ',(grader-pass-event label)
      ',(grader-fail-events label msg nil))))

; Alpha-equivalence of translated terms: variables (symbols in argument
; positions and lambda formals) may be renamed consistently.

(mutual-recursion
 (defun grader-alpha (a b alist)
   (declare (xargs :mode :program))
   (cond ((and (symbolp a) (symbolp b))
          (let ((pair (assoc-eq a alist)))
            (cond (pair (mv (eq (cdr pair) b) alist))
                  ((rassoc-eq b alist) (mv nil alist))
                  (t (mv t (acons a b alist))))))
         ((or (atom a) (atom b)) (mv (equal a b) alist))
         ((eq (car a) 'quote) (mv (equal a b) alist))
         ((and (consp (car a)) (consp (car b))) ; lambdas
          (mv-let (ok alist1)
            (grader-alpha-lst (cadr (car a)) (cadr (car b)) nil)
            (if (not ok)
                (mv nil alist)
              (mv-let (ok2 ign)
                (grader-alpha (caddr (car a)) (caddr (car b)) alist1)
                (declare (ignore ign))
                (if ok2
                    (grader-alpha-lst (cdr a) (cdr b) alist)
                  (mv nil alist))))))
         ((not (equal (car a) (car b))) (mv nil alist))
         (t (grader-alpha-lst (cdr a) (cdr b) alist))))
 (defun grader-alpha-lst (a b alist)
   (declare (xargs :mode :program))
   (cond ((or (atom a) (atom b)) (mv (and (atom a) (atom b)) alist))
         (t (mv-let (ok alist)
              (grader-alpha (car a) (car b) alist)
              (if ok (grader-alpha-lst (cdr a) (cdr b) alist) (mv nil alist)))))))

(defun grader-translate (term w)
  (declare (xargs :mode :program))
  (mv-let (ctx val)
    (translate-cmp term t t t 'grader w (default-state-vars nil))
    (if ctx (mv t nil) (mv nil val))))

; Check that the theorem NAME exists and its formula is exactly (the
; translation of) TERM.

(defun grader-formula-fn (label name term w)
  (declare (xargs :mode :program))
  (mv-let (erp tterm)
    (grader-translate term w)
    (let ((actual (and (symbolp name) (getpropc name 'theorem nil w))))
      (cond (erp (grader-fail-events label "expected statement ~x0 does not translate" (list term)))
            ((null actual) (grader-fail-events label "theorem ~x0 does not exist" (list name)))
            ((equal actual tterm) (grader-pass-event label))
            (t (mv-let (ok ign)
                 (grader-alpha actual tterm nil)
                 (declare (ignore ign))
                 (grader-fail-events
                  label
                  (if ok
                      "formula of ~x0 is ~x1, which equals the expected ~x2 ONLY UP TO VARIABLE RENAMING"
                    "formula of ~x0 is ~x1, expected ~x2")
                  (list name actual tterm))))))))

(defmacro grader-formula (label name term)
  `(make-event (grader-formula-fn ',label ',name ',term (w state))))

; Formals of a function, or :none.

(defun grader-formals (fn w)
  (declare (xargs :mode :program))
  (getpropc fn 'formals :none w))

; A function of the given arity, or a macro (FTY accessors are macros for
; $inline functions).

(defun grader-callable (name arity w)
  (declare (xargs :mode :program))
  (or (and (function-symbolp name w) (equal (len (grader-formals name w)) arity))
      (and (getpropc name 'macro-body nil w) t)))

; Summary of an FTY flextypes table entry:
; (name (sumname recp (kind (field type) ...) ...) ...).

(defun grader-fields (fields)
  (declare (xargs :mode :program))
  (if (atom fields)
      nil
    (cons (list (cdr (assoc 'fty::name (cdr (car fields))))
                (cdr (assoc 'fty::type (cdr (car fields)))))
          (grader-fields (cdr fields)))))

(defun grader-prods (prods)
  (declare (xargs :mode :program))
  (if (atom prods)
      nil
    (cons (cons (cdr (assoc 'fty::kind (cdr (car prods))))
                (grader-fields (cdr (assoc 'fty::fields (cdr (car prods))))))
          (grader-prods (cdr prods)))))

(defun grader-sums (types)
  (declare (xargs :mode :program))
  (if (atom types)
      nil
    (cons (list* (cdr (assoc 'fty::name (cdr (car types))))
                 (grader-prods (cdr (assoc 'fty::prods (cdr (car types))))))
          (grader-sums (cdr types)))))

(defun grader-flextypes-entry (name w)
  (declare (xargs :mode :program))
  (cdr (assoc-eq name (table-alist 'fty::flextypes-table w))))

(defun grader-flextypes-summary (name w)
  (declare (xargs :mode :program))
  (let ((entry (grader-flextypes-entry name w)))
    (and entry
         (grader-sums (cdr (assoc 'fty::types (cdr entry)))))))

; The flexsum record of type TYPENAME inside flextypes entry NAME.

(defun grader-find-sum (typename types)
  (declare (xargs :mode :program))
  (cond ((atom types) nil)
        ((eq (cdr (assoc 'fty::name (cdr (car types)))) typename) (cdr (car types)))
        (t (grader-find-sum typename (cdr types)))))

(defun grader-sum (name typename w)
  (declare (xargs :mode :program))
  (grader-find-sum typename
                   (cdr (assoc 'fty::types (cdr (grader-flextypes-entry name w))))))

; Constraints of a constrained function, as a list of formulas.

(defun grader-constraints (fn w)
  (declare (xargs :mode :program))
  (mv-let (sym lst origins)
    (constraint-info fn w)
    (declare (ignore origins))
    (cond ((null sym) (list lst)) ; a defining axiom, not a constraint list
          ((unknown-constraints-p lst) :unknown)
          (t lst))))

(defun grader-translate-list (terms w)
  (declare (xargs :mode :program))
  (if (atom terms)
      nil
    (mv-let (erp tterm)
      (grader-translate (car terms) w)
      (cons (if erp :untranslatable tterm) (grader-translate-list (cdr terms) w)))))

(defun grader-set-equal (a b)
  (declare (xargs :mode :program))
  (and (subsetp-equal a b) (subsetp-equal b a)))

; Theory of the :definition runes, introduced between two labels, of functions
; whose names end in -VALIDP (used to fill the paper's elided hints).

(defun grader-validp-runes (runes)
  (declare (xargs :mode :program))
  (cond ((atom runes) nil)
        ((and (consp (car runes))
              (eq (car (car runes)) :definition)
              (let ((s (symbol-name (cadr (car runes)))))
                (and (>= (length s) 7)
                     (equal (subseq s (- (length s) 7) (length s)) "-VALIDP"))))
         (cons (car runes) (grader-validp-runes (cdr runes))))
        (t (grader-validp-runes (cdr runes)))))

(defmacro grader-validp-theory (name before after)
  `(make-event
    (let ((runes (grader-validp-runes
                  (set-difference-equal (universal-theory-fn ',after (w state))
                                        (universal-theory-fn ',before (w state))))))
      (list 'deftheory ',name (kwote runes)))))

(defun grader-induction-schemes (rules)
  (declare (xargs :mode :program))
  (if (atom rules)
      nil
    (cons (access induction-rule (car rules) :scheme)
          (grader-induction-schemes (cdr rules)))))

; Names of the theorems, among the :rewrite runes of theory THY, whose
; formulas mention all of FNS.

(defun grader-thms-mentioning (fns runes w)
  (declare (xargs :mode :program))
  (cond ((atom runes) nil)
        ((and (consp (car runes))
              (eq (car (car runes)) :rewrite)
              (let ((thm (getpropc (cadr (car runes)) 'theorem nil w)))
                (and thm (subsetp-eq fns (all-fnnames thm)))))
         (add-to-set-eq (cadr (car runes)) (grader-thms-mentioning fns (cdr runes) w)))
        (t (grader-thms-mentioning fns (cdr runes) w))))

; DEFTHM with a :use hint of instances of all the theorems of theory THY that
; mention FNS: the formals of PRED are instantiated with ACTUALS, and the one
; remaining free variable, if any, with EXTRA.

(defun grader-instances (thms pred actuals extra w)
  (declare (xargs :mode :program))
  (if (atom thms)
      nil
    (let* ((formals (grader-formals pred w))
           (vars (all-vars (getpropc (car thms) 'theorem nil w)))
           (others (set-difference-eq vars formals))
           (subst (append (and (true-listp formals)
                               (equal (len formals) (len actuals))
                               (pairlis$ formals (pairlis$ actuals nil)))
                          (and (equal (len others) 1)
                               (list (list (car others) extra))))))
      (cons (cons :instance (cons (car thms) subst))
            (grader-instances (cdr thms) pred actuals extra w)))))

(defmacro grader-defthm-using (name term thy fns pred actuals extra)
  `(make-event
    (let* ((thms (grader-thms-mentioning ',fns (theory-fn ',thy (w state)) (w state)))
           (insts (grader-instances thms ',pred ',actuals ',extra (w state))))
      (list 'defthm ',name ',term
            :hints (list (list "Goal" :use insts))
            :rule-classes nil))))

;; Executability: the functions reachable from the body of FN (FN's own
;; clique excluded) are all defined, executable functions: none is constrained
;; (encapsulated, e.g. a defun-sk witness), none is introduced by defchoose,
;; and none is non-executable (defun-sk predicates are defun-nx).  Returns the
;; list of offending functions.

(defun grader-bad-fn-p (fn w)
  (declare (xargs :mode :program))
  (or (getpropc fn 'constrainedp nil w)
      (getpropc fn 'defchoose-axiom nil w)
      (getpropc fn 'non-executablep nil w)))

(defun grader-exec-closure (todo seen bad fuel w)
  (declare (xargs :mode :program))
  (cond ((or (atom todo) (zp fuel)) bad)
        ((member-eq (car todo) seen)
         (grader-exec-closure (cdr todo) seen bad (1- fuel) w))
        (t (let* ((fn (car todo))
                  (body (getpropc fn 'unnormalized-body nil w))
                  (bad (if (grader-bad-fn-p fn w) (cons fn bad) bad)))
             (grader-exec-closure (append (and body (all-fnnames body)) (cdr todo))
                                  (cons fn seen) bad (1- fuel) w)))))

(defun grader-exec-clean (fn w)
  (declare (xargs :mode :program))
  (let ((body (getpropc fn 'unnormalized-body nil w)))
    (if (null body)
        (list :no-body fn)
      (grader-exec-closure (all-fnnames body)
                           (or (getpropc fn 'recursivep nil w) (list fn))
                           nil 100000 w))))

(defmacro grader-final ()
  '(make-event
    (let ((fails (strip-cars (table-alist 'grader-fails (w state)))))
      (if fails
          (er soft 'grader "GRADER: failed checks: ~x0" fails)
        (value '(value-triple (cw "~%GRADER-ALL-PASS~%")))))))
