; Grader helper for fw-multisets (written before any run).  Does not include
; the model's books.  All checks print "GRADER-OK <what>" or
; "GRADER-FAIL <what>" lines, which grade.py collects; a failed check does not
; stop certification, so one failure does not mask the others.

(in-package "ACL2")

(program)
(set-state-ok t)

; ---------------------------------------------------------------- theorems
; Definition runes of the given function symbols (the model's required
; functions), disabled while our statements are proved, so that a statement
; passes only if the model's own rules prove it.
(defun gr-def-runes (fns wrld)
  (cond ((endp fns) nil)
        ((and (function-symbolp (car fns) wrld)
              (getpropc (car fns) 'def-bodies nil wrld))
         (cons (list :definition (car fns)) (gr-def-runes (cdr fns) wrld)))
        (t (gr-def-runes (cdr fns) wrld))))

(defmacro gr-step-limit () 2000000)
(defmacro gr-use-step-limit () 300000)

; Theorems of the model (names in package MSET), with the MSET functions their
; formulas mention: a list of (name . fns), collected from the world.
(defun gr-mset-fns (fns)
  (cond ((endp fns) nil)
        ((equal (symbol-package-name (car fns)) "MSET")
         (cons (car fns) (gr-mset-fns (cdr fns))))
        (t (gr-mset-fns (cdr fns)))))

(defun gr-collect-thms (wrld acc)
  (cond ((endp wrld) acc)
        ((and (eq (cadr (car wrld)) 'theorem)
              (symbolp (car (car wrld)))
              (equal (symbol-package-name (car (car wrld))) "MSET")
              (not (assoc-eq (car (car wrld)) acc)))
         (gr-collect-thms (cdr wrld)
                          (cons (cons (car (car wrld)) (gr-mset-fns (all-fnnames (cddr (car wrld)))))
                                acc)))
        (t (gr-collect-thms (cdr wrld) acc))))

(defun gr-candidates (fns thms)
  ;; model theorems whose formula mentions every MSET function of our statement
  (cond ((endp thms) nil)
        ((subsetp-eq fns (cdr (car thms)))
         (cons (car (car thms)) (gr-candidates fns (cdr thms))))
        (t (gr-candidates fns (cdr thms)))))

(defun gr-theory-off ()
  '(set-difference-theories (current-theory :here) (theory 'gr-model-defs)))

(defun gr-attempt (name stmt hints label)
  `(progn (with-prover-step-limit ,(if (assoc-keyword :use (cdar hints)) '(gr-use-step-limit) '(gr-step-limit))
            (defthm ,name ,stmt :rule-classes nil :hints ,hints))
          (value-triple (cw "GRADER-OK ~x0 (~s1) GRADEREND~%" ',name ,label))))

(defun gr-by-attempts (name stmt cands label)
  (if (endp cands)
      nil
    (cons (gr-attempt name stmt `(("Goal" :by ,(car cands)))
                      (concatenate 'string label ", :by " (symbol-name (car cands))))
          (gr-by-attempts name stmt (cdr cands) label))))

(defun gr-use-attempts (name stmt cands label)
  (if (endp cands)
      nil
    (cons (gr-attempt name stmt `(("Goal" :use ,(car cands) :do-not-induct t :in-theory ,(gr-theory-off)))
                      (concatenate 'string label ", :use " (symbol-name (car cands))))
          (gr-use-attempts name stmt (cdr cands) label))))

; Attempts for one statement, in order (the first success wins):
;   1. :by the lemma of the required name (count-of-X), when given;
;   2. the model's rules, with the model's definitions of the required
;      functions disabled and no induction;
;   3. :by each model theorem mentioning the statement's MSET functions;
;   4. :use each such theorem (or the required lemma), definitions disabled,
;      no induction.
(defun gr-attempts (name stmt by cands label)
  (append (and by (gr-by-attempts name stmt (list by) label))
          (list (gr-attempt name stmt `(("Goal" :do-not-induct t :in-theory ,(gr-theory-off)))
                            (concatenate 'string label ", model's rules")))
          (gr-by-attempts name stmt (remove-eq by cands) label)
          (gr-use-attempts name stmt (if by (cons by (remove-eq by cands)) cands) label)))

(defun gr-thm-fn (name stmt hyps by state)
  (let ((stmt2 (and hyps `(implies (and ,@hyps) ,stmt)))
        (thms (gr-collect-thms (w state) nil)))
    (mv-let (erp tstmt state)
      (translate stmt t nil t 'grader (w state) state)
      (if erp
          (value `(value-triple
                   (cw "GRADER-FAIL ~x0: the statement does not translate (missing function?) GRADEREND~%"
                       ',name)))
        (let ((cands (gr-candidates (gr-mset-fns (all-fnnames tstmt)) thms)))
          (value
           `(:or ,@(gr-attempts name stmt by cands "as stated")
                 ,@(and hyps (gr-attempts name stmt2 by cands "with hypotheses"))
                 (value-triple (cw "GRADER-FAIL ~x0: not proved GRADEREND~%" ',name)))))))))

(defmacro gr-thm (name stmt &key hyps by)
  `(make-event (gr-thm-fn ',name ',stmt ',hyps ',by state)))

; A required theorem name exists (used for the count-of-X names the prompt fixes)
(defmacro gr-name-exists (name)
  `(make-event
    (if (formula ',name nil (w state))
        '(value-triple (cw "GRADER-OK ~x0 exists GRADEREND~%" ',name))
      '(value-triple (cw "GRADER-FAIL ~x0: no theorem with this name GRADEREND~%" ',name)))))

; Rule classes: the theorem has a :rewrite rule
(defmacro gr-rewrite-rule (name)
  `(make-event
    (if (getpropc ',name 'runic-mapping-pairs nil (w state))
        (if (assoc-eq :rewrite (strip-cdrs (getpropc ',name 'runic-mapping-pairs nil (w state))))
            '(value-triple (cw "GRADER-OK ~x0 is a rewrite rule GRADEREND~%" ',name))
          '(value-triple (cw "GRADER-FAIL ~x0: not a rewrite rule GRADEREND~%" ',name)))
      '(value-triple (cw "GRADER-FAIL ~x0: no rules GRADEREND~%" ',name)))))

; ---------------------------------------------------------------- guards
(defun gr-guards-fn (fns wrld)
  (if (endp fns)
      nil
    (let ((f (car fns)))
      (cons (cond ((not (function-symbolp f wrld))
                   (msg "GRADER-FAIL guard ~x0: not a function GRADEREND~%" f))
                  ((eq (symbol-class f wrld) :common-lisp-compliant)
                   (msg "GRADER-OK guard ~x0 verified GRADEREND~%" f))
                  (t (msg "GRADER-FAIL guard ~x0: guards not verified (~x1) GRADEREND~%" f (symbol-class f wrld))))
            (gr-guards-fn (cdr fns) wrld)))))

(defun gr-print-msgs (msgs)
  (if (endp msgs)
      nil
    (prog2$ (cw "~@0" (car msgs)) (gr-print-msgs (cdr msgs)))))

(defmacro gr-guards (fns)
  `(make-event
    (prog2$ (gr-print-msgs (gr-guards-fn ',fns (w state)))
            '(value-triple :guards-checked))))

; ---------------------------------------------------------------- bequiv
; (f . positions): f respects EQUIV in argument position i (1-based), with
; result equivalence EQUAL or EQUIV.
(defun gr-geneqv-has (geneqv equiv)
  (and (consp geneqv)
       (or (eq (cadr (car geneqv)) equiv)
           (gr-geneqv-has (cdr geneqv) equiv))))

(defun gr-cong-at (congs i equiv results)
  ;; congs: the 'congruences property, a list of (result-equiv . geneqv-list)
  (and (consp congs)
       (or (and (member-eq (car (car congs)) results)
                (gr-geneqv-has (nth (1- i) (cdr (car congs))) equiv))
           (gr-cong-at (cdr congs) i equiv results))))

(defun gr-congs-fn1 (f positions equiv wrld)
  (if (endp positions)
      nil
    (cons (if (gr-cong-at (getpropc f 'congruences nil wrld) (car positions) equiv
                          (list 'equal equiv))
              (msg "GRADER-OK congruence ~x0 respects ~x1 in argument ~x2 GRADEREND~%" f equiv (car positions))
            (msg "GRADER-FAIL congruence ~x0 does not respect ~x1 in argument ~x2 (no congruence rule) GRADEREND~%"
                 f equiv (car positions)))
          (gr-congs-fn1 f (cdr positions) equiv wrld))))

(defun gr-congs-fn (specs equiv wrld)
  (if (endp specs)
      nil
    (let ((f (car (car specs))))
      (append
       (gr-congs-fn1 f (cdr (car specs)) equiv wrld)
       (gr-congs-fn (cdr specs) equiv wrld)))))

(defmacro gr-congruences (equiv specs)
  `(make-event
    (prog2$
     (if (equivalence-relationp ',equiv (w state))
         (cw "GRADER-OK ~x0 is an equivalence relation GRADEREND~%" ',equiv)
       (cw "GRADER-FAIL ~x0 is not an equivalence relation (no defequiv) GRADEREND~%" ',equiv))
     (prog2$ (gr-print-msgs (gr-congs-fn ',specs ',equiv (w state)))
             '(value-triple :congruences-checked)))))

; ---------------------------------------------------------------- no list conversion
; Functions reachable from ROOTS through the bodies of functions in package
; PKG (the model's own functions); library functions are not entered.
(defun gr-reach (todo pkg seen wrld fuel)
  (declare (xargs :mode :program))
  (cond ((or (endp todo) (zp fuel)) seen)
        ((member-eq (car todo) seen) (gr-reach (cdr todo) pkg seen wrld fuel))
        (t (let* ((f (car todo))
                  (seen (cons f seen))
                  (body (and (equal (symbol-package-name f) pkg)
                             (getpropc f 'unnormalized-body nil wrld)))
                  (callees (and body (all-fnnames body))))
             (gr-reach (append callees (cdr todo)) pkg seen wrld (1- fuel))))))

(defun gr-bad-callees (fns bad pkg)
  ;; a function is a list conversion if it is in BAD, or is in PKG and its
  ;; name contains "LIST"
  (cond ((endp fns) nil)
        ((or (member-eq (car fns) bad)
             (and (equal (symbol-package-name (car fns)) pkg)
                  (search "LIST" (symbol-name (car fns)))))
         (cons (car fns) (gr-bad-callees (cdr fns) bad pkg)))
        (t (gr-bad-callees (cdr fns) bad pkg))))

(defun gr-nolist-fn (roots bad pkg wrld)
  (if (endp roots)
      nil
    (let* ((reach (gr-reach (list (car roots)) pkg nil wrld 10000))
           (hits (gr-bad-callees reach bad pkg)))
      (cons (if hits
                (msg "GRADER-FAIL nolist ~x0 reaches list conversions ~x1 (reachable: ~x2) GRADEREND~%"
                     (car roots) hits reach)
              (msg "GRADER-OK nolist ~x0 (reachable: ~x1) GRADEREND~%" (car roots) reach))
            (gr-nolist-fn (cdr roots) bad pkg wrld)))))

(defmacro gr-nolist (roots bad pkg)
  `(make-event
    (prog2$ (gr-print-msgs (gr-nolist-fn ',roots ',bad ',pkg (w state)))
            '(value-triple :nolist-checked))))

(logic)
