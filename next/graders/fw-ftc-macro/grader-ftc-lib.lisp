; Grader helper for fw-ftc-macro (written before any run).  Does not include
; the model's books.  Provides GR-CHECK-FTC, which checks the events generated
; by one def-ftc-integral call against the prompt's specification:
;   - map-NAME, riemann-NAME, strict-int-NAME, int-NAME (and NAME-integrand for
;     a lambda integrand) exist, with the bodies of ftc-2.lisp (up to renaming
;     of formals; the domain may appear as the :domain term, its value, or a
;     call of a 0-ary function whose body is one of those);
;   - strict-int-NAME is introduced by DEFUN-STD;
;   - int-NAME-ftc has exactly the prompt's formula (translated), with (F b)
;     either as the lambda application or beta-reduced;
;   - int-NAME-is-integral has exactly the prompt's formula (translated), as
;     strict-int-rcdfn-prime-is-integral-of-rcdfn-prime in ftc-2.lisp.
; A failed check stops certification with an error containing "GRADER-FAIL".

(in-package "ACL2")

(program)
(set-state-ok t)

(defun gr-name (fmt name)
  ;; fmt is a list of strings and :name, e.g. ("INT-" :name "-FTC")
  (intern-in-package-of-symbol
   (if (endp fmt)
       ""
     (concatenate 'string
                  (if (eq (car fmt) :name) (symbol-name name) (car fmt))
                  (symbol-name (gr-name (cdr fmt) name))))
   name))

(defun gr-match (pat term alist)
  ;; pat may contain the wildcard GR-DOM-WILD; returns (mv ok alist)
  (cond ((eq pat 'gr-dom-wild)
         (let ((b (assoc-eq 'gr-dom-wild alist)))
           (if b
               (mv (equal (cdr b) term) alist)
             (mv t (acons 'gr-dom-wild term alist)))))
        ((atom pat) (mv (equal pat term) alist))
        ((atom term) (mv nil alist))
        (t (mv-let (ok alist)
             (gr-match (car pat) (car term) alist)
             (if ok
                 (gr-match (cdr pat) (cdr term) alist)
               (mv nil alist))))))

(defun gr-event-formals-body (name wrld)
  ;; (mv kind formals body) from the introducing event, or (mv nil nil nil)
  (let ((ev (get-event name wrld)))
    (if (and (consp ev)
             (member-eq (car ev) '(defun defund defun-std defun-nx defund-nx))
             (eq (cadr ev) name))
        (mv (car ev) (caddr ev) (car (last ev)))
      (mv nil nil nil))))

(defun gr-trans (x state)
  ;; translate a term for logic; returns (mv erp val state)
  (translate x t nil t 'grader (w state) state))

(defun gr-defn-check (name canon pat state)
  ;; check that function NAME has formals of length (len canon) and a body
  ;; that, after renaming formals to CANON and translation, matches PAT.
  ;; Returns (mv msg-or-nil dom-binding kind state).
  (let ((wrld (w state)))
    (mv-let (kind formals body)
      (gr-event-formals-body name wrld)
      (cond
       ((null kind)
        (mv (msg "~x0 is not introduced by a defun/defun-std event (get-event: ~x1)"
                 name (get-event name wrld))
            nil nil state))
       ((not (equal (len formals) (len canon)))
        (mv (msg "~x0 has formals ~x1, expected ~x2 arguments" name formals (len canon))
            nil kind state))
       (t
        (mv-let (erp tbody state)
          (gr-trans body state)
          (if erp
              (mv (msg "cannot translate the body of ~x0" name) nil kind state)
            (let ((rbody (sublis-var (pairlis$ formals canon) tbody)))
              (mv-let (ok alist)
                (gr-match pat rbody nil)
                (if ok
                    (mv nil (cdr (assoc-eq 'gr-dom-wild alist)) kind state)
                  (mv (msg "the body of ~x0 (formals renamed to ~x1) is~%~x2~%expected~%~x3"
                           name canon rbody pat)
                      nil kind state)))))))))))

(defun gr-dom-ok (term tdom domval wrld)
  ;; TERM is acceptable as the domain in a body
  (or (equal term tdom)
      (equal term (kwote domval))
      (and (consp term)
           (symbolp (car term))
           (null (cdr term))
           (let ((ev (get-event (car term) wrld)))
             (and (consp ev)
                  (member-eq (car ev) '(defun defund))
                  (null (caddr ev))
                  ;; body as written: the :domain term or its quoted value
                  (or (equal (car (last ev)) tdom)
                      (equal (car (last ev)) (kwote domval))
                      (equal (car (last ev)) domval)))))))

(defun gr-check-ftc-fn (name f antider dom domval state)
  ;; returns an error triple; value is the list of events to run after the checks
  (let* ((map (gr-name '("MAP-" :name) name))
         (riem (gr-name '("RIEMANN-" :name) name))
         (sint (gr-name '("STRICT-INT-" :name) name))
         (int (gr-name '("INT-" :name) name))
         (integ (gr-name '(:name "-INTEGRAND") name))
         (ftc (gr-name '("INT-" :name "-FTC") name))
         (isint (gr-name '("INT-" :name "-IS-INTEGRAL") name))
         (lambdap (and (consp f) (eq (car f) 'lambda)))
         (fsym (if lambdap integ f)))
    (er-let*
     ((tdom (gr-trans dom state))
      (spat (gr-trans `(if (and (realp a) (realp b)
                                 (inside-interval-p a gr-dom-wild)
                                 (inside-interval-p b gr-dom-wild)
                                 (< a b))
                            (standard-part (,riem (make-small-partition a b)))
                          0)
                      state))
      (ipat (gr-trans `(if (<= a b) (,sint a b) (- (,sint b a))) state))
      (ftc1 (gr-trans `(implies (and (inside-interval-p a ,dom) (inside-interval-p b ,dom))
                                (equal (,int a b) (- (,antider b) (,antider a))))
                      state))
      (isint1 (gr-trans `(implies (and (standardp a) (standardp b) (<= a b)
                                        (inside-interval-p a ,dom) (inside-interval-p b ,dom)
                                        (partitionp p) (equal (car p) a) (equal (car (last p)) b)
                                        (i-small (mesh p)))
                                   (i-close (,riem p) (,sint a b)))
                        state))
      (ftc2 (if (and (consp antider) (eq (car antider) 'lambda))
                (er-let* ((tF (gr-trans (caddr antider) state))
                          (shape (gr-trans `(implies (and (inside-interval-p a ,dom)
                                                          (inside-interval-p b ,dom))
                                                     (equal (,int a b) (- gr-fb gr-fa)))
                                           state)))
                  (value (sublis-var (list (cons 'gr-fb (subcor-var (cadr antider) '(b) tF))
                                           (cons 'gr-fa (subcor-var (cadr antider) '(a) tF)))
                                     shape)))
              (value ftc1))))
     (er-progn
      ;; name-integrand
      (if lambdap
          (er-let* ((tlbody (gr-trans (caddr f) state)))
            (mv-let (msg b kind state)
              (gr-defn-check integ '(x) (sublis-var (pairlis$ (cadr f) '(x)) tlbody) state)
              (declare (ignore b kind))
              (if msg (er soft 'grader "GRADER-FAIL: ~@0" msg) (value :ok))))
        (value :ok))
      ;; map-name
      (mv-let (msg b kind state)
        (gr-defn-check map '(p)
                       `(if (consp p) (cons (,fsym (car p)) (,map (cdr p))) 'nil)
                       state)
        (declare (ignore b kind))
        (if msg (er soft 'grader "GRADER-FAIL: ~@0" msg) (value :ok)))
      ;; riemann-name
      (mv-let (msg b kind state)
        (gr-defn-check riem '(p) `(dotprod (deltas p) (,map (cdr p))) state)
        (declare (ignore b kind))
        (if msg (er soft 'grader "GRADER-FAIL: ~@0" msg) (value :ok)))
      ;; strict-int-name: defun-std with the ftc-2.lisp body
      (mv-let (msg b kind state)
        (gr-defn-check sint '(a b) spat state)
        (cond (msg (er soft 'grader "GRADER-FAIL: ~@0" msg))
              ((not (eq kind 'defun-std))
               (er soft 'grader "GRADER-FAIL: ~x0 is introduced by ~x1, not defun-std" sint kind))
              ((not (gr-dom-ok b tdom domval (w state)))
               (er soft 'grader "GRADER-FAIL: domain term ~x0 in ~x1 is not the :domain ~x2"
                   b sint dom))
              (t (value :ok))))
      ;; int-name
      (mv-let (msg b kind state)
        (gr-defn-check int '(a b) ipat state)
        (declare (ignore b kind))
        (if msg (er soft 'grader "GRADER-FAIL: ~@0" msg) (value :ok)))
      ;; int-name-ftc: exact formula
      (let ((fm (formula ftc nil (w state))))
        (cond ((null fm)
               (er soft 'grader "GRADER-FAIL: no theorem named ~x0" ftc))
              ((or (equal fm ftc1) (equal fm ftc2)) (value :ok))
              (t (er soft 'grader "GRADER-FAIL: ~x0 has formula~%~x1~%expected~%~x2~%or~%~x3"
                     ftc fm ftc1 ftc2))))
      ;; int-name-is-integral: exactly the form of the prompt (as in ftc-2.lisp)
      (let ((fm (formula isint nil (w state))))
        (cond ((null fm)
               (er soft 'grader "GRADER-FAIL: no theorem named ~x0" isint))
              ((equal fm isint1) (value :ok))
              (t (er soft 'grader "GRADER-FAIL: ~x0 has formula~%~x1~%expected~%~x2" isint fm isint1))))
     (value
      `(value-triple (cw "GRADER: generated definitions, ~x0 and ~x1 match the specification~%"
                         ',ftc ',isint)))))))

(defmacro gr-check-ftc (name &key integrand antiderivative domain)
  `(make-event (gr-check-ftc-fn ',name ',integrand ',antiderivative ',domain
                                ,domain state)))

(logic)
