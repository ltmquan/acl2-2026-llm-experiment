;; def-ftc-integral.lisp
;;
;; The event macro DEF-FTC-INTEGRAL: given an integrand f and an
;; antiderivative F on an interval domain, it introduces the definite
;; integral of f (following nonstd/integrals/ftc-2.lisp) and proves, by
;; functional instantiation of FTC-2, that the integral from a to b equals
;; F(b) - F(a).
;;
;; (def-ftc-integral name
;;   :integrand      f      ; unary function symbol or (lambda (x) term)
;;   :antiderivative F      ; unary function symbol or (lambda (x) term)
;;   :domain         dom    ; ground term evaluating to an interval
;;   :derivative-thm thm1   ; optional
;;   :continuity-thm thm2   ; optional
;;   :hints          hints) ; optional, used for the macro's own obligations
;;
;; Generated events (named from NAME): NAME-INTEGRAND (only when f is a
;; lambda), MAP-NAME, RIEMANN-NAME, STRICT-INT-NAME (a defun-std), INT-NAME,
;; INT-NAME-IS-INTEGRAL and INT-NAME-FTC.  All other events are local.
;;
;; Method.  FTC-2 constrains rcdfn and rcdfn-prime to be real everywhere, so
;; the functional instance uses local "guarded" copies of f and F (equal to
;; them on the domain, 0 elsewhere) plus guarded map/riemann functions; the
;; exported riemann sum of f agrees with the guarded one on every partition
;; with endpoints in the domain (FTCI-RIEMANN-EQUAL below), which lets
;; STRICT-INT-NAME and INT-NAME themselves be substituted for
;; strict-int-rcdfn-prime and int-rcdfn-prime.
;;
;; Obligations not supplied as theorems are attempted automatically: the
;; derivative of F with the Reid-Gamboa differentiator (DEFDERIVATIVE),
;; followed by an arithmetic proof that the computed derivative equals f on
;; the domain; continuity of f by differentiating f and using that a
;; function with a standard derivative is continuous.  The other side
;; conditions are tried with the default theory, with interval definitions
;; enabled, and with arithmetic-5, each also with the user's :HINTS.  If an
;; obligation cannot be proved, the macro stops with an error printing it.

(in-package "ACL2")
(include-book "nonstd/integrals/ftc-2" :dir :system)
(include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/differentiator" :dir :system)
(include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/sin-cos-minimal" :dir :system)
(include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/ln-derivative-real" :dir :system)
(include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/sqrt-derivative" :dir :system)
(include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/inverse-trig-derivatives" :dir :system)

(encapsulate
  (((ftci-f *) => *)
   ((ftci-dom) => *))
  (local (defun ftci-f (x) x))
  (local (defun ftci-dom () (interval nil nil)))
  (defthm ftci-dom-is-interval
    (interval-p (ftci-dom))))

(defun ftci-map (p)
  (if (consp p)
      (cons (ftci-f (car p)) (ftci-map (cdr p)))
    nil))

(defun ftci-map-g (p)
  (if (consp p)
      (cons (if (inside-interval-p (car p) (ftci-dom)) (ftci-f (car p)) 0)
            (ftci-map-g (cdr p)))
    nil))

(defun ftci-riemann (p)
  (dotprod (deltas p) (ftci-map (cdr p))))

(defun ftci-riemann-g (p)
  (dotprod (deltas p) (ftci-map-g (cdr p))))

(local
 (defthm ftci-partition-car-<=-last
   (implies (partitionp p)
            (<= (car p) (car (last p))))
   :rule-classes (:rewrite :linear)))

(local
 (defthm ftci-map-equal-lemma
   (implies (and (partitionp p)
                 (inside-interval-p a (ftci-dom))
                 (<= a (car p))
                 (inside-interval-p (car (last p)) (ftci-dom)))
            (equal (ftci-map p) (ftci-map-g p)))
   :hints (("Goal" :induct (ftci-map p))
           ("Subgoal *1/1" :use ((:instance inside-interval-p-squeeze
                                            (interval (ftci-dom))
                                            (b (car (last p)))
                                            (c (car p))))))))

(defthm ftci-riemann-equal
  (implies (and (partitionp p)
                (inside-interval-p (car p) (ftci-dom))
                (inside-interval-p (car (last p)) (ftci-dom)))
           (equal (ftci-riemann p) (ftci-riemann-g p)))
  :hints (("Goal" :use ((:instance ftci-map-equal-lemma (p (cdr p)) (a (car p)))))))

(defthm ftci-diff-quotient-close
  (implies (and (acl2-numberp a) (acl2-numberp b)
                (acl2-numberp x) (acl2-numberp y)
                (not (equal x y))
                (i-close x y)
                (i-close (/ (- a b) (- x y)) d)
                (standardp d))
           (i-close a b))
  :hints (("Goal"
           :use ((:instance i-close-limited-2
                            (x (/ (- a b) (- x y)))
                            (y (fix d)))
                 (:instance small*limited->small
                            (x (- x y))
                            (y (/ (- a b) (- x y)))))
           :in-theory (e/d (i-close) (i-close-limited-2 small*limited->small))))
  :rule-classes nil)

(defthm ftci-close-equal-subst
  (implies (and (i-close q d)
                (equal d e))
           (i-close q e))
  :rule-classes nil)

(in-theory (disable ftci-riemann ftci-riemann-g))

;;; ======================================================================
;;; Program-mode helpers for the macro
;;; ======================================================================

(program)

(defun ftci-sym (name prefix suffix)
  ;; Generated names live in the package of NAME, except that names in the
  ;; COMMON-LISP package (e.g. COS) generate names in the ACL2 package.
  (intern-in-package-of-symbol
   (concatenate 'string prefix (symbol-name name) suffix)
   (if (equal (symbol-package-name name) *main-lisp-package-name*)
       'def-ftc-integral
     name)))

(defun ftci-flatten-and (term)
  ;; flatten a translated conjunction (if a b 'nil)
  (if (and (consp term)
           (eq (car term) 'if)
           (equal (fourth term) *nil*))
      (append (ftci-flatten-and (second term))
              (ftci-flatten-and (third term)))
    (if (equal term *t*)
        nil
      (list term))))

(defun ftci-x-hyps (lits)
  ;; hypotheses that mention neither Y nor STANDARDP
  (cond ((endp lits) nil)
        ((or (member-eq 'y (all-vars (car lits)))
             (and (consp (car lits))
                  (eq (car (car lits)) 'standardp)))
         (ftci-x-hyps (cdr lits)))
        (t (cons (car lits) (ftci-x-hyps (cdr lits))))))

(defun ftci-raw-parts (thm)
  ;; THM is the translated formula (implies hyps (i-close quotient deriv))
  ;; produced by DEFDERIVATIVE.  Return (mv ok x-hyps quotient deriv).
  (if (and (consp thm)
           (eq (car thm) 'implies)
           (consp (third thm))
           (eq (car (third thm)) 'i-close))
      (mv t
          (ftci-x-hyps (ftci-flatten-and (second thm)))
          (second (third thm))
          (third (third thm)))
    (mv nil nil nil nil)))

(defun ftci-conj (lst)
  (cond ((endp lst) t)
        ((endp (cdr lst)) (car lst))
        (t (cons 'and lst))))

(defun ftci-fail-event (what name formula)
  `(make-event
    (er soft 'def-ftc-integral
        "DEF-FTC-INTEGRAL ~x0: unable to prove the ~s1 obligation:~%~%~X23~%~%~
         Supply a theorem of this form, or :HINTS that prove it."
        ',name ',what ',formula nil)))

(defun ftci-hint-alternatives (form hints)
  ;; FORM is (defthm nm stmt . rest) without hints.  Return a list of
  ;; alternative events: with user hints (if any), with the default theory,
  ;; with interval definitions enabled, and with arithmetic-5.
  (let ((nm (second form)) (stmt (third form)) (rest (cdddr form)))
    (append
     (and hints `((defthm ,nm ,stmt :hints ,hints ,@rest)))
     `((defthm ,nm ,stmt ,@rest)
       (defthm ,nm ,stmt
         :hints (("Goal" :in-theory (enable interval-definition-theory)))
         ,@rest)
       (encapsulate
         ()
         (local (include-book "arithmetic-5/top" :dir :system))
         (defthm ,nm ,stmt
           ,@(and hints `(:hints ,hints))
           ,@rest))
       (encapsulate
         ()
         (local (include-book "arithmetic-5/top" :dir :system))
         (defthm ,nm ,stmt
           :hints (("Goal" :in-theory (enable interval-definition-theory)))
           ,@rest))))))

(defun ftci-or (name what form hint1 hint2)
  ;; Prove FORM with the hint keywords HINT1 on Goal, else HINT2, else fail.
  `(make-event
    '(:or (,@form :hints (("Goal" ,@hint1)))
          (,@form :hints (("Goal" ,@hint2)))
          ,(ftci-fail-event what name (third form)))))

(defun ftci-try (what name form hints display)
  ;; Try to prove FORM, else fail with an error that prints the obligation.
  ;; When WHAT is NIL, just fail (used for internal lemmas, whose failure
  ;; makes an enclosing strategy fail over to the next alternative).
  `(make-event
    '(:or ,@(ftci-hint-alternatives form hints)
          ,@(and what (list (ftci-fail-event what name
                                             (or display (third form))))))))

;;; Second step of the automatic derivative proof: DEFDERIVATIVE has proved
;;; theorem RAW about the antiderivative.  Relate it to the obligation.

(defun ftci-deriv-step2 (name raw dom f-sym obligation hints wrld)
  (let ((thm (getpropc raw 'theorem nil wrld)))
    (mv-let (ok x-hyps quot deriv)
            (ftci-raw-parts thm)
            (if (not ok)
                `(make-event (er soft 'def-ftc-integral
                                 "Unexpected DEFDERIVATIVE result ~x0" ',thm))
              (let* ((hyps-name (ftci-sym name "" "-FTC-RAW-DERIV-HYPS"))
                     (eq-name (ftci-sym name "" "-FTC-RAW-DERIV-EQUAL"))
                     (oname (second obligation))
                     (quot1 (subcor-var '(y) '(x1) quot)))
                `(progn
                   (local
                    ,(ftci-try nil name
                               `(defthm ,hyps-name
                                  (implies (inside-interval-p x ,dom)
                                           ,(ftci-conj x-hyps))
                                  :rule-classes nil)
                               hints nil))
                   (local
                    ,(ftci-try nil name
                               `(defthm ,eq-name
                                  (implies (inside-interval-p x ,dom)
                                           (equal ,deriv (,f-sym x)))
                                  :rule-classes nil)
                               hints nil))
                   (make-event
                    '(:or
                      (defthm ,oname ,(third obligation)
                        :hints (("Goal"
                                 :use ((:instance ,raw (y x1))
                                       (:instance ,hyps-name)
                                       (:instance ,hyps-name (x x1))
                                       (:instance ,eq-name)
                                       (:instance ftci-close-equal-subst
                                                  (q ,quot1)
                                                  (d ,deriv)
                                                  (e (,f-sym x))))
                                 :in-theory (theory 'minimal-theory))))
                      (defthm ,oname ,(third obligation)
                        :hints (("Goal"
                                 :use ((:instance ,raw (y x1))
                                       (:instance ,hyps-name)
                                       (:instance ,hyps-name (x x1))
                                       (:instance ,eq-name)
                                       (:instance ftci-close-equal-subst
                                                  (q ,quot1)
                                                  (d ,deriv)
                                                  (e (,f-sym x))))
                                 :in-theory (disable ,raw))))))))))))

;;; Second step of the automatic continuity proof: DEFDERIVATIVE has proved
;;; that f itself is differentiable (theorem RAW); a differentiable function
;;; with a standard derivative is continuous.

(defun ftci-cont-step2 (name raw dom f-sym real-name dom-real-name obligation
                             hints wrld)
  (declare (ignorable dom))
  (let ((thm (getpropc raw 'theorem nil wrld)))
    (mv-let (ok x-hyps quot deriv)
            (ftci-raw-parts thm)
            (declare (ignore quot))
            (if (not ok)
                `(make-event (er soft 'def-ftc-integral
                                 "Unexpected DEFDERIVATIVE result ~x0" ',thm))
              (let* ((hyps-name (ftci-sym name "" "-FTC-RAW-CONT-HYPS"))
                     (std-name (ftci-sym name "" "-FTC-RAW-CONT-STD"))
                     (oname (second obligation)))
                `(progn
                   (local
                    ,(ftci-try nil name
                               `(defthm ,hyps-name
                                  (implies (inside-interval-p x ,dom)
                                           ,(ftci-conj x-hyps))
                                  :rule-classes nil)
                               hints nil))
                   (local
                    (defthm-std ,std-name
                      (implies (standardp x)
                               (standardp ,deriv))
                      :rule-classes nil))
                   (make-event
                    '(:or
                      (defthm ,oname ,(third obligation)
                        :hints (("Goal"
                                 :use ((:instance ,raw (y x1))
                                       (:instance ,hyps-name)
                                       (:instance ,hyps-name (x x1))
                                       (:instance ,std-name)
                                       (:instance ,real-name)
                                       (:instance ,real-name (x x1))
                                       (:instance ,dom-real-name)
                                       (:instance ,dom-real-name (x x1))
                                       (:instance ftci-diff-quotient-close
                                                  (a (,f-sym x))
                                                  (b (,f-sym x1))
                                                  (y x1)
                                                  (d ,deriv)))
                                 :in-theory (union-theories
                                             '(i-close-reflexive)
                                             (theory 'minimal-theory)))))
                      (defthm ,oname ,(third obligation)
                        :hints (("Goal"
                                 :use ((:instance ,raw (y x1))
                                       (:instance ,hyps-name)
                                       (:instance ,hyps-name (x x1))
                                       (:instance ,std-name)
                                       (:instance ,real-name)
                                       (:instance ,real-name (x x1))
                                       (:instance ,dom-real-name)
                                       (:instance ,dom-real-name (x x1))
                                       (:instance ftci-diff-quotient-close
                                                  (a (,f-sym x))
                                                  (b (,f-sym x1))
                                                  (y x1)
                                                  (d ,deriv)))
                                 :in-theory (disable ,raw ,f-sym))))))))))))

;;; Parsing the :integrand / :antiderivative arguments.
;;; Returns (mv erp kind sym formal tbody) where KIND is :SYM or :LAMBDA.

(defun ftci-parse-fn (spec what wrld state)
  (declare (xargs :stobjs state))
  (cond
   ((and (symbolp spec) spec)
    (if (and (function-symbolp spec wrld)
             (eql (arity spec wrld) 1))
        (mv nil :sym spec nil nil)
      (mv (msg "The ~s0 ~x1 is not a unary function symbol." what spec)
          nil nil nil nil)))
   ((and (true-listp spec)
         (eql (len spec) 3)
         (eq (car spec) 'lambda)
         (true-listp (cadr spec))
         (eql (len (cadr spec)) 1)
         (symbolp (car (cadr spec)))
         (legal-variablep (car (cadr spec))))
    (mv-let (erp tbody bindings)
            (translate1-cmp (caddr spec) '(nil) nil nil 'def-ftc-integral wrld
                            (default-state-vars t))
            (declare (ignore bindings))
            (cond (erp (mv (msg "The body of the ~s0 ~x1 does not translate."
                                what spec)
                           nil nil nil nil))
                  ((not (subsetp-eq (all-vars tbody) (cadr spec)))
                   (mv (msg "The ~s0 ~x1 has free variables." what spec)
                       nil nil nil nil))
                  (t (mv nil :lambda nil (car (cadr spec)) tbody)))))
   (t (mv (msg "The ~s0 ~x1 must be a unary function symbol or a term ~
                (LAMBDA (x) body)." what spec)
          nil nil nil nil))))

(defun ftci-app (kind sym formal tbody arg)
  ;; translated application of the function to the translated term ARG
  (if (eq kind :sym)
      (list sym arg)
    (subcor-var (list formal) (list arg) tbody)))

(defun ftci-subst-alist (dom-l ag fg map-g riemann-g strict int)
  `((rcdfn-domain ,dom-l)
    (rcdfn ,ag)
    (rcdfn-prime ,fg)
    (map-rcdfn-prime ,map-g)
    (riemann-rcdfn-prime ,riemann-g)
    (strict-int-rcdfn-prime ,strict)
    (int-rcdfn-prime ,int)))

(defun def-ftc-integral-fn (name integrand antiderivative domain
                                 derivative-thm continuity-thm hints state)
  (declare (xargs :stobjs state))
  (let ((wrld (w state)) (ctx 'def-ftc-integral))
    (cond
     ((not (and (symbolp name) name (not (keywordp name))))
      (er soft ctx "The name ~x0 must be a non-keyword symbol." name))
     ((null integrand) (er soft ctx "Missing :INTEGRAND."))
     ((null antiderivative) (er soft ctx "Missing :ANTIDERIVATIVE."))
     ((null domain) (er soft ctx "Missing :DOMAIN."))
     ((not (symbolp derivative-thm))
      (er soft ctx ":DERIVATIVE-THM must be the name of a theorem."))
     ((and derivative-thm (not (getpropc derivative-thm 'theorem nil wrld)))
      (er soft ctx "~x0 (supplied as :DERIVATIVE-THM) is not a theorem."
          derivative-thm))
     ((not (symbolp continuity-thm))
      (er soft ctx ":CONTINUITY-THM must be the name of a theorem."))
     ((and continuity-thm (not (getpropc continuity-thm 'theorem nil wrld)))
      (er soft ctx "~x0 (supplied as :CONTINUITY-THM) is not a theorem."
          continuity-thm))
     ((not (true-listp hints))
      (er soft ctx ":HINTS must be a true list of hints."))
     (t
      (mv-let
       (erp fkind fsym fformal fbody)
       (ftci-parse-fn integrand "integrand" wrld state)
       (if erp (er soft ctx "~@0" erp)
         (mv-let
          (erp akind asym aformal abody)
          (ftci-parse-fn antiderivative "antiderivative" wrld state)
          (if erp (er soft ctx "~@0" erp)
            (mv-let
             (erp tdom bindings)
             (translate1-cmp domain '(nil) nil nil ctx wrld
                             (default-state-vars t))
             (declare (ignore bindings))
             (cond
              (erp (er soft ctx "The domain ~x0 does not translate." domain))
              ((all-vars tdom)
               (er soft ctx "The domain ~x0 must be a ground term." domain))
              (t
               (let* ((dom domain)
                      (integrand-fn (ftci-sym name "" "-INTEGRAND"))
                      (f-sym (if (eq fkind :sym) fsym integrand-fn))
                      (fx `(,f-sym x))
                      (fx1 `(,f-sym x1))
                      (fx-user (untranslate (ftci-app fkind fsym fformal fbody 'x)
                                            nil wrld))
                      (fx1-user (untranslate (ftci-app fkind fsym fformal fbody 'x1)
                                             nil wrld))
                      (ax (untranslate (ftci-app akind asym aformal abody 'x)
                                       nil wrld))
                      (ax1 (untranslate (ftci-app akind asym aformal abody 'x1)
                                        nil wrld))
                      (aa (untranslate (ftci-app akind asym aformal abody 'a)
                                       nil wrld))
                      (ab (untranslate (ftci-app akind asym aformal abody 'b)
                                       nil wrld))
                      (map (ftci-sym name "MAP-" ""))
                      (riemann (ftci-sym name "RIEMANN-" ""))
                      (strict (ftci-sym name "STRICT-INT-" ""))
                      (int (ftci-sym name "INT-" ""))
                      (is-integral (ftci-sym name "INT-" "-IS-INTEGRAL"))
                      (ftc (ftci-sym name "INT-" "-FTC"))
                      (dom-interval (ftci-sym name "" "-FTC-DOMAIN-INTERVAL"))
                      (dom-real (ftci-sym name "" "-FTC-DOMAIN-REAL"))
                      (dom-nontriv (ftci-sym name "" "-FTC-DOMAIN-NON-TRIVIAL"))
                      (f-real (ftci-sym name "" "-FTC-INTEGRAND-REAL"))
                      (a-real (ftci-sym name "" "-FTC-ANTIDERIVATIVE-REAL"))
                      (deriv (ftci-sym name "" "-FTC-DERIVATIVE"))
                      (cont (ftci-sym name "" "-FTC-CONTINUITY"))
                      (user-deriv (ftci-sym name "" "-FTC-USER-DERIVATIVE"))
                      (user-cont (ftci-sym name "" "-FTC-USER-CONTINUITY"))
                      (raw-a (ftci-sym name "" "-FTC-RAW-ANTIDERIVATIVE"))
                      (raw-f (ftci-sym name "" "-FTC-RAW-INTEGRAND"))
                      (fg (ftci-sym name "" "-FTC-FG"))
                      (ag (ftci-sym name "" "-FTC-AG"))
                      (map-g (ftci-sym name "MAP-" "-FTC-G"))
                      (riemann-g (ftci-sym name "RIEMANN-" "-FTC-G"))
                      (riemann-equal (ftci-sym name "" "-FTC-RIEMANN-EQUAL"))
                      (limited (ftci-sym name "" "-FTC-LIMITED-RIEMANN"))
                      (limited-g (ftci-sym name "" "-FTC-LIMITED-RIEMANN-G"))
                      (c-ag-real (ftci-sym name "" "-FTC-C-AG-REAL"))
                      (c-fg-real (ftci-sym name "" "-FTC-C-FG-REAL"))
                      (c-deriv (ftci-sym name "" "-FTC-C-DERIVATIVE"))
                      (c-cont (ftci-sym name "" "-FTC-C-CONTINUITY"))
                      (c-strict (ftci-sym name "" "-FTC-C-STRICT"))
                      (is-integral-g (ftci-sym name "INT-" "-FTC-IS-INTEGRAL-G"))
                      (ftc-g (ftci-sym name "INT-" "-FTC-G"))
                      (th `(union-theories
                            '(,dom-interval ,dom-real ,c-fg-real ,c-cont
                                            ,map-g ,riemann-g)
                            (union-theories (executable-counterpart-theory :here)
                                            (theory 'minimal-theory))))
                      (th2 `(union-theories
                             '(,dom-interval ,dom-real ,c-fg-real ,c-cont
                                             ,c-ag-real ,c-deriv
                                             ,map-g ,riemann-g ,int ,c-strict)
                             (union-theories (executable-counterpart-theory :here)
                                             (theory 'minimal-theory))))
                      (dom-l `(lambda () ,dom))
                      (deriv-stmt
                       `(implies (and (standardp x)
                                      (inside-interval-p x ,dom)
                                      (inside-interval-p x1 ,dom)
                                      (i-close x x1)
                                      (not (= x x1)))
                                 (i-close (/ (- ,ax ,ax1) (- x x1))
                                          ,fx)))
                      (cont-stmt
                       `(implies (and (standardp x)
                                      (inside-interval-p x ,dom)
                                      (i-close x x1)
                                      (inside-interval-p x1 ,dom))
                                 (i-close ,fx ,fx1)))
                      (deriv-stmt-user
                       `(implies (and (standardp x)
                                      (inside-interval-p x ,dom)
                                      (inside-interval-p x1 ,dom)
                                      (i-close x x1)
                                      (not (= x x1)))
                                 (i-close (/ (- ,ax ,ax1) (- x x1))
                                          ,fx-user)))
                      (cont-stmt-user
                       `(implies (and (standardp x)
                                      (inside-interval-p x ,dom)
                                      (i-close x x1)
                                      (inside-interval-p x1 ,dom))
                                 (i-close ,fx-user ,fx1-user)))
                      (deriv-form `(defthm ,deriv ,deriv-stmt))
                      (cont-form `(defthm ,cont ,cont-stmt))
                      (subst (ftci-subst-alist dom-l ag fg map-g riemann-g
                                               strict int))
                      (ftci-subst `((ftci-f ,f-sym)
                                    (ftci-dom ,dom-l)
                                    (ftci-map ,map)
                                    (ftci-map-g ,map-g)
                                    (ftci-riemann ,riemann)
                                    (ftci-riemann-g ,riemann-g))))
                 (value
                  `(encapsulate
                     ()
                     ,@(and (eq fkind :lambda)
                            `((defun ,integrand-fn (,fformal)
                                ,(caddr integrand))))

                     ;; ---- side conditions of FTC-2 ----
                     (local
                      ,(ftci-try "domain is an interval" name
                                 `(defthm ,dom-interval
                                    (interval-p ,dom)
                                    :rule-classes (:type-prescription :rewrite))
                                 hints nil))
                     (local
                      ,(ftci-try "domain is real" name
                                 `(defthm ,dom-real
                                    (implies (inside-interval-p x ,dom)
                                             (realp x))
                                    :rule-classes (:forward-chaining :rewrite))
                                 hints nil))
                     (local
                      ,(ftci-try "domain is non-trivial" name
                                 `(defthm ,dom-nontriv
                                    (or (null (interval-left-endpoint ,dom))
                                        (null (interval-right-endpoint ,dom))
                                        (< (interval-left-endpoint ,dom)
                                           (interval-right-endpoint ,dom)))
                                    :rule-classes nil)
                                 hints nil))
                     (local
                      ,(ftci-try "integrand is real on the domain" name
                                 `(defthm ,f-real
                                    (implies (inside-interval-p x ,dom)
                                             (realp ,fx)))
                                 hints
                                 `(implies (inside-interval-p x ,dom)
                                           (realp ,fx-user))))
                     (local
                      ,(ftci-try "antiderivative is real on the domain" name
                                 `(defthm ,a-real
                                    (implies (inside-interval-p x ,dom)
                                             (realp ,ax)))
                                 hints nil))

                     ;; ---- derivative obligation ----
                     (local
                      ,(if derivative-thm
                           `(make-event
                             '(:or
                               (defthm ,deriv ,deriv-stmt
                                 :hints (("Goal" :use ,derivative-thm)))
                               (defthm ,deriv ,deriv-stmt
                                 :hints (("Goal" :use ,derivative-thm
                                          :in-theory (disable ,derivative-thm))))
                               (encapsulate
                                 ()
                                 (local (defthm ,user-deriv ,deriv-stmt-user
                                          :hints (("Goal" :by ,derivative-thm))))
                                 (defthm ,deriv ,deriv-stmt
                                   :hints (("Goal" :use ,user-deriv
                                            :in-theory (disable ,user-deriv)))))
                               ,(ftci-fail-event
                                 "derivative (from the supplied :DERIVATIVE-THM)"
                                 name deriv-stmt-user)))
                         `(make-event
                           '(:or
                             (encapsulate
                               ()
                               (local (defderivative ,raw-a ,ax))
                               (make-event
                                (ftci-deriv-step2 ',name ',raw-a ',dom ',f-sym
                                                  ',deriv-form ',hints
                                                  (w state))))
                             ,@(ftci-hint-alternatives deriv-form hints)
                             ,(ftci-fail-event "derivative" name deriv-stmt-user)))))

                     ;; ---- continuity obligation ----
                     (local
                      ,(if continuity-thm
                           `(make-event
                             '(:or
                               (defthm ,cont ,cont-stmt
                                 :hints (("Goal" :use ,continuity-thm)))
                               (defthm ,cont ,cont-stmt
                                 :hints (("Goal" :use ,continuity-thm
                                          :in-theory (disable ,continuity-thm))))
                               (encapsulate
                                 ()
                                 (local (defthm ,user-cont ,cont-stmt-user
                                          :hints (("Goal" :by ,continuity-thm))))
                                 (defthm ,cont ,cont-stmt
                                   :hints (("Goal" :use ,user-cont
                                            :in-theory (disable ,user-cont)))))
                               ,(ftci-fail-event
                                 "continuity (from the supplied :CONTINUITY-THM)"
                                 name cont-stmt-user)))
                         `(make-event
                           '(:or
                             (encapsulate
                               ()
                               (local (defderivative ,raw-f ,fx))
                               (make-event
                                (ftci-cont-step2 ',name ',raw-f ',dom ',f-sym
                                                 ',f-real ',dom-real
                                                 ',cont-form ',hints
                                                 (w state))))
                             ,@(ftci-hint-alternatives cont-form hints)
                             ,(ftci-fail-event "continuity" name cont-stmt-user)))))

                     ;; ---- the integral, as in ftc-2.lisp ----
                     (local (defun ,fg (x)
                              (if (inside-interval-p x ,dom) ,fx 0)))
                     (local (defun ,ag (x)
                              (if (inside-interval-p x ,dom) ,ax 0)))

                     (defun ,map (p)
                       (if (consp p)
                           (cons (,f-sym (car p))
                                 (,map (cdr p)))
                         nil))

                     (defun ,riemann (p)
                       (dotprod (deltas p)
                                (,map (cdr p))))

                     (local (defun ,map-g (p)
                              (if (consp p)
                                  (cons (,fg (car p)) (,map-g (cdr p)))
                                nil)))
                     (local (defun ,riemann-g (p)
                              (dotprod (deltas p) (,map-g (cdr p)))))

                     (local
                      (defthm ,riemann-equal
                        (implies (and (partitionp p)
                                      (inside-interval-p (car p) ,dom)
                                      (inside-interval-p (car (last p)) ,dom))
                                 (equal (,riemann p) (,riemann-g p)))
                        :hints (("Goal"
                                 :by (:functional-instance ftci-riemann-equal
                                                           ,@ftci-subst)))))

                     ;; exact instances of the constraints of FTC-2
                     (local
                      ,(ftci-or name "constraint (realness of the guarded antiderivative)"
                                `(defthm ,c-ag-real (realp (,ag x))
                                   :rule-classes (:rewrite :type-prescription))
                                `(:use ((:instance ,a-real)) :in-theory (union-theories '(,ag) (theory 'minimal-theory)))
                                `(:use ((:instance ,a-real)))))
                     (local
                      ,(ftci-or name "constraint (realness of the guarded integrand)"
                                `(defthm ,c-fg-real (realp (,fg x))
                                   :rule-classes (:rewrite :type-prescription))
                                `(:use ((:instance ,f-real)) :in-theory (union-theories '(,fg) (theory 'minimal-theory)))
                                `(:use ((:instance ,f-real)))))
                     (local
                      ,(ftci-or name "constraint (derivative of the guarded antiderivative)"
                                `(defthm ,c-deriv
                                   (implies (and (standardp x)
                                                 (inside-interval-p x ,dom)
                                                 (inside-interval-p x1 ,dom)
                                                 (i-close x x1)
                                                 (not (= x x1)))
                                            (i-close (/ (- (,ag x) (,ag x1)) (- x x1))
                                                     (,fg x))))
                                `(:use ((:instance ,deriv)) :in-theory (union-theories '(,ag ,fg) (theory 'minimal-theory)))
                                `(:use ((:instance ,deriv)) :in-theory (disable ,deriv))))
                     (local
                      ,(ftci-or name "constraint (continuity of the guarded integrand)"
                                `(defthm ,c-cont
                                   (implies (and (standardp x)
                                                 (inside-interval-p x ,dom)
                                                 (i-close x x1)
                                                 (inside-interval-p x1 ,dom))
                                            (i-close (,fg x) (,fg x1))))
                                `(:use ((:instance ,cont)) :in-theory (union-theories '(,fg) (theory 'minimal-theory)))
                                `(:use ((:instance ,cont)) :in-theory (disable ,cont))))

                     (local
                      (defthm ,limited-g
                        (implies (and (realp a) (standardp a)
                                      (realp b) (standardp b)
                                      (inside-interval-p a ,dom)
                                      (inside-interval-p b ,dom)
                                      (< a b))
                                 (i-limited (,riemann-g (make-small-partition a b))))
                        :hints (("Goal"
                                 :by (:functional-instance
                                      limited-riemann-rcfn-small-partition
                                      (rcfn-domain ,dom-l)
                                      (rcfn ,fg)
                                      (map-rcfn ,map-g)
                                      (riemann-rcfn ,riemann-g))
                                 :in-theory ,th))))

                     (local
                      (defthm ,limited
                        (implies (and (realp a) (standardp a)
                                      (realp b) (standardp b)
                                      (inside-interval-p a ,dom)
                                      (inside-interval-p b ,dom)
                                      (< a b))
                                 (i-limited (,riemann (make-small-partition a b))))
                        :hints (("Goal"
                                 :use ((:instance ,limited-g)
                                       (:instance ,riemann-equal
                                                  (p (make-small-partition a b))))
                                 :in-theory (disable ,riemann ,riemann-g ,limited-g
                                                     ,riemann-equal)))))

                     (local (in-theory (disable ,riemann ,riemann-g ,riemann-equal ,limited-g)))

                     (defun-std ,strict (a b)
                       (if (and (realp a)
                                (realp b)
                                (inside-interval-p a ,dom)
                                (inside-interval-p b ,dom)
                                (< a b))
                           (standard-part (,riemann (make-small-partition a b)))
                         0))

                     (local (in-theory (enable ,riemann ,riemann-g ,riemann-equal)))

                     (defun ,int (a b)
                       (if (<= a b)
                           (,strict a b)
                         (- (,strict b a))))

                     (local
                      ,(ftci-or name "constraint (definition of the strict integral)"
                                `(defthm ,c-strict
                                   (implies (and (standardp a) (standardp b))
                                            (equal (,strict a b)
                                                   (if (and (realp a)
                                                            (realp b)
                                                            (inside-interval-p a ,dom)
                                                            (inside-interval-p b ,dom)
                                                            (< a b))
                                                       (standard-part
                                                        (,riemann-g (make-small-partition a b)))
                                                     0))))
                                `(:use ((:instance ,riemann-equal
                                                   (p (make-small-partition a b))))
                                  :in-theory (disable ,riemann-equal ,riemann ,riemann-g))
                                `(:in-theory (disable ,riemann ,riemann-g))))
                     (local
                      (defthm ,is-integral-g
                        (implies (and (standardp a)
                                      (standardp b)
                                      (<= a b)
                                      (inside-interval-p a ,dom)
                                      (inside-interval-p b ,dom)
                                      (partitionp p)
                                      (equal (car p) a)
                                      (equal (car (last p)) b)
                                      (i-small (mesh p)))
                                 (i-close (,riemann-g p)
                                          (,strict a b)))
                        :hints (("Goal"
                                 :by (:functional-instance
                                      strict-int-rcdfn-prime-is-integral-of-rcdfn-prime
                                      ,@subst)
                                 :in-theory ,th2))))

                     (defthm ,is-integral
                       (implies (and (standardp a)
                                     (standardp b)
                                     (<= a b)
                                     (inside-interval-p a ,dom)
                                     (inside-interval-p b ,dom)
                                     (partitionp p)
                                     (equal (car p) a)
                                     (equal (car (last p)) b)
                                     (i-small (mesh p)))
                                (i-close (,riemann p)
                                         (,strict a b)))
                       :hints (("Goal"
                                :use ((:instance ,is-integral-g)
                                      (:instance ,riemann-equal))
                                :in-theory (disable ,is-integral-g ,riemann-equal
                                                    ,riemann ,riemann-g ,strict))))

                     (local
                      (defthm ,ftc-g
                        (implies (and (inside-interval-p a ,dom)
                                      (inside-interval-p b ,dom))
                                 (equal (,int a b)
                                        (- (,ag b) (,ag a))))
                        :hints (("Goal"
                                 :by (:functional-instance ftc-2 ,@subst)
                                 :in-theory ,th2))))

                     ,(ftci-or name "final step"
                               `(defthm ,ftc
                                  (implies (and (inside-interval-p a ,dom)
                                                (inside-interval-p b ,dom))
                                           (equal (,int a b)
                                                  (- ,ab ,aa))))
                               `(:use ((:instance ,ftc-g))
                                 :in-theory (union-theories '(,ag) (theory 'minimal-theory)))
                               `(:use ((:instance ,ftc-g))
                                 :in-theory (disable ,ftc-g ,int)))))))))))))))))

(logic)

(defmacro def-ftc-integral (&whole whole name &key integrand antiderivative domain
                                   derivative-thm continuity-thm hints)
  `(make-event
    (def-ftc-integral-fn ',name ',integrand ',antiderivative ',domain
      ',derivative-thm ',continuity-thm ',hints state)
    :on-behalf-of ,whole))
