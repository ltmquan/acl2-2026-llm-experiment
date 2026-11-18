; DEFINDUCTIVE -- Inductive Definitions via Inference Rules
;
; An implementation of the DEFINDUCTIVE event macro described in
; "Inductive Definitions via Inference Rules in ACL2" (Coglio & Jurgensen,
; ACL2-2026).
;
; Usage:
;
;   (definductive name
;     :preds ((p x1 x2 ...) ...)                 ; predicates being defined
;     :irules ((rule (prem1 prem2 ...) concl) ...) ; inference rules
;     :parents ... :short ... :long ...  ; optional, for XDOC (defxdoc name)
;     :verbose t/nil)                    ; optional, show all the output
;
; For each clique of mutually dependent predicates, the macro generates
;
;   - proof tree types p-proof (one FTY event per clique: a deftagsum for a
;     singleton clique, a deftypes for a larger clique), with recognizers
;     p-proofp and count functions p-proof-count;
;   - validity functions p-proof-validp (mutually recursive for cliques of
;     two or more predicates, accompanied by the flag macro
;     defthm-p-proof-validp-clique-flag);
;   - proof-tree minimality functions p-proof-minimalp (defun-sk forall);
;   - the predicates p (defun-sk exists, witness p-proof);
;   - theorems p-when-proof-validp;
;   - the inference rule theorems p-rule;
;   - rule induction functions p-induct (mutually recursive for cliques of two
;     or more predicates, with flag macro defthm-p-induct-clique-flag), and an
;     induction rule p-induction for singleton cliques;
;   - the constrained alternative predicates p-alt with constraints
;     p-alt-rule (one encapsulate for all the predicates);
;   - the minimality theorems p-alt-when-p-proof-validp and p-alt-when-p.
;
; All the generated proofs are carried out in a fixed theory (the theory at
; the end of this book, plus the newly generated rules), so they do not depend
; on the user's current theory.

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "tools/flag" :dir :system)

(program)
(set-state-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Generic utilities.

(defun definductive-cat-sym (sym str)
  ;; SYM followed by STR, in the package of SYM.
  (intern-in-package-of-symbol (concatenate 'string (symbol-name sym) str)
                               sym))

(defun definductive-cat-sym2 (sym1 str sym2)
  ;; SYM1, STR, SYM2 in the package of SYM1.
  (intern-in-package-of-symbol (concatenate 'string
                                            (symbol-name sym1)
                                            str
                                            (symbol-name sym2))
                               sym1))

(defun definductive-kwd (sym)
  (intern (symbol-name sym) "KEYWORD"))

(defun definductive-nat-str (n)
  (coerce (explode-nonnegative-integer n 10 nil) 'string))

(defun definductive-premise-field (sym k)
  ;; premiseK-proof, in the package of SYM.
  (intern-in-package-of-symbol (concatenate 'string
                                            "PREMISE"
                                            (definductive-nat-str k)
                                            "-PROOF")
                               (if (equal (symbol-package-name sym)
                                          "COMMON-LISP")
                                   'proof
                                 sym)))

(defun definductive-get (key alist)
  (cdr (assoc-eq key alist)))

(defun definductive-pairlis (xs ys)
  (if (or (endp xs) (endp ys))
      nil
    (cons (cons (car xs) (car ys))
          (definductive-pairlis (cdr xs) (cdr ys)))))

(defun definductive-doublets (xs ys)
  ;; ((x1 y1) (x2 y2) ...)
  (if (or (endp xs) (endp ys))
      nil
    (cons (list (car xs) (car ys))
          (definductive-doublets (cdr xs) (cdr ys)))))

(defun definductive-union-eq (xs ys)
  ;; Union preserving the order of XS then new elements of YS.
  (cond ((endp ys) xs)
        ((member-eq (car ys) xs) (definductive-union-eq xs (cdr ys)))
        (t (definductive-union-eq (append xs (list (car ys))) (cdr ys)))))

(defun definductive-subsetp-eq (xs ys)
  (cond ((endp xs) t)
        ((member-eq (car xs) ys) (definductive-subsetp-eq (cdr xs) ys))
        (t nil)))

;; Free variables of a translated term, in order of first occurrence.

(mutual-recursion
 (defun definductive-term-vars (term acc)
   (cond ((variablep term)
          (if (member-eq term acc) acc (append acc (list term))))
         ((fquotep term) acc)
         (t (definductive-term-list-vars (fargs term) acc))))
 (defun definductive-term-list-vars (terms acc)
   (if (endp terms)
       acc
     (definductive-term-list-vars (cdr terms)
       (definductive-term-vars (car terms) acc)))))

;; Whether an untranslated form contains a call of one of the predicates
;; (ignoring quoted constants).  This is a syntactic over-approximation that
;; is sufficient to detect occurrences of the predicates being defined
;; anywhere other than at the top level of premises and conclusions.

(mutual-recursion
 (defun definductive-mentions-preds-p (x preds)
   (cond ((atom x) nil)
         ((eq (car x) 'quote) nil)
         ((and (symbolp (car x)) (member-eq (car x) preds)) t)
         (t (definductive-mentions-preds-list-p x preds))))
 (defun definductive-mentions-preds-list-p (x preds)
   (cond ((atom x) nil)
         (t (or (definductive-mentions-preds-p (car x) preds)
                (definductive-mentions-preds-list-p (cdr x) preds))))))

(defun definductive-symbol-listp-no-dups (x)
  (and (symbol-listp x) (no-duplicatesp-eq x)))

(defun definductive-translate-list (forms ctx wrld state)
  (if (endp forms)
      (value nil)
    (er-let* ((term (translate (car forms) t t nil ctx wrld state))
              (terms (definductive-translate-list (cdr forms) ctx wrld state)))
      (value (cons term terms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Processing of the :preds input.
;;
;; Each predicate is represented as an alist with keys
;;   :name :formals

(defun definductive-check-new-name (name ctx wrld state)
  (cond ((not (symbolp name))
         (er soft ctx "~x0 is not a symbol." name))
        ((keywordp name)
         (er soft ctx "The name ~x0 must not be a keyword." name))
        ((not (new-namep name wrld))
         (er soft ctx "The name ~x0 is already in use." name))
        ((or (function-symbolp name wrld)
             (getpropc name 'macro-body nil wrld))
         (er soft ctx "The name ~x0 is already in use." name))
        (t (value nil))))

(defun definductive-process-preds (preds ctx wrld state)
  (if (endp preds)
      (value nil)
    (let ((pred (car preds)))
      (if (not (and (consp pred)
                    (symbolp (car pred))
                    (true-listp (cdr pred))))
          (er soft ctx "Each :PREDS entry must have the form (P X1 X2 ...), ~
                        but ~x0 does not."
              pred)
        (let ((name (car pred))
              (formals (cdr pred)))
          (er-progn
           (definductive-check-new-name name ctx wrld state)
           (if (not (and (arglistp formals)))
               (er soft ctx "The formal parameters ~x0 of predicate ~x1 ~
                             must be distinct legal variable names."
                   formals name)
             (value nil))
           (if (or (member-eq 'proof formals)
                   (member-eq 'proof2 formals))
               (er soft ctx "The formal parameters of predicate ~x0 ~
                             must not include ~x1 or ~x2."
                   name 'proof 'proof2)
             (value nil))
           (er-let* ((rest (definductive-process-preds (cdr preds)
                             ctx wrld state)))
             (value (cons (list (cons :name name)
                                (cons :formals formals))
                          rest)))))))))

(defun definductive-pred-names (preds)
  (if (endp preds)
      nil
    (cons (definductive-get :name (car preds))
          (definductive-pred-names (cdr preds)))))

(defun definductive-find-pred (p preds)
  (cond ((endp preds) nil)
        ((eq (definductive-get :name (car preds)) p) (car preds))
        (t (definductive-find-pred p (cdr preds)))))

(defun definductive-formals (p preds)
  (definductive-get :formals (definductive-find-pred p preds)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Processing of the :irules input.
;;
;; Each premise is represented as an alist with keys
;;   :kind    -- :pred or :term
;;   :index   -- position (1-based) in the list of premises
;;   :form    -- the untranslated premise
;;   :pred    -- (for :pred) the predicate
;;   :args    -- (for :pred) the translated arguments
;;   :term    -- (for :term) the translated term
;;
;; Each rule is represented as an alist with keys
;;   :name :prems :concl-form :pred :args :vars

(defun definductive-bad-connective-p (x preds)
  ;; Recognize AND, OR, NOT, IMPLIES etc. applied to predicates.
  (and (consp x)
       (member-eq (car x) '(and or not implies iff if))
       (definductive-mentions-preds-list-p (cdr x) preds)))

(defun definductive-process-pred-call (x what rule-name preds ctx wrld state)
  ;; X is a call (q t1 ... tn) of a predicate q in PREDS.
  (let* ((q (car x))
         (formals (definductive-formals q preds)))
    (cond ((not (true-listp x))
           (er soft ctx "The ~@0 ~x1 of rule ~x2 is malformed."
               what x rule-name))
          ((not (equal (len (cdr x)) (len formals)))
           (er soft ctx "The ~@0 ~x1 of rule ~x2 calls predicate ~x3 ~
                         with ~x4 arguments, but it has ~x5 formal parameters."
               what x rule-name q (len (cdr x)) (len formals)))
          ((definductive-mentions-preds-list-p (cdr x)
             (definductive-pred-names preds))
           (er soft ctx "The ~@0 ~x1 of rule ~x2 has arguments that ~
                         reference the predicates being defined, which ~
                         may only appear at the top level of premises ~
                         and conclusions."
               what x rule-name))
          (t (er-let* ((args (definductive-translate-list (cdr x)
                               ctx wrld state)))
               (value args))))))

(defun definductive-process-prems (prems k rule-name preds ctx wrld state)
  (if (endp prems)
      (value nil)
    (let ((prem (car prems))
          (names (definductive-pred-names preds)))
      (er-let*
          ((prem-info
            (cond
             ((and (consp prem) (member-eq (car prem) names))
              (er-let* ((args (definductive-process-pred-call
                                prem "premise" rule-name preds
                                ctx wrld state)))
                (value (list (cons :kind :pred)
                             (cons :index k)
                             (cons :form prem)
                             (cons :pred (car prem))
                             (cons :args args)))))
             ((definductive-bad-connective-p prem names)
              (er soft ctx "The premise ~x0 of rule ~x1 is not allowed: ~
                            the predicates being defined may only appear ~
                            at the top level of premises, not inside ~x2 ~
                            or other connectives or terms.  (Conjunctions ~
                            may be split into multiple premises, and ~
                            disjunctions into multiple rules; negations ~
                            and implications are not supported.)"
                  prem rule-name (car prem)))
             ((definductive-mentions-preds-p prem names)
              (er soft ctx "The premise ~x0 of rule ~x1 is not allowed: ~
                            the predicates being defined may only appear ~
                            at the top level of premises."
                  prem rule-name))
             (t (er-let* ((term (translate prem t t nil ctx wrld state)))
                  (value (list (cons :kind :term)
                               (cons :index k)
                               (cons :form prem)
                               (cons :term term)))))))
           (rest (definductive-process-prems (cdr prems) (1+ k) rule-name
                   preds ctx wrld state)))
        (value (cons prem-info rest))))))

(defun definductive-prems-vars (prems acc)
  (if (endp prems)
      acc
    (let ((prem (car prems)))
      (definductive-prems-vars
        (cdr prems)
        (if (eq (definductive-get :kind prem) :pred)
            (definductive-term-list-vars (definductive-get :args prem) acc)
          (definductive-term-vars (definductive-get :term prem) acc))))))

(defun definductive-pred-prems (prems)
  (cond ((endp prems) nil)
        ((eq (definductive-get :kind (car prems)) :pred)
         (cons (car prems) (definductive-pred-prems (cdr prems))))
        (t (definductive-pred-prems (cdr prems)))))

(defun definductive-term-prems (prems)
  (cond ((endp prems) nil)
        ((eq (definductive-get :kind (car prems)) :term)
         (cons (car prems) (definductive-term-prems (cdr prems))))
        (t (definductive-term-prems (cdr prems)))))

(defun definductive-premise-fields (pprems rule-name)
  (if (endp pprems)
      nil
    (cons (definductive-premise-field rule-name
            (definductive-get :index (car pprems)))
          (definductive-premise-fields (cdr pprems) rule-name))))

(defun definductive-process-rule (rule preds ctx wrld state)
  (let ((names (definductive-pred-names preds)))
    (cond
     ((not (and (true-listp rule) (= (len rule) 3)))
      (er soft ctx "Each :IRULES entry must have the form ~
                    (NAME (PREM1 PREM2 ...) CONCL), but ~x0 does not."
          rule))
     ((not (and (symbolp (first rule))
                (not (keywordp (first rule)))))
      (er soft ctx "The name ~x0 of the rule ~x1 must be a non-keyword ~
                    symbol."
          (first rule) rule))
     ((not (true-listp (second rule)))
      (er soft ctx "The premises ~x0 of rule ~x1 must be a true list."
          (second rule) (first rule)))
     ((not (and (consp (third rule))
                (member-eq (car (third rule)) names)))
      (er soft ctx "The conclusion ~x0 of rule ~x1 must be a call of one ~
                    of the predicates ~&2."
          (third rule) (first rule) names))
     (t
      (let ((name (first rule))
            (prems (second rule))
            (concl (third rule)))
        (er-let* ((args (definductive-process-pred-call
                          concl "conclusion" name preds ctx wrld state))
                  (prem-infos (definductive-process-prems
                                prems 1 name preds ctx wrld state)))
          (let* ((vars (definductive-prems-vars prem-infos nil))
                 (vars (definductive-term-list-vars args vars))
                 (fields (definductive-premise-fields
                           (definductive-pred-prems prem-infos)
                           name))
                 (clash (intersection-eq vars fields)))
            (if clash
                (er soft ctx "The variables ~&0 of rule ~x1 clash with the ~
                              names of the premise proof fields."
                    clash name)
              (value (list (cons :name name)
                           (cons :prems prem-infos)
                           (cons :concl-form concl)
                           (cons :pred (car concl))
                           (cons :args args)
                           (cons :vars vars)))))))))))

(defun definductive-process-rules (rules preds ctx wrld state)
  (if (endp rules)
      (value nil)
    (er-let* ((rule (definductive-process-rule (car rules) preds
                      ctx wrld state))
              (rest (definductive-process-rules (cdr rules) preds
                      ctx wrld state)))
      (value (cons rule rest)))))

(defun definductive-rules-of (p rules)
  (cond ((endp rules) nil)
        ((eq (definductive-get :pred (car rules)) p)
         (cons (car rules) (definductive-rules-of p (cdr rules))))
        (t (definductive-rules-of p (cdr rules)))))

(defun definductive-rule-keys (rules)
  (if (endp rules)
      nil
    (cons (cons (definductive-get :pred (car rules))
                (definductive-get :name (car rules)))
          (definductive-rule-keys (cdr rules)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Dependencies, cliques, levels.

(defun definductive-prems-preds (prems)
  (cond ((endp prems) nil)
        ((eq (definductive-get :kind (car prems)) :pred)
         (add-to-set-eq (definductive-get :pred (car prems))
                        (definductive-prems-preds (cdr prems))))
        (t (definductive-prems-preds (cdr prems)))))

(defun definductive-direct-deps (p rules)
  ;; Predicates in premises of rules whose conclusion is P.
  (cond ((endp rules) nil)
        ((eq (definductive-get :pred (car rules)) p)
         (definductive-union-eq
           (definductive-direct-deps p (cdr rules))
           (definductive-prems-preds (definductive-get :prems (car rules)))))
        (t (definductive-direct-deps p (cdr rules)))))

(defun definductive-deps-of-list (ps rules)
  (if (endp ps)
      nil
    (definductive-union-eq (definductive-direct-deps (car ps) rules)
                           (definductive-deps-of-list (cdr ps) rules))))

(defun definductive-reach (frontier seen rules n)
  ;; Predicates reachable (in one or more steps) from FRONTIER.
  (if (or (zp n) (endp frontier))
      seen
    (let* ((next (definductive-deps-of-list frontier rules))
           (new (set-difference-eq next seen)))
      (definductive-reach new (definductive-union-eq seen new) rules (1- n)))))

(defun definductive-depends-on (p rules n)
  (definductive-reach (list p) nil rules n))

(defun definductive-clique-of (p names rules n)
  ;; Predicates (in the order of NAMES) mutually dependent with P, plus P.
  (cond ((endp names) nil)
        ((or (eq (car names) p)
             (and (member-eq (car names) (definductive-depends-on p rules n))
                  (member-eq p (definductive-depends-on (car names) rules n))))
         (cons (car names) (definductive-clique-of p (cdr names) rules n)))
        (t (definductive-clique-of p (cdr names) rules n))))

(defun member-equal-in-lists (x lists)
  (cond ((endp lists) nil)
        ((member-eq x (car lists)) t)
        (t (member-equal-in-lists x (cdr lists)))))

(defun definductive-all-cliques (ps names rules n acc)
  (cond ((endp ps) (reverse acc))
        ((member-equal-in-lists (car ps) acc)
         (definductive-all-cliques (cdr ps) names rules n acc))
        (t (definductive-all-cliques
             (cdr ps) names rules n
             (cons (definductive-clique-of (car ps) names rules n) acc)))))

(defun definductive-flatten (lists)
  (if (endp lists) nil (append (car lists) (definductive-flatten (cdr lists)))))

(defun definductive-pick-ready (cliques done rules)
  ;; First clique whose external dependencies are all in DONE.
  (cond ((endp cliques) nil)
        ((definductive-subsetp-eq
           (set-difference-eq (definductive-deps-of-list (car cliques) rules)
                              (car cliques))
           done)
         (car cliques))
        (t (definductive-pick-ready (cdr cliques) done rules))))

(defun definductive-order-cliques (cliques done rules n)
  (if (or (zp n) (endp cliques))
      nil
    (let ((c (definductive-pick-ready cliques done rules)))
      (if (null c)
          nil ; impossible
        (cons c (definductive-order-cliques
                  (remove-equal c cliques)
                  (append done c)
                  rules
                  (1- n)))))))

;; Levels within a clique.  LEVELS is an alist from predicates to levels.

(defun definductive-rule-ok-at-level-p (pprems clique levels l)
  ;; All premise predicates either outside the clique or at levels below L.
  (cond ((endp pprems) t)
        ((let ((q (definductive-get :pred (car pprems))))
           (or (not (member-eq q clique))
               (let ((lq (cdr (assoc-eq q levels))))
                 (and lq (< lq l)))))
         (definductive-rule-ok-at-level-p (cdr pprems) clique levels l))
        (t nil)))

(defun definductive-level-rule (rules clique levels l)
  ;; First rule (among RULES) that witnesses level L.
  (cond ((endp rules) nil)
        ((definductive-rule-ok-at-level-p
           (definductive-pred-prems (definductive-get :prems (car rules)))
           clique levels l)
         (car rules))
        (t (definductive-level-rule (cdr rules) clique levels l))))

(defun definductive-levels-round (ps clique rules levels l)
  ;; Returns new assignments at level L for the predicates PS not yet assigned.
  (cond ((endp ps) nil)
        ((assoc-eq (car ps) levels)
         (definductive-levels-round (cdr ps) clique rules levels l))
        ((definductive-level-rule (definductive-rules-of (car ps) rules)
           clique levels l)
         (cons (cons (car ps) l)
               (definductive-levels-round (cdr ps) clique rules levels l)))
        (t (definductive-levels-round (cdr ps) clique rules levels l))))

(defun definductive-levels (clique rules levels l n)
  (if (zp n)
      levels
    (let ((new (definductive-levels-round clique clique rules levels l)))
      (if (null new)
          levels
        (definductive-levels clique rules (append levels new) (1+ l) (1- n))))))

(defun definductive-unleveled (ps levels)
  (cond ((endp ps) nil)
        ((assoc-eq (car ps) levels) (definductive-unleveled (cdr ps) levels))
        (t (cons (car ps) (definductive-unleveled (cdr ps) levels)))))

(defun definductive-max-level (ps levels)
  (if (endp ps)
      0
    (max (cdr (assoc-eq (car ps) levels))
         (definductive-max-level (cdr ps) levels))))

(defun definductive-clique-recursivep (clique rules)
  (intersection-eq (definductive-deps-of-list clique rules) clique))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Names.

(defun definductive-proof-type (p) (definductive-cat-sym p "-PROOF"))
(defun definductive-proofp (p) (definductive-cat-sym p "-PROOFP"))
(defun definductive-proof-count (p) (definductive-cat-sym p "-PROOF-COUNT"))
(defun definductive-proof-kind (p) (definductive-cat-sym p "-PROOF-KIND"))
(defun definductive-proof-kind-fn (p)
  (definductive-cat-sym p "-PROOF-KIND$INLINE"))
(defun definductive-kind-possibilities (p)
  (definductive-cat-sym p "-PROOF-KIND-POSSIBILITIES"))
(defun definductive-proof-case (p) (definductive-cat-sym p "-PROOF-CASE"))
(defun definductive-validp (p) (definductive-cat-sym p "-PROOF-VALIDP"))
(defun definductive-minimalp (p) (definductive-cat-sym p "-PROOF-MINIMALP"))
(defun definductive-minimalp-witness (p)
  (definductive-cat-sym p "-PROOF-MINIMALP-WITNESS"))
(defun definductive-minimalp-necc (p)
  (definductive-cat-sym p "-PROOF-MINIMALP-NECC"))
(defun definductive-minimize (p) (definductive-cat-sym p "-PROOF-MINIMIZE"))
(defun definductive-minimize-thm (p)
  (definductive-cat-sym p "-PROOF-MINIMIZE-CORRECT"))
(defun definductive-witness (p) (definductive-cat-sym p "-PROOF"))
(defun definductive-suff (p) (definductive-cat-sym p "-SUFF"))
(defun definductive-when-validp (p)
  (definductive-cat-sym p "-WHEN-PROOF-VALIDP"))
(defun definductive-count-bound (p)
  (definductive-cat-sym p "-PROOF-COUNT-OF-WITNESS-BOUND"))
(defun definductive-induct (p) (definductive-cat-sym p "-INDUCT"))
(defun definductive-induction (p) (definductive-cat-sym p "-INDUCTION"))
(defun definductive-alt (p) (definductive-cat-sym p "-ALT"))
(defun definductive-alt-when-validp (p)
  (definductive-cat-sym2 (definductive-alt p) "-WHEN-" (definductive-validp p)))
(defun definductive-alt-when-p (p)
  (definductive-cat-sym2 (definductive-alt p) "-WHEN-" p))
(defun definductive-rule-thm (p rule-name)
  (definductive-cat-sym2 p "-" rule-name))
(defun definductive-alt-rule-thm (p rule-name)
  (definductive-cat-sym2 (definductive-alt p) "-" rule-name))
(defun definductive-ctor (p rule-name)
  (definductive-cat-sym2 (definductive-proof-type p) "-" rule-name))
(defun definductive-acc (p rule-name field)
  (definductive-cat-sym2 (definductive-ctor p rule-name) "->" field))
(defun definductive-induct-termination-thm (p rule-name k)
  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name p) "-INDUCT-TERMINATION-"
                (symbol-name rule-name) "-" (definductive-nat-str k))
   p))
(defun definductive-clique-type-name (clique)
  (definductive-cat-sym (car clique) "-PROOF-CLIQUE"))
(defun definductive-validp-flag (clique)
  (definductive-cat-sym (car clique) "-PROOF-VALIDP-CLIQUE-FLAG"))
(defun definductive-induct-flag (clique)
  (definductive-cat-sym (car clique) "-INDUCT-CLIQUE-FLAG"))
(defun definductive-defthm-flag (flag)
  (definductive-cat-sym2 'defthm "-" flag))

(defun definductive-map-names (fn ps)
  (if (endp ps)
      nil
    (cons (case fn
            (proofp (definductive-proofp (car ps)))
            (validp (definductive-validp (car ps)))
            (minimalp (definductive-minimalp (car ps)))
            (induct (definductive-induct (car ps)))
            (alt (definductive-alt (car ps)))
            (otherwise (car ps)))
          (definductive-map-names fn (cdr ps)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof tree types.

(defun definductive-var-fields (vars)
  (if (endp vars)
      nil
    (cons (list (car vars)) (definductive-var-fields (cdr vars)))))

(defun definductive-prem-fields (pprems rule-name)
  (if (endp pprems)
      nil
    (cons (list (definductive-premise-field rule-name
                  (definductive-get :index (car pprems)))
                (definductive-proof-type (definductive-get :pred (car pprems))))
          (definductive-prem-fields (cdr pprems) rule-name))))

(defun definductive-summands (rules)
  (if (endp rules)
      nil
    (let ((rule (car rules)))
      (cons (list (definductive-kwd (definductive-get :name rule))
                  (append (definductive-var-fields (definductive-get :vars rule))
                          (definductive-prem-fields
                            (definductive-pred-prems
                              (definductive-get :prems rule))
                            (definductive-get :name rule))))
            (definductive-summands (cdr rules))))))

(defun definductive-all-field-names (rules)
  (if (endp rules)
      nil
    (append (definductive-get :vars (car rules))
            (definductive-premise-fields
              (definductive-pred-prems (definductive-get :prems (car rules)))
              (definductive-get :name (car rules)))
            (definductive-all-field-names (cdr rules)))))

(defun definductive-fresh-xvar (names k)
  ;; A variable for FTY's :xvar that is not among NAMES.
  (declare (xargs :measure (nfix (- (+ 1 (len names)) k))))
  (let ((var (if (= k 0)
                 'proof
               (intern-in-package-of-symbol
                (concatenate 'string "PROOF" (definductive-nat-str k) "-X")
                'proof))))
    (if (and (member-eq var names) (< k (+ 1 (len names))))
        (definductive-fresh-xvar names (1+ k))
      var)))

(defun definductive-tagsum (p rules clique levels multilevelp xvar)
  (let* ((prules (definductive-rules-of p rules))
         (level (cdr (assoc-eq p levels)))
         (base-rule (and (> level 0)
                         (definductive-level-rule prules clique levels level))))
    `(fty::deftagsum ,(definductive-proof-type p)
       ,@(definductive-summands prules)
       :pred ,(definductive-proofp p)
       :count ,(definductive-proof-count p)
       :xvar ,xvar
       ,@(and base-rule
              `(:base-case-override
                ,(definductive-kwd (definductive-get :name base-rule))))
       ,@(and multilevelp
              `(:measure (two-nats-measure (acl2-count ,xvar) ,level))))))

(defun definductive-tagsums (ps rules clique levels multilevelp xvar)
  (if (endp ps)
      nil
    (cons (definductive-tagsum (car ps) rules clique levels multilevelp xvar)
          (definductive-tagsums (cdr ps) rules clique levels multilevelp
            xvar))))

(defun definductive-rules-of-list (ps rules)
  (if (endp ps)
      nil
    (append (definductive-rules-of (car ps) rules)
            (definductive-rules-of-list (cdr ps) rules))))

(defun definductive-clique-xvar (clique rules)
  (definductive-fresh-xvar
    (definductive-all-field-names (definductive-rules-of-list clique rules))
    0))

(defun definductive-kind-poss-use (p rules)
  ;; For a proof tree type with a single summand, the kind function, whose
  ;; definition is enabled in some proofs (it returns the only possible kind).
  (and (= (len (definductive-rules-of p rules)) 1)
       (list (definductive-proof-kind-fn p))))

(defun definductive-kind-poss-uses (ps rules)
  (if (endp ps)
      nil
    (append (definductive-kind-poss-use (car ps) rules)
            (definductive-kind-poss-uses (cdr ps) rules))))

(defun definductive-types-event (clique rules levels)
  (let* ((multilevelp (> (definductive-max-level clique levels) 0))
         (xvar (definductive-clique-xvar clique rules))
         (tagsums (definductive-tagsums clique rules clique levels
                    multilevelp xvar)))
    (if (consp (cdr clique))
        `(fty::deftypes ,(definductive-clique-type-name clique)
           ,@tagsums)
      (car tagsums))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Validity functions.

(defun definductive-var-alist (vars p rule-name proof-term)
  ;; Maps each variable of the rule to the corresponding field of PROOF-TERM.
  (if (endp vars)
      nil
    (cons (cons (car vars)
                (list (definductive-acc p rule-name (car vars)) proof-term))
          (definductive-var-alist (cdr vars) p rule-name proof-term))))

(defun definductive-sublis-list (alist terms)
  (if (endp terms)
      nil
    (cons (sublis-var alist (car terms))
          (definductive-sublis-list alist (cdr terms)))))

(defun definductive-term-conjuncts (tprems alist)
  (if (endp tprems)
      nil
    (cons (sublis-var alist (definductive-get :term (car tprems)))
          (definductive-term-conjuncts (cdr tprems) alist))))

(defun definductive-equal-conjuncts (formals args)
  (if (endp formals)
      nil
    (cons `(equal ,(car formals) ,(car args))
          (definductive-equal-conjuncts (cdr formals) (cdr args)))))

(defun definductive-premise-proof-term (p rule-name k proof-term)
  (list (definductive-acc p rule-name (definductive-premise-field rule-name k))
        proof-term))

(defun definductive-validp-conjuncts (pprems p rule-name alist proof-term)
  (if (endp pprems)
      nil
    (let ((prem (car pprems)))
      (cons `(,(definductive-validp (definductive-get :pred prem))
              ,(definductive-premise-proof-term
                 p rule-name (definductive-get :index prem) proof-term)
              ,@(definductive-sublis-list alist (definductive-get :args prem)))
            (definductive-validp-conjuncts (cdr pprems) p rule-name alist
              proof-term)))))

(defun definductive-rule-validity (rule p formals proof-term)
  ;; The validity condition of a proof tree of the kind of RULE.
  (let* ((rule-name (definductive-get :name rule))
         (alist (definductive-var-alist (definductive-get :vars rule)
                  p rule-name proof-term))
         (prems (definductive-get :prems rule)))
    `(and ,@(definductive-term-conjuncts (definductive-term-prems prems) alist)
          ,@(definductive-equal-conjuncts
              formals (definductive-sublis-list alist
                        (definductive-get :args rule)))
          ,@(definductive-validp-conjuncts (definductive-pred-prems prems)
              p rule-name alist proof-term))))

(defun definductive-validp-cases (prules p formals)
  (if (endp prules)
      nil
    (list* (definductive-kwd (definductive-get :name (car prules)))
           (definductive-rule-validity (car prules) p formals 'proof)
           (definductive-validp-cases (cdr prules) p formals))))

(defun definductive-validp-defun (p rules preds recursivep hints)
  (let ((formals (definductive-formals p preds)))
    `(defun ,(definductive-validp p) (proof ,@formals)
       (declare (xargs :guard (,(definductive-proofp p) proof)
                       :verify-guards nil
                       ,@(and hints `(:hints ,hints))
                       ,@(and recursivep
                              `(:measure (,(definductive-proof-count p)
                                          proof)
                                :well-founded-relation o<
                                :ruler-extenders :basic))))
       (,(definductive-proof-case p)
        proof
        ,@(definductive-validp-cases (definductive-rules-of p rules)
            p formals)))))

(defun definductive-validp-defuns (ps rules preds hints)
  (if (endp ps)
      nil
    (cons (definductive-validp-defun (car ps) rules preds t hints)
          (definductive-validp-defuns (cdr ps) rules preds nil))))

(defun definductive-validp-events (clique rules preds)
  (if (consp (cdr clique))
      (let* ((fns (definductive-kind-poss-uses clique rules))
             (hints (and fns `(("Goal" :in-theory (enable ,@fns))))))
        `((mutual-recursion
           ,@(definductive-validp-defuns clique rules preds hints))
          (flag::make-flag ,(definductive-validp-flag clique)
                           ,(definductive-validp (car clique))
                           ,@(and hints `(:hints ,hints)))))
    `(,(definductive-validp-defun (car clique) rules preds
         (definductive-clique-recursivep clique rules)
         nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Predicates, minimality of proof trees.

(defun definductive-pred-events (p preds)
  (let* ((formals (definductive-formals p preds))
         (proofp (definductive-proofp p))
         (validp (definductive-validp p))
         (count (definductive-proof-count p))
         (minimalp (definductive-minimalp p))
         (witness-m (definductive-minimalp-witness p))
         (minimize (definductive-minimize p))
         (minimize-thm (definductive-minimize-thm p))
         (witness (definductive-witness p))
         (bound (definductive-count-bound p)))
    `((defun-sk ,minimalp (proof ,@formals)
        (declare (xargs :verify-guards nil))
        (forall (proof2)
                (implies (and (,proofp proof2)
                              (,validp proof2 ,@formals))
                         (<= (,count proof) (,count proof2)))))
      (local (in-theory (disable ,minimalp)))
      (local
       (defun ,minimize (proof ,@formals)
         (declare (xargs :measure (,count proof)
                         :well-founded-relation o<
                         :ruler-extenders :basic
                         :verify-guards nil
                         :hints (("Goal" :in-theory (e/d (,minimalp)
                                                         (,validp))))))
         (if (and (,proofp proof)
                  (,validp proof ,@formals)
                  (not (,minimalp proof ,@formals)))
             (,minimize (,witness-m proof ,@formals) ,@formals)
           proof)))
      (local
       (defthm ,minimize-thm
         (implies (and (,proofp proof)
                       (,validp proof ,@formals))
                  (and (,proofp (,minimize proof ,@formals))
                       (,validp (,minimize proof ,@formals) ,@formals)
                       (,minimalp (,minimize proof ,@formals) ,@formals)))
         :hints (("Goal" :induct (,minimize proof ,@formals)
                  :in-theory (e/d (,minimalp) (,validp))))))
      (defun-sk ,p ,formals
        (declare (xargs :verify-guards nil))
        (exists (proof) (and (,proofp proof)
                             (,validp proof ,@formals)
                             (,minimalp proof ,@formals)))
        :skolem-name ,witness)
      (local (in-theory (disable ,p)))
      (defthm ,(definductive-when-validp p)
        (implies (and (,validp proof ,@formals)
                      (,proofp proof))
                 (,p ,@formals))
        :hints (("Goal"
                 :in-theory (theory 'minimal-theory)
                 :use ((:instance ,(definductive-suff p)
                        (proof (,minimize proof ,@formals)))
                       (:instance ,minimize-thm)))))
      (local
       (defthm ,(definductive-cat-sym p "-WITNESS-MINIMAL")
         (implies (,p ,@formals)
                  (,minimalp (,witness ,@formals) ,@formals))
         :rule-classes nil
         :hints (("Goal"
                  :in-theory (union-theories
                              '(,p (:type-prescription ,minimalp)
                                   (:type-prescription ,validp))
                              (theory 'minimal-theory))))))
      (local
       (defthm ,bound
         (implies (and (,proofp proof)
                       (,validp proof ,@formals))
                  (<= (,count (,witness ,@formals)) (,count proof)))
         :rule-classes nil
         :hints (("Goal"
                  :in-theory (theory 'minimal-theory)
                  :use ((:instance ,(definductive-when-validp p))
                        (:instance ,(definductive-cat-sym p "-WITNESS-MINIMAL"))
                        (:instance ,(definductive-minimalp-necc p)
                         (proof (,witness ,@formals))
                         (proof2 proof))))))))))

(defun definductive-preds-events (ps preds)
  (if (endp ps)
      nil
    (append (definductive-pred-events (car ps) preds)
            (definductive-preds-events (cdr ps) preds))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Inference rule theorems.

(defun definductive-implies-form (hyps concl)
  (cond ((endp hyps) concl)
        ((endp (cdr hyps)) `(implies ,(car hyps) ,concl))
        (t `(implies (and ,@hyps) ,concl))))

(defun definductive-prem-forms (prems)
  (if (endp prems)
      nil
    (cons (definductive-get :form (car prems))
          (definductive-prem-forms (cdr prems)))))

(defun definductive-rename-preds (x alist)
  ;; Replace the predicate (in function position at the top level) by the
  ;; corresponding one in ALIST.
  (if (and (consp x) (assoc-eq (car x) alist))
      (cons (cdr (assoc-eq (car x) alist)) (cdr x))
    x))

(defun definductive-rename-preds-list (xs alist)
  (if (endp xs)
      nil
    (cons (definductive-rename-preds (car xs) alist)
          (definductive-rename-preds-list (cdr xs) alist))))

(defun definductive-witness-args (pprems)
  ;; For each predicate premise, (q-proof args...) with untranslated args.
  (if (endp pprems)
      nil
    (cons (cons (definductive-witness (definductive-get :pred (car pprems)))
                (cdr (definductive-get :form (car pprems))))
          (definductive-witness-args (cdr pprems)))))

(defun definductive-expand-prems (pprems)
  (definductive-prem-forms pprems))

(defun definductive-rule-thm-event (rule preds)
  (let* ((p (definductive-get :pred rule))
         (rule-name (definductive-get :name rule))
         (formals (definductive-formals p preds))
         (prems (definductive-get :prems rule))
         (pprems (definductive-pred-prems prems))
         (vars (definductive-get :vars rule))
         (concl (definductive-get :concl-form rule))
         (proof-term `(,(definductive-ctor p rule-name)
                       ,@vars
                       ,@(definductive-witness-args pprems)))
         (pnames (definductive-pred-names preds)))
    `(defthm ,(definductive-rule-thm p rule-name)
       ,(definductive-implies-form (definductive-prem-forms prems) concl)
       :hints (("Goal"
                :in-theory (e/d (,@(remove-duplicates-eq
                                    (definductive-map-names 'validp pnames)))
                                (,@pnames))
                ,@(and pprems
                       `(:expand ,(definductive-expand-prems pprems)))
                :use ((:instance ,(definductive-when-validp p)
                       (proof ,proof-term)
                       ,@(definductive-doublets formals (cdr concl)))))
               (and stable-under-simplificationp
                    '(:expand ((,(definductive-validp p)
                                ,proof-term ,@(cdr concl)))))))))

(defun definductive-rule-thm-events (rules preds)
  (if (endp rules)
      nil
    (cons (definductive-rule-thm-event (car rules) preds)
          (definductive-rule-thm-events (cdr rules) preds))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Rule induction.

(defun definductive-case-hyps (tag all-tags kind-term)
  ;; The tests under which (p-proof-case ...) selects the case TAG:
  ;; the negations of the tests of the preceding cases, and the test of TAG
  ;; unless it is the last case.
  (cond ((endp all-tags) nil)
        ((eq (car all-tags) tag)
         (if (endp (cdr all-tags))
             nil
           (list `(eql ,kind-term ,tag))))
        (t (cons `(not (eql ,kind-term ,(car all-tags)))
                 (definductive-case-hyps tag (cdr all-tags) kind-term)))))

(defun definductive-rule-tags (rules)
  (if (endp rules)
      nil
    (cons (definductive-kwd (definductive-get :name (car rules)))
          (definductive-rule-tags (cdr rules)))))

(defun definductive-termination-thms (pprems rule p formals clique all-tags
                                             preds rules)
  ;; One theorem for each premise of RULE whose predicate is in CLIQUE.
  (if (endp pprems)
      nil
    (let ((prem (car pprems)))
      (if (not (member-eq (definductive-get :pred prem) clique))
          (definductive-termination-thms (cdr pprems) rule p formals clique
            all-tags preds rules)
        (let* ((q (definductive-get :pred prem))
               (rule-name (definductive-get :name rule))
               (witness `(,(definductive-witness p) ,@formals))
               (alist (definductive-var-alist (definductive-get :vars rule)
                        p rule-name witness))
               (args (definductive-sublis-list alist
                       (definductive-get :args prem)))
               (k (definductive-get :index prem))
               (kind-term `(,(definductive-proof-kind p) ,witness)))
          (cons
           `(local
             (defthm ,(definductive-induct-termination-thm p rule-name k)
               (implies (and (,p ,@formals)
                             ,@(definductive-case-hyps
                                 (definductive-kwd rule-name)
                                 all-tags kind-term))
                        (o< (,(definductive-proof-count q)
                             (,(definductive-witness q) ,@args))
                            (,(definductive-proof-count p) ,witness)))
               :hints (("Goal"
                        :in-theory (enable ,p
                                           ,@(definductive-kind-poss-use
                                               p rules))
                        :expand ((,(definductive-validp p) ,witness ,@formals))
                        :use ((:instance ,(definductive-count-bound q)
                               (proof ,(definductive-premise-proof-term
                                         p rule-name k witness))
                               ,@(definductive-doublets
                                   (definductive-formals q preds)
                                   args)))))))
           (definductive-termination-thms (cdr pprems) rule p formals clique
             all-tags preds rules)))))))

(defun definductive-termination-thms-rules (prules p formals clique all-tags
                                                   preds rules)
  (if (endp prules)
      nil
    (append (definductive-termination-thms
              (definductive-pred-prems (definductive-get :prems (car prules)))
              (car prules) p formals clique all-tags preds rules)
            (definductive-termination-thms-rules (cdr prules) p formals clique
              all-tags preds rules))))

(defun definductive-termination-thms-clique (ps clique rules preds)
  (if (endp ps)
      nil
    (let ((prules (definductive-rules-of (car ps) rules)))
      (append (definductive-termination-thms-rules
                prules (car ps) (definductive-formals (car ps) preds) clique
                (definductive-rule-tags prules) preds rules)
              (definductive-termination-thms-clique (cdr ps) clique rules
                preds)))))

(defun definductive-termination-names (events)
  (if (endp events)
      nil
    (cons (cadr (cadr (car events))) ; (local (defthm name ...))
          (definductive-termination-names (cdr events)))))

(defun definductive-induct-calls (pprems rule p clique)
  (if (endp pprems)
      nil
    (let ((prem (car pprems)))
      (if (member-eq (definductive-get :pred prem) clique)
          (let* ((alist (definductive-var-alist (definductive-get :vars rule)
                          p (definductive-get :name rule) 'proof)))
            (cons `(,(definductive-induct (definductive-get :pred prem))
                    ,@(definductive-sublis-list alist
                        (definductive-get :args prem)))
                  (definductive-induct-calls (cdr pprems) rule p clique)))
        (definductive-induct-calls (cdr pprems) rule p clique)))))

(defun definductive-induct-cases (prules p clique)
  (if (endp prules)
      nil
    (let ((calls (definductive-induct-calls
                   (definductive-pred-prems
                     (definductive-get :prems (car prules)))
                   (car prules) p clique)))
      (list* (definductive-kwd (definductive-get :name (car prules)))
             (cond ((endp calls) nil)
                   ((endp (cdr calls)) (car calls))
                   (t `(list ,@calls)))
             (definductive-induct-cases (cdr prules) p clique)))))

(defun definductive-induct-defun (p clique rules preds recursivep hints)
  (let ((formals (definductive-formals p preds)))
    `(defun ,(definductive-induct p) ,formals
       (declare (xargs ,@(and recursivep
                              `(:measure (,(definductive-proof-count p)
                                          (,(definductive-witness p)
                                           ,@formals))
                                :well-founded-relation o<
                                :ruler-extenders :basic))
                       ,@(and hints `(:hints ,hints))
                       :verify-guards nil))
       (and (,p ,@formals)
            (let ((proof (,(definductive-witness p) ,@formals)))
              (,(definductive-proof-case p)
               proof
               ,@(definductive-induct-cases (definductive-rules-of p rules)
                   p clique)))))))

(defun definductive-induct-defuns (ps clique rules preds hints)
  (if (endp ps)
      nil
    (cons (definductive-induct-defun (car ps) clique rules preds t hints)
          (definductive-induct-defuns (cdr ps) clique rules preds nil))))

(defun definductive-o-p-thms (ps)
  (if (endp ps)
      nil
    (cons `(local (defthm ,(definductive-cat-sym (car ps) "-PROOF-COUNT-O-P")
                    (o-p (,(definductive-proof-count (car ps)) proof))))
          (definductive-o-p-thms (cdr ps)))))

(defun definductive-induct-events (clique rules preds)
  ;; The termination of the induction functions is proved by rewriting with
  ;; the termination theorems (one per recursive call), whose hypotheses are
  ;; exactly the rulers of the calls.
  (let* ((recursivep (definductive-clique-recursivep clique rules))
         (thms (append (definductive-termination-thms-clique clique clique
                         rules preds)
                       (and recursivep (definductive-o-p-thms clique))))
         (hints (and thms
                     `(("Goal"
                        :in-theory (union-theories
                                    '(,@(definductive-termination-names thms))
                                    (theory 'minimal-theory)))))))
    (if (consp (cdr clique))
        `(,@thms
          (mutual-recursion
           ,@(definductive-induct-defuns clique clique rules preds hints))
          (flag::make-flag ,(definductive-induct-flag clique)
                           ,(definductive-induct (car clique))
                           :hints ,hints))
      (let ((p (car clique)))
        `(,@thms
          ,(definductive-induct-defun p clique rules preds recursivep hints)
          ,@(and recursivep
                 `((defthm ,(definductive-induction p)
                     t
                     :rule-classes
                     ((:induction
                       :pattern (,p ,@(definductive-formals p preds))
                       :scheme (,(definductive-induct p)
                                ,@(definductive-formals p preds))))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Alternative predicates and minimality theorems.

(defun definductive-alt-alist (pnames)
  (if (endp pnames)
      nil
    (cons (cons (car pnames) (definductive-alt (car pnames)))
          (definductive-alt-alist (cdr pnames)))))

(defun definductive-alt-signatures (preds)
  (if (endp preds)
      nil
    (cons `((,(definductive-alt (definductive-get :name (car preds)))
             ,@(make-list (len (definductive-get :formals (car preds)))
                          :initial-element '*))
            => *)
          (definductive-alt-signatures (cdr preds)))))

(defun definductive-alt-local-defuns (preds)
  (if (endp preds)
      nil
    (let ((p (definductive-get :name (car preds)))
          (formals (definductive-get :formals (car preds))))
      (cons `(local (defun ,(definductive-alt p) ,formals
                      (declare (xargs :verify-guards nil))
                      (,p ,@formals)))
            (definductive-alt-local-defuns (cdr preds))))))

(defun definductive-alt-rule-thms (rules alist)
  (if (endp rules)
      nil
    (let* ((rule (car rules))
           (p (definductive-get :pred rule))
           (rule-name (definductive-get :name rule)))
      (cons `(defthm ,(definductive-alt-rule-thm p rule-name)
               ,(definductive-implies-form
                  (definductive-rename-preds-list
                    (definductive-prem-forms (definductive-get :prems rule))
                    alist)
                  (definductive-rename-preds (definductive-get :concl-form rule)
                    alist))
               :hints (("Goal"
                        :in-theory (union-theories
                                    '(,@(strip-cdrs alist))
                                    (theory 'minimal-theory))
                        :use (,(definductive-rule-thm p rule-name)))))
            (definductive-alt-rule-thms (cdr rules) alist)))))

(defun definductive-alt-encapsulate (preds rules)
  (let ((alist (definductive-alt-alist (definductive-pred-names preds))))
    `(encapsulate
       ,(definductive-alt-signatures preds)
       ,@(definductive-alt-local-defuns preds)
       ,@(definductive-alt-rule-thms rules alist))))

;; Computed hint for the proofs of the p-alt-when-p-proof-validp theorems.
;; CASES is a list of entries (KIND-TERM TAG ALL-TAGS . HINT), where KIND-TERM
;; is (p-proof-kind proof), TAG is the tag of a summand, ALL-TAGS are all the
;; tags of that type, and HINT is the hint (keyword list) to use for the case
;; of TAG.  A case is recognized by the presence of a literal saying that
;; KIND-TERM is TAG, or by the presence of literals saying that KIND-TERM is
;; not any of the other tags.

(defun definductive-kind-test-p (lit kind-term tag)
  ;; LIT is (equal KIND-TERM 'TAG) or (eql ...) or symmetric.
  (and (consp lit)
       (member-eq (ffn-symb lit) '(equal eql))
       (consp (cdr lit))
       (consp (cddr lit))
       (or (and (equal (fargn lit 1) kind-term)
                (equal (fargn lit 2) (kwote tag)))
           (and (equal (fargn lit 2) kind-term)
                (equal (fargn lit 1) (kwote tag))))))

(defun definductive-clause-has-kind-hyp (clause kind-term tag)
  ;; Literal (not (equal KIND-TERM 'TAG)) is present.
  (cond ((endp clause) nil)
        ((and (consp (car clause))
              (eq (ffn-symb (car clause)) 'not)
              (definductive-kind-test-p (fargn (car clause) 1) kind-term tag))
         t)
        (t (definductive-clause-has-kind-hyp (cdr clause) kind-term tag))))

(defun definductive-clause-has-not-kind-hyp (clause kind-term tag)
  ;; Literal (equal KIND-TERM 'TAG) is present.
  (cond ((endp clause) nil)
        ((definductive-kind-test-p (car clause) kind-term tag) t)
        (t (definductive-clause-has-not-kind-hyp (cdr clause) kind-term tag))))

(defun definductive-clause-excludes-all (clause kind-term tags tag)
  (cond ((endp tags) t)
        ((eq (car tags) tag)
         (definductive-clause-excludes-all clause kind-term (cdr tags) tag))
        ((definductive-clause-has-not-kind-hyp clause kind-term (car tags))
         (definductive-clause-excludes-all clause kind-term (cdr tags) tag))
        (t nil)))

(mutual-recursion
 (defun definductive-occurs-p (sub term)
   (cond ((equal sub term) t)
         ((variablep term) nil)
         ((fquotep term) nil)
         (t (definductive-occurs-list-p sub (fargs term)))))
 (defun definductive-occurs-list-p (sub terms)
   (cond ((endp terms) nil)
         (t (or (definductive-occurs-p sub (car terms))
                (definductive-occurs-list-p sub (cdr terms)))))))

(defun definductive-case-applies-p (clause kind-term tag all-tags)
  (and (not (definductive-clause-has-not-kind-hyp clause kind-term tag))
       (or (endp (cdr all-tags))
       (or (definductive-clause-has-kind-hyp clause kind-term tag)
           (and (definductive-occurs-list-p kind-term clause)
                (definductive-clause-excludes-all clause kind-term all-tags
                  tag))))))

(defun definductive-collect-uses (clause cases)
  (cond ((endp cases) nil)
        ((let ((c (car cases)))
           (definductive-case-applies-p clause (first c) (second c) (third c)))
         (append (cdddr (car cases))
                 (definductive-collect-uses clause (cdr cases))))
        (t (definductive-collect-uses clause (cdr cases)))))

(defun definductive-alt-hint (clause cases)
  (let ((uses (definductive-collect-uses clause cases)))
    (and uses
         `(:use ,uses))))

(defun definductive-alt-case-uses (pprems p rule-name proof-term clique)
  ;; For premises from earlier cliques, the instances of the theorems
  ;; q-alt-when-q-proof-validp.
  (if (endp pprems)
      nil
    (let ((prem (car pprems)))
      (if (member-eq (definductive-get :pred prem) clique)
          (definductive-alt-case-uses (cdr pprems) p rule-name proof-term
            clique)
        (let* ((q (definductive-get :pred prem)))
          (cons (list* :instance
                       (definductive-alt-when-validp q)
                       (list 'proof (definductive-premise-proof-term
                                      p rule-name
                                      (definductive-get :index prem)
                                      proof-term))
                       (definductive-doublets
                         (definductive-get :q-formals prem)
                         (definductive-sublis-list
                           (definductive-var-alist
                             (definductive-get :vars prem)
                             p rule-name proof-term)
                           (definductive-get :args prem))))
                (definductive-alt-case-uses (cdr pprems) p rule-name
                  proof-term clique)))))))

(defun definductive-annotate-prems (pprems vars preds)
  ;; Add :q-formals and :vars to the predicate premises.
  (if (endp pprems)
      nil
    (cons (list* (cons :q-formals
                       (definductive-formals
                         (definductive-get :pred (car pprems)) preds))
                 (cons :vars vars)
                 (car pprems))
          (definductive-annotate-prems (cdr pprems) vars preds))))

(defun definductive-alt-cases (prules p all-tags clique preds)
  (if (endp prules)
      nil
    (let* ((rule (car prules))
           (rule-name (definductive-get :name rule))
           (vars (definductive-get :vars rule))
           (alist (definductive-var-alist vars p rule-name 'proof))
           (pprems (definductive-annotate-prems
                     (definductive-pred-prems (definductive-get :prems rule))
                     vars preds))
           (uses (cons `(:instance ,(definductive-alt-rule-thm p rule-name)
                         ,@(definductive-doublets vars (strip-cdrs alist)))
                       (definductive-alt-case-uses pprems p rule-name 'proof
                         clique))))
      (cons (list* `(,(definductive-proof-kind-fn p) proof)
                   (definductive-kwd rule-name)
                   all-tags
                   uses)
            (definductive-alt-cases (cdr prules) p all-tags clique preds)))))

(defun definductive-alt-cases-clique (ps clique rules preds)
  (if (endp ps)
      nil
    (let ((prules (definductive-rules-of (car ps) rules)))
      (append (definductive-alt-cases prules (car ps)
                (definductive-rule-tags prules) clique preds)
              (definductive-alt-cases-clique (cdr ps) clique rules preds)))))

(defun definductive-alt-when-validp-thm (p preds)
  (let ((formals (definductive-formals p preds)))
    `(defthm ,(definductive-alt-when-validp p)
       (implies (,(definductive-validp p) proof ,@formals)
                (,(definductive-alt p) ,@formals)))))

(defun definductive-alt-when-validp-flag-thms (ps preds)
  (if (endp ps)
      nil
    (cons (append (definductive-alt-when-validp-thm (car ps) preds)
                  `(:flag ,(definductive-validp (car ps))))
          (definductive-alt-when-validp-flag-thms (cdr ps) preds))))

(defun definductive-validp-expands (ps preds)
  (if (endp ps)
      nil
    (cons `(,(definductive-validp (car ps)) proof
            ,@(definductive-formals (car ps) preds))
          (definductive-validp-expands (cdr ps) preds))))

(defun definductive-alt-rule-thm-names (rules)
  (if (endp rules)
      nil
    (cons (definductive-alt-rule-thm (definductive-get :pred (car rules))
            (definductive-get :name (car rules)))
          (definductive-alt-rule-thm-names (cdr rules)))))

(defun definductive-alt-when-validp-names (ps)
  (if (endp ps)
      nil
    (cons (definductive-alt-when-validp (car ps))
          (definductive-alt-when-validp-names (cdr ps)))))

(defun definductive-alt-when-validp-events (clique rules preds prev)
  ;; PREV are the predicates in the preceding cliques.
  (let* ((cases (definductive-alt-cases-clique clique clique rules preds))
         (recursivep (definductive-clique-recursivep clique rules))
         (hints-after-induction
          `((and stable-under-simplificationp
                 (definductive-alt-hint clause ',cases))))
         ;; The constraints on the alternative predicates, and the theorems
         ;; for the preceding cliques, are used only via the :use hints
         ;; generated by the computed hint above.
         (disabled `(,@(definductive-alt-rule-thm-names rules)
                     ,@(definductive-alt-when-validp-names prev))))
    (if (consp (cdr clique))
        `((,(definductive-defthm-flag (definductive-validp-flag clique))
           ,@(definductive-alt-when-validp-flag-thms clique preds)
           :hints (("Goal" :expand ,(definductive-validp-expands clique preds)
                    :in-theory (disable ,@disabled))
                   ,@hints-after-induction)))
      (let ((p (car clique)))
        `((defthm ,(definductive-alt-when-validp p)
            (implies (,(definductive-validp p) proof
                      ,@(definductive-formals p preds))
                     (,(definductive-alt p) ,@(definductive-formals p preds)))
            :hints (("Goal"
                     ,@(and recursivep
                            `(:induct (,(definductive-validp p) proof
                                       ,@(definductive-formals p preds))))
                     :expand ,(definductive-validp-expands clique preds)
                     :in-theory (disable ,@disabled))
                    ,@hints-after-induction)))))))


(defun definductive-alt-when-p-thm (p preds)
  (let ((formals (definductive-formals p preds)))
    `(defthm ,(definductive-alt-when-p p)
       (implies (,p ,@formals) (,(definductive-alt p) ,@formals))
       :hints (("Goal"
                ;; The type prescriptions are needed because the definition
                ;; rule of P may omit conjuncts that are known to be true by
                ;; type reasoning.
                :in-theory (union-theories
                            '(,p (:type-prescription ,(definductive-validp p))
                                 (:type-prescription ,(definductive-minimalp p)))
                            (theory 'minimal-theory))
                :use ((:instance ,(definductive-alt-when-validp p)
                       (proof (,(definductive-witness p) ,@formals)))))))))

(defun definductive-alt-when-p-thms (ps preds)
  (if (endp ps)
      nil
    (cons (definductive-alt-when-p-thm (car ps) preds)
          (definductive-alt-when-p-thms (cdr ps) preds))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Top level.

(defun definductive-clique-events (cliques rules preds)
  ;; Proof types, validity, predicates, for each clique in order.
  (if (endp cliques)
      nil
    (let* ((clique (car cliques))
           (levels (definductive-levels clique rules nil 0 (1+ (len clique)))))
      (append (list (definductive-types-event clique rules levels))
              (definductive-validp-events clique rules preds)
              (definductive-preds-events clique preds)
              (definductive-clique-events (cdr cliques) rules preds)))))

(defun definductive-induct-events-cliques (cliques rules preds)
  (if (endp cliques)
      nil
    (append (definductive-induct-events (car cliques) rules preds)
            (definductive-induct-events-cliques (cdr cliques) rules preds))))

(defun definductive-alt-when-validp-events-cliques (cliques rules preds prev)
  (if (endp cliques)
      nil
    (append (definductive-alt-when-validp-events (car cliques) rules preds
              prev)
            (definductive-alt-when-p-thms (car cliques) preds)
            (definductive-alt-when-validp-events-cliques (cdr cliques) rules
              preds (append prev (car cliques))))))

(defun definductive-check-levels (cliques rules ctx state)
  (if (endp cliques)
      (value nil)
    (let* ((clique (car cliques))
           (levels (definductive-levels clique rules nil 0 (1+ (len clique))))
           (bad (definductive-unleveled clique levels)))
      (if bad
          (er soft ctx "The predicate~#0~[~/s~] ~&0 cannot be assigned a ~
                        level: every inference rule with ~#0~[it~/them~] in ~
                        the conclusion has a premise with ~#0~[it~/one of ~
                        them~] (or with another predicate that cannot be ~
                        assigned a level).  Thus, there are no finite proof ~
                        trees for ~#0~[it~/them~], and the proof tree ~
                        type~#0~[~/s~] would be empty."
              bad)
        (definductive-check-levels (cdr cliques) rules ctx state)))))

(defconst *definductive-keywords* '(:preds :irules :parents :short :long
                                           :verbose))

(defun definductive-check-keyword-args (args ctx state)
  (cond ((null args) (value nil))
        ((not (and (consp args) (consp (cdr args))))
         (er soft ctx "The arguments after the name must be a keyword/value ~
                       list, but they end with ~x0."
             args))
        ((not (member-eq (car args) *definductive-keywords*))
         (er soft ctx "Unknown keyword ~x0; the allowed keywords are ~&1."
             (car args) *definductive-keywords*))
        ((assoc-keyword (car args) (cddr args))
         (er soft ctx "Duplicate keyword ~x0." (car args)))
        (t (definductive-check-keyword-args (cddr args) ctx state))))

(defun definductive-fn (name args state)
  (let ((ctx (cons 'definductive name))
        (wrld (w state)))
    (er-progn
     (if (and (symbolp name) name (not (keywordp name)))
         (value nil)
       (er soft ctx "The name ~x0 must be a non-keyword symbol." name))
     (definductive-check-keyword-args args ctx state)
     (let ((preds-in (cadr (assoc-keyword :preds args)))
           (irules-in (cadr (assoc-keyword :irules args)))
           (verbose (cadr (assoc-keyword :verbose args)))
           (xdoc-args (append
                       (let ((x (assoc-keyword :parents args)))
                         (and x (list :parents (cadr x))))
                       (let ((x (assoc-keyword :short args)))
                         (and x (list :short (cadr x))))
                       (let ((x (assoc-keyword :long args)))
                         (and x (list :long (cadr x)))))))
       (cond
        ((not (and (true-listp preds-in) (consp preds-in)))
         (er soft ctx "The :PREDS input must be a non-empty list, but it is ~
                       ~x0."
             preds-in))
        ((not (true-listp irules-in))
         (er soft ctx "The :IRULES input must be a list, but it is ~x0."
             irules-in))
        (t
         (er-let* ((preds (definductive-process-preds preds-in ctx wrld state)))
           (let ((names (definductive-pred-names preds)))
             (if (not (no-duplicatesp-eq names))
                 (er soft ctx "The predicates ~x0 must be distinct." names)
               (er-let* ((rules (definductive-process-rules irules-in preds
                                  ctx wrld state)))
                 (if (not (no-duplicatesp-equal
                           (definductive-rule-keys rules)))
                     (er soft ctx "Rules with the same conclusion predicate ~
                                   must have distinct names.")
                   (let* ((n (1+ (len names)))
                          (cliques (definductive-all-cliques
                                     names names rules n nil))
                          (cliques (definductive-order-cliques
                                     cliques nil rules (1+ (len cliques)))))
                     (er-progn
                      (definductive-check-levels cliques rules ctx state)
                      (let ((events
                             `(encapsulate
                                ()
                                (local (in-theory *definductive-base-theory*))
                                (local (set-default-hints nil))
                                (local (set-override-hints nil))
                                ,@(definductive-clique-events cliques rules
                                    preds)
                                ,@(definductive-rule-thm-events rules preds)
                                ,@(definductive-induct-events-cliques
                                    cliques rules preds)
                                ,(definductive-alt-encapsulate preds rules)
                                ,@(definductive-alt-when-validp-events-cliques
                                    cliques rules preds nil)
                                (in-theory
                                 (disable
                                  ,@names
                                  ,@(definductive-map-names 'minimalp
                                      names)))
                                ,@(and xdoc-args
                                       `((xdoc::defxdoc ,name ,@xdoc-args))))))
                        (value (if verbose
                                   events
                                 `(with-output
                                    :off :all
                                    :on (error)
                                    :gag-mode nil
                                    ,events)))))))))))))))))

(defmacro definductive (name &rest args)
  `(make-event (definductive-fn ',name ',args state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The fixed theory in which the generated proofs are carried out:
;; the current theory at the end of this book, at certification time.

(logic)

(make-event
 `(defconst *definductive-base-theory*
    ',(current-theory-fn :here (w state))))
