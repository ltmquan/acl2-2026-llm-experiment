; Smtlink 3 (reimplementation) -- top-level book
;
; Usage:
;
;   (include-book "smtlink" :ttags ((:smtlink)))
;
;   (defthm foo
;     ...
;     :hints (("Goal" :smtlink (:translation-theory <theory expression>
;                               [:types (recognizer ...)]
;                               [:hypothesize (term ...)]
;                               [:print t]
;                               [:max-rounds n]
;                               [:simplify-theory <theory expression>]
;                               [:smt-file "file.smt2"]
;                               [:smt-solver "z3"]))))
;
; The :smtlink hint enters a chain of clause processors (Figure 1 of the
; paper), driven by the computed hint SMTLINK-DRIVER, which is installed as
; a default hint:
;
;   entry -> type inference -> type fixing -> term rewriting --(changed)--+
;              ^                                   |                       |
;              +-----------------------------------|-----------------------+
;                                                  | (unchanged)
;                                                  v
;            type extraction -> simplification -> trusted SMT clause processor
;
; Type inference, term rewriting and simplification use REWRITE$, which
; cannot be called from a clause processor.  As described in Section 5.1, the
; computed hint calls REWRITE$ and passes its result as the hint of the next
; (verified) clause processor, which generates a side goal validating it.

(in-package "SMT")
(include-book "tools/rewrite-dollar" :dir :system)
(include-book "base")
(include-book "cps")
(include-book "smt-theory")
(include-book "trusted" :ttags ((:smtlink)))

(program)
(set-state-ok t)

; ----------------------------------------------------------------------
; Entry: putting the goal in clause form

(defun negate-lit (x)
  (dumb-negate-lit x))

(mutual-recursion
 (defun flatten-lit (lit)
   ;; a list of literals whose disjunction is equivalent to lit
   (cond ((equal lit *nil*) nil)
         ((variablep lit) (list lit))
         ((fquotep lit) (list lit))
         ((and (eq (ffn-symb lit) 'implies) (equal (len (fargs lit)) 2))
          (append (flatten-lit (negate-lit (fargn lit 1)))
                  (flatten-lit (fargn lit 2))))
         ((and (eq (ffn-symb lit) 'if) (equal (fargn lit 2) *t*))
          ;; (or a c)
          (append (flatten-lit (fargn lit 1))
                  (flatten-lit (fargn lit 3))))
         ((and (eq (ffn-symb lit) 'if) (equal (fargn lit 3) *t*))
          ;; (implies a b)
          (append (flatten-lit (negate-lit (fargn lit 1)))
                  (flatten-lit (fargn lit 2))))
         ((and (eq (ffn-symb lit) 'not)
               (consp (fargn lit 1))
               (eq (ffn-symb (fargn lit 1)) 'if)
               (equal (fargn (fargn lit 1) 3) *nil*))
          ;; (not (and a b))
          (append (flatten-lit (negate-lit (fargn (fargn lit 1) 1)))
                  (flatten-lit (negate-lit (fargn (fargn lit 1) 2)))))
         ((and (eq (ffn-symb lit) 'not)
               (consp (fargn lit 1))
               (eq (ffn-symb (fargn lit 1)) 'not))
          (flatten-lit (fargn (fargn lit 1) 1)))
         (t (list lit))))
 (defun flatten-lits (lits)
   (if (endp lits)
       nil
     (append (flatten-lit (car lits))
             (flatten-lits (cdr lits))))))

(defun remove-duplicate-lits (lits acc)
  (cond ((endp lits) (reverse acc))
        ((member-equal (car lits) acc) (remove-duplicate-lits (cdr lits) acc))
        (t (remove-duplicate-lits (cdr lits) (cons (car lits) acc)))))

; ----------------------------------------------------------------------
; Printing

(defun print-lits (title lits config)
  (if (info-get :print config)
      (cw "~%Smtlink: ~s0:~%~x1~%" title
          (if (and (consp lits) (null (cdr lits)))
              (car lits)
            (cons 'or lits)))
    nil))

; ----------------------------------------------------------------------
; Type inference (Section 5.2)

(defun path-hyps-term (pc concl)
  (if (endp pc)
      concl
    (list 'if (conjoin (reverse pc)) concl *t*)))

(defun ti-checks (id x types)
  (if (endp types)
      nil
    (let ((rx (list (car types) x)))
      (cons `(ti-equal (hide (cdr (cons ',id ,rx))) ,rx)
            (ti-checks id x (cdr types))))))

(mutual-recursion
 (defun ti-enumerate (term pc id acc)
   ;; returns (mv next-id acc); acc collects (id term pc), preorder
   (let ((acc (cons (list id term pc) acc))
         (id (1+ id)))
     (cond ((or (variablep term) (fquotep term) (flambdap (ffn-symb term)))
            (mv id acc))
           ((and (eq (ffn-symb term) 'if) (equal (len (fargs term)) 3))
            (let ((test (fargn term 1)))
              (mv-let (id acc)
                (ti-enumerate test pc id acc)
                (mv-let (id acc)
                  (ti-enumerate (fargn term 2) (cons test pc) id acc)
                  (ti-enumerate (fargn term 3) (cons (list 'not test) pc)
                                id acc)))))
           (t (ti-enumerate-list (fargs term) pc id acc)))))
 (defun ti-enumerate-list (terms pc id acc)
   (if (endp terms)
       (mv id acc)
     (mv-let (id acc)
       (ti-enumerate (car terms) pc id acc)
       (ti-enumerate-list (cdr terms) pc id acc)))))

(defun ti-big-term (entries types acc)
  (if (endp entries)
      (conjoin (reverse acc))
    (let* ((e (car entries))
           (id (car e)) (x (cadr e)) (pc (caddr e)))
      (ti-big-term (cdr entries) types
                   (cons (path-hyps-term pc (conjoin (ti-checks id x types)))
                         acc)))))

(mutual-recursion
 (defun ti-collect (term acc)
   ;; collect (id . r) for each (ti-equal (hide (cdr (cons 'id (r x)))) 't)
   (cond ((or (variablep term) (fquotep term)) acc)
         ((and (eq (ffn-symb term) 'ti-equal)
               (equal (fargn term 2) *t*))
          (let ((h (fargn term 1)))
            (if (and (consp h) (eq (car h) 'hide)
                     (consp (cadr h)) (eq (car (cadr h)) 'cdr)
                     (consp (cadr (cadr h))) (eq (car (cadr (cadr h))) 'cons)
                     (quotep (cadr (cadr (cadr h))))
                     (consp (caddr (cadr (cadr h)))))
                (cons (cons (unquote (cadr (cadr (cadr h))))
                            (car (caddr (cadr (cadr h)))))
                      acc)
              acc)))
         ((flambdap (ffn-symb term)) acc)
         (t (ti-collect-list (fargs term) acc))))
 (defun ti-collect-list (terms acc)
   (if (endp terms)
       acc
     (ti-collect-list (cdr terms) (ti-collect (car terms) acc)))))

(defun ti-judgements-of (id proved acc)
  (cond ((endp proved) (set::mergesort acc))
        ((equal (caar proved) id)
         (ti-judgements-of id (cdr proved)
                           (cons (make-judgement (cdar proved)) acc)))
        (t (ti-judgements-of id (cdr proved) acc))))

(mutual-recursion
 (defun ti-build (term id proved)
   ;; same traversal order as ti-enumerate; returns (mv node next-id)
   (let ((js (ti-judgements-of id proved nil))
         (id (1+ id)))
     (cond ((variablep term) (mv (make-tt js nil (list :var term)) id))
           ((fquotep term) (mv (make-tt js nil (list :quote (unquote term))) id))
           ((flambdap (ffn-symb term)) (mv (make-tt js nil (list :lambda term)) id))
           (t (mv-let (args id)
                (ti-build-list (fargs term) id proved)
                (mv (make-tt js nil (list* :fncall (ffn-symb term) args)) id))))))
 (defun ti-build-list (terms id proved)
   (if (endp terms)
       (mv nil id)
     (mv-let (node id)
       (ti-build (car terms) id proved)
       (mv-let (nodes id)
         (ti-build-list (cdr terms) id proved)
         (mv (cons node nodes) id))))))

(defun other-lits (i lits n)
  ;; the literals other than the i-th
  (cond ((endp lits) nil)
        ((equal i n) (other-lits i (cdr lits) (1+ n)))
        (t (cons (car lits) (other-lits i (cdr lits) (1+ n))))))

(defun negate-lits (lits)
  (if (endp lits)
      nil
    (cons (negate-lit (car lits)) (negate-lits (cdr lits)))))

(defun rewrite-or-keep (term hyps theory state)
  ;; REWRITE$ term under hyps; on error, return term.
  (mv-let (erp val state)
    (if theory
        (rewrite$ term :hyps hyps :in-theory theory
                  :prove-forced-assumptions nil :default-hints-p nil
                  :ctx 'smtlink)
      (rewrite$ term :hyps hyps
                :prove-forced-assumptions nil :default-hints-p nil
                :ctx 'smtlink))
    (mv (if erp term (car val)) state)))

(defun type-infer-lit (lit hyps types state)
  ;; returns (mv typed-term state)
  (mv-let (next entries)
    (ti-enumerate lit nil 0 nil)
    (declare (ignore next))
    (let ((big (ti-big-term (reverse entries) types nil)))
      (mv-let (erp val state)
        (rewrite$ big :hyps hyps :prove-forced-assumptions nil
                  :default-hints-p nil :ctx 'smtlink)
        (let ((proved (if erp nil (ti-collect (car val) nil))))
          (mv-let (node next)
            (ti-build lit 0 proved)
            (declare (ignore next))
            (mv node state)))))))

(defun type-infer-lits (lits all i types state)
  (if (endp lits)
      (mv nil state)
    (mv-let (tt state)
      (type-infer-lit (car lits) (negate-lits (other-lits i all 0)) types state)
      (mv-let (tts state)
        (type-infer-lits (cdr lits) all (1+ i) types state)
        (mv (cons tt tts) state)))))

; ----------------------------------------------------------------------
; Term rewriting (Section 5.4)

(defun plain-judgements (conjuncts)
  ;; the judgements (r term) without path conditions
  (cond ((endp conjuncts) nil)
        ((and (consp (car conjuncts)) (eq (car (car conjuncts)) 'if))
         (plain-judgements (cdr conjuncts)))
        (t (cons (car conjuncts) (plain-judgements (cdr conjuncts))))))

(defun rewrite-lits (lits tts theory state)
  (if (endp lits)
      (mv nil state)
    (let ((hyps (remove-duplicates-equal
                 (plain-judgements (tt-judgement-conjuncts (car tts) nil)))))
      (mv-let (new state)
        (rewrite-or-keep (car lits) hyps theory state)
        (mv-let (rest state)
          (rewrite-lits (cdr lits) (cdr tts) theory state)
          (mv (if (equal new *nil*) rest (cons new rest)) state))))))

; ----------------------------------------------------------------------
; Simplification (Section 5.5)

(defun var-judgement-hyps (vars)
  (cond ((endp vars) nil)
        ((eq (entry-get 'judgement (car vars)) 'any-p)
         (var-judgement-hyps (cdr vars)))
        (t (cons (list (entry-get 'judgement (car vars))
                       (entry-get 'name (car vars)))
                 (var-judgement-hyps (cdr vars))))))

(defun simplify-lits (lits hyps theory state)
  (if (endp lits)
      (mv nil state)
    (mv-let (new state)
      (rewrite-or-keep (car lits) hyps theory state)
      (mv-let (rest state)
        (simplify-lits (cdr lits) hyps theory state)
        (mv (if (equal new *nil*) rest (cons new rest)) state)))))

; ----------------------------------------------------------------------
; The driver

(defun smtlink-driver (clause state)
  ;; A computed hint.  Fires on clauses tagged by Smtlink.
  (cond
   ((side-clause-p clause)
    (let ((theory (side-clause-theory clause)))
      (value (if theory
                 `(:clause-processor (strip-side-cp clause) :in-theory ,theory)
               '(:clause-processor (strip-side-cp clause))))))
   ((not (tagged-clause-p clause))
    (value nil))
   (t
    (let* ((info (tag-info clause))
           (stage (info-stage info))
           (config (info-get :config info))
           (lits (clause-lits clause)))
      (case stage
        (:type-inference
         (let ((max (info-get :max-rounds config))
               (round (info-get :round info)))
           (if (and (natp max) (natp round) (> round max))
               (er soft 'smtlink
                   "Smtlink: the term rewriting stage did not converge after ~
                    ~x0 rounds.  The current goal is~|~x1."
                   max (cons 'or lits))
             (mv-let (tts state)
               (type-infer-lits lits lits 0 (info-get :types config) state)
               (value `(:computed-hint-replacement
                        t
                        :clause-processor (type-inference-cp clause ',tts)))))))
        (:type-fixing
         (value '(:computed-hint-replacement
                  t
                  :clause-processor (type-fix-cp clause nil state))))
        (:term-rewriting
         (mv-let (new-lits state)
           (rewrite-lits lits (info-get :typed-terms info)
                         (info-get :translation-theory config) state)
           (prog2$
            (print-lits (if (equal new-lits lits)
                            "term after rewriting (unchanged, rewriting done)"
                          "term after rewriting")
                        new-lits config)
            (value `(:computed-hint-replacement
                     t
                     :clause-processor (term-rewrite-cp clause ',new-lits))))))
        (:type-extraction
         (value '(:computed-hint-replacement
                  t
                  :clause-processor (type-extract-cp clause nil))))
        (:simplification
         (let ((smtj (info-get :smt-judgement info)))
           (mv-let (new-lits state)
             (simplify-lits lits (var-judgement-hyps (smtj-vars smtj))
                            (info-get :simplify-theory config) state)
             (prog2$
              (and (info-get :print config)
                   (cw "~%Smtlink: smt-judgement:~%~x0~%" smtj))
              (prog2$
               (print-lits "term after simplification" new-lits config)
               (value `(:computed-hint-replacement
                        t
                        :clause-processor (simplify-cp clause ',new-lits))))))))
        (:smt
         (value '(:computed-hint-replacement
                  t
                  :clause-processor (smtlink-trusted-cp clause nil state))))
        (otherwise (value nil)))))))

(add-default-hints! '((smtlink-driver clause state)))

; ----------------------------------------------------------------------
; The :smtlink custom keyword hint

(defconst *smtlink-keywords*
  '(:translation-theory :types :hypothesize :print :max-rounds
    :simplify-theory :smt-file :smt-solver))

(defconst *default-types* '(booleanp integerp rationalp))

(defun translate-hyps (hyps world state)
  (if (endp hyps)
      (value nil)
    (er-let* ((h (translate (car hyps) t t nil 'smtlink world state))
              (rest (translate-hyps (cdr hyps) world state)))
      (value (cons h rest)))))

(defun keyword-value-alist (val)
  (if (or (endp val) (endp (cdr val)))
      nil
    (cons (cons (car val) (cadr val))
          (keyword-value-alist (cddr val)))))

(defun smtlink-hint-fn (val clause world state)
  (cond
   ((not (and (keyword-value-listp val)
              (subsetp-eq (evens val) *smtlink-keywords*)))
    (er soft 'smtlink
        "The value of the :smtlink hint must be a keyword-value list with ~
         keywords among ~x0, but it is ~x1."
        *smtlink-keywords* val))
   (t
    (let* ((kv (keyword-value-alist val))
           (types (cdr (assoc-eq :types kv)))
           (hyps (cdr (assoc-eq :hypothesize kv))))
      (cond
       ((not (symbol-listp types))
        (er soft 'smtlink ":types must be a list of recognizers, but it is ~x0."
            types))
       ((not (true-listp hyps))
        (er soft 'smtlink ":hypothesize must be a list of terms, but it is ~x0."
            hyps))
       (t
        (er-let* ((hyps (translate-hyps hyps world state)))
          (let* ((config
                  (list
                   (cons :translation-theory
                         (if (assoc-eq :translation-theory kv)
                             (cdr (assoc-eq :translation-theory kv))
                           '(current-theory :here)))
                   (cons :simplify-theory
                         (if (assoc-eq :simplify-theory kv)
                             (cdr (assoc-eq :simplify-theory kv))
                           '(theory 'minimal-theory)))
                   (cons :types (remove-duplicates-eq
                                 (append *default-types* types)))
                   (cons :print (cdr (assoc-eq :print kv)))
                   (cons :max-rounds (if (assoc-eq :max-rounds kv)
                                         (cdr (assoc-eq :max-rounds kv))
                                       10))
                   (cons :smt-file (cdr (assoc-eq :smt-file kv)))
                   (cons :smt-solver (cdr (assoc-eq :smt-solver kv)))))
                 (new-lits (remove-duplicate-lits (flatten-lits clause) nil)))
            (value `(:clause-processor
                     (smtlink-entry-cp clause
                                       '(,config ,new-lits ,hyps))))))))))))

(add-custom-keyword-hint :smtlink
                         (smtlink-hint-fn acl2::val clause world state))
