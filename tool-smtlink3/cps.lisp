; Smtlink 3 (reimplementation) -- the verified clause processors
;
; Every clause processor in this book is proved correct with respect to the
; evaluator SMT-EV by a :clause-processor rule.  Each one either returns its
; input clause unchanged (when it does not apply) or returns the "main"
; clause, tagged for the next stage, together with the side goals described
; in the paper:
;
;  SMTLINK-ENTRY-CP      : enters Smtlink; flattens the goal into clause form
;                          and adds the :hypothesize hypotheses.
;  TYPE-INFERENCE-CP     : Section 5.2, attaches typed terms; side goal: the
;                          type judgements are correct.
;  TYPE-FIX-CP           : Section 5.3, selects SMT judgements (top-down),
;                          using typing theorems found in the world.
;  TERM-REWRITE-CP       : Section 5.4, replaces the goal by the rewritten
;                          goal; side goal: under the type hypothesis the
;                          rewritten goal implies the original goal.
;  TYPE-EXTRACT-CP       : Section 5.5, extracts the unconditional type
;                          judgements; side goal: they hold when the goal is
;                          false.
;  SIMPLIFY-CP           : Section 5.5, replaces the goal by its
;                          simplification; side goal as for TERM-REWRITE-CP.
;  STRIP-SIDE-CP         : removes the tag of a side goal.

(in-package "SMT")
(include-book "base")
(set-verify-guards-eagerness 0)

(local (in-theory (disable smt-ev-constraint-0)))

; ----------------------------------------------------------------------
; Generic lemmas

(defun negate-terms (hyps)
  (if (atom hyps)
      nil
    (cons (list 'not (car hyps))
          (negate-terms (cdr hyps)))))

(defthm smt-ev-disjoin-negate-terms
  (iff (smt-ev (disjoin (negate-terms hyps)) a)
       (not (smt-ev (conjoin hyps) a)))
  :hints (("Goal" :induct (negate-terms hyps))))

(defun hyp-side-goals (hyps cl)
  ;; one goal per hypothesis h: (or h cl)
  (if (atom hyps)
      nil
    (cons (make-side nil (cons (car hyps) cl))
          (hyp-side-goals (cdr hyps) cl))))

(defthm smt-ev-conjoin-clauses-append
  (iff (smt-ev (conjoin-clauses (append x y)) a)
       (and (smt-ev (conjoin-clauses x) a)
            (smt-ev (conjoin-clauses y) a)))
  :hints (("Goal" :induct (append x y))))

(defthm smt-ev-hyp-side-goals
  (implies (and (smt-ev (conjoin-clauses (hyp-side-goals hyps cl)) a)
                (not (smt-ev (disjoin cl) a)))
           (smt-ev (conjoin hyps) a))
  :hints (("Goal" :induct (hyp-side-goals hyps cl))))

; ----------------------------------------------------------------------
; Entry
;
; hint = (config new-lits hyps) where new-lits is the goal in clause form
; (computed by the :smtlink hint) and hyps are the :hypothesize terms.
;
; Main clause:  (tag (not 't) (not h1) ... (not hk) . new-lits)
; Side goals:   (or (not (disjoin new-lits)) cl)       -- clausification
;               (or hi cl)  for each i                 -- :hypothesize

(defun initial-info (config)
  (list (cons :stage :type-inference)
        (cons :round 0)
        (cons :config config)))

(defun smtlink-entry-cp (cl hint)
  (let ((config (car hint))
        (new-lits (cadr hint))
        (hyps (caddr hint)))
    (list* (make-main (initial-info config) *t*
                      (append (negate-terms hyps) new-lits))
           (make-side nil (cons (list 'not (disjoin new-lits)) cl))
           (hyp-side-goals hyps cl))))

(defthm smtlink-entry-cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (smt-ev (conjoin-clauses (smtlink-entry-cp cl hint)) a))
           (smt-ev (disjoin cl) a))
  :hints (("Goal" :use ((:instance smt-ev-hyp-side-goals
                                   (hyps (caddr hint))))
           :in-theory (disable smt-ev-hyp-side-goals)))
  :rule-classes :clause-processor)

; ----------------------------------------------------------------------
; Stripping the tag of a side goal

(defun side-clause-p (cl)
  (and (consp cl)
       (consp (car cl))
       (consp (cdar cl))
       (consp (cadar cl))
       (consp (cdr (cadar cl)))
       (consp (cadr (cadar cl)))
       (consp (cdr (cadr (cadar cl))))
       (equal (car cl) (side-lit (cadr (cadr (cadar cl)))))))

(defun side-clause-theory (cl)
  (cadr (cadr (cadar cl))))

(defun strip-side-cp (cl)
  (if (side-clause-p cl)
      (list (cdr cl))
    (list cl)))

(defthm strip-side-cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (smt-ev (conjoin-clauses (strip-side-cp cl)) a))
           (smt-ev (disjoin cl) a))
  :hints (("Goal" :use ((:instance smt-ev-disjoin-cons
                                   (x (car cl)) (y (cdr cl)))
                        (:instance smt-ev-side-lit
                                   (theory (cadr (cadr (cadar cl))))))
           :in-theory (disable smt-ev-disjoin-cons smt-ev-side-lit)))
  :rule-classes :clause-processor)

; ----------------------------------------------------------------------
; Type inference (Section 5.2)
;
; hint = list of typed terms, one for each literal, computed by the Smtlink
; computed hint from the results of REWRITE$.  The clause processor does not
; trust them: it builds the type correctness hypothesis H' from them and asks
; ACL2 to prove that H' holds whenever the goal is false.
;
;   input : (tag (not H) . lits)
;   main  : (tag' (not H') . lits)
;   side  : (or H' . lits)

(defun type-inference-cp (cl hint)
  (if (and (tagged-clause-p cl)
           (eq (info-stage (tag-info cl)) :type-inference))
      (let* ((info (tag-info cl))
             (lits (clause-lits cl))
             (hyp (typed-terms-hyp hint))
             (info (info-set :stage :type-fixing
                             (info-set :typed-terms hint info))))
        (list (make-main info hyp lits)
              (make-side nil (cons hyp lits))))
    (list cl)))

(defthm type-inference-cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (smt-ev (conjoin-clauses (type-inference-cp cl hint)) a))
           (smt-ev (disjoin cl) a))
  :rule-classes :clause-processor)

; ----------------------------------------------------------------------
; Type fixing and judgement selection (Section 5.3)
;
; Top-down selection of one judgement per node.  For a function call node
; whose selected judgement is (r x), we look for a typing rule
;
;    (implies (and (r1 v1) ... (rn vn)) (r (f v1 ... vn)))
;
; among the rewrite rules stored in the world (or among a few built-in rules
; for ACL2 primitives) such that each argument has the judgement (ri x), and
; propagate (ri x) to the arguments.

(defconst *builtin-typing-rules*
  ;; (fn range . domain)
  '((binary-+ integerp integerp integerp)
    (binary-+ rationalp rationalp rationalp)
    (binary-* integerp integerp integerp)
    (binary-* rationalp rationalp rationalp)
    (unary-- integerp integerp)
    (unary-- rationalp rationalp)
    (unary-/ rationalp rationalp)
    (< booleanp rationalp rationalp)
    (not booleanp booleanp)
    (implies booleanp booleanp booleanp)
    (iff booleanp booleanp booleanp)))

(defconst *builtin-recognizers*
  '(booleanp integerp rationalp acl2-numberp symbolp consp atom
    natp posp stringp characterp true-listp))

(defun has-judgement (r tt)
  (or (eq r 'any-p)
      (set::in (make-judgement r) (tt-judgements tt))))

(defun all-have-judgements (rs tts)
  (if (atom rs)
      t
    (and (consp tts)
         (has-judgement (car rs) (car tts))
         (all-have-judgements (cdr rs) (cdr tts)))))

(defun builtin-rule-domain (f r rules args)
  ;; first built-in rule for f with range r applicable to args
  (if (atom rules)
      nil
    (let ((rule (car rules)))
      (if (and (consp rule) (consp (cdr rule))
               (eq (car rule) f)
               (eq (cadr rule) r)
               (equal (len (cddr rule)) (len args))
               (all-have-judgements (cddr rule) args))
          (cons t (cddr rule))
        (builtin-rule-domain f r (cdr rules) args)))))

(defun var-hyp-recognizer (v hyps)
  ;; recognizer r of the first hypothesis (r v), or any-p
  (if (atom hyps)
      'any-p
    (let ((h (car hyps)))
      (if (and (consp h) (symbolp (car h)) (consp (cdr h))
               (null (cddr h)) (eq (cadr h) v))
          (car h)
        (var-hyp-recognizer v (cdr hyps))))))

(defun hyps-about-vars-p (hyps vars)
  ;; every hypothesis is (r v) for some v among vars
  (if (atom hyps)
      t
    (let ((h (car hyps)))
      (and (consp h) (symbolp (car h)) (not (eq (car h) 'quote))
           (consp (cdr h)) (null (cddr h))
           (member-eq (cadr h) vars)
           (hyps-about-vars-p (cdr hyps) vars)))))

(defun vars-recognizers (vars hyps)
  (if (atom vars)
      nil
    (cons (var-hyp-recognizer (car vars) hyps)
          (vars-recognizers (cdr vars) hyps))))

(defun rule-domain (f r rules args)
  ;; Look for a rewrite rule (r (f v1 ... vn)) --> t with hypotheses about
  ;; the vi.  Returns (t . domain) or nil.
  (if (atom rules)
      nil
    (let* ((rule (car rules))
           (lhs (access rewrite-rule rule :lhs))
           (rhs (access rewrite-rule rule :rhs))
           (hyps (access rewrite-rule rule :hyps))
           (subclass (access rewrite-rule rule :subclass)))
      (if (and (member-eq subclass '(acl2::backchain acl2::abbreviation))
               (equal rhs *t*)
               (consp lhs) (eq (car lhs) r)
               (consp (cdr lhs)) (null (cddr lhs))
               (consp (cadr lhs)) (eq (car (cadr lhs)) f)
               (symbol-listp (cdr (cadr lhs)))
               (no-duplicatesp-eq (cdr (cadr lhs)))
               (equal (len (cdr (cadr lhs))) (len args))
               (true-listp hyps)
               (hyps-about-vars-p hyps (cdr (cadr lhs)))
               (all-have-judgements
                (vars-recognizers (cdr (cadr lhs)) hyps) args))
          (cons t (vars-recognizers (cdr (cadr lhs)) hyps))
        (rule-domain f r (cdr rules) args)))))

(defun first-preferred (prefs js)
  ;; first recognizer r in prefs with (r x) in js
  (if (atom prefs)
      nil
    (if (set::in (make-judgement (car prefs)) js)
        (car prefs)
      (first-preferred (cdr prefs) js))))

(defun default-choice (tt prefs)
  (let ((js (tt-judgements tt)))
    (or (first-preferred prefs js)
        (and (consp js)
             (symbolp (judgement-recognizer (car js)))
             (judgement-recognizer (car js)))
        'any-p)))

(defun default-choices (tts prefs)
  (if (atom tts)
      nil
    (cons (default-choice (car tts) prefs)
          (default-choices (cdr tts) prefs))))

(defun any-ps (n)
  (if (zp n) nil (cons 'any-p (any-ps (1- n)))))

(defun common-choice (tt1 tt2 prefs)
  (let ((r (first-preferred prefs (set::intersect (tt-judgements tt1)
                                                  (tt-judgements tt2)))))
    (if r (list r r) (list (default-choice tt1 prefs)
                           (default-choice tt2 prefs)))))

(defun arg-wants (f r args prefs recognizers wrld)
  ;; The judgements to propagate to the arguments of (f . args) given that
  ;; (f . args) has the selected judgement r.
  (cond ((eq f 'if)
         (list 'booleanp r r))
        ((and (eq f 'equal) (consp args) (consp (cdr args)))
         (common-choice (car args) (cadr args) prefs))
        ((eq r 'any-p)
         (any-ps (len args)))
        (t
         (let ((rd (rule-domain f r (getpropc r 'acl2::lemmas nil wrld) args)))
           (if rd
               (cdr rd)
             (let ((bd (builtin-rule-domain f r *builtin-typing-rules* args)))
               (if bd
                   (cdr bd)
                 (if (and (eq r 'booleanp)
                          (member-eq f recognizers)
                          (equal (len args) 1))
                     ;; a type recognizer accepts anything
                     (list 'any-p)
                   (default-choices args prefs)))))))))

(mutual-recursion
 (defun fix-tt (tt want prefs recognizers wrld)
   (declare (xargs :measure (acl2-count tt) :ruler-extenders :all
                   :hints (("Goal" :in-theory (disable tt-guts guts-args)))))
   (let* ((chosen (if (and (has-judgement want tt)
                           (not (and (eq want (quote any-p))
                                     (eq (guts-kind (tt-guts tt)) :fncall))))
                      want
                    (default-choice tt prefs)))
          (g (tt-guts tt))
          (new-g (if (and (eq (guts-kind g) :fncall) (consp tt))
                     (list* :fncall (guts-arg g)
                            (fix-tt-list (guts-args g)
                                         (arg-wants (guts-arg g) chosen
                                                    (guts-args g) prefs
                                                    recognizers wrld)
                                         prefs recognizers wrld))
                   g)))
     (make-tt (tt-judgements tt)
              (list (make-judgement chosen))
              new-g)))
 (defun fix-tt-list (tts wants prefs recognizers wrld)
   (declare (xargs :measure (acl2-count tts)))
   (if (atom tts)
       nil
     (cons (fix-tt (car tts) (if (consp wants) (car wants) 'any-p)
                   prefs recognizers wrld)
           (fix-tt-list (cdr tts) (if (consp wants) (cdr wants) nil)
                        prefs recognizers wrld)))))

(defun fix-literals (tts prefs recognizers wrld)
  (if (atom tts)
      nil
    (cons (fix-tt (car tts) 'booleanp prefs recognizers wrld)
          (fix-literals (cdr tts) prefs recognizers wrld))))

(defun config-types (info)
  (let ((types (info-get :types (info-get :config info))))
    (if (symbol-listp types) types nil)))

(defun type-preferences (info)
  (append '(booleanp rationalp integerp) (config-types info)))

(defun type-fix-cp (cl hint state)
  (declare (xargs :stobjs state)
           (ignore hint))
  (if (and (tagged-clause-p cl)
           (eq (info-stage (tag-info cl)) :type-fixing))
      (let* ((info (tag-info cl))
             (tts (fix-literals (info-get :typed-terms info)
                                (type-preferences info)
                                (append *builtin-recognizers*
                                        (config-types info))
                                (w state)))
             (info (info-set :stage :term-rewriting
                             (info-set :typed-terms tts info))))
        (mv nil (list (make-main info (clause-hyp cl) (clause-lits cl))) state))
    (mv nil (list cl) state)))

(defthm type-fix-cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (smt-ev (conjoin-clauses (clauses-result (type-fix-cp cl hint state))) a))
           (smt-ev (disjoin cl) a))
  :rule-classes :clause-processor)

; ----------------------------------------------------------------------
; Term rewriting (Section 5.4)
;
; hint = the rewritten literals, computed by REWRITE$ with the translation
; theory in the Smtlink computed hint.  If they are the original literals,
; the goal is fully transformed and passed on to type extraction.
; Otherwise the new goal re-enters type inference.
;
;   input : (tag (not H) . lits)
;   main  : (tag' (not H) . new-lits)
;   side  : (or (not H) (not (or . new-lits)) . lits)

(defun term-rewrite-cp (cl hint)
  (if (and (tagged-clause-p cl)
           (eq (info-stage (tag-info cl)) :term-rewriting))
      (let* ((info (tag-info cl))
             (hyp (clause-hyp cl))
             (lits (clause-lits cl)))
        (if (equal hint lits)
            (list (make-main (info-set :stage :type-extraction info) hyp lits))
          (list (make-main (info-set :stage :type-inference
                                     (info-set :round
                                               (1+ (nfix (info-get :round info)))
                                               info))
                           hyp hint)
                (make-side (info-get :translation-theory
                                     (info-get :config info))
                           (list* (list 'not hyp)
                                  (list 'not (disjoin hint))
                                  lits)))))
    (list cl)))

(defthm term-rewrite-cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (smt-ev (conjoin-clauses (term-rewrite-cp cl hint)) a))
           (smt-ev (disjoin cl) a))
  :rule-classes :clause-processor)

; ----------------------------------------------------------------------
; Type extraction (Section 5.5)
;
; Walk the typed terms and gather the variable and function judgements into
; an smt-judgement.  Ambiguous judgements are reported as errors.

(defconst *smt-builtin-fns*
  '(if not equal implies iff))

(defun add-to-entry (key val alist)
  ;; alist maps key -> list of values; add val (without duplicates)
  (let ((old (cdr (assoc-equal key alist))))
    (if (member-equal val old)
        alist
      (cons (cons key (cons val old))
            (remove1-assoc-equal key alist)))))

; Collect, for every variable, the selected judgements of its occurrences
; (key (:smt . v)) and the inferred judgements of its unconditional
; occurrences (key (:inf . v)); and for every function, its signatures
; (key (:fn . f)) as (range . domain).

(mutual-recursion
 (defun collect-tt (tt uncond acc)
   (declare (xargs :measure (acl2-count tt)))
   (let ((g (tt-guts tt)))
     (case (guts-kind g)
       (:var
        (let* ((v (guts-arg g))
               (acc (add-to-entry (cons :smt v) (tt-chosen tt) acc)))
          (if uncond
              (collect-recognizers (cons :inf v)
                                   (judgement-recognizers (tt-judgements tt))
                                   acc)
            acc)))
       (:fncall
        (let* ((f (guts-arg g))
               (args (guts-args g))
               (acc (if (or (member-eq f *smt-builtin-fns*) (not (consp tt)))
                        acc
                      (add-to-entry (cons :fn f)
                                    (cons (tt-chosen tt) (tt-chosen-list args))
                                    acc))))
          (if (and (eq f 'if) (consp args))
              (collect-tt-list (cdr args) nil
                               (collect-tt (car args) uncond acc))
            (collect-tt-list args uncond acc))))
       (otherwise acc))))
 (defun collect-tt-list (tts uncond acc)
   (declare (xargs :measure (acl2-count tts)))
   (if (atom tts)
       acc
     (collect-tt-list (cdr tts) uncond
                      (collect-tt (car tts) uncond acc))))
 (defun tt-chosen-list (tts)
   (declare (xargs :measure (acl2-count tts)))
   (if (atom tts)
       nil
     (cons (tt-chosen (car tts))
           (tt-chosen-list (cdr tts)))))
 (defun collect-recognizers (key rs acc)
   (declare (xargs :measure (acl2-count rs)))
   (if (atom rs)
       acc
     (collect-recognizers key (cdr rs) (add-to-entry key (car rs) acc)))))

(defun subtype-p (r s)
  ;; r implies s (as far as Smtlink knows)
  (or (eq r s)
      (eq s 'any-p)
      (and (eq r 'integerp) (eq s 'rationalp))))

(defun first-member-pref (prefs rs)
  (if (atom prefs)
      nil
    (if (member-eq (car prefs) rs)
        (car prefs)
      (first-member-pref (cdr prefs) rs))))

(defun most-specific (rs prefs)
  (cond ((member-eq (quote integerp) rs) (quote integerp))
        ((first-member-pref prefs rs) (first-member-pref prefs rs))
        ((and (consp rs) (symbolp (car rs)) (car rs)) (car rs))
        (t (quote any-p))))

(defun choose-var-judgement (smt inf prefs)
  ;; smt: selected judgements of the occurrences; inf: inferred judgements of
  ;; the unconditional occurrences.  Returns (mv erp r).
  (let ((smt (remove-eq 'any-p smt)))
    (cond ((atom smt)
           (mv nil (most-specific inf prefs)))
          ((atom (cdr smt))
           (if (and (eq (car smt) 'rationalp) (member-eq 'integerp inf))
               (mv nil 'integerp)
             (mv nil (car smt))))
          ((and (atom (cddr smt))
                (member-eq 'integerp smt)
                (member-eq 'rationalp smt))
           (mv nil 'integerp))
          (t (mv (msg "Smtlink: ambiguous type judgements ~x0." smt) nil)))))

(defun extract-vars (acc all prefs)
  ;; acc, all: the collected alist
  (if (atom acc)
      (mv nil nil)
    (let ((entry (car acc)))
      (if (and (consp entry) (consp (car entry)) (eq (caar entry) :smt))
          (let ((v (cdar entry)))
            (mv-let (erp r)
              (choose-var-judgement (cdr entry)
                                    (cdr (assoc-equal (cons :inf v) all))
                                    prefs)
              (if erp
                  (mv (msg "Smtlink: ambiguous type judgements for variable ~
                            ~x0: ~x1." v (cdr entry))
                      nil)
                (mv-let (erp rest)
                  (extract-vars (cdr acc) all prefs)
                  (if erp
                      (mv erp nil)
                    (mv nil (cons (list (cons 'name v) (cons 'judgement r))
                                  rest)))))))
        (extract-vars (cdr acc) all prefs)))))

(defun trivial-signature-p (sig)
  ;; (any-p any-p ... any-p): range and domain unconstrained
  (and (consp sig)
       (eq (car sig) (quote any-p))
       (subsetp-eq (cdr sig) (quote (any-p)))))

(defun remove-trivial-signatures (sigs)
  (cond ((atom sigs) nil)
        ((trivial-signature-p (car sigs))
         (remove-trivial-signatures (cdr sigs)))
        (t (cons (car sigs) (remove-trivial-signatures (cdr sigs))))))

(defun extract-fns (acc)
  (if (atom acc)
      (mv nil nil)
    (let ((entry (car acc)))
      (if (and (consp entry) (consp (car entry)) (eq (caar entry) :fn))
          (let* ((f (cdar entry))
                 (sigs (if (consp (remove-trivial-signatures (cdr entry)))
                           (remove-trivial-signatures (cdr entry))
                         (cdr entry))))
            (if (or (atom sigs) (consp (cdr sigs)) (atom (car sigs)))
                (mv (msg "Smtlink: ambiguous type judgements for function ~
                          ~x0: ~x1." f sigs)
                    nil)
              (mv-let (erp rest)
                (extract-fns (cdr acc))
                (if erp
                    (mv erp nil)
                  (mv nil (cons (list (cons 'name f)
                                      (cons 'domain (cdar sigs))
                                      (cons 'range (caar sigs)))
                                rest))))))
        (extract-fns (cdr acc))))))

(defun extract-smt-judgement (tts prefs)
  (let ((acc (collect-tt-list tts t nil)))
    (mv-let (erp vars)
      (extract-vars (reverse acc) acc prefs)
      (if erp
          (mv erp nil)
        (mv-let (erp fns)
          (extract-fns (reverse acc))
          (if erp
              (mv erp nil)
            (mv nil (list (cons 'vars vars)
                          (cons 'fns fns)))))))))

;   input : (tag (not H) . lits)
;   main  : (tag' (not Tu) . lits)
;   side  : (or (not H) Tu . lits)

(defun type-extract-cp (cl hint)
  (declare (ignore hint))
  (if (and (tagged-clause-p cl)
           (eq (info-stage (tag-info cl)) :type-extraction))
      (let* ((info (tag-info cl))
             (hyp (clause-hyp cl))
             (lits (clause-lits cl)))
        (mv-let (erp smtj)
          (extract-smt-judgement (info-get :typed-terms info)
                                 (type-preferences info))
          (if erp
              (mv erp nil)
            (let ((tu (smt-judgement->expr smtj)))
              (mv nil
                  (list (make-main (info-set :stage :simplification
                                             (info-set :smt-judgement smtj
                                                       info))
                                   tu lits)
                        (make-side nil (list* (list 'not hyp) tu lits))))))))
    (mv nil (list cl))))

(defthm type-extract-cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (smt-ev (conjoin-clauses
                         (clauses-result (type-extract-cp cl hint)))
                        a))
           (smt-ev (disjoin cl) a))
  :rule-classes :clause-processor)

; ----------------------------------------------------------------------
; Simplification (Section 5.5)
;
; hint = the literals rewritten under the smt-judgement (erasing type
; recognizers).
;
;   input : (tag (not Tu) . lits)
;   main  : (tag' (not Tu) . new-lits)
;   side  : (or (not Tu) (not (or . new-lits)) . lits)

(defun simplify-cp (cl hint)
  (if (and (tagged-clause-p cl)
           (eq (info-stage (tag-info cl)) :simplification))
      (let* ((info (tag-info cl))
             (hyp (clause-hyp cl))
             (lits (clause-lits cl)))
        (list (make-main (info-set :stage :smt info) hyp hint)
              (make-side (info-get :simplify-theory (info-get :config info))
                         (list* (list 'not hyp)
                                (list 'not (disjoin hint))
                                lits))))
    (list cl)))

(defthm simplify-cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (smt-ev (conjoin-clauses (simplify-cp cl hint)) a))
           (smt-ev (disjoin cl) a))
  :rule-classes :clause-processor)
