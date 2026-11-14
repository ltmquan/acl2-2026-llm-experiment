; Smtlink 3 (reimplementation) -- the trusted clause processor
;
; This is the only trusted component of Smtlink 3 (Section 5.6).  It
; receives a clause of the form
;
;    ((not (smtlink-goal 'info)) (not Tu) lit1 ... litn)
;
; where INFO contains an smt-judgement SMTJ and Tu is (smt-judgement->expr
; SMTJ).  It translates the smt-judgement into SMT-LIB declarations and the
; goal into the assertion of its negation, runs the SMT solver (Z3) on the
; script, and proves the clause only if the solver answers "unsat".  In that
; case it returns, as new goals, the function judgements of SMTJ, which must
; hold universally for the uninterpreted-function declarations to be
; faithful.  On "sat", "unknown", or any error it signals an error, so the
; proof fails.
;
; Soundness argument (informal).  Let s be an assignment falsifying the
; clause.  Then Tu holds at s: every variable has the value of a member of
; the type of its declared sort.  Since the function judgements hold
; universally, every uninterpreted function maps arguments of its domain
; sorts to its range sort.  Interpret Bool as {t, nil}, Int as the
; integers, Real as the reals (containing the rationals), an uninterpreted
; sort named after a recognizer r as the set of objects satisfying r, and an
; array sort (Array K V) registered with DEF-SMT-ARRAY as the functions from
; K to V, mapping an ACL2 array a to the function k |-> (select a k).  The
; theorems required by DEF-SMT-ARRAY (checked below) make select/store
; faithful; since array-sorted terms may only occur as the first argument of
; select and store (no equalities between arrays, no arrays as arguments of
; uninterpreted functions), extensionality is never needed.  The functions
; RATIONAL-+ etc. of smt-theory.lisp coincide with +, -, *, / and < on
; rationals (on 0 the reciprocal is unspecified in both worlds).  Hence
; every term of sort Bool evaluates in this model to the SMT truth value of
; its ACL2 value, so the negated goal is satisfiable, and the solver cannot
; answer unsat (assuming it is sound).

(in-package "SMT")
(include-book "base")
(include-book "smt-theory")

(defttag :smtlink)

(program)
(set-state-ok t)

; ----------------------------------------------------------------------
; Array theories
;
; (def-smt-array :recognizer arrp :key-p kp :val-p vp
;                :select sel :store st [:hints hints])
;
; proves the following theorems and records the array theory in the table
; SMT-ARRAYS.  The trusted clause processor checks that these theorems are
; present in the world before translating sel and st to SMT-LIB select and
; store.

(defun array-axioms (arrp kp vp sel st)
  ;; list of (name . formula); formulas are in translated form
  (let ((a 'a) (k 'k) (j 'j) (v 'v))
    (list
     (cons (acl2::packn-pos (list sel '-select-of-store-same) sel)
           `(implies (if (,arrp ,a) (if (,kp ,k) (,vp ,v) 'nil) 'nil)
                     (equal (,sel (,st ,a ,k ,v) ,k) ,v)))
     (cons (acl2::packn-pos (list sel '-select-of-store-diff) sel)
           `(implies (if (,arrp ,a)
                         (if (,kp ,k)
                             (if (,kp ,j)
                                 (if (,vp ,v) (not (equal ,j ,k)) 'nil)
                               'nil)
                           'nil)
                       'nil)
                     (equal (,sel (,st ,a ,k ,v) ,j) (,sel ,a ,j))))
     (cons (acl2::packn-pos (list 'return-of- sel) sel)
           `(implies (if (,arrp ,a) (,kp ,k) 'nil)
                     (,vp (,sel ,a ,k))))
     (cons (acl2::packn-pos (list 'return-of- st) st)
           `(implies (if (,arrp ,a) (if (,kp ,k) (,vp ,v) 'nil) 'nil)
                     (,arrp (,st ,a ,k ,v)))))))

(defun array-axiom-events (axioms hints)
  (if (endp axioms)
      nil
    (cons `(defthm ,(caar axioms) ,(cdar axioms) :hints ,hints)
          (array-axiom-events (cdr axioms) hints))))

(defmacro def-smt-array (&key recognizer key-p val-p select store hints)
  `(progn
     ,@(array-axiom-events (array-axioms recognizer key-p val-p select store)
                           hints)
     (table smt-arrays ',recognizer
            '((:key-p . ,key-p) (:val-p . ,val-p)
              (:select . ,select) (:store . ,store)))))

(defun array-theorems-present-p (axioms wrld)
  (or (endp axioms)
      (and (equal (getpropc (caar axioms) 'acl2::theorem nil wrld)
                  (cdar axioms))
           (array-theorems-present-p (cdr axioms) wrld))))

(defun checked-arrays (table wrld)
  ;; the entries of the SMT-ARRAYS table whose theorems are present
  (cond ((endp table) nil)
        (t (let* ((arrp (caar table))
                  (e (cdar table))
                  (kp (cdr (assoc-eq :key-p e)))
                  (vp (cdr (assoc-eq :val-p e)))
                  (sel (cdr (assoc-eq :select e)))
                  (st (cdr (assoc-eq :store e))))
             (if (and (symbolp arrp) (symbolp kp) (symbolp vp)
                      (symbolp sel) (symbolp st)
                      (not (member-eq kp (list arrp 'any-p)))
                      (not (member-eq vp (list arrp 'any-p)))
                      (not (assoc-eq kp table))
                      (not (assoc-eq vp table))
                      (array-theorems-present-p
                       (array-axioms arrp kp vp sel st) wrld))
                 (cons (car table) (checked-arrays (cdr table) wrld))
               (checked-arrays (cdr table) wrld))))))

; ----------------------------------------------------------------------
; Sorts
;
;   :bool, :int, :real, (:usort . "name"), (:array key-sort val-sort)

(defun smt-quote (str)
  (concatenate 'string "|" str "|"))

(defun legal-smt-name-p (str)
  (let ((chars (coerce str 'list)))
    (not (or (member #\| chars) (member #\\ chars)))))

(defun symbol-smt-string (sym)
  (concatenate 'string (symbol-package-name sym) "::" (symbol-name sym)))

(defun recognizer-sort (r arrays)
  (cond ((eq r 'booleanp) :bool)
        ((eq r 'integerp) :int)
        ((eq r 'rationalp) :real)
        ((assoc-eq r arrays)
         (let ((e (cdr (assoc-eq r arrays))))
           (list :array
                 (recognizer-sort (cdr (assoc-eq :key-p e)) nil)
                 (recognizer-sort (cdr (assoc-eq :val-p e)) nil))))
        (t (cons :usort (symbol-smt-string r)))))

(defun sort-string (s)
  (cond ((eq s :bool) "Bool")
        ((eq s :int) "Int")
        ((eq s :real) "Real")
        ((and (consp s) (eq (car s) :usort)) (smt-quote (cdr s)))
        ((and (consp s) (eq (car s) :array))
         (concatenate 'string "(Array " (sort-string (cadr s)) " "
                      (sort-string (caddr s)) ")"))
        (t "?")))

(defun numeric-sort-p (s)
  (member-eq s '(:int :real)))

(defun array-sort-p (s)
  (and (consp s) (eq (car s) :array)))

(defun usorts-of-sort (s acc)
  (cond ((and (consp s) (eq (car s) :usort))
         (add-to-set-equal s acc))
        ((array-sort-p s)
         (usorts-of-sort (caddr s) (usorts-of-sort (cadr s) acc)))
        (t acc)))

(defun usorts-of-sorts (ss acc)
  (if (endp ss)
      acc
    (usorts-of-sorts (cdr ss) (usorts-of-sort (car ss) acc))))

; ----------------------------------------------------------------------
; Signatures

; The functions of smt-theory.lisp and the SMT-LIB operators they denote.
(defconst *interpreted-fns*
  '((rational-+ . "+")
    (rational-* . "*")
    (rational-- . "-")
    (rational-/ . "/")
    (rational-< . "<")))

(defun recognizer-sorts (rs arrays)
  (if (endp rs)
      nil
    (cons (recognizer-sort (car rs) arrays)
          (recognizer-sorts (cdr rs) arrays))))

; A signature is (kind op domain-sorts . range-sort) where kind is
; :interpreted, :select, :store or :uf.

(defun array-op (f arrays)
  ;; (mv kind arrp) if f is the select or store of a checked array theory
  (cond ((endp arrays) (mv nil nil))
        ((eq f (cdr (assoc-eq :select (cdar arrays)))) (mv :select (caar arrays)))
        ((eq f (cdr (assoc-eq :store (cdar arrays)))) (mv :store (caar arrays)))
        (t (array-op f (cdr arrays)))))

(defun check-signature (fn arrays)
  ;; fn: an entry of the smt-judgement.  Returns (mv erp sig).
  (let* ((f (entry-get 'name fn))
         (domain (entry-get 'domain fn))
         (range (entry-get 'range fn))
         (dsorts (recognizer-sorts domain arrays))
         (rsort (recognizer-sort range arrays))
         (interp (assoc-eq f *interpreted-fns*)))
    (mv-let
      (akind arrp)
      (array-op f arrays)
      (cond
       ((not (and (symbolp f) (symbol-listp domain) (symbolp range)
                  (legal-smt-name-p (symbol-smt-string f))))
        (mv (msg "Smtlink: ill-formed function judgement ~x0." fn) nil))
       (interp
        (let ((op (cdr interp)))
          (cond
           ((and (member-eq f '(rational-+ rational-*))
                 (equal (len dsorts) 2)
                 (numeric-sort-p rsort)
                 (equal dsorts (list rsort rsort)))
            (mv nil (list* :interpreted op dsorts rsort)))
           ((and (eq f 'rational--)
                 (numeric-sort-p rsort)
                 (equal dsorts (list rsort)))
            (mv nil (list* :interpreted op dsorts rsort)))
           ((and (eq f 'rational-/)
                 (eq rsort :real)
                 (equal dsorts (list :real)))
            (mv nil (list* :interpreted op dsorts rsort)))
           ((and (eq f 'rational-<)
                 (eq rsort :bool)
                 (equal (len dsorts) 2)
                 (numeric-sort-p (car dsorts))
                 (equal (car dsorts) (cadr dsorts)))
            (mv nil (list* :interpreted op dsorts rsort)))
           (t (mv (msg "Smtlink: unsupported signature for ~x0: ~x1 -> ~x2."
                       f domain range)
                  nil)))))
       ((eq akind :select)
        (let* ((e (cdr (assoc-eq arrp arrays)))
               (kp (cdr (assoc-eq :key-p e)))
               (vp (cdr (assoc-eq :val-p e))))
          (if (and (equal domain (list arrp kp)) (eq range vp))
              (mv nil (list* :select "select" dsorts rsort))
            (mv (msg "Smtlink: unsupported signature for array select ~x0: ~
                      ~x1 -> ~x2." f domain range)
                nil))))
       ((eq akind :store)
        (let* ((e (cdr (assoc-eq arrp arrays)))
               (kp (cdr (assoc-eq :key-p e)))
               (vp (cdr (assoc-eq :val-p e))))
          (if (and (equal domain (list arrp kp vp)) (eq range arrp))
              (mv nil (list* :store "store" dsorts rsort))
            (mv (msg "Smtlink: unsupported signature for array store ~x0: ~
                      ~x1 -> ~x2." f domain range)
                nil))))
       ((member-eq f '(if not equal implies iff))
        (mv (msg "Smtlink: unexpected judgement for ~x0." f) nil))
       ((intersectp-equal (strip-cars arrays) domain)
        (mv (msg "Smtlink: arrays may not be arguments of the uninterpreted ~
                  function ~x0." f)
            nil))
       (t (mv nil (list* :uf (smt-quote (symbol-smt-string f)) dsorts rsort)))))))

(defun check-signatures (fns arrays)
  ;; returns (mv erp alist) mapping function symbols to signatures
  (if (endp fns)
      (mv nil nil)
    (mv-let (erp sig)
      (check-signature (car fns) arrays)
      (if erp
          (mv erp nil)
        (mv-let (erp rest)
          (check-signatures (cdr fns) arrays)
          (if erp
              (mv erp nil)
            (mv nil (acons (entry-get 'name (car fns)) sig rest))))))))

(defun var-sorts (vars arrays)
  ;; returns (mv erp alist) mapping variables to sorts
  (if (endp vars)
      (mv nil nil)
    (let ((v (entry-get 'name (car vars)))
          (r (entry-get 'judgement (car vars))))
      (if (not (and (symbolp v) v (not (eq v t)) (symbolp r)
                    (legal-smt-name-p (symbol-smt-string v))))
          (mv (msg "Smtlink: ill-formed variable judgement ~x0." (car vars))
              nil)
        (mv-let (erp rest)
          (var-sorts (cdr vars) arrays)
          (if (or erp (assoc-eq v rest))
              (mv (or erp (msg "Smtlink: two judgements for variable ~x0." v))
                  nil)
            (mv nil (acons v (recognizer-sort r arrays) rest))))))))

; ----------------------------------------------------------------------
; Terms

(defun nat-string (n)
  (coerce (explode-atom n 10) 'string))

(defun constant-translation (c)
  ;; (mv erp string sort)
  (cond ((eq c t) (mv nil "true" :bool))
        ((eq c nil) (mv nil "false" :bool))
        ((integerp c)
         (mv nil
             (if (< c 0)
                 (concatenate 'string "(- " (nat-string (- c)) ")")
               (nat-string c))
             :int))
        ((rationalp c)
         (let* ((n (numerator c)) (d (denominator c))
                (q (concatenate 'string "(/ " (nat-string (abs n)) ".0 "
                                (nat-string d) ".0)")))
           (mv nil
               (if (< n 0) (concatenate 'string "(- " q ")") q)
               :real)))
        (t (mv (msg "Smtlink: unsupported constant ~x0." c) nil nil))))

(defun coerce-to (str from to)
  ;; (mv ok str): an Int may be used where a Real is expected
  (cond ((equal from to) (mv t str))
        ((and (eq from :int) (eq to :real))
         (mv t (concatenate 'string "(to_real " str ")")))
        (t (mv nil str))))

(defun join-strings (strs)
  (cond ((endp strs) "")
        ((endp (cdr strs)) (car strs))
        (t (concatenate 'string (car strs) " " (join-strings (cdr strs))))))

(defun coerce-args (strs sorts dsorts)
  ;; (mv ok strs)
  (if (endp strs)
      (mv (endp dsorts) nil)
    (if (endp dsorts)
        (mv nil nil)
      (mv-let (ok str)
        (coerce-to (car strs) (car sorts) (car dsorts))
        (mv-let (ok2 rest)
          (coerce-args (cdr strs) (cdr sorts) (cdr dsorts))
          (mv (and ok ok2) (cons str rest)))))))

(defun same-sort-args (s1 s2 str1 str2)
  ;; (mv ok str1 str2 sort) for if-branches and equalities
  (cond ((equal s1 s2) (mv t str1 str2 s1))
        ((and (numeric-sort-p s1) (numeric-sort-p s2))
         (mv-let (ok1 a) (coerce-to str1 s1 :real)
           (mv-let (ok2 b) (coerce-to str2 s2 :real)
             (mv (and ok1 ok2) a b :real))))
        (t (mv nil str1 str2 nil))))

(defun member-if-array-sort (sorts)
  (and (consp sorts)
       (or (array-sort-p (car sorts))
           (member-if-array-sort (cdr sorts)))))

(defun translate-call (f strs sorts term sigs)
  (cond
   ((eq f 'if)
    (if (and (equal (len strs) 3) (eq (car sorts) :bool))
        (mv-let (ok b c s)
          (same-sort-args (cadr sorts) (caddr sorts) (cadr strs) (caddr strs))
          (if ok
              (mv nil (concatenate 'string "(ite " (car strs) " " b " " c ")") s)
            (mv (msg "Smtlink: ill-sorted IF: ~x0." term) nil nil)))
      (mv (msg "Smtlink: ill-sorted IF test: ~x0." term) nil nil)))
   ((eq f 'not)
    (if (equal sorts '(:bool))
        (mv nil (concatenate 'string "(not " (car strs) ")") :bool)
      (mv (msg "Smtlink: ill-sorted NOT: ~x0." term) nil nil)))
   ((member-eq f '(implies iff))
    (if (equal sorts '(:bool :bool))
        (mv nil (concatenate 'string (if (eq f 'implies) "(=> " "(= ")
                             (car strs) " " (cadr strs) ")")
            :bool)
      (mv (msg "Smtlink: ill-sorted ~x0: ~x1." f term) nil nil)))
   ((eq f 'equal)
    (if (and (equal (len sorts) 2)
             (not (array-sort-p (car sorts)))
             (not (array-sort-p (cadr sorts))))
        (mv-let (ok a b s)
          (same-sort-args (car sorts) (cadr sorts) (car strs) (cadr strs))
          (declare (ignore s))
          (if ok
              (mv nil (concatenate 'string "(= " a " " b ")") :bool)
            (mv (msg "Smtlink: ill-sorted EQUAL: ~x0." term) nil nil)))
      (mv (msg "Smtlink: equalities between arrays are not supported: ~x0."
               term)
          nil nil)))
   (t
    (let ((sig (cdr (assoc-eq f sigs))))
      (if (null sig)
          (mv (msg "Smtlink: no type judgement for function ~x0." f) nil nil)
        (let ((kind (car sig))
              (op (cadr sig))
              (dsorts (car (cddr sig)))
              (rsort (cdr (cddr sig))))
          (mv-let (ok args)
            (coerce-args strs sorts dsorts)
            (cond
             ((not ok)
              (mv (msg "Smtlink: ill-sorted arguments in ~x0." term) nil nil))
             ((and (not (member-eq kind '(:select :store)))
                   (member-if-array-sort sorts))
              (mv (msg "Smtlink: arrays may only be used with select and ~
                        store: ~x0." term)
                  nil nil))
             ((and (eq kind :store) (array-sort-p (caddr sorts)))
              (mv (msg "Smtlink: arrays may not be stored in arrays: ~x0."
                       term)
                  nil nil))
             ((and (eq kind :select) (array-sort-p (cadr sorts)))
              (mv (msg "Smtlink: arrays may not be array indices: ~x0." term)
                  nil nil))
             ((and (eq kind :interpreted) (equal op "/"))
              (mv nil (concatenate 'string "(/ 1.0 " (car args) ")") rsort))
             ((endp args)
              (mv nil op rsort))
             (t
              (mv nil (concatenate 'string "(" op " " (join-strings args) ")")
                  rsort))))))))))

(mutual-recursion
 (defun translate-term (term vsorts sigs)
   ;; (mv erp string sort)
   (cond
    ((variablep term)
     (let ((s (assoc-eq term vsorts)))
       (if s
           (mv nil (smt-quote (symbol-smt-string term)) (cdr s))
         (mv (msg "Smtlink: no type judgement for variable ~x0." term)
             nil nil))))
    ((fquotep term) (constant-translation (unquote term)))
    ((flambda-applicationp term)
     (mv (msg "Smtlink: lambda expressions are not supported: ~x0." term)
         nil nil))
    (t
     (let ((f (ffn-symb term)))
       (mv-let (erp strs sorts)
         (translate-terms (fargs term) vsorts sigs)
         (if erp
             (mv erp nil nil)
           (translate-call f strs sorts term sigs)))))))
 (defun translate-terms (terms vsorts sigs)
   (if (endp terms)
       (mv nil nil nil)
     (mv-let (erp str sort)
       (translate-term (car terms) vsorts sigs)
       (if erp
           (mv erp nil nil)
         (mv-let (erp strs sorts)
           (translate-terms (cdr terms) vsorts sigs)
           (if erp
               (mv erp nil nil)
             (mv nil (cons str strs) (cons sort sorts)))))))))

; ----------------------------------------------------------------------
; Declarations and the script

(defun declare-sort-lines (usorts)
  (if (endp usorts)
      nil
    (cons (concatenate 'string "(declare-sort " (sort-string (car usorts)) " 0)")
          (declare-sort-lines (cdr usorts)))))

(defun sort-strings (sorts)
  (if (endp sorts)
      nil
    (cons (sort-string (car sorts)) (sort-strings (cdr sorts)))))

(defun declare-fun-lines (sigs)
  (cond ((endp sigs) nil)
        ((eq (cadr (car sigs)) :uf)
         (let ((sig (cdar sigs)))
           (cons (concatenate 'string "(declare-fun " (cadr sig) " ("
                              (join-strings (sort-strings (car (cddr sig))))
                              ") " (sort-string (cdr (cddr sig))) ")")
                 (declare-fun-lines (cdr sigs)))))
        (t (declare-fun-lines (cdr sigs)))))

(defun declare-const-lines (vsorts)
  (if (endp vsorts)
      nil
    (cons (concatenate 'string "(declare-const "
                       (smt-quote (symbol-smt-string (caar vsorts))) " "
                       (sort-string (cdar vsorts)) ")")
          (declare-const-lines (cdr vsorts)))))

(defun sig-sorts (sigs acc)
  (if (endp sigs)
      acc
    (let ((sig (cdar sigs)))
      (sig-sorts (cdr sigs)
                 (cons (cdr (cddr sig)) (append (car (cddr sig)) acc))))))

(defun all-bool-p (sorts)
  (or (endp sorts)
      (and (eq (car sorts) :bool)
           (all-bool-p (cdr sorts)))))

(defun lines-string (lines)
  (if (endp lines)
      ""
    (concatenate 'string (car lines) (string #\Newline)
                 (lines-string (cdr lines)))))

(defun smt-script (smtj lits wrld)
  ;; (mv erp script)
  (let ((arrays (checked-arrays (table-alist 'smt-arrays wrld) wrld)))
    (mv-let (erp vsorts)
      (var-sorts (smtj-vars smtj) arrays)
      (if erp
          (mv erp nil)
        (mv-let (erp sigs)
          (check-signatures (smtj-fns smtj) arrays)
          (if erp
              (mv erp nil)
            (mv-let (erp strs sorts)
              (translate-terms lits vsorts sigs)
              (cond
               (erp (mv erp nil))
               ((not (all-bool-p sorts))
                (mv (msg "Smtlink: every literal of the goal must have sort ~
                          Bool; the sorts are ~x0." sorts)
                    nil))
               (t
                (let* ((goal (cond ((endp strs) "false")
                                   ((endp (cdr strs)) (car strs))
                                   (t (concatenate 'string "(or "
                                                   (join-strings strs) ")"))))
                       (usorts (usorts-of-sorts
                                (append (strip-cdrs vsorts) (sig-sorts sigs nil))
                                nil)))
                  (mv nil
                      (lines-string
                       (append (list "(set-logic AUFNIRA)")
                               (declare-sort-lines (reverse usorts))
                               (declare-fun-lines sigs)
                               (declare-const-lines vsorts)
                               (list (concatenate 'string "(assert (not "
                                                  goal "))")
                                     "(check-sat)"))))))))))))))

; ----------------------------------------------------------------------
; Running the solver

(defun whitespace-char-p (c)
  (member c '(#\Space #\Tab #\Newline #\Return #\Page)))

(defun drop-whitespace (chars)
  (if (and (consp chars) (whitespace-char-p (car chars)))
      (drop-whitespace (cdr chars))
    chars))

(defun trim-whitespace (str)
  (coerce (reverse (drop-whitespace
                    (reverse (drop-whitespace (coerce str 'list)))))
          'string))

(defconst *run-solver-script*
  ;; $1 = script, $2 = file name ("" for a temporary file), $3 = solver
  "if [ -z \"$2\" ]; then f=$(mktemp /tmp/smtlink-XXXXXX.smt2) || exit 1; else f=\"$2\"; fi; printf '%s' \"$1\" > \"$f\" || exit 1; \"$3\" -smt2 \"$f\" 2>&1; if [ -z \"$2\" ]; then rm -f \"$f\"; fi")

(defun run-solver (script config state)
  ;; returns (mv output state)
  (let ((file (info-get :smt-file config))
        (solver (or (info-get :smt-solver config) "z3")))
    (mv-let (erp out state)
      (sys-call+ "sh" (list "-c" *run-solver-script* "smtlink" script
                            (if (stringp file) file "")
                            (if (stringp solver) solver "z3"))
                 state)
      (declare (ignore erp))
      (mv (if (stringp out) out "") state))))

(defun fn-judgement-clauses (fns)
  (if (endp fns)
      nil
    (cons (list (fn-judgement-expr (car fns)))
          (fn-judgement-clauses (cdr fns)))))

; ----------------------------------------------------------------------
; The trusted clause processor


(defun print-smt-script (script result state)
  (pprogn (princ$ "
Smtlink: SMT-LIB script:
" *standard-co* state)
          (princ$ script *standard-co* state)
          (princ$ "Smtlink: solver output: " *standard-co* state)
          (princ$ result *standard-co* state)
          (newline *standard-co* state)))

(defun smtlink-trusted-cp (cl hint state)
  (declare (xargs :stobjs state)
           (ignore hint))
  (let ((info (tag-info cl)))
    (cond
     ((not (and (tagged-clause-p cl)
                (eq (info-stage info) :smt)))
      (mv (msg "Smtlink: the trusted clause processor was applied to a goal ~
                that has not been prepared by Smtlink.")
          nil state))
     (t
      (let* ((smtj (info-get :smt-judgement info))
             (config (info-get :config info))
             (tu (clause-hyp cl))
             (lits (clause-lits cl)))
        (cond
         ((not (equal tu (smt-judgement->expr smtj)))
          (mv (msg "Smtlink: the type hypothesis of the goal does not match ~
                    its smt-judgement.")
              nil state))
         (t
          (mv-let (erp script)
            (smt-script smtj lits (w state))
            (if erp
                (mv erp nil state)
              (mv-let (out state)
                (run-solver script config state)
                (let ((result (trim-whitespace out))
                      (print (info-get :print config)))
                  (pprogn
                   (if (or print (not (equal result "unsat")))
                       (print-smt-script script result state)
                     state)
                   (if (equal result "unsat")
                       (mv nil (fn-judgement-clauses (smtj-fns smtj)) state)
                     (mv (msg "Smtlink: the SMT solver did not prove the goal ~
                               (it answered ~x0; the SMT-LIB script is ~
                               printed above)."
                              result)
                         nil state))))))))))))))

(define-trusted-clause-processor
  smtlink-trusted-cp
  (smtlink-goal rational-+ rational-- rational-* rational-/ rational-<))
