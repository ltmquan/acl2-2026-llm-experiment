; Erlang in ACL2: a continuation-passing style evaluator.
;
; This book defines
;   - the representation of Erlang values (tagged lists, see README.md),
;   - pattern matching and guard evaluation,
;   - the built-in functions (BIFs) we support,
;   - the estate (Erlang state) of a process,
;   - continuations, the single-continuation step function EVAL-CONT, and
;   - the CPS evaluator EVAL-CONT-LIST, which interprets a list of
;     continuations, consuming one unit of fuel for each continuation it
;     evaluates.  It yields to the scheduler on receive (and spawn), and
;     returns an out-of-fuel status when fuel is exhausted.
;
; The ASTs are those produced by the front end erl_to_acl2.erl; see README.md.

(in-package "ACL2")

(set-verify-guards-eagerness 0)

; ---------------------------------------------------------------------------
; Erlang values
;
;   (:integer i)              integers (same shape as the integer AST)
;   (:atom a)                 atoms, a is a symbol such as |true| (same as AST)
;   (:nil)                    the empty list (same as AST)
;   (:cons hd tl)             list cells
;   (:tuple (v1 ... vn))      tuples; the elements are a Lisp list
;   (:pid n)                  process identifiers
;   (:fun clauses env module name)   closures (name is nil or the named-fun name)
;   (:funref module name arity)      fun f/n and fun m:f/n
;
; Exceptions are not values; they are signals that flow through the
; continuation list:  (:exception class reason)  with class |error|, |throw|
; or |exit|.

(defun erl-val-integer (val) (list :integer val))
(defmacro make-erl-val-integer (&key val) `(erl-val-integer ,val))
(defun erl-val-integer->val (x) (cadr x))
(defun erl-val-integer-p (x) (and (consp x) (eq (car x) :integer) (integerp (cadr x))
                                  (null (cddr x))))

(defun erl-atom (a) (list :atom a))
(defun erl-val-atom-p (x) (and (consp x) (eq (car x) :atom) (symbolp (cadr x))))
(defun erl-pid (n) (list :pid n))
(defun erl-pid-p (x) (and (consp x) (eq (car x) :pid)))
(defun erl-tuple (vals) (list :tuple vals))
(defun erl-nil () (list :nil))
(defun erl-cons (h tl) (list :cons h tl))

(defun erl-bool (b) (if b (list :atom '|true|) (list :atom '|false|)))
(defmacro erl-true () ''(:atom |true|))
(defmacro erl-false () ''(:atom |false|))

(defun erl-exception (class reason) (list :exception class reason))
(defun erl-exception-p (v) (and (consp v) (eq (car v) :exception)))
(defun erl-error (reason) (erl-exception '|error| reason))
(defun erl-badarg () (erl-error (erl-atom '|badarg|)))
(defun erl-badarith () (erl-error (erl-atom '|badarith|)))

; Conversion between Lisp lists and Erlang lists
(defun lisp-to-erl-list (l)
  (if (atom l) (erl-nil) (erl-cons (car l) (lisp-to-erl-list (cdr l)))))

(defun erl-proper-list-p (v)
  (declare (xargs :measure (acl2-count v)))
  (cond ((atom v) nil)
        ((eq (car v) :nil) t)
        ((eq (car v) :cons) (erl-proper-list-p (caddr v)))
        (t nil)))

(defun erl-list-to-lisp (v)
  (declare (xargs :measure (acl2-count v)))
  (if (and (consp v) (eq (car v) :cons))
      (cons (cadr v) (erl-list-to-lisp (caddr v)))
    nil))

; AST lists (function arguments, tuple elements, patterns) are parsed
; Erlang lists (:cons a (:cons b (:nil))).
(defun ast-list-to-lisp (x)
  (declare (xargs :measure (acl2-count x)))
  (if (and (consp x) (eq (car x) :cons))
      (cons (cadr x) (ast-list-to-lisp (caddr x)))
    nil))

; Convenient constructors for ACL2-side test inputs:  (erl-ints '(1 2 3))
(defun erl-ints (l)
  (if (atom l) (erl-nil)
    (erl-cons (erl-val-integer (car l)) (erl-ints (cdr l)))))

; ---------------------------------------------------------------------------
; Erlang term order:  number < atom < fun < pid < tuple < nil < list

(defun erl-rank (v)
  (case (and (consp v) (car v))
    (:integer 0) (:atom 1) (:funref 3) (:fun 3) (:pid 5) (:tuple 6) (:nil 8) (:cons 9)
    (otherwise 10)))

(mutual-recursion
 (defun erl-cmp (a b)
   ; returns :lt, :eq or :gt
   (declare (xargs :measure (+ (acl2-count a) (acl2-count b))))
   (let ((ra (erl-rank a)) (rb (erl-rank b)))
     (cond ((< ra rb) :lt)
           ((< rb ra) :gt)
           (t (case ra
                (0 (let ((x (ifix (cadr a))) (y (ifix (cadr b))))
                     (cond ((< x y) :lt) ((< y x) :gt) (t :eq))))
                (1 (let ((x (cadr a)) (y (cadr b)))
                     (cond ((equal x y) :eq)
                           ((and (symbolp x) (symbolp y) (symbol< x y)) :lt)
                           (t :gt))))
                (5 (let ((x (nfix (cadr a))) (y (nfix (cadr b))))
                     (cond ((< x y) :lt) ((< y x) :gt) (t :eq))))
                (6 (let ((x (len (cadr a))) (y (len (cadr b))))
                     (cond ((< x y) :lt) ((< y x) :gt)
                           (t (erl-cmp-list (cadr a) (cadr b))))))
                (8 :eq)
                (9 (let ((c (erl-cmp (cadr a) (cadr b))))
                     (if (eq c :eq) (erl-cmp (caddr a) (caddr b)) c)))
                (otherwise (cond ((equal a b) :eq) ((lexorder a b) :lt) (t :gt))))))))
 (defun erl-cmp-list (as bs)
   (declare (xargs :measure (+ (acl2-count as) (acl2-count bs))))
   (cond ((or (atom as) (atom bs)) :eq)
         (t (let ((c (erl-cmp (car as) (car bs))))
              (if (eq c :eq) (erl-cmp-list (cdr as) (cdr bs)) c))))))

; ---------------------------------------------------------------------------
; Operators

(defun erl-int-args-p (a b)
  (and (erl-val-integer-p a) (erl-val-integer-p b)))

(defun erl-bool-val (v)
  ; :true, :false or nil (not a boolean)
  (cond ((equal v (erl-true)) :true)
        ((equal v (erl-false)) :false)
        (t nil)))

(defun erl-list-subtract (l r)
  (if (atom r) l (erl-list-subtract (remove1-equal (car r) l) (cdr r))))

(defun erl-append-lisp (l b)
  (if (atom l) b (erl-cons (car l) (erl-append-lisp (cdr l) b))))

(defun erl-binop (op a b)
  (case op
    (+ (if (erl-int-args-p a b) (erl-val-integer (+ (cadr a) (cadr b))) (erl-badarith)))
    (- (if (erl-int-args-p a b) (erl-val-integer (- (cadr a) (cadr b))) (erl-badarith)))
    (* (if (erl-int-args-p a b) (erl-val-integer (* (cadr a) (cadr b))) (erl-badarith)))
    (div (if (and (erl-int-args-p a b) (not (equal (cadr b) 0)))
             (erl-val-integer (truncate (cadr a) (cadr b)))
           (erl-badarith)))
    (rem (if (and (erl-int-args-p a b) (not (equal (cadr b) 0)))
             (erl-val-integer (rem (cadr a) (cadr b)))
           (erl-badarith)))
    (band (if (erl-int-args-p a b) (erl-val-integer (logand (cadr a) (cadr b))) (erl-badarith)))
    (bor (if (erl-int-args-p a b) (erl-val-integer (logior (cadr a) (cadr b))) (erl-badarith)))
    (bxor (if (erl-int-args-p a b) (erl-val-integer (logxor (cadr a) (cadr b))) (erl-badarith)))
    ((== |=:=|) (erl-bool (equal a b)))
    ((/= |=/=|) (erl-bool (not (equal a b))))
    (< (erl-bool (eq (erl-cmp a b) :lt)))
    (> (erl-bool (eq (erl-cmp a b) :gt)))
    (=< (erl-bool (not (eq (erl-cmp a b) :gt))))
    (>= (erl-bool (not (eq (erl-cmp a b) :lt))))
    (and (let ((x (erl-bool-val a)) (y (erl-bool-val b)))
           (if (and x y) (erl-bool (and (eq x :true) (eq y :true))) (erl-badarg))))
    (or (let ((x (erl-bool-val a)) (y (erl-bool-val b)))
          (if (and x y) (erl-bool (or (eq x :true) (eq y :true))) (erl-badarg))))
    (xor (let ((x (erl-bool-val a)) (y (erl-bool-val b)))
           (if (and x y) (erl-bool (not (eq x y))) (erl-badarg))))
    (++ (if (erl-proper-list-p a) (erl-append-lisp (erl-list-to-lisp a) b) (erl-badarg)))
    (-- (if (and (erl-proper-list-p a) (erl-proper-list-p b))
            (lisp-to-erl-list (erl-list-subtract (erl-list-to-lisp a) (erl-list-to-lisp b)))
          (erl-badarg)))
    (otherwise (erl-badarith))))

(defun erl-unop (op a)
  (case op
    (- (if (erl-val-integer-p a) (erl-val-integer (- (cadr a))) (erl-badarith)))
    (+ (if (erl-val-integer-p a) a (erl-badarith)))
    (bnot (if (erl-val-integer-p a) (erl-val-integer (lognot (cadr a))) (erl-badarith)))
    (not (let ((x (erl-bool-val a)))
           (if x (erl-bool (eq x :false)) (erl-badarg))))
    (otherwise (erl-badarith))))

; ---------------------------------------------------------------------------
; Built-in functions (pure ones).  SELF is the pid value of the caller.

(defun erl-nth-tuple (n l)
  ; element(N, T): 1-based
  (nth (1- n) l))

(defun erl-seq (lo n)
  ; [lo, lo+1, ..., lo+n-1]
  (if (zp n) nil (cons (erl-val-integer lo) (erl-seq (1+ lo) (1- n)))))

(defun erl-sum-list (l)
  (if (atom l) 0 (+ (ifix (cadr (car l))) (erl-sum-list (cdr l)))))

(defun erl-all-integers (l)
  (if (atom l) t (and (erl-val-integer-p (car l)) (erl-all-integers (cdr l)))))

(defun erl-bif (mod name args self)
  ; returns an Erlang value or an exception
  (let ((n (len args)) (a1 (car args)) (a2 (cadr args)))
    (cond
     ((and (eq mod '|erlang|) (= n 2)
           (member-eq name '(+ - * div rem band bor bxor == |=:=| /= |=/=| < > =< >=
                               and or xor ++ --)))
      ; erlang:'+'/2 etc.
      (erl-binop name a1 a2))
     ((eq mod '|erlang|)
      (case name
        (|self| (if (= n 0) self (erl-badarg)))
        (|is_integer| (erl-bool (erl-val-integer-p a1)))
        (|is_number| (erl-bool (erl-val-integer-p a1)))
        (|is_atom| (erl-bool (erl-val-atom-p a1)))
        (|is_boolean| (erl-bool (and (erl-bool-val a1) t)))
        (|is_list| (erl-bool (and (consp a1) (member-eq (car a1) '(:nil :cons)) t)))
        (|is_tuple| (erl-bool (and (consp a1) (eq (car a1) :tuple))))
        (|is_pid| (erl-bool (erl-pid-p a1)))
        (|is_function| (erl-bool (and (consp a1) (member-eq (car a1) '(:fun :funref)) t)))
        (|length| (if (erl-proper-list-p a1)
                      (erl-val-integer (len (erl-list-to-lisp a1)))
                    (erl-badarg)))
        (|hd| (if (and (consp a1) (eq (car a1) :cons)) (cadr a1) (erl-badarg)))
        (|tl| (if (and (consp a1) (eq (car a1) :cons)) (caddr a1) (erl-badarg)))
        (|tuple_size| (if (and (consp a1) (eq (car a1) :tuple))
                          (erl-val-integer (len (cadr a1)))
                        (erl-badarg)))
        (|element| (if (and (erl-val-integer-p a1) (consp a2) (eq (car a2) :tuple)
                            (<= 1 (cadr a1)) (<= (cadr a1) (len (cadr a2))))
                       (erl-nth-tuple (cadr a1) (cadr a2))
                     (erl-badarg)))
        (|abs| (if (erl-val-integer-p a1) (erl-val-integer (abs (cadr a1))) (erl-badarg)))
        (|max| (if (eq (erl-cmp a1 a2) :lt) a2 a1))
        (|min| (if (eq (erl-cmp a2 a1) :lt) a2 a1))
        (|not| (erl-unop 'not a1))
        (|tuple_to_list| (if (and (consp a1) (eq (car a1) :tuple))
                             (lisp-to-erl-list (cadr a1))
                           (erl-badarg)))
        (|list_to_tuple| (if (erl-proper-list-p a1)
                             (erl-tuple (erl-list-to-lisp a1))
                           (erl-badarg)))
        (|throw| (erl-exception '|throw| a1))
        (|error| (erl-exception '|error| a1))
        (|exit| (erl-exception '|exit| a1))
        (otherwise (erl-error (erl-tuple (list (erl-atom '|undef|) (erl-atom mod)
                                               (erl-atom name)))))))
     ((eq mod '|lists|)
      (case name
        (|reverse| (if (erl-proper-list-p a1)
                       (lisp-to-erl-list (reverse (erl-list-to-lisp a1)))
                     (erl-badarg)))
        (|append| (if (erl-proper-list-p a1) (erl-binop '++ a1 a2) (erl-badarg)))
        (|split| (if (and (erl-val-integer-p a1) (erl-proper-list-p a2) (<= 0 (cadr a1))
                          (<= (cadr a1) (len (erl-list-to-lisp a2))))
                     (let ((l (erl-list-to-lisp a2)))
                       (erl-tuple (list (lisp-to-erl-list (take (cadr a1) l))
                                        (lisp-to-erl-list (nthcdr (cadr a1) l)))))
                   (erl-badarg)))
        (|seq| (if (and (erl-val-integer-p a1) (erl-val-integer-p a2)
                        (<= (cadr a1) (+ 1 (cadr a2))))
                   (lisp-to-erl-list (erl-seq (cadr a1) (+ 1 (- (cadr a2) (cadr a1)))))
                 (erl-badarg)))
        (|sum| (if (and (erl-proper-list-p a1) (erl-all-integers (erl-list-to-lisp a1)))
                   (erl-val-integer (erl-sum-list (erl-list-to-lisp a1)))
                 (erl-badarg)))
        (|nth| (if (and (erl-val-integer-p a1) (erl-proper-list-p a2) (<= 1 (cadr a1))
                        (<= (cadr a1) (len (erl-list-to-lisp a2))))
                   (nth (1- (cadr a1)) (erl-list-to-lisp a2))
                 (erl-badarg)))
        (|last| (if (and (erl-proper-list-p a1) (consp (erl-list-to-lisp a1)))
                    (car (last (erl-list-to-lisp a1)))
                  (erl-badarg)))
        (|member| (if (erl-proper-list-p a2)
                      (erl-bool (member-equal a1 (erl-list-to-lisp a2)))
                    (erl-badarg)))
        (otherwise (erl-error (erl-tuple (list (erl-atom '|undef|) (erl-atom mod)
                                               (erl-atom name)))))))
     (t (erl-error (erl-tuple (list (erl-atom '|undef|) (erl-atom mod) (erl-atom name))))))))

; BIFs that may be used in guards
(defconst *erl-guard-bifs*
  '(|self| |is_integer| |is_number| |is_atom| |is_boolean| |is_list| |is_tuple| |is_pid|
    |is_function| |length| |hd| |tl| |tuple_size| |element| |abs| |max| |min| |not|))

; ---------------------------------------------------------------------------
; Pattern matching.  ENV is an alist from variable names to values.
; Literal patterns (:integer i), (:atom a), (:nil) have the same shape as
; the values they match.

(mutual-recursion
 (defun erl-match (pat val env)
   (declare (xargs :measure (acl2-count pat)))
   (if (atom pat)
       (mv nil env)
     (case (car pat)
       (:var (let ((name (cadr pat)))
               (if (eq name '|_|)
                   (mv t env)
                 (let ((b (assoc-equal name env)))
                   (if b
                       (mv (equal (cdr b) val) env)
                     (mv t (acons name val env)))))))
       ((:integer :atom :nil) (mv (equal pat val) env))
       (:cons (if (and (consp val) (eq (car val) :cons))
                  (mv-let (ok env1)
                    (erl-match (cadr pat) (cadr val) env)
                    (if ok (erl-match (caddr pat) (caddr val) env1) (mv nil env)))
                (mv nil env)))
       (:tuple (if (and (consp val) (eq (car val) :tuple))
                   (erl-match-list (cadr pat) (cadr val) env)
                 (mv nil env)))
       (:match (mv-let (ok env1)
                 (erl-match (cadr pat) val env)
                 (if ok (erl-match (caddr pat) val env1) (mv nil env))))
       (:unop (if (and (eq (cadr pat) '-) (consp (caddr pat))
                       (eq (car (caddr pat)) :integer))
                  (mv (equal val (erl-val-integer (- (ifix (cadr (caddr pat)))))) env)
                (mv nil env)))
       (otherwise (mv nil env)))))
 (defun erl-match-list (pats vals env)
   ; PATS is a parsed list (:cons p (:cons q (:nil))), VALS a Lisp list.
   (declare (xargs :measure (acl2-count pats)))
   (if (and (consp pats) (eq (car pats) :cons))
       (if (consp vals)
           (mv-let (ok env1)
             (erl-match (cadr pats) (car vals) env)
             (if ok (erl-match-list (caddr pats) (cdr vals) env1) (mv nil env)))
         (mv nil env))
     (mv (atom vals) env))))

; ---------------------------------------------------------------------------
; Guard expressions.  Guards are side-effect free, so we evaluate them
; directly rather than in CPS.  Any exception makes the guard fail.

(mutual-recursion
 (defun erl-geval (e env self)
   (declare (xargs :measure (acl2-count e)))
   (if (atom e)
       (erl-badarg)
     (case (car e)
       ((:integer :atom :nil) e)
       (:var (let ((b (assoc-equal (cadr e) env)))
               (if b (cdr b) (erl-error (erl-tuple (list (erl-atom '|unbound|)
                                                         (erl-atom (cadr e))))))))
       (:cons (let ((h (erl-geval (cadr e) env self)))
                (if (erl-exception-p h) h
                  (let ((tl (erl-geval (caddr e) env self)))
                    (if (erl-exception-p tl) tl (erl-cons h tl))))))
       (:tuple (let ((vs (erl-geval-list (cadr e) env self)))
                 (if (erl-exception-p vs) vs (erl-tuple vs))))
       (:binop (let ((op (cadr e)))
                 (let ((a (erl-geval (caddr e) env self)))
                   (cond ((erl-exception-p a) a)
                         ((eq op 'andalso)
                          (cond ((equal a (erl-true)) (erl-geval (cadddr e) env self))
                                ((equal a (erl-false)) a)
                                (t (erl-badarg))))
                         ((eq op 'orelse)
                          (cond ((equal a (erl-false)) (erl-geval (cadddr e) env self))
                                ((equal a (erl-true)) a)
                                (t (erl-badarg))))
                         (t (let ((b (erl-geval (cadddr e) env self)))
                              (if (erl-exception-p b) b (erl-binop op a b))))))))
       (:unop (let ((a (erl-geval (caddr e) env self)))
                (if (erl-exception-p a) a (erl-unop (cadr e) a))))
       (:call-local (if (member-eq (cadr e) *erl-guard-bifs*)
                        (let ((vs (erl-geval-list (caddr e) env self)))
                          (if (erl-exception-p vs) vs
                            (erl-bif '|erlang| (cadr e) vs self)))
                      (erl-badarg)))
       (:call-remote (if (and (eq (cadr e) '|erlang|)
                              (member-eq (caddr e) *erl-guard-bifs*))
                         (let ((vs (erl-geval-list (cadddr e) env self)))
                           (if (erl-exception-p vs) vs
                             (erl-bif '|erlang| (caddr e) vs self)))
                       (erl-badarg)))
       (otherwise (erl-badarg)))))
 (defun erl-geval-list (es env self)
   ; ES is a parsed list; returns a Lisp list of values or an exception
   (declare (xargs :measure (acl2-count es)))
   (if (and (consp es) (eq (car es) :cons))
       (let ((v (erl-geval (cadr es) env self)))
         (if (erl-exception-p v) v
           (let ((vs (erl-geval-list (caddr es) env self)))
             (if (erl-exception-p vs) vs (cons v vs)))))
     nil)))

(defun erl-guard-seq-true (gs env self)
  ; a comma-separated guard sequence: all must evaluate to true
  (if (atom gs) t
    (and (equal (erl-geval (car gs) env self) (erl-true))
         (erl-guard-seq-true (cdr gs) env self))))

(defun erl-guards-true-1 (guards env self)
  (if (atom guards) nil
    (or (erl-guard-seq-true (car guards) env self)
        (erl-guards-true-1 (cdr guards) env self))))

(defun erl-guards-true (guards env self)
  ; semicolon-separated guard sequences: no guard, or some sequence true
  (if (atom guards) t
    (erl-guards-true-1 guards env self)))

; ---------------------------------------------------------------------------
; Clause selection.  A clause is (:clause pats guards body), with PATS a
; parsed list, GUARDS a list of guard sequences, BODY a list of expressions.

(defun clause->pats (c) (cadr c))
(defun clause->guards (c) (caddr c))
(defun clause->body (c) (cadddr c))

(defun select-clause (clauses vals env self)
  ; For case, receive, if and try: patterns match against ENV (already-bound
  ; variables must have equal values).  Returns (mv found body new-env).
  (if (atom clauses)
      (mv nil nil env)
    (mv-let (ok env1)
      (erl-match-list (clause->pats (car clauses)) vals env)
      (if (and ok (erl-guards-true (clause->guards (car clauses)) env1 self))
          (mv t (clause->body (car clauses)) env1)
        (select-clause (cdr clauses) vals env self)))))

(defun select-fun-clause (clauses vals cenv self)
  ; For functions and funs: head variables are fresh; the body (and guard)
  ; also see the captured environment CENV (nil for module functions).
  (if (atom clauses)
      (mv nil nil cenv)
    (mv-let (ok env1)
      (erl-match-list (clause->pats (car clauses)) vals nil)
      (let ((env2 (append env1 cenv)))
        (if (and ok (erl-guards-true (clause->guards (car clauses)) env2 self))
            (mv t (clause->body (car clauses)) env2)
          (select-fun-clause (cdr clauses) vals cenv self))))))

(defun receive-match (inbox clauses env self)
  ; Erlang receive: messages oldest first, and for each message the clauses
  ; top to bottom.  Returns (mv found body new-env new-inbox), where
  ; new-inbox is the inbox with the matched message removed.
  (if (atom inbox)
      (mv nil nil env nil)
    (mv-let (found body env1)
      (select-clause clauses (list (car inbox)) env self)
      (if found
          (mv t body env1 (cdr inbox))
        (mv-let (found2 body2 env2 rest)
          (receive-match (cdr inbox) clauses env self)
          (mv found2 body2 env2 (cons (car inbox) rest)))))))

; ---------------------------------------------------------------------------
; Modules and logical worlds
;
; A module is (:module name exports imports functions) where exports is a
; list of (f . arity), imports a list of ((f . arity) . module) and functions
; an alist from (f . arity) to a list of clauses.  A logical world is an
; alist from module names to modules.

(defun module->name (m) (cadr m))
(defun module->exports (m) (caddr m))
(defun module->imports (m) (cadddr m))
(defun module->functions (m) (car (cddddr m)))

(defun erl-make-world (modules)
  (if (atom modules) nil
    (acons (module->name (car modules)) (car modules) (erl-make-world (cdr modules)))))

(defun erl-lookup-module (world mod)
  (cdr (assoc-equal mod world)))

(defun erl-lookup-fn (world mod name arity)
  (cdr (assoc-equal (cons name arity)
                    (module->functions (erl-lookup-module world mod)))))

(defun erl-lookup-import (world mod name arity)
  (cdr (assoc-equal (cons name arity)
                    (module->imports (erl-lookup-module world mod)))))

; ---------------------------------------------------------------------------
; The estate (Erlang state) of a process:
;   val     the value produced by the previous continuation (or :none, or a
;           tagged yield / exception)
;   env     current variable bindings
;   module  the current module
;   world   the logical world
;   self    the pid value of this process
;   inbox   message queue, oldest first (maintained by the scheduler)
;   outbox  alist from destination pid to the queue of messages sent to it
;           during the current execution segment, oldest first

(defun make-estate (val env module world self inbox outbox)
  (list val env module world self inbox outbox))

(defun estate->val (s) (nth 0 s))
(defun estate->env (s) (nth 1 s))
(defun estate->module (s) (nth 2 s))
(defun estate->world (s) (nth 3 s))
(defun estate->self (s) (nth 4 s))
(defun estate->inbox (s) (nth 5 s))
(defun estate->outbox (s) (nth 6 s))

(defun update-estate->val (s v)
  (make-estate v (estate->env s) (estate->module s) (estate->world s)
               (estate->self s) (estate->inbox s) (estate->outbox s)))
(defun update-estate->env (s env)
  (make-estate (estate->val s) env (estate->module s) (estate->world s)
               (estate->self s) (estate->inbox s) (estate->outbox s)))
(defun update-estate->inbox (s inbox)
  (make-estate (estate->val s) (estate->env s) (estate->module s) (estate->world s)
               (estate->self s) inbox (estate->outbox s)))
(defun update-estate->outbox (s outbox)
  (make-estate (estate->val s) (estate->env s) (estate->module s) (estate->world s)
               (estate->self s) (estate->inbox s) outbox))
(defun update-estate-call (s val env module)
  (make-estate val env module (estate->world s)
               (estate->self s) (estate->inbox s) (estate->outbox s)))

(defun outbox-send (outbox dest msg)
  ; append MSG to the queue for DEST
  (put-assoc-equal dest (append (cdr (assoc-equal dest outbox)) (list msg)) outbox))

; ---------------------------------------------------------------------------
; Continuations.  Each is a tagged list performing one primitive operation;
; it receives the value of the previous continuation in (estate->val s).
;
;   (:expr ast)               evaluate AST
;   (:exprs asts)             evaluate a body (sequence), value of the last
;   (:binop1 op right)        got left operand; evaluate RIGHT
;   (:binop2 op left)         got right operand; apply OP
;   (:andalso right) (:orelse right)   short-circuit operators
;   (:unop op)
;   (:match pat)              match the value against PAT
;   (:args-acc todo acc)      collecting argument values
;   (:mk-tuple)  (:cons1 tl)  (:cons2 hd)
;   (:send1 msg) (:send2 dest)
;   (:case clauses)
;   (:receive clauses)        first encounter of receive: yield
;   (:receive2 clauses)       resumed by the scheduler: look for a message
;   (:call-local name)        the value is the list of argument values
;   (:call-remote module name)
;   (:call-fun1 args) (:call-fun2 fun)
;   (:restore env module)     return from a function call
;   (:try-of of-clauses catch-clauses)
;   (:after body) (:restore-val v)
;   (:catch)

(defmacro cont-expr (&key expr) `(list :expr ,expr))
(defmacro cont-exprs (&key exprs) `(list :exprs ,exprs))
(defmacro cont-binop1 (&key op right_expr) `(list :binop1 ,op ,right_expr))
(defmacro cont-binop2 (&key op left) `(list :binop2 ,op ,left))
(defmacro cont-receive (&key clauses) `(list :receive ,clauses))
(defmacro cont-receive2 (&key clauses) `(list :receive2 ,clauses))
(defmacro cont-call-local (&key name) `(list :call-local ,name))
(defmacro cont-call-remote (&key module name) `(list :call-remote ,module ,name))
(defmacro cont-call-fun2 (&key fun) `(list :call-fun2 ,fun))
(defmacro cont-restore (&key env module) `(list :restore ,env ,module))

; Continuations that act even when the incoming value is an exception.
(defconst *exception-conts* '(:expr :restore :try-of :catch :after :restore-val))

(defun push-args (asts then rest s)
  ; Evaluate the parsed list of ASTs, then run THEN with the Lisp list of
  ; values as the incoming value.
  (if (and (consp asts) (eq (car asts) :cons))
      (mv nil
          (list* (list :expr (cadr asts)) (list :args-acc (caddr asts) nil) then rest)
          (update-estate->val s :none))
    (mv nil (cons then rest) (update-estate->val s nil))))

(defun do-call (body env module rest s)
  ; Enter a function body.  A (:restore ...) continuation returns to the
  ; caller's environment; for tail calls (the next continuation is already
  ; a restore) no new one is pushed: tail-call elimination.
  (let ((rest2 (if (and (consp rest) (eq (car (car rest)) :restore))
                   rest
                 (cons (list :restore (estate->env s) (estate->module s)) rest))))
    (mv nil (cons (list :exprs body) rest2) (update-estate-call s :none env module))))

(defun apply-clauses (clauses args cenv module fname rest s)
  (mv-let (found body env)
    (select-fun-clause clauses args cenv (estate->self s))
    (if found
        (do-call body env module rest s)
      (mv nil rest (update-estate->val
                    s (erl-error (erl-tuple (list (erl-atom '|function_clause|)
                                                  (erl-atom fname)))))))))

(defun call-remote (mod name args rest s)
  (let ((clauses (erl-lookup-fn (estate->world s) mod name (len args))))
    (cond (clauses (apply-clauses clauses args nil mod name rest s))
          ((and (member-eq mod '(|erlang|)) (eq name '|spawn|) (= (len args) 1))
           ; spawn is a globally visible action: yield to the scheduler
           (mv t nil (update-estate->val s (list :spawn (car args) rest))))
          (t (mv nil rest (update-estate->val s (erl-bif mod name args
                                                         (estate->self s))))))))

(defun call-local (name args rest s)
  (let* ((world (estate->world s))
         (mod (estate->module s))
         (clauses (erl-lookup-fn world mod name (len args))))
    (if clauses
        (apply-clauses clauses args nil mod name rest s)
      (let ((imp (erl-lookup-import world mod name (len args))))
        (call-remote (or imp '|erlang|) name args rest s)))))

(defun call-fun-value (f args rest s)
  (cond ((and (consp f) (eq (car f) :fun))
         ; (:fun clauses env module name)
         (let* ((clauses (nth 1 f)) (cenv (nth 2 f)) (cmod (nth 3 f)) (name (nth 4 f))
                (cenv (if name (acons name f cenv) cenv)))
           (apply-clauses clauses args cenv cmod '|fun| rest s)))
        ((and (consp f) (eq (car f) :funref) (equal (len args) (nth 3 f)))
         (call-remote (nth 1 f) (nth 2 f) args rest s))
        (t (mv nil rest (update-estate->val
                         s (erl-error (erl-tuple (list (erl-atom '|badfun|) f))))))))

(defun catch-value (ex)
  ; the value of `catch Expr' when Expr raised EX
  (let ((class (cadr ex)) (reason (caddr ex)))
    (cond ((eq class '|throw|) reason)
          ((eq class '|exit|) (erl-tuple (list (erl-atom 'exit) reason)))
          (t (erl-tuple (list (erl-atom '|EXIT|)
                              (erl-tuple (list reason (erl-nil)))))))))

(defun eval-expr (ast rest s)
  ; The (:expr ast) continuation.
  (let ((env (estate->env s)) (self (estate->self s)))
    (case (and (consp ast) (car ast))
      ((:integer :atom :nil) (mv nil rest (update-estate->val s ast)))
      (:var (let ((b (assoc-equal (cadr ast) env)))
              (mv nil rest
                  (update-estate->val
                   s (if b (cdr b)
                       (erl-error (erl-tuple (list (erl-atom '|unbound|)
                                                   (erl-atom (cadr ast))))))))))
      (:cons (mv nil (list* (list :expr (cadr ast)) (list :cons1 (caddr ast)) rest)
                 (update-estate->val s :none)))
      (:tuple (push-args (cadr ast) (list :mk-tuple) rest s))
      (:binop (let ((op (cadr ast)))
                (mv nil
                    (list* (list :expr (caddr ast))
                           (cond ((eq op 'andalso) (list :andalso (cadddr ast)))
                                 ((eq op 'orelse) (list :orelse (cadddr ast)))
                                 (t (list :binop1 op (cadddr ast))))
                           rest)
                    (update-estate->val s :none))))
      (:unop (mv nil (list* (list :expr (caddr ast)) (list :unop (cadr ast)) rest)
                 (update-estate->val s :none)))
      (:match (mv nil (list* (list :expr (caddr ast)) (list :match (cadr ast)) rest)
                  (update-estate->val s :none)))
      (:send (mv nil (list* (list :expr (cadr ast)) (list :send1 (caddr ast)) rest)
                 (update-estate->val s :none)))
      (:block (mv nil (cons (list :exprs (cadr ast)) rest) (update-estate->val s :none)))
      (:if (mv-let (found body env1)
             (select-clause (cadr ast) nil env self)
             (if found
                 (mv nil (cons (list :exprs body) rest)
                     (update-estate->val (update-estate->env s env1) :none))
               (mv nil rest (update-estate->val s (erl-error (erl-atom '|if_clause|)))))))
      (:case (mv nil (list* (list :expr (cadr ast)) (list :case (caddr ast)) rest)
                 (update-estate->val s :none)))
      (:receive (mv nil (cons (list :receive (cadr ast)) rest) (update-estate->val s :none)))
      (:try (let* ((body (nth 1 ast)) (of (nth 2 ast)) (catch (nth 3 ast))
                   (after (nth 4 ast))
                   (rest1 (if (consp after) (cons (list :after after) rest) rest)))
              (mv nil (list* (list :exprs body) (list :try-of of catch) rest1)
                  (update-estate->val s :none))))
      (:catch (mv nil (list* (list :expr (cadr ast)) (list :catch) rest)
                  (update-estate->val s :none)))
      (:fun (mv nil rest (update-estate->val
                          s (list :fun (cadr ast) env (estate->module s) nil))))
      (:named-fun (mv nil rest (update-estate->val
                                s (list :fun (caddr ast) env (estate->module s) (cadr ast)))))
      (:fun-ref (mv nil rest (update-estate->val
                              s (list :funref (estate->module s) (cadr ast) (caddr ast)))))
      (:fun-ref-remote (mv nil rest (update-estate->val
                                     s (list :funref (cadr ast) (caddr ast) (cadddr ast)))))
      (:call-local (push-args (caddr ast) (list :call-local (cadr ast)) rest s))
      (:call-remote (push-args (cadddr ast) (list :call-remote (cadr ast) (caddr ast)) rest s))
      (:call-fun (mv nil (list* (list :expr (cadr ast)) (list :call-fun1 (caddr ast)) rest)
                     (update-estate->val s :none)))
      (otherwise (mv nil rest (update-estate->val
                               s (erl-error (erl-tuple (list (erl-atom '|unsupported|)
                                                             ast)))))))))

(defun eval-cont (k rest s)
  ; Evaluate the single continuation K, whose successors are REST.
  ; Returns (mv yield new-klist new-estate).  When YIELD is true the process
  ; yields to the scheduler and the estate's val describes why:
  ;   (:receive klist clauses)  blocked in a receive
  ;   (:spawn fun klist)        spawn request
  (let ((val (estate->val s)) (tag (and (consp k) (car k))))
    (if (and (erl-exception-p val) (not (member-eq tag *exception-conts*)))
        ; an exception propagates past continuations that cannot handle it
        (mv nil rest s)
      (case tag
        (:expr (eval-expr (cadr k) rest s))
        (:exprs (let ((es (cadr k)))
                  (cond ((atom es) (mv nil rest s))
                        ((atom (cdr es)) (mv nil (cons (list :expr (car es)) rest)
                                             (update-estate->val s :none)))
                        (t (mv nil (list* (list :expr (car es)) (list :exprs (cdr es)) rest)
                               (update-estate->val s :none))))))
        (:binop1 (mv nil (list* (list :expr (caddr k)) (list :binop2 (cadr k) val) rest)
                     (update-estate->val s :none)))
        (:binop2 (mv nil rest (update-estate->val s (erl-binop (cadr k) (caddr k) val))))
        (:andalso (cond ((equal val (erl-true))
                         (mv nil (cons (list :expr (cadr k)) rest) (update-estate->val s :none)))
                        ((equal val (erl-false)) (mv nil rest s))
                        (t (mv nil rest (update-estate->val s (erl-badarg))))))
        (:orelse (cond ((equal val (erl-false))
                        (mv nil (cons (list :expr (cadr k)) rest) (update-estate->val s :none)))
                       ((equal val (erl-true)) (mv nil rest s))
                       (t (mv nil rest (update-estate->val s (erl-badarg))))))
        (:unop (mv nil rest (update-estate->val s (erl-unop (cadr k) val))))
        (:match (mv-let (ok env1)
                  (erl-match (cadr k) val (estate->env s))
                  (if ok
                      (mv nil rest (update-estate->env s env1))
                    (mv nil rest (update-estate->val
                                  s (erl-error (erl-tuple (list (erl-atom '|badmatch|) val))))))))
        (:args-acc (let ((todo (cadr k)) (acc (cons val (caddr k))))
                     (if (and (consp todo) (eq (car todo) :cons))
                         (mv nil (list* (list :expr (cadr todo)) (list :args-acc (caddr todo) acc)
                                        rest)
                             (update-estate->val s :none))
                       (mv nil rest (update-estate->val s (reverse acc))))))
        (:mk-tuple (mv nil rest (update-estate->val s (erl-tuple val))))
        (:cons1 (mv nil (list* (list :expr (cadr k)) (list :cons2 val) rest)
                    (update-estate->val s :none)))
        (:cons2 (mv nil rest (update-estate->val s (erl-cons (cadr k) val))))
        (:send1 (mv nil (list* (list :expr (cadr k)) (list :send2 val) rest)
                    (update-estate->val s :none)))
        (:send2 (let ((dest (cadr k)))
                  (if (erl-pid-p dest)
                      (mv nil rest (update-estate->outbox
                                    s (outbox-send (estate->outbox s) dest val)))
                    (mv nil rest (update-estate->val s (erl-badarg))))))
        (:case (mv-let (found body env1)
                 (select-clause (cadr k) (list val) (estate->env s) (estate->self s))
                 (if found
                     (mv nil (cons (list :exprs body) rest)
                         (update-estate->val (update-estate->env s env1) :none))
                   (mv nil rest (update-estate->val
                                 s (erl-error (erl-tuple (list (erl-atom '|case_clause|)
                                                               val))))))))
        (:receive (mv t nil (update-estate->val s (list :receive rest (cadr k)))))
        (:receive2 (mv-let (found body env1 inbox1)
                     (receive-match (estate->inbox s) (cadr k) (estate->env s)
                                    (estate->self s))
                     (if found
                         (mv nil (cons (list :exprs body) rest)
                             (update-estate->val
                              (update-estate->inbox (update-estate->env s env1) inbox1)
                              :none))
                       ; no matching message: yield to the scheduler again
                       (mv t nil (update-estate->val s (list :receive rest (cadr k)))))))
        (:call-local (call-local (cadr k) val rest s))
        (:call-remote (call-remote (cadr k) (caddr k) val rest s))
        (:call-fun1 (push-args (cadr k) (list :call-fun2 val) rest s))
        (:call-fun2 (call-fun-value (cadr k) val rest s))
        (:restore (mv nil rest (update-estate-call s val (cadr k) (caddr k))))
        (:try-of (let ((of (cadr k)) (catch (caddr k)))
                   (if (erl-exception-p val)
                       (mv-let (found body env1)
                         (select-clause catch
                                        (list (erl-tuple (list (erl-atom (cadr val)) (caddr val)
                                                               (erl-nil))))
                                        (estate->env s) (estate->self s))
                         (if found
                             (mv nil (cons (list :exprs body) rest)
                                 (update-estate->val (update-estate->env s env1) :none))
                           (mv nil rest s)))
                     (if (atom of)
                         (mv nil rest s)
                       (mv-let (found body env1)
                         (select-clause of (list val) (estate->env s) (estate->self s))
                         (if found
                             (mv nil (cons (list :exprs body) rest)
                                 (update-estate->val (update-estate->env s env1) :none))
                           (mv nil rest (update-estate->val
                                         s (erl-error (erl-tuple (list (erl-atom '|try_clause|)
                                                                       val)))))))))))
        (:after (mv nil (list* (list :exprs (cadr k)) (list :restore-val val) rest)
                    (update-estate->val s :none)))
        (:restore-val (if (erl-exception-p val) (mv nil rest s)
                        (mv nil rest (update-estate->val s (cadr k)))))
        (:catch (if (erl-exception-p val)
                    (mv nil rest (update-estate->val s (catch-value val)))
                  (mv nil rest s)))
        (otherwise (mv nil rest (update-estate->val
                                 s (erl-error (erl-tuple (list (erl-atom '|bad_continuation|)
                                                               k))))))))))

; ---------------------------------------------------------------------------
; The CPS evaluator.  Interprets the continuation list KLIST, one unit of
; FUEL per continuation.  Returns the final estate:
;   - KLIST exhausted: the process exits; val is its exit value (or exception)
;   - yield on receive/spawn: val is (:receive ...) or (:spawn ...)
;   - fuel exhausted: val is (:out-of-fuel klist)

(defun eval-cont-list (klist estate fuel)
  (declare (xargs :measure (nfix fuel)))
  (cond ((atom klist) estate)
        ((zp fuel) (update-estate->val estate (list :out-of-fuel klist)))
        (t (mv-let (yield klist2 estate2)
             (eval-cont (car klist) (cdr klist) estate)
             (if yield
                 estate2
               (eval-cont-list klist2 estate2 (1- fuel)))))))

(defun erl-out-of-fuel-p (v) (and (consp v) (eq (car v) :out-of-fuel)))

; Status of the result of eval-cont-list
(defun eval-status (s)
  (let ((v (estate->val s)))
    (cond ((erl-out-of-fuel-p v) :out-of-fuel)
          ((and (consp v) (eq (car v) :receive)) :blocked)
          ((and (consp v) (eq (car v) :spawn)) :spawn)
          ((erl-exception-p v) :exception)
          (t :done))))

; Evaluate a single (sequential) call MOD:FN(ARGS) in WORLD, without a
; scheduler (no receive/spawn).  Useful for sequential code.
(defun erl-initial-estate (world mod self)
  (make-estate :none nil mod world self nil nil))

(defun erl-eval-call (world mod fn args fuel)
  (eval-cont-list (list (list :call-remote mod fn))
                  (update-estate->val (erl-initial-estate world mod (erl-pid 0)) args)
                  fuel))

; ---------------------------------------------------------------------------
; Printing Erlang values in Erlang syntax (as io:format("~w") does), for
; tests and examples.

(defun erl-int-string (i)
  (coerce (explode-atom i 10) 'string))

(mutual-recursion
 (defun erl-format (v)
   (declare (xargs :measure (* 2 (acl2-count v))))
   (if (atom v)
       "?"
     (case (car v)
       (:integer (erl-int-string (cadr v)))
       (:atom (if (symbolp (cadr v)) (symbol-name (cadr v)) "?"))
       (:nil "[]")
       (:cons (concatenate 'string "[" (erl-format (cadr v))
                           (erl-format-tail (caddr v)) "]"))
       (:tuple (concatenate 'string "{" (erl-format-elems (cadr v)) "}"))
       (:pid (concatenate 'string "<0." (erl-int-string (cadr v)) ".0>"))
       ((:fun :funref) "#Fun")
       (:exception (concatenate 'string "EXCEPTION "
                                (if (symbolp (cadr v)) (symbol-name (cadr v)) "?")
                                ":" (erl-format (caddr v))))
       (otherwise "?"))))
 (defun erl-format-tail (v)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count v)))))
   (cond ((and (consp v) (eq (car v) :nil)) "")
         ((and (consp v) (eq (car v) :cons))
          (concatenate 'string "," (erl-format (cadr v)) (erl-format-tail (caddr v))))
         (t (concatenate 'string "|" (erl-format v)))))
 (defun erl-format-elems (vs)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count vs)))))
   (cond ((atom vs) "")
         ((atom (cdr vs)) (erl-format (car vs)))
         (t (concatenate 'string (erl-format (car vs)) "," (erl-format-elems (cdr vs)))))))
