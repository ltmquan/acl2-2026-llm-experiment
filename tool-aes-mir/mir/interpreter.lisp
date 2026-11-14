; MIR semantics: the interpreter.
;
; Small-step at the level of statements and terminators (each statement, and
; each terminator, including a call of a modeled standard-library function,
; is one machine step); big-step, functional evaluation of places, operands,
; and rvalues.
;
; Operating assumptions (adequate for the AES crate):
;  - 64-bit target (usize is 64 bits; the importer checks the target);
;  - abort on panic: unwind edges are dropped at import, and a panic ends the
;    run with a :panic outcome;
;  - moves read without de-initializing (a borrow-checked program never reads
;    a moved-from place);
;  - drops are no-ops (the importer rejects drop statements; the crate has
;    none).

(in-package "MIR")

(include-book "stdlib")

(set-induction-depth-limit 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constants

(defines constant->value
  :verify-guards nil
  (define constant->value ((c constant-p))
    :returns (v value-p)
    :measure (constant-count c)
    (constant-case c
      :int (value-int c.it c.v)
      :bool (value-bool c.b)
      :adt (value-adt c.variant (constant-list->values c.fields))
      :str (value-str c.s)
      :other (value-uninit)))
  (define constant-list->values ((cs constant-list-p))
    :returns (vs value-list-p)
    :measure (constant-list-count cs)
    (if (atom cs)
        nil
      (cons (constant->value (car cs))
            (constant-list->values (cdr cs)))))
  ///
  (verify-guards constant->value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Places

(define frame-local ((depth natp) (i natp) (st mstate-p))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (v value-p))
  (read-loc (loc (locbase-local depth i) nil) st))

;; The index operand of an Index projection is a local in MIR (and an
;; integer constant after constant propagation).
(define eval-index-operand ((op operand-p) (depth natp) (st mstate-p))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (i natp :rule-classes :type-prescription))
  (b* (((mv err v)
        (operand-case op
          :const (mv nil (constant->value op.c))
          :otherwise
          (b* ((p (case (operand-kind op)
                    (:copy (operand-copy->place op))
                    (:move (operand-move->place op))
                    (otherwise (operand-read->place op)))))
            (place-case p
              :local (frame-local depth p.index st)
              :otherwise (mv "index operand is not a local" (value-uninit))))))
       ((when err) (mv err 0)))
    (value-case v
      :int (if (natp v.v) (mv nil v.v) (mv "negative index" 0))
      :otherwise (mv "index operand is not an integer" 0))))

;; The location a place designates, in the frame at the given depth.
(define eval-place ((p place-p) (depth natp) (st mstate-p))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (l loc-p))
  :measure (place-count p)
  :verify-guards nil
  (place-case p
    :local (mv nil (loc (locbase-local depth p.index) nil))
    :global (mv nil (loc (locbase-global p.id) nil))
    :proj
    (b* (((mv err l) (eval-place p.base depth st))
         ((when err) (mv err l)))
      (projelem-case p.elem
        :deref (b* (((mv err v) (read-loc l st))
                    ((when err) (mv err l)))
                 (value-case v
                   :ptr (mv nil v.loc)
                   :otherwise (mv "dereference of a non-pointer" l)))
        :field (mv nil (loc-extend l (pathelem-field p.elem.variant p.elem.index)))
        :index (b* (((mv err i) (eval-index-operand p.elem.offset depth st))
                    ((when err) (mv err l))
                    ((unless p.elem.from-end)
                     (mv nil (loc-extend l (pathelem-index i))))
                    ((mv err v) (read-loc l st))
                    ((when err) (mv err l)))
                 (value-case v
                   :array (if (and (< 0 i) (<= i (len v.elems)))
                              (mv nil (loc-extend l (pathelem-index (- (len v.elems) i))))
                            (mv "index from end out of bounds" l))
                   :otherwise (mv "index into a non-array" l)))
        :ptr-metadata (mv "pointer metadata is not a place" l)))))

(verify-guards eval-place)

;; Reading a place.  The pointer-metadata projection p.metadata yields the
;; length of the slice that the pointer p designates.
(define read-place ((p place-p) (depth natp) (st mstate-p))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (v value-p))
  (b* (((when (and (place-case p :proj)
                   (projelem-case (place-proj->elem p) :ptr-metadata)))
        (b* (((mv err l) (eval-place (place-proj->base p) depth st))
             ((when err) (mv err (value-uninit)))
             ((mv err ptr) (read-loc l st))
             ((when err) (mv err (value-uninit))))
          (value-case ptr
            :ptr (b* (((mv err target) (read-loc ptr.loc st))
                      ((when err) (mv err (value-uninit))))
                   (value-case target
                     :array (mv nil (value-usize (len target.elems)))
                     :str (mv nil (value-usize (length target.s)))
                     :otherwise (mv nil (value-unit))))
            :otherwise (mv "metadata of a non-pointer" (value-uninit)))))
       ((mv err l) (eval-place p depth st))
       ((when err) (mv err (value-uninit))))
    (read-loc l st)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Operands and rvalues

(define eval-operand ((op operand-p) (depth natp) (st mstate-p))
  :returns (mv (oc outcome-p) (v value-p))
  (b* (((when (operand-case op :const))
        (mv (ok-outcome) (constant->value (operand-const->c op))))
       (p (case (operand-kind op)
            (:copy (operand-copy->place op))
            (:move (operand-move->place op))
            (otherwise (operand-read->place op))))
       ((mv err v) (read-place p depth st))
       ((when err) (mv (err-outcome err) (value-uninit)))
       ((when (value-case v :uninit))
        (mv (outcome-error "read of an uninitialized place") (value-uninit))))
    (mv (ok-outcome) v)))

(define eval-operands ((ops operand-list-p) (depth natp) (st mstate-p))
  :returns (mv (oc outcome-p) (vs value-list-p))
  (b* (((when (atom ops)) (mv (ok-outcome) nil))
       ((mv oc v) (eval-operand (car ops) depth st))
       ((unless (outcome-ok-p oc)) (mv oc nil))
       ((mv oc vs) (eval-operands (cdr ops) depth st))
       ((unless (outcome-ok-p oc)) (mv oc nil)))
    (mv (ok-outcome) (cons v vs))))

(define eval-rvalue ((rv rvalue-p) (depth natp) (st mstate-p))
  :returns (mv (oc outcome-p) (v value-p))
  (rvalue-case rv
    :use (eval-operand rv.op depth st)
    :ref (b* (((mv err l) (eval-place rv.place depth st))
              ((when err) (mv (err-outcome err) (value-uninit))))
           (mv (ok-outcome) (value-ptr l)))
    :rawptr (b* (((mv err l) (eval-place rv.place depth st))
                 ((when err) (mv (err-outcome err) (value-uninit))))
              (mv (ok-outcome) (value-ptr l)))
    :binop (b* (((mv oc a) (eval-operand rv.a depth st))
                ((unless (outcome-ok-p oc)) (mv oc (value-uninit)))
                ((mv oc b) (eval-operand rv.b depth st))
                ((unless (outcome-ok-p oc)) (mv oc (value-uninit))))
             (eval-binop rv.op a b))
    :unop (b* (((mv oc a) (eval-operand rv.a depth st))
               ((unless (outcome-ok-p oc)) (mv oc (value-uninit))))
            (eval-unop rv.op a))
    :discriminant (b* (((mv err v) (read-place rv.place depth st))
                       ((when err) (mv (err-outcome err) (value-uninit))))
                    (value-case v
                      :adt (mv (ok-outcome) (value-int :isize (nfix v.variant)))
                      :otherwise (mv (outcome-error "discriminant of a non-enum")
                                     (value-uninit))))
    :aggregate (b* (((mv oc vs) (eval-operands rv.ops depth st))
                    ((unless (outcome-ok-p oc)) (mv oc (value-uninit))))
                 (aggkind-case rv.kind
                   :adt (mv (ok-outcome) (value-adt rv.kind.variant vs))
                   :array (mv (ok-outcome) (value-array vs))))
    :repeat (b* (((mv oc v) (eval-operand rv.op depth st))
                 ((unless (outcome-ok-p oc)) (mv oc (value-uninit))))
              (mv (ok-outcome) (value-array (value-list-repeat rv.count v))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Frames

(define top-frame ((st mstate-p))
  :returns (f (implies f (frame-p f)))
  (let ((frames (mstate->frames st)))
    (if (consp frames) (frame-fix (car frames)) nil)))

(define set-top-frame ((f frame-p) (st mstate-p))
  :returns (st2 mstate-p)
  (let ((frames (mstate->frames st)))
    (change-mstate st :frames (cons (frame-fix f)
                                    (if (consp frames) (cdr frames) nil)))))

(define frame-goto ((f frame-p) (target natp))
  :returns (f2 frame-p)
  (change-frame f :block target :stmt 0))

(define set-local ((i natp) (v value-p) (f frame-p))
  :returns (f2 frame-p)
  (change-frame f :locals (value-list-update i v (frame->locals f))))

(define init-locals ((n natp) (args value-list-p))
  ;; _0 (the return place) uninitialized, then the arguments, then the
  ;; remaining locals uninitialized.
  :returns (l value-list-p)
  (b* ((nargs (len args))
       (rest (nfix (- (lnfix n) (+ 1 nargs)))))
    (cons (value-uninit)
          (append (value-list-fix args) (value-list-repeat rest (value-uninit))))))

(define new-frame ((id natp) (b body-p) (args value-list-p))
  :returns (f frame-p)
  (frame id b (init-locals (body->local-count b) args) 0 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Statements

(define exec-statement ((s statement-p) (st mstate-p))
  :returns (mv (oc outcome-p) (st2 mstate-p))
  (b* ((depth (mstate-top-depth st))
       ((unless (natp depth)) (mv (outcome-error "no frame") (mstate-fix st)))
       (f (top-frame st))
       ((unless f) (mv (outcome-error "no frame") (mstate-fix st))))
    (statement-case s
      :assign (b* (((mv oc v) (eval-rvalue s.rv depth st))
                   ((unless (outcome-ok-p oc)) (mv oc (mstate-fix st)))
                   ((mv err l) (eval-place s.place depth st))
                   ((when err) (mv (err-outcome err) (mstate-fix st)))
                   ((mv err st) (write-loc l v st))
                   ((when err) (mv (err-outcome err) (mstate-fix st))))
                (mv (ok-outcome) st))
      :storage-live (mv (ok-outcome) (set-top-frame (set-local s.local (value-uninit) f) st))
      :storage-dead (mv (ok-outcome) (set-top-frame (set-local s.local (value-uninit) f) st))
      :nop (mv (ok-outcome) (mstate-fix st)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Terminators

(define switch-target ((v value-p) (branches switch-branch-list-p) (otherwise natp))
  :returns (target natp :rule-classes :type-prescription)
  (b* (((when (atom branches)) (lnfix otherwise))
       ((switch-branch br) (car branches))
       (c (constant->value br.value))
       (match (or (and (value-case v :int) (value-case c :int)
                       (equal (value-int->v v) (value-int->v c)))
                  (and (value-case v :bool) (value-case c :bool)
                       (equal (value-bool->b v) (value-bool->b c))))))
    (if match br.target (switch-target v (cdr branches) otherwise))))

(define next-static-id ((al value-alist-p))
  :returns (id natp :rule-classes :type-prescription)
  (cond ((atom al) 1000000)
        ((consp (car al)) (max (+ 1 (nfix (caar al))) (next-static-id (cdr al))))
        (t (next-static-id (cdr al)))))

;; Finish the run when the bottom frame returns.  A pointer into the bottom
;; frame's own locals (a promoted constant's initializer returns one) is
;; redirected to a fresh static allocation holding that local's value.
(define final-return ((v value-p) (st mstate-p))
  :returns (mv (oc outcome-p) (st2 mstate-p))
  (b* (((unless (value-case v :ptr)) (mv (outcome-returned v) (mstate-fix st)))
       (l (value-ptr->loc v))
       (b (loc->base l))
       ((unless (and (locbase-case b :local) (equal (locbase-local->frame b) 0)))
        (mv (outcome-returned v) (mstate-fix st)))
       ((mv err pointee) (read-base b st))
       ((when err) (mv (err-outcome err) (mstate-fix st)))
       (id (next-static-id (mstate->statics st)))
       (st (change-mstate st :statics (value-alist-store id pointee (mstate->statics st)))))
    (mv (outcome-returned (value-ptr (change-loc l :base (locbase-static id))))
        st)))

;; Return from the top frame into its caller, which is stopped at the Call
;; terminator that created the frame.
(define exec-return ((st mstate-p))
  :returns (mv (oc outcome-p) (st2 mstate-p))
  (b* ((f (top-frame st))
       ((unless f) (mv (outcome-error "return without a frame") (mstate-fix st)))
       (v (value-list-nth 0 (frame->locals f)))
       ((when (value-case v :uninit))
        (mv (outcome-error "return place uninitialized") (mstate-fix st)))
       ((when (atom (cdr (mstate->frames st)))) (final-return v st))
       (st (change-mstate st :frames (cdr (mstate->frames st))))
       (caller (top-frame st))
       ((unless caller) (mv (outcome-error "no caller") st))
       (blk (body-block (frame->block caller) (frame->body caller)))
       ((unless blk) (mv (outcome-error "bad caller block") st))
       (term (bblock->term blk))
       ((unless (terminator-case term :call))
        (mv (outcome-error "caller not at a call") st))
       (depth (mstate-top-depth st))
       ((unless (natp depth)) (mv (outcome-error "no frame") st))
       ((mv err l) (eval-place (terminator-call->dest term) depth st))
       ((when err) (mv (err-outcome err) st))
       ((mv err st) (write-loc l v st))
       ((when err) (mv (err-outcome err) st))
       (target (terminator-call->target term))
       ((unless (natp target))
        (mv (outcome-error "return from a diverging call") st))
       (caller (top-frame st))
       ((unless caller) (mv (outcome-error "no caller") st)))
    (mv (ok-outcome) (set-top-frame (frame-goto caller target) st))))

(define exec-call ((term terminator-p) (prog program-p) (st mstate-p))
  :guard (terminator-case term :call)
  :returns (mv (oc outcome-p) (st2 mstate-p))
  (b* (((terminator-call term) term)
       (depth (mstate-top-depth st))
       ((unless (natp depth)) (mv (outcome-error "no frame") (mstate-fix st)))
       ((mv oc args) (eval-operands term.args depth st))
       ((unless (outcome-ok-p oc)) (mv oc (mstate-fix st))))
    (callee-case term.callee
      :crate (b* ((fd (program-lookup-fun term.callee.id prog))
                  ((unless fd)
                   (mv (outcome-error (str::cat "unknown function " term.callee.name))
                       (mstate-fix st)))
                  (b (fundecl->body fd))
                  ((unless (equal (len args) (body->arg-count b)))
                   (mv (outcome-error "arity mismatch") (mstate-fix st)))
                  (new (new-frame term.callee.id b args)))
               ;; Push the callee; the caller stays at this Call until it returns.
               (mv (ok-outcome)
                   (change-mstate st :frames (cons new (mstate->frames st)))))
      :std (b* (((mv oc v st) (std-call term.callee.model term.callee.tys args st))
                ((unless (outcome-ok-p oc)) (mv oc st))
                ((unless (natp term.target))
                 (mv (outcome-error "diverging standard-library call returned") st))
                ((mv err l) (eval-place term.dest depth st))
                ((when err) (mv (err-outcome err) st))
                ((mv err st) (write-loc l v st))
                ((when err) (mv (err-outcome err) st))
                (f (top-frame st))
                ((unless f) (mv (outcome-error "no frame") st)))
             (mv (ok-outcome) (set-top-frame (frame-goto f term.target) st))))))

(define exec-terminator ((term terminator-p) (prog program-p) (st mstate-p))
  :returns (mv (oc outcome-p) (st2 mstate-p))
  (b* ((depth (mstate-top-depth st))
       ((unless (natp depth)) (mv (outcome-error "no frame") (mstate-fix st)))
       (f (top-frame st))
       ((unless f) (mv (outcome-error "no frame") (mstate-fix st))))
    (terminator-case term
      :goto (mv (ok-outcome) (set-top-frame (frame-goto f term.target) st))
      :switch (b* (((mv oc v) (eval-operand term.discr depth st))
                   ((unless (outcome-ok-p oc)) (mv oc (mstate-fix st))))
                (mv (ok-outcome)
                    (set-top-frame (frame-goto f (switch-target v term.branches
                                                                term.otherwise))
                                   st)))
      :assert (b* (((mv oc v) (eval-operand term.cond depth st))
                   ((unless (outcome-ok-p oc)) (mv oc (mstate-fix st)))
                   ((unless (value-case v :bool))
                    (mv (outcome-error "assert on a non-boolean") (mstate-fix st))))
                (if (equal (value-bool->b v) term.expected)
                    (mv (ok-outcome) (set-top-frame (frame-goto f term.target) st))
                  (mv (outcome-panic term.msg) (mstate-fix st))))
      :call (exec-call term prog st)
      :return (exec-return st)
      :unreachable (mv (outcome-ub term.msg) (mstate-fix st))
      :abort (mv (outcome-panic term.msg) (mstate-fix st)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Steps and runs

(define mstep ((prog program-p) (st mstate-p))
  :returns (mv (oc outcome-p) (st2 mstate-p))
  (b* ((f (top-frame st))
       ((unless f) (mv (outcome-error "no frame") (mstate-fix st)))
       (blk (body-block (frame->block f) (frame->body f)))
       ((unless blk) (mv (outcome-error "jump to a nonexistent block") (mstate-fix st)))
       (stmts (bblock->stmts blk))
       (i (frame->stmt f))
       (st (change-mstate st :steps (+ 1 (mstate->steps st))))
       ((when (< i (len stmts)))
        (b* (((mv oc st) (exec-statement (nth i stmts) st))
             ((unless (outcome-ok-p oc)) (mv oc st))
             ;; advance past the statement (the frame may have been updated)
             (f (top-frame st))
             ((unless f) (mv (outcome-error "no frame") st)))
          (mv (ok-outcome) (set-top-frame (change-frame f :stmt (+ 1 i)) st)))))
    (exec-terminator (bblock->term blk) prog st)))

(define run ((fuel natp) (prog program-p) (st mstate-p))
  :returns (mv (oc outcome-p) (st2 mstate-p))
  :measure (nfix fuel)
  (b* (((when (zp fuel)) (mv (outcome-out-of-fuel) (mstate-fix st)))
       ((mv oc st) (mstep prog st))
       ((unless (outcome-ok-p oc)) (mv oc st)))
    (run (1- fuel) prog st)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Calling a function of the program

(define start-call ((id natp) (args value-list-p) (prog program-p)
                    (globals value-alist-p) (statics value-alist-p))
  :returns (mv (oc outcome-p) (st mstate-p))
  (b* ((st0 (mstate nil globals statics 0))
       (fd (program-lookup-fun id prog))
       ((unless fd) (mv (outcome-error "unknown function") st0))
       (b (fundecl->body fd))
       ((unless (equal (len args) (body->arg-count b)))
        (mv (outcome-error "arity mismatch") st0)))
    (mv (ok-outcome) (change-mstate st0 :frames (list (new-frame id b args))))))

(define run-call ((fuel natp) (id natp) (args value-list-p) (prog program-p)
                  (globals value-alist-p) (statics value-alist-p))
  :returns (mv (oc outcome-p) (st mstate-p))
  (b* (((mv oc st) (start-call id args prog globals statics))
       ((unless (outcome-ok-p oc)) (mv oc st)))
    (run fuel prog st)))

;; Evaluate the program's globals, in order; an initializer may read the
;; globals before it.
(define init-globals ((defs globaldef-alist-p) (fuel natp) (prog program-p)
                      (globals value-alist-p) (statics value-alist-p))
  :returns (mv (oc outcome-p) (globals2 value-alist-p) (statics2 value-alist-p))
  (b* (((when (atom defs)) (mv (ok-outcome) (value-alist-fix globals)
                               (value-alist-fix statics)))
       ((unless (consp (car defs)))
        (init-globals (cdr defs) fuel prog globals statics))
       (id (nfix (caar defs)))
       (def (globaldef-fix (cdar defs))))
    (globaldef-case def
      :const (init-globals (cdr defs) fuel prog
                           (value-alist-store id (constant->value def.c) globals)
                           statics)
      :init (b* (((mv oc st) (run-call fuel def.fn nil prog globals statics))
                 ((unless (outcome-case oc :returned))
                  (mv (if (outcome-ok-p oc) (outcome-error "global initializer") oc)
                      (value-alist-fix globals) (value-alist-fix statics))))
              (init-globals (cdr defs) fuel prog
                            (value-alist-store id (outcome-returned->v oc) globals)
                            (mstate->statics st))))))

;; Run the named function of the program on the given arguments, with the
;; given static allocations (which pointer arguments may point into).
;; Returns the outcome and the final state.
(define call-function ((name stringp) (args value-list-p) (statics value-alist-p)
                       (fuel natp) (prog program-p))
  :returns (mv (oc outcome-p) (st mstate-p))
  (b* ((id (program-find-fun name prog))
       ((unless (natp id))
        (mv (outcome-error (str::cat "no function named " name))
            (mstate nil nil statics 0)))
       ((mv oc globals statics)
        (init-globals (program->globals prog) fuel prog nil statics))
       ((unless (outcome-ok-p oc)) (mv oc (mstate nil globals statics 0))))
    (run-call fuel id args prog globals statics)))
