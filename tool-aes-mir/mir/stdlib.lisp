; MIR semantics: integer operations and models of standard-library functions.
;
; The crate's MIR calls into core; Charon leaves those functions opaque (no
; bodies), so the interpreter gives each a model here, executed as a single
; machine step.  The importer's classifier maps each call site to a model
; keyword (see std-model-p below), choosing it from the declaration's path,
; its implementation's self type and trait, and the call's generic arguments.

(in-package "MIR")

(include-book "values")
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

(set-induction-depth-limit 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Results of operations: a success value, or a panic / UB / error outcome.

(define ok-outcome ()
  :returns (oc outcome-p)
  (outcome-running))

(define outcome-ok-p ((oc outcome-p))
  :returns (b booleanp)
  (outcome-case oc :running))

(define err-outcome ((msg acl2::maybe-stringp))
  :returns (oc outcome-p)
  (outcome-error (if (stringp msg) msg "error")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Integer arithmetic

(define arith-result ((it inttype-p) (exact integerp) (mode overflow-mode-p)
                      (what stringp))
  :returns (mv (oc outcome-p) (v value-p))
  (cond ((int-in-range-p it exact) (mv (ok-outcome) (value-int it exact)))
        ((eq (overflow-mode-fix mode) :wrap)
         (mv (ok-outcome) (value-int it (int-wrap it exact))))
        ((eq (overflow-mode-fix mode) :panic)
         (mv (outcome-panic (str::cat "attempt to " what " with overflow"))
             (value-uninit)))
        (t (mv (outcome-ub (str::cat "overflow in " what)) (value-uninit)))))

(define shift-amount ((it inttype-p) (n integerp) (mode overflow-mode-p))
  ;; The effective shift amount, or nil if out of range under a checked mode.
  :returns (k maybe-natp :rule-classes :type-prescription)
  (let ((w (inttype-width it)))
    (if (and (<= 0 (lifix n)) (< (lifix n) w))
        (lifix n)
      (if (eq (overflow-mode-fix mode) :wrap)
          (mod (lifix n) w)
        nil))))

(define compare-ints ((name binop-name-p) (x integerp) (y integerp))
  :returns (b booleanp)
  (let ((x (lifix x)) (y (lifix y)))
    (case (binop-name-fix name)
      (:eq (equal x y))
      (:ne (not (equal x y)))
      (:lt (< x y))
      (:le (<= x y))
      (:gt (> x y))
      (otherwise (>= x y)))))

(define compare-bools ((name binop-name-p) (x booleanp) (y booleanp))
  :returns (b booleanp)
  (let ((x (if x 1 0)) (y (if y 1 0)))
    (compare-ints name x y)))

(define eval-int-binop ((op binop-p) (it inttype-p) (x integerp) (it2 inttype-p) (y integerp))
  :returns (mv (oc outcome-p) (v value-p))
  (b* (((binop op) op)
       (x (lifix x)) (y (lifix y)))
    (case op.name
      ((:eq :ne :lt :le :gt :ge) (mv (ok-outcome) (value-bool (compare-ints op.name x y))))
      ((:shl :shr)
       ;; The shift amount may have a different integer type than the value.
       (b* ((k (shift-amount it y op.mode))
            ((unless k)
             (if (eq op.mode :panic)
                 (mv (outcome-panic "attempt to shift with overflow") (value-uninit))
               (mv (outcome-ub "shift amount out of range") (value-uninit))))
            (r (if (eq op.name :shl) (ash x k) (ash x (- k)))))
         (mv (ok-outcome) (value-int it (int-wrap it r)))))
      (otherwise
       (b* (((unless (equal (inttype-fix it) (inttype-fix it2)))
             (mv (outcome-error "binary operation on mismatched integer types")
                 (value-uninit))))
         (case op.name
           (:add (arith-result it (+ x y) op.mode "add"))
           (:sub (arith-result it (- x y) op.mode "subtract"))
           (:mul (arith-result it (* x y) op.mode "multiply"))
           ((:div :rem)
            (cond ((equal y 0)
                   (if (eq op.mode :ub)
                       (mv (outcome-ub "division by zero") (value-uninit))
                     (mv (outcome-panic (if (eq op.name :div)
                                            "attempt to divide by zero"
                                          "attempt to calculate the remainder with a divisor of zero"))
                         (value-uninit))))
                  (t (arith-result it (if (eq op.name :div) (truncate x y) (rem x y))
                                   op.mode (if (eq op.name :div) "divide"
                                             "calculate the remainder")))))
           (:bitxor (mv (ok-outcome) (value-int it (int-wrap it (logxor x y)))))
           (:bitand (mv (ok-outcome) (value-int it (int-wrap it (logand x y)))))
           (:bitor (mv (ok-outcome) (value-int it (int-wrap it (logior x y)))))
           (otherwise (mv (outcome-error "unsupported integer operation")
                          (value-uninit)))))))))

(define eval-binop ((op binop-p) (a value-p) (b value-p))
  :returns (mv (oc outcome-p) (v value-p))
  (b* ((name (binop->name op)))
    (cond ((and (value-case a :int) (value-case b :int))
           (eval-int-binop op (value-int->it a) (value-int->v a)
                           (value-int->it b) (value-int->v b)))
          ((and (value-case a :bool) (value-case b :bool))
           (b* ((x (value-bool->b a)) (y (value-bool->b b)))
             (case name
               ((:eq :ne :lt :le :gt :ge) (mv (ok-outcome) (value-bool (compare-bools name x y))))
               (:bitxor (mv (ok-outcome) (value-bool (not (equal x y)))))
               (:bitand (mv (ok-outcome) (value-bool (and x y))))
               (:bitor (mv (ok-outcome) (value-bool (or x y))))
               (otherwise (mv (outcome-error "unsupported boolean operation")
                              (value-uninit))))))
          ((or (value-case a :uninit) (value-case b :uninit))
           (mv (outcome-error "read of an uninitialized value") (value-uninit)))
          (t (mv (outcome-error "binary operation on unsupported operands")
                 (value-uninit))))))

(define eval-unop ((op unop-p) (a value-p))
  :returns (mv (oc outcome-p) (v value-p))
  (unop-case op
    :not (value-case a
           :bool (mv (ok-outcome) (value-bool (not a.b)))
           :int (mv (ok-outcome) (value-int a.it (int-wrap a.it (lognot a.v))))
           :otherwise (mv (outcome-error "! of a non-scalar") (value-uninit)))
    :neg (value-case a
           :int (arith-result a.it (- a.v) op.mode "negate")
           :otherwise (mv (outcome-error "- of a non-integer") (value-uninit)))
    :cast-int (value-case a
                :int (mv (ok-outcome) (value-int op.target (int-wrap op.target a.v)))
                :bool (mv (ok-outcome) (value-int op.target (if a.b 1 0)))
                :otherwise (mv (outcome-error "integer cast of a non-scalar")
                               (value-uninit)))
    :cast-bool-int (value-case a
                     :bool (mv (ok-outcome) (value-int op.target (if a.b 1 0)))
                     :otherwise (mv (outcome-error "bool cast of a non-bool")
                                    (value-uninit)))
    :unsize (value-case a
              :ptr (mv (ok-outcome) (value-fix a))   ; &[T; N] and &[T] share a representation
              :otherwise (mv (outcome-error "unsize cast of a non-pointer")
                             (value-uninit)))
    :other-cast (mv (outcome-error "unsupported cast") (value-uninit))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Byte conversions and rotations

(define le-bytes->int ((bytes value-list-p))
  :returns (mv (ok booleanp) (n natp :rule-classes :type-prescription))
  (b* (((when (atom bytes)) (mv t 0))
       (b (value-fix (car bytes)))
       ((unless (and (value-case b :int) (eq (value-int->it b) :u8)))
        (mv nil 0))
       ((mv ok rest) (le-bytes->int (cdr bytes))))
    (mv ok (+ (loghead 8 (value-int->v b)) (* 256 rest)))))

(define int->le-bytes ((n natp) (x integerp))
  :returns (bytes value-list-p)
  (if (zp n)
      nil
    (cons (value-int :u8 (loghead 8 (lifix x)))
          (int->le-bytes (1- n) (ash (lifix x) -8)))))

(define rotate-right-int ((it inttype-p) (x integerp) (k integerp))
  :returns (r integerp :rule-classes :type-prescription)
  (b* ((w (inttype-width it))
       (k (mod (lifix k) w))
       (u (loghead w (lifix x))))
    (int-wrap it (logior (ash u (- k)) (loghead w (ash u (- w k)))))))

(define rotate-left-int ((it inttype-p) (x integerp) (k integerp))
  :returns (r integerp :rule-classes :type-prescription)
  (b* ((w (inttype-width it))
       (k (mod (lifix k) w)))
    (rotate-right-int it x (mod (- w k) w))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Iterators

(define range-fields ((r value-p))
  ;; Recognize a core::ops::Range value {start, end}.
  :returns (mv (ok booleanp) (it inttype-p)
               (start integerp :rule-classes :type-prescription)
               (end integerp :rule-classes :type-prescription))
  (b* (((unless (value-case r :adt)) (mv nil :usize 0 0))
       (fields (value-adt->fields r))
       ((unless (and (equal (len fields) 2)
                     (not (value-adt->variant r))))
        (mv nil :usize 0 0))
       (s (value-list-nth 0 fields))
       (e (value-list-nth 1 fields))
       ((unless (and (value-case s :int) (value-case e :int)
                     (equal (value-int->it s) (value-int->it e))))
        (mv nil :usize 0 0)))
    (mv t (value-int->it s) (value-int->v s) (value-int->v e))))

(define make-range ((it inttype-p) (start integerp) (end integerp))
  :returns (v value-p)
  (value-adt nil (list (value-int it start) (value-int it end))))

;; One call of Iterator::next on the iterator value it.  Returns the item
;; (an Option) and the advanced iterator.
(define iter-next ((it value-p))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (opt value-p)
               (it2 value-p))
  :measure (value-count it)
  :verify-guards nil
  (value-case it
    :adt (b* (((mv ok ity s e) (range-fields it))
              ((unless ok) (mv "next on an unsupported iterator" (value-uninit) (value-fix it))))
           ;; <Range<A> as Iterator>::next
           (if (< s e)
               (mv nil (value-option-some (value-int ity s)) (make-range ity (+ 1 s) e))
             (mv nil (value-option-none) (value-fix it))))
    :slice-iter (if (< it.pos it.end)
                    (mv nil
                        (value-option-some
                         (value-ptr (loc-extend it.base (pathelem-index it.pos))))
                        (change-value-slice-iter it :pos (+ 1 it.pos)))
                  (mv nil (value-option-none) (value-fix it)))
    :step-by (b* (((mv ok ity s e) (range-fields it.iter))
                  ((unless ok)
                   (mv "StepBy over an unsupported iterator" (value-uninit) (value-fix it)))
                  ((when (zp it.step))
                   (mv "StepBy with step 0" (value-uninit) (value-fix it)))
                  ;; The first call yields the first element; later calls skip
                  ;; step - 1 elements first.
                  (s (if it.first s (+ s (- it.step 1)))))
               (if (< s e)
                   (mv nil (value-option-some (value-int ity s))
                       (change-value-step-by it :iter (make-range ity (+ 1 s) e)
                                             :first nil))
                 (mv nil (value-option-none)
                     (change-value-step-by it :iter (make-range ity e e)
                                           :first nil))))
    :rev (b* (((mv ok ity s e) (range-fields it.iter))
              ((unless ok) (mv "Rev over an unsupported iterator" (value-uninit) (value-fix it))))
           ;; <Range<A> as DoubleEndedIterator>::next_back
           (if (< s e)
               (mv nil (value-option-some (value-int ity (- e 1)))
                   (change-value-rev it :iter (make-range ity s (- e 1))))
             (mv nil (value-option-none) (value-fix it))))
    :zip (b* (((mv err x a2) (iter-next it.a))
              ((when err) (mv err (value-uninit) (value-fix it)))
              ((unless (and (value-case x :adt) (equal (value-adt->variant x) 1)))
               (mv nil (value-option-none) (change-value-zip it :a a2)))
              ((mv err y b2) (iter-next it.b))
              ((when err) (mv err (value-uninit) (value-fix it)))
              ((unless (and (value-case y :adt) (equal (value-adt->variant y) 1)))
               (mv nil (value-option-none) (change-value-zip it :a a2 :b b2))))
           (mv nil
               (value-option-some
                (value-adt nil (list (value-list-nth 0 (value-adt->fields x))
                                     (value-list-nth 0 (value-adt->fields y)))))
               (change-value-zip it :a a2 :b b2)))
    :otherwise (mv "next on a non-iterator" (value-uninit) (value-fix it))))

(verify-guards iter-next
  :hints (("Goal" :in-theory (enable value-option-some value-option-none))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The models

(defconst *std-models*
  '(;; slices and arrays
    :slice-len :slice-iter :slice-iter-mut :slice-into-iter :copy-from-slice
    :index-usize :index-range :index-range-to :index-range-from :index-range-full
    :array-default :try-into-array :result-unwrap
    ;; iterators
    :into-iter :slice-iter-next :range-next :range-next-back :step-by
    :step-by-next :rev :rev-next :zip :zip-next
    ;; integers
    :from-le-bytes :to-le-bytes :rotate-right :rotate-left :bitxor-assign-ref
    :add-with-overflow :sub-with-overflow :mul-with-overflow
    ;; panics
    :panic :assert-failed))

(define std-model-p (x)
  :returns (b booleanp)
  (if (member-eq x *std-models*) t nil))

(define ptr-arg ((v value-p))
  :returns (mv (ok booleanp) (l loc-p))
  (value-case v
    :ptr (mv t v.loc)
    :otherwise (mv nil (loc (locbase-static 0) nil))))

(define array-arg ((v value-p))
  :returns (mv (ok booleanp) (elems value-list-p))
  (value-case v
    :array (mv t v.elems)
    :otherwise (mv nil nil)))

(define default-value ((ty ty-p))
  :returns (v value-p)
  :measure (ty-count ty)
  :verify-guards :after-returns
  (ty-case ty
    :int (value-int ty.it 0)
    :bool (value-bool nil)
    :array (if (natp ty.len)
               (value-array (value-list-repeat ty.len (default-value ty.elem)))
             (value-uninit))
    :otherwise (value-uninit)))

(define ty-list-nth ((n natp) (l ty-list-p))
  :returns (ty ty-p)
  (cond ((atom l) (ty-other))
        ((zp n) (ty-fix (car l)))
        (t (ty-list-nth (1- n) (cdr l)))))

(define std-error ((msg stringp) (st mstate-p))
  :returns (mv (oc outcome-p) (v value-p) (st2 mstate-p))
  (mv (outcome-error msg) (value-uninit) (mstate-fix st)))

(define std-ok ((v value-p) (st mstate-p))
  :returns (mv (oc outcome-p) (v2 value-p) (st2 mstate-p))
  (mv (ok-outcome) (value-fix v) (mstate-fix st)))

(define std-index ((model symbolp) (args value-list-p) (st mstate-p))
  ;; <[T] as Index<I>>::index and friends (also for arrays); the model was
  ;; chosen from the index type I.  Produces a pointer to the element or to
  ;; the slice window, after the same bounds checks as core (which panic).
  :returns (mv (oc outcome-p) (v value-p) (st2 mstate-p))
  (b* (((unless (equal (len args) 2)) (std-error "index: arity" st))
       ((mv ok l) (ptr-arg (value-list-nth 0 args)))
       ((unless ok) (std-error "index: not a pointer" st))
       ((mv err arr) (read-loc l st))
       ((when err) (std-error err st))
       ((mv ok elems) (array-arg arr))
       ((unless ok) (std-error "index: not a slice" st))
       (n (len elems))
       (idx (value-list-nth 1 args)))
    (case model
      (:index-usize
       (b* (((unless (value-case idx :int)) (std-error "index: bad index" st))
            (i (value-int->v idx))
            ((unless (and (<= 0 i) (< i n)))
             (mv (outcome-panic "index out of bounds") (value-uninit) (mstate-fix st))))
         (std-ok (value-ptr (loc-extend l (pathelem-index i))) st)))
      (otherwise
       (b* (((mv ok s e)
             (case model
               (:index-range-full (mv t 0 n))
               (:index-range-to
                (if (and (value-case idx :adt)
                         (equal (len (value-adt->fields idx)) 1)
                         (value-case (value-list-nth 0 (value-adt->fields idx)) :int))
                    (mv t 0 (value-int->v (value-list-nth 0 (value-adt->fields idx))))
                  (mv nil 0 0)))
               (:index-range-from
                (if (and (value-case idx :adt)
                         (equal (len (value-adt->fields idx)) 1)
                         (value-case (value-list-nth 0 (value-adt->fields idx)) :int))
                    (mv t (value-int->v (value-list-nth 0 (value-adt->fields idx))) n)
                  (mv nil 0 0)))
               (otherwise
                (b* (((mv ok & s e) (range-fields idx)))
                  (mv ok s e)))))
            ((unless ok) (std-error "index: bad range" st))
            ((unless (and (<= 0 s) (<= s e)))
             (mv (outcome-panic "slice index starts after it ends")
                 (value-uninit) (mstate-fix st)))
            ((unless (<= e n))
             (mv (outcome-panic "range end index out of range for slice")
                 (value-uninit) (mstate-fix st))))
         (std-ok (value-ptr (loc-extend l (pathelem-window s (- e s)))) st))))))

(define std-call ((model symbolp) (tys ty-list-p) (args value-list-p) (st mstate-p))
  :returns (mv (oc outcome-p) (v value-p) (st2 mstate-p))
  (b* ((a0 (value-list-nth 0 args))
       (a1 (value-list-nth 1 args)))
    (case model
      ;; ---- slices and arrays
      (:slice-len
       ;; <[T]>::len
       (b* (((mv ok l) (ptr-arg a0))
            ((unless ok) (std-error "len: not a pointer" st))
            ((mv err v) (read-loc l st))
            ((when err) (std-error err st))
            ((mv ok elems) (array-arg v))
            ((unless ok) (std-error "len: not a slice" st)))
         (std-ok (value-usize (len elems)) st)))
      ((:slice-iter :slice-iter-mut :slice-into-iter)
       ;; <[T]>::iter, <[T]>::iter_mut, <&[T] as IntoIterator>::into_iter
       (b* (((mv ok l) (ptr-arg a0))
            ((unless ok) (std-error "iter: not a pointer" st))
            ((mv err v) (read-loc l st))
            ((when err) (std-error err st))
            ((mv ok elems) (array-arg v))
            ((unless ok) (std-error "iter: not a slice" st)))
         (std-ok (value-slice-iter l 0 (len elems)) st)))
      (:copy-from-slice
       ;; <[T]>::copy_from_slice (panics if the lengths differ)
       (b* (((mv ok dst) (ptr-arg a0))
            ((unless ok) (std-error "copy_from_slice: not a pointer" st))
            ((mv ok src) (ptr-arg a1))
            ((unless ok) (std-error "copy_from_slice: not a pointer" st))
            ((mv err dv) (read-loc dst st))
            ((when err) (std-error err st))
            ((mv err sv) (read-loc src st))
            ((when err) (std-error err st))
            ((mv ok delems) (array-arg dv))
            ((unless ok) (std-error "copy_from_slice: not a slice" st))
            ((mv ok selems) (array-arg sv))
            ((unless ok) (std-error "copy_from_slice: not a slice" st))
            ((unless (equal (len delems) (len selems)))
             (mv (outcome-panic "copy_from_slice: source slice length does not match destination slice length")
                 (value-uninit) (mstate-fix st)))
            ((mv err st) (write-loc dst (value-array selems) st))
            ((when err) (std-error err st)))
         (std-ok (value-unit) st)))
      ((:index-usize :index-range :index-range-to :index-range-from :index-range-full)
       (std-index model args st))
      (:array-default
       ;; <[T; N] as Default>::default; tys = ([T; N])
       (b* ((v (default-value (ty-list-nth 0 tys)))
            ((when (value-case v :uninit)) (std-error "default: unsupported type" st)))
         (std-ok v st)))
      (:try-into-array
       ;; <&[T] as TryInto<[T; N]>>::try_into; tys = ([T; N])
       (b* ((target (ty-list-nth 0 tys))
            ((unless (and (ty-case target :array) (natp (ty-array->len target))))
             (std-error "try_into: unsupported target type" st))
            ((mv ok l) (ptr-arg a0))
            ((unless ok) (std-error "try_into: not a pointer" st))
            ((mv err v) (read-loc l st))
            ((when err) (std-error err st))
            ((mv ok elems) (array-arg v))
            ((unless ok) (std-error "try_into: not a slice" st)))
         (if (equal (len elems) (ty-array->len target))
             (std-ok (value-adt 0 (list (value-array elems))) st) ; Ok
           (std-ok (value-adt 1 (list (value-adt nil (list (value-unit))))) st)))) ; Err(TryFromSliceError)
      (:result-unwrap
       ;; Result::<T, E>::unwrap
       (value-case a0
         :adt (cond ((and (equal a0.variant 0) (consp a0.fields))
                     (std-ok (value-list-nth 0 a0.fields) st))
                    ((equal a0.variant 1)
                     (mv (outcome-panic "called `Result::unwrap()` on an `Err` value")
                         (value-uninit) (mstate-fix st)))
                    (t (std-error "unwrap: not a Result" st)))
         :otherwise (std-error "unwrap: not a Result" st)))
      ;; ---- iterators
      ((:into-iter :step-by :rev :zip)
       (case model
         ;; <I as IntoIterator>::into_iter for an iterator I is the identity
         (:into-iter (std-ok a0 st))
         ;; Iterator::step_by (panics on a zero step)
         (:step-by (value-case a1
                     :int (if (posp a1.v)
                              (std-ok (value-step-by a0 a1.v t) st)
                            (mv (outcome-panic "assertion failed: step != 0")
                                (value-uninit) (mstate-fix st)))
                     :otherwise (std-error "step_by: bad step" st)))
         (:rev (std-ok (value-rev a0) st))
         ;; Iterator::zip converts its argument with IntoIterator: a slice
         ;; reference becomes a slice iterator.
         (otherwise
          (value-case a1
            :ptr (b* (((mv err v) (read-loc a1.loc st))
                      ((when err) (std-error err st))
                      ((mv ok elems) (array-arg v))
                      ((unless ok) (std-error "zip: not a slice" st)))
                   (std-ok (value-zip a0 (value-slice-iter a1.loc 0 (len elems))) st))
            :otherwise (std-ok (value-zip a0 a1) st)))))
      ((:slice-iter-next :range-next :range-next-back :step-by-next :rev-next :zip-next)
       ;; Iterator::next (and DoubleEndedIterator::next_back) through &mut self
       (b* (((mv ok l) (ptr-arg a0))
            ((unless ok) (std-error "next: not a pointer" st))
            ((mv err it) (read-loc l st))
            ((when err) (std-error err st))
            ((mv err opt it2)
             (if (eq model :range-next-back)
                 (iter-next (value-rev it))
               (iter-next it)))
            ((when err) (std-error err st))
            (it2 (if (and (eq model :range-next-back) (value-case it2 :rev))
                     (value-rev->iter it2)
                   it2))
            ((mv err st) (write-loc l it2 st))
            ((when err) (std-error err st)))
         (std-ok opt st)))
      ;; ---- integers
      (:from-le-bytes
       ;; uN::from_le_bytes; tys = (uN)
       (b* ((ty (ty-list-nth 0 tys))
            ((unless (ty-case ty :int)) (std-error "from_le_bytes: bad type" st))
            ((mv ok elems) (array-arg a0))
            ((unless ok) (std-error "from_le_bytes: not an array" st))
            ((mv ok n) (le-bytes->int elems))
            ((unless ok) (std-error "from_le_bytes: not bytes" st))
            (it (ty-int->it ty)))
         (std-ok (value-int it (int-wrap it n)) st)))
      (:to-le-bytes
       ;; uN::to_le_bytes
       (value-case a0
         :int (std-ok (value-array (int->le-bytes (floor (inttype-width a0.it) 8) a0.v)) st)
         :otherwise (std-error "to_le_bytes: not an integer" st)))
      ((:rotate-right :rotate-left)
       ;; uN::rotate_right, uN::rotate_left
       (if (and (value-case a0 :int) (value-case a1 :int))
           (std-ok (value-int (value-int->it a0)
                              (if (eq model :rotate-right)
                                  (rotate-right-int (value-int->it a0) (value-int->v a0)
                                                    (value-int->v a1))
                                (rotate-left-int (value-int->it a0) (value-int->v a0)
                                                 (value-int->v a1))))
                   st)
         (std-error "rotate: not integers" st)))
      (:bitxor-assign-ref
       ;; <uN as BitXorAssign<&uN>>::bitxor_assign
       (b* (((mv ok l) (ptr-arg a0))
            ((unless ok) (std-error "bitxor_assign: not a pointer" st))
            ((mv ok r) (ptr-arg a1))
            ((unless ok) (std-error "bitxor_assign: not a pointer" st))
            ((mv err x) (read-loc l st))
            ((when err) (std-error err st))
            ((mv err y) (read-loc r st))
            ((when err) (std-error err st))
            ((mv oc z) (eval-binop (binop :bitxor :wrap) x y))
            ((unless (outcome-ok-p oc)) (mv oc (value-uninit) (mstate-fix st)))
            ((mv err st) (write-loc l z st))
            ((when err) (std-error err st)))
         (std-ok (value-unit) st)))
      ((:add-with-overflow :sub-with-overflow :mul-with-overflow)
       ;; core::intrinsics::{add,sub,mul}_with_overflow: (wrapped result, overflowed)
       (if (and (value-case a0 :int) (value-case a1 :int)
                (equal (value-int->it a0) (value-int->it a1)))
           (b* ((it (value-int->it a0))
                (x (value-int->v a0)) (y (value-int->v a1))
                (exact (case model
                         (:add-with-overflow (+ x y))
                         (:sub-with-overflow (- x y))
                         (otherwise (* x y)))))
             (std-ok (value-adt nil (list (value-int it (int-wrap it exact))
                                          (value-bool (not (int-in-range-p it exact)))))
                     st))
         (std-error "overflow intrinsic: bad operands" st)))
      ;; ---- panics
      (:panic (mv (outcome-panic "explicit panic") (value-uninit) (mstate-fix st)))
      (:assert-failed (mv (outcome-panic "assertion `left == right` failed")
                          (value-uninit) (mstate-fix st)))
      (otherwise (std-error "unmodeled standard-library function" st)))))
