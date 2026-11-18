; MIR semantics: runtime values, locations, memory, and machine states.
;
; Memory is structured (not byte-level): every local of every frame, every
; global, and every static allocation holds a value; a pointer is a location,
; i.e. a base (a frame's local, a global, or a static allocation) plus a path
; of field, index, and slice-window steps into the base's value.  A slice
; reference is a pointer whose last step is a window (or a pointer to a whole
; array); its length is the length of the array it designates.

(in-package "MIR")

(include-book "syntax")

(set-induction-depth-limit 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Locations

(fty::deftagsum locbase
  (:local ((frame natp) (index natp)))   ; frame = depth from the bottom of the stack
  (:global ((id natp)))
  (:static ((id natp))))

(fty::deftagsum pathelem
  (:field ((variant maybe-natp) (index natp)))
  (:index ((i natp)))
  (:window ((start natp) (len natp))))

(fty::deflist path :elt-type pathelem :true-listp t)

(fty::defprod loc
  ((base locbase)
   (path path)))

(define loc-extend ((l loc-p) (e pathelem-p))
  :returns (l2 loc-p)
  (change-loc l :path (append (loc->path l) (list (pathelem-fix e)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Values

(fty::deftypes value
  (fty::deftagsum value
    (:uninit ())
    (:int ((it inttype-p) (v integerp)))
    (:bool ((b booleanp)))
    ;; structs, tuples (unit is (:adt nil nil)), and enum variants
    (:adt ((variant maybe-natp) (fields value-list)))
    (:array ((elems value-list)))
    (:ptr ((loc loc)))
    (:str ((s stringp)))
    ;; Models of opaque standard-library iterator types:
    ;; core::slice::Iter and IterMut: a cursor over the slice at base
    (:slice-iter ((base loc) (pos natp) (end natp)))
    ;; core::iter::StepBy
    (:step-by ((iter value) (step natp) (first booleanp)))
    ;; core::iter::Rev
    (:rev ((iter value)))
    ;; core::iter::Zip
    (:zip ((a value) (b value))))
  (fty::deflist value-list :elt-type value :true-listp t))

(fty::defalist value-alist :key-type natp :val-type value :true-listp t)

(define value-unit ()
  :returns (v value-p)
  (value-adt nil nil))

(define value-usize ((n integerp))
  :returns (v value-p)
  (value-int :usize n))

(define value-option-none ()
  :returns (v value-p)
  (value-adt 0 nil))

(define value-option-some ((x value-p))
  :returns (v value-p)
  (value-adt 1 (list x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; List utilities (total; out-of-range accesses are reported by callers)

(define value-list-nth ((n natp) (l value-list-p))
  :returns (v value-p)
  (cond ((atom l) (value-uninit))
        ((zp n) (value-fix (car l)))
        (t (value-list-nth (1- n) (cdr l)))))

(define value-list-update ((n natp) (v value-p) (l value-list-p))
  :returns (l2 value-list-p)
  (cond ((atom l) nil)
        ((zp n) (cons (value-fix v) (value-list-fix (cdr l))))
        (t (cons (value-fix (car l)) (value-list-update (1- n) v (cdr l))))))

(defret len-of-value-list-update
  (equal (len l2) (len l))
  :fn value-list-update
  :hints (("Goal" :in-theory (enable value-list-update))))

(define value-list-take ((n natp) (l value-list-p))
  :returns (l2 value-list-p)
  (cond ((zp n) nil)
        ((atom l) nil)
        (t (cons (value-fix (car l)) (value-list-take (1- n) (cdr l))))))

(define value-list-drop ((n natp) (l value-list-p))
  :returns (l2 value-list-p)
  (cond ((zp n) (value-list-fix l))
        ((atom l) nil)
        (t (value-list-drop (1- n) (cdr l)))))

(define value-list-subseq ((start natp) (n natp) (l value-list-p))
  :returns (l2 value-list-p)
  (value-list-take n (value-list-drop start l)))

;; Replace the elements of l starting at position start by those of new.
(define value-list-splice ((start natp) (new value-list-p) (l value-list-p))
  :returns (l2 value-list-p)
  (cond ((atom l) nil)
        ((zp start)
         (if (atom new)
             (value-list-fix l)
           (cons (value-fix (car new))
                 (value-list-splice 0 (cdr new) (cdr l)))))
        (t (cons (value-fix (car l))
                 (value-list-splice (1- start) new (cdr l))))))

(define value-list-repeat ((n natp) (v value-p))
  :returns (l value-list-p)
  (if (zp n) nil (cons (value-fix v) (value-list-repeat (1- n) v))))

(define value-alist-lookup ((k natp) (al value-alist-p))
  :returns (v (iff (value-p v) v))
  (cond ((atom al) nil)
        ((and (consp (car al)) (equal (nfix (caar al)) (lnfix k)))
         (value-fix (cdar al)))
        (t (value-alist-lookup k (cdr al)))))

(define value-alist-store ((k natp) (v value-p) (al value-alist-p))
  :returns (al2 value-alist-p)
  (cond ((atom al) (list (cons (lnfix k) (value-fix v))))
        ((and (consp (car al)) (equal (nfix (caar al)) (lnfix k)))
         (cons (cons (lnfix k) (value-fix v)) (value-alist-fix (cdr al))))
        (t (if (consp (car al))
               (cons (cons (nfix (caar al)) (value-fix (cdar al)))
                     (value-alist-store k v (cdr al)))
             (value-alist-store k v (cdr al))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reading and writing along a path inside a value.  Errors are strings.

(define read-path ((v value-p) (p path-p))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (r value-p))
  :measure (len p)
  (b* (((when (atom p)) (mv nil (value-fix v)))
       (e (pathelem-fix (car p))))
    (pathelem-case e
      :field (value-case v
               :adt (if (and e.variant (not (equal e.variant v.variant)))
                        (mv "field of an inactive enum variant" (value-uninit))
                      (if (< e.index (len v.fields))
                          (read-path (value-list-nth e.index v.fields) (cdr p))
                        (mv "field index out of range" (value-uninit))))
               :otherwise (mv "field projection of a non-aggregate" (value-uninit)))
      :index (value-case v
               :array (if (< e.i (len v.elems))
                          (read-path (value-list-nth e.i v.elems) (cdr p))
                        (mv "index out of bounds" (value-uninit)))
               :otherwise (mv "index projection of a non-array" (value-uninit)))
      :window (value-case v
                :array (if (<= (+ e.start e.len) (len v.elems))
                           (read-path (value-array
                                       (value-list-subseq e.start e.len v.elems))
                                      (cdr p))
                         (mv "slice window out of bounds" (value-uninit)))
                :otherwise (mv "slice window of a non-array" (value-uninit))))))

(define write-path ((v value-p) (p path-p) (new value-p))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (r value-p))
  :measure (len p)
  :verify-guards nil
  (b* (((when (atom p)) (mv nil (value-fix new)))
       (e (pathelem-fix (car p))))
    (pathelem-case e
      :field (value-case v
               :adt (b* (((when (and e.variant (not (equal e.variant v.variant))))
                          (mv "write to a field of an inactive enum variant"
                              (value-fix v)))
                         ((unless (< e.index (len v.fields)))
                          (mv "field index out of range" (value-fix v)))
                         ((mv err sub)
                          (write-path (value-list-nth e.index v.fields) (cdr p) new))
                         ((when err) (mv err (value-fix v))))
                      (mv nil (change-value-adt
                               v :fields (value-list-update e.index sub v.fields))))
               :otherwise (mv "field write into a non-aggregate" (value-fix v)))
      :index (value-case v
               :array (b* (((unless (< e.i (len v.elems)))
                            (mv "index out of bounds" (value-fix v)))
                           ((mv err sub)
                            (write-path (value-list-nth e.i v.elems) (cdr p) new))
                           ((when err) (mv err (value-fix v))))
                        (mv nil (value-array (value-list-update e.i sub v.elems))))
               :otherwise (mv "index write into a non-array" (value-fix v)))
      :window (value-case v
                :array (b* (((unless (<= (+ e.start e.len) (len v.elems)))
                             (mv "slice window out of bounds" (value-fix v)))
                            ((mv err sub)
                             (write-path (value-array
                                          (value-list-subseq e.start e.len v.elems))
                                         (cdr p) new))
                            ((when err) (mv err (value-fix v))))
                         (value-case sub
                           :array (if (equal (len sub.elems) e.len)
                                      (mv nil (value-array
                                               (value-list-splice e.start sub.elems
                                                                  v.elems)))
                                    (mv "slice window write changes the length"
                                        (value-fix v)))
                           :otherwise (mv "slice window write of a non-array"
                                          (value-fix v))))
                :otherwise (mv "slice window into a non-array" (value-fix v))))))

(verify-guards write-path)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Frames and machine states

(fty::defprod frame
  ((fn natp)                 ; the crate function this frame runs
   (body body)
   (locals value-list)
   (block natp)              ; current basic block
   (stmt natp)))             ; index of the next statement in it

(fty::deflist frame-list :elt-type frame :true-listp t)

(fty::defprod mstate
  ((frames frame-list)       ; the call stack, innermost frame first
   (globals value-alist)     ; values of the program's globals
   (statics value-alist)     ; static allocations (promoted constants, inputs)
   (steps natp)))            ; number of machine steps taken

(fty::deftagsum outcome
  (:running ())
  (:returned ((v value)))
  (:panic ((msg stringp)))
  (:ub ((msg stringp)))
  (:error ((msg stringp)))
  (:out-of-fuel ()))

(define frame-list-nth ((n natp) (l frame-list-p))
  :returns (f (iff (frame-p f) f))
  (cond ((atom l) nil)
        ((zp n) (frame-fix (car l)))
        (t (frame-list-nth (1- n) (cdr l)))))

(define frame-list-update ((n natp) (f frame-p) (l frame-list-p))
  :returns (l2 frame-list-p)
  (cond ((atom l) nil)
        ((zp n) (cons (frame-fix f) (frame-list-fix (cdr l))))
        (t (cons (frame-fix (car l)) (frame-list-update (1- n) f (cdr l))))))

;; Frames are numbered from the bottom of the stack, so that pointers into a
;; frame stay valid while frames are pushed above it.
(define frame-position ((depth natp) (frames frame-list-p))
  :returns (pos integerp :rule-classes :type-prescription)
  (- (len frames) (+ 1 (lnfix depth))))

(define mstate-top-depth ((st mstate-p))
  :returns (d integerp :rule-classes :type-prescription)
  (1- (len (mstate->frames st))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reading and writing memory at a location

(define read-base ((b locbase-p) (st mstate-p))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (v value-p))
  (locbase-case b
    :local (b* ((pos (frame-position b.frame (mstate->frames st)))
                ((unless (natp pos)) (mv "dangling pointer to a popped frame"
                                         (value-uninit)))
                (f (frame-list-nth pos (mstate->frames st)))
                ((unless f) (mv "no such frame" (value-uninit)))
                ((unless (< b.index (len (frame->locals f))))
                 (mv "no such local" (value-uninit))))
             (mv nil (value-list-nth b.index (frame->locals f))))
    :global (b* ((v (value-alist-lookup b.id (mstate->globals st))))
              (if v (mv nil v) (mv "unknown global" (value-uninit))))
    :static (b* ((v (value-alist-lookup b.id (mstate->statics st))))
              (if v (mv nil v) (mv "unknown static allocation" (value-uninit))))))

(define write-base ((b locbase-p) (v value-p) (st mstate-p))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (st2 mstate-p))
  (locbase-case b
    :local (b* ((frames (mstate->frames st))
                (pos (frame-position b.frame frames))
                ((unless (natp pos)) (mv "dangling pointer to a popped frame"
                                         (mstate-fix st)))
                (f (frame-list-nth pos frames))
                ((unless f) (mv "no such frame" (mstate-fix st)))
                ((unless (< b.index (len (frame->locals f))))
                 (mv "no such local" (mstate-fix st)))
                (f (change-frame f :locals (value-list-update b.index v
                                                              (frame->locals f)))))
             (mv nil (change-mstate st :frames (frame-list-update pos f frames))))
    :global (mv "write to a global" (mstate-fix st))
    :static (mv nil (change-mstate st :statics (value-alist-store
                                                b.id v (mstate->statics st))))))

(define read-loc ((l loc-p) (st mstate-p))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (v value-p))
  (b* (((mv err bv) (read-base (loc->base l) st))
       ((when err) (mv err (value-uninit))))
    (read-path bv (loc->path l))))

(define write-loc ((l loc-p) (v value-p) (st mstate-p))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (st2 mstate-p))
  (b* (((mv err bv) (read-base (loc->base l) st))
       ((when err) (mv err (mstate-fix st)))
       ((mv err bv) (write-path bv (loc->path l) v))
       ((when err) (mv err (mstate-fix st))))
    (write-base (loc->base l) bv st)))
