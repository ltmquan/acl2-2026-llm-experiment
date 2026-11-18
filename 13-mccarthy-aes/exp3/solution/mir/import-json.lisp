; MIR semantics: importer from Charon's ULLBC JSON to the MIR fixtypes.
;
; Two passes over the parsed JSON (kestrel/json-parser):
;
;  1. Expand Charon's serialization sharing.  Charon keeps one sharing table
;     per hash-consed type (types, trait references, constant expressions,
;     layout size expressions, layout predicates, spans): {"Value": [id, X]}
;     is the first, full occurrence of X and defines id in that table,
;     {"Deduplicated": id} refers back to it, and {"Untagged": X} is an
;     unshared occurrence.  Which table a marker belongs to is determined by
;     its JSON context (the field name, its position in a list, and the
;     sibling fields), which jx-category encodes.  Spans are dropped.
;
;  2. Map the expanded JSON to a program value: the crate's functions (with
;     their bodies), its globals, and, at each call site, either a crate
;     function or a standard-library model chosen by the classifier from the
;     callee's path (implementation self type and trait) and the call's
;     generic arguments.  Unwind edges are dropped (abort-on-panic), the
;     target is checked to be 64-bit, enum discriminants are checked to be
;     the variant indices, and drops and other unsupported statements are
;     rejected.
;
; The navigation functions are nil-tolerant: they return nil (or a default)
; on unexpected input, and ACL2 accepts the recursion over the semi-structured
; input after a few linear lemmas about acl2-count.

(in-package "MIR")

(include-book "syntax")
(include-book "kestrel/json-parser/parse-json-file" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/cat" :dir :system)

(set-induction-depth-limit 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Navigation in parsed JSON: (:object ((key . val) ...)), (:array (val ...)),
;; strings, rationals, :true, :false, :null.

(define jpairs (x)
  :returns (pairs true-listp :rule-classes :type-prescription)
  (if (and (consp x) (eq (car x) :object) (consp (cdr x)) (true-listp (cadr x)))
      (cadr x)
    nil))

(define jvals (x)
  :returns (vals true-listp :rule-classes :type-prescription)
  (if (and (consp x) (eq (car x) :array) (consp (cdr x)) (true-listp (cadr x)))
      (cadr x)
    nil))

(define jassoc (key pairs)
  (cond ((atom pairs) nil)
        ((and (consp (car pairs)) (equal (caar pairs) key)) (cdar pairs))
        (t (jassoc key (cdr pairs)))))

(define jget (key x) (jassoc key (jpairs x)))

(define jnth ((n natp) vals)
  (cond ((atom vals) nil)
        ((zp n) (car vals))
        (t (jnth (1- n) (cdr vals)))))

(define jelem ((n natp) x) (jnth n (jvals x)))

;; The tag of a single-field object {"Tag": X} (or of a string "Tag"), and X.
(define jtag (x)
  (b* ((pairs (jpairs x)))
    (cond ((stringp x) x)
          ((and (consp pairs) (consp (car pairs))) (caar pairs))
          (t nil))))

(define jtagval (x)
  (b* ((pairs (jpairs x)))
    (if (and (consp pairs) (consp (car pairs))) (cdar pairs) nil)))

(define jnat (x)
  :returns (n natp :rule-classes :type-prescription)
  (if (natp x) x 0))

(define jbool (x)
  :returns (b booleanp)
  (eq x :true))

(define jstr (x)
  :returns (s stringp :rule-classes :type-prescription)
  (if (stringp x) x ""))

;; Linear lemmas for termination of the recursions below.

(defthm acl2-count-of-jassoc
  (<= (acl2-count (jassoc key pairs)) (acl2-count pairs))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable jassoc))))

(defthm acl2-count-of-jpairs
  (implies (consp x) (< (acl2-count (jpairs x)) (acl2-count x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable jpairs))))

(defthm acl2-count-of-jvals
  (implies (consp x) (< (acl2-count (jvals x)) (acl2-count x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable jvals))))

(defthm acl2-count-of-jget
  (implies (consp x) (< (acl2-count (jget key x)) (acl2-count x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable jget))))

(defthm acl2-count-of-jnth
  (<= (acl2-count (jnth n vals)) (acl2-count vals))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable jnth))))

(defthm acl2-count-of-jelem
  (implies (consp x) (< (acl2-count (jelem n x)) (acl2-count x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable jelem))))

(defthm acl2-count-of-jtagval
  (implies (consp x) (< (acl2-count (jtagval x)) (acl2-count x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable jtagval jpairs))))

(defthm acl2-count-of-jpairs-weak
  (<= (acl2-count (jpairs x)) (acl2-count x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable jpairs))))

(defthm acl2-count-of-jvals-weak
  (<= (acl2-count (jvals x)) (acl2-count x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable jvals))))

(defthm acl2-count-of-jget-weak
  (<= (acl2-count (jget key x)) (acl2-count x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable jget))))

(defthm acl2-count-of-jelem-weak
  (<= (acl2-count (jelem n x)) (acl2-count x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable jelem))))

(defthm acl2-count-of-jtagval-weak
  (<= (acl2-count (jtagval x)) (acl2-count x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable jtagval jpairs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pass 1: expanding the sharing

;; Sharing tables: 0 = spans (dropped), 1 = types, 2 = trait references,
;; 3 = constant expressions, 4 = layout size expressions, 5 = layout
;; predicates; nil = no table (a marker there is an error).
;; Inside the content of a shared value of table c, the context key is the
;; string "#c" (it matters for constant expressions, which are [kind, ty]).

(defconst *jx-ty-keys*
  '("ty" "types" "inputs" "output" "Lub" "Alias" "SizeOf" "AlignOf"
    "GenericType" "InheritFrom" "self_ty"))
(defconst *jx-tref-keys*
  '("Copy" "ParentClause" "TraitType" "elem_is_copy" "elem_is_sized" "trait_ref"))
(defconst *jx-cexpr-keys*
  '("Const" "Constant" "Length" "const_generics" "count" "ptr_metadata" "branches"))
(defconst *jx-size-keys*
  '("AtLeast" "GuaranteedAlignment" "Max" "chosen" "target_align" "guarantee"
    "base" "Plus" "AlignTo"))
(defconst *jx-pred-keys* '("And" "Or" "inhabited"))

(define jx-category (key idx sibs)
  :returns (cat maybe-natp :rule-classes :type-prescription)
  (cond ((equal key "span") 0)
        ((equal key "#3") (if (equal idx 1) 1 nil))
        ((equal key "skip_binder") (if (member-equal "params" (true-list-fix sibs)) 1 2))
        ((equal key "value") (if (member-equal "implied_trait_refs" (true-list-fix sibs)) 1 3))
        ((equal key "Ref") (if (equal idx 1) 1 nil))
        ((equal key "RawPtr") (if (equal idx 0) 1 nil))
        ((equal key "Unsize") (if (equal idx 0) 1 nil))
        ((equal key "Array") (cond ((equal idx 0) 1) ((equal idx 1) 3) ((equal idx 2) 2) (t nil)))
        ((equal key "Slice") (cond ((equal idx 0) 1) ((equal idx 1) 2) (t nil)))
        ((and (member-equal key '("Const" "Constant")) (equal idx 1)) 1)
        ((and (equal key "Copy") (equal idx 1)) 2)
        ((member-equal key *jx-ty-keys*) 1)
        ((member-equal key *jx-tref-keys*) 2)
        ((member-equal key *jx-cexpr-keys*) 3)
        ((member-equal key *jx-size-keys*) 4)
        ((member-equal key *jx-pred-keys*) 5)
        (t nil)))

(define jx-content-key ((cat natp))
  :returns (k stringp :rule-classes :type-prescription)
  (case cat (1 "#1") (2 "#2") (3 "#3") (4 "#4") (5 "#5") (otherwise "#0")))

(define jx-table-key ((cat natp) (id natp))
  :returns (k natp :rule-classes :type-prescription)
  (+ (* 8 (lnfix id)) (lnfix cat)))

;; Recognize a sharing marker: returns (mv kind id content), kind one of
;; :value, :dedup, :untagged, or nil.
(define jx-marker (x)
  :returns (mv kind (id natp :rule-classes :type-prescription) content)
  (b* ((pairs (jpairs x))
       ((unless (and (consp pairs) (consp (car pairs)) (atom (cdr pairs))))
        (mv nil 0 nil))
       (k (caar pairs))
       (v (cdar pairs)))
    (cond ((equal k "Untagged") (mv :untagged 0 v))
          ((and (equal k "Deduplicated") (natp v)) (mv :dedup v nil))
          ((and (equal k "Value")
                (natp (jnth 0 (jvals v)))
                (equal (len (jvals v)) 2))
           (mv :value (jnth 0 (jvals v)) (jnth 1 (jvals v))))
          (t (mv nil 0 nil)))))

(defthm acl2-count-of-jx-marker-content
  (implies (consp x) (< (acl2-count (mv-nth 2 (jx-marker x))) (acl2-count x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable jx-marker jget jassoc jpairs jvals jnth))))

(defines jx-expand
  :flag-local nil
  (define jx-expand (x key idx sibs tabs errs)
    ;; Returns (mv expanded-x tabs errs).
    :measure (acl2-count x)
    (b* (((when (atom x)) (mv x tabs errs))
         ((when (eq (car x) :array))
          (b* (((mv vals tabs errs) (jx-expand-list (jvals x) key 0 sibs tabs errs)))
            (mv (list :array vals) tabs errs)))
         ((unless (eq (car x) :object)) (mv x tabs errs))
         ((mv kind id content) (jx-marker x)))
      (case kind
        (:untagged (jx-expand content key idx sibs tabs errs))
        (:value
         (b* ((cat (jx-category key idx sibs))
              ((unless cat) (mv nil tabs (cons (list :unknown-sharing-context key idx) errs)))
              ((when (equal cat 0)) (mv nil tabs errs)) ; spans are dropped
              ((mv v tabs errs) (jx-expand content (jx-content-key cat) nil sibs tabs errs)))
           (mv v (hons-acons (jx-table-key cat id) v tabs) errs)))
        (:dedup
         (b* ((cat (jx-category key idx sibs))
              ((unless cat) (mv nil tabs (cons (list :unknown-sharing-context key idx) errs)))
              ((when (equal cat 0)) (mv nil tabs errs))
              (hit (hons-get (jx-table-key cat id) tabs)))
           (if hit
               (mv (cdr hit) tabs errs)
             (mv nil tabs (cons (list :dangling-reference key id) errs)))))
        (otherwise
         (b* ((pairs (jpairs x))
              ((mv pairs tabs errs) (jx-expand-pairs pairs (strip-cars-safe pairs) tabs errs)))
           (mv (list :object pairs) tabs errs))))))
  (define jx-expand-pairs (pairs sibs tabs errs)
    :measure (acl2-count pairs)
    (b* (((when (atom pairs)) (mv nil tabs errs))
         (p (car pairs))
         ((unless (consp p)) (jx-expand-pairs (cdr pairs) sibs tabs errs))
         ((mv v tabs errs) (jx-expand (cdr p) (car p) nil sibs tabs errs))
         ((mv rest tabs errs) (jx-expand-pairs (cdr pairs) sibs tabs errs)))
      (mv (cons (cons (car p) v) rest) tabs errs)))
  (define jx-expand-list (vals key (i natp) sibs tabs errs)
    :measure (acl2-count vals)
    (b* (((when (atom vals)) (mv nil tabs errs))
         ((mv v tabs errs) (jx-expand (car vals) key (lnfix i) sibs tabs errs))
         ((mv rest tabs errs) (jx-expand-list (cdr vals) key (+ 1 (lnfix i)) sibs tabs errs)))
      (mv (cons v rest) tabs errs)))
  :prepwork
  ((define strip-cars-safe (pairs)
     :returns (keys true-listp :rule-classes :type-prescription)
     (cond ((atom pairs) nil)
           ((consp (car pairs)) (cons (caar pairs) (strip-cars-safe (cdr pairs))))
           (t (strip-cars-safe (cdr pairs)))))))

;; Expand a whole document; returns (mv errs expanded).
(define jx-expand-document (doc)
  (b* (((mv x tabs errs) (jx-expand doc "" nil nil nil nil)))
    (prog2$ (fast-alist-free tabs)
            (mv (reverse (true-list-fix errs)) x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pass 2: mapping to the MIR fixtypes

;; ---- integers and literals

(define digits-value (cs (acc natp))
  :returns (mv (ok booleanp) (n natp :rule-classes :type-prescription))
  (b* (((when (atom cs)) (mv t (lnfix acc)))
       (c (car cs))
       ((unless (and (characterp c) (char<= #\0 c) (char<= c #\9))) (mv nil 0)))
    (digits-value (cdr cs) (+ (* 10 (lnfix acc)) (- (char-code c) 48)))))

(define parse-int-string ((s stringp))
  :returns (mv (ok booleanp) (n integerp :rule-classes :type-prescription))
  (b* ((cs (coerce (str-fix s) 'list))
       ((when (atom cs)) (mv nil 0))
       (neg (eql (car cs) #\-))
       (digits (if neg (cdr cs) cs))
       ((when (atom digits)) (mv nil 0))
       ((mv ok n) (digits-value digits 0)))
    (mv ok (if neg (- n) n))))

(define json-inttype (x)
  ;; {"Unsigned": "U32"} or {"Signed": "I32"} (or with the name in a list).
  :returns (mv (ok booleanp) (it inttype-p))
  (b* ((tag (jtag x))
       (v (jtagval x))
       (name (if (stringp v) v (jnth 0 (jvals v))))
       (it (cond ((equal tag "Unsigned")
                  (cond ((equal name "U8") :u8) ((equal name "U16") :u16)
                        ((equal name "U32") :u32) ((equal name "U64") :u64)
                        ((equal name "U128") :u128) ((equal name "Usize") :usize)
                        (t nil)))
                 ((equal tag "Signed")
                  (cond ((equal name "I8") :i8) ((equal name "I16") :i16)
                        ((equal name "I32") :i32) ((equal name "I64") :i64)
                        ((equal name "I128") :i128) ((equal name "Isize") :isize)
                        (t nil)))
                 (t nil))))
    (if it (mv t it) (mv nil :u8))))

;; {"Unsigned": ["U32", "5"]} -> (mv t :u32 5)
(define json-int-literal (x)
  :returns (mv (ok booleanp) (it inttype-p) (v integerp :rule-classes :type-prescription))
  (b* (((mv ok it) (json-inttype x))
       ((unless ok) (mv nil :u8 0))
       ((mv ok v) (parse-int-string (jstr (jnth 1 (jvals (jtagval x)))))))
    (mv ok it v)))

;; ---- types

(defines json-ty
  :verify-guards nil
  (define json-ty (x)
    :returns (ty ty-p)
    :measure (acl2-count x)
    (b* (((when (atom x)) (if (equal x "Never") (ty-never) (ty-other)))
         (tag (jtag x))
         (v (jtagval x)))
      (cond ((equal tag "Scalar")
             (cond ((equal v "Bool") (ty-bool))
                   ((equal v "Char") (ty-char))
                   ((equal (jtag v) "Integer")
                    (b* (((mv ok it) (json-inttype (jtagval v))))
                      (if ok (ty-int it) (ty-other))))
                   (t (ty-other))))
            ((equal tag "Adt")
             (b* ((builtin (jget "builtin" v))
                  (args (if (consp v) (json-ty-list (jvals (jget "types" (jget "generics" v)))) nil)))
               (cond ((equal builtin "Tuple") (ty-tuple args))
                     ((equal builtin "Str") (ty-str))
                     (t (ty-adt (jnat (jget "id" v)) args)))))
            ((equal tag "Array")
             (b* ((elem (if (consp v) (json-ty (jelem 0 v)) (ty-other)))
                  (len (jelem 1 v))
                  (lit (jnth 0 (jvals len)))
                  ((mv ok & n) (if (equal (jtag lit) "Integer")
                                   (json-int-literal (jtagval lit))
                                 (mv nil :u8 0))))
               (ty-array elem (and ok (natp n) n))))
            ((equal tag "Slice") (ty-slice (if (consp v) (json-ty (jelem 0 v)) (ty-other))))
            ((equal tag "Ref")
             (ty-ref (if (consp v) (json-ty (jelem 1 v)) (ty-other))
                     (equal (jelem 2 v) "Mut")))
            ((equal tag "RawPtr")
             (ty-rawptr (if (consp v) (json-ty (jelem 0 v)) (ty-other))
                        (equal (jelem 1 v) "Mut")))
            ((equal tag "TypeVar")
             (ty-param (jnat (jnth 1 (jvals (jtagval v))))))
            (t (ty-other)))))
  (define json-ty-list (xs)
    :returns (tys ty-list-p)
    :measure (acl2-count xs)
    (if (atom xs)
        nil
      (cons (json-ty (car xs)) (json-ty-list (cdr xs)))))
  ///
  (verify-guards json-ty))

(define json-generic-types (generics)
  :returns (tys ty-list-p)
  (json-ty-list (jvals (jget "types" generics))))

;; Rendering of a type for the classifier: "u32", "array", "slice", "&slice",
;; "Range", "T", ...
(define ty-short-name ((ty ty-p) (adt-names true-listp))
  :returns (s stringp :rule-classes :type-prescription)
  (ty-case ty
    :int (str::downcase-string (symbol-name ty.it))
    :bool "bool"
    :char "char"
    :str "str"
    :never "!"
    :tuple "tuple"
    :adt (let ((name (jassoc ty.id adt-names)))
           (if (stringp name) name "adt"))
    :array "array"
    :slice "slice"
    :ref (str::cat "&" (ty-case ty.target :slice "slice" :array "array"
                                :int (str::downcase-string (symbol-name ty.target.it))
                                :otherwise "T"))
    :rawptr "ptr"
    :param "T"
    :other "?"))

;; ---- constants

(defines json-constant
  :verify-guards nil
  (define json-constant (k)
    ;; k is the kind part of a constant expression [kind, ty]
    :returns (c constant-p)
    :measure (acl2-count k)
    (b* (((when (atom k)) (constant-other))
         (tag (jtag k))
         (v (jtagval k)))
      (cond ((equal tag "Integer")
             (b* (((mv ok it n) (json-int-literal v)))
               (if ok (constant-int it n) (constant-other))))
            ((equal tag "Bool") (constant-bool (jbool v)))
            ((equal tag "Str") (constant-str (jstr v)))
            ((equal tag "Adt")
             (b* ((variant (jelem 0 v))
                  (fields (if (consp v) (json-constant-list (jvals (jelem 1 v))) nil)))
               (constant-adt (and (natp variant) variant) fields)))
            (t (constant-other)))))
  (define json-constant-list (cs)
    ;; each element is a constant expression [kind, ty]
    :returns (l constant-list-p)
    :measure (acl2-count cs)
    (if (atom cs)
        nil
      (cons (if (consp (car cs)) (json-constant (jelem 0 (car cs))) (constant-other))
            (json-constant-list (cdr cs)))))
  ///
  (verify-guards json-constant))

(define json-cexpr (x)
  :returns (c constant-p)
  (json-constant (jelem 0 x)))

;; ---- places and operands

(define json-index-operand (x)
  ;; The offset of an Index projection: a copy or move of a local, or a
  ;; constant.  (No nested places, so no mutual recursion with places.)
  :returns (op operand-p)
  (b* ((tag (jtag x))
       (v (jtagval x))
       (p (if (equal tag "Copy") (if (equal (jtag v) nil) (jelem 0 v) v) v))
       (kind (jget "kind" p)))
    (cond ((and (member-equal tag '("Copy" "Move" "Read"))
                (equal (jtag kind) "Local"))
           (operand-copy (place-local (jnat (jtagval kind)))))
          ((equal tag "Const") (operand-const (json-cexpr v)))
          (t (operand-const (constant-other))))))

(define json-projelem (e)
  :returns (mv (ok booleanp) (pe projelem-p))
  (b* ((tag (jtag e))
       (v (jtagval e)))
    (cond ((equal tag "Deref") (mv t (projelem-deref)))
          ((equal tag "PtrMetadata") (mv t (projelem-ptr-metadata)))
          ((equal tag "Field")
           (b* ((variant (jelem 0 v)))
             (mv t (projelem-field (and (natp variant) variant) (jnat (jelem 1 v))))))
          ((equal tag "Index")
           (mv t (projelem-index (json-index-operand (jget "offset" v))
                                 (jbool (jget "from_end" v)))))
          (t (mv nil (projelem-deref))))))

(define json-place (x)
  ;; {"kind": {"Local": n} | {"Global": {...}} | {"Projection": [place, elem]}, "ty": ...}
  :returns (mv (ok booleanp) (p place-p))
  :measure (acl2-count x)
  :verify-guards :after-returns
  (b* (((when (atom x)) (mv nil (place-local 0)))
       (kind (jget "kind" x))
       (tag (jtag kind))
       (v (jtagval kind)))
    (cond ((equal tag "Local") (mv (natp v) (place-local (jnat v))))
          ((equal tag "Global") (mv t (place-global (jnat (jget "id" v)))))
          ((and (equal tag "Projection") (consp kind) (consp x))
           (b* ((base (jelem 0 v))
                ((unless (< (acl2-count base) (acl2-count x))) (mv nil (place-local 0)))
                ((mv ok b) (json-place base))
                ((unless ok) (mv nil (place-local 0)))
                ((mv ok e) (json-projelem (jelem 1 v))))
             (mv ok (place-proj b e))))
          (t (mv nil (place-local 0))))))

(define json-operand (x)
  :returns (mv (ok booleanp) (op operand-p))
  (b* ((tag (jtag x))
       (v (jtagval x)))
    (cond ((equal tag "Copy")
           ;; {"Copy": [place, copy-proof]} (or {"Copy": place})
           (b* ((p (if (jvals v) (jelem 0 v) v))
                ((mv ok pl) (json-place p)))
             (mv ok (operand-copy pl))))
          ((equal tag "Move")
           (b* (((mv ok pl) (json-place v))) (mv ok (operand-move pl))))
          ((equal tag "Read")
           (b* (((mv ok pl) (json-place v))) (mv ok (operand-read pl))))
          ((equal tag "Const") (mv t (operand-const (json-cexpr v))))
          (t (mv nil (operand-const (constant-other)))))))

(define json-operand-list (xs)
  :returns (mv (ok booleanp) (ops operand-list-p))
  (b* (((when (atom xs)) (mv t nil))
       ((mv ok op) (json-operand (car xs)))
       ((unless ok) (mv nil nil))
       ((mv ok ops) (json-operand-list (cdr xs))))
    (mv ok (cons op ops))))

;; ---- rvalues

(define json-overflow-mode (x)
  :returns (m overflow-mode-p)
  (cond ((equal x "Panic") :panic)
        ((equal x "UB") :ub)
        (t :wrap)))

(define json-binop (x)
  :returns (mv (ok booleanp) (op binop-p))
  (b* ((tag (jtag x))
       (mode (json-overflow-mode (jtagval x)))
       (name (cond ((equal tag "BitXor") :bitxor) ((equal tag "BitAnd") :bitand)
                   ((equal tag "BitOr") :bitor) ((equal tag "Eq") :eq)
                   ((equal tag "Ne") :ne) ((equal tag "Lt") :lt) ((equal tag "Le") :le)
                   ((equal tag "Gt") :gt) ((equal tag "Ge") :ge)
                   ((equal tag "Add") :add) ((equal tag "Sub") :sub)
                   ((equal tag "Mul") :mul) ((equal tag "Div") :div)
                   ((equal tag "Rem") :rem) ((equal tag "Shl") :shl)
                   ((equal tag "Shr") :shr) (t nil))))
    (if name (mv t (binop name mode)) (mv nil (binop :eq :wrap)))))

(define json-unop (x)
  :returns (mv (ok booleanp) (op unop-p))
  (b* ((tag (jtag x))
       (v (jtagval x)))
    (cond ((equal tag "Not") (mv t (unop-not)))
          ((equal tag "Neg") (mv t (unop-neg (json-overflow-mode v))))
          ((equal tag "Cast")
           (b* ((ctag (jtag v))
                (cv (jtagval v)))
             (cond ((equal ctag "Unsize") (mv t (unop-unsize)))
                   ((and (equal ctag "Scalar") (equal (jtag cv) "Integer"))
                    (b* (((mv ok it) (json-inttype (jtagval cv))))
                      (mv ok (unop-cast-int it))))
                   (t (mv t (unop-other-cast))))))
          (t (mv nil (unop-not))))))

(define json-refkind (x)
  :returns (k refkind-p)
  (cond ((equal x "Mut") :mut)
        ((equal x "TwoPhaseMut") :two-phase-mut)
        (t :shared)))

(define json-rvalue (x (bad-enums true-listp))
  :returns (mv (ok booleanp) (rv rvalue-p))
  (b* ((tag (jtag x))
       (v (jtagval x))
       (fail (rvalue-use (operand-const (constant-other)))))
    (cond ((equal tag "Use")
           (b* (((mv ok op) (json-operand (if (jvals v) (jelem 0 v) v))))
             (mv ok (rvalue-use op))))
          ((equal tag "Ref")
           (b* (((mv ok p) (json-place (jget "place" v))))
             (mv ok (rvalue-ref p (json-refkind (jget "kind" v))))))
          ((equal tag "RawPtr")
           (b* (((mv ok p) (json-place (jget "place" v))))
             (mv ok (rvalue-rawptr p (if (equal (jget "kind" v) "Mut") :raw-mut :raw-const)))))
          ((equal tag "BinaryOp")
           (b* (((mv ok1 op) (json-binop (jelem 0 v)))
                ((mv ok2 a) (json-operand (jelem 1 v)))
                ((mv ok3 b) (json-operand (jelem 2 v))))
             (mv (and ok1 ok2 ok3) (rvalue-binop op a b))))
          ((equal tag "UnaryOp")
           (b* (((mv ok1 op) (json-unop (jelem 0 v)))
                ((mv ok2 a) (json-operand (jelem 1 v))))
             (mv (and ok1 ok2) (rvalue-unop op a))))
          ((equal tag "Discriminant")
           ;; The semantics reads a discriminant as the variant index; enums
           ;; with other discriminants are rejected.
           (b* (((mv ok p) (json-place v))
                (id (jget "id" (jget "Adt" (jget "ty" v)))))
             (mv (and ok (not (member-equal id bad-enums))) (rvalue-discriminant p))))
          ((equal tag "Aggregate")
           (b* ((k (jelem 0 v))
                ((mv ok ops) (json-operand-list (jvals (jelem 1 v))))
                (ktag (jtag k))
                (kv (jtagval k)))
             (cond ((equal ktag "Adt")
                    (b* ((variant (jelem 1 kv)))
                      (mv ok (rvalue-aggregate
                              (aggkind-adt (jnat (jget "id" (jelem 0 kv)))
                                           (and (natp variant) variant))
                              ops))))
                   ((equal ktag "Array") (mv ok (rvalue-aggregate (aggkind-array) ops)))
                   (t (mv nil fail)))))
          ((equal tag "Repeat")
           (b* (((mv ok op) (json-operand (jget "operand" v)))
                (c (json-cexpr (jget "count" v))))
             (if (and (constant-case c :int) (natp (constant-int->v c)))
                 (mv ok (rvalue-repeat op (constant-int->v c)))
               (mv nil fail))))
          (t (mv nil fail)))))

;; ---- statements

(define json-statement (x (bad-enums true-listp))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (s statement-p))
  (b* ((k (jget "kind" x))
       (tag (jtag k))
       (v (jtagval k)))
    (cond ((equal tag "Assign")
           (b* (((mv ok1 p) (json-place (jelem 0 v)))
                ((mv ok2 rv) (json-rvalue (jelem 1 v) bad-enums)))
             (if (and ok1 ok2)
                 (mv nil (statement-assign p rv))
               (mv "unsupported assignment" (statement-nop)))))
          ((equal tag "StorageLive") (mv nil (statement-storage-live (jnat v))))
          ((equal tag "StorageDead") (mv nil (statement-storage-dead (jnat v))))
          ((equal tag "Nop") (mv nil (statement-nop)))
          ((member-equal tag '("Drop" "PlaceMention"))
           (mv (str::cat "unsupported statement " tag) (statement-nop)))
          (t (mv (str::cat "unsupported statement " (if (stringp tag) tag "?"))
                 (statement-nop))))))

(define json-statement-list (xs (bad-enums true-listp))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (ss statement-list-p))
  (b* (((when (atom xs)) (mv nil nil))
       ((mv err s) (json-statement (car xs) bad-enums))
       ((when err) (mv err nil))
       ((mv err ss) (json-statement-list (cdr xs) bad-enums)))
    (mv err (cons s ss))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The classifier

;; Context for classification: the crate's declarations.
(fty::defprod crate-info
  ((funs true-listp)          ; fun_decls (JSON values, index = id)
   (trait-impls true-listp)
   (trait-decls true-listp)
   (adt-names true-listp)     ; alist type id -> short name
   (type-paths true-listp)    ; alist type id -> full path
   (bad-enums true-listp)))   ; ids of enums whose discriminants are not the variant indices

(define name-elem-ident (e)
  :returns (s acl2::maybe-stringp :rule-classes :type-prescription)
  (if (equal (jtag e) "Ident")
      (let ((s (jnth 0 (jvals (jtagval e))))) (if (stringp s) s nil))
    nil))

(define simple-path-aux (elems)
  ;; Join the identifiers of a name with "::" (impl elements become "{impl}").
  :returns (s stringp :rule-classes :type-prescription)
  (b* (((when (atom elems)) "")
       (e (car elems))
       (s (or (name-elem-ident e)
              (cond ((equal (jtag e) "Impl") "{impl}")
                    ((equal (jtag e) "Builtin") "{builtin}")
                    (t "?"))))
       (rest (simple-path-aux (cdr elems))))
    (if (equal rest "") s (str::cat s "::" rest))))

(define simple-path (name)
  :returns (s stringp :rule-classes :type-prescription)
  (simple-path-aux (jvals name)))

(define impl-elem-string (e (info crate-info-p))
  ;; {impl TRAIT for SELF} or {inherent SELF}
  :returns (s stringp :rule-classes :type-prescription)
  (b* ((i (jtagval e))
       (adts (crate-info->adt-names info)))
    (cond ((equal (jtag i) "Trait")
           (b* ((impl (jnth (jnat (jtagval i)) (crate-info->trait-impls info)))
                (tr (jget "impl_trait" impl))
                (decl (jnth (jnat (jget "id" tr)) (crate-info->trait-decls info)))
                (trait (simple-path (jget "name" (jget "item_meta" decl))))
                (self (jnth 0 (jvals (jget "types" (jget "generics" tr))))))
             (str::cat "{impl " trait " for " (ty-short-name (json-ty self) adts) "}")))
          ((equal (jtag i) "Ty")
           (str::cat "{inherent "
                     (ty-short-name (json-ty (jget "skip_binder" (jtagval i))) adts)
                     "}"))
          (t "{impl}"))))

(define decl-path-aux (elems (info crate-info-p))
  :returns (s stringp :rule-classes :type-prescription)
  (b* (((when (atom elems)) "")
       (e (car elems))
       (s (or (name-elem-ident e)
              (cond ((equal (jtag e) "Impl") (impl-elem-string e info))
                    ((equal (jtag e) "Builtin")
                     (b* ((b (jtagval e))
                          (k (jtag (jnth 0 (jvals b)))))
                       (str::cat "{" (if (stringp k) k "builtin") "}")))
                    (t "?"))))
       (rest (decl-path-aux (cdr elems) info)))
    (if (equal rest "") s (str::cat s "::" rest))))

;; The full path of a declaration, with implementations rendered by trait
;; and self type, e.g. "core::array::{impl core::default::Default for array}::default".
(define decl-path (decl (info crate-info-p))
  :returns (s stringp :rule-classes :type-prescription)
  (decl-path-aux (jvals (jget "name" (jget "item_meta" decl))) info))

;; The table of modeled functions: path -> model.
(defconst *std-model-table*
  '(("core::slice::{inherent slice}::len" . :slice-len)
    ("core::slice::{inherent slice}::iter" . :slice-iter)
    ("core::slice::{inherent slice}::iter_mut" . :slice-iter-mut)
    ("core::slice::{inherent slice}::copy_from_slice" . :copy-from-slice)
    ("core::slice::iter::{impl core::iter::traits::collect::IntoIterator for &slice}::into_iter" . :slice-into-iter)
    ("core::array::{impl core::ops::index::Index for array}::index" . :index)
    ("core::array::{impl core::ops::index::IndexMut for array}::index_mut" . :index)
    ("core::slice::index::{impl core::ops::index::Index for slice}::index" . :index)
    ("core::slice::index::{impl core::ops::index::IndexMut for slice}::index_mut" . :index)
    ("core::array::{impl core::default::Default for array}::default" . :array-default)
    ("core::convert::{impl core::convert::TryInto for T}::try_into" . :try-into-array)
    ("core::result::{inherent Result}::unwrap" . :result-unwrap)
    ("core::iter::traits::collect::{impl core::iter::traits::collect::IntoIterator for T}::into_iter" . :into-iter)
    ("core::iter::traits::iterator::Iterator::step_by" . :step-by)
    ("core::iter::traits::iterator::Iterator::rev" . :rev)
    ("core::iter::traits::iterator::Iterator::zip" . :zip)
    ("core::iter::range::{impl core::iter::traits::iterator::Iterator for Range}::next" . :range-next)
    ("core::iter::range::{impl core::iter::traits::double_ended::DoubleEndedIterator for Range}::next_back" . :range-next-back)
    ("core::iter::adapters::step_by::{impl core::iter::traits::iterator::Iterator for StepBy}::next" . :step-by-next)
    ("core::iter::adapters::rev::{impl core::iter::traits::iterator::Iterator for Rev}::next" . :rev-next)
    ("core::iter::adapters::zip::{impl core::iter::traits::iterator::Iterator for Zip}::next" . :zip-next)
    ("core::slice::iter::{impl core::iter::traits::iterator::Iterator for IterMut}::next" . :slice-iter-next)
    ("core::slice::iter::{impl core::iter::traits::iterator::Iterator for Iter}::next" . :slice-iter-next)
    ("core::num::{inherent u8}::from_le_bytes" . :from-le-bytes)
    ("core::num::{inherent u16}::from_le_bytes" . :from-le-bytes)
    ("core::num::{inherent u32}::from_le_bytes" . :from-le-bytes)
    ("core::num::{inherent u64}::from_le_bytes" . :from-le-bytes)
    ("core::num::{inherent u32}::to_le_bytes" . :to-le-bytes)
    ("core::num::{inherent u64}::to_le_bytes" . :to-le-bytes)
    ("core::num::{inherent u32}::rotate_right" . :rotate-right)
    ("core::num::{inherent u64}::rotate_right" . :rotate-right)
    ("core::num::{inherent u32}::rotate_left" . :rotate-left)
    ("core::num::{inherent u64}::rotate_left" . :rotate-left)
    ("core::ops::bit::{impl core::ops::bit::BitXorAssign for u32}::bitxor_assign" . :bitxor-assign-ref)
    ("core::ops::bit::{impl core::ops::bit::BitXorAssign for u8}::bitxor_assign" . :bitxor-assign-ref)
    ("core::intrinsics::add_with_overflow" . :add-with-overflow)
    ("core::intrinsics::sub_with_overflow" . :sub-with-overflow)
    ("core::intrinsics::mul_with_overflow" . :mul-with-overflow)
    ("core::panicking::panic" . :panic)
    ("core::panicking::assert_failed" . :assert-failed)))

;; The Index model is chosen from the index type (the second generic argument).
(define index-model ((idx-ty ty-p) (info crate-info-p))
  :returns (model symbolp)
  (ty-case idx-ty
    :int :index-usize
    :adt (let ((path (jassoc idx-ty.id (crate-info->type-paths info))))
           (cond ((equal path "core::ops::range::Range") :index-range)
                 ((equal path "core::ops::range::RangeTo") :index-range-to)
                 ((equal path "core::ops::range::RangeFrom") :index-range-from)
                 ((equal path "core::ops::range::RangeFull") :index-range-full)
                 (t nil)))
    :otherwise nil))

;; Substitute generic arguments for type parameters (for the self type of
;; an implementation, e.g. [T; 8] with T := u32).
(defines ty-subst
  :verify-guards nil
  (define ty-subst ((ty ty-p) (args ty-list-p))
    :returns (r ty-p)
    :measure (ty-count ty)
    (ty-case ty
      :param (if (< ty.index (len args)) (ty-fix (nth ty.index args)) (ty-fix ty))
      :tuple (ty-tuple (ty-list-subst ty.elems args))
      :adt (ty-adt ty.id (ty-list-subst ty.args args))
      :array (ty-array (ty-subst ty.elem args) ty.len)
      :slice (ty-slice (ty-subst ty.elem args))
      :ref (ty-ref (ty-subst ty.target args) ty.mut)
      :rawptr (ty-rawptr (ty-subst ty.target args) ty.mut)
      :otherwise (ty-fix ty)))
  (define ty-list-subst ((tys ty-list-p) (args ty-list-p))
    :returns (r ty-list-p)
    :measure (ty-list-count tys)
    (if (atom tys) nil
      (cons (ty-subst (car tys) args) (ty-list-subst (cdr tys) args))))
  ///
  (verify-guards ty-subst))

(define impl-self-ty (decl (info crate-info-p))
  ;; The self type of the trait implementation a method belongs to.
  :returns (ty ty-p)
  (b* ((elems (jvals (jget "name" (jget "item_meta" decl))))
       (impl (impl-elem-find elems)))
    (if impl
        (b* ((i (jtagval impl))
             ((unless (equal (jtag i) "Trait")) (ty-other))
             (ti (jnth (jnat (jtagval i)) (crate-info->trait-impls info))))
          (json-ty (jnth 0 (jvals (jget "types" (jget "generics" (jget "impl_trait" ti)))))))
      (ty-other)))
  :prepwork
  ((define impl-elem-find (elems)
     (cond ((atom elems) nil)
           ((equal (jtag (car elems)) "Impl") (car elems))
           (t (impl-elem-find (cdr elems)))))))

;; Classify a call to a non-crate function: (mv model tys path).
(define classify-std-call ((id natp) generics (info crate-info-p))
  :returns (mv (model symbolp) (tys ty-list-p) (path stringp))
  (b* ((decl (jnth id (crate-info->funs info)))
       (path (decl-path decl info))
       (gtys (json-generic-types generics))
       (model (jassoc path *std-model-table*))
       ((unless (and model (symbolp model))) (mv nil nil path)))
    (case model
      (:index (mv (index-model (if (consp (cdr gtys)) (cadr gtys) (ty-other)) info)
                  nil path))
      (:array-default (mv model (list (ty-subst (impl-self-ty decl info) gtys)) path))
      (:try-into-array (mv model (if (consp (cdr gtys)) (list (cadr gtys)) nil) path))
      (:from-le-bytes
       (b* ((it (cond ((equal path "core::num::{inherent u8}::from_le_bytes") :u8)
                      ((equal path "core::num::{inherent u16}::from_le_bytes") :u16)
                      ((equal path "core::num::{inherent u32}::from_le_bytes") :u32)
                      (t :u64))))
         (mv model (list (ty-int it)) path)))
      (:zip (mv model gtys path))
      (otherwise (mv model gtys path)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Terminators, bodies, functions

(define json-assert-msg (check-kind)
  :returns (msg stringp :rule-classes :type-prescription)
  (b* ((tag (jtag check-kind))
       (v (jtagval check-kind)))
    (cond ((equal tag "Overflow")
           (b* ((op (jtag (jelem 0 v))))
             (str::cat "attempt to compute "
                       (if (stringp op) op "?") " with overflow")))
          ((equal tag "BoundsCheck") "index out of bounds")
          ((equal tag "RemainderByZero")
           "attempt to calculate the remainder with a divisor of zero")
          ((equal tag "DivisionByZero") "attempt to divide by zero")
          ((stringp tag) (str::cat "assertion failed: " tag))
          (t "assertion failed"))))

(define json-switch-branches (branches targets)
  ;; branches: [[cexpr, index-into-targets], ...]; targets: [block ids]
  :returns (mv (ok booleanp) (l switch-branch-list-p))
  (b* (((when (atom branches)) (mv t nil))
       (br (car branches))
       (c (json-cexpr (jelem 0 br)))
       (k (jelem 1 br))
       (target (jnth (jnat k) targets))
       ((unless (and (natp k) (natp target))) (mv nil nil))
       ((mv ok rest) (json-switch-branches (cdr branches) targets)))
    (mv ok (cons (switch-branch c target) rest))))

(define json-callee (func (info crate-info-p))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (c callee-p))
  (b* ((reg (jget "Regular" func))
       (fid (jget "Fun" (jget "kind" reg)))
       ((unless (natp fid))
        (mv "unsupported callee (not a regular function)" (callee-crate 0 "")))
       (decl (jnth fid (crate-info->funs info)))
       (local (and (jbool (jget "is_local" (jget "item_meta" decl)))
                   (equal (jtag (jget "body" decl)) "Unstructured")))
       ((when local) (mv nil (callee-crate fid (simple-path (jget "name" (jget "item_meta" decl))))))
       ((mv model tys path) (classify-std-call fid (jget "generics" reg) info))
       ((unless model)
        (mv (str::cat "unmodeled standard-library function " path) (callee-crate 0 ""))))
    (mv nil (callee-std model tys path))))

(define json-terminator (x (info crate-info-p))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (term terminator-p))
  (b* ((k (jget "kind" x))
       (tag (jtag k))
       (v (jtagval k))
       (fail (terminator-unreachable "")))
    (cond ((equal tag "Goto") (mv nil (terminator-goto (jnat (jget "target" v)))))
          ((equal tag "Return") (mv nil (terminator-return)))
          ((equal tag "UndefinedBehavior")
           (mv nil (terminator-unreachable "entered unreachable code")))
          ((equal tag "UnwindResume")
           ;; only reachable along unwind edges, which are dropped
           (mv nil (terminator-abort "unwind")))
          ((equal tag "Abort") (mv nil (terminator-abort "abort")))
          ((equal tag "Switch")
           (b* ((data (jget "data" v))
                (targets (jvals (jget "branches" v)))
                ((mv ok1 discr) (json-operand (jget "Value" (jget "scrutinee" data))))
                ((mv ok2 brs) (json-switch-branches (jvals (jget "branches" data)) targets))
                (fb (jnth (jnat (jget "fallback" data)) targets)))
             (if (and ok1 ok2 (natp fb))
                 (mv nil (terminator-switch discr brs fb))
               (mv "unsupported switch" fail))))
          ((equal tag "Assert")
           (b* ((a (jget "assert" v))
                ((mv ok c) (json-operand (jget "cond" a))))
             (if ok
                 (mv nil (terminator-assert c (jbool (jget "expected" a))
                                            (jnat (jget "target" v))
                                            (json-assert-msg (jget "check_kind" a))))
               (mv "unsupported assert" fail))))
          ((equal tag "Call")
           (b* ((call (jget "call" v))
                ((mv err callee) (json-callee (jget "func" call) info))
                ((when err) (mv err fail))
                ((mv ok1 args) (json-operand-list (jvals (jget "args" call))))
                ((mv ok2 dest) (json-place (jget "dest" v)))
                (target (jget "target" v)))
             (if (and ok1 ok2)
                 (mv nil (terminator-call callee args dest (and (natp target) target)))
               (mv "unsupported call" fail))))
          ((equal tag "Drop") (mv "unsupported terminator Drop (drops are rejected)" fail))
          (t (mv (str::cat "unsupported terminator " (if (stringp tag) tag "?")) fail)))))

(define json-blocks (xs (info crate-info-p))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (bs bblock-list-p))
  (b* (((when (atom xs)) (mv nil nil))
       ((mv err ss) (json-statement-list (jvals (jget "statements" (car xs)))
                                          (crate-info->bad-enums info)))
       ((when err) (mv err nil))
       ((mv err term) (json-terminator (jget "terminator" (car xs)) info))
       ((when err) (mv err nil))
       ((mv err bs) (json-blocks (cdr xs) info)))
    (mv err (cons (bblock ss term) bs))))

(define json-fundecl (decl (info crate-info-p))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (f fundecl-p))
  (b* ((name (simple-path (jget "name" (jget "item_meta" decl))))
       (body (jget "Unstructured" (jget "body" decl)))
       (locals (jget "locals" body))
       ((mv err blocks) (json-blocks (jvals (jget "body" body)) info))
       ((when err) (mv (str::cat name ": " err) (fundecl name (body 0 0 nil)))))
    (mv nil (fundecl name (body (jnat (jget "arg_count" locals))
                                (len (jvals (jget "locals" locals)))
                                blocks)))))

(define json-fundecls (decls (info crate-info-p))
  ;; The crate's own functions with bodies, keyed by declaration id.
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (al fundecl-alist-p))
  (b* (((when (atom decls)) (mv nil nil))
       (d (car decls))
       ((unless (and (jbool (jget "is_local" (jget "item_meta" d)))
                     (equal (jtag (jget "body" d)) "Unstructured")))
        (json-fundecls (cdr decls) info))
       ((mv err f) (json-fundecl d info))
       ((when err) (mv err nil))
       ((mv err rest) (json-fundecls (cdr decls) info)))
    (mv err (cons (cons (jnat (jget "def_id" d)) f) rest))))

(define json-globals (decls)
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (al globaldef-alist-p))
  (b* (((when (atom decls)) (mv nil nil))
       (d (car decls))
       ((unless (consp d)) (json-globals (cdr decls)))
       (val (jget "value" d))
       (kind (jelem 0 val))
       (def (if (equal (jtag kind) "Call")
                (b* ((fid (jget "Fun" (jget "kind" (jelem 0 (jtagval kind))))))
                  (and (natp fid) (globaldef-init fid)))
              (let ((c (json-constant kind)))
                (and (not (constant-case c :other)) (globaldef-const c)))))
       ((unless def) (mv "unsupported global initializer" nil))
       ((mv err rest) (json-globals (cdr decls))))
    (mv err (cons (cons (jnat (jget "def_id" d)) def) rest))))

;; Type declarations: short names, full paths, and the discriminant check.
(define json-type-names (decls)
  :returns (mv (short true-listp) (full true-listp))
  (b* (((when (atom decls)) (mv nil nil))
       (d (car decls))
       ((mv s f) (json-type-names (cdr decls)))
       ((unless (consp d)) (mv s f))
       (elems (jvals (jget "name" (jget "item_meta" d))))
       (last (name-elem-ident (car (last elems))))
       (id (jnat (jget "def_id" d))))
    (mv (cons (cons id (or last "adt")) s)
        (cons (cons id (simple-path-aux elems)) f))))

(define variants-discriminants-ok (variants (i natp))
  :returns (ok booleanp)
  (b* (((when (atom variants)) t)
       ((mv ok & n) (json-int-literal (jget "discriminant" (car variants)))))
    (and ok (equal n (lnfix i))
         (variants-discriminants-ok (cdr variants) (+ 1 (lnfix i))))))

(define bad-enum-ids (decls)
  ;; The enums whose discriminants are not their variant indices.
  :returns (ids true-listp :rule-classes :type-prescription)
  (b* (((when (atom decls)) nil)
       (d (car decls))
       (k (jget "kind" d))
       (rest (bad-enum-ids (cdr decls))))
    (if (and (equal (jtag k) "Enum")
             (not (variants-discriminants-ok (jvals (jtagval k)) 0)))
        (cons (jget "def_id" d) rest)
      rest)))

(define json-pointer-size-ok (tinfo)
  ;; A 64-bit target (usize = u64).
  :returns (ok booleanp)
  (b* ((entries (jvals tinfo)))
    (and (consp entries)
         (pointer-sizes-ok entries)))
  :prepwork
  ((define pointer-sizes-ok (entries)
     :returns (ok booleanp)
     (if (atom entries)
         t
       (and (equal (jget "target_pointer_size" (jget "value" (car entries))) 8)
            (pointer-sizes-ok (cdr entries)))))))

;; The whole conversion: (mv err program).
(define json-program (doc)
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (prog program-p))
  (b* ((empty (program "" nil nil))
       ((mv errs x) (jx-expand-document doc))
       ((when errs) (mv "sharing expansion failed" empty))
       (tr (jget "translated" x))
       ((unless (json-pointer-size-ok (jget "target_information" tr)))
        (mv "the target is not 64-bit" empty))
       (tdecls (jvals (jget "type_decls" tr)))
       ((mv short full) (json-type-names tdecls))
       (info (crate-info (jvals (jget "fun_decls" tr))
                         (jvals (jget "trait_impls" tr))
                         (jvals (jget "trait_decls" tr))
                         short full (bad-enum-ids tdecls)))
       ((mv err funs) (json-fundecls (jvals (jget "fun_decls" tr)) info))
       ((when err) (mv err empty))
       ((mv err globals) (json-globals (jvals (jget "global_decls" tr))))
       ((when err) (mv err empty)))
    (mv nil (program (jstr (jget "crate_name" tr)) funs globals))))

;; Read and import a ULLBC JSON file.
(define import-ullbc-file ((filename stringp) state)
  :returns (mv err (prog program-p) state)
  :verify-guards nil
  (b* (((mv erp doc state) (acl2::parse-file-as-json filename state))
       ((when erp) (mv "could not parse the JSON file" (program "" nil nil) state))
       ((mv err prog) (json-program doc)))
    (mv err prog state)))
