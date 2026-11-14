; MIR semantics: abstract syntax of the MIR subset (fixtypes).
;
; The subset follows Charon's ULLBC rendering of rustc's runtime-phase MIR
; (--mir elaborated).  It covers what the RustCrypto fixsliced AES-128 crate
; uses, and somewhat more: places with deref, field, index and
; pointer-metadata projections; copy, move, constant, and read operands; eight
; rvalue forms; assignments and storage markers; and seven terminator kinds.

(in-package "MIR")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/top" :dir :system)
(include-book "std/util/defenum" :dir :system)
(include-book "centaur/bitops/ihsext-basics" :dir :system)

(set-induction-depth-limit 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Integer types

(std::defenum inttype-p
  (:u8 :u16 :u32 :u64 :u128 :usize
   :i8 :i16 :i32 :i64 :i128 :isize))

(define inttype-width ((it inttype-p))
  :returns (w posp :rule-classes :type-prescription)
  ;; The model fixes a 64-bit target: usize/isize are 64 bits wide (the
  ;; importer checks the target's pointer size).
  (case (inttype-fix it)
    ((:u8 :i8) 8)
    ((:u16 :i16) 16)
    ((:u32 :i32) 32)
    ((:u64 :i64 :usize :isize) 64)
    (otherwise 128)))

(define inttype-signedp ((it inttype-p))
  :returns (b booleanp)
  (if (member-eq (inttype-fix it) '(:i8 :i16 :i32 :i64 :i128 :isize)) t nil))

(define inttype-min ((it inttype-p))
  :returns (m integerp :rule-classes :type-prescription)
  (case (inttype-fix it)
    (:i8 -128)
    (:i16 -32768)
    (:i32 -2147483648)
    ((:i64 :isize) -9223372036854775808)
    (:i128 -170141183460469231731687303715884105728)
    (otherwise 0)))

(define inttype-max ((it inttype-p))
  :returns (m integerp :rule-classes :type-prescription)
  (case (inttype-fix it)
    (:u8 255)
    (:u16 65535)
    (:u32 4294967295)
    ((:u64 :usize) 18446744073709551615)
    (:u128 340282366920938463463374607431768211455)
    (:i8 127)
    (:i16 32767)
    (:i32 2147483647)
    ((:i64 :isize) 9223372036854775807)
    (otherwise 170141183460469231731687303715884105727)))

(define int-in-range-p ((it inttype-p) (v integerp))
  :returns (b booleanp)
  (and (<= (inttype-min it) (lifix v))
       (<= (lifix v) (inttype-max it))))

(define int-wrap ((it inttype-p) (v integerp))
  :returns (r integerp :rule-classes :type-prescription)
  ;; Two's-complement wrap-around of v into the range of it.
  (if (inttype-signedp it)
      (logext (inttype-width it) (lifix v))
    (loghead (inttype-width it) (lifix v))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Types (only what the semantics consults: generic arguments of calls, cast
;; targets, and the element types of standard-library models).

(fty::deftypes ty
  (fty::deftagsum ty
    (:int ((it inttype-p)))
    (:bool ())
    (:char ())
    (:str ())
    (:never ())
    (:tuple ((elems ty-list)))
    (:adt ((id natp) (args ty-list)))
    (:array ((elem ty) (len maybe-natp)))
    (:slice ((elem ty)))
    (:ref ((target ty) (mut booleanp)))
    (:rawptr ((target ty) (mut booleanp)))
    (:param ((index natp)))
    (:other ()))
  (fty::deflist ty-list :elt-type ty :true-listp t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constants

(fty::deftypes constant
  (fty::deftagsum constant
    (:int ((it inttype-p) (v integerp)))
    (:bool ((b booleanp)))
    (:adt ((variant maybe-natp) (fields constant-list))) ; unit is (:adt nil nil)
    (:str ((s stringp)))
    (:other ()))
  (fty::deflist constant-list :elt-type constant :true-listp t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Places, projections, and operands

(fty::deftypes place
  (fty::deftagsum place
    (:local ((index natp)))
    (:global ((id natp)))
    (:proj ((base place) (elem projelem))))
  (fty::deftagsum projelem
    (:deref ())
    ;; variant is nil for a struct or tuple field, n for a field of variant n
    (:field ((variant maybe-natp) (index natp)))
    (:index ((offset operand) (from-end booleanp)))
    (:ptr-metadata ()))
  (fty::deftagsum operand
    (:copy ((place place)))
    (:move ((place place)))
    (:const ((c constant)))
    (:read ((place place))))
  (fty::deflist operand-list :elt-type operand :true-listp t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Rvalues

(std::defenum binop-name-p
  (:add :sub :mul :div :rem :bitxor :bitand :bitor :shl :shr
   :eq :ne :lt :le :gt :ge))

;; How an arithmetic operator treats overflow: :wrap (wrap around), :panic
;; (overflow-checked: overflow panics), or :ub (overflow is undefined
;; behavior); comparisons and bitwise operators ignore it.
(std::defenum overflow-mode-p (:wrap :panic :ub))

(fty::defprod binop
  ((name binop-name-p)
   (mode overflow-mode-p)))

(fty::deftagsum unop
  (:not ())
  (:neg ((mode overflow-mode-p)))
  (:cast-int ((target inttype-p)))     ; integer-to-integer `as' cast
  (:cast-bool-int ((target inttype-p)))
  (:unsize ())                        ; &[T; N] -> &[T]
  (:other-cast ()))

(fty::deftagsum aggkind
  ;; Structs, tuples (including unit), and enum variants.
  (:adt ((type-id natp) (variant maybe-natp)))
  (:array ()))

(std::defenum refkind-p (:shared :mut :two-phase-mut :raw-const :raw-mut))

(fty::deftagsum rvalue
  (:use ((op operand)))
  (:ref ((place place) (kind refkind-p)))
  (:rawptr ((place place) (kind refkind-p)))
  (:binop ((op binop) (a operand) (b operand)))
  (:unop ((op unop) (a operand)))
  (:discriminant ((place place)))
  (:aggregate ((kind aggkind) (ops operand-list)))
  (:repeat ((op operand) (count natp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Statements

(fty::deftagsum statement
  (:assign ((place place) (rv rvalue)))
  (:storage-live ((local natp)))
  (:storage-dead ((local natp)))
  (:nop ()))

(fty::deflist statement-list :elt-type statement :true-listp t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Terminators

;; A switch branch: the scrutinee's value (an integer or boolean constant)
;; and the target block.
(fty::defprod switch-branch
  ((value constant)
   (target natp)))

(fty::deflist switch-branch-list :elt-type switch-branch :true-listp t)

;; The function a Call invokes: a function of the crate (by declaration id),
;; or a modeled standard-library function.  For the latter the importer's
;; classifier has chosen the model per call site (from the declaration's path
;; and the call's generic arguments) and recorded the types the model needs.
(fty::deftagsum callee
  (:crate ((id natp) (name stringp)))
  (:std ((model symbolp) (tys ty-list) (name stringp))))

(fty::deftagsum terminator
  (:goto ((target natp)))
  (:switch ((discr operand) (branches switch-branch-list) (otherwise natp)))
  (:call ((callee callee) (args operand-list) (dest place) (target maybe-natp)))
  (:assert ((cond operand) (expected booleanp) (target natp) (msg stringp)))
  (:return ())
  (:unreachable ((msg stringp)))
  (:abort ((msg stringp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Bodies, functions, globals, programs

(fty::defprod bblock
  ((stmts statement-list)
   (term terminator)))

(fty::deflist bblock-list :elt-type bblock :true-listp t)

(fty::defprod body
  ((arg-count natp)
   (local-count natp)   ; includes the return place _0 and the arguments
   (blocks bblock-list)))

(fty::defprod fundecl
  ((name stringp)
   (body body)))

(fty::defalist fundecl-alist :key-type natp :val-type fundecl :true-listp t)

(fty::deftagsum globaldef
  ;; A global whose value is computed by running an initializer body (a
  ;; crate function), or a literal constant.
  (:init ((fn natp)))
  (:const ((c constant))))

(fty::defalist globaldef-alist :key-type natp :val-type globaldef :true-listp t)

(fty::defprod program
  ((crate stringp)
   (funs fundecl-alist)
   (globals globaldef-alist)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lookup

(define fundecl-alist-lookup ((id natp) (al fundecl-alist-p))
  :returns (f (iff (fundecl-p f) f))
  (cond ((atom al) nil)
        ((and (consp (car al)) (equal (nfix (caar al)) (lnfix id)))
         (fundecl-fix (cdar al)))
        (t (fundecl-alist-lookup id (cdr al)))))

(define program-lookup-fun ((id natp) (prog program-p))
  :returns (f (iff (fundecl-p f) f))
  (fundecl-alist-lookup id (program->funs prog)))

(define fundecl-alist-find-name ((name stringp) (funs fundecl-alist-p))
  :returns (id maybe-natp :rule-classes :type-prescription)
  (cond ((atom funs) nil)
        ((and (consp (car funs))
              (equal (fundecl->name (cdar funs)) (str-fix name)))
         (nfix (caar funs)))
        (t (fundecl-alist-find-name name (cdr funs)))))

(define program-find-fun ((name stringp) (prog program-p))
  :returns (id maybe-natp :rule-classes :type-prescription)
  (fundecl-alist-find-name name (program->funs prog)))

(define globaldef-alist-lookup ((id natp) (al globaldef-alist-p))
  :returns (g (iff (globaldef-p g) g))
  (cond ((atom al) nil)
        ((and (consp (car al)) (equal (nfix (caar al)) (lnfix id)))
         (globaldef-fix (cdar al)))
        (t (globaldef-alist-lookup id (cdr al)))))

(define program-lookup-global ((id natp) (prog program-p))
  :returns (g (iff (globaldef-p g) g))
  (globaldef-alist-lookup id (program->globals prog)))

(define bblock-list-nth ((n natp) (blocks bblock-list-p))
  :returns (blk (iff (bblock-p blk) blk))
  (cond ((atom blocks) nil)
        ((zp n) (bblock-fix (car blocks)))
        (t (bblock-list-nth (1- n) (cdr blocks)))))

(define body-block ((n natp) (b body-p))
  :returns (blk (iff (bblock-p blk) blk))
  (bblock-list-nth n (body->blocks b)))
