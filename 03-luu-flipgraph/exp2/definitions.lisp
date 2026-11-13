;; defs.lisp -- definitions for the luu-flipgraph targets (ACL2 Workshop 2026,
;; Luu, Medley, Manolios: the matrix multiplication flip graph over F2).
;;
;; Every define / defun-sk below is copied verbatim from the authors' books
;; (workshops/2026/luu-medley-manolios/); the comment above each gives the
;; source file:line.  The "///" sections (theorems) are removed.  Only the
;; definitions needed by the target statements (transitively) are kept.  The
;; local events are lemmas used only to admit the definitions (guard
;; verification); most are the authors' own lemmas, copied verbatim.  The one
;; non-author definition is flip-plus-reachablep (marked below).

(in-package "ACL2")

;;; ===== from luu-medley-manolios/bits.lisp =====
;;; luu-medley-manolios/bits.lisp, lines 3-3
(include-book "kestrel/bv/bitxor" :dir :system)
;;; luu-medley-manolios/bits.lisp, lines 4-4
(include-book "kestrel/bv/bitand" :dir :system)
;;; luu-medley-manolios/bits.lisp, lines 5-5
(include-book "std/util/define" :dir :system)
;;; luu-medley-manolios/bits.lisp, lines 6-6
(include-book "std/util/defrule" :dir :system)
;;; luu-medley-manolios/bits.lisp, lines 7-7
(include-book "std/lists/repeat" :dir :system)
;;; luu-medley-manolios/bits.lisp, lines 8-8
(include-book "std/basic/inductions" :dir :system)
;;; ===== from luu-medley-manolios/bags.lisp =====
;;; luu-medley-manolios/bags.lisp, lines 4-4
(include-book "std/obags/top" :dir :system)

;;; ===== from luu-medley-manolios/bits.lisp =====
;;; luu-medley-manolios/bits.lisp, lines 10-10
(local (include-book "std/lists/append" :dir :system))
;;; ===== from luu-medley-manolios/entry.lisp =====
;;; luu-medley-manolios/entry.lisp, lines 5-5
(local (include-book "std/lists/nth" :dir :system))
;;; ===== from luu-medley-manolios/bits.lisp =====
;;; luu-medley-manolios/bits.lisp, lines 11-11
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; bits.lisp:15
;;; luu-medley-manolios/bits.lisp, lines 15-35 (the /// section is removed)
(define bit-list-p (x)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (bitp (car x))
         (bit-list-p (cdr x)))))

;; bits.lisp:37
;;; luu-medley-manolios/bits.lisp, lines 37-89 (the /// section is removed)
(define bit-listnp (x (n natp))
  :returns (yes/no booleanp)
  (if (zp n)
      (null x)
    (and (consp x)
         (bitp (car x))
         (bit-listnp (cdr x) (1- n)))))

;; bits.lisp:91
;;; luu-medley-manolios/bits.lisp, lines 91-107 (the /// section is removed)
(define bit-listn0 ((n natp))
  :returns (r bit-list-p
              :hints (("Goal" :in-theory (enable repeat))))
  (repeat n 0))

;; bits.lisp:132
;;; luu-medley-manolios/bits.lisp, lines 132-233 (the /// section is removed)
(define bit-list-add ((x bit-list-p) (y bit-list-p))
  :returns (z bit-list-p)
  (if (and (consp x) (consp y))
      (cons (bitxor (car x) (car y))
            (bit-list-add (cdr x) (cdr y)))
    nil))

;; bits.lisp:237
;;; luu-medley-manolios/bits.lisp, lines 237-274 (the /// section is removed)
(define bit-list-scale ((b bitp) (x bit-list-p))
  :returns (z bit-list-p)
  (if (atom x)
      nil
    (cons (bitand b (car x))
          (bit-list-scale b (cdr x)))))

;; bits.lisp:276
;;; luu-medley-manolios/bits.lisp, lines 276-308 (the /// section is removed)
(define bit-list-outer ((u bit-list-p) (v bit-list-p))
  :returns (z bit-list-p)
  (if (atom u)
      nil
    (append (bit-list-scale (car u) v)
            (bit-list-outer (cdr u) v))))

;; bits.lisp:372
;;; luu-medley-manolios/bits.lisp, lines 372-378
(define bit-list-listp (a)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom a)
      (null a)
    (and (bit-list-p (car a))
         (bit-list-listp (cdr a)))))

;; bits.lisp:380
;;; luu-medley-manolios/bits.lisp, lines 380-398 (the /// section is removed)
(define bit-matp (a (m natp) (n natp))
  :returns (yes/no booleanp)
  :measure (nfix m)
  (if (zp m)
      (null a)
    (and (consp a)
         (bit-listnp (car a) n)
         (bit-matp (cdr a) (1- m) n))))

;; Local, from the /// sections of bit-listnp and bit-matp (bits.lisp).
;;; luu-medley-manolios/bits.lisp, lines 46-50 (the authors' statement with a new proof, made local)
(local
 (defrule bit-list-p-when-bit-listnp
   (implies (bit-listnp x n)
            (bit-list-p x))
   :enable (bit-listnp bit-list-p)
   :rule-classes (:rewrite :forward-chaining)))

;;; luu-medley-manolios/bits.lisp, lines 390-393 (the authors' statement with a new proof, made local)
(local
 (defrule bit-list-listp-when-bit-matp
   (implies (bit-matp a m n)
            (bit-list-listp a))
   :enable bit-matp
   :rule-classes (:rewrite :forward-chaining)))

;; bits.lisp:400
;;; luu-medley-manolios/bits.lisp, lines 400-408 (the /// section is removed)
(define bit-mat0 ((m natp) (n natp))
  :returns (a bit-list-listp
              :hints (("Goal" :in-theory (enable repeat))))
  (repeat m (bit-listn0 n)))

;; bits.lisp:412
;;; luu-medley-manolios/bits.lisp, lines 412-471 (the /// section is removed)
(define bit-mat-add ((a bit-list-listp) (b bit-list-listp))
  :returns (c bit-list-listp)
  (if (and (consp a) (consp b))
      (cons (bit-list-add (car a) (car b))
            (bit-mat-add (cdr a) (cdr b)))
    nil))

;; bits.lisp:475
;;; luu-medley-manolios/bits.lisp, lines 475-528 (the /// section is removed)
(define mat-flat ((a bit-list-listp))
  :returns (l bit-list-p :hyp (bit-list-listp a))
  (if (atom a)
      nil
    (append (car a) (mat-flat (cdr a)))))

;; scheme.lisp:8
;;; ===== from luu-medley-manolios/scheme.lisp =====
;;; luu-medley-manolios/scheme.lisp, lines 8-15
(define mat-triplep (s)
  :enabled t
  :returns (yes/no booleanp)
  (and (true-listp s)
       (equal (len s) 3)
       (bit-list-listp (car s))
       (bit-list-listp (cadr s))
       (bit-list-listp (caddr s))))

;; scheme.lisp:17
;;; luu-medley-manolios/scheme.lisp, lines 17-20
(define summand ((a bit-list-listp) (b bit-list-listp) (c bit-list-listp))
  :enabled t
  :returns (s mat-triplep :hyp :guard)
  (list a b c))

;; scheme.lisp:22
;;; luu-medley-manolios/scheme.lisp, lines 22-25
(define summand-A ((s mat-triplep))
  :enabled t
  :returns (a bit-list-listp :hyp :guard)
  (car s))

;; scheme.lisp:27
;;; luu-medley-manolios/scheme.lisp, lines 27-30
(define summand-B ((s mat-triplep))
  :enabled t
  :returns (b bit-list-listp :hyp :guard)
  (cadr s))

;; scheme.lisp:32
;;; luu-medley-manolios/scheme.lisp, lines 32-35
(define summand-C ((s mat-triplep))
  :enabled t
  :returns (c bit-list-listp :hyp :guard)
  (caddr s))

;; scheme.lisp:37
;;; luu-medley-manolios/scheme.lisp, lines 37-42
(define summand0p ((s mat-triplep) (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (or (equal (summand-A s) (bit-mat0 n n))
      (equal (summand-B s) (bit-mat0 n n))
      (equal (summand-C s) (bit-mat0 n n))))

;; scheme.lisp:44
;;; luu-medley-manolios/scheme.lisp, lines 44-51
(define summandp (s (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (and (mat-triplep s)
       (bit-matp (car s) n n)
       (bit-matp (cadr s) n n)
       (bit-matp (caddr s) n n)
       (not (summand0p s n))))

;; scheme.lisp:58
;;; luu-medley-manolios/scheme.lisp, lines 58-91 (the /// section is removed)
(define summand-dimp (s (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (and (mat-triplep s)
       (bit-matp (car s) n n)
       (bit-matp (cadr s) n n)
       (bit-matp (caddr s) n n)))

;; scheme.lisp:93
;;; luu-medley-manolios/scheme.lisp, lines 93-99
(define summand-dim-listp (l (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (summand-dimp (car l) n)
         (summand-dim-listp (cdr l) n))))

;; scheme.lisp:101
;;; luu-medley-manolios/scheme.lisp, lines 101-152 (the /// section is removed)
(define summand-listp (x (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (summandp (car x) n)
         (summand-listp (cdr x) n))))

;; scheme.lisp:156
;;; luu-medley-manolios/scheme.lisp, lines 156-160
(define schemep (x (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (and (obag::bagp x)
       (summand-listp x n)))

;; scheme.lisp:169
;;; luu-medley-manolios/scheme.lisp, lines 169-171
(define pos-next ((p natp))
  :enabled t
  (case p (0 1) (1 2) (t 0)))

;; scheme.lisp:173
;;; luu-medley-manolios/scheme.lisp, lines 173-175
(define pos-prev ((p natp))
  :enabled t
  (case p (0 2) (1 0) (t 1)))

;; scheme.lisp:177
;;; luu-medley-manolios/scheme.lisp, lines 177-188 (the /// section is removed)
(define summand-get-pos ((s mat-triplep) p)
  :enabled t
  :returns (m bit-list-listp :hyp :guard)
  (case p
    (0 (car s))
    (1 (cadr s))
    (t (caddr s))))

;; scheme.lisp:190
;;; luu-medley-manolios/scheme.lisp, lines 190-202 (the /// section is removed)
(define summand-set-pos ((s mat-triplep) p (m bit-list-listp))
  :enabled t
  :returns (s1 mat-triplep :hyp :guard)
  (case p
    (0 (summand m (cadr s) (caddr s)))
    (1 (summand (car s) m (caddr s)))
    (t (summand (car s) (cadr s) m))))

;; scheme.lisp:204
;;; luu-medley-manolios/scheme.lisp, lines 204-210
(define mat-triple-listp (l)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (mat-triplep (car l))
         (mat-triple-listp (cdr l)))))

;; scheme.lisp:332
;;; luu-medley-manolios/scheme.lisp, lines 332-345 (the /// section is removed)
(define flip ((s1 mat-triplep) (s2 mat-triplep) (p natp))
  :enabled t
  :returns (l mat-triple-listp :hyp :guard)
  (let ((q (pos-next p))
        (r (pos-prev p)))
    (list (summand-set-pos s1 r (bit-mat-add (summand-get-pos s1 r)
                                             (summand-get-pos s2 r)))
          (summand-set-pos s2 q (bit-mat-add (summand-get-pos s2 q)
                                             (summand-get-pos s1 q))))))

;; scheme.lisp:352
;;; luu-medley-manolios/scheme.lisp, lines 352-362 (the /// section is removed)
(define plus ((target mat-triplep) (pivot mat-triplep) (p natp))
  :enabled t
  :returns (l mat-triple-listp :hyp :guard)
  (list (summand-set-pos target p (bit-mat-add (summand-get-pos target p)
                                               (summand-get-pos pivot p)))
        (summand-set-pos target p (summand-get-pos pivot p))))

;; scheme.lisp:367
;;; luu-medley-manolios/scheme.lisp, lines 367-367
(define move-kind ((move true-listp)) :enabled t (car move))

;; scheme.lisp:368
;;; luu-medley-manolios/scheme.lisp, lines 368-368
(define move-pos ((move true-listp)) :enabled t (cadr move))

;; scheme.lisp:369
;;; luu-medley-manolios/scheme.lisp, lines 369-369
(define move-s1 ((move true-listp)) :enabled t (caddr move))

;; scheme.lisp:370
;;; luu-medley-manolios/scheme.lisp, lines 370-370
(define move-s2 ((move true-listp)) :enabled t (cadddr move))

;; scheme.lisp:372
;;; luu-medley-manolios/scheme.lisp, lines 372-382
(define move-p (move)
  :enabled t
  :returns (yes/no booleanp)
  (and (true-listp move)
       (equal (len move) 4)
       (or (eq (move-kind move) :flip)
           (eq (move-kind move) :plus))
       (natp (move-pos move))
       (< (move-pos move) 3)
       (mat-triplep (move-s1 move))
       (mat-triplep (move-s2 move))))

;; scheme.lisp:384
;;; luu-medley-manolios/scheme.lisp, lines 384-390
(define move-list-p (moves)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom moves)
      (null moves)
    (and (move-p (car moves))
         (move-list-p (cdr moves)))))

;; scheme.lisp:392
;;; luu-medley-manolios/scheme.lisp, lines 392-416 (the /// section is removed)
(define insert-all-nonzero ((l mat-triple-listp) (s obag::bagp) (n natp))
  :enabled t
  :returns (s1 obag::bagp :hyp (obag::bagp s))
  (if (atom l)
      s
    (if (summand0p (car l) n)
        (insert-all-nonzero (cdr l) s n)
      (obag::insert (car l) (insert-all-nonzero (cdr l) s n)))))

;; scheme.lisp:418
;;; luu-medley-manolios/scheme.lisp, lines 418-436
(define move-validp ((move move-p) (sch obag::bagp))
  :enabled t
  :returns (yes/no booleanp)
  (case (move-kind move)
    (:flip (and (natp (move-pos move))
                (< (move-pos move) 3)
                (if (equal (move-s1 move) (move-s2 move))
                    (<= 2 (obag::occs (move-s1 move) sch))
                  (and (obag::in (move-s1 move) sch)
                       (obag::in (move-s2 move) sch)
                       (equal (summand-get-pos (move-s1 move) (move-pos move))
                              (summand-get-pos (move-s2 move) (move-pos move)))))))
    (:plus (and (natp (move-pos move))
                (< (move-pos move) 3)
                (if (equal (move-s1 move) (move-s2 move))
                    (<= 2 (obag::occs (move-s1 move) sch))
                  (and (obag::in (move-s1 move) sch)
                       (obag::in (move-s2 move) sch)))))
    (t nil)))

;; scheme.lisp:440
;;; luu-medley-manolios/scheme.lisp, lines 440-471 (the /// section is removed)
(define apply-move ((move move-p) (sch obag::bagp) (n natp))
  :returns (sch1 obag::bagp :hyp (obag::bagp sch))
  (case (move-kind move)
    (:plus (insert-all-nonzero (plus (move-s1 move) (move-s2 move) (move-pos move))
                               (obag::delete (move-s1 move) sch)
                               n))
    (:flip (insert-all-nonzero (flip (move-s1 move) (move-s2 move) (move-pos move))
                               (obag::delete (move-s1 move)
                                             (obag::delete (move-s2 move) sch))
                               n))
    (t sch)))

;; scheme.lisp:473
;;; luu-medley-manolios/scheme.lisp, lines 473-477
(define apply-moves ((moves move-list-p) (sch obag::bagp) (n natp))
  :returns (sch1 obag::bagp :hyp (obag::bagp sch))
  (if (atom moves)
      sch
    (apply-moves (cdr moves) (apply-move (car moves) sch n) n)))

;; scheme.lisp:479
;;; luu-medley-manolios/scheme.lisp, lines 479-499 (the /// section is removed)
(define path-validp ((moves move-list-p) (sch obag::bagp) (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (if (atom moves)
      t
    (and (move-validp (car moves) sch)
         (path-validp (cdr moves) (apply-move (car moves) sch n) n))))

;; NOT in the authors' books: the existential form of reachability used to
;; state the main theorem without naming the authors' path construction.
;; sch2 is reachable from sch by a valid sequence of flip/plus moves.
;;; not from the authors' sources
(defun-sk flip-plus-reachablep (sch sch2 n)
  (exists (moves)
          (and (path-validp moves sch n)
               (equal (apply-moves moves sch n) sch2))))

;; tensor.lisp:9
;;; ===== from luu-medley-manolios/tensor.lisp =====
;;; luu-medley-manolios/tensor.lisp, lines 9-64 (the /// section is removed)
(define tensor ((a bit-list-listp) (b bit-list-listp) (c bit-list-listp))
  :returns (tt bit-list-p :hyp :guard)
  (bit-list-outer (mat-flat a)
                  (bit-list-outer (mat-flat b) (mat-flat c))))

;; tensor.lisp:69
;;; luu-medley-manolios/tensor.lisp, lines 69-76 (the /// section is removed)
(define summand-tensor ((s mat-triplep))
  :enabled t
  (tensor (car s) (cadr s) (caddr s)))

;; tensor.lisp:136
;;; luu-medley-manolios/tensor.lisp, lines 136-158 (the /// section is removed)
(define scheme-sum ((l mat-triple-listp) (n natp))
  :returns (tt bit-list-p)
  (if (atom l)
      (bit-listn0 (* n n n n n n))
    (bit-list-add (summand-tensor (car l))
                  (scheme-sum (cdr l) n))))

;; mm-tensor.lisp:21
;;; ===== from luu-medley-manolios/mm-tensor.lisp =====
;;; luu-medley-manolios/mm-tensor.lisp, lines 21-32 (the /// section is removed)
(define bit-unit-list ((j natp) (n natp))
  :returns (l bit-list-p)
  (if (zp n)
      nil
    (if (zp j)
        (cons 1 (bit-listn0 (1- n)))
      (cons 0 (bit-unit-list (1- j) (1- n))))))

;; mm-tensor.lisp:34
;;; luu-medley-manolios/mm-tensor.lisp, lines 34-51 (the /// section is removed)
(define bit-mat-unit ((i natp) (j natp) (m natp) (n natp))
  :returns (a bit-list-listp)
  (if (zp m)
      nil
    (if (zp i)
        (cons (bit-unit-list j n) (bit-mat0 (1- m) n))
      (cons (bit-listn0 n) (bit-mat-unit (1- i) j (1- m) n)))))

;; mm-tensor.lisp:55
;;; luu-medley-manolios/mm-tensor.lisp, lines 55-77 (the /// section is removed)
(define mm-tensor-3 ((i natp) (j natp) (k natp) (n natp))
  :returns (tt bit-list-p)
  :verify-guards :after-returns
  (if (zp k)
      (bit-listn0 (* n n n n n n))
    (bit-list-add
     (tensor (bit-mat-unit i j n n)
             (bit-mat-unit j (1- k) n n)
             (bit-mat-unit i (1- k) n n))
     (mm-tensor-3 i j (1- k) n))))

;; mm-tensor.lisp:79
;;; luu-medley-manolios/mm-tensor.lisp, lines 79-98 (the /// section is removed)
(define mm-tensor-2 ((i natp) (j natp) (n natp))
  :returns (tt bit-list-p)
  :verify-guards :after-returns
  (if (zp j)
      (bit-listn0 (* n n n n n n))
    (bit-list-add (mm-tensor-3 i (1- j) n n)
                  (mm-tensor-2 i (1- j) n))))

;; mm-tensor.lisp:100
;;; luu-medley-manolios/mm-tensor.lisp, lines 100-119 (the /// section is removed)
(define mm-tensor-1 ((i natp) (n natp))
  :returns (tt bit-list-p)
  :verify-guards :after-returns
  (if (zp i)
      (bit-listn0 (* n n n n n n))
    (bit-list-add (mm-tensor-2 (1- i) n n)
                  (mm-tensor-1 (1- i) n))))

;; mm-tensor.lisp:121
;;; luu-medley-manolios/mm-tensor.lisp, lines 121-136 (the /// section is removed)
(define mm-tensor ((n natp))
  :returns (tt bit-list-p)
  (mm-tensor-1 n n))

;; Local, for the guard of correct-schemep.
;;; not from the authors' sources
(local
 (defrule mat-triple-listp-when-summand-listp
   (implies (summand-listp x n)
            (mat-triple-listp x))))

;; mm-tensor.lisp:147
;;; luu-medley-manolios/mm-tensor.lisp, lines 147-150
(define correct-schemep (sch (n natp))
  :returns (yes/no booleanp)
  (and (schemep sch n)
       (equal (scheme-sum sch n) (mm-tensor n))))

;; entry.lisp:110
;;; ===== from luu-medley-manolios/entry.lisp =====
;;; luu-medley-manolios/entry.lisp, lines 110-112
(define mat-entry ((i natp) (j natp) (a bit-list-listp))
  :enabled t
  (nth j (nth i a)))

;; Local, for guard proofs that read matrix entries.
;;; not from the authors' sources
(local
 (defun nth-dim-induct (x j n)
   (if (or (zp j) (atom x))
       (list x n)
     (nth-dim-induct (cdr x) (1- j) (1- n)))))

;;; not from the authors' sources
(local
 (defrule bitp-of-nth-when-bit-listnp-local
   (implies (and (bit-listnp x n) (natp n) (natp j) (< j n))
            (bitp (nth j x)))
   :induct (nth-dim-induct x j n)
   :enable bit-listnp))

;;; not from the authors' sources
(local
 (defrule bit-listnp-of-nth-when-bit-matp-local
   (implies (and (bit-matp x m n) (natp m) (natp i) (< i m))
            (bit-listnp (nth i x) n))
   :induct (nth-dim-induct x i m)
   :enable bit-matp))

;;; ===== from luu-medley-manolios/mmt.lisp =====
;;; luu-medley-manolios/mmt.lisp, lines 136-144 (the authors' statement with a new proof, made local)
(local
 (defruled integerp-of-mat-entry
   (implies (and (bit-matp x m n)
                 (natp m) (natp n)
                 (natp i) (natp j)
                 (< i m) (< j n))
            (integerp (mat-entry i j x)))
   :use ((:instance bitp-of-nth-when-bit-listnp-local (x (nth i x))))))

;;; luu-medley-manolios/mmt.lisp, lines 123-131 (the authors' statement with a new proof, made local)
(local
 (defrule bitp-of-mat-entry
   (implies (and (bit-matp x m n)
                 (natp m) (natp n)
                 (natp i) (natp j)
                 (< i m) (< j n))
            (bitp (mat-entry i j x)))
   :use ((:instance bitp-of-nth-when-bit-listnp-local (x (nth i x))))))

;; adequacy.lisp:69
;;; ===== from luu-medley-manolios/adequacy.lisp =====
;;; luu-medley-manolios/adequacy.lisp, lines 69-80 (the /// section is removed)
(define bit-mat-scale ((b bitp) (a bit-list-listp))
  :returns (c bit-list-listp)
  (if (atom a)
      nil
    (cons (bit-list-scale b (car a))
          (bit-mat-scale b (cdr a)))))

;; adequacy.lisp:109
;;; luu-medley-manolios/adequacy.lisp, lines 109-119
(define mat-mul-entry ((d bit-list-listp) (f bit-list-listp)
                       (k natp) (l natp) (h natp) (n natp))
  :guard (and (bit-matp d n n) (bit-matp f n n) (< k n) (< l n) (<= h n))
  :guard-hints (("Goal" :in-theory (e/d (integerp-of-mat-entry) (mat-entry))
                        :do-not-induct t))
  :returns (b bitp)
  :verify-guards :after-returns
  (if (zp h)
      0
    (bitxor (bitand (mat-entry k (1- h) d) (mat-entry (1- h) l f))
            (mat-mul-entry d f k l (1- h) n))))

;; adequacy.lisp:124
;;; luu-medley-manolios/adequacy.lisp, lines 124-136 (the /// section is removed)
(define bit-mat-mul-row ((d bit-list-listp) (f bit-list-listp)
                         (k natp) (c natp) (n natp))
  :guard (and (bit-matp d n n) (bit-matp f n n) (< k n) (<= c n))
  :returns (r bit-list-p)
  :verify-guards :after-returns
  (if (zp c)
      nil
    (cons (mat-mul-entry d f k (- n c) n n)
          (bit-mat-mul-row d f k (1- c) n))))

;; adequacy.lisp:138
;;; luu-medley-manolios/adequacy.lisp, lines 138-150 (the /// section is removed)
(define bit-mat-mul-rows ((d bit-list-listp) (f bit-list-listp)
                          (c natp) (n natp))
  :guard (and (bit-matp d n n) (bit-matp f n n) (<= c n))
  :returns (a bit-list-listp)
  :verify-guards :after-returns
  (if (zp c)
      nil
    (cons (bit-mat-mul-row d f (- n c) n n)
          (bit-mat-mul-rows d f (1- c) n))))

;; adequacy.lisp:152
;;; luu-medley-manolios/adequacy.lisp, lines 152-158 (the /// section is removed)
(define bit-mat-mul ((d bit-list-listp) (f bit-list-listp) (n natp))
  :guard (and (bit-matp d n n) (bit-matp f n n))
  :returns (a bit-list-listp)
  (bit-mat-mul-rows d f n n))

;; matmul-expr.lisp:69
;;; ===== from luu-medley-manolios/matmul-expr.lisp =====
;;; luu-medley-manolios/matmul-expr.lisp, lines 69-79
(define lformp (e (n natp))
  :returns (yes/no booleanp)
  (and (consp e)
       (true-listp e)
       (equal (len e) 3)
       (case (car e)
         (:var (and (natp (cadr e)) (natp (caddr e))
                    (< (cadr e) n) (< (caddr e) n)))
         (:add (and (lformp (cadr e) n) (lformp (caddr e) n)))
         (:scale (and (bitp (cadr e)) (lformp (caddr e) n)))
         (t nil))))

;; matmul-expr.lisp:81
;;; luu-medley-manolios/matmul-expr.lisp, lines 81-99 (the /// section is removed)
(define eval-lform (e (m bit-list-listp) (n natp))
  :guard (and (lformp e n) (bit-matp m n n))
  :guard-hints (("Goal" :in-theory (e/d (lformp integerp-of-mat-entry) (mat-entry))))
  :returns (b bitp :hyp :guard
              :hints (("Goal" :in-theory (e/d (lformp) (mat-entry bitp)))))
  :verify-guards :after-returns
  (case (car e)
    (:var (mat-entry (cadr e) (caddr e) m))
    (:add (bitxor (eval-lform (cadr e) m n) (eval-lform (caddr e) m n)))
    (:scale (bitand (cadr e) (eval-lform (caddr e) m n)))
    (t 0)))

;; Local, from the /// section of eval-lform (matmul-expr.lisp:95), for the
;; guard of prod-value.
;;; luu-medley-manolios/matmul-expr.lisp, lines 95-99 (wrapped in local)
(local
 (defruled integerp-of-eval-lform
   (implies (and (lformp e n) (bit-matp m n n) (natp n))
            (integerp (eval-lform e m n)))
   :use bitp-of-eval-lform
   :disable bitp-of-eval-lform))

;; matmul-expr.lisp:101
;;; luu-medley-manolios/matmul-expr.lisp, lines 101-115 (the /// section is removed)
(define lform-mat (e (n natp))
  :guard (lformp e n)
  :guard-hints (("Goal" :in-theory (enable lformp)))
  :returns (a bit-list-listp)
  :verify-guards :after-returns
  (case (car e)
    (:var (bit-mat-unit (cadr e) (caddr e) n n))
    (:add (bit-mat-add (lform-mat (cadr e) n) (lform-mat (caddr e) n)))
    (:scale (bit-mat-scale (cadr e) (lform-mat (caddr e) n)))
    (t (bit-mat0 n n))))

;; matmul-expr.lisp:119
;;; luu-medley-manolios/matmul-expr.lisp, lines 119-125
(define prodp (p (n natp))
  :returns (yes/no booleanp)
  (and (true-listp p)
       (equal (len p) 3)
       (eq (car p) :mul)
       (lformp (cadr p) n)
       (lformp (caddr p) n)))

;; matmul-expr.lisp:127
;;; luu-medley-manolios/matmul-expr.lisp, lines 127-142 (the /// section is removed)
(define prod-listp (l (n natp))
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (prodp (car l) n)
         (prod-listp (cdr l) n))))

;; Local copies of lemmas from the /// section of prod-listp (matmul-expr.lisp),
;; proved, as there, with prod-listp enabled.
;;; local encapsulate with verbatim copies of the authors' /// lemmas (see the comment above)
(local
 (encapsulate ()
  (local (in-theory (enable prod-listp)))

;; matmul-expr.lisp:134
(defrule true-listp-when-prod-listp
    (implies (prod-listp l n)
             (true-listp l))
    :rule-classes (:rewrite :forward-chaining))

;; matmul-expr.lisp:138
(defrule prodp-of-nth-when-prod-listp
    (implies (and (prod-listp l n)
                  (< (nfix i) (len l)))
             (prodp (nth i l) n))
    :induct (cdr-dec-induct l i))

))

;; matmul-expr.lisp:144
;;; luu-medley-manolios/matmul-expr.lisp, lines 144-155 (the /// section is removed)
(define index-listp (l (r natp))
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (natp (car l))
         (< (car l) r)
         (index-listp (cdr l) r))))

;; Local copies of lemmas from the /// section of index-listp (matmul-expr.lisp),
;; proved, as there, with index-listp enabled.
;;; local encapsulate with verbatim copies of the authors' /// lemmas (see the comment above)
(local
 (encapsulate ()
  (local (in-theory (enable index-listp)))

;; matmul-expr.lisp:152
(defrule nat-listp-when-index-listp
    (implies (index-listp l r)
             (nat-listp l))
    :rule-classes (:rewrite :forward-chaining))

))

;; matmul-expr.lisp:157
;;; luu-medley-manolios/matmul-expr.lisp, lines 157-163
(define idx-rowp (x)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (nat-listp (car x))
         (idx-rowp (cdr x)))))

;; matmul-expr.lisp:165
;;; luu-medley-manolios/matmul-expr.lisp, lines 165-171
(define idx-tablep (x)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (idx-rowp (car x))
         (idx-tablep (cdr x)))))

;; matmul-expr.lisp:173
;;; luu-medley-manolios/matmul-expr.lisp, lines 173-192 (the /// section is removed)
(define outs-rowp (row (r natp) (n natp))
  :returns (yes/no booleanp)
  (if (zp n)
      (null row)
    (and (consp row)
         (index-listp (car row) r)
         (outs-rowp (cdr row) r (1- n)))))

;; Local copies of lemmas from the /// section of outs-rowp (matmul-expr.lisp),
;; proved, as there, with outs-rowp enabled.
;;; local encapsulate with verbatim copies of the authors' /// lemmas (see the comment above)
(local
 (encapsulate ()
  (local (in-theory (enable outs-rowp)))

;; matmul-expr.lisp:181
(defrule idx-rowp-when-outs-rowp
    (implies (outs-rowp row r n)
             (idx-rowp row))
    :rule-classes (:rewrite :forward-chaining))

;; matmul-expr.lisp:185
(defrule true-listp-when-outs-rowp
    (implies (outs-rowp row r n)
             (true-listp row))
    :rule-classes (:rewrite :forward-chaining))

;; matmul-expr.lisp:189
(defruled len-of-outs-rowp
    (implies (and (outs-rowp row r n)
                  (natp n))
             (equal (len row) n)))

))

;; matmul-expr.lisp:194
;;; luu-medley-manolios/matmul-expr.lisp, lines 194-213 (the /// section is removed)
(define outs-rowsp (outs (r natp) (m natp) (n natp))
  :returns (yes/no booleanp)
  (if (zp m)
      (null outs)
    (and (consp outs)
         (outs-rowp (car outs) r n)
         (outs-rowsp (cdr outs) r (1- m) n))))

;; Local copies of lemmas from the /// section of outs-rowsp (matmul-expr.lisp),
;; proved, as there, with outs-rowsp enabled.
;;; local encapsulate with verbatim copies of the authors' /// lemmas (see the comment above)
(local
 (encapsulate ()
  (local (in-theory (enable outs-rowsp)))

;; matmul-expr.lisp:202
(defrule idx-tablep-when-outs-rowsp
    (implies (outs-rowsp outs r m n)
             (idx-tablep outs))
    :rule-classes (:rewrite :forward-chaining))

;; matmul-expr.lisp:206
(defrule true-listp-when-outs-rowsp
    (implies (outs-rowsp outs r m n)
             (true-listp outs))
    :rule-classes (:rewrite :forward-chaining))

;; matmul-expr.lisp:210
(defruled len-of-outs-rowsp
    (implies (and (outs-rowsp outs r m n)
                  (natp m))
             (equal (len outs) m)))

))

;; matmul-expr.lisp:215
;;; luu-medley-manolios/matmul-expr.lisp, lines 215-219
(define algop (alg (n natp))
  :returns (yes/no booleanp)
  (and (consp alg)
       (prod-listp (car alg) n)
       (outs-rowsp (cdr alg) (len (car alg)) n n)))

;; matmul-expr.lisp:224
;;; luu-medley-manolios/matmul-expr.lisp, lines 223-229
(local
 (defruled outs-rowp-of-nth-when-outs-rowsp-core
   (implies (and (outs-rowsp outs r (len outs) n)
                 (< (nfix k) (len outs)))
            (outs-rowp (nth k outs) r n))
   :induct (cdr-dec-induct outs k)
   :enable outs-rowsp))

;; matmul-expr.lisp:231
;;; luu-medley-manolios/matmul-expr.lisp, lines 231-238 (wrapped in local)
(local
 (defrule outs-rowp-of-nth-when-outs-rowsp
  (implies (and (outs-rowsp outs r m n)
                (natp m)
                (< (nfix k) m))
           (outs-rowp (nth k outs) r n))
  :do-not-induct t
  :use (outs-rowp-of-nth-when-outs-rowsp-core
        len-of-outs-rowsp)))

;; matmul-expr.lisp:241
;;; luu-medley-manolios/matmul-expr.lisp, lines 240-246
(local
 (defruled index-listp-of-nth-when-outs-rowp-core
   (implies (and (outs-rowp row r (len row))
                 (< (nfix l) (len row)))
            (index-listp (nth l row) r))
   :induct (cdr-dec-induct row l)
   :enable outs-rowp))

;; matmul-expr.lisp:248
;;; luu-medley-manolios/matmul-expr.lisp, lines 248-255 (wrapped in local)
(local
 (defrule index-listp-of-nth-when-outs-rowp
  (implies (and (outs-rowp row r n)
                (natp n)
                (< (nfix l) n))
           (index-listp (nth l row) r))
  :do-not-induct t
  :use (index-listp-of-nth-when-outs-rowp-core
        len-of-outs-rowp)))

;; matmul-expr.lisp:260
;;; luu-medley-manolios/matmul-expr.lisp, lines 260-268 (wrapped in local)
(local
 (defrule index-listp-of-nth-nth-when-outs-rowsp
  (implies (and (outs-rowsp outs r m n)
                (natp m) (natp n)
                (< (nfix k) m)
                (< (nfix l) n))
           (index-listp (nth l (nth k outs)) r))
  :do-not-induct t
  :use (outs-rowp-of-nth-when-outs-rowsp
        (:instance index-listp-of-nth-when-outs-rowp (row (nth k outs))))))

;; matmul-expr.lisp:272
;;; luu-medley-manolios/matmul-expr.lisp, lines 272-279 (wrapped in local)
(local
 (defrule true-listp-of-nth-when-outs-rowsp
  (implies (and (outs-rowsp outs r m n)
                (natp m)
                (< (nfix k) m))
           (true-listp (nth k outs)))
  :do-not-induct t
  :use (outs-rowp-of-nth-when-outs-rowsp)
  :disable (outs-rowp-of-nth-when-outs-rowsp)))

;; matmul-expr.lisp:281
;;; luu-medley-manolios/matmul-expr.lisp, lines 281-289 (wrapped in local)
(local
 (defrule nat-listp-of-nth-nth-when-outs-rowsp
  (implies (and (outs-rowsp outs r m n)
                (natp m) (natp n)
                (< (nfix k) m)
                (< (nfix l) n))
           (nat-listp (nth l (nth k outs))))
  :do-not-induct t
  :use (index-listp-of-nth-nth-when-outs-rowsp)
  :disable (index-listp-of-nth-nth-when-outs-rowsp)))

;; matmul-expr.lisp:293
;;; luu-medley-manolios/matmul-expr.lisp, lines 293-298
(define prod-value (p (d bit-list-listp) (f bit-list-listp) (n natp))
  :guard (and (prodp p n) (bit-matp d n n) (bit-matp f n n))
  :guard-hints (("Goal" :in-theory (enable prodp integerp-of-eval-lform)))
  :returns (b bitp)
  (bitand (eval-lform (cadr p) d n)
          (eval-lform (caddr p) f n)))

;; matmul-expr.lisp:300
;;; luu-medley-manolios/matmul-expr.lisp, lines 300-312
(define prods-xor ((idxs nat-listp) (prods true-listp)
                   (d bit-list-listp) (f bit-list-listp) (n natp))
  :guard (and (index-listp idxs (len prods))
              (prod-listp prods n)
              (bit-matp d n n)
              (bit-matp f n n))
  :guard-hints (("Goal" :in-theory (enable index-listp)))
  :returns (b bitp)
  :verify-guards :after-returns
  (if (atom idxs)
      0
    (bitxor (prod-value (nth (car idxs) prods) d f n)
            (prods-xor (cdr idxs) prods d f n))))

;; matmul-expr.lisp:314
;;; luu-medley-manolios/matmul-expr.lisp, lines 314-320
(define algo-entry (alg (d bit-list-listp) (f bit-list-listp)
                    (k natp) (l natp) (n natp))
  :guard (and (algop alg n) (bit-matp d n n) (bit-matp f n n)
              (< k n) (< l n))
  :guard-hints (("Goal" :in-theory (enable algop) :do-not-induct t))
  :returns (b bitp)
  (prods-xor (nth l (nth k (cdr alg))) (car alg) d f n))

;; matmul-expr.lisp:322
;;; luu-medley-manolios/matmul-expr.lisp, lines 322-334 (the /// section is removed)
(define eval-algo-row (alg (d bit-list-listp) (f bit-list-listp)
                       (k natp) (c natp) (n natp))
  :guard (and (algop alg n) (bit-matp d n n) (bit-matp f n n)
              (< k n) (<= c n))
  :returns (row bit-list-p)
  (if (zp c)
      nil
    (cons (algo-entry alg d f k (- n c) n)
          (eval-algo-row alg d f k (1- c) n))))

;; matmul-expr.lisp:336
;;; luu-medley-manolios/matmul-expr.lisp, lines 336-348 (the /// section is removed)
(define eval-algo-rows (alg (d bit-list-listp) (f bit-list-listp)
                        (c natp) (n natp))
  :guard (and (algop alg n) (bit-matp d n n) (bit-matp f n n)
              (<= c n))
  :returns (a bit-list-listp)
  (if (zp c)
      nil
    (cons (eval-algo-row alg d f (- n c) n n)
          (eval-algo-rows alg d f (1- c) n))))

;; matmul-expr.lisp:350
;;; luu-medley-manolios/matmul-expr.lisp, lines 350-356 (the /// section is removed)
(define eval-algo (alg (d bit-list-listp) (f bit-list-listp) (n natp))
  :guard (and (algop alg n) (bit-matp d n n) (bit-matp f n n))
  :returns (a bit-list-listp)
  (eval-algo-rows alg d f n n))

;; matmul-expr.lisp:360
;;; luu-medley-manolios/matmul-expr.lisp, lines 360-365
(define occ-parity ((r natp) (idxs nat-listp))
  :returns (b bitp)
  (if (atom idxs)
      0
    (bitxor (if (equal (car idxs) r) 1 0)
            (occ-parity r (cdr idxs)))))

;; matmul-expr.lisp:367
;;; luu-medley-manolios/matmul-expr.lisp, lines 367-378 (the /// section is removed)
(define c-mat-row ((r natp) (row idx-rowp))
  :returns (x bit-list-p)
  (if (atom row)
      nil
    (cons (occ-parity r (car row))
          (c-mat-row r (cdr row)))))

;; matmul-expr.lisp:380
;;; luu-medley-manolios/matmul-expr.lisp, lines 380-391 (the /// section is removed)
(define c-mat ((r natp) (outs idx-tablep))
  :returns (a bit-list-listp)
  (if (atom outs)
      nil
    (cons (c-mat-row r (car outs))
          (c-mat r (cdr outs)))))

;; matmul-expr.lisp:393
;;; luu-medley-manolios/matmul-expr.lisp, lines 393-412 (the /// section is removed)
(define triples-from ((prods true-listp) (outs idx-tablep) (r natp) (n natp))
  :guard (prod-listp prods n)
  :guard-hints (("Goal" :in-theory (enable prod-listp prodp)))
  :returns (l mat-triple-listp)
  (if (atom prods)
      nil
    (cons (list (lform-mat (cadr (car prods)) n)
                (lform-mat (caddr (car prods)) n)
                (c-mat r outs))
          (triples-from (cdr prods) outs (1+ r) n))))

;; matmul-expr.lisp:414
;;; luu-medley-manolios/matmul-expr.lisp, lines 414-423 (the /// section is removed)
(define algo-triples (alg (n natp))
  :guard (algop alg n)
  :guard-hints (("Goal" :in-theory (enable algop)))
  :returns (l mat-triple-listp)
  (triples-from (car alg) (cdr alg) 0 n))

;; matmul-expr.lisp:425
;;; luu-medley-manolios/matmul-expr.lisp, lines 425-433 (the /// section is removed)
(define algo-scheme (alg (n natp))
  :guard (algop alg n)
  :returns (sch obag::bagp)
  (insert-all-nonzero (algo-triples alg n) nil n))

;; algo-completeness.lisp:19
;;; ===== from luu-medley-manolios/algo-completeness.lisp =====
;;; luu-medley-manolios/algo-completeness.lisp, lines 19-24
(defun-sk algo-correctp (alg n)
  (forall (d f)
          (implies (and (bit-matp d n n)
                        (bit-matp f n n))
                   (equal (eval-algo alg d f n)
                          (bit-mat-mul d f n)))))

;; scheme-algo.lisp:64
;;; ===== from luu-medley-manolios/scheme-algo.lisp =====
;;; luu-medley-manolios/scheme-algo.lisp, lines 64-72
(define mat-lform-row ((a bit-list-listp) (i natp) (c natp) (n natp))
  :guard (and (bit-matp a n n) (< i n) (<= c n))
  :returns (e (lformp e n) :hyp :guard
              :hints (("Goal" :in-theory (enable lformp))))
  (if (zp c)
      '(:scale 0 (:var 0 0))
    (if (equal (mat-entry i (- n c) a) 1)
        (list :add (list :var i (- n c)) (mat-lform-row a i (1- c) n))
      (mat-lform-row a i (1- c) n))))

;; scheme-algo.lisp:74
;;; luu-medley-manolios/scheme-algo.lisp, lines 74-80
(define mat-lform-rows ((a bit-list-listp) (c natp) (n natp))
  :guard (and (bit-matp a n n) (<= c n) (< 0 n))
  :returns (e (lformp e n) :hyp :guard
              :hints (("Goal" :in-theory (enable lformp))))
  (if (zp c)
      '(:scale 0 (:var 0 0))
    (list :add (mat-lform-row a (- n c) n n) (mat-lform-rows a (1- c) n))))

;; scheme-algo.lisp:82
;;; luu-medley-manolios/scheme-algo.lisp, lines 82-85
(define mat-lform ((a bit-list-listp) (n natp))
  :guard (and (bit-matp a n n) (< 0 n))
  :returns (e (lformp e n) :hyp :guard)
  (mat-lform-rows a n n))

;; scheme-algo.lisp:91
;;; luu-medley-manolios/scheme-algo.lisp, lines 91-104 (the /// section is removed)
(define c-indices ((l mat-triple-listp) (k natp) (j natp) (r natp))
  :returns (idxs nat-listp :hyp (natp r))
  (if (atom l)
      nil
    (if (equal (mat-entry k j (caddr (car l))) 1)
        (cons r (c-indices (cdr l) k j (1+ r)))
      (c-indices (cdr l) k j (1+ r)))))

;; scheme-algo.lisp:106
;;; luu-medley-manolios/scheme-algo.lisp, lines 106-116 (the /// section is removed)
(define triples-outs-row ((l mat-triple-listp) (k natp) (c natp) (n natp))
  :guard (<= c n)
  :returns (row idx-rowp)
  (if (zp c)
      nil
    (cons (c-indices l k (- n c) 0)
          (triples-outs-row l k (1- c) n))))

;; scheme-algo.lisp:118
;;; luu-medley-manolios/scheme-algo.lisp, lines 118-128 (the /// section is removed)
(define triples-outs-rows ((l mat-triple-listp) (c natp) (n natp))
  :guard (<= c n)
  :returns (outs idx-tablep)
  (if (zp c)
      nil
    (cons (triples-outs-row l (- n c) n n)
          (triples-outs-rows l (1- c) n))))

;; scheme-algo.lisp:130
;;; luu-medley-manolios/scheme-algo.lisp, lines 130-135 (the /// section is removed)
(define triples-outs ((l mat-triple-listp) (n natp))
  :returns (outs idx-tablep)
  (triples-outs-rows l n n))

;; scheme-algo.lisp:139
;;; luu-medley-manolios/scheme-algo.lisp, lines 139-152 (the /// section is removed)
(define scheme-prods ((l mat-triple-listp) (n natp))
  :guard (and (summand-dim-listp l n) (< 0 n))
  :returns (prods true-listp)
  (if (atom l)
      nil
    (cons (list :mul (mat-lform (car (car l)) n) (mat-lform (cadr (car l)) n))
          (scheme-prods (cdr l) n))))

;; scheme-algo.lisp:154
;;; luu-medley-manolios/scheme-algo.lisp, lines 154-162 (the /// section is removed)
(define scheme-algo ((l mat-triple-listp) (n natp))
  :guard (and (summand-dim-listp l n) (< 0 n))
  :returns (alg consp)
  (cons (scheme-prods l n) (triples-outs l n)))

