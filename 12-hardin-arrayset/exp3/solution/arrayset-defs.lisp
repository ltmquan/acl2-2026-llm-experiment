; Arrayset Revisited -- verification-only definitions.
;
; The arrayset functions themselves (FREE_HEAD, USED_HEAD, ASET_INIT,
; ASET_TRANSFER, ASET_ADD, ASET_DEL_HEAD, ASET_FIND_VAL_FROM, ASET_DEL) are
; in gen/arrayset.lisp, generated mechanically from src/arrayset.rs by
; plexi (RAR -> RAC) and the RAC translator (RAC -> ACL2); see build.sh.
;
; Here we define the predicates and functions used to state their
; correctness: ASETP, the transfer preconditions, NO-DUPS-ANEXT, and the
; list functions ASET-USED-LIST and ASET-FREE-LIST.  None of these depends
; on the value of ARR_SZ, only on 1 < ARR_SZ < 2^32.

(in-package "RTL")
(include-book "gen/arrayset")
(local (include-book "rtl/rel11/lib/bits" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

;;; ------------------------------------------------------------------
;;; Facts about the array size, after which ARR_SZ is kept disabled.

(in-theory (disable arr_sz (:e arr_sz)))

(defthm natp-arr_sz
  (natp (arr_sz))
  :hints (("Goal" :in-theory (enable arr_sz (:e arr_sz))))
  :rule-classes (:rewrite :type-prescription))

(defthm arr_sz-bounds
  (and (< 1 (arr_sz))
       (< (arr_sz) (expt 2 32)))
  :hints (("Goal" :in-theory (enable arr_sz (:e arr_sz))))
  :rule-classes :linear)

;;; ------------------------------------------------------------------
;;; Verification-only functions.

;; anext entries at indices i, ..., n-1 are natural numbers below n.
(defun anext-rangep (i n anext)
  (declare (xargs :measure (nfix (- n i))))
  (if (and (natp i) (natp n) (< i n))
      (and (natp (ag i anext))
           (< (ag i anext) n)
           (anext-rangep (1+ i) n anext))
    t))

;; The list of anext entries at indices i, ..., n-1.
(defun anext-list (i n anext)
  (declare (xargs :measure (nfix (- n i))))
  (if (and (natp i) (natp n) (< i n))
      (cons (ag i anext) (anext-list (1+ i) n anext))
    nil))

(defund no-dups-anext (aset)
  (no-duplicatesp-equal (anext-list 0 (arr_sz) (ag 'anext aset))))

;; Follow the anext links from idx until tail is reached (at most fuel
;; elements), collecting the indices visited, tail included.
(defun aset-walk (idx tail fuel anext)
  (declare (xargs :measure (nfix fuel)))
  (cond ((zp fuel) nil)
        ((equal idx tail) (list idx))
        (t (cons idx (aset-walk (ag idx anext) tail (1- fuel) anext)))))

;; Does that walk reach tail within fuel steps?
(defun aset-walk-closedp (idx tail fuel anext)
  (declare (xargs :measure (nfix fuel)))
  (cond ((zp fuel) nil)
        ((equal idx tail) t)
        (t (aset-walk-closedp (ag idx anext) tail (1- fuel) anext))))

(defund aset-used-nonemptyp (aset)
  (and (natp (ag 'used_lst aset)) (< (ag 'used_lst aset) (arr_sz))))

(defund aset-free-nonemptyp (aset)
  (and (natp (ag 'free_lst aset)) (< (ag 'free_lst aset) (arr_sz))))

;; The used list: the indices of the used elements, from used_head round
;; to used_lst.
(defund aset-used-list (aset)
  (if (aset-used-nonemptyp aset)
      (aset-walk (used_head aset) (ag 'used_lst aset) (1- (arr_sz))
                 (ag 'anext aset))
    nil))

;; The free list: the indices of the free elements, from free_head round
;; to free_lst.
(defund aset-free-list (aset)
  (if (aset-free-nonemptyp aset)
      (aset-walk (free_head aset) (ag 'free_lst aset) (1- (arr_sz))
                 (ag 'anext aset))
    nil))

;; Each nonempty list is a cycle through its tail, and the used and free
;; lists are disjoint and contain no repetitions.
(defund aset-lists-wfp (aset)
  (and (implies (aset-used-nonemptyp aset)
                (aset-walk-closedp (used_head aset) (ag 'used_lst aset)
                                   (1- (arr_sz)) (ag 'anext aset)))
       (implies (aset-free-nonemptyp aset)
                (aset-walk-closedp (free_head aset) (ag 'free_lst aset)
                                   (1- (arr_sz)) (ag 'anext aset)))
       (no-duplicatesp-equal (append (aset-used-list aset)
                                     (aset-free-list aset)))))

;; A well-formed arrayset.
(defund asetp (aset)
  (and (natp (ag 'used_lst aset))
       (<= (ag 'used_lst aset) (arr_sz))
       (natp (ag 'free_lst aset))
       (<= (ag 'free_lst aset) (arr_sz))
       (natp (ag 'err aset))
       (anext-rangep 0 (arr_sz) (ag 'anext aset))
       (aset-lists-wfp aset)))

;; Common preconditions (cf. the Verus requires clauses of Figure 10).
(defund aset-common-preconditionp (aset)
  (and (< 0 (ag 'used_lst aset))
       (<= (ag 'used_lst aset) (arr_sz))
       (< 0 (ag 'free_lst aset))
       (<= (ag 'free_lst aset) (arr_sz))
       (equal (ag 0 (ag 'anext aset)) 0)
       (not (equal (ag 'used_lst aset) (ag 'free_lst aset)))))

;; A free-to-used transfer (aset_add) has an element to move.
(defund aset-free-to-used-preconditionp (aset)
  (and (aset-common-preconditionp aset)
       (< (ag 'free_lst aset) (arr_sz))))

;; A used-to-free transfer (aset_del_head, aset_del) has an element to move.
(defund aset-used-to-free-preconditionp (aset)
  (and (aset-common-preconditionp aset)
       (< (ag 'used_lst aset) (arr_sz))))
