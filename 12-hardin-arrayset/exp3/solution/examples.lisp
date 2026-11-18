; Arrayset Revisited -- the example of Figure 4, by execution.
;
; The example has 5 usable cells (indices 1..5; index 0 is unused), so it
; uses the instance of the arrayset generated with ARR_SZ = 6 (see
; gen/arrayset6.lisp and build.sh).  ARR_SZ (= 6) is the null index.

(in-package "RTL")

(include-book "arrayset6-invariants") ; gen/arrayset6 + verification

(assert-event (equal (arr_sz) 6))

;; Build a RAC array (record) holding the elements of lst at indices
;; i, i+1, ...
(defun list->arr (lst i)
  (if (endp lst)
      nil
    (as i (car lst) (list->arr (cdr lst) (1+ i)))))

;; The values held by the elements of a list of indices.
(defun vals-at (idxs aset)
  (if (endp idxs)
      nil
    (cons (si (ag (car idxs) (ag 'avals aset)) 64)
          (vals-at (cdr idxs) aset))))

(defun mk-aset (anext avals free used err)
  (as 'anext (list->arr anext 0)
      (as 'avals (list->arr avals 0)
          (as 'free_lst free
              (as 'used_lst used
                  (as 'err err nil))))))

;;; ------------------------------------------------------------------
;;; Figure 4(a): contents {33, 22}.  used_lst = 1, free_lst = 5.
;;;
;;;   index  0  1  2  3  4  5
;;;   anext  0  2  1  4  5  3
;;;   avals  X 22 33  X  X  X      (X: free elements; we use 0)

(defconst *fig4a*
  (mk-aset '(0 2 1 4 5 3)
           '(0 22 33 0 0 0)
           5 1 1))

;;; Figure 4(b): the arrayset after aset_del(22, aset).  used_lst = 2,
;;; free_lst = 5.
;;;
;;;   index  0  1  2  3  4  5
;;;   anext  0  3  2  4  5  1
;;;   avals  X  X 33  X  X  X
;;;
;;; aset_del does not erase the deleted value: avals[1] still holds 22
;;; (shown as X in the figure, as element 1 is now free).

(defconst *fig4b*
  (mk-aset '(0 3 2 4 5 1)
           '(0 22 33 0 0 0)
           5 2 1))

;; The main check: from the state of panel (a), aset_del of 22 gives the
;; state of panel (b).
(assert-event (equal (aset_del 22 *fig4a*) *fig4b*))

;; Field by field, as described in the text of Section 5.1.
(assert-event (equal (ag 'used_lst (aset_del 22 *fig4a*)) 2))
(assert-event (equal (ag 'free_lst (aset_del 22 *fig4a*)) 5))
(assert-event (equal (ag 'err (aset_del 22 *fig4a*)) 1))     ; no error
(assert-event (equal (anext-list 0 6 (ag 'anext (aset_del 22 *fig4a*)))
                     '(0 3 2 4 5 1)))
(assert-event (equal (ag 2 (ag 'avals (aset_del 22 *fig4a*))) 33))

;; Panel (a): used_head is 2, avals[2] = 33; following anext from 2 gives
;; 1 = used_lst, the tail, so the contents are {33, 22}.  The free list
;; is 3, 4, 5.
(assert-event (equal (used_head *fig4a*) 2))
(assert-event (equal (free_head *fig4a*) 3))
(assert-event (equal (aset-used-list *fig4a*) '(2 1)))
(assert-event (equal (vals-at (aset-used-list *fig4a*) *fig4a*) '(33 22)))
(assert-event (equal (aset-free-list *fig4a*) '(3 4 5)))

;; Panel (b): the used list is shortened by one and the free list
;; lengthened by one.  Traversing the free list from free_lst = 5:
;; anext[5] = 1, anext[1] = 3, anext[3] = 4, anext[4] = 5.
(assert-event (equal (aset-used-list *fig4b*) '(2)))
(assert-event (equal (vals-at (aset-used-list *fig4b*) *fig4b*) '(33)))
(assert-event (equal (aset-free-list *fig4b*) '(1 3 4 5)))
(assert-event (equal (free_head *fig4b*) 1))
(assert-event (equal (si (ag (free_head *fig4b*) (ag 'avals *fig4b*)) 64)
                     22))

;; aset_find_val_from returns the predecessor (index 2) of the element
;; holding 22 (index 1).
(assert-event (equal (aset_find_val_from 1 22 *fig4a*) 2))
(assert-event (equal (aset_find_val_from 1 33 *fig4a*) 1))
(assert-event (equal (aset_find_val_from 1 44 *fig4a*) 6))

;;; ------------------------------------------------------------------
;;; Panel (a) is reachable: aset_init, then add 22, then add 33.

(defconst *empty* (mk-aset nil nil 0 0 0))

(defconst *init* (aset_init *empty*))

(assert-event (equal (anext-list 0 6 (ag 'anext *init*)) '(0 2 3 4 5 1)))
(assert-event (equal (ag 'free_lst *init*) 5))
(assert-event (equal (ag 'used_lst *init*) 6))       ; empty used list
(assert-event (equal (aset-free-list *init*) '(1 2 3 4 5)))
(assert-event (equal (aset-used-list *init*) nil))

(assert-event (equal (aset_add 33 (aset_add 22 *init*)) *fig4a*))

;;; ------------------------------------------------------------------
;;; The hypotheses of the theorems of Figures 8 and 9 hold of these
;;; states (so the theorems are not vacuous), and so do their conclusions.

(assert-event (asetp *init*))
(assert-event (asetp *fig4a*))
(assert-event (asetp *fig4b*))
(assert-event (aset-free-to-used-preconditionp *fig4a*))
(assert-event (aset-used-to-free-preconditionp *fig4a*))
(assert-event (no-dups-anext *fig4a*))
(assert-event (no-dups-anext *fig4b*))
(assert-event (equal (+ (len (aset-used-list *fig4a*))
                        (len (aset-free-list *fig4a*)))
                     (1- (arr_sz))))
(assert-event (aset-sizes-okp *init*))
(assert-event (aset-sizes-okp *fig4a*))
(assert-event (aset-sizes-okp *fig4b*))
(assert-event (< (aset_find_val_from (ag 'used_lst *fig4a*) 22 *fig4a*)
                 (arr_sz)))

;; Figure 8.
(assert-event (equal (si (ag (used_head (aset_add 44 *fig4a*))
                             (ag 'avals (aset_add 44 *fig4a*))) 64)
                     44))
(assert-event (equal (si (ag (free_head (aset_del 22 *fig4a*))
                             (ag 'avals (aset_del 22 *fig4a*))) 64)
                     22))
;; Figure 9.
(assert-event (equal (aset-used-list (aset_del_head *fig4a*))
                     (cdr (aset-used-list *fig4a*))))
(assert-event (equal (aset-free-list (aset_del_head *fig4a*))
                     (cons (used_head *fig4a*) (aset-free-list *fig4a*))))

;;; ------------------------------------------------------------------
;;; Error cases.

;; Deleting a value that is not present: err = ARR_SZ, nothing else changes.
(assert-event (equal (aset_del 99 *fig4a*) (as 'err 6 *fig4a*)))

;; Fill the arrayset: 3 more adds succeed, the 4th fails.
(defconst *full* (aset_add 3 (aset_add 2 (aset_add 1 *fig4a*))))
(assert-event (equal (ag 'err *full*) 1))
(assert-event (equal (ag 'free_lst *full*) 6))       ; empty free list
(assert-event (equal (vals-at (aset-used-list *full*) *full*) '(3 2 1 33 22)))
(assert-event (equal (ag 'err (aset_add 4 *full*)) 6))

;; Negative values are stored as 64-bit two's complement bit patterns.
(assert-event (equal (vals-at (aset-used-list (aset_add -5 *fig4a*))
                              (aset_add -5 *fig4a*))
                     '(-5 33 22)))
(assert-event (equal (ag 'err (aset_del -5 (aset_add -5 *fig4a*))) 1))
