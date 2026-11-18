;; Grader for tool-arrayset, supporting evidence for R3 (reported inside the R3 MANUAL line): the example of
;; Figure 4, executed on the model's functions at the model's ARR_SZ.  Figure 4(a) is built as in
;; grade-r4v.lisp (aset_init, add 22, add 33); Figure 4(b) is aset_del(22) of it.  Section 5 text:
;; (a) has contents {33, 22} with 33 at the used head; after aset_del(22, aset) the used list is shortened
;; by one and the free list lengthened by one, and the deleted index becomes the free head.
;; Uses the model's aset-used-list / aset-free-list (Sec. 5.3), used_head and free_head (Sec. 5.1).
(in-package "RTL")
(include-book "grader-init")

(defconst *grader-a* (aset_add 33 (aset_add 22 (grader-init))))
(defconst *grader-b* (aset_del 22 *grader-a*))

;; (a): two used elements, 33 at the head, then 22; no error
(assert-event (equal (len (aset-used-list *grader-a*)) 2))
(assert-event (equal (ag 'err *grader-a*) 1))
(assert-event (= (si (ag (used_head *grader-a*) (ag 'avals *grader-a*)) 64) 33))
(assert-event (= (si (ag (ag (used_head *grader-a*) (ag 'anext *grader-a*)) (ag 'avals *grader-a*)) 64) 22))
;; the used list is circular: the head's successor is the tail used_lst (Figure 4(a): anext[2] = 1)
(assert-event (equal (ag (used_head *grader-a*) (ag 'anext *grader-a*)) (ag 'used_lst *grader-a*)))

;; (b): used list shortened by one, free list lengthened by one; 33 remains, 22 is at the free head
(assert-event (equal (len (aset-used-list *grader-b*)) 1))
(assert-event (equal (len (aset-free-list *grader-b*)) (1+ (len (aset-free-list *grader-a*)))))
(assert-event (= (si (ag (used_head *grader-b*) (ag 'avals *grader-b*)) 64) 33))
(assert-event (= (si (ag (free_head *grader-b*) (ag 'avals *grader-b*)) 64) 22))
;; one-element circular used list: anext[used_lst] = used_lst (Figure 4(b): anext[2] = 2)
(assert-event (equal (used_head *grader-b*) (ag 'used_lst *grader-b*)))
;; the deleted element's index follows free_lst (Figure 4(b): anext[5] = 1)
(assert-event (equal (free_head *grader-b*) (ag (used_head *grader-a*) (ag 'anext *grader-a*))))
