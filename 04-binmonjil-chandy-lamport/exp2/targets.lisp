(in-package "ACL2")

; MAIN-1: authors' checkpoint-complete-segment-reordered-run-state-equivalent,
; global_reorder.lisp:5748. Global reordering theorem: running a complete
; checkpoint segment is state-equivalent to running all its pre-recording
; (before-cut) inputs followed by all its post-recording (after-cut) inputs.
(defthm MAIN-1
  (implies
   (checkpoint-start-end-segment-p st input-seg)
   (state-equivalent-p
    (run-imp st input-seg)
    (run-imp
     st
     (append
      (checkpoint-segment-before-cut-inputs st input-seg)
      (checkpoint-segment-after-cut-inputs st input-seg))))))

; MAIN-2: authors' post-pre-two-imp-inputs-commute-under-state-equivalence,
; local_swap.lisp:2224. Local swap theorem: an adjacent post-cut input followed
; by a pre-cut input can be exchanged without changing the resulting state
; (up to state equivalence).
(defthm MAIN-2
  (implies
   (post-pre-swap-start-p st m input-1 input-2)
   (state-equivalent-p
    (run-imp st (list input-1 input-2))
    (run-imp st (list input-2 input-1)))))
