(in-package "ACL2")
(include-book "../authors/global_reorder")

(defthm MAIN-1
  (implies
   (checkpoint-start-end-segment-p st input-seg)
   (state-equivalent-p
    (run-imp st input-seg)
    (run-imp
     st
     (append
      (checkpoint-segment-before-cut-inputs st input-seg)
      (checkpoint-segment-after-cut-inputs st input-seg)))))
  :hints (("Goal" :use checkpoint-complete-segment-reordered-run-state-equivalent
           :in-theory nil)))

(defthm MAIN-2
  (implies
   (post-pre-swap-start-p st m input-1 input-2)
   (state-equivalent-p
    (run-imp st (list input-1 input-2))
    (run-imp st (list input-2 input-1))))
  :hints (("Goal" :use post-pre-two-imp-inputs-commute-under-state-equivalence
           :in-theory nil)))
