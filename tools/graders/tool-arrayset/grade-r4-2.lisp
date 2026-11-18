;; Grader for tool-arrayset, R4: aset_del-val-at-free_head--thm (hardin-arrayset, Fig. 8).
;; THEOREM: aset_del-val-at-free_head--thm
;; The statement below is the paper's, transcribed verbatim (curly quotes written as '); it must follow
;; :by from the model's theorem of the same name, over the model's own definitions.
(in-package "RTL")
(include-book "grader-model")

(defthm grader-aset_del-val-at-free_head--thm
  (implies
   (and (asetp aset)
        (aset-used-to-free-preconditionp aset)
        (no-dups-anext aset)
        (unsigned-byte-p 64 val)
        (< (aset_find_val_from (ag 'used_lst aset) val aset) (ARR_SZ)))
   (= (si (ag (free_head (aset_del val aset))
              (ag 'avals (aset_del val aset))) 64)
      (si val 64)))
  :hints (("Goal" :by aset_del-val-at-free_head--thm))
  :rule-classes nil)
