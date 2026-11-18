;; Grader for tool-arrayset, R4: aset_add-val-at-used_head--thm (hardin-arrayset, Fig. 8).
;; THEOREM: aset_add-val-at-used_head--thm
;; The statement below is the paper's, transcribed verbatim (curly quotes written as '); it must follow
;; :by from the model's theorem of the same name, over the model's own definitions.
(in-package "RTL")
(include-book "grader-model")

(defthm grader-aset_add-val-at-used_head--thm
  (implies
   (and (asetp aset)
        (aset-free-to-used-preconditionp aset)
        (unsigned-byte-p 64 val))
   (= (si (ag (used_head (aset_add val aset))
              (ag 'avals (aset_add val aset))) 64)
      (si val 64)))
  :hints (("Goal" :by aset_add-val-at-used_head--thm))
  :rule-classes nil)
