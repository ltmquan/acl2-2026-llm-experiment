;; Grader for tool-arrayset, R4: aset_del_head-used-list--thm (hardin-arrayset, Fig. 9).
;; THEOREM: aset_del_head-used-list--thm
;; The statement below is the paper's, transcribed verbatim (curly quotes written as '); it must follow
;; :by from the model's theorem of the same name, over the model's own definitions.
(in-package "RTL")
(include-book "grader-model")

(defthm grader-aset_del_head-used-list--thm
  (implies
   (and (asetp aset)
        (aset-used-to-free-preconditionp aset)
        (no-dups-anext aset)
        (= (+ (len (aset-used-list aset)) (len (aset-free-list aset)))
           (1- (ARR_SZ))))
   (= (aset-used-list (aset_del_head aset))
      (cdr (aset-used-list aset))))
  :hints (("Goal" :by aset_del_head-used-list--thm))
  :rule-classes nil)
