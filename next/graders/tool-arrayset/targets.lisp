; Statements of Figures 8-9 of hardin-arrayset, transcribed verbatim (curly quotes written as ').
; Data file: grade.sh uses it to compare the model's formulas in its report; the checks themselves are the
; :by proofs in grade-r4-*.lisp, which restate the same forms.
(defthm aset_add-val-at-used_head--thm
  (implies
   (and (asetp aset)
        (aset-free-to-used-preconditionp aset)
        (unsigned-byte-p 64 val))
   (= (si (ag (used_head (aset_add val aset))
              (ag 'avals (aset_add val aset))) 64)
      (si val 64))))

(defthm aset_del-val-at-free_head--thm
  (implies
   (and (asetp aset)
        (aset-used-to-free-preconditionp aset)
        (no-dups-anext aset)
        (unsigned-byte-p 64 val)
        (< (aset_find_val_from (ag 'used_lst aset) val aset) (ARR_SZ)))
   (= (si (ag (free_head (aset_del val aset))
              (ag 'avals (aset_del val aset))) 64)
      (si val 64))))

(defthm aset_del_head-used-list--thm
  (implies
   (and (asetp aset)
        (aset-used-to-free-preconditionp aset)
        (no-dups-anext aset)
        (= (+ (len (aset-used-list aset)) (len (aset-free-list aset)))
           (1- (ARR_SZ))))
   (= (aset-used-list (aset_del_head aset))
      (cdr (aset-used-list aset)))))

(defthm aset_del_head-free-list--thm
  (implies
   (and (asetp aset)
        (aset-used-to-free-preconditionp aset)
        (no-dups-anext aset)
        (= (+ (len (aset-used-list aset)) (len (aset-free-list aset)))
           (1- (ARR_SZ))))
   (= (aset-free-list (aset_del_head aset))
      (cons (used_head aset) (aset-free-list aset)))))
