; Grader R1 (fw-multisets): guard verification of every required function,
; bequiv an equivalence respected by every function with a bag argument, and
; the non-functional requirement that count, insert and delete do not convert
; to lists.  Results are printed as GRADER-OK / GRADER-FAIL lines.
(in-package "ACL2")
(include-book "grader-mset-model-defs")

(gr-guards (mset::bagp mset::bfix mset::bequiv mset::empty mset::emptyp mset::count mset::in
            mset::insert mset::insert-n mset::delete mset::delete-all mset::cardinality
            mset::support mset::subbag mset::sum mset::union mset::intersect mset::diff
            mset::from-list mset::to-list))

(gr-congruences mset::bequiv
                ((mset::emptyp 1) (mset::count 2) (mset::in 2) (mset::insert 2) (mset::insert-n 3)
                 (mset::delete 2) (mset::delete-all 2) (mset::cardinality 1) (mset::support 1)
                 (mset::subbag 1 2) (mset::sum 1 2) (mset::union 1 2) (mset::intersect 1 2)
                 (mset::diff 1 2) (mset::to-list 1)))

; List conversions: the bag/list conversions of the library itself, the omap
; conversions to and from lists and alists, and the ACL2 alist projections.
; Any function of the MSET package whose name contains "LIST" also counts.
(gr-nolist (mset::count mset::insert mset::delete)
           (mset::to-list mset::from-list
            omap::keys omap::values omap::from-lists omap::from-alist omap::list-in omap::list-notin
            omap::list-lookup
            strip-cars strip-cdrs alist-keys alist-vals true-list-fix list-fix
            set::mergesort)
           "MSET")
