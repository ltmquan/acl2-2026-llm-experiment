; Grader helper (fw-multisets): the theory of the model's definitions of the
; required functions, which grader statements are proved with disabled.
; Included after the model's library by each grader book.
(in-package "ACL2")
(include-book "mset")
(include-book "grader-mset-lib")
(make-event
 `(deftheory gr-model-defs
    ',(gr-def-runes '(mset::bagp mset::bfix mset::bequiv mset::empty mset::emptyp mset::count mset::in
                      mset::insert mset::insert-n mset::delete mset::delete-all mset::cardinality
                      mset::support mset::subbag mset::sum mset::union mset::intersect mset::diff
                      mset::from-list mset::to-list)
                    (w state))))
