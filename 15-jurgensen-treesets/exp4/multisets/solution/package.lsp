; Package for the MSET (finite multisets / bags) library.

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "std/omaps/portcullis" :dir :system)

(defpkg "MSET"
  (append '(duplicity
            lnfix
            repeat
            assert-event)
          (set-difference-eq *std-pkg-symbols*
                             '(count
                               set::emptyp
                               set::head
                               set::tail
                               set::insert
                               set::in
                               set::subset
                               set::delete
                               set::union
                               set::intersect
                               set::cardinality))))
