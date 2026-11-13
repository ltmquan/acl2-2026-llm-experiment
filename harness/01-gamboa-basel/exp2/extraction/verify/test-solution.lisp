; Checker test: skip-proofs solution (expected to be rejected as BANNED).
(in-package "ACL2")
(include-book "defs")
(skip-proofs
 (defthm MAIN-1
   (implies (and (posp n)
                 (i-large n))
            (i-close (basel-series 1 n)
                     (/ (expt (acl2-pi) 2) 6)))))
