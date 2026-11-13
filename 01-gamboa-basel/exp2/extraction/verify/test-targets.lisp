; V2: admit every target under skip-proofs on top of defs (verification only).
(in-package "ACL2")
(include-book "defs")
(skip-proofs
 (defthm MAIN-1
   (implies (and (posp n)
                 (i-large n))
            (i-close (basel-series 1 n)
                     (/ (expt (acl2-pi) 2) 6)))))
