; Checker test: correct statement with a deliberately hopeless proof attempt.
; Expected checker result: passes BANNED/NO-INCLUDE/TARGET-MISMATCH, then FAILED at certification.
(in-package "ACL2")
(include-book "defs")
(defthm MAIN-1
  (implies (and (posp n)
                (i-large n))
           (i-close (basel-series 1 n)
                    (/ (expt (acl2-pi) 2) 6)))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :do-not-induct t)))
