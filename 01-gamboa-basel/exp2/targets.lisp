; Target theorems for gamboa-basel (ACL2(r)).

; Author's name: basel-series-closed-form-close
; Paper (gamboa-basel.pdf) Sec. 6, p. 13 (gamboa-basel.txt, pdftotext -layout, lines 794-799).
; Meaning: for every infinitely large positive integer n, sum_{k=1}^{n-1} 1/k^2 is
; infinitely close to pi^2/6 (Euler's solution to the Basel problem).
(defthm MAIN-1
  (implies (and (posp n)
                (i-large n))
           (i-close (basel-series 1 n)
                    (/ (expt (acl2-pi) 2) 6))))
