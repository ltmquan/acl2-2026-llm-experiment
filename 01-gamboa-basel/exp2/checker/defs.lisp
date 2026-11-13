; Given definitions for: R. Gamboa, "An Alternative Proof in ACL2(r) of Euler's
; Solution to the Basel Problem".  Logic: ACL2(r).
; The author's books are not available; basel-series is copied verbatim from the
; paper (Sec. 3, p. 3).  acl2-pi, i-close, i-large come from ACL2(r) and the
; community book nonstd/nsa/trig.

(in-package "ACL2")

(include-book "nonstd/nsa/trig" :dir :system)

; Paper, Sec. 3, p. 3.  Computes sum_{k=i}^{n-1} 1/k^2.
(defun basel-series (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      0
      (+ (expt i -2)
         (basel-series (1+ i) n))))
