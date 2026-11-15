; Non-vacuity checks for 06-russinoff-fields/exp1/solution.lisp (reviewer addition, not part of the run).
; Certify next to a copy of solution.lisp: cert.pl --acl2 <ACL2 8.7 image> 06-russinoff-fields-exp1-nonvac.lisp

(in-package "ACL2")
(include-book "solution")

; x^2+1 = (x+1)^2 over F_2 is reducible, so the extension is NOT a field
(defthm not-fieldp-reducible-example
  (not (fieldp (quote (:ext (:fp 2) (1 0 1)))))
  :hints (("Goal" :use ((:instance reducible-suff (b (quote (:fp 2))) (p (quote (1 0 1))) (q (quote (1 1)))))
           :in-theory (e/d (irreducible) ((:e fieldp) (:e irreducible))))))

; x^2+x+1 over F_2 is irreducible, so F_4 IS a field
(defthm monic-deg1-over-f2
  (implies (and (monicp (quote (:fp 2)) q) (equal (len q) 2))
           (or (equal q (quote (0 1))) (equal q (quote (1 1)))))
  :hints (("Goal" :in-theory (enable fep fone pfield::fep)
           :expand ((polyp (quote (:fp 2)) q) (polyp (quote (:fp 2)) (cdr q))
                    (polyp (quote (:fp 2)) (cddr q)))))
  :rule-classes nil)

(defthm fieldp-f4
  (fieldp (quote (:ext (:fp 2) (1 1 1))))
  :hints (("Goal" :in-theory (e/d (irreducible reducible (:e dm::primep)) (reducible-suff (:e fieldp) (:e irreducible)))
           :use ((:instance monic-deg1-over-f2
                  (q (reducible-witness (quote (:fp 2)) (quote (1 1 1)))))))))

; in F_4 = F_2[x]/(x^2+x+1), the root alpha times its inverse is 1
(defthm main-instance-f4
  (let ((f (quote (:ext (:fp 2) (1 1 1)))))
    (equal (fmul f (quote (0 1)) (finv f (quote (0 1)))) (fone f)))
  :hints (("Goal" :in-theory (enable fmul finv fone))))
