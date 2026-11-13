; V3: the targets follow from the authors' development (authors' books on 8.7).
(in-package "ACL2")

(include-book "../authors/main")
(include-book "../authors/scheme-algo")

;; Identical to the form in defs.lisp.
(defun-sk flip-plus-reachablep (sch sch2 n)
  (exists (moves)
          (and (path-validp moves sch n)
               (equal (apply-moves moves sch n) sch2))))

(defthm main-1
  (implies (and (correct-schemep sch n)
                (correct-schemep sch2 n)
                (natp n) (<= 2 n))
           (flip-plus-reachablep sch sch2 n))
  :hints (("Goal" :use ((:instance flip-plus-reachablep-suff
                                   (moves (main-path sch sch2 n)))
                        flip-plus-connectivity)
           :in-theory nil)))

(defthm main-2
  (implies (and (algop alg n) (natp n) (< 0 n) (algo-correctp alg n))
           (correct-schemep (algo-scheme alg n) n))
  :hints (("Goal" :use algo-to-correct-scheme :in-theory nil)))

(defthm main-3
  (implies (and (correct-schemep sch n) (natp n) (< 0 n))
           (algo-correctp (scheme-algo sch n) n))
  :hints (("Goal" :use scheme-algo-correct :in-theory nil)))

(defthm main-4
  (implies (and (schemep sch n) (natp n) (< 0 n))
           (equal (algo-scheme (scheme-algo sch n) n) sch))
  :hints (("Goal" :use algo-scheme-of-scheme-algo :in-theory nil)))
