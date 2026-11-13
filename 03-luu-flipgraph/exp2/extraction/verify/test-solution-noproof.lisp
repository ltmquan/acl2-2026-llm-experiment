; Test solution: the target statements with no proofs (checks TARGET matching; certification is expected to fail).
; Book: (include-book "defs").  Prove each MAIN-k exactly as stated.

(in-package "ACL2")

(include-book "defs")

; MAIN-1. Authors: flip-plus-connectivity (main.lisp:148), restated with the
; existential flip-plus-reachablep instead of the authors' path main-path
; (survey's existential rewrite, approved by the author).
; Meaning: for n >= 2, every correct n x n scheme over F2 reaches every other
; correct n x n scheme by a valid sequence of flip/plus moves (the flip graph
; is strongly connected).
(defthm main-1
  (implies (and (correct-schemep sch n)
                (correct-schemep sch2 n)
                (natp n) (<= 2 n))
           (flip-plus-reachablep sch sch2 n)))

; MAIN-2. Authors: algo-to-correct-scheme (algo-completeness.lisp:41).
; Meaning (completeness): every correct bilinear matrix multiplication
; algorithm over F2 translates to a correct scheme.
(defthm main-2
  (implies (and (algop alg n) (natp n) (< 0 n) (algo-correctp alg n))
           (correct-schemep (algo-scheme alg n) n)))

; MAIN-3. Authors: scheme-algo-correct (scheme-algo.lisp:470).
; Meaning (soundness): the algorithm built from a correct scheme is a correct
; matrix multiplication algorithm.
(defthm main-3
  (implies (and (correct-schemep sch n) (natp n) (< 0 n))
           (algo-correctp (scheme-algo sch n) n)))

; MAIN-4. Authors: algo-scheme-of-scheme-algo (scheme-algo.lisp:451).
; Meaning (round trip): converting a scheme to an algorithm and translating
; it back gives the scheme itself.
(defthm main-4
  (implies (and (schemep sch n) (natp n) (< 0 n))
           (equal (algo-scheme (scheme-algo sch n) n) sch)))
