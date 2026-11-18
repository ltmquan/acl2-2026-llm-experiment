; The bad calls of grade-r4.lisp, one per block (blocks separated by a line
; ";;;;").  grade.sh submits each at the top level, outside must-fail, and
; checks that it fails with an ACL2 error and not a raw Lisp error.
(definductive no-proof-trees
  :preds ((p x))
  :irules ((recurse ((p x)) (p x))))
;;;;
(definductive bad-and
  :preds ((pa x) (qa x))
  :irules ((pa0 () (pa 0))
           (qa0 () (qa 0))
           (both ((and (pa x) (qa x))) (pa (cons x x)))))
;;;;
(definductive bad-or
  :preds ((po x) (qo x))
  :irules ((po0 () (po 0))
           (qo0 () (qo 0))
           (either ((or (po x) (qo x))) (po (cons x x)))))
;;;;
(definductive bad-not
  :preds ((pn x))
  :irules ((pn0 () (pn 0))
           (neg ((not (pn x))) (pn (cons x x)))))
;;;;
(definductive bad-implies
  :preds ((pm x) (qm x))
  :irules ((pm0 () (pm 0))
           (qm0 () (qm 0))
           (imp ((implies (pm x) (qm x))) (pm (cons x x)))))
