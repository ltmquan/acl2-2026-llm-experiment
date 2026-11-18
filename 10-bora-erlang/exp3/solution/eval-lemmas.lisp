; Rules for symbolic execution of the CPS evaluator.
;
; EVAL-CONT-LIST is opened only when the next continuation is syntactically
; known, i.e. the continuation list is a term (cons K REST) where the tag of
; K is a constant.  Two openers are provided:
;
;   eval-cont-list-open      requires (not (zp fuel)), and treats function
;                            calls (:call-local, :call-remote, :call-fun2)
;                            as cut points that are not stepped through.
;                            Used for proofs that need induction over calls.
;   eval-cont-list-open-if   splits on (zp fuel) instead, and steps through
;                            every known continuation.  Used for proofs that
;                            consider every amount of fuel (disabled by default).

(in-package "ACL2")

(include-book "evaluator")

(defconst *cut-point-tags* '(:call-local :call-remote :call-fun2))

(defun klist-head-known-p (klist cut-tags)
  (declare (xargs :mode :program))
  (if (quotep klist)
      (let ((kl (unquote klist)))
        (and (consp kl)
             (not (and (consp (car kl)) (member-eq (caar kl) cut-tags)))))
    (and (consp klist)
         (eq (car klist) 'cons)
         (let ((k (cadr klist)))
           (cond ((quotep k) (let ((kv (unquote k)))
                               (not (and (consp kv) (member-eq (car kv) cut-tags)))))
                 ((and (consp k) (eq (car k) 'cons) (quotep (cadr k)))
                  (not (member-eq (unquote (cadr k)) cut-tags)))
                 (t nil))))))

(defthm eval-cont-list-nil
  (equal (eval-cont-list nil estate fuel) estate))

(defthm eval-cont-list-open
  (implies (and (syntaxp (klist-head-known-p klist *cut-point-tags*))
                (consp klist)
                (not (zp fuel)))
           (equal (eval-cont-list klist estate fuel)
                  (mv-let (yield klist2 estate2)
                    (eval-cont (car klist) (cdr klist) estate)
                    (if yield
                        estate2
                      (eval-cont-list klist2 estate2 (1- fuel))))))
  :hints (("Goal" :expand ((eval-cont-list klist estate fuel))
                  :in-theory (disable eval-cont))))

(defthmd eval-cont-list-open-if
  (implies (and (syntaxp (klist-head-known-p klist nil))
                (consp klist))
           (equal (eval-cont-list klist estate fuel)
                  (if (zp fuel)
                      (update-estate->val estate (list :out-of-fuel klist))
                    (mv-let (yield klist2 estate2)
                      (eval-cont (car klist) (cdr klist) estate)
                      (if yield
                          estate2
                        (eval-cont-list klist2 estate2 (1- fuel)))))))
  :hints (("Goal" :expand ((eval-cont-list klist estate fuel))
                  :in-theory (disable eval-cont))))

(in-theory (disable eval-cont-list))

(defthm len-of-list-1
  (equal (len (list x)) 1))
