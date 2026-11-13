; Prints, for every function introduced by defs.lisp (list *fns* below) and for every function
; they transitively depend on, the unnormalized body, the constraint (for constrained/defchoose
; functions), the formals and the guard.  Run after including either defs (8.7) or the authors'
; projects/linear/vectors (master); the two outputs are diffed.
(in-package "DM")
(defconst *fns* '(vp v+ v0 v- v* vbasis0 vcoords0 vlistnp vcomb vdim
  vcoord-mat vindepp vdepp vdep-coeffs vcoords vbasisp vunspanned extend-to-basis
  wp w+ w0 w- w* wbasis0 wcoords0 wlistnp wcomb wdim wcoord-mat windepp
  lin lin-list lin-mat lin-injective-p lin-injective-p-witness lin-preimage
  lin-surjective-p lin-surjective-p-witness lin-inv
  sp slistnp sunspanned sbasis0-aux sbasis0 sdim scoords0 sbasis1 scoords1 sdim1
  in-kernel-p klistnp kbasis-coord kbasis-coords-aux kbasis-coords kbasis-aux kbasis kdim
  kcoords-aux kcoords in-image-p idim extend-kbasis firstn ibasis ilistnp icoords))
(program)
(defun constraint-of (f wrld)
  ; a list of terms
  (mv-let (flg x origins) (acl2::constraint-info f wrld)
    (declare (ignore origins))
    (if flg x (list x))))
(defun deps (fns wrld seen)
  (cond ((endp fns) seen)
        ((member-eq (car fns) seen) (deps (cdr fns) wrld seen))
        ((acl2::getpropc (car fns) 'acl2::primitive-recursive-defun nil wrld)
         (deps (cdr fns) wrld (cons (car fns) seen)))
        (t (let* ((f (car fns))
                  (b (acl2::body f nil wrld))
                  (c (constraint-of f wrld))
                  (new (append (acl2::all-fnnames b) (acl2::all-fnnames-lst c))))
             (deps (append new (cdr fns)) wrld (cons f seen))))))
(defun dump (fns wrld)
  (if (endp fns) nil
    (let ((f (car fns)))
      (prog2$ (cw "@@ ~x0~%  formals ~x1~%  body ~x2~%  constraint ~x3~%  guard ~x4~%  measure ~x5~%"
                  f (acl2::getpropc f 'acl2::formals nil wrld) (acl2::body f nil wrld)
                  (constraint-of f wrld)
                  (acl2::getpropc f 'acl2::guard t wrld)
                  (let ((j (acl2::getpropc f 'acl2::justification nil wrld)))
                    (and j (acl2::access acl2::justification j :measure))))
              (dump (cdr fns) wrld)))))
(defun dm-syms-only (l)
  (cond ((endp l) nil)
        ((equal (symbol-package-name (car l)) "DM") (cons (car l) (dm-syms-only (cdr l))))
        (t (dm-syms-only (cdr l)))))
(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 100000 state)
(cw "BEGIN-DUMP~%")
(dump (acl2::merge-sort-symbol< (dm-syms-only (deps *fns* (w state) nil))) (w state))
(cw "END-DUMP~%")
