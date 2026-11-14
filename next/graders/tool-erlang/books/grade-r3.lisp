; tool-erlang grader, requirement 3 (mechanical part): the model's books introduce at least one
; constrained function (encapsulate) with an executable attachment (defattach).  The attachments
; added by the model's books are printed; that the constraint is the fairness condition of
; Section 3.1 is checked by hand (CHECKLIST.md R3).
(in-package "ACL2")
(include-book "grader-util")
(make-event `(defconst *grader-attachments-before* ',(all-attachments (w state))))
(include-book "../examples")
(include-book "../reduce")

(defun grader-new-constrained-attachments (al before w)
  (declare (xargs :mode :program))
  (cond ((endp al) nil)
        ((and (not (member-equal (car al) before))
              (getpropc (caar al) 'constrainedp nil w))
         (cons (car al) (grader-new-constrained-attachments (cdr al) before w)))
        (t (grader-new-constrained-attachments (cdr al) before w))))

(make-event
 (let ((new (grader-new-constrained-attachments (all-attachments (w state))
                                                *grader-attachments-before* (w state))))
   (prog2$ (cw "~%GRADER-R3-ATTACHMENTS ~x0~%" new)
           `(defconst *grader-new-attachments* ',new))))

(assert-event (consp *grader-new-attachments*)
              :msg "No constrained function of the model's books has an attachment.")
