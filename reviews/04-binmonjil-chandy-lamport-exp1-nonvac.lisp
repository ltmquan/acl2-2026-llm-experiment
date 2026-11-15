; Non-vacuity checks for 04-binmonjil-chandy-lamport/exp1/solution.lisp (reviewer addition, not part of the run).
; Certify next to a copy of solution.lisp: cert.pl --acl2 <ACL2 8.7 image> 04-binmonjil-chandy-lamport-exp1-nonvac.lisp

(in-package "ACL2")
(include-book "solution")

(local (in-theory (enable cl-step ps-of chan-of pop-chans ins-of outs-of sids-of
                          local-ps local-out marker)))
(local (in-theory (disable (:e init-state) (:e init-pstates) (:e legal-exec) (:e cl-run) (:e cl-step)
                           (:e local-ps) (:e local-out) (:e app-outbox) (:e complete-segment-p)
                           (:e incomplete-before-each) (:e pre-inputs) (:e post-inputs) (:e legal-input))))

; A concrete 2-process system (processes 1 and 2, channels both ways), fixed by
; hypotheses on the abstract topology/application functions.
(defmacro sys-hyps ()
  (quote (and (equal (sys-procs) (quote (1 2)))
              (equal (in-nbrs 1) (quote (2))) (equal (out-nbrs 1) (quote (2)))
              (equal (in-nbrs 2) (quote (1))) (equal (out-nbrs 2) (quote (1)))
              (equal (init-local 1) (quote l1)) (equal (init-local 2) (quote l2))
              (equal (app-compute 1 (quote l1)) (quote a1))
              (equal (app-compute 2 (quote l2)) (quote a2))
              (equal (app-compute 1 (quote a1)) (quote b1))
              (app-send-p 1 2 (quote a1)) (app-send-p 2 1 (quote a2))
              (not (app-send-p 1 2 (quote b1)))
              (equal (app-make-msg 1 2 (quote a1)) (quote m1))
              (equal (app-make-msg 2 1 (quote a2)) (quote m2)))))

; prefix: both processes compute, putting m1 on 1->2 and m2 on 2->1
(defconst *prefix* (quote ((1 :compute) (2 :compute))))

; the state reached (a records-library record)
(defconst *st0*
  (quote ((:CHANS ((1 . 2) M1) ((2 . 1) M2))
          (:PROCS 1 2)
          (:PSTATES (1 (:APP . A1) (:COUNTER . 0) (:IN 2) (:OUT 2))
                    (2 (:APP . A2) (:COUNTER . 0) (:IN 1) (:OUT 1))))))

(defthm prefix-legal-and-reaches-st0
  (implies (sys-hyps)
           (and (legal-exec (init-state) *prefix*)
                (equal (cl-run (init-state) *prefix*) *st0*)))
  :rule-classes nil)

; segment: 1 initiates; 1 computes (post); 1 receives m2 (post, so m2 is recorded
; as in flight on 2->1); 2 receives m1 (pre); 2 receives the marker (pre, r_2);
; 1 receives 2s marker (post) -> snapshot complete.
(defconst *seg* (quote ((1 :checkpoint) (1 :compute) (1 :receive 2)
                        (2 :receive 1) (2 :receive 1) (1 :receive 2))))

(defthm segment-complete
  (implies (sys-hyps) (complete-segment-p *st0* *seg*))
  :rule-classes nil)

; all three hypotheses of MAIN hold together for st, prefix and e
(defthm main-hyps-satisfiable
  (implies (sys-hyps)
           (let ((prefix *prefix*) (st *st0*) (e *seg*))
             (and (legal-exec (init-state) prefix)
                  (equal st (cl-run (init-state) prefix))
                  (complete-segment-p st e))))
  :hints (("Goal" :use (prefix-legal-and-reaches-st0 segment-complete)))
  :rule-classes nil)

; the reordering is not the identity: a postrecording input of 1 precedes
; prerecording inputs of 2
(defthm reordering-is-nontrivial
  (implies (sys-hyps)
           (and (equal (pre-inputs (segment-target *st0* *seg*) *st0* *seg*)
                       (quote ((1 :checkpoint) (2 :receive 1) (2 :receive 1))))
                (equal (post-inputs (segment-target *st0* *seg*) *st0* *seg*)
                       (quote ((1 :compute) (1 :receive 2) (1 :receive 2))))))
  :rule-classes nil)

; the snapshot is the expected Chandy-Lamport one: 1 saved a1 and recorded m2
; in flight on 2->1; 2 saved its state after receiving m1, with 1->2 empty
(defthm snapshot-contents
  (implies (sys-hyps)
           (let* ((s2 (cl-run *st0* *seg*))
                  (sid (quote (1 . 0))))
             (and (equal (g :state (g sid (g :snaps (ps-of 1 s2)))) (quote a1))
                  (equal (g 2 (g :chans (g sid (g :snaps (ps-of 1 s2))))) (quote (m2)))
                  (equal (g :state (g sid (g :snaps (ps-of 2 s2))))
                         (app-receive 2 1 (quote m1) (quote a2)))
                  (equal (g 1 (g :chans (g sid (g :snaps (ps-of 2 s2))))) nil))))
  :rule-classes nil)

; non-examples: a segment that runs past completion, and one that stops early
(defthm not-segment-overlong
  (implies (sys-hyps)
           (not (complete-segment-p *st0* (append *seg* (quote ((2 :compute)))))))
  :rule-classes nil)

(defthm not-segment-short
  (implies (sys-hyps)
           (not (complete-segment-p *st0* (butlast *seg* 1))))
  :rule-classes nil)

; non-example: a segment must start with a checkpoint initiation
(defthm not-segment-no-initiation
  (implies (sys-hyps)
           (not (complete-segment-p *st0* (cdr *seg*))))
  :rule-classes nil)
