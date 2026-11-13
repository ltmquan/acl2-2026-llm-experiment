(in-package "ACL2")

;;; ===== from monjil-ray/model.lisp =====
;;; monjil-ray/model.lisp, lines 104-104
(include-book "misc/records" :dir :system)

;;; monjil-ray/model.lisp, lines 50-53
(defun memberp (e l)
  (cond ((endp l) nil)
        ((equal e (first l)) t)
        (t (memberp e (rest l)))))

;;; monjil-ray/model.lisp, lines 56-59
(defun subset (x y)
  (cond ((endp x) t)
        (t (and (memberp (first x) y)
                (subset (rest x) y)))))

;;; monjil-ray/model.lisp, lines 62-65
(defun uniquep (x)
  (if (endp x) t
    (and (not (memberp (first x) (rest x)))
         (uniquep (rest x)))))

;;; monjil-ray/model.lisp, lines 83-85
(defun snoc (x e)
  (if (endp x) (list e)
    (cons (first x) (snoc (rest x) e))))

;;; monjil-ray/model.lisp, lines 90-96
(defun remove-from-list (x e)
  (if (endp x)
      nil
    (if (equal e (first x))
        (remove-from-list (rest x) e)
      (cons (first x)
            (remove-from-list (rest x) e)))))

;;; monjil-ray/model.lisp, lines 111-111
(defmacro procs     (s) `(g :procs ,s))

;;; monjil-ray/model.lisp, lines 112-112
(defmacro channels  (s) `(g :channels ,s))

;;; monjil-ray/model.lisp, lines 113-113
(defmacro proc-ids  (s) `(g :proc-ids ,s))

;;; monjil-ray/model.lisp, lines 117-117
(defmacro local-state           (p) `(g :local-state ,p))

;;; monjil-ray/model.lisp, lines 118-118
(defmacro channel-state (i j chans) `(g ,i (g ,j ,chans)))

;;; monjil-ray/model.lisp, lines 121-121
(defmacro nbrs-to               (p) `(g :nbrs-to ,p))

;;; monjil-ray/model.lisp, lines 122-122
(defmacro nbrs-from             (p) `(g :nbrs-from ,p))

;;; monjil-ray/model.lisp, lines 127-127
(defmacro pid   (input) `(g :pid ,input))

;;; monjil-ray/model.lisp, lines 128-128
(defmacro ttype (input) `(g :ttype ,input))

;;; monjil-ray/model.lisp, lines 129-129
(defmacro sender (input) `(g :sender ,input))

;;; monjil-ray/model.lisp, lines 134-138
(defun update-macro (upds result)
  (declare (xargs :guard (keyword-value-listp upds)))
  (if (endp upds) result
    (update-macro (cddr upds)
                  (list 's (car upds) (cadr upds) result))))

;;; monjil-ray/model.lisp, lines 140-142
(defmacro update (old &rest updates)
  (declare (xargs :guard (keyword-value-listp updates)))
  (update-macro updates old))

;;; monjil-ray/model.lisp, lines 144-144
(defmacro >st (&rest upds) `(update st ,@upds))

;;; monjil-ray/model.lisp, lines 145-145
(defmacro >p  (&rest upds) `(update p  ,@upds))

;;; monjil-ray/model.lisp, lines 146-146
(defmacro >_ (&rest upds) `(update nil ,@upds))

;;; monjil-ray/model.lisp, lines 150-153
(defmacro >channel (i j val channels)
  `(s ,j
      (s ,i ,val (g ,j ,channels))
      ,channels))

;;; monjil-ray/model.lisp, lines 155-158
(defmacro append-to-record-list (key val record)
  `(let* ((existing (g ,key ,record))
          (updated (append existing (list ,val))))
     (s ,key updated ,record)))

;;; monjil-ray/model.lisp, lines 163-163
(defmacro proc-status           (p) `(g :proc-status ,p))

;;; monjil-ray/model.lisp, lines 164-164
(defmacro waiting-recovery-from (p) `(g :waiting-recovery-from ,p))

;;; monjil-ray/model.lisp, lines 165-165
(defmacro counter               (p) `(g :counter ,p))

;;; monjil-ray/model.lisp, lines 172-172
(defmacro snapshot-ids          (p) `(g :snapshot-ids ,p))

;;; monjil-ray/model.lisp, lines 175-175
(defmacro snapshots             (p) `(g :snapshots ,p))

;;; monjil-ray/model.lisp, lines 178-178
(defmacro snapshot-entry    (sid p) `(g ,sid (snapshots ,p)))

;;; monjil-ray/model.lisp, lines 182-182
(defmacro sid (msg) `(g :sid ,msg))

;;; monjil-ray/model.lisp, lines 185-185
(defmacro msg-type (msg) `(g :msg-type ,msg))

;;; monjil-ray/model.lisp, lines 189-190
(defmacro snapshot-status (entry)
  `(g :status ,entry))

;;; monjil-ray/model.lisp, lines 193-194
(defmacro snapshot-local-snap-shot (entry)
  `(g :local-snap-shot ,entry))

;;; monjil-ray/model.lisp, lines 197-198
(defmacro snapshot-channel-snapshots (entry)
  `(g :channel-snapshots ,entry))

;;; monjil-ray/model.lisp, lines 202-203
(defmacro snapshot-waiting-marker-from (entry)
  `(g :waiting-marker-from ,entry))

;;; monjil-ray/model.lisp, lines 211-218
(defun make-snapshot-entry (local-snap-shot waiting-marker-from j)
  (let ((cs (if j
                (s j nil nil)
              nil)))
    (>_ :status :checkpointing
        :local-snap-shot local-snap-shot
        :channel-snapshots cs
        :waiting-marker-from waiting-marker-from)))

;;; monjil-ray/model.lisp, lines 221-224
(defun add-snapshot-id (sid ids)
  (if (memberp sid ids)
      ids
    (cons  sid ids)))

;;; monjil-ray/model.lisp, lines 227-230
(defun set-snapshot-entry (sid entry p)
  (let* ((snaps (snapshots p))
         (snaps (s sid entry snaps)))
    (s :snapshots snaps p)))

;;; monjil-ray/model.lisp, lines 233-239
(defun install-snapshot-entry (sid entry p)
  (let* ((snapshot-ids   (add-snapshot-id sid (snapshot-ids p)))
         (snapshots (snapshots p))
         (snapshots (s sid entry snapshots)))
    (update p
            :snapshot-ids snapshot-ids
            :snapshots snapshots)))

;;; monjil-ray/model.lisp, lines 263-291
(encapsulate
 (((update-local-state-rcv * * *) => *)
  ((update-local-state-normal *) => *)
  ((message-to-send? * *) => *)
  ((create-compute-message * *) => *))
 (local
  (defun update-local-state-rcv (local-state msg nbr)
    (declare (ignore local-state msg nbr))
    nil))
 (local
  (defun update-local-state-normal (local-state)
    (declare (ignore local-state))
    nil))
 (local
  (defun message-to-send? (local-state nbr)
    (declare (ignore local-state nbr))
    nil))
 (local
  (defun create-compute-message (local-state nbr)
    (declare (ignore local-state nbr))
    (>_ :msg-type :normal)))
 (defthm msg-type-of-create-compute-message
   (equal (msg-type (create-compute-message local-state nbr))
          :normal)))

;;; monjil-ray/model.lisp, lines 294-297
(defun create-marker-message (local-state sid)
  (declare (ignore local-state))
  (>_ :msg-type :marker
      :sid sid))

;;; monjil-ray/model.lisp, lines 299-302
(defun create-recovery-message (local-state sid)
  (declare (ignore local-state))
  (>_ :msg-type :recovery
      :sid sid))

;;; monjil-ray/model.lisp, lines 325-329
(defun remove-message-from-channel (nbr i channels)
    (let* ((channel (channel-state nbr i channels))
           (channel (if channel (cdr channel) nil))
           (channels (>channel nbr i  channel channels)))
      channels))

;;; monjil-ray/model.lisp, lines 333-341
(defun send-msg-all-outgoing-channels (msg i nbrs channels)
  (cond ((endp nbrs) channels)
        (t
         (let* ((nbr      (first nbrs))
                (channels (send-msg-all-outgoing-channels msg i (rest nbrs) channels))
                (channel  (channel-state i nbr channels))
                (channel  (snoc channel msg))
                (channels (>channel i nbr channel channels)))
           channels))))

;;; monjil-ray/model.lisp, lines 343-353
(defun update-proc-for-first-marker-msg (p sid j)
  (let* ((nbrs-from           (nbrs-from p))
         (local-state         (local-state p))
         (waiting-marker-from (remove-from-list nbrs-from j))
         (entry               (make-snapshot-entry local-state
                                                   waiting-marker-from
                                                   j)))
    (install-snapshot-entry sid entry p)))

;;; monjil-ray/model.lisp, lines 355-374
(defun handle-first-marker-msg (st i j msg)
  (let* ((procs    (procs st))
         (p        (g i procs))
         (nbrs-to  (nbrs-to p))
         (channels (channels st))
         (sid      (sid msg))
         (channels (remove-message-from-channel j i channels))
         (p        (update-proc-for-first-marker-msg p sid j))
         (channels (send-msg-all-outgoing-channels msg i nbrs-to channels))
         (procs    (s i p procs)))
    (>st :procs procs
         :channels channels)))

;;; monjil-ray/model.lisp, lines 376-392
(defun update-proc-for-non-first-marker-msg (p sid j)
  (let* ((entry               (snapshot-entry sid p))
         (waiting-marker-from (snapshot-waiting-marker-from entry))
         (waiting-marker-from (remove-from-list waiting-marker-from j))
         (status              (if (endp waiting-marker-from)
                                  :done
                                (snapshot-status entry)))
         (entry               (update entry
                                      :waiting-marker-from waiting-marker-from
                                      :status status)))
    (set-snapshot-entry sid entry p)))

;;; monjil-ray/model.lisp, lines 394-409
(defun handle-non-first-marker-msg (st i j msg)
  (let* ((sid      (sid msg))
         (procs    (procs st))
         (p        (g i procs))
         (channels (channels st))
         (p        (update-proc-for-non-first-marker-msg p sid j))
         (channels (remove-message-from-channel j i channels))
         (procs    (s i p procs)))
    (>st :procs procs
         :channels channels)))

;;; monjil-ray/model.lisp, lines 411-418
(defun handle-marker-msg (st i j msg)
  (let* ((sid (sid msg))
         (procs (procs st))
         (p (g i procs))
         (snapshot-ids (snapshot-ids p)))
    (if (memberp sid snapshot-ids)
        (handle-non-first-marker-msg st i j msg)
      (handle-first-marker-msg st i j msg))))

;;; monjil-ray/model.lisp, lines 440-456
(defun replay-msgs-on-channel (local-state msgs j)
  (cond ((endp msgs)
         local-state)
        ((not (first msgs))
         (replay-msgs-on-channel
          local-state
          (rest msgs)
          j))
        (t
         (replay-msgs-on-channel
          (update-local-state-rcv local-state (first msgs) j)
          (rest msgs)
          j))))

;;; monjil-ray/model.lisp, lines 459-468
(defun replay-channel-snapshots (local-state channel-snaps nbrs-from)
  (cond ((endp nbrs-from)
         local-state)
        (t
         (let* ((ch          (first nbrs-from))
                (msgs        (g ch channel-snaps))
                (local-state (replay-msgs-on-channel local-state msgs ch)))
           (replay-channel-snapshots local-state
                                     channel-snaps
                                     (rest nbrs-from))))))

;;; monjil-ray/model.lisp, lines 470-482
(defun update-proc-for-first-recovery-msg (p sid j)
  (let* ((nbrs-from     (nbrs-from p))
         (entry         (snapshot-entry sid p))
         (local-state   (snapshot-local-snap-shot entry))
         (channel-snaps (snapshot-channel-snapshots entry))
         (local-state   (replay-channel-snapshots local-state
                                                  channel-snaps
                                                  nbrs-from))
         (waiting       (remove-from-list nbrs-from j)))
    (update p
            :local-state local-state
            :proc-status :recovering
            :waiting-recovery-from waiting)))

;;; monjil-ray/model.lisp, lines 484-499
(defun handle-first-recovery-msg (st i j msg)
  (let* ((sid           (sid msg))
         (procs         (procs st))
         (channels      (channels st))
         (p             (g i procs))
         (nbrs-to       (nbrs-to p))
         (channels      (remove-message-from-channel j i channels))
         (channels      (send-msg-all-outgoing-channels msg i nbrs-to channels))
         (p             (update-proc-for-first-recovery-msg p sid j))
         (procs         (s i p procs)))
    (>st :procs procs
         :channels channels)))

;;; monjil-ray/model.lisp, lines 501-509
(defun update-proc-for-non-first-recovery-msg (p j)
  (let* ((waiting     (waiting-recovery-from p))
         (waiting     (remove-from-list waiting j))
         (proc-status (if (endp waiting)
                          :normal
                        :recovering)))
    (update p
            :proc-status proc-status
            :waiting-recovery-from waiting)))

;;; monjil-ray/model.lisp, lines 511-520
(defun handle-non-first-recovery-msg (st i j msg)
  (declare (ignore msg))
  (let* ((procs    (procs st))
         (channels (channels st))
         (p        (g i procs))
         (channels (remove-message-from-channel j i channels))
         (p        (update-proc-for-non-first-recovery-msg p j))
         (procs    (s i p procs)))
    (>st :procs procs
         :channels channels)))

;;; monjil-ray/model.lisp, lines 541-547
(defun handle-recovery-msg (st i j msg)
  (let* ((procs       (procs st))
         (p           (g i procs))
         (proc-status (proc-status p)))
    (if (equal proc-status :normal)
        (handle-first-recovery-msg st i j msg)
	(handle-non-first-recovery-msg st i j msg))))

;;; monjil-ray/model.lisp, lines 553-570
(defun record-msg-in-snapshots (snapshots snapshot-ids j msg)
  (cond ((endp snapshot-ids)
         snapshots)
        (t
         (let* ((sid       (first snapshot-ids))
                (rest-ids  (rest snapshot-ids))
                (snapshots (record-msg-in-snapshots snapshots rest-ids j msg))
                (entry     (g sid snapshots))
                (status    (snapshot-status entry))
                (waiting   (snapshot-waiting-marker-from entry)))
           (if (and (equal status :checkpointing)
                    (memberp j waiting))
               (let* ((cs        (snapshot-channel-snapshots entry))
                      (cs        (append-to-record-list j msg cs))
                      (entry     (update entry :channel-snapshots cs))
                      (snapshots (s sid entry snapshots)))
                 snapshots)
               snapshots)))))

;;; monjil-ray/model.lisp, lines 572-583
(defun update-proc-for-normal-msg-core (p j msg)
  (let* ((local-state  (local-state p))
         (local-state  (update-local-state-rcv local-state msg j))
         (snapshot-ids (snapshot-ids p))
         (snapshots    (snapshots p))
         (snapshots    (record-msg-in-snapshots snapshots
                                                snapshot-ids
                                                j
                                                msg)))
    (update p
            :local-state local-state
            :snapshots snapshots)))

;;; monjil-ray/model.lisp, lines 585-596
(defun handle-normal-msg-core (st i j msg)
  (let* ((procs    (procs st))
         (channels (channels st))
         (p        (g i procs))
         (p        (update-proc-for-normal-msg-core p j msg))
         (channels (remove-message-from-channel j i channels))
         (procs    (s i p procs)))
    (>st :procs procs
         :channels channels)))

;;; monjil-ray/model.lisp, lines 598-603
(defun ignore-normal-msg (st i j msg)
  (declare (ignore msg))
  (let* ((channels (channels st))
         (channels (remove-message-from-channel j i channels)))
    (>st :procs (procs st)
         :channels channels)))

;;; monjil-ray/model.lisp, lines 605-613
(defun handle-normal-msg (st i j msg)
  (let* ((procs   (procs st))
         (p       (g i procs))
         (status  (proc-status p))
         (waiting (waiting-recovery-from p)))
    (if (and (equal status :recovering)
             (memberp j waiting))
        (ignore-normal-msg st i j msg)
	(handle-normal-msg-core st i j msg))))

;;; monjil-ray/model.lisp, lines 620-624
(defun get-msg-from-channel (nbr i channels)
  (let ((channel (channel-state nbr i channels)))
    (if (consp channel)
        (first channel)
      nil)))

;;; monjil-ray/model.lisp, lines 638-648
(defun step-rcv (st i j)
  (let* ((channels (channels st))
         (msg      (get-msg-from-channel j i channels)))
    (if (not msg)
        st
      (let ((msg-type (msg-type msg)))
        (case msg-type
          (:normal   (handle-normal-msg st i j msg))
          (:marker   (handle-marker-msg st i j msg))
          (:recovery (handle-recovery-msg st i j msg))
          (otherwise st))))))

;;; monjil-ray/model.lisp, lines 665-685
(defun send-compute-message (local-state i nbrs channels)
  (cond
   ((endp nbrs)
    channels)
   ((message-to-send? local-state (first nbrs))
    (let* ((nbr      (first nbrs))
           (channel  (channel-state i nbr channels))
           (msg      (create-compute-message local-state nbr))
           (channel  (snoc channel msg))
           (channels (>channel i nbr channel channels)))
      (send-compute-message local-state
                            i
                            (rest nbrs)
                            channels)))
   (t
    (send-compute-message local-state
                          i
                          (rest nbrs)
                          channels))))

;;; monjil-ray/model.lisp, lines 687-699
(defun step-normal (st i)
(let* ((procs (procs st))
       (channels (channels st))
       (p (g i procs))
       (nbrs-to (nbrs-to p))
       (local (local-state p))
       (channels (send-compute-message local i nbrs-to channels))
       (local (update-local-state-normal local))
       (p     (>p  :local-state local))
       (procs (s i p procs))
       (st (>st :procs procs
         	:channels channels)))
       st))

;;; monjil-ray/model.lisp, lines 705-715
(defun start-checkpoint-helper (procs i)
  (let* ((p     (g i procs))
         (sid   (list i (counter p)))
         (entry (make-snapshot-entry
                 (local-state p)
                 (nbrs-from p)
                 nil))
         (p-new (s :counter
                   (+ 1 (counter p))
                   (install-snapshot-entry sid entry p))))
    (s i p-new procs)))

;;; monjil-ray/model.lisp, lines 717-737
(defun step-checkpoint (st i)
  (let* ((procs       (procs st))
         (channels    (channels st))
         (p           (g i procs))
         (sid         (list i (counter p)))
         (local-state (local-state p))
         (nbrs-to     (nbrs-to p))
         (procs       (start-checkpoint-helper procs i))
         (msg         (create-marker-message local-state sid))
         (channels    (send-msg-all-outgoing-channels msg i nbrs-to channels))
         (st          (>st :procs procs
                           :channels channels)))
    st))

;;; monjil-ray/model.lisp, lines 741-747
(defun step-crash (st i)
  (let* ((procs (procs st))
         (p     (g i procs))
         (p     (update p :proc-status :crashed))
         (procs (s i p procs)))
    (>st :procs procs
         :channels (channels st))))

;;; monjil-ray/model.lisp, lines 753-761
(defun recovery-local-state-after-replay (p)
  (let* ((nbrs-from     (nbrs-from p))
         (sid           (car (snapshot-ids p)))
         (entry         (snapshot-entry sid p))
         (local-state   (snapshot-local-snap-shot entry))
         (channel-snaps (snapshot-channel-snapshots entry)))
    (replay-channel-snapshots local-state
                              channel-snaps
                              nbrs-from)))

;;; monjil-ray/model.lisp, lines 763-771
(defun start-recovery-helper (procs i)
  (let* ((p           (g i procs))
         (nbrs-from   (nbrs-from p))
         (local-state (recovery-local-state-after-replay p))
         (p-new       (update p
                              :local-state local-state
                              :proc-status :recovering
                              :waiting-recovery-from nbrs-from)))
    (s i p-new procs)))

;;; monjil-ray/model.lisp, lines 773-792
(defun step-recover (st i)
  (let* ((procs         (procs st))
         (channels      (channels st))
         (p             (g i procs))
         (nbrs-to       (nbrs-to p))
         (sid           (car (snapshot-ids p)))
         (local-state   (recovery-local-state-after-replay p))
         (procs         (start-recovery-helper procs i))
         (msg           (create-recovery-message local-state sid))
         (channels      (send-msg-all-outgoing-channels msg i nbrs-to channels))
         (st            (>st :procs procs
                             :channels channels)))
    st))

;;; monjil-ray/model.lisp, lines 797-809
(defun system-step (st input)
  (let* (
	 (i (pid input))
         (j (sender input))
         (ttype (ttype input)))
    (case ttype
      (:receive          (step-rcv st i j))
      (:normal           (step-normal st i))
      (:start-checkpoint (step-checkpoint st i))
      (:crash            (step-crash st i))
      (:recover          (step-recover st i))
      (:nop               st)
      (t st))))

;;; monjil-ray/model.lisp, lines 873-878
(defun run-imp (st inputs)
  (if (endp inputs)
      st
    (run-imp
     (system-step st (first inputs))
     (rest inputs))))

;;; monjil-ray/model.lisp, lines 909-916
(defun any-checkpointing-snapshot-in-ids-p (snapshot-ids p)
  (cond ((endp snapshot-ids)
         nil)
        (t
         (let* ((sid   (first snapshot-ids))
                (entry (snapshot-entry sid p)))
           (or (equal (snapshot-status entry) :checkpointing)
               (any-checkpointing-snapshot-in-ids-p (rest snapshot-ids) p))))))

;;; monjil-ray/model.lisp, lines 918-919
(defun proc-has-checkpointing-snapshot-p (p)
  (any-checkpointing-snapshot-in-ids-p (snapshot-ids p) p))

;;; monjil-ray/model.lisp, lines 921-928
(defun any-proc-checkpointing-p (proc-ids procs)
  (cond ((endp proc-ids)
         nil)
        (t
         (let* ((pid (first proc-ids))
                (p   (g pid procs)))
           (or (proc-has-checkpointing-snapshot-p p)
               (any-proc-checkpointing-p (rest proc-ids) procs))))))

;;; monjil-ray/model.lisp, lines 930-933
(defun any-snapshot-checkpointing-p (st)
  (let* ((ids   (proc-ids st))
         (procs (procs st)))
    (any-proc-checkpointing-p ids procs)))

;;; monjil-ray/model.lisp, lines 935-942
(defun any-proc-recovering-p (proc-ids procs)
  (cond ((endp proc-ids)
         nil)
        (t
         (let* ((pid (first proc-ids))
                (p   (g pid procs)))
           (or (equal (proc-status p) :recovering)
               (any-proc-recovering-p (rest proc-ids) procs))))))

;;; monjil-ray/model.lisp, lines 944-947
(defun any-process-recovering-p (st)
  (let* ((ids   (proc-ids st))
         (procs (procs st)))
    (any-proc-recovering-p ids procs)))

;;; monjil-ray/model.lisp, lines 950-956
(defun some-proc-has-snapshot-id-p (sid ids procs)
  (if (endp ids)
      nil
    (let* ((i (first ids))
           (p (g i procs)))
      (or (memberp sid (snapshot-ids p))
          (some-proc-has-snapshot-id-p sid (rest ids) procs)))))

;;; monjil-ray/model.lisp, lines 958-964
(defun all-procs-have-snapshot-id-p (sid ids procs)
  (if (endp ids)
      t
    (let* ((i (first ids))
           (p (g i procs)))
      (and (memberp sid (snapshot-ids p))
           (all-procs-have-snapshot-id-p sid (rest ids) procs)))))

;;; monjil-ray/model.lisp, lines 970-1042
(defun legal-inputp (st input)
  (let* ((tp       (ttype input))
         (i        (pid input))
         (j        (sender input))
         (ids      (proc-ids st))
         (procs    (procs st))
         (channels (channels st)))
    (cond
     ((equal tp :nop)
      t)
     ((equal tp :normal)
      (memberp i ids))
     ((equal tp :receive)
      (and
       (memberp i ids)
       (memberp j ids)
       (memberp
        j
        (nbrs-from
         (g i procs)))
       (consp
        (channel-state
         j
         i
         channels))))
     ((equal tp :start-checkpoint)
      (and
       (memberp i ids)
       (not
        (any-process-recovering-p st))))
     ((equal tp :crash)
      (and
       (memberp i ids)
       (not
        (any-process-recovering-p st))
       (not
        (any-snapshot-checkpointing-p st))))
     ((equal tp :recover)
      (and
       (memberp i ids)
       (not
        (any-process-recovering-p st))
       (not
        (any-snapshot-checkpointing-p st))
       (all-procs-have-snapshot-id-p
        (car
         (snapshot-ids
          (g i procs)))
        ids
        procs)))
     (t nil))))

;;; monjil-ray/model.lisp, lines 1046-1053
(defun legal-input-sequencep (st inputs)
  (declare (xargs :measure (acl2-count inputs)))
  (if (endp inputs)
      t
    (and (legal-inputp st (first inputs))
         (legal-input-sequencep
          (system-step st (first inputs))
          (rest inputs)))))

;;; monjil-ray/model.lisp, lines 1408-1433
(defun cl-checkpoint-control-equivalent-p
    (ids procs-1 procs-2)
  (declare
   (xargs :measure (acl2-count ids)))
  (if (endp ids)
      t
    (let* ((i  (first ids))
           (p1 (g i procs-1))
           (p2 (g i procs-2)))
      (and
       (equal
        (counter p1)
        (counter p2))
       (equal
        (snapshot-ids p1)
        (snapshot-ids p2))
       (cl-checkpoint-control-equivalent-p
        (rest ids)
        procs-1
        procs-2)))))

;;; monjil-ray/model.lisp, lines 1437-1445
(defun proc-equivalent-p (imp-p spec-p)
  (and
   (equal (local-state imp-p)
          (local-state spec-p))
   (equal (nbrs-to imp-p)
          (nbrs-to spec-p))
   (equal (nbrs-from imp-p)
          (nbrs-from spec-p))))

;;; monjil-ray/model.lisp, lines 1447-1458
(defun procs-equivalent-p (ids imp-procs spec-procs)
  (if (endp ids)
      t
    (and
     (proc-equivalent-p
      (g (first ids) imp-procs)
      (g (first ids) spec-procs))
     (procs-equivalent-p
      (rest ids)
      imp-procs
      spec-procs))))

;;; monjil-ray/model.lisp, lines 1462-1479
(defun state-equivalent-p (st-1 st-2)
  (and
   (equal
    (proc-ids st-1)
    (proc-ids st-2))
   (equal
    (channels st-1)
    (channels st-2))
   (procs-equivalent-p
    (proc-ids st-1)
    (procs st-1)
    (procs st-2))
   (cl-checkpoint-control-equivalent-p
    (proc-ids st-1)
   (procs st-1)
   (procs st-2))))

;;; ===== from monjil-ray/scan.lisp =====
;;; monjil-ray/scan.lisp, lines 26-30
(defun current-msg-for-receive (input st)
  (let* ((i        (pid input))
         (j        (sender input))
         (channels (channels st)))
    (get-msg-from-channel j i channels)))

;;; monjil-ray/scan.lisp, lines 44-45
(defmacro cm-sid (m)
  `(g :sid ,m))

;;; monjil-ray/scan.lisp, lines 47-48
(defun cm-proc-ids (m)
  (g :proc-ids m))

;;; monjil-ray/scan.lisp, lines 50-51
(defun cm-cut-not-taken (m)
  (g :cut-not-taken m))

;;; monjil-ray/scan.lisp, lines 53-54
(defun cm-waiting-marker-from (m)
  (g :waiting-marker-from m))

;;; monjil-ray/scan.lisp, lines 73-74
(defun cm-after-cut-input-sequence (m)
  (g :after-cut-input-sequence m))

;;; monjil-ray/scan.lisp, lines 77-78
(defun cm-before-cut-input-sequence (m)
  (g :before-cut-input-sequence m))

;;; monjil-ray/scan.lisp, lines 81-82
(defun cm-waiting-marker-for (m i)
  (g i (cm-waiting-marker-from m)))

;;; monjil-ray/scan.lisp, lines 84-87
(defun cm-set-waiting-marker-for (m i xs)
  (s :waiting-marker-from
     (s i xs (cm-waiting-marker-from m))
     m))

;;; monjil-ray/scan.lisp, lines 89-90
(defun cm-cut-not-taken-p (m i)
  (memberp i (cm-cut-not-taken m)))

;;; monjil-ray/scan.lisp, lines 92-95
(defun cm-remove-cut-not-taken (m i)
  (s :cut-not-taken
     (remove1-equal i (cm-cut-not-taken m))
     m))

;;; monjil-ray/scan.lisp, lines 98-103
(defun cm-add-after-cut-input-sequence (m input)
  (s :after-cut-input-sequence
     (append
      (cm-after-cut-input-sequence m)
      (list input))
     m))

;;; monjil-ray/scan.lisp, lines 106-111
(defun cm-add-before-cut-input-sequence (m input)
  (s :before-cut-input-sequence
     (append
      (cm-before-cut-input-sequence m)
      (list input))
     m))

;;; monjil-ray/scan.lisp, lines 116-121
(defun make-empty-waiting-marker-from (proc-ids)
  (if (endp proc-ids)
      nil
    (s (first proc-ids)
       nil
       (make-empty-waiting-marker-from (rest proc-ids)))))

;;; monjil-ray/scan.lisp, lines 125-150
(defun make-cut-meta (sid initiator st)
  (declare (ignore initiator))
  (let* (
         (proc-ids (proc-ids st))
         (m        nil)
         (m        (s :after-cut-input-sequence nil m))
         (m        (s :before-cut-input-sequence nil m))
         (m        (s :waiting-marker-from
                      (make-empty-waiting-marker-from proc-ids)
                      m))
         (m        (s :cut-not-taken
                      proc-ids
                      m))
         (m        (s :proc-ids proc-ids m))
         (m        (s :sid sid m)))
    m))

;;; monjil-ray/scan.lisp, lines 156-160
(defun all-waiting-marker-empty-p (ids m)
  (if (endp ids)
      t
    (and (endp (cm-waiting-marker-for m (first ids)))
         (all-waiting-marker-empty-p (rest ids) m))))

;;; monjil-ray/scan.lisp, lines 162-168
(defun checkpoint-collection-complete-p (m)
  (if (equal (cm-sid m) :init)
      t
    (and (endp (cm-cut-not-taken m))
         (all-waiting-marker-empty-p
          (cm-proc-ids m)
          m))))

;;; monjil-ray/scan.lisp, lines 186-200
(defun process-cut-marker-receive (i j st m)
  (let ((procs (procs st)))
    (if (cm-cut-not-taken-p m i)
        (let* ((p    (g i procs))
               (nbrs (nbrs-from p))
               (ws   (remove1-equal j nbrs))
               (m    (cm-remove-cut-not-taken m i)))
          (cm-set-waiting-marker-for m i ws))
      (cm-set-waiting-marker-for
       m i
       (remove1-equal j
                      (cm-waiting-marker-for m i))))))

;;; monjil-ray/scan.lisp, lines 204-221
(defun process-cut-receive (input st m)
  (let* ((i   (pid input))
         (j   (sender input))
         (msg (current-msg-for-receive input st))
         (sid (cm-sid m)))
    (cond
     ((and (equal (msg-type msg) :marker)
           (equal (sid msg) sid))
      (process-cut-marker-receive i j st m))
     ((equal (msg-type msg) :normal)
      m)
     (t m))))

;;; monjil-ray/scan.lisp, lines 225-243
(defun process-cut-checkpoint (input st m)
  (let* ((i          (pid input))
         (p          (g i (procs st)))
         (input-sid  (list i (counter p)))
         (target-sid (cm-sid m)))
    (if (equal input-sid target-sid)
        (let ((m (cm-remove-cut-not-taken m i)))
          (cm-set-waiting-marker-for
           m
           i
           (nbrs-from p)))
      m)))

;;; monjil-ray/scan.lisp, lines 245-274
(defun process-cut-step (input st m)
  (let*
      ((i
        (pid input))
       (m
        (if
            (cm-cut-not-taken-p m i)
            (cm-add-before-cut-input-sequence
             m input)
          (cm-add-after-cut-input-sequence
           m input))))
    (cond
     ((equal (ttype input) :start-checkpoint)
      (process-cut-checkpoint input st m))
     ((equal (ttype input) :normal)
       m)
     ((equal (ttype input) :receive)
      (process-cut-receive input st m))
     (t
      m))))

;;; monjil-ray/scan.lisp, lines 333-342
(defun scan-until-checkpoint-done (inputs st m)
  (declare (xargs :measure (acl2-count inputs)))
  (if (or (endp inputs)
          (checkpoint-collection-complete-p m))
      m
    (let* ((input   (first inputs))
           (next-m  (process-cut-step input st m))
           (next-st (system-step st input)))
      (scan-until-checkpoint-done
       (rest inputs) next-st next-m))))

;;; ===== from monjil-ray/good_state_inv.lisp =====
;;; monjil-ray/good_state_inv.lisp, lines 36-39
(defun good-proc-status-p (x)
  (or (equal x :normal)
      (equal x :crashed)
      (equal x :recovering)))

;;; monjil-ray/good_state_inv.lisp, lines 41-43
(defun good-snapshot-status-p (x)
  (or (equal x :checkpointing)
      (equal x :done)))

;;; monjil-ray/good_state_inv.lisp, lines 45-51
(defun good-snapshot-id-p (sid ids)
  (or (equal sid :init)
      (and (consp sid)
           (consp (cdr sid))
           (endp (cddr sid))
           (memberp (car sid) ids)
           (natp (cadr sid)))))

;;; monjil-ray/good_state_inv.lisp, lines 53-57
(defun good-snapshot-ids-p (snapshot-ids ids)
  (if (endp snapshot-ids)
      t
    (and (good-snapshot-id-p (first snapshot-ids) ids)
         (good-snapshot-ids-p (rest snapshot-ids) ids))))

;;; monjil-ray/good_state_inv.lisp, lines 59-63
(defun good-snapshot-ids-list-p (snapshot-ids ids)
  (and (true-listp snapshot-ids)
       (uniquep snapshot-ids)
       (memberp :init snapshot-ids)
       (good-snapshot-ids-p snapshot-ids ids)))

;;; monjil-ray/good_state_inv.lisp, lines 72-80
(defun good-msg-p (msg ids procs)
  (let ((tp (msg-type msg)))
    (cond ((equal tp :normal)
           t)
          ((equal tp :marker)
           (some-proc-has-snapshot-id-p (sid msg) ids procs))
          ((equal tp :recovery)
           (all-procs-have-snapshot-id-p (sid msg) ids procs))
          (t nil))))

;;; monjil-ray/good_state_inv.lisp, lines 82-86
(defun good-msg-list-p (msgs ids procs)
  (if (endp msgs)
      t
    (and (good-msg-p (first msgs) ids procs)
         (good-msg-list-p (rest msgs) ids procs))))

;;; monjil-ray/good_state_inv.lisp, lines 107-108
(defun good-normal-msg-p (msg)
  (equal (msg-type msg) :normal))

;;; monjil-ray/good_state_inv.lisp, lines 113-117
(defun good-normal-msg-list-p (msgs)
  (if (endp msgs)
      t
    (and (good-normal-msg-p (first msgs))
         (good-normal-msg-list-p (rest msgs)))))

;;; monjil-ray/good_state_inv.lisp, lines 119-123
(defun good-channel-snapshot-record-p (nbrs-from-i cs)
  (if (endp nbrs-from-i)
      t
    (and (good-normal-msg-list-p (g (first nbrs-from-i) cs))
         (good-channel-snapshot-record-p (rest nbrs-from-i) cs))))

;;; monjil-ray/good_state_inv.lisp, lines 125-131
(defun good-snapshot-entry-p (entry nbrs-from-i)
  (and (good-snapshot-status-p (snapshot-status entry))
       (true-listp (snapshot-waiting-marker-from entry))
       (uniquep (snapshot-waiting-marker-from entry))
       (subset (snapshot-waiting-marker-from entry) nbrs-from-i)
       (good-channel-snapshot-record-p nbrs-from-i
                                       (snapshot-channel-snapshots entry))))

;;; monjil-ray/good_state_inv.lisp, lines 133-144
(defun good-snapshots-p (snapshot-ids p nbrs-from-i ids)
  (declare (irrelevant ids))
  (if (endp snapshot-ids)
      t
    (let* ((sid   (first snapshot-ids))
           (entry (snapshot-entry sid p)))
      (and
           (good-snapshot-entry-p entry nbrs-from-i)
           (good-snapshots-p (rest snapshot-ids)
                             p
                             nbrs-from-i
                             ids)))))

;;; monjil-ray/good_state_inv.lisp, lines 169-192
(defun good-proc-p (p ids)
  (let* ((nbrs-in  (nbrs-from p))
         (nbrs-out (nbrs-to p)))
    (and
     (true-listp nbrs-in)
     (true-listp nbrs-out)
     (uniquep nbrs-in)
     (uniquep nbrs-out)
     (subset nbrs-in ids)
     (subset nbrs-out ids)
     (good-proc-status-p (proc-status p))
     (natp (counter p))
     (true-listp (waiting-recovery-from p))
     (subset (waiting-recovery-from p) nbrs-in)
     (good-snapshot-ids-list-p (snapshot-ids p) ids)
     (good-snapshots-p
      (snapshot-ids p)
      p
      nbrs-in
      ids))))

;;; monjil-ray/good_state_inv.lisp, lines 194-200
(defun good-procs-p (ids procs all-ids)
  (if (endp ids)
      t
    (let* ((i (first ids))
           (p (g i procs)))
      (and (good-proc-p  p  all-ids)
           (good-procs-p (rest ids) procs all-ids)))))

;;; monjil-ray/good_state_inv.lisp, lines 202-206
(defun good-channel-p (src dst channels ids procs)
  (let ((p (g src procs)))
    (if (memberp dst (nbrs-to p))
        (good-msg-list-p (channel-state src dst channels) ids procs)
      (equal (channel-state src dst channels) nil))))

;;; monjil-ray/good_state_inv.lisp, lines 208-212
(defun good-channel-row-p (src dsts channels ids procs)
  (if (endp dsts)
      t
    (and (good-channel-p src (first dsts) channels ids procs)
         (good-channel-row-p src (rest dsts) channels ids procs))))

;;; monjil-ray/good_state_inv.lisp, lines 214-218
(defun good-channels-p (srcs dsts channels ids procs)
  (if (endp srcs)
      t
    (and (good-channel-row-p (first srcs) dsts channels ids procs)
         (good-channels-p (rest srcs) dsts channels ids procs))))

;;; monjil-ray/good_state_inv.lisp, lines 220-232
(defun nbrs-from-to-consistent-for-one-dst-p (i srcs procs)
  (if (endp srcs)
      t
    (and
     (implies
      (memberp (first srcs)
               (nbrs-from (g i procs)))
      (memberp i
               (nbrs-to (g (first srcs) procs))))
     (nbrs-from-to-consistent-for-one-dst-p
      i
      (rest srcs)
      procs))))

;;; monjil-ray/good_state_inv.lisp, lines 234-245
(defun nbrs-from-to-consistent-p (dsts srcs procs)
  (if (endp dsts)
      t
    (and
     (nbrs-from-to-consistent-for-one-dst-p
      (first dsts)
      srcs
      procs)
     (nbrs-from-to-consistent-p
      (rest dsts)
      srcs
      procs))))

;;; monjil-ray/good_state_inv.lisp, lines 247-259
(defun nbrs-to-from-consistent-for-one-src-p (j dsts procs)
  (if (endp dsts)
      t
    (and
     (implies
      (memberp (first dsts)
               (nbrs-to (g j procs)))
      (memberp j
               (nbrs-from (g (first dsts) procs))))
     (nbrs-to-from-consistent-for-one-src-p
      j
      (rest dsts)
      procs))))

;;; monjil-ray/good_state_inv.lisp, lines 261-272
(defun nbrs-to-from-consistent-p (srcs dsts procs)
  (if (endp srcs)
      t
    (and
     (nbrs-to-from-consistent-for-one-src-p
      (first srcs)
      dsts
      procs)
     (nbrs-to-from-consistent-p
      (rest srcs)
      dsts
      procs))))

;;; monjil-ray/good_state_inv.lisp, lines 275-279
(defun checkpoint-sid-p (x)
  (and
   (consp x)
   (consp (cdr x))
   (endp (cddr x))))

;;; monjil-ray/good_state_inv.lisp, lines 337-371
(defun stored-sids-for-initiator-have-smaller-counters-p
  (initiator initiator-counter sids)
 (declare
  (xargs :measure (acl2-count sids)))
 (if (endp sids)
     t
  (let ((sid (first sids)))
     (and
      (cond
       ((equal sid :init)
        t)
       ((not (checkpoint-sid-p sid))
        nil)
       ((equal (first sid) initiator)
        (< (second sid)
           initiator-counter))
       (t
        t))
      (stored-sids-for-initiator-have-smaller-counters-p
       initiator
       initiator-counter
       (rest sids))))))

;;; monjil-ray/good_state_inv.lisp, lines 380-404
(defun all-stored-sids-for-initiator-have-smaller-counters-p
   (initiator ids procs)
 (declare
  (xargs :measure (acl2-count ids)))
 (if (endp ids)
     t
   (let* ((holder            (first ids))
          (holder-p          (g holder procs))
          (initiator-p       (g initiator procs))
          (initiator-counter (counter initiator-p)))
     (and
      (stored-sids-for-initiator-have-smaller-counters-p
       initiator
       initiator-counter
       (snapshot-ids holder-p))
      (all-stored-sids-for-initiator-have-smaller-counters-p
       initiator
       (rest ids)
       procs)))))

;;; monjil-ray/good_state_inv.lisp, lines 411-430
(defun all-initiators-stored-sids-have-smaller-counters-p
   (initiators ids procs)
 (declare
  (xargs :measure (acl2-count initiators)))
 (if (endp initiators)
     t
   (and
    (all-stored-sids-for-initiator-have-smaller-counters-p
     (first initiators)
     ids
     procs)
    (all-initiators-stored-sids-have-smaller-counters-p
     (rest initiators)
     ids
     procs))))

;;; monjil-ray/good_state_inv.lisp, lines 433-457
(defun good-state-p (st)
  (let* ((ids      (proc-ids st))
         (procs    (procs st))
         (channels (channels st)))
    (and (true-listp ids)
         (uniquep ids)
	 (all-initiators-stored-sids-have-smaller-counters-p
	  ids
	  ids
	  procs)
         (good-procs-p ids procs ids)
         (nbrs-from-to-consistent-p ids ids procs)
         (nbrs-to-from-consistent-p ids ids procs)
         (good-channels-p ids ids channels ids procs))))

;;; ===== from monjil-ray/recovery_inv.lisp =====
;;; monjil-ray/recovery_inv.lisp, lines 186-200
(defun no-recovery-msgs-in-channel-p (channel)
  (declare
   (xargs :measure (acl2-count channel)))
  (if (endp channel)
      t
    (and
     (not
      (equal
       (msg-type (first channel))
       :recovery))
     (no-recovery-msgs-in-channel-p
      (rest channel)))))

;;; monjil-ray/recovery_inv.lisp, lines 208-227
(defun no-recovery-msgs-for-dsts-p
    (src dsts channels)
  (declare
   (xargs :measure (acl2-count dsts)))
  (if (endp dsts)
      t
    (and
     (no-recovery-msgs-in-channel-p
      (channel-state
       src
       (first dsts)
       channels))
     (no-recovery-msgs-for-dsts-p
      src
      (rest dsts)
      channels))))

;;; monjil-ray/recovery_inv.lisp, lines 234-252
(defun no-recovery-msgs-in-channels-p
    (srcs dsts channels)
  (declare
   (xargs :measure (acl2-count srcs)))
  (if (endp srcs)
      t
    (and
     (no-recovery-msgs-for-dsts-p
      (first srcs)
      dsts
      channels)
     (no-recovery-msgs-in-channels-p
      (rest srcs)
      dsts
      channels))))

;;; monjil-ray/recovery_inv.lisp, lines 258-269
(defun recovery-free-state-p (st)
  (let ((ids (proc-ids st)))
    (and
     (not
      (any-proc-recovering-p
       ids
       (procs st)))
     (no-recovery-msgs-in-channels-p
      ids
      ids
      (channels st)))))

;;; monjil-ray/recovery_inv.lisp, lines 272-277
(defun cl-checkpoint-body-input-p (input)
  (let ((tp (ttype input)))
    (or (equal tp :nop)
        (equal tp :normal)
        (equal tp :receive)
        (equal tp :start-checkpoint))))

;;; monjil-ray/recovery_inv.lisp, lines 280-287
(defun cl-checkpoint-body-inputs-p (inputs)
  (declare
   (xargs :measure (acl2-count inputs)))
  (if (endp inputs)
      t
    (and
     (cl-checkpoint-body-input-p (first inputs))
     (cl-checkpoint-body-inputs-p (rest inputs)))))

;;; ===== from monjil-ray/cut_meta_inv.lisp =====
;;; monjil-ray/cut_meta_inv.lisp, lines 31-83
(defun cut-meta-imp-procs-consistent-p
    (ids target-sid m imp-procs)
  (declare
   (xargs :measure (acl2-count ids)))
  (if (endp ids)
      t
    (let* ((i       (first ids))
           (p       (g i imp-procs))
           (has-sid (memberp target-sid
                             (snapshot-ids p))))
      (and
       (equal
        (cm-cut-not-taken-p m i)
        (not has-sid))
       (if has-sid
           (equal
            (g i
               (cm-waiting-marker-from m))
            (snapshot-waiting-marker-from
             (snapshot-entry
              target-sid
              p)))
         (endp
          (g i
             (cm-waiting-marker-from m))))
       (cut-meta-imp-procs-consistent-p
        (rest ids)
        target-sid
        m
        imp-procs)))))

;;; monjil-ray/cut_meta_inv.lisp, lines 87-112
(defun cut-meta-imp-initiator-consistent-p (m imp-st)
  (let* ((target-sid     (cm-sid m))
         (initiator      (first target-sid))
         (target-counter (second target-sid))
         (proc-ids       (proc-ids imp-st))
         (p              (g initiator
                            (procs imp-st))))
    (and
     (memberp initiator proc-ids)
     (if (cm-cut-not-taken-p m initiator)
         (and
          (equal (counter p)
                 target-counter)
          (equal (cm-cut-not-taken m)
                 (cm-proc-ids m)))
       (< target-counter
          (counter p))))))

;;; monjil-ray/cut_meta_inv.lisp, lines 116-119
(defun cut-meta-imp-proc-ids-consistent-p (m imp-st)
  (equal
   (cm-proc-ids m)
   (proc-ids imp-st)))

;;; monjil-ray/cut_meta_inv.lisp, lines 124-140
(defun cut-meta-imp-consistent-p (m imp-st)
  (and
   (cut-meta-imp-proc-ids-consistent-p m imp-st)
   (cut-meta-imp-initiator-consistent-p
    m
    imp-st)
   (cut-meta-imp-procs-consistent-p
    (cm-proc-ids m)
    (cm-sid m)
    m
    (procs imp-st))))

;;; monjil-ray/cut_meta_inv.lisp, lines 300-312
(defun good-cut-meta-sid-p (m)
  (let ((sid (cm-sid m)))
    (and
     (true-listp sid)
     (equal (len sid) 2)
     (memberp
      (first sid)
      (cm-proc-ids m))
     (natp
      (second sid)))))

;;; monjil-ray/cut_meta_inv.lisp, lines 315-325
(defun good-cut-meta-cut-not-taken-p (m)
  (and
   (true-listp
    (cm-cut-not-taken m))
   (uniquep
    (cm-cut-not-taken m))
   (subset
    (cm-cut-not-taken m)
    (cm-proc-ids m))))

;;; monjil-ray/cut_meta_inv.lisp, lines 328-359
(defun good-cut-meta-waiting-for-procs-p (ids m)
  (declare
   (xargs :measure (acl2-count ids)))
  (if (endp ids)
      t
    (let* ((i       (first ids))
           (waiting (g i
                       (g :waiting-marker-from m))))
      (and
       (true-listp waiting)
       (uniquep waiting)
       (subset
        waiting
        (cm-proc-ids m))
       (implies
        (cm-cut-not-taken-p m i)
        (endp waiting))
       (good-cut-meta-waiting-for-procs-p
        (rest ids)
        m)))))

;;; monjil-ray/cut_meta_inv.lisp, lines 362-368
(defun good-cut-meta-global-input-sequences-p (m)
  (and
   (true-listp
    (g :before-cut-input-sequence m))
   (true-listp
    (g :after-cut-input-sequence m))))

;;; monjil-ray/cut_meta_inv.lisp, lines 372-393
(defun good-cut-meta-p (m)
  (and
   (true-listp
    (cm-proc-ids m))
   (uniquep
    (cm-proc-ids m))
   (good-cut-meta-sid-p m)
   (good-cut-meta-cut-not-taken-p m)
   (good-cut-meta-waiting-for-procs-p
    (cm-proc-ids m)
    m)
   (good-cut-meta-global-input-sequences-p m)))

;;; monjil-ray/cut_meta_inv.lisp, lines 2783-2802
(defun marker-for-sid-in-channel-p (target-sid channel)
  (declare
   (xargs :measure (acl2-count channel)))
  (if (endp channel)
      nil
    (or
     (and
      (equal
       (msg-type (first channel))
       :marker)
      (equal
       (sid (first channel))
       target-sid))
     (marker-for-sid-in-channel-p
      target-sid
      (rest channel)))))

;;; monjil-ray/cut_meta_inv.lisp, lines 2805-2841
(defun cut-marker-in-transit-for-outgoing-nbrs-p
    (src outgoing-nbrs target-sid m channels)
  (declare
   (xargs :measure (acl2-count outgoing-nbrs)))
  (if (cm-cut-not-taken-p m src)
      t
    (if (endp outgoing-nbrs)
        t
      (let ((out-nbr (first outgoing-nbrs)))
        (and
         (if (cm-cut-not-taken-p m out-nbr)
             (marker-for-sid-in-channel-p
              target-sid
              (channel-state
               src
               out-nbr
               channels))
           t)
         (cut-marker-in-transit-for-outgoing-nbrs-p
          src
          (rest outgoing-nbrs)
          target-sid
          m
          channels))))))

;;; monjil-ray/cut_meta_inv.lisp, lines 2844-2871
(defun cut-markers-in-transit-for-srcs-p
    (srcs target-sid m procs channels)
  (declare
   (xargs :measure (acl2-count srcs)))
  (if (endp srcs)
      t
    (let ((src (first srcs)))
      (and
       (cut-marker-in-transit-for-outgoing-nbrs-p
        src
        (nbrs-to
         (g src procs))
        target-sid
        m
        channels)
       (cut-markers-in-transit-for-srcs-p
        (rest srcs)
        target-sid
        m
        procs
        channels)))))

;;; monjil-ray/cut_meta_inv.lisp, lines 2874-2881
(defun cut-markers-in-transit-p (m st)
  (cut-markers-in-transit-for-srcs-p
   (proc-ids st)
   (cm-sid m)
   m
   (procs st)
   (channels st)))

;;; ===== from monjil-ray/local_swap.lisp =====
;;; monjil-ray/local_swap.lisp, lines 40-41
(defun checkpoint-segment-initiator (input-seg)
  (pid (first input-seg)))

;;; monjil-ray/local_swap.lisp, lines 43-46
(defun checkpoint-segment-sid (st input-seg)
  (let* ((i (checkpoint-segment-initiator input-seg))
         (p (g i (procs st))))
    (list i (counter p))))

;;; monjil-ray/local_swap.lisp, lines 48-52
(defun checkpoint-segment-initial-meta (st input-seg)
  (make-cut-meta
   (checkpoint-segment-sid st input-seg)
   (checkpoint-segment-initiator input-seg)
   st))

;;; monjil-ray/local_swap.lisp, lines 54-58
(defun checkpoint-segment-meta (st input-seg)
  (scan-until-checkpoint-done
   input-seg
   st
   (checkpoint-segment-initial-meta st input-seg)))

;;; monjil-ray/local_swap.lisp, lines 60-62
(defun checkpoint-segment-completep (st input-seg)
  (checkpoint-collection-complete-p
   (checkpoint-segment-meta st input-seg)))

;;; monjil-ray/local_swap.lisp, lines 71-81
(defun checkpoint-completes-at-segment-end-p (inputs st m)
  (declare (xargs :measure (acl2-count inputs)))
  (if (endp inputs)
      (checkpoint-collection-complete-p m)
    (and
     (not (checkpoint-collection-complete-p m))
     (let* ((input   (first inputs))
            (next-m  (process-cut-step input st m))
            (next-st (system-step st input)))
       (checkpoint-completes-at-segment-end-p
        (rest inputs) next-st next-m)))))

;;; monjil-ray/local_swap.lisp, lines 87-89
(defun checkpoint-segment-before-cut-inputs (st input-seg)
  (cm-before-cut-input-sequence
   (checkpoint-segment-meta st input-seg)))

;;; monjil-ray/local_swap.lisp, lines 91-93
(defun checkpoint-segment-after-cut-inputs (st input-seg)
  (cm-after-cut-input-sequence
   (checkpoint-segment-meta st input-seg)))

;;; monjil-ray/local_swap.lisp, lines 104-117
(defun checkpoint-start-end-segment-p (st input-seg)
  (and
   (consp input-seg)
   (equal (ttype (first input-seg)) :start-checkpoint)
   (true-listp input-seg)
   (cl-checkpoint-body-inputs-p (rest input-seg))
   (good-state-p st)
   (legal-input-sequencep st input-seg)
   (recovery-free-state-p st)
   (checkpoint-segment-completep st input-seg)
   (checkpoint-completes-at-segment-end-p
    input-seg
    st
    (checkpoint-segment-initial-meta st input-seg))))

;;; monjil-ray/local_swap.lisp, lines 1348-1383
(defun post-pre-swap-start-p
    (st m input-1 input-2)
  (let*
      ((m-after-1
        (process-cut-step
         input-1
         st
         m)))
    (and
     (cut-markers-in-transit-p
      m st)
     (cut-meta-imp-consistent-p
      m st)
     (good-cut-meta-p m)
     (good-state-p st)
     (recovery-free-state-p st)
     (legal-input-sequencep
      st
      (list input-1 input-2))
     (cl-checkpoint-body-input-p
      input-1)
     (cl-checkpoint-body-input-p
      input-2)
     (not
      (cm-cut-not-taken-p
       m
       (pid input-1)))
     (cm-cut-not-taken-p
     m-after-1
     (pid input-2)))))
