# 04 — Chandy–Lamport

**Paper:** Mohammad Bin Monjil, Sandip Ray, *Formalizing the Chandy–Lamport Distributed Snapshot Reordering Theorem in ACL2* (ACL2 Workshop 2026). PDF in `source/paper.pdf`.
**Logic:** ACL2.

## The paper

The paper builds an executable ACL2 model of a message-passing system with FIFO channels, an
abstract application, checkpoints indexed by snapshot id, marker messages and per-channel recording. On it the
authors prove the Chandy–Lamport reordering argument: two swappable inputs commute up to state equivalence; an
adjacent postrecording/prerecording pair is swappable; and an executable sorting transformation turns a
completed checkpoint segment into its prerecording inputs followed by its postrecording inputs, preserving
state equivalence.

**Contribution.** A case study / theorem on a large custom model. The theorem was proved before in
Isabelle (Fiedler and Traytel, 2020); the new parts are the ACL2 model and the executable reordering. The paper
reports more than 1000 theorems and lemmas.

**Authors' ACL2 books.** Pull request [acl2/acl2#2105](https://github.com/acl2/acl2/pull/2105) (opened 2026-11-11,
not merged when we ran the experiments), directory `books/workshops/2026/monjil-ray/`. A copy is in
`source/authors-books/`. All 9 books certify on ACL2 8.7 (about 5 minutes).

## Files

```
04-binmonjil-chandy-lamport/
  README.md
  source/
    paper.pdf
    authors-books/        the authors' ACL2 books (copy)
  exp1/
    prompt.txt            the exact prompt sent to the model
    solution.lisp         the model's final /work/solution.lisp
    audit.txt             transcript audit (tools/audit.py)
    review.md             short factual review of the run
  exp2/
    prompt.txt            the exact prompt sent to the model
    definitions.lisp      the definitions, annotated with their source locations (comments only)
    targets.lisp          the target theorems (the authors' names in comments)
    checker/              the exact files the checker certifies against (hashes below)
    extraction/           how definitions.lisp was built and verified (NOTES.md, scripts, logs)
    solution.lisp         the model's final /work/solution.lisp
    audit.txt
    review.md
```

## Results

| | Experiment 1 (English → ACL2) | Experiment 2 (ACL2 statements) |
|---|---|---|
| Result | proved (certified) | all 2 target(s) proved (certified, statements matched) |
| Model time | 14 min | 25 min |
| Tool calls | 38 | 85 |
| Certification time of solution.lisp (ACL2 8.7) | 0.8 s | 4.0 s |
| Audit | CLEAN | CLEAN |
| solution.lisp: lines / definitions / theorems | 754 / 60 / 60 | 1063 / 19 / 139 |

Authors' development (for scale): 9 books, 27,898 lines, 250 definitions, 626 theorems (our counter; the paper reports more than 1000 theorems and lemmas, which may count events our counter does not see).

*Model time* runs from when the model received the prompt to the end of its run (setup not included).
Certification time is for `solution.lisp` alone, with its dependencies already certified, on our build
(experiment 2: against `exp2/checker/`). Sizes are counted with `tools/sizes.py` (definitions = `defun`,
`define`, `defun-sk`, `defmacro`, … and encapsulated functions; theorems = `defthm`, `defrule`, …, local
ones included). Both experiments: first attempt, Claude Opus 5.5 at medium effort.

## Experiment 1: English definitions and theorem

**Theorem given:** The global reordering theorem: reordering a complete checkpoint segment into its prerecording inputs followed by its postrecording inputs gives a state-equivalent execution. The paper has no single English sentence for it; the prompt composes it from §5.2–5.3.

### Statement rewrites (paper text → prompt)

The definitions and theorem were copied from the paper as close to verbatim as possible. Every edit:

#### Sources
- **Theorem.** Composed from §5.3, p. 12: the prose after `checkpoint-complete-segment-reordered-run-state-equivalent`, which reads "The second execution contains exactly the prerecording inputs … followed by exactly its postrecording inputs … this globally reordered execution is state-equivalent to the original execution". The relative-order clause comes from §5.2, p. 11. The paper has no single precise English sentence: the §2.2 "Execution-Reordering Theorem" is existential and says "relevant" states, so it was not used. **Composed.**
- **System and state:** §2.1 p. 3; §3.1 p. 5.
- **Application and topology:** §3.1 p. 6.
- **Snapshots, initiation, markers, recording:** §3.2 pp. 6–7 and §2.1.
- **Inputs and legality:** §3.3 p. 7.
- **Equivalence:** §4.1 p. 8 and §6.2 p. 13.
- **Classification:** §2.1 p. 3–4, §4.2 p. 8 and §1 p. 2.
- **Segment:** §5.3 pp. 11–12.
- **Initial state:** Remark 2 p. 12 and §6.1 p. 13.

#### Edits (original → edited)
- "We assume reliable communication" → "Communication is reliable". Reason: anonymization.
- I added "Messages are either ordinary (application) messages or markers." The paper implies this but never says it.
- `update-local-state-normal is an internal computation step; …` → the four operations described without ACL2 names. "The theorem shown above is the only constraint…" → "The only constraint … is that it is an ordinary message". "constrained functions" → "arbitrary functions".
- `start-checkpoint-helper saves … increments …` plus `create-marker-message …` plus `send-msg-all-outgoing-channels …` → merged into one passive sentence without function names. The rest is as the paper has it.
- "The argument j identifies the channel on which the first marker was received; that channel is initialized with an empty snapshot" → folded into the marker bullet.
- "The function record-msg-in-snapshots examines each active snapshot and records…" → "an arriving message … is recorded in each snapshot … exactly when…".
- I added "a checkpoint counter" and "(checkpointing or done)" to the snapshot description. The paper names the counter in `step-checkpoint` and the statuses in §3.2.
- **The ordinary-computation bullet is my own paraphrase.** The paper never says how a compute step sends messages.
- Dropped from §3.3: crash, recovery and no-op transitions, and the sentence about them. Reason: §6.1 says the theorem "is restricted to ordinary computation, message receipt, and checkpoint initiation from a recovery-free state".
- Replaced `legal-input-sequencep` code with an English recursive definition. "Protocol restrictions similarly constrain checkpoint, crash, and recovery transitions" → "…checkpoint transitions".
- Remark 2 and §6.1 → the "Initial state of a segment" paragraph. "starting from the system's initial state" is my addition. It replaces `good-state-p`, which the paper never defines.
- §2.1 r_p sentences: I added "for the target snapshot" and the parenthetical "(by initiating it, or on receiving its first marker for it)". The parenthetical is my gloss.
- The classification sentence is adapted from §4.2: the cut-metadata wording was removed. "in particular r_p itself is prerecording" is **my inference** from "before processing the checkpoint-specific effect".
- The §1 sentence on classification: "cut metadata" → "checkpoint information".
- §5.3: "Such a segment begins with a legal :start-checkpoint input…" was kept nearly verbatim. "requires the target checkpoint to be incomplete…" → "The target checkpoint is incomplete…".
- `state-equivalent-p` code and the §4.1 prose → one English sentence. §6.2 "stopping short of requiring equality of every stored snapshot entry" → final sentence.
- I did not state the local swap property, the transformation, the inversion count, or any invariants.

#### Details the paper leaves open
1. **`good-state-p`.** It is never defined and is described only as "recovery-free". I substituted "reachable from the system's initial state". The system's initial state (empty channels, no snapshots, counters 0?) is itself not defined.
2. **Compute step.** The order of the local update and the sends is not given. It is also unclear whether the message is built from the old or the new state, and whether a receive can also send.
3. **Legality of checkpoint initiation** ("protocol restrictions") is not given. Examples would be "valid process" or "no own snapshot in progress".
4. **Marker contents and target matching.** A marker carries a sid. It is not said whether a process's set of expected markers is all of its incoming neighbors at initiation.
5. **Topology.** It is not said whether the outgoing and incoming neighbor functions must be mutually consistent, or whether there is an implicit process set.
6. **Constraints on the abstract application.** The encapsulate's other constraints are elided ("...").
7. **"Snapshot complete."** This most likely means that every process holds the sid with status done. The paper also says "all markers required…received".
8. **Legality of the reordered execution.** The formal theorem does not assert it, and neither does the prompt. The informal §2.2 theorem (2) implies it.
9. **"Topology" inside equivalence** presumes that the neighbor lists are stored per process.

### Prompt

<details>
<summary>Experiment 1 prompt (also in exp1/prompt.txt)</summary>

```text
Formalize the definitions and the theorem below in ACL2, and prove the theorem.

<definitions>
System and global state. Consider a distributed system consisting of a finite collection of processes that communicate by sending messages over directed FIFO channels. Each process maintains a local state; the global state of the system consists of the collection of all local states together with the contents of all communication channels. The global state contains the process identifiers, the states of the individual processes, and the communication channels. Communication is reliable: messages are neither lost nor duplicated, and messages sent along a channel are received in FIFO order. Channels are lists: sending appends a message and receiving removes the head message. Messages are either ordinary (application) messages or markers.

Application and topology. The application executed by the processes is deliberately abstract: it is given by arbitrary operations for an internal computation step; for the effect of receiving an application message; a predicate that determines whether an ordinary message is sent to an outgoing neighbor; and an operation that constructs that message. The only constraint on the constructed message is that it is an ordinary message (not a marker). The model is parameterized over both the distributed application and its communication topology: the network topology and initial process states are abstracted similarly, as arbitrary functions for incoming and outgoing neighbors and for initial local state.

Snapshots. Each process maintains a set of snapshot identifiers, a checkpoint counter, and a record mapping each identifier to a snapshot entry. A snapshot entry stores the saved local state, the recorded states of incoming channels, the incoming neighbors from which markers are still expected, and the status of the snapshot (checkpointing or done). Snapshot identifiers are generated locally as the pair consisting of an initiating process identifier and its checkpoint counter, permitting multiple snapshots without a global snapshot counter.

Inputs and transitions. An input identifies the process taking a step, the transition type, and, for a receive, the sending process. The transition types are ordinary computation, receive, and checkpoint initiation.
- Ordinary computation: an internal computation step of the process; ordinary messages are sent to those outgoing neighbors selected by the predicate, using the message-construction operation.
- Checkpoint initiation at process i: the current local state is saved in a new snapshot entry, the set of expected incoming markers is initialized, the entry is installed under the identifier sid = (i, checkpoint counter of i), and the process's checkpoint counter is incremented. A marker carrying sid is constructed and appended to every outgoing FIFO channel of i.
- Receive at process i from process j: the head message of the channel from j to i is removed. Marker receipt distinguishes the first marker for a snapshot from later markers. On the first marker, the receiving process saves its local state, begins waiting for markers on the remaining incoming channels, and propagates the marker to its outgoing neighbors; the channel on which the first marker was received is initialized with an empty snapshot. Each later marker closes the corresponding incoming channel; when no markers remain outstanding, the local snapshot is marked done. Receiving an ordinary message applies the application's receive effect to the local state, and ordinary messages received while a snapshot is open implement the Chandy–Lamport channel-recording rule: an arriving message from neighbor j is recorded in each snapshot of the receiving process exactly when that snapshot is still checkpointing and its marker from j has not yet arrived.

Executions and legality. An execution is a list of inputs, run by applying the inputs in order to a state. A receive is legal only when its sender and receiver are valid processes, the sender is an incoming neighbor of the receiver, and the corresponding channel is nonempty. Protocol restrictions similarly constrain checkpoint transitions. An execution is legal from a state when its first input is legal in that state and the rest of the execution is legal from the state reached by executing that input.

Initial state of a segment. The state from which a checkpoint segment starts need not be the start of a system execution: it may be the state reached after an arbitrary legal execution prefix, starting from the system's initial state. Multiple concurrent snapshots with distinct snapshot identifiers remain permitted.

Recording cut, prerecording and postrecording events. Fix a target snapshot. For each process p, let r_p denote the event at which p records its local state for the target snapshot (by initiating it, or on receiving its first marker for it); at that point p has taken its local cut. An event executed by p before r_p is a prerecording event, and an event executed after r_p is a postrecording event. Each input is classified, before its own checkpoint-specific effect is processed, according to whether its process has already taken its cut; in particular r_p itself is prerecording. The collection of the local recording points therefore defines a cut through the distributed execution. Prerecording and postrecording are not static labels on events; their classification depends on the checkpoint information accumulated along the execution prefix.

Checkpoint segment. A complete checkpoint segment from a state is a legal execution from that state which begins with a checkpoint-initiation input and ends at the first point at which every process has taken its local cut and all markers required for the target snapshot have been received. The target snapshot is the one initiated by the first input. The target checkpoint is incomplete on every proper prefix and complete after the entire segment; thus the segment ends exactly when collection of the snapshot completes.

State equivalence. Two states are state-equivalent when they contain the same list of process identifiers, their channels are equal, the application-visible local state and topology of corresponding processes are equal, and their checkpoint-control information, including process counters and snapshot-identifier lists, is equal. Equality of every stored snapshot entry is not required.
</definitions>

<theorem>
Let st be a state as above, and let a complete checkpoint segment from st be given. Consider the execution that contains exactly the prerecording inputs of the original checkpoint segment followed by exactly its postrecording inputs, each group in its original relative order. Then this globally reordered execution is state-equivalent to the original execution: the states reached by running the two executions from st are state-equivalent.
</theorem>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
Put your work in /work/solution.lisp; it must certify with `cert.pl` (add `--acl2 acl2r` for ACL2(r)), and its last
event must be the theorem, named MAIN.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done. When you are done, print the final contents of /work/solution.lisp.
```

</details>

## Experiment 2: the authors' ACL2 definitions and statements

### Targets

| Target | Authors' theorem | Meaning |
|---|---|---|
| MAIN-1 | `checkpoint-complete-segment-reordered-run-state-equivalent` (global_reorder.lisp:5748) | global reordering theorem |
| MAIN-2 | `post-pre-two-imp-inputs-commute-under-state-equivalence` (local_swap.lisp:2224) | local post/pre swap theorem |

### How the definitions were extracted

`definitions.lisp` holds 163 of the authors' forms (133 `defun`s, 29 `defmacro`s, 1
`encapsulate` for the abstract application), in the authors' order, from `model`, `scan`, `good_state_inv`,
`recovery_inv`, `cut_meta_inv` and `local_swap`. The set is the transitive symbol closure of the two target
statements (scripts in `exp2/extraction/verify/`). Nothing from `global_reorder` is needed. In particular the
reordering machinery (`reorder-inputs`, `swap-first-after-before`, `inversion-count`, …) is not included.
Every definition admits without hints, so there are no local lemmas.

The general procedure, and how each package was checked, is in [`../EXPERIMENT-2.md`](../EXPERIMENT-2.md);
the full notes for this paper are in `exp2/extraction/NOTES.md`.

Checker files:

| File | SHA-256 |
|---|---|
| `exp2/checker/defs.lisp` | `86d0bb3845860fd7d55a1853473b8fb54861364c7a1e463f3bc5e6fce039228b` |

`exp2/definitions.lisp` differs from `exp2/checker/defs.lisp` only in comments
(`tools/check-comments-only.py`).

### Statement rewrites (authors' ACL2 → targets)

- Comments and blank lines inside forms are removed; otherwise every form is verbatim.
- MAIN-1: the authors' `:rule-classes nil` and hints are dropped. MAIN-2: hints dropped. Statements unchanged.
- `cut_meta_inv` invariants and `post-pre-swap-start-p` are there only because MAIN-2 needs them; they are
  also visible when proving MAIN-1.

### Prompt

<details>
<summary>Experiment 2 prompt (also in exp2/prompt.txt)</summary>

```text
Prove the theorems below in ACL2.

1. Create /work/defs.lisp containing exactly the text between the tags. defs.lisp holds the definitions the theorems use. Do not modify these files.

<defs.lisp>
(in-package "ACL2")

(include-book "misc/records" :dir :system)

(defun memberp (e l)
  (cond ((endp l) nil)
        ((equal e (first l)) t)
        (t (memberp e (rest l)))))

(defun subset (x y)
  (cond ((endp x) t)
        (t (and (memberp (first x) y)
                (subset (rest x) y)))))

(defun uniquep (x)
  (if (endp x) t
    (and (not (memberp (first x) (rest x)))
         (uniquep (rest x)))))

(defun snoc (x e)
  (if (endp x) (list e)
    (cons (first x) (snoc (rest x) e))))

(defun remove-from-list (x e)
  (if (endp x)
      nil
    (if (equal e (first x))
        (remove-from-list (rest x) e)
      (cons (first x)
            (remove-from-list (rest x) e)))))

(defmacro procs     (s) `(g :procs ,s))

(defmacro channels  (s) `(g :channels ,s))

(defmacro proc-ids  (s) `(g :proc-ids ,s))

(defmacro local-state           (p) `(g :local-state ,p))

(defmacro channel-state (i j chans) `(g ,i (g ,j ,chans)))

(defmacro nbrs-to               (p) `(g :nbrs-to ,p))

(defmacro nbrs-from             (p) `(g :nbrs-from ,p))

(defmacro pid   (input) `(g :pid ,input))

(defmacro ttype (input) `(g :ttype ,input))

(defmacro sender (input) `(g :sender ,input))

(defun update-macro (upds result)
  (declare (xargs :guard (keyword-value-listp upds)))
  (if (endp upds) result
    (update-macro (cddr upds)
                  (list 's (car upds) (cadr upds) result))))

(defmacro update (old &rest updates)
  (declare (xargs :guard (keyword-value-listp updates)))
  (update-macro updates old))

(defmacro >st (&rest upds) `(update st ,@upds))

(defmacro >p  (&rest upds) `(update p  ,@upds))

(defmacro >_ (&rest upds) `(update nil ,@upds))

(defmacro >channel (i j val channels)
  `(s ,j
      (s ,i ,val (g ,j ,channels))
      ,channels))

(defmacro append-to-record-list (key val record)
  `(let* ((existing (g ,key ,record))
          (updated (append existing (list ,val))))
     (s ,key updated ,record)))

(defmacro proc-status           (p) `(g :proc-status ,p))

(defmacro waiting-recovery-from (p) `(g :waiting-recovery-from ,p))

(defmacro counter               (p) `(g :counter ,p))

(defmacro snapshot-ids          (p) `(g :snapshot-ids ,p))

(defmacro snapshots             (p) `(g :snapshots ,p))

(defmacro snapshot-entry    (sid p) `(g ,sid (snapshots ,p)))

(defmacro sid (msg) `(g :sid ,msg))

(defmacro msg-type (msg) `(g :msg-type ,msg))

(defmacro snapshot-status (entry)
  `(g :status ,entry))

(defmacro snapshot-local-snap-shot (entry)
  `(g :local-snap-shot ,entry))

(defmacro snapshot-channel-snapshots (entry)
  `(g :channel-snapshots ,entry))

(defmacro snapshot-waiting-marker-from (entry)
  `(g :waiting-marker-from ,entry))

(defun make-snapshot-entry (local-snap-shot waiting-marker-from j)
  (let ((cs (if j
                (s j nil nil)
              nil)))
    (>_ :status :checkpointing
        :local-snap-shot local-snap-shot
        :channel-snapshots cs
        :waiting-marker-from waiting-marker-from)))

(defun add-snapshot-id (sid ids)
  (if (memberp sid ids)
      ids
    (cons  sid ids)))

(defun set-snapshot-entry (sid entry p)
  (let* ((snaps (snapshots p))
         (snaps (s sid entry snaps)))
    (s :snapshots snaps p)))

(defun install-snapshot-entry (sid entry p)
  (let* ((snapshot-ids   (add-snapshot-id sid (snapshot-ids p)))
         (snapshots (snapshots p))
         (snapshots (s sid entry snapshots)))
    (update p
            :snapshot-ids snapshot-ids
            :snapshots snapshots)))

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

(defun create-marker-message (local-state sid)
  (declare (ignore local-state))
  (>_ :msg-type :marker
      :sid sid))

(defun create-recovery-message (local-state sid)
  (declare (ignore local-state))
  (>_ :msg-type :recovery
      :sid sid))

(defun remove-message-from-channel (nbr i channels)
    (let* ((channel (channel-state nbr i channels))
           (channel (if channel (cdr channel) nil))
           (channels (>channel nbr i  channel channels)))
      channels))

(defun send-msg-all-outgoing-channels (msg i nbrs channels)
  (cond ((endp nbrs) channels)
        (t
         (let* ((nbr      (first nbrs))
                (channels (send-msg-all-outgoing-channels msg i (rest nbrs) channels))
                (channel  (channel-state i nbr channels))
                (channel  (snoc channel msg))
                (channels (>channel i nbr channel channels)))
           channels))))

(defun update-proc-for-first-marker-msg (p sid j)
  (let* ((nbrs-from           (nbrs-from p))
         (local-state         (local-state p))
         (waiting-marker-from (remove-from-list nbrs-from j))
         (entry               (make-snapshot-entry local-state
                                                   waiting-marker-from
                                                   j)))
    (install-snapshot-entry sid entry p)))

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

(defun handle-marker-msg (st i j msg)
  (let* ((sid (sid msg))
         (procs (procs st))
         (p (g i procs))
         (snapshot-ids (snapshot-ids p)))
    (if (memberp sid snapshot-ids)
        (handle-non-first-marker-msg st i j msg)
      (handle-first-marker-msg st i j msg))))

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

(defun update-proc-for-non-first-recovery-msg (p j)
  (let* ((waiting     (waiting-recovery-from p))
         (waiting     (remove-from-list waiting j))
         (proc-status (if (endp waiting)
                          :normal
                        :recovering)))
    (update p
            :proc-status proc-status
            :waiting-recovery-from waiting)))

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

(defun handle-recovery-msg (st i j msg)
  (let* ((procs       (procs st))
         (p           (g i procs))
         (proc-status (proc-status p)))
    (if (equal proc-status :normal)
        (handle-first-recovery-msg st i j msg)
	(handle-non-first-recovery-msg st i j msg))))

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

(defun handle-normal-msg-core (st i j msg)
  (let* ((procs    (procs st))
         (channels (channels st))
         (p        (g i procs))
         (p        (update-proc-for-normal-msg-core p j msg))
         (channels (remove-message-from-channel j i channels))
         (procs    (s i p procs)))
    (>st :procs procs
         :channels channels)))

(defun ignore-normal-msg (st i j msg)
  (declare (ignore msg))
  (let* ((channels (channels st))
         (channels (remove-message-from-channel j i channels)))
    (>st :procs (procs st)
         :channels channels)))

(defun handle-normal-msg (st i j msg)
  (let* ((procs   (procs st))
         (p       (g i procs))
         (status  (proc-status p))
         (waiting (waiting-recovery-from p)))
    (if (and (equal status :recovering)
             (memberp j waiting))
        (ignore-normal-msg st i j msg)
	(handle-normal-msg-core st i j msg))))

(defun get-msg-from-channel (nbr i channels)
  (let ((channel (channel-state nbr i channels)))
    (if (consp channel)
        (first channel)
      nil)))

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

(defun step-crash (st i)
  (let* ((procs (procs st))
         (p     (g i procs))
         (p     (update p :proc-status :crashed))
         (procs (s i p procs)))
    (>st :procs procs
         :channels (channels st))))

(defun recovery-local-state-after-replay (p)
  (let* ((nbrs-from     (nbrs-from p))
         (sid           (car (snapshot-ids p)))
         (entry         (snapshot-entry sid p))
         (local-state   (snapshot-local-snap-shot entry))
         (channel-snaps (snapshot-channel-snapshots entry)))
    (replay-channel-snapshots local-state
                              channel-snaps
                              nbrs-from)))

(defun start-recovery-helper (procs i)
  (let* ((p           (g i procs))
         (nbrs-from   (nbrs-from p))
         (local-state (recovery-local-state-after-replay p))
         (p-new       (update p
                              :local-state local-state
                              :proc-status :recovering
                              :waiting-recovery-from nbrs-from)))
    (s i p-new procs)))

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

(defun run-imp (st inputs)
  (if (endp inputs)
      st
    (run-imp
     (system-step st (first inputs))
     (rest inputs))))

(defun any-checkpointing-snapshot-in-ids-p (snapshot-ids p)
  (cond ((endp snapshot-ids)
         nil)
        (t
         (let* ((sid   (first snapshot-ids))
                (entry (snapshot-entry sid p)))
           (or (equal (snapshot-status entry) :checkpointing)
               (any-checkpointing-snapshot-in-ids-p (rest snapshot-ids) p))))))

(defun proc-has-checkpointing-snapshot-p (p)
  (any-checkpointing-snapshot-in-ids-p (snapshot-ids p) p))

(defun any-proc-checkpointing-p (proc-ids procs)
  (cond ((endp proc-ids)
         nil)
        (t
         (let* ((pid (first proc-ids))
                (p   (g pid procs)))
           (or (proc-has-checkpointing-snapshot-p p)
               (any-proc-checkpointing-p (rest proc-ids) procs))))))

(defun any-snapshot-checkpointing-p (st)
  (let* ((ids   (proc-ids st))
         (procs (procs st)))
    (any-proc-checkpointing-p ids procs)))

(defun any-proc-recovering-p (proc-ids procs)
  (cond ((endp proc-ids)
         nil)
        (t
         (let* ((pid (first proc-ids))
                (p   (g pid procs)))
           (or (equal (proc-status p) :recovering)
               (any-proc-recovering-p (rest proc-ids) procs))))))

(defun any-process-recovering-p (st)
  (let* ((ids   (proc-ids st))
         (procs (procs st)))
    (any-proc-recovering-p ids procs)))

(defun some-proc-has-snapshot-id-p (sid ids procs)
  (if (endp ids)
      nil
    (let* ((i (first ids))
           (p (g i procs)))
      (or (memberp sid (snapshot-ids p))
          (some-proc-has-snapshot-id-p sid (rest ids) procs)))))

(defun all-procs-have-snapshot-id-p (sid ids procs)
  (if (endp ids)
      t
    (let* ((i (first ids))
           (p (g i procs)))
      (and (memberp sid (snapshot-ids p))
           (all-procs-have-snapshot-id-p sid (rest ids) procs)))))

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

(defun legal-input-sequencep (st inputs)
  (declare (xargs :measure (acl2-count inputs)))
  (if (endp inputs)
      t
    (and (legal-inputp st (first inputs))
         (legal-input-sequencep
          (system-step st (first inputs))
          (rest inputs)))))

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

(defun proc-equivalent-p (imp-p spec-p)
  (and
   (equal (local-state imp-p)
          (local-state spec-p))
   (equal (nbrs-to imp-p)
          (nbrs-to spec-p))
   (equal (nbrs-from imp-p)
          (nbrs-from spec-p))))

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

(defun current-msg-for-receive (input st)
  (let* ((i        (pid input))
         (j        (sender input))
         (channels (channels st)))
    (get-msg-from-channel j i channels)))

(defmacro cm-sid (m)
  `(g :sid ,m))

(defun cm-proc-ids (m)
  (g :proc-ids m))

(defun cm-cut-not-taken (m)
  (g :cut-not-taken m))

(defun cm-waiting-marker-from (m)
  (g :waiting-marker-from m))

(defun cm-after-cut-input-sequence (m)
  (g :after-cut-input-sequence m))

(defun cm-before-cut-input-sequence (m)
  (g :before-cut-input-sequence m))

(defun cm-waiting-marker-for (m i)
  (g i (cm-waiting-marker-from m)))

(defun cm-set-waiting-marker-for (m i xs)
  (s :waiting-marker-from
     (s i xs (cm-waiting-marker-from m))
     m))

(defun cm-cut-not-taken-p (m i)
  (memberp i (cm-cut-not-taken m)))

(defun cm-remove-cut-not-taken (m i)
  (s :cut-not-taken
     (remove1-equal i (cm-cut-not-taken m))
     m))

(defun cm-add-after-cut-input-sequence (m input)
  (s :after-cut-input-sequence
     (append
      (cm-after-cut-input-sequence m)
      (list input))
     m))

(defun cm-add-before-cut-input-sequence (m input)
  (s :before-cut-input-sequence
     (append
      (cm-before-cut-input-sequence m)
      (list input))
     m))

(defun make-empty-waiting-marker-from (proc-ids)
  (if (endp proc-ids)
      nil
    (s (first proc-ids)
       nil
       (make-empty-waiting-marker-from (rest proc-ids)))))

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

(defun all-waiting-marker-empty-p (ids m)
  (if (endp ids)
      t
    (and (endp (cm-waiting-marker-for m (first ids)))
         (all-waiting-marker-empty-p (rest ids) m))))

(defun checkpoint-collection-complete-p (m)
  (if (equal (cm-sid m) :init)
      t
    (and (endp (cm-cut-not-taken m))
         (all-waiting-marker-empty-p
          (cm-proc-ids m)
          m))))

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

(defun good-proc-status-p (x)
  (or (equal x :normal)
      (equal x :crashed)
      (equal x :recovering)))

(defun good-snapshot-status-p (x)
  (or (equal x :checkpointing)
      (equal x :done)))

(defun good-snapshot-id-p (sid ids)
  (or (equal sid :init)
      (and (consp sid)
           (consp (cdr sid))
           (endp (cddr sid))
           (memberp (car sid) ids)
           (natp (cadr sid)))))

(defun good-snapshot-ids-p (snapshot-ids ids)
  (if (endp snapshot-ids)
      t
    (and (good-snapshot-id-p (first snapshot-ids) ids)
         (good-snapshot-ids-p (rest snapshot-ids) ids))))

(defun good-snapshot-ids-list-p (snapshot-ids ids)
  (and (true-listp snapshot-ids)
       (uniquep snapshot-ids)
       (memberp :init snapshot-ids)
       (good-snapshot-ids-p snapshot-ids ids)))

(defun good-msg-p (msg ids procs)
  (let ((tp (msg-type msg)))
    (cond ((equal tp :normal)
           t)
          ((equal tp :marker)
           (some-proc-has-snapshot-id-p (sid msg) ids procs))
          ((equal tp :recovery)
           (all-procs-have-snapshot-id-p (sid msg) ids procs))
          (t nil))))

(defun good-msg-list-p (msgs ids procs)
  (if (endp msgs)
      t
    (and (good-msg-p (first msgs) ids procs)
         (good-msg-list-p (rest msgs) ids procs))))

(defun good-normal-msg-p (msg)
  (equal (msg-type msg) :normal))

(defun good-normal-msg-list-p (msgs)
  (if (endp msgs)
      t
    (and (good-normal-msg-p (first msgs))
         (good-normal-msg-list-p (rest msgs)))))

(defun good-channel-snapshot-record-p (nbrs-from-i cs)
  (if (endp nbrs-from-i)
      t
    (and (good-normal-msg-list-p (g (first nbrs-from-i) cs))
         (good-channel-snapshot-record-p (rest nbrs-from-i) cs))))

(defun good-snapshot-entry-p (entry nbrs-from-i)
  (and (good-snapshot-status-p (snapshot-status entry))
       (true-listp (snapshot-waiting-marker-from entry))
       (uniquep (snapshot-waiting-marker-from entry))
       (subset (snapshot-waiting-marker-from entry) nbrs-from-i)
       (good-channel-snapshot-record-p nbrs-from-i
                                       (snapshot-channel-snapshots entry))))

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

(defun good-procs-p (ids procs all-ids)
  (if (endp ids)
      t
    (let* ((i (first ids))
           (p (g i procs)))
      (and (good-proc-p  p  all-ids)
           (good-procs-p (rest ids) procs all-ids)))))

(defun good-channel-p (src dst channels ids procs)
  (let ((p (g src procs)))
    (if (memberp dst (nbrs-to p))
        (good-msg-list-p (channel-state src dst channels) ids procs)
      (equal (channel-state src dst channels) nil))))

(defun good-channel-row-p (src dsts channels ids procs)
  (if (endp dsts)
      t
    (and (good-channel-p src (first dsts) channels ids procs)
         (good-channel-row-p src (rest dsts) channels ids procs))))

(defun good-channels-p (srcs dsts channels ids procs)
  (if (endp srcs)
      t
    (and (good-channel-row-p (first srcs) dsts channels ids procs)
         (good-channels-p (rest srcs) dsts channels ids procs))))

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

(defun checkpoint-sid-p (x)
  (and
   (consp x)
   (consp (cdr x))
   (endp (cddr x))))

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

(defun cl-checkpoint-body-input-p (input)
  (let ((tp (ttype input)))
    (or (equal tp :nop)
        (equal tp :normal)
        (equal tp :receive)
        (equal tp :start-checkpoint))))

(defun cl-checkpoint-body-inputs-p (inputs)
  (declare
   (xargs :measure (acl2-count inputs)))
  (if (endp inputs)
      t
    (and
     (cl-checkpoint-body-input-p (first inputs))
     (cl-checkpoint-body-inputs-p (rest inputs)))))

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

(defun cut-meta-imp-proc-ids-consistent-p (m imp-st)
  (equal
   (cm-proc-ids m)
   (proc-ids imp-st)))

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

(defun good-cut-meta-cut-not-taken-p (m)
  (and
   (true-listp
    (cm-cut-not-taken m))
   (uniquep
    (cm-cut-not-taken m))
   (subset
    (cm-cut-not-taken m)
    (cm-proc-ids m))))

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

(defun good-cut-meta-global-input-sequences-p (m)
  (and
   (true-listp
    (g :before-cut-input-sequence m))
   (true-listp
    (g :after-cut-input-sequence m))))

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

(defun cut-markers-in-transit-p (m st)
  (cut-markers-in-transit-for-srcs-p
   (proc-ids st)
   (cm-sid m)
   m
   (procs st)
   (channels st)))

(defun checkpoint-segment-initiator (input-seg)
  (pid (first input-seg)))

(defun checkpoint-segment-sid (st input-seg)
  (let* ((i (checkpoint-segment-initiator input-seg))
         (p (g i (procs st))))
    (list i (counter p))))

(defun checkpoint-segment-initial-meta (st input-seg)
  (make-cut-meta
   (checkpoint-segment-sid st input-seg)
   (checkpoint-segment-initiator input-seg)
   st))

(defun checkpoint-segment-meta (st input-seg)
  (scan-until-checkpoint-done
   input-seg
   st
   (checkpoint-segment-initial-meta st input-seg)))

(defun checkpoint-segment-completep (st input-seg)
  (checkpoint-collection-complete-p
   (checkpoint-segment-meta st input-seg)))

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

(defun checkpoint-segment-before-cut-inputs (st input-seg)
  (cm-before-cut-input-sequence
   (checkpoint-segment-meta st input-seg)))

(defun checkpoint-segment-after-cut-inputs (st input-seg)
  (cm-after-cut-input-sequence
   (checkpoint-segment-meta st input-seg)))

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
</defs.lisp>

2. Write /work/solution.lisp. It must (include-book "defs") and then prove every theorem in <theorems>, each with exactly the name and statement given (MAIN-1, MAIN-2). You may add your own definitions and lemmas before them.

<theorems>
(in-package "ACL2")

(defthm MAIN-1
  (implies
   (checkpoint-start-end-segment-p st input-seg)
   (state-equivalent-p
    (run-imp st input-seg)
    (run-imp
     st
     (append
      (checkpoint-segment-before-cut-inputs st input-seg)
      (checkpoint-segment-after-cut-inputs st input-seg))))))

(defthm MAIN-2
  (implies
   (post-pre-swap-start-p st m input-1 input-2)
   (state-equivalent-p
    (run-imp st (list input-1 input-2))
    (run-imp st (list input-2 input-1)))))
</theorems>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
/work/solution.lisp must certify with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done. When you are done, print the final contents of /work/solution.lisp.
```

</details>

## Notes for reviewers

**Experiment 1.**
- The prompt's theorem and system description were composed from several sections, and some details are not
  fixed by the paper (see "Statement rewrites" below).

**Experiment 2.**
- The session's worker restarted once (infrastructure), after the file had certified. The resumed turn
  re-certified the file and printed it.

