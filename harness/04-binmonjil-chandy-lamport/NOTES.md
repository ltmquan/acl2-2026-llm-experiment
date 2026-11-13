# 04 — Chandy–Lamport: harness notes

Our records for this paper: how the prompts and packages were made, and how the runs went. Reviewers do not
need this; the paper folder [`../../04-binmonjil-chandy-lamport/`](../../04-binmonjil-chandy-lamport/) has what they review.

**Contribution (our classification).** A case study / theorem on a large custom model. The theorem was proved before in Isabelle (Fiedler and Traytel, 2020); the new parts are the ACL2 model and the executable reordering. The paper reports more than 1000 theorems and lemmas.

## Results

| | Experiment 1 | Experiment 2 |
|---|---|---|
| Result | proved (certified) | 2 / 2 targets proved |
| Model time | 14 min | 25 min |
| Tool calls | 38 | 85 |
| Certification time of solution.lisp (ACL2 8.7) | 0.8 s | 4.0 s |
| Audit (`exp*/audit.txt`) | CLEAN | CLEAN |
| solution.lisp: lines / definitions / theorems | 754 / 60 / 60 | 1063 / 19 / 139 |

Authors' development: 9 books, 27,898 lines, 250 definitions, 626 theorems (our counter; the paper reports more than 1000 theorems and lemmas, which may count events our counter does not see). Per-run accounts: `exp1/run.md`, `exp2/run.md`.

## Experiment 1: how the prompt was made from the paper

**Theorem chosen:** The global reordering theorem: reordering a complete checkpoint segment into its prerecording inputs followed by its postrecording inputs gives a state-equivalent execution. The paper has no single English sentence for it; the prompt composes it from §5.2–5.3.

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

## Experiment 2: how the package was made

`definitions.lisp` holds 163 of the authors' forms (133 `defun`s, 29 `defmacro`s, 1
`encapsulate` for the abstract application), in the authors' order, from `model`, `scan`, `good_state_inv`,
`recovery_inv`, `cut_meta_inv` and `local_swap`. The set is the transitive symbol closure of the two target
statements (scripts in `exp2/extraction/verify/`). Nothing from `global_reorder` is needed. In particular the
reordering machinery (`reorder-inputs`, `swap-first-after-before`, `inversion-count`, …) is not included.
Every definition admits without hints, so there are no local lemmas.

Full notes, scripts and logs: `exp2/extraction/`.

### Changes from the authors' text

- Comments and blank lines inside forms are removed; otherwise every form is verbatim.
- MAIN-1: the authors' `:rule-classes nil` and hints are dropped. MAIN-2: hints dropped. Statements unchanged.
- `cut_meta_inv` invariants and `post-pre-swap-start-p` are there only because MAIN-2 needs them; they are
  also visible when proving MAIN-1.

### Checker files

`exp2/checker/` holds the exact files `tools/check-exp2.py` certifies the solution against. The paper folder's
`exp2/definitions.lisp` is the same file with comments added (`tools/check-comments-only.py`).

| File | SHA-256 |
|---|---|
| `exp2/checker/defs.lisp` | `86d0bb3845860fd7d55a1853473b8fb54861364c7a1e463f3bc5e6fce039228b` |

## Run notes

**Experiment 1.**
- The prompt's theorem and system description were composed from several sections, and some details are not
  fixed by the paper (see "Statement rewrites" below).

**Experiment 2.**
- The session's worker restarted once (infrastructure), after the file had certified. The resumed turn
  re-certified the file and printed it.

