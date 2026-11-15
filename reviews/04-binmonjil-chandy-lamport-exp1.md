# Review: 04-binmonjil-chandy-lamport, experiment 1

Reviewer audit of `04-binmonjil-chandy-lamport/exp1/solution.lisp` against the prompt (`exp1/prompt.txt`) and the
authors' books (`source/authors-books/model.lisp`, `scan.lisp`, `local_swap.lisp`, `global_reorder.lisp`).

**Verdict:** no problem found that makes `MAIN` wrong or vacuous. `MAIN` is a faithful, and in places stronger,
version of the prompt's theorem: it proves the two final states *equal*, not only state-equivalent, and the
underlying lemma holds for any legal execution from a reachable state. Its hypotheses are satisfiable by a real
run with messages in flight and a genuinely reordered execution. Caveats: the segment-completion definitions
are never used by the proof, so they are checked only by the tests below (item 1), and some modelling choices
differ from the authors' model where the prompt leaves them open (items 2–4).

## Reproduction

- Image: `Dockerfile.base` (SBCL 2.6.1, ACL2 at commit `bc6f4f49e81a0711214a8d91f0d06e0e084d2204`, tag 8.7).
- Setup: certify `misc/records` and `misc/equal-by-g`.
- `tools/check-exp1.sh` (ACL2 path changed from `/opt/acl2` to `/root/acl2`): no banned events, last event is
  `(defthm MAIN …)`, `CERTIFIED with saved_acl2`. `certify-book` took 0.24 s (repo reported 0.8 s).
- `solution.cert`: the only "ttag"/"skip-proofs" matches are the certificate's field names.

## Checks

1. **Soundness.** No `skip-proofs`, `defaxiom`, trust tags, `defattach`, `:program` mode or redefinition. The only
   `local` events are the witness functions of the application/topology `encapsulate`.
2. **What `MAIN` says** (`solution.lisp:741`). If `prefix` is legal from `(init-state)`, `st` is the state it
   reaches, and `e` is a complete segment from `st`, then running pre-inputs ++ post-inputs from `st` is
   state-equivalent to running `e`. The proof goes through `reorder-from-state` (`:728`), which proves *equality*
   of the final states for *any* legal `e` and *any* snapshot id, needing only the marker invariant `cl-inv`,
   which holds in every reachable state.
3. **Definitions against the prompt and the authors' model:**
   - Checkpoint initiation (`local-ps`, `local-out`): saves the local state, expects markers from all incoming
     neighbours, installs sid = (i . counter), increments the counter, sends the marker on every outgoing
     channel. Matches `step-checkpoint`.
   - First marker: saves state, expects all incoming neighbours except j, records channel j as empty,
     forwards the marker. Later marker: removes j, status `:done` when none remain. Matches
     `handle-first-marker-msg` / `handle-non-first-marker-msg`.
   - Ordinary receive: applies the receive effect and records the message in every snapshot that is
     checkpointing and still expects j. Matches `record-msg-in-snapshots`.
   - Legality of receive: valid sender and receiver, sender is an incoming neighbour, channel nonempty. Matches
     `legal-inputp`.
   - Pre/post classification (`pre-inputs`, `post-inputs`): by whether the process already holds the target
     sid *before* the input runs, so r_p is prerecording. Matches `process-cut-step`.
   - Segment: starts with a checkpoint input, legal, target incomplete before every input, complete at the
     end. Matches `checkpoint-start-end-segment-p`. Target sid = (initiator . its counter in `st`), as in
     `checkpoint-segment-sid`.
   - State equivalence: same process list, equal channels, and per process the same application state, in/out
     neighbours, counter and sid list. Matches `state-equivalent-p`.
4. **Concrete run** (`04-binmonjil-chandy-lamport-exp1-eval.lsp`, using `defattach` with concrete functions).
   Two processes with channels both ways. Prefix: both compute, putting m1 on 1→2 and m2 on 2→1. Segment:
   1 initiates; 1 computes; 1 receives m2; 2 receives m1; 2 receives the marker; 1 receives 2's marker.
   Results: `complete-segment-p` is T. Pre = (1 checkpoint, 2 receive, 2 receive), post = (1 compute,
   1 receive, 1 receive). Final states of both orders are equal. Process 1's snapshot saved a1 and recorded m2
   as in flight on 2→1; process 2's snapshot saved its state after receiving m1, with channel 1→2 empty
   (the correct Chandy–Lamport snapshot). The segment extended past completion, cut one step short, or without
   the initiating input is rejected.
5. **Non-vacuity theorems** (`04-binmonjil-chandy-lamport-exp1-nonvac.lisp`, certified on top of
   `solution.lisp`). Under hypotheses that fix the abstract functions to the system above:
   - the prefix is legal and reaches a concrete state `*st0*`;
   - all three hypotheses of `MAIN` hold together for that prefix, state and segment;
   - the reordering is not the identity (pre/post lists as above);
   - the snapshot contents are as in item 4;
   - the over-long, too-short and no-initiation segments are not complete.

   The hypotheses are consistent: the concrete functions in the eval file satisfy them, and `defattach`
   accepted them against the encapsulate's one constraint.

## Potential problems (most important first)

1. **Low–moderate. The segment-completion definitions are not exercised by the proof.** Because the key lemma
   holds for any legal execution and any sid, `MAIN` uses `complete-segment-p` only for its `legal-exec` part.
   `checkpoint-complete`, `incomplete-before-each` and `segment-target` could be wrong without the proof
   noticing. This can only make the hypothesis too strong (vacuous) or select the wrong target, and the
   theorem holds for every target anyway. The non-vacuity theorems show the hypothesis is satisfiable and
   rejects the obvious non-examples, so I consider this checked, but only by example.
2. **Low. Compute step sends based on the *new* local state.** `local-out` builds messages from
   `(app-compute p app)`; the authors' `step-normal` sends from the *old* state, then updates. The prompt leaves
   this open (harness note, detail 2). Both readings are reasonable, and since the application is abstract,
   neither is more general.
3. **Low. Topology is unconstrained.** The solution places no constraints on `in-nbrs`, `out-nbrs` or
   `sys-procs` (no consistency between in/out lists, no uniqueness, neighbours need not be processes). The
   authors constrain all of these. This makes the theorem more general, not less. Side effect: on an
   inconsistent topology some channels can never be drained, so no segment completes there, but `MAIN` still
   holds.
4. **Low. Checkpoint initiation is unrestricted** apart from a valid process id. The authors forbid it only
   during recovery, which neither model includes. Crash, recovery and no-op inputs are absent, as the prompt
   specifies.
5. **Low. Legality of the reordered execution is not stated.** `MAIN` says the final states agree but not that
   the reordered execution is legal. Neither the prompt nor the authors' theorem asserts it (harness note,
   detail 8). The proof does establish a related fact internally (`feasible`), but it is not exported.
6. **Very low. `MAIN` concludes `state-equiv`, but the proof gives equality.** So the definition of
   `state-equiv` doesn't affect the strength of the result. It still matches the prompt.
7. **Notes, no action.** Messages are any non-marker object (including `nil`); the authors tag messages with a
   type. Snapshot records use the `misc/records` library, so a recorded empty channel reads as `nil`, the same
   as "not recorded". Only one two-process configuration was tested; larger topologies and concurrent
   snapshots were not.

## Suggested follow-up

None needed for the verdict. If wanted: a three-process example with two concurrent snapshots, and a statement
that the reordered execution is legal (both orders should already follow from the internal lemmas).
