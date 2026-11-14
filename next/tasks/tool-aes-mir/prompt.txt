The paper below describes three artifacts. Build, in ACL2, the third one only: the executable MIR semantics
of Section 6, with its loader for Charon's ULLBC JSON, running the paper's AES subject. The authors'
implementation is not available; write your own, following the paper. The requirements after the paper say
what will be checked.

<paper>
Verifying RustCrypto’s Fixsliced AES-128 in ACL2:
      An Aeneas Backend and an Executable MIR Semantics*

                                                   Eric McCarthy
                                       Kestrel Institute   https://kestrel.edu


       Aeneas translates safe Rust programs into pure functional code by symbolically resolving borrows,
       with existing backends for F∗ , Rocq, HOL4, and Lean. We present an ACL2 backend for Aeneas, to-
       gether with supporting changes to Aeneas and to its Rust front end Charon, and use it to verify a real-
       world cryptographic implementation: the RustCrypto project’s 32-bit ﬁxsliced AES-128, extracted
       essentially verbatim from the upstream crate. We prove that the extracted encryption and decryption
       functions, key schedule included, equal the existing ACL2 AES-128 speciﬁcation for all keys and
       blocks, with every bounds check and assertion proven to pass. The proofs combine GL bit-blasting
       for bit-level facts about the bitsliced S-box and state packing with structured rewriting for the round
       ladders’ mask and frame algebra, over fueled recursive models of the upstream loops. To reduce the
       trust placed in the unveriﬁed Rust-to-ACL2 translation chain, we also present an executable MIR
       semantics in ACL2 covering every operation the crate uses, with a loader for the compiled crate’s
       MIR: the interpreter runs the same AES inside ACL2, reproduces the FIPS-197 vectors, and agrees
       with the same AES-128 speciﬁcation on differential tests, independently of the Aeneas translation —
       a step toward translation validation of the extraction.


1     Introduction
Rust has become a language of choice for security-critical infrastructure: its ownership type system rules
out memory errors in safe code by construction. Memory safety, however, is not functional correctness,
and the veriﬁcation of Rust programs has become an active industrial concern—the Rust standard li-
brary now runs a veriﬁcation campaign of over 16,000 proof harnesses per code change in continuous
integration [6]. Nearly all of this tooling either veriﬁes Rust in place, with speciﬁcations embedded in
the source, or extracts it to other proof assistants (Section 7). ACL2 [20], with its executable speciﬁca-
tions, industrial-strength rewriting, and an existing library of cryptographic speciﬁcations—including an
AES-128 speciﬁcation already used to verify JVM bytecode and x86 implementations [31, 32]—has met
Rust only for programs written to ﬁt a restricted subset designed for transpilation [11, 12]; it has had no
general path from the ecosystem’s existing code.
    This paper builds that path and walks it end to end, making three contributions. First, an ACL2 back-
end for Aeneas [14], the borrow-resolving translator from safe Rust to pure functional code, together
with supporting changes to Aeneas and its front end Charon [13]: extraction to an untyped, ﬁrst-order
target, with a monomorphization carve-out, defunctionalized iterators, and fueled loop models (Section
3). Second, a veriﬁed real-world cipher: the RustCrypto project’s 32-bit ﬁxsliced AES-128, vendored
essentially verbatim from the upstream crate under a mechanical audit (Section 4), with both extracted
directions—encryption and decryption, key schedule included—proved equal to the ACL2 AES-128
speciﬁcation for all keys and blocks, every assertion and bounds check proved to pass (Section 5); our
    * Substantial parts of this paper, and much of the work it describes — the Aeneas ACL2 backend, the AES-128 proof
development, and the MIR interpreter and loader — were produced by Claude Fable 5, an AI assistant from Anthropic, working
under the author’s direction; see Section 1.

                                                                                  © E. McCarthy
A. Coglio and S. Srinivasan (Eds.): 20th ACL2 Workshop (ACL2-2026)
                                                                                  This work is licensed under the
EPTCS ??, 2026, pp. 1–16, doi:10.4204/EPTCS.??.??
                                                                                  Creative Commons Attribution License.

2                                                                      Verifying Rust’s AES-128 in ACL2


emphasis throughout is the ACL2 path—the audit discipline, the proof architecture, and the proof’s
place in the family of veriﬁcations against this same speciﬁcation, after JVM bytecode and x86. Third,
an executable MIR semantics in ACL2 with a loader for the compiled crate’s MIR, giving the same
program an independent second reading that reproduces the FIPS-197 vectors and agrees with the same
speciﬁcation on differential tests (Section 6).
    The three artifacts compose into an assurance case (Figure 1): one path proves the extracted program
correct; the other path checks the compiled program independently of Aeneas and our backend, sharing
only rustc and Charon’s translation of MIR, run with different options; and the remaining trusted com-
ponents are explicit, each with a concrete plan to discharge it (Section 8). Throughout, we emphasize
reusable method over one-off proof: the mechanical vendoring audit, the division of labor between GL
bit-blasting and structured rewriting, and the probe-then-prove discovery loop are all portable to the next
crate and the next algorithm.
    In accordance with the workshop’s guidance on the use of AI assistants: the Aeneas backend, the
proof development, and the MIR semantics and loader described in this paper were developed by Claude
Fable 5, an AI assistant from Anthropic, working under the author’s direction; the author speciﬁed goals,
reviewed the work, and certiﬁed and integrated all results. This paper was drafted the same way. The
supporting materials—all books, certiﬁable from scratch—accompany the submission (Section 9).


2    Background
2.1 Rust, borrows, and purity
Rust manages memory without garbage collection through ownership: every value has one owner, other
code sees it only through borrows—shared references (&T, read-only, many at once) or mutable refer-
ences (&mut T, exclusive)—and the compiler’s borrow checker enforces the discipline statically. The
payoff for veriﬁcation is that safe Rust, despite its imperative surface, is observationally close to a func-
tional language: exclusive mutation with no aliasing means a mutable update can be read as producing a
new value. That reading is exactly what Aeneas [14] makes precise, resolving borrows symbolically and
emitting pure functions—mutation becomes value threading, and a mutable borrow passed into a call
comes back as an ordinary result.

2.2 The pipeline: rustc, MIR, Charon, Aeneas
rustc lowers source through several intermediate representations to MIR, the mid-level intermediate
representation on which borrow checking and optimization run: a small control-ﬂow-graph language of
statements, terminators, and places, with monomorphized types (generics specialized away) available.
Charon [13] extracts MIR from the compiler and serializes it (as ULLBC, and structured into LLBC)
for external analyzers; Aeneas consumes LLBC, performs its borrow-resolving symbolic execution, and
hands each backend a pure AST. Prior backends target F∗ , Rocq, HOL4, and Lean; Section 3 describes
ours. Because Aeneas does not establish termination, recursive functions are extracted with fuel.

2.3 The ACL2 AES-128 speciﬁcation
The veriﬁcation target is the AES-128 speciﬁcation in the ACL2 community books (kestrel/crypto/
aes): an executable, audited rendering of FIPS-197 [25], covering both cipher directions and the key ex-
pansion. It is not new, and that is the point—the same speciﬁcation has anchored Axe-based veriﬁcations

E. McCarthy                                                                                                    3


               Rust source   rustc         Charon                 Aeneas     pure      backend    extracted
                                     MIR            LLBC                   functions
               (aes crate)                                                                       ACL2 book


                                                                                       proved:
                                                    ULLBC
                                           Charon                             encrypt-correct
                                                                              decrypt-correct
                                                    ACL2 loader


                               MIR program             ACL2 MIR interpreter               ACL2 AES-128 spec
                              (ACL2 ﬁxtypes)                                            (kestrel/crypto/aes)
                                                        tested: FIPS-197,
                                                       differential vectors


Figure 1: Two paths from the Rust source to the ACL2 AES-128 speciﬁcation. Gray arrows are trusted
(unveriﬁed) translations; the doubled arrow is the machine-checked equivalence for all keys and blocks;
the dashed arrow is differential testing, which runs the MIR program on the ACL2 MIR interpreter (also
trusted). The two paths share rustc and Charon’s translation of MIR, run with different options: for
the ﬁrst path, Charon translates promoted MIR into monomorphized, structured LLBC; for the second,
runtime MIR into unmonomorphized ULLBC. Neither Aeneas nor the backend is on the second path.


of JVM bytecode and x86 implementations of AES [31, 32], so a proof against it places extracted Rust
in an existing family of veriﬁed implementations (Section 7).


3    An ACL2 Backend for Aeneas
Aeneas [14] ends its borrow-resolving translation with a pure abstract syntax tree: functions and alge-
braic data types with no references, no lifetimes, and no mutation, in which the effects Rust expresses
through panics—failed bounds checks, failed assertions, integer overﬂow—appear as explicit error re-
sults. Our backend prints this AST as ACL2. Each crate becomes one generated book; each Rust function
becomes a defun written in a monadic b* style over a result sum with ok and failure constructors, so
that a Rust function of type fn(...) -> T whose execution can panic becomes an ACL2 function
returning either (ok v) or a failure value that all callers propagate. For example, the one-line upstream
rotation helper
      fn rotate_rows_1(x: u32) -> u32 { ror(x, ror_distance(1, 0)) }

extracts as
      (defun aes-fixslice-encrypt-rotate-rows-1 (x)
        (b* (((ok v3) (aes-fixslice-encrypt-ror-distance 1 0)))
        (aes-fixslice-encrypt-ror x v3)))

with names systematically derived from the crate and function path.

3.1 The Rust primitives model
Generated books include a handwritten book, rust-primitives, that gives ﬁrst-order ACL2 meanings
to the Rust value layer the extracted code manipulates: machine integers of each width with checked
arithmetic (u32-add returns ok on in-range sums and a failure otherwise, with rules characterizing both
cases), total bitwise operations, monadic shifts (a shift amount at or beyond the width is an arithmetic
overﬂow, a panic under the overﬂow checks in force here), rotations, and truncating and widening casts.

4                                                                        Verifying Rust’s AES-128 in ACL2


Arrays and slices are lists with bounds-checked monadic array-index and array-update; range val-
ues are structures; and the Result/Option plumbing of the standard library completes the layer. Up-
stream debug_assert!s extract as massert forms— ok-binders on the asserted condition—so a veri-
ﬁed theorem about an extracted function establishes that every assertion and bounds check along the way
succeeds (Section 5).

3.2 Loops and fuel
Aeneas does not prove termination, so recursive functions—including the recursive loop functions pro-
duced from upstream loop { ... break } text—take an explicit fuel argument and return a dis-
tinguished out-of-fuel failure when it is exhausted. A driver passes its fuel to each loop it calls, and
each recursive call decrements it (both visible in the example of Section 3.3). Our correctness theorems
instantiate a concrete fuel that the proofs show sufﬁcient: the theorems conclude an ok result, so fuel
exhaustion is ruled out along with every other failure. The AES crate exercises this on its three upstream
loop shapes: the key schedule’s rcon fold, the encrypt round loop, and the decrypt round loop with its
descending offset counter and mid-body break.

3.3 Iterators, defunctionalized
The hardest constructs to extract are the slice iterations: upstream shift_rows_* and add_round_key
are for loops over iter(), iter_mut(), and zip. For mutable iteration, Aeneas threads backward
functions: the translated loop state includes a continuation that writes the mutated elements back into the
slice, so one argument of the loop function is itself a function, and the result is not directly ﬁrst-order. The
printer removes the higher-order structure in two steps. First, it gives the opaque iterator types concrete
ﬁrst-order models: Iter and IterMut become the underlying list paired with a cursor position, Zip
becomes a pair of iterators, and the constructor and next operations are generated to match. Second,
it defunctionalizes the write-back continuation into a list of pending writes: the identity continuation
becomes nil, each wrapping lambda becomes a cons, and generated companion functions apply the
list. After k calls to next the cursor sits at position k, and applying the pending writes newest-ﬁrst puts
each value back in the slot its next read. A dedicated probe crate in the test suite checks this translation
and its proof treatment independently of AES.
     The crate’s simplest instance shows both steps at full size. Upstream:
      fn shift_rows_2(state: &mut [u32]) {
          debug_assert_eq!(state.len(), 8);
          for x in state.iter_mut() {
              delta_swap_1(x, 4, 0x0f000f00);
          }
      }

extracts as a recursive loop function and its caller—shown lightly reformatted, with declare forms
elided and the generated standard-library names shortened:
      (defun aes-fixslice-encrypt-shift-rows-2-loop0 (n iter back)
        ;; n: fuel. iter: the IterMut model, list plus cursor.
        ;; back: the pending writes---the loop’s defunctionalized
        ;; write-back continuation.
        (if (zp n) (result-fail (err-out-of-fuel))
        (b* ((n_181 (1- n))             ; fuel decrements on each call

E. McCarthy                                                                                             5


             ((ok v182_182) (IterMut-next iter))
             (v183_183 (car v182_182)) ; an Option: Some(x) or None
             (iter_184 (cdr v182_182))) ; iterator, cursor advanced
        (option-case v183_183
          ;; None: iterator exhausted---replay the pending writes,
          ;; newest first, each into the slot its next read
          :none (ok (apply-back back iter_184))
          ;; Some(x): the loop body, then push one pending write;
          ;; this cons is "each wrapping lambda becomes a cons"
          :some (b* ((x_188 (option-some->f0 v183_183))
                     ((ok x_189) (aes-fixslice-encrypt-delta-swap-1
                                  x_188 4 251662080)))
                (aes-fixslice-encrypt-shift-rows-2-loop0
                 n_181 iter_184 (cons x_189 back)))))))

      (defun aes-fixslice-encrypt-shift-rows-2 (n state-var)
        (b* (((ok left-val_192) (vec-len state-var))
             ((ok &) (massert (equal left-val_192 8))) ; debug_assert!
             (iter_195 (IterMut state-var 0))    ; cursor at position 0
             ((ok back_198)
              (aes-fixslice-encrypt-shift-rows-2-loop0 n iter_195 nil)))
                                        ; nil: identity continuation
        (ok (IterMut->lst back_198)))) ; the updated slice




Everything Section 3.2 and this subsection describe is on the surface: the fuel n, threaded and decre-
mented; the iterators as data; and back growing one cons per element, replayed when next returns
None.




3.4 Supporting changes to Charon and Aeneas

ACL2’s ﬁrst-order world wants monomorphic code. Monomorphization is the compile-time step that
replaces each generic deﬁnition with specialized copies, one for each concrete type it is used at, until
no type parameters remain; it is how rustc ordinarily reaches machine code, and Charon [13] can
perform it in the pipeline. But done indiscriminately it bakes out instantiations that carry borrows (such
as Option<&mut u32> and the slice iterator types), erasing region information that Aeneas’s analysis
needs and causing it to reject the input. We therefore run a carve-out conﬁguration, contributed to
our Charon fork: types capable of carrying mutable borrows stay polymorphic while everything else
monomorphizes, with associated types lifted and ADT clauses removed so the result still prints ﬁrst-
order. The AES crate needs this on exactly the iterator shapes above; the conﬁguration is general, and we
plan to contribute it upstream. Monomorphization is a choice, not forced: ACL2 being untyped, generic
code could instead be printed with ﬁrst-order dictionary passing. Monomorphic code is what the proofs
want anyway—the GL bit-blasts of Section 5.2 run on concrete widths—and it keeps the generated book
executable and recognizable against its source.

6                                                                   Verifying Rust’s AES-128 in ACL2


4   Case Study: RustCrypto’s Fixsliced AES-128
4.1 Fixslicing
The RustCrypto aes crate’s [30] portable software fallback is a ﬁxsliced implementation, a constant-
time bitsliced representation due to Adomnicai and Peyrin [2]. The 32-bit variant processes two blocks
per call: the 256 bits of two AES states are transposed into eight 32-bit words, one per bit position,
so that the S-box becomes a ﬁxed Boolean circuit over the words and the whole cipher runs without
data-dependent memory access. Classical bitslicing must still permute the representation for ShiftRows
every round; ﬁxslicing instead ﬁxes the slice layout and rotates the round operations around it. The
per-round standalone ShiftRows disappears: the state simply drifts one ShiftRows frame per round,
the implementation provides four conjugated variants mix_columns_0 through mix_columns_3 that
each absorb the current frame, and the cycle closes every four rounds. What remain, and do permute
the words, are boundary and key-schedule corrections: shift_rows_2 before the ﬁnal round, and its
inverses at decryption’s entry and on the key schedule’s windows. The key schedule is pre-distorted to
match, storing round key j rotated into its frame. The S-box circuit has 113 gates—32 ANDs, 77 XORs,
and 4 XNORs; the implementation realizes them as 32 & and 81 ˆ operations, absorbing the XNORs’
inversions into the key schedule—so the stored keys also carry a compensating byte mask, cancelled at
each add_round_key. Decryption runs the same machinery in reverse, with the inverse S-box circuit
taking the mask compensation on its input instead of its output. All of this—bit-level packing, frame
and mask distortions threaded through ten rounds and an 88-word key schedule, iterator-based inner
loops, subslice borrows—is what makes the crate an exacting subject for extraction and proof, and a
representative one: it is real, shipped, optimized cryptographic Rust, not code written to be veriﬁed.

4.2 Provenance and mechanical audit
Our subject is vendored by hand from aes v0.9.1, src/soft/fixslice32.rs (repository RustCrypto/
block-ciphers, tag aes-v0.9.1, commit 507938c), and the pristine upstream ﬁle is checked in beside
it so the adaptation is diffable forever. The vendored copy began life with several de-sugarings that the
early toolchain required; as backend and Charon support landed, a sequence of eleven restoration passes
replaced each de-sugared form with the verbatim upstream text—the re-rolled encrypt and decrypt round
loops, the iter_mut()/zip loops, the key schedule’s subslice borrows and step_by fold, upstream’s
own function signatures, and all thirteen upstream debug_assert!s. A script-veriﬁed, whitespace-
and comment-insensitive, function-by-function audit keeps a classiﬁed inventory of the remaining dif-
ferences. At this writing the shared round-operation and key-schedule bodies are statement-identical to
upstream; the rest is the adaptation layer around them. The batch drivers, the key schedule’s signature,
and one inv_bitslice initializer replace the types of the cipher crate dependency we do not ven-
dor with plain byte arrays (upstream’s Array blocks and the FixsliceKeys128 alias; default() ini-
tializers written out), and four added single-block entry points—encrypt, encrypt_block, decrypt,
decrypt_block, the functions the theorems name—wrap a batch driver, duplicating the one block into
both lanes and returning lane 0. Dropped scope: AES-192/256, the cipher-crate trait implementations,
and the untaken cfg path. The theorems are about the adapted copy; they transfer to shipped RustCrypto
exactly modulo these documented deltas.

4.3 Extraction
The crate goes through the carve-out pipeline of Section 3.4:

E. McCarthy                                                                                            7


      charon rustc --preset=aeneas --monomorphize \
          --monomorphize-mut=except-types --remove-adt-clauses \
          --lift-associated-types=’*’ \
          -- --edition=2021 aes_fixslice_encrypt.rs --crate-type=rlib
      aeneas -backend acl2 -use-fuel -loops-to-rec aes_fixslice_encrypt.llbc
From the 863-line vendored source this produces one generated book of 1,852 lines deﬁning 74 func-
tions, including the extracted single-block entry points the main theorems are stated about: encrypt and
decrypt each run the extracted aes128_key_schedule and then the two-lane block function, mirror-
ing how the upstream trait implementations invoke the same internals. The generated book certiﬁes as
ordinary ACL2, with no axioms and no trust tags; every handwritten proof book of Section 5 builds on it
unchanged.


5    Correctness Proofs
The main theorems equate the extracted encrypt and decrypt—key schedule included—with the au-
dited AES-128 speciﬁcation in the ACL2 community books, for all keys and blocks:
      (defthm encrypt-correct
        (implies (and (aes::inp key) (aes::inp block))
                 (equal (aes-fixslice-encrypt-encrypt 100 key block)
                        (ok (aes::aes-128-encrypt block key)))))

      (defthm decrypt-correct
        (implies (and (aes::inp key) (aes::inp block))
                 (equal (aes-fixslice-encrypt-decrypt 100 key block)
                        (ok (aes::aes-128-decrypt block key)))))
Here aes::inp recognizes arbitrary 16-byte blocks, and 100 is the concrete fuel. The subjects are the
crate’s single-block entry points (Section 4.2): each expands the key, runs the two-block batch driver
with its block in both lanes, and returns lane 0, so the equalities are single-block statements, with the
two-lane internals covered by component lemmas along the way. Because the conclusion is an ok result,
the theorems also establish that no execution path fails: every one of the thirteen upstream assertions,
every bounds check, and every fuel decrement succeeds, for every input. The natural next theorem is
correctness of the two-block batch: each output lane equal to the speciﬁcation of its own input.

5.1 Architecture
The proof is a stack of layers (Figure 2), each stated in the vocabulary the layer below establishes,
with the decrypt stack a structural mirror of the encrypt stack. The collapse layer turns each fueled
driver into an explicit chain of round operations: the recursive loop function at fuel 100 is expanded
once per round, at each successively smaller fuel, in a deliberately minimal theory, so the ten rounds
unroll deterministically without the rewriter exploring anything else. The push-in layer moves reasoning
from the packed representation to bytes: for each round operation op, a rule inv_bitslice(op(s)) =
op-bytes(inv_bitslice(s)) rewrites the chain into per-lane byte transformations, where each op-bytes
is the operation’s byte-level speciﬁcation. The algebra layer normalizes the two ﬁxslice distortions of
Section 4: mask lemmas move the S-box constant between state, keys, and round operations, and frame
lemmas telescope one ShiftRows per round through the conjugated MixColumns variants. The ladder
layer proves the per-round invariant—after round r, a lane of the un-bitsliced state is the byte-level

8                                                                         Verifying Rust’s AES-128 in ACL2


                                extracted drivers
                          encrypt, decrypt (fueled loops)

                           collapse to explicit round chains
                                 cipher | decipher

                                                                     GL bit-blasts: S-box cir-
                        push-ins: ops become byte ops on 16-
                                                                     cuits, packing, through-
                          byte lanes through inv_bitslice
                                                                        packing op specs
                       cipherops | decipherops, decoptypes
                                                                   round, subbytes, invops*

                     mask/frame algebra: ⊕63 masks, isr c frames
                                maskalg | decmask

                              round ladders: after round
                                                                   key-schedule window facts
                             r, lane = isr c(r) (spec chainr )
                                                                      windows, keymain
                                  ladder | decladder

                            spec hop: chain recurrence =
                          aes::cipher | aes::invcipher
                                 final | decfinal

                       encrypt-correct         decrypt-correct


Figure 2: The proof architecture: each layer names its job and the encrypt | decrypt books that implement
it. Bit-level facts enter once, as GL bit-blasts, at the push-in and algebra layers; everything above and
below is structured rewriting.


speciﬁcation chain in the ShiftRows frame of round r—as nine explicit round lemmas plus a ﬁnal one,
no induction needed. The spec hop layer, ﬁnally, is a fact about the Kestrel speciﬁcation alone: its
cipher loop, read through the ﬂat 16-byte representation, is exactly the ladder’s chain recurrence, with
the extracted key schedule’s windows already bridged to aes::keyexpansion.


5.2 GL where bits live, rewriting where structure lives

Two proof styles carry the stack, with a deliberate division of labor. Facts that are true because of bit-
level computation—what the 113-gate S-box circuit computes through the packing, that bitslice and
inv_bitslice are inverses, what each conjugated MixColumns variant does to a lane of bytes—are
proved by GL [33] bit-blasting, as symbolic BDD computations over all 2256 packed states or all 2128
byte lanes. Everything else is structured rewriting under pinned theories: collapses, push-in folds, mask
and frame algebra, ladders, and spec hops never open a bit-level deﬁnition.
    The blasts required their own engineering. The forward MixColumns facts certify with variables in
natural order, but the conjugated inverse MixColumns facts—coefﬁcients 9, 11, 13, 14 rather than 1,
2, 3—exhausted memory under every book organization and memoization-clearing discipline we tried.
The ﬁx was a variable ordering: for the variant conjugated into frame c, interleaving the sixteen byte
variables along the frame’s diagonals makes each output column read contiguous BDD variables, and the
same blasts that died at seven gigabytes certify in under a minute. Memory discipline matters elsewhere
too: heavy blasts live in books with the slimmest possible include chains, memoization tables are cleared
between them, and the heaviest blast in a session is sequenced last. We could have used Axe [31] or a
SAT back end, but that would have required a trust tag, which we avoided with the GL engineering work.

E. McCarthy                                                                                            9


5.3 The decrypt mirror
Decryption mirrors the encrypt stack layer for layer, but the mask ﬂows the other way, and the difference
is instructive. On the encrypt side the state and the stored round keys both carry the S-box constant,
and the two cancel at each add_round_key. On the decrypt side the state is mask-free: each add_-
round_key deposits the key’s mask, and the following inv_sub_bytes consumes it, because the inverse
S-box circuit expects the constant on its input. So where the encrypt algebra cancels masks across
an exclusive-or, the decrypt algebra associates the mask outward, commutes it through the conjugated
inverse MixColumns (whose coefﬁcients also sum to 1, so the uniform mask is ﬁxed), and cancels it into
the true inverse S-box map. The frames likewise telescope in reverse, and the ﬁnal round key window is
stored unmasked and unrotated—so the last add_round_key lands lane 0 on the speciﬁcation’s output
exactly.

5.4 Probe, then prove
The invariants above were discovered before they were proved. For each round operation, and then for
each state of the round chains, we ran the extracted code and the speciﬁcation on FIPS-197 data and
matched the extracted value against a table of candidate spec stages under every frame rotation and mask
combination. One row of the encrypt table:
      after round 2 on the C.1 data, lane 0 of the un-bitsliced state is:
          chain2?                       no
          isr(chain2)?                  no
          isrˆ2(chain2)?               match
          isrˆ2(chain2) ⊕ 63?            no
          (frame 3 and the remaining mask variants: no)
Proved for every key and block, this row is ladder-2. The match table read off the entire ladder
invariant—including the frame schedule and exactly where masks appear and vanish—after which each
equation became a lemma to certify, by GL if bit-level and by rewriting otherwise. The ﬁrst run of
the decrypt probe was also the extracted decrypt’s ﬁrst end-to-end known-answer test. We found this
probe, then prove loop fast and robust: executability turned invariant discovery into observation, and no
discovered equation later failed to certify.

5.5 The suite
The complete development is 78 books: the generated book, the handwritten proof stack, and books
certifying FIPS-197 known-answer vectors by execution—the Appendix C.1 cipher vector in both direc-
tions with round trips, and the Appendix A.1 key-expansion example against aes::keyexpansion. All
books are in logic mode with no axioms, no skip-proofs, and no trust tags, and the suite recertiﬁes
from scratch in about twelve minutes with two parallel jobs in our development environment.


6    An Executable MIR Semantics
The veriﬁcation of Section 5 is only as trustworthy as the translation chain that produced the extracted
functions. Our second line of assurance gives MIR itself a formal semantics in ACL2, so the same
compiled program can be read a second way, independently of Aeneas and our backend; the two readings
share rustc and Charon’s translation of MIR into its serialized IR, though run with different options
(Figure 1).

10                                                                    Verifying Rust’s AES-128 in ACL2


6.1 The MIR subset and its semantics
We formalize, as ﬁxtypes and functions in the ACL2 community books, a subset of MIR sufﬁcient
for the AES crate: values, places and their projections, rvalues, statements, terminators, bodies, and a
machine state. The interpreter is small-step at the statement and terminator level, with big-step eval-
uation of operands, places, and rvalues, which are functional. Coverage follows the crate’s own MIR,
and the interpreter handles a superset of what the crate exercises: six terminator kinds (Call, Assert,
Return, SwitchInt, Goto, Unreachable, plus the Abort that Charon produces for diverging panic
calls), Assign statements and StorageLive/StorageDead markers, eight rvalue forms, and twelve bi-
nary operators, including the overﬂow-checked forms that rustc emits by default in unoptimized builds.
Thirty-three named standard-library functions are given ACL2 models, twenty-three of which the im-
ported AES program calls—rotation, little-endian byte conversion, slice length and range indexing with
their bounds panics, copy_from_slice, the TryInto slice-to-array conversion with unwrap, range it-
eration (including step_by and rev), mutable slice iteration with zip, and XOR-assignment through a
reference; the two modeled panic entry points appear in the program only as Abort terminators. The
model also ﬁxes its operating assumptions: a 64-bit target for usize (checked at import), abort-on-panic
with unwind edges dropped at import, moves that read without deinitializing, and no-op drops—each
adequate for this crate, whose MIR contains no drops (the importer rejects them) and which, like any
borrow-checked program, never reads a moved-from place. The semantics is executable, and its pieces
were exercised by dedicated probe programs as they were added—development checks, not part of the
committed suite.

6.2 Loading compiled MIR
The interpreter runs the actual crate. Charon, run without monomorphization or any of the extraction
pipeline’s reshaping ﬂags, but on rustc’s later, runtime-phase MIR (--mir elaborated, after drop
elaboration), translates the crate’s MIR into its unstructured IR and serializes it as 6.9 MB of ULLBC
JSON, normalization passes included (storage markers, pointer metadata, unit returns); an ACL2 im-
porter turns that into a program value. The importer ﬁrst expands Charon’s serialization sharing (each
shared value is written in full at its ﬁrst occurrence and referenced by id afterwards; 19,249 markers in
the AES dump), then maps JSON into the MIR ﬁxtypes with nil-tolerant navigation functions whose
termination ACL2 accepts after a handful of linear lemmas—a reusable pattern for recursion over semi-
structured input. A classiﬁer names crate functions by identiﬁer and standard-library declarations by
implementation self-type and trait; because nothing is monomorphized, one generic Index implementa-
tion serves every slice-index call, so the standard-library model to invoke is chosen per call site from the
call’s generic arguments. The whole import runs in under a second; an import test book parses the com-
mitted sample at certiﬁcation time and checks that the result is exactly the program ﬁxture the interpreter
tests run on.

6.3 Running AES
The interpreter runs the imported crate end to end: encrypt reproduces the FIPS-197 ciphertexts of
Appendix C.1 and Appendix B byte for byte, and decrypt inverts both. The vector constants are the
ones the speciﬁcation’s own test book uses. Sixty-six further inputs, two corner cases and sixty-four
pseudorandom key/block pairs generated in-book, are checked differentially: the interpreted encrypt
agrees on every one with aes::aes-128-encrypt itself, the same speciﬁcation function that the theo-
rems of Section 5 equate the Aeneas extraction to, and the interpreted decrypt inverts the pseudorandom

E. McCarthy                                                                                             11


ciphertexts. One interpreted encryption, 83,602 machine steps with each standard-library call a single
step, takes about a quarter of a second.
    During development, running the real crate exposed one semantic gap, in iterator conversion: add_-
round_key zips against a bare slice, relying on the standard library’s zip to convert it to an iterator
(IntoIterator) internally—a conversion the interpreter had not modeled. The crate also required the
Abort terminator and slice-window dereferences, which the unit probes had not needed.


6.4 What this adds to the assurance case
The two readings of the compiled crate agree: one is proved equal to the speciﬁcation for all inputs,
the other reproduces the speciﬁcation on the tested vectors. The readings share rustc up to promoted
MIR and Charon’s translation of MIR into its IR, run with different options: the extraction reads pro-
moted MIR, which Charon monomorphizes and restructures, while the interpreter reads the later runtime
MIR, unmonomorphized. The remaining stages are not shared: Charon’s restructuring, Aeneas’s borrow
resolution, and our backend on one side; rustc’s lowering to runtime MIR, our importer, interpreter,
and standard-library models on the other. Agreement on the tested vectors is therefore evidence against
errors in all of these—evidence on those inputs, not a proof for all of them. The point generalizes beyond
extraction: automation-ﬁrst tools meet Rust at the same level—Kani, for instance, translates the MIR
of each proof harness, and of the code it reaches, into CBMC’s GOTO programs through a translation
that is itself trusted [6]—so an independently tested MIR semantics could serve the ecosystem, not only
our pipeline. The remaining steps are to validate the MIR semantics itself by differential testing against
Miri [17], and to replace testing by proof—either proving the interpreted MIR equal to the extracted
functions (translation validation), or proving it equal to the speciﬁcation directly (Section 8).


7    Related Work
Rust veriﬁcation is an active ﬁeld. RustBelt [16] gave the language’s ownership discipline its founda-
tional semantic model. Most practical tools verify Rust in place, with speciﬁcations embedded in the
source: Prusti [3] builds on Viper, Creusot [7] translates to Why3, and Verus [22] extends Rust itself
with a veriﬁcation dialect; Kani [6] model-checks Rust by translating the MIR of each proof harness,
and of the code it reaches, into CBMC’s GOTO programs, with function and loop contracts extending
its bounded core, and ReﬁnedRust [9] derives foundational proofs in Iris. Miri [17], the Rust project’s
MIR interpreter, serves the ecosystem as a de facto dynamic semantics—and serves us as the differential-
testing target for ours. A second school extracts Rust into a prover’s native language. The prior path into
ACL2 is Hardin’s Restricted Algorithmic Rust (RAR) [11, 12]: programs are written in a restricted sub-
set of Rust, transpiled source-to-source into Restricted Algorithmic C, and reach ACL2 through the RAC
translator of industrial ﬂoating-point practice, an approach demonstrated on array-backed data structures,
cryptographic routines, and Knuth’s Dancing Links. Where RAR asks the program to be written in the
subset, our pipeline consumes what the ecosystem already ships, borrows included. In the same school,
hax [4] translates a restricted Rust subset for security-critical code (mutation is supported; mutable bor-
rows are restricted), and Aeneas [14], on which we build, handles borrows themselves by translating them
away, with backends for F∗ , Rocq, HOL4, and Lean. Our backend adds an untyped, ﬁrst-order target to
that family, which is what forces the monomorphization carve-out and the iterator defunctionalization of
Section 3—and what buys ACL2’s executability and industrial-strength rewriting for the proofs.
     Veriﬁed AES implementations have a long history. Ours joins a lineage attached to this same ACL2

12                                                                    Verifying Rust’s AES-128 in ACL2


speciﬁcation: with the Axe toolkit [31, 32], JVM bytecode and x86 implementations of AES were proved
equivalent to it, and the present work adds ﬁxsliced Rust as a third veriﬁed implementation family (with
Axe over our MIR semantics as a prospective fourth route, Section 8). Elsewhere, SAW [8] veriﬁes AES
implementations against Cryptol speciﬁcations by symbolic execution, and projects like HACL* [37]
take the complementary clean-slate approach, writing new cryptographic code in veriﬁcation-ﬁrst lan-
guages. Our distinguishing constraint is that the subject is shipped, third-party, optimization-heavy code,
veriﬁed essentially as-is under a mechanical audit against upstream.
    Rust and MIR have also been formalized directly. In the K framework [28], two contemporane-
ous 2018 semantics made source-level subsets executable—KRust [35] and K-Rust, since grown into
RustSEM [19], whose ownership-and-borrowing model is validated against the compiler on around
700 tests—and KMIR [29] now gives the compiler’s Stable MIR JSON export a K semantics with
concrete and symbolic execution. Of the existing efforts, KMIR is the nearest relative of our loader-
plus-interpreter. Calculi such as Oxide [36] and Featherweight Rust [26] distill the borrow checker for
metatheory. The Rust project itself maintains MiniRust [18], a precise speciﬁcation pitched just above
MIR, and a-mir-formality [23], a model of MIR and the trait system, while the Stacked and Tree
Borrows aliasing models [15, 34] supply the rules Miri enforces on unsafe code.
    Finally, the MIR interpreter continues ACL2’s long tradition of executable formal semantics used for
code proofs—the x86 ISA [10], RISC-V [21], and the Yul intermediate language [5] being recent and
classic examples—brought here to a compiler’s internal representation, with translation validation [27]
as the intended endgame for connecting the two readings of a program.


8    Future Work
Two engineering items continue the current arc. Complete de-vendoring: whole-crate extraction would
retire the vendored copy entirely, and the residual driver-signature delta of Section 4.2 dissolves once
the cipher-crate API can be consumed. Guard veriﬁcation: the suite is logic mode with no axioms,
skip-proofs, or trust tags, but the generated books declare no guards; emitting real :guard annotations
(for example, unsigned-byte-p argument types) and discharging the call-site obligations would add
well-formedness checking and execution efﬁciency.
     The larger program strengthens Figure 1 arrow by arrow. The MIR semantics itself will be validated
by differential testing against Miri [17], the Rust project’s MIR interpreter. Testing then gives way to
proof: using the Axe equivalence checker [31] to prove the interpreted MIR for AES equal to the ACL2
AES-128 speciﬁcation would upgrade the ﬁgure’s dashed arrow to a doubled one—Axe’s third AES
representation, after JVM bytecode and x86—and proving the interpreted MIR equal to the extracted
functions (translation validation [27]) would remove Aeneas and our backend from the trusted base per
program. The MIR path is also the opening to unsafe Rust, which Aeneas excludes by design, resting
as it does on the borrow checker’s guarantees. A planned byte-level memory model, with raw-pointer
operations, will let the interpreter, and the same Axe equivalence, cover unsafe code.
     Finally, the chain extends beyond MIR in both directions. Above it, a formal model of the Rust front
end is underway—executable, tested speciﬁcations of Rust’s lexical grammar and lexer, including token
trees, exist today—toward independently checking rustc’s translation from source to MIR. Below it,
Axe can lift the compiled AES binary from RISC-V machine code to logic, using ACL2’s executable
RISC-V model [21], and prove that equal to the same speciﬁcation—checking rustc’s back half just as
the front-end model checks its front half. The same AES-128 speciﬁcation then anchors veriﬁed readings
of the same program at every level from source to binary.

E. McCarthy                                                                                                13


9    Conclusion
There is now a working path from shipped, third-party Rust code to ACL2 theorems, and it has been
walked end to end on a demanding subject: a shipped, optimization-heavy, bitsliced AES-128, veriﬁed
in both directions against a speciﬁcation with a decade of prior use, with an executable MIR semantics
providing an independent reading of the same compiled program. Beyond the theorems, we hope the
reusable pieces travel: the mechanical vendoring audit as a discipline for verifying third-party code
essentially as-is, the GL-versus-rewriting division of labor and its memory discipline, and the probe-
then-prove loop that turns executable speciﬁcations into a tool for discovering invariants.
     Supporting materials accompany the submission, and the whole pipeline is reproducible from a
pinned toolchain. The extraction and the complete book suite—the generated book, the proof stack, and
the known-answer tests—build and certify from scratch inside a published development-environment
image [24] that ﬁxes the exact Charon fork, Aeneas branch, and ACL2 build together with the Kestrel
certiﬁed books; re-running the extraction there reproduces the generated books byte-for-byte, and the
full suite then certiﬁes. The MIR semantics and importer, with the serialized crate sample and its end-
to-end tests, are part of the ACL2 community books’ Rust development (master, commit [removed],
books/kestrel/rust) [1]. Appendix A records the exact identiﬁers, the commands, the expected
output, and the measured cost.


References
 [1] ACL2 Community: ACL2 Community Books. https://github.com/acl2/acl2.
 [2] Alexandre Adomnicai & Thomas Peyrin (2020): Fixslicing AES-like Ciphers: New bitsliced AES
     speed records on ARM-Cortex M and RISC-V. IACR Transactions on Cryptographic Hardware and
     Embedded Systems 2021(1), pp. 402–425, doi:10.46586/tches.v2021.i1.402-425. Artifact available at
     https://artifacts.iacr.org/tches/2021/a6.
 [3] Vytautas Astrauskas, Peter Müller, Federico Poli & Alexander J. Summers (2019): Leveraging Rust Types for
     Modular Speciﬁcation and Veriﬁcation. Proceedings of the ACM on Programming Languages 3(OOPSLA),
     doi:10.1145/3360573.
 [4] Karthikeyan Bhargavan, Maxime Buyse, Lucas Franceschino, Lasse Letager Hansen, Franziskus Kiefer,
     Jonas Schneider-Bensch & Bas Spitters (2025): hax: Verifying Security-Critical Rust Software Using Multi-
     ple Provers. In: Veriﬁed Software: Theories, Tools and Experiments (VSTTE 2024), LNCS 15525, Springer,
     doi:10.1007/978-3-031-86695-1_7.
 [5] Alessandro Coglio & Eric McCarthy (2025): A Formalization of the Yul Language and Some
     Veriﬁed Yul Code Transformations. Electronic Proceedings in Theoretical Computer Science 423,
     doi:10.4204/EPTCS.423.8. Proceedings of the 19th ACL2 Workshop.
 [6] Rémi Delmas, Zyad Hassan, Qinheping Hu, Rahul Kumar, Felipe R. Monteiro, Thanh Nguyen, Adrián Pala-
     cios, Celina Val, Michael Tautschnig, Justus Adam, Daniel Schwartz-Narbonne & Carolyn Zech (2026):
     Kani: A Model Checker for Rust. ArXiv:2607.01504; to appear at ASE 2026, Industry Showcase.
 [7] Xavier Denis, Jacques-Henri Jourdan & Claude Marché (2022): Creusot: A Foundry for the Deductive Ver-
     iﬁcation of Rust Programs. In: Formal Methods and Software Engineering (ICFEM 2022), Springer, pp.
     90–105, doi:10.1007/978-3-031-17244-1_6.
 [8] Robert Dockins, Adam Foltzer, Joe Hendrix, Brian Huffman, Dylan McNamee & Aaron Tomb (2016): Con-
     structing Semantic Models of Programs with the Software Analysis Workbench. In: Veriﬁed Software: Theo-
     ries, Tools, and Experiments (VSTTE 2016), LNCS 9971, Springer, doi:10.1007/978-3-319-48869-1_5.

14                                                                      Verifying Rust’s AES-128 in ACL2


 [9] Lennard Gäher, Michael Sammler, Ralf Jung, Robbert Krebbers & Derek Dreyer (2024): ReﬁnedRust: A
     Type System for High-Assurance Veriﬁcation of Rust Programs. Proceedings of the ACM on Programming
     Languages 8(PLDI), doi:10.1145/3656422.
[10] Shilpi Goel, Warren A. Hunt, Jr. & Matt Kaufmann (2017): Engineering a Formal, Executable x86 ISA Sim-
     ulator for Software Veriﬁcation. In: Provably Correct Systems, Springer, doi:10.1007/978-3-319-48628-4_8.
[11] David S. Hardin (2022): Hardware/Software Co-Assurance using the Rust Programming Lan-
     guage and ACL2.     Electronic Proceedings in Theoretical Computer Science 359, pp. 202–216,
     doi:10.4204/EPTCS.359.16.
[12] David S. Hardin (2023): Veriﬁcation of a Rust Implementation of Knuth’s Dancing Links using ACL2. Elec-
     tronic Proceedings in Theoretical Computer Science 393, pp. 161–174, doi:10.4204/EPTCS.393.13.
[13] Son Ho, Guillaume Boisseau, Lucas Franceschino, Yoann Prak, Aymeric Fromherz & Jonathan Protzenko
     (2025): Charon: An Analysis Framework for Rust.          In: Computer Aided Veriﬁcation (CAV),
     doi:10.1007/978-3-031-98685-7_18.
[14] Son Ho & Jonathan Protzenko (2022): Aeneas: Rust Veriﬁcation by Functional Translation. Proceedings of
     the ACM on Programming Languages 6(ICFP), doi:10.1145/3547647.
[15] Ralf Jung, Hoang-Hai Dang, Jeehoon Kang & Derek Dreyer (2020): Stacked Borrows: An Aliasing Model
     for Rust. Proceedings of the ACM on Programming Languages 4(POPL), doi:10.1145/3371109.
[16] Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers & Derek Dreyer (2018): RustBelt: Securing the Foun-
     dations of the Rust Programming Language. Proceedings of the ACM on Programming Languages 2(POPL),
     doi:10.1145/3158154.
[17] Ralf Jung, Benjamin Kimock, Christian Poveda, Eduardo Sánchez Muñoz, Oli Scherer & Qian Wang (2026):
     Miri: Practical Undeﬁned Behavior Detection for Rust. Proceedings of the ACM on Programming Languages
     10(POPL), doi:10.1145/3776690.
[18] Ralf Jung et al.:     MiniRust:   A Precise              Speciﬁcation   for   “Rust    lite / MIR   plus”.
     https://github.com/minirust/minirust.
[19] Shuanglong Kan, Zhe Chen, David Sanán & Yang Liu (2024): Formally Understanding Rust’s Owner-
     ship and Borrowing System at the Memory Level. Formal Methods in System Design 64, pp. 200–236,
     doi:10.1007/s10703-024-00460-3.
[20] Matt Kaufmann, Panagiotis Manolios & J Strother Moore (2000): Computer-Aided Reasoning: An Approach.
     Kluwer Academic Publishers, doi:10.1007/978-1-4615-4449-4.
[21] Carl Kwan (2025): RV32I in ACL2. Electronic Proceedings in Theoretical Computer Science 423, pp. 46–50,
     doi:10.4204/EPTCS.423.4.
[22] Andrea Lattuada, Travis Hance, Chanhee Cho, Matthias Brun, Isitha Subasinghe, Yi Zhou, Jon Howell, Bryan
     Parno & Chris Hawblitzel (2023): Verus: Verifying Rust Programs using Linear Ghost Types. Proceedings
     of the ACM on Programming Languages 7(OOPSLA1), doi:10.1145/3586037.
[23] Nicholas D. Matsakis et al.: a-mir-formality: A Model of MIR and the Rust Type/Trait System.
     https://github.com/rust-lang/a-mir-formality.
[24] Eric McCarthy (2026): A Reproducible Development Environment for the Aeneas ACL2 Backend.
     [removed] [removed] Prebuilt image
     [removed], built by continuous integration from pinned toolchain commits.
[25] National Institute of Standards and Technology (2001): Advanced Encryption Standard (AES). FIPS PUB
     197.
[26] David J. Pearce (2021): A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust. ACM
     Transactions on Programming Languages and Systems 43, doi:10.1145/3443420.
[27] Amir Pnueli, Michael Siegel & Eli Singerman (1998): Translation Validation. In: Tools and Algorithms for
     the Construction and Analysis of Systems (TACAS), LNCS 1384, Springer, doi:10.1007/BFb0054170.

E. McCarthy                                                                                              15


[28] Grigore Roşu & Traian Florin Şerbănuţă (2010): An Overview of the K Semantic Framework. Journal of
     Logic and Algebraic Programming 79(6), pp. 397–434, doi:10.1016/j.jlap.2010.03.012.
[29] Runtime Veriﬁcation (2023):        Introducing KMIR: Concrete and Symbolic Execution of Rust
     MIR.         https://runtimeverification.com/blog/introducing-kmir.                     Semantics at
     https://github.com/runtimeverification/mir-semantics.
[30] RustCrypto   Developers:        RustCrypto:                   aes       crate,      version      0.9.1.
     https://github.com/RustCrypto/block-ciphers.
[31] Eric Whitman Smith (2011): Axe: An Automated Formal Equivalence Checking Tool for Programs. Ph.D.
     thesis, Stanford University. https://www.kestrel.edu/research/axe/.
[32] Eric Whitman Smith & David L. Dill (2008): Automatic Formal Veriﬁcation of Block Cipher Imple-
     mentations. In: Formal Methods in Computer-Aided Design (FMCAD 2008), IEEE, doi:10.1109/FM-
     CAD.2008.ECP.10.
[33] Sol Swords & Jared Davis (2011): Bit-Blasting ACL2 Theorems. Electronic Proceedings in Theoretical
     Computer Science 70, pp. 84–102, doi:10.4204/EPTCS.70.7.
[34] Neven Villani, Johannes Hostert, Derek Dreyer & Ralf Jung (2025): Tree Borrows. Proceedings of the ACM
     on Programming Languages 9(PLDI), doi:10.1145/3735592.
[35] Feng Wang, Fu Song, Min Zhang, Xiaoran Zhu & Jun Zhang (2018): KRust: A Formal Executable
     Semantics of Rust. In: Theoretical Aspects of Software Engineering (TASE 2018), IEEE, pp. 44–51,
     doi:10.1109/TASE.2018.00014.
[36] Aaron Weiss, Olek Gierczak, Daniel Patterson, Amal Ahmed & Nicholas D. Matsakis (2019): Oxide: A
     Formal Foundation for Rust’s Borrow Checker. ArXiv:1903.00982.
[37] Jean-Karim Zinzindohoué, Karthikeyan Bhargavan, Jonathan Protzenko & Benjamin Beurdouche (2017):
     HACL*: A Veriﬁed Modern Cryptographic Library. In: ACM Conference on Computer and Communications
     Security (CCS), doi:10.1145/3133956.3134043.


A    Artifact: Reproducing the Results
The artifact is a Linux (amd64) container image with the proof path of Figure 1 built and pinned: Aeneas
with the ACL2 backend, the Charon fork with the monomorphization carve-out (Section 3.4), their Rust
and OCaml toolchains, and ACL2 with Kestrel’s certiﬁed community books. It is built by continuous
integration from the repository of [24], which also provides scripts for using the image without Docker;
the v1.0.0 release is archived on Zenodo, [removed]. The image records its own
provenance in /etc/aeneas-dev-manifest:
      aeneas = [removed]        ([removed], acl2-backend)
      charon = [removed]        ([removed]: upstream pin
                                                                [removed] + the carve-out)
      acl2   = [removed]        (4,492 certified books; SBCL 2.6.1)
      rustc = nightly-2026-06-01     ocaml = 5.3.0
      image = [removed]
      digest = [removed]

The veriﬁcation subject and all books live in the Aeneas repository. tests/acl2 holds the 19 generated
books (one per test crate; aes_fixslice_encrypt.lisp is the whole cipher, both directions, and the
rest are extraction probes and two TEA examples), the 489-line handwritten runtime rust-primitives
(Section 3.1), and 58 handwritten proof books, 42 of which are the AES stack of Section 5, topped by
encrypt-correct and decrypt-correct. The vendored subject and its pristine upstream reference sit
in tests/src, with the audit ledger (PORTING-NOTES-ACL2.md, at the repository root) and the classes
of differences documented as in Section 4.2.

16                                                                    Verifying Rust’s AES-128 in ACL2


Reproducing. With Docker, docker run -it on the image above. Without Docker (as root on Linux
amd64), the repository’s scripts/bootstrap-sandbox.sh pulls and unpacks the image over plain
HTTPS and scripts/in-dev.sh enters it. Inside, the shell starts in /work/aeneas:
      grep -l ’GENERATED BY AENEAS’ tests/acl2/*.lisp | xargs rm
      make -C tests/acl2 regen \
        CHARON=/work/charon/bin/charon AENEAS=/work/aeneas/bin/aeneas
      git status --short tests/acl2
      make -C tests/acl2 verify JOBS=1

Expected results: the rm deletes the 19 generated books, and regen re-runs Charon and Aeneas on
all 19 crates, rewriting them; git status then prints nothing, which shows both that every book was
actually regenerated and that each is byte-identical to the committed one. (Deleting ﬁrst matters: the
Makeﬁle tolerates extraction failures so that the expected-failure probe crates can run, so with the books
left in place a failure could leave a stale book and a clean status.) Then verify certiﬁes all 78 books,
leaving a .cert beside every .lisp, including aes_fixslice_final.cert and aes_fixslice_-
decfinal.cert. (Aeneas prints a few [Error] diagnostics during regen, from probe crates that de-
liberately exercise constructs the backend does not translate; they are expected and do not affect the
generated books.)

Cost. Measured on a 2-core, 7 GB machine without Docker (2026-09-05): fetching and unpacking the
image, about ﬁve minutes and about 10 GB of disk; regen, about 2 12 minutes; verify, about 16 minutes
wall clock. Certiﬁcation is memory-bound: the GL bit-blasting books need several gigabytes each, so
JOBS=1 is required on machines with less than about 12 GB of RAM (with more parallelism the affected
book is killed silently); with two parallel jobs and more memory the suite takes about twelve minutes
(Section 5.5).

What is and is not checked. regen checks that the pinned toolchain reproduces the committed books
from the Rust sources; verify checks that ACL2 accepts every deﬁnition and proof. The theorems
are about the ACL2 functions the translation produces: the correspondence to the Rust source rests on
Charon, Aeneas, and our backend printer, which are not themselves veriﬁed, and is tested by the known-
answer books (Section 5.5). On the ACL2 side the trusted base is the ACL2 core plus the speciﬁcations:
the community books’ AES-128 speciﬁcation (kestrel/crypto/aes, validated by its own FIPS-197
test book and by prior veriﬁcations) and the handwritten rust-primitives model of Rust’s integers,
arrays, slices, and result monad. Each veriﬁcation against the speciﬁcation is also evidence for it: inde-
pendently written implementations can agree with a wrong speciﬁcation only by being wrong in the same
way, and this paper adds a third, after the JVM and x86 veriﬁcations. The lemma libraries the proofs use
(kestrel/bv and kestrel/bv-arrays, centaur/gl and centaur/fty, std, arithmetic-5 and
relatives) are themselves proved, adding nothing to that trusted base: across the two main theorems’ full
include-book closure (338 books), there are no defaxioms and no trust tags. The theorems are func-
tional correctness only: nothing is claimed about timing or the compiled binary. The MIR-interpreter
artifact is separate from this image: its committed sample, tests, and generation recipe live with the ACL2
books at the commit pinned in the conclusion (see books/kestrel/rust/samples/README.md).
</paper>

<requirements>
1. `/work/subject/` holds your own adaptation of `src/soft/fixslice32.rs` from the crate, in the manner of
   Section 4.2 (AES-128 only, byte-array types instead of the `cipher` crate's, single-block `encrypt` and
   `decrypt` entry points), as a cargo crate, with `/work/subject/ADAPTATION.md` listing every difference from
   upstream.
2. Charon's ULLBC JSON for that crate, produced with `--mir elaborated` as in Section 6.2, is in
   `/work/subject/`, with the command in `/work/README.md`.
3. The ACL2 MIR semantics of Section 6.1 (fixtypes and an executable interpreter) and the JSON importer of
   Section 6.2 certify with `cert.pl`. An import test book parses the JSON at certification time and checks
   that the result equals the program value the interpreter tests use.
4. `/work/run.lisp` defines `(mir-aes-encrypt key block)` and `(mir-aes-decrypt key block)`, which run the
   interpreter on the imported crate's `encrypt` and `decrypt`. They take and return the same representation
   of keys and blocks as `aes::aes-128-encrypt` and `aes::aes-128-decrypt` in `kestrel/crypto/aes/aes-spec`.
5. By execution with `assert-event` on `mir-aes-encrypt` and `mir-aes-decrypt`, the interpreter reproduces the
   FIPS-197 AES-128 ciphertexts of Appendix C.1 and Appendix B byte for byte, and decrypt inverts both.
6. By execution, `mir-aes-encrypt` agrees with `aes::aes-128-encrypt` on 66 inputs: 2 corner cases and 64
   pseudorandom key/block pairs. The checker will also run its own inputs.
7. All books certify with `cert.pl`.
</requirements>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
Books are certified with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
Charon (upstream, `charon`) and its Rust toolchain are installed. The pristine RustCrypto `aes` 0.9.1
crate is at /opt/inputs/aes-0.9.1.crate (a .tar.gz); there is no crate registry access.
Put all your work in /work. Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done.
When you are done, run `submit tool-aes-mir`, which saves /work. Then print a short summary: the files you
wrote, and for each numbered requirement whether it is met.
