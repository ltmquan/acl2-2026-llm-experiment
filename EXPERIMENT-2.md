# Experiment 2: the authors' ACL2 definitions and statements → proofs

In experiment 1 the model wrote its own definitions and statement, so a certified proof alone does not show
that it proved the paper's theorem. Experiment 2 removes that question. The model gets the authors' ACL2
definitions, with all proofs removed, and the exact ACL2 statements of the paper's main theorems. It only has
to prove them. The checker certifies the solution against our own copy of the definitions and requires every
target statement verbatim. The harness (model, ACL2 version, network, audit) is the same as in experiment 1;
see the [top-level README](README.md#2-the-harness-common-to-both-experiments).

## 1. Choosing the targets

For each paper we read the paper and the authors' books and listed every result the paper presents as a main
contribution. We then dropped supporting lemmas and kept the main theorems: 24 targets across the seven
papers. Each paper's README has the list, with the authors' theorem names and source locations. Some
choices:

- **Conjunctions.** Where the authors split one result into several theorems with the same hypotheses (for
  example, "`kbasis` is a basis of the kernel" is four theorems), the target is their conjunction. Results with
  different hypotheses stay separate (flip graph MAIN-3 and MAIN-4).
- **Neutral restatements.** Some authors' statements name the very construction that proves them. Giving such
  a statement would hand over the proof. We replaced these with an equivalent existential or bound form,
  using a small new definition, and proved the new form from the authors' theorem:
  - flip graph MAIN-1: "a valid path exists" (`defun-sk flip-plus-reachablep`) instead of "`main-path` is a
    valid path"; this form was approved by one of the authors;
  - fields MAIN-3: "x is a root of some monic irreducible polynomial of degree ≤ [e:f]" instead of a statement
    about `min-poly`;
  - fields MAIN-4: "every duplicate-free list of embeddings has length ≤ [e:f]" instead of a statement about
    the list `embeddings`.
- Targets are named `MAIN-1`, `MAIN-2`, …, with no hints. Their statements are the authors' text otherwise;
  `defrule`/`defthmd` become `defthm`.

## 2. How the definitions were extracted

For every paper, one file, `defs.lisp`, holds exactly the definitions that the target statements need. It is
built as follows.

1. **Closure.** Start from the symbols in the target statements, and repeatedly add the authors' definitions
   of the functions and macros they mention: in bodies, guards and measures, and in the signatures and
   constraints of encapsulates. Where possible this was computed in ACL2 from the authors' world, not
   textually. Nothing else is included. So the proof machinery the authors defined for themselves (for
   example `main-path`, `reorder-inputs`, `min-poly`, the Stirling integrals) is absent unless a statement
   needs it.
2. **Verbatim copy.** Each definition is copied verbatim from the authors' source, with paper-specific
   exceptions. These are listed in `harness/NN-<paper>/NOTES.md` and in
   `harness/NN-<paper>/exp2/extraction/NOTES.md`: removed `///` sections (flip graph), a renaming to avoid a name clash (AC
   machine), one changed termination hint (fields). Include-books are the authors' own, using the 8.7
   community books.
3. **Admission only.** All of the authors' theorems are dropped, except constraints exported by
   encapsulates, which are part of the definition. Where a definition needs lemmas to be admitted
   (termination, guards, encapsulate witnesses), they are added as `local` events: the authors' own lemmas
   where possible, and minimal ones of ours otherwise. A greedy pass removed every local event that was not
   needed.
4. **Annotation.** The paper folder's `exp2/definitions.lisp` is the same file with a comment before each form giving its
   source file and line range (`tools/annotate-defs.py`). `tools/check-comments-only.py` confirms that the
   annotated file and the checker's `harness/NN-<paper>/exp2/checker/defs.lisp` differ only in comments. `harness/NN-<paper>/NOTES.md`
   lists the SHA-256 of the checker files.

For Basel and Stirling, the authors' books are not available: they are not in the community books and there
is no pull request. Their (one-definition) packages were transcribed from the paper and compared with the
paper's text.

### Verification of each package

| Check | What it shows |
|---|---|
| V1 | `defs.lisp` certifies on ACL2 8.7 (or ACL2(r) 8.7) with no `skip-proofs`, `defaxiom` or trust tags. |
| V2 | A book that includes `defs` and admits every target under `skip-proofs` certifies: the targets are well-formed over these definitions. |
| V3 | The package means what the authors' books mean. In the authors' world, every target is proved from the authors' theorems by `:use` with `(:in-theory nil)`. Every definition is identical to the authors': a dump of formals, body, guard, measure, symbol class and constraints is byte-identical between the two worlds, or including `defs` after the authors' books succeeds because every event is redundant. Linear III and fields used ACL2 master here, where the authors' books live; for Linear III the dumps differ only in the formals and guards that master adds to the library field functions `f+ f* f- f/`. Basel and Stirling were compared token by token with the paper. |
| Checker | `check-exp2.py` rejects a `skip-proofs` solution and a solution with a wrong statement. Where possible, it accepts a real solution. |

The scripts and logs are in each `harness/NN-<paper>/exp2/extraction/verify/`, and `extraction/NOTES.md` records the
results. Some logs mention scratch paths, shown as `<scratch>`.

### The model-facing copy

For four papers (AC machine, flip graph, Linear III, fields) `defs.lisp` contains local lemmas. Lemmas
needed to admit a definition can be steps of the target proofs (in Linear III, for example, the local lemmas
include `vdepp-vcomb-v0`). The model was therefore given a different copy, `harness/NN-<paper>/exp2/model-facing/defs.lisp`,
made by `tools/make-prompt-defs.py`:
- every top-level `local` event is dropped, and so are local theorems inside encapsulates (local definitions,
  such as encapsulate witnesses, stay);
- `:hints`, `:guard-hints` and `:measure-hints` are removed;
- full-line comments are removed;
- every remaining event, except `in-package`, `include-book`, `in-theory`, `defmacro`, `defconst` and similar,
  is wrapped in `skip-proofs`;
- `model-facing/cert.acl2` adds `; cert-flags: ? t :skip-proofs-okp t`, so that books including `defs` can be
  certified in the model's sandbox.

The prompt tells the model that some definitions use `skip-proofs`, and that its own files must not, because
the solution is checked against fully proved definitions. To confirm that the two copies define the same
logical world, `tools/world-dump.lsp` dumped every name each copy introduces (formals, unnormalized body,
theorem, constraints, guard, symbol class, measure, macro body, constant value). The dumps are identical: AC
machine 1825 names, flip graph 2194, fields 719, Linear III 1506. For the other three papers the model got
the checker's file, without comments.

## 3. Prompt

Generated by `tools/make-prompt.py` from `defs.lisp` (or the model-facing copy) and `targets.lisp`. Comments
are removed, including the comments in `targets.lisp` that name the authors' theorems:

```
Prove the theorems below in ACL2.

1. Create /work/defs.lisp[, /work/cert.acl2] containing exactly the text between the tags. defs.lisp holds
the definitions the theorems use. Do not modify these files.[ skip-proofs note]

<defs.lisp>
…
</defs.lisp>
[<cert.acl2> … </cert.acl2>]

2. Write /work/solution.lisp. It must (include-book "defs") and then prove every theorem in <theorems>, each
with exactly the name and statement given (MAIN-1, …). You may add your own definitions and lemmas before
them.

<theorems>
…
</theorems>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
/work/solution.lisp must certify with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done. When you are done, print the final contents of /work/solution.lisp.
```

The exact prompts (1–44 KB) are in each `NN-<paper>/exp2/prompt.txt` and in the paper's README.

## 4. Checking

`tools/check-exp2.py solution.lisp <checker-dir> [acl2|acl2r]`:
1. copies the solution and the checker's `defs.lisp` (and `cert.acl2`) into a fresh directory, ignoring the
   model's own copy;
2. rejects banned events (`skip-proofs`, `defaxiom`, `defttag`, `:ttags`, redefinition, `progn!`, `sys-call`,
   trusted clause processors, …);
3. requires `(include-book "defs")`, and allows no other include except community books (`:dir :system`);
4. requires every target to appear as a `defthm` with exactly the target's name and statement (as
   s-expressions, ignoring case), at top level or exported from an `encapsulate`/`progn`, never under
   `local`;
5. certifies with `cert.pl`.

The fourth check originally accepted only top-level theorems. It was widened after the Basel run, whose
MAIN-1 sat inside a non-local `encapsulate` (see `harness/01-gamboa-basel/NOTES.md`). A local MAIN is still rejected.

## 5. Results

All runs were first attempts, launched together late on 2026-11-12 (UTC).

| # | Paper | Targets proved | Model time | Tool calls | Certified (8.7) | Cert. time | Audit | solution.lisp lines / defs / theorems |
|---|---|---|---|---|---|---|---|---|
| 07 | AC machine | 4 / 4 | 2.6 min | 18 | ACL2(r) | 1.5 s | clean | 100 / 0 / 15 |
| 04 | Chandy–Lamport | 2 / 2 | 25 min | 85 | ACL2 | 4.0 s | clean | 1063 / 19 / 139 |
| 01 | Basel | 1 / 1 | 28 min | 120 | ACL2(r) | 11.6 s | clean | 712 / 9 / 84 |
| 05 | Linear III | 6 / 6 | 55 min | 194 | ACL2 | 3.6 s | clean | 2038 / 20 / 248 |
| 03 | Flip graph | 4 / 4 | 58 min | 166 | ACL2 | 56.1 s | clean | 3420 / 91 / 455 |
| 06 | Fields | 4 / 4 | 1 h 57 min | 237 | ACL2 | 750.5 s | clean | 3101 / 58 / 552 |
| 02 | Stirling | 3 / 3 | 3 h 30 min | 222 | ACL2(r) | 390.7 s | clean | 1743 / 25 / 217 |

Column definitions are as in experiment 1. Certification is against the checker's `defs.lisp`. No run needed
a retry, and none came near the 6-hour limit.

Three solution files were not printed in full at the end of the run, so they had to be rebuilt from the
transcript: flip graph (from the model's own reads of the file), Linear III and fields (by replaying all of
the model's file-changing commands). Each rebuilt file matches the size the session recorded, and it
certifies. Each `harness/NN-<paper>/exp2/run.md` gives the details.

### Why experiment 2 took longer than experiment 1

Experiment 2 took longer on five of the seven papers (not on Basel or the AC machine), and it produced
larger solutions on six (not on the AC machine). The transcripts suggest four reasons:
- **More theorems.** Experiment 2 has 24 targets against 7 theorems, and the extra targets are often the
  harder ones: Wallis's product and the ln form for Stirling; completeness and soundness of the algorithm
  translation for the flip graph; kernel and image bases for Linear III; roots, minimal polynomials and
  embeddings for fields.
- **Fixed representations.** In experiment 1 the model chose definitions that suited its proof. Here it had to
  work with the authors' definitions: the 21-function mutual recursion for fields, the constructive
  definitions over row reduction for Linear III, the full system model for Chandy–Lamport.
- **Missing libraries.** Some of the authors' proofs rely on later books that are not in 8.7. Linear III needs
  master Part II lemmas. Fields needs `projects/groups` and `projects/linear`, which are not pre-certified;
  the model waited for them to certify.
- **Assembly.** The longer runs developed each target in separate books and then merged them. Merging alone
  took about 1.3 h for Stirling, because rules from one section made proofs in another hang.

## 6. Re-check on ACL2 master

All seven solutions also certify on ACL2 master (commit 1d2b39a424, 2026-11-12), with the same checker and
checker definitions, every target matched. Certification times on master are close to those on 8.7 (Fields 782 s vs 750 s, Stirling 412 s vs 391 s)
(`harness/master-recheck.txt`). All experiment-1 solutions also pass on master.
