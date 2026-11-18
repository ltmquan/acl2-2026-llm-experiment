# Can an LLM formalize and prove new ACL2 results?

This repository holds four experiments on the accepted papers of the ACL2 Workshop 2026. In each, a
current LLM (Claude Opus 5.5, medium effort, one autonomous Claude Code cloud session per task) works on its
own, and every result is re-checked by our own tools.

- **Experiment 1 — English → ACL2** ([EXPERIMENT-1.md](EXPERIMENT-1.md)). The model gets the paper's
  definitions and main theorem in English. It writes the ACL2 definitions, the ACL2 statement and the proof.
- **Experiment 2 — ACL2 statements** ([EXPERIMENT-2.md](EXPERIMENT-2.md)). The model gets the authors' own ACL2
  definitions (proofs removed) and the exact ACL2 statements of the paper's main theorems. It only has to
  prove them.
- **Experiment 3 — paper → tool** ([EXPERIMENT-3.md](EXPERIMENT-3.md)). For six tool papers, the model gets the
  paper (links to the authors' code removed) and builds the system it describes.
- **Experiment 4 — future work** ([EXPERIMENT-4.md](EXPERIMENT-4.md)). Open items from the papers'
  future-work sections and from Kaufmann's ZFC future-work list: 17 statements to prove and 3 things to build.

All runs were first attempts. Experiments 1–2: 7 of 7 theorems and 24 of 24 targets. Experiment 3: 6 tools
built, with no requirement failing a mechanical check (some need a person to judge). Experiment 4: all 20
items done. Two of our own ZFC statements were false; the models found it, and reruns with corrected
statements proved them.

**Please keep this repository private.** It contains the papers and unpublished books.

## Results at a glance

| # | Paper | Exp. 1 model time | Exp. 2 targets | Exp. 2 model time | Logic |
|---|---|---|---|---|---|
| 01 | [Gamboa — Basel problem](01-gamboa-basel/) | 52 min | 1 / 1 | 28 min | ACL2(r) |
| 02 | [Gamboa — Stirling's approximation](02-gamboa-stirling/) | 58 min ⚠️ | 3 / 3 | 3 h 30 min | ACL2(r) |
| 03 | [Luu, Medley, Manolios — flip graph](03-luu-flipgraph/) | 50 min | 4 / 4 | 58 min | ACL2 |
| 04 | [Bin Monjil & Ray — Chandy–Lamport](04-binmonjil-chandy-lamport/) | 14 min | 2 / 2 | 25 min | ACL2 |
| 05 | [Russinoff — linear algebra III](05-russinoff-linear3/) | 16 min | 6 / 6 | 55 min | ACL2 |
| 06 | [Russinoff — field extensions](06-russinoff-fields/) | 38 min | 4 / 4 | 1 h 57 min | ACL2 |
| 07 | [Cayuela — AC machine](07-cayuela-ac-machine/) | 6 min | 4 / 4 | 2.6 min | ACL2(r) |

⚠️ In the experiment-1 Stirling run, the model ran `pip install sympy` once (see
[harness/02-gamboa-stirling](harness/02-gamboa-stirling/NOTES.md)). All other runs passed the internet audit.

**Not yet checked:** whether the experiment-1 statements are faithful to the papers. Mechanical checking
cannot settle this. It is the reviewers' job, and this repository deliberately gives no verdicts. In
experiment 2 the statements are fixed, so the checker settles correctness.

### Experiments 3 and 4

| # | Paper | Experiment 3: requirements pass · manual | Experiment 4 |
|---|---|---|---|
| 01 | [Gamboa — Basel](01-gamboa-basel/) | — | Euler product: 3 / 3 |
| 02 | [Gamboa — Stirling](02-gamboa-stirling/) | — | trapezoid error 2 / 2; ratio bounds 2 / 2; FTC macro 2 · 1 manual |
| 07 | [Cayuela — AC machine](07-cayuela-ac-machine/) | — | inductance integral: 2 / 2 |
| 08 | [Coglio & Jurgensen — definductive](08-coglio-jurgensen-definductive/) | 6 · 0 | executable predicates: 4 / 4 |
| 09 | [Chen, Greenstreet & Seltzer — Smtlink 3](09-chen-smtlink3/) | 5 · 4 | — |
| 10 | [Bora & Greenstreet — Erlang in ACL2](10-bora-erlang/) | 1 · 6 | — |
| 11 | [Gamboa — Remora argument frames](11-gamboa-remora/) | 3 · 2 | — |
| 12 | [Hardin — Arrayset revisited](12-hardin-arrayset/) | 4 · 1 | — |
| 13 | [McCarthy — fixsliced AES-128](13-mccarthy-aes/) | 5 · 2 | — |
| 14 | [Cayuela — q-pulse rectifiers](14-cayuela-rectifiers/) | — | rows 6 / 6; integral master theorem 4 / 4 |
| 15 | [Jurgensen — treesets](15-jurgensen-treesets/) | — | multisets: 3 / 3 |
| 16 | [Kaufmann — set theory](16-kaufmann-set-theory/) | — | ZFC T1–T11: all; T8, T9 after correcting our statements |

No experiment-3 requirement failed a mechanical check. "Manual" means a person, ideally the authors, still
has to judge it; each grader's `CHECKLIST.md` says how. All 28 experiment 3–4 transcripts passed the audit.

## Repository layout

```
README.md            this file: papers, harness, how to reproduce
EXPERIMENT-1.md      report: English definitions and theorem → ACL2
EXPERIMENT-2.md      report: authors' ACL2 definitions and statements → proofs (incl. how definitions were extracted)
EXPERIMENT-3.md      report: paper → tool
EXPERIMENT-4.md      report: future work; also the harness of experiments 3–4 and their audit
tools/               every script used (setup, checkers, graders, audit, prompt and definitions generators, …)
NN-<paper>/          one folder per paper (01–16): only what reviewers need to review the Lisp files
  README.md          short paper summary, what each experiment asked, what to review
  source/            paper PDF, and the authors' ACL2 books where they exist
  exp1/              prompt.txt, solution.lisp
  exp2/              prompt.txt, definitions.lisp (annotated with source locations), targets.lisp, solution.lisp
  exp3/              prompt.txt (paper text + requirements), solution/ (the model's work)
  exp4/<item>/       prompt.txt, our defs.lisp / targets.lisp / admit.lisp for prove tasks, solution/
harness/exp3-4/      our records for experiments 3–4: runs/<task>/ (grade.txt, audit.txt, run.md), the task
                     drafts (planning/), the statement checks, and the scripts that generated the prompts
harness/NN-<paper>/  our records for experiments 1–2 (reviewers do not need these)
  NOTES.md           results table, how the prompt and the exp2 package were made, changes from the
                     paper's / authors' text, checker file hashes, run notes
  exp1/, exp2/       audit.txt, run.md (timing, audit, how the solution was recovered, the model's route);
                     exp2 also has checker/ (exact files the checker uses), model-facing/ (the definitions
                     file the model was given, where different) and extraction/ (scripts and logs)
```

Session transcripts are not included. The prompts are exactly the text that was sent. The branches
`results/<task>` hold what each experiment 3–4 session saved, exactly as it pushed it; `task/<task>` holds the
prompt each session read.

## 1. Papers

We included the papers that state clear theorems. We excluded papers whose contribution is an ACL2 tool,
a library interface, or a system.

### Included (7)

| # | Paper | Theorem in experiment 1 | Paper's main result? |
|---|---|---|---|
| 01 | Gamboa — *An Alternative Proof in ACL2(r) of Euler's Solution to the Basel Problem* | Σ 1/i² = π²/6 | yes |
| 02 | Gamboa — *A Mechanical Proof of Stirling's Approximation in ACL2(r)* | n! ∼ √(2πn)(n/e)ⁿ | yes |
| 03 | Luu, Medley, Manolios — *Formalizing the Connectivity Theorem for the Matrix Multiplication Flip Graph in ACL2* | over F2, n ≥ 2, the flip graph with flip and plus edges is strongly connected | yes |
| 04 | Bin Monjil & Ray — *Formalizing the Chandy–Lamport Distributed Snapshot Reordering Theorem in ACL2* | reordering a complete checkpoint segment into pre- then post-recording inputs gives an equivalent state | yes |
| 05 | Russinoff — *A Formalization of Elementary Linear Algebra: Part III* | T: V→W injective ⇒ dim V ≤ dim W, and T surjective ⇔ dim V = dim W | one of several (library chapter) |
| 06 | Russinoff — *A Formal Theory of Algebraic Field Extensions* | every tower of simple algebraic extensions over Q, F_p or a generic field satisfies the field axioms | one of several (a whole theory) |
| 07 | Cayuela — *Mechanized Verification of Complex-to-Vector Derivations in a Three-Phase AC Machine Model* | three-phase collapse Σₙ₌₀² (2/3)(A·e^{jnγ})e^{jnγ} = A, γ = 2π/3 | no: the headline (torque sign) restates a lemma, so we took the most substantial derivation |

Experiment 2 covers more of each paper: all the theorems we judged to be main results (24 targets in all;
listed in each paper's README).

### Excluded from experiments 1–2 (9)

These papers have folders 08–16, and appear in experiments 3–4 instead: the six tool papers in experiment 3,
and the rectifier, treeset and set-theory papers (plus definductive, Basel, Stirling and the AC machine) through
their future work in experiment 4.

| Paper | Why |
|---|---|
| Coglio & Jurgensen — definductive | The contribution is an ACL2 feature (a tool), not a theorem. |
| Chen, Greenstreet, Seltzer — Smtlink 3 | A tool; relies on Z3 and a trusted clause processor; states no theorem of its own. |
| Kaufmann — set theory in ACL2 | Extended abstract; integration of set theory into ACL2. |
| Jurgensen — Treesets | Library paper; most key theorems were already in ACL2 8.7. |
| Bora & Greenstreet — Erlang CPS evaluator | The evaluator is the contribution; no standalone theorem. |
| Hardin — Arrayset revisited | Toolchain case study; the definitions its theorems need are not available. |
| Gamboa — Remora argument frames | Work in progress; lemmas about an interpreter written by others. |
| McCarthy — fixsliced AES via Aeneas | The definitions are ~2,000 lines of compiler output and cannot be stated in English. |
| Cayuela — q-pulse rectifiers | The proved results are exact evaluations of sin(x)/x at fixed points; the interesting integral theorem is not proved in the paper. |

### Authors' books

| Paper | Where the authors' ACL2 books are |
|---|---|
| Basel, Stirling | **Not available**: not in the community books, and **no pull request** to the ACL2 repository |
| Flip graph | unmerged pull request acl2/acl2#2103 |
| Chandy–Lamport | unmerged pull request acl2/acl2#2105 |
| Linear III, Fields | ACL2 master, `books/projects/linear/vectors.lisp`, `books/projects/fields/` (added after 8.7) |
| AC machine | ACL2 master, `books/workshops/2026/cayuela-ac-machine/` (added after 8.7), and the author's public GitHub repository |

Copies are in each paper's `source/authors-books/`.

## 2. The harness of experiments 1–2

Experiments 3–4 use the same model, rules and audit, with a prebuilt toolchain and a different way of saving
results; see [EXPERIMENT-4.md](EXPERIMENT-4.md#harness-shared-by-experiments-3-and-4).

### Model and runs
- **Model:** Claude Opus 5.5, effort medium. Each run is a Claude Code cloud session, one per paper,
  fully autonomous: no human interaction during the run, and sessions cannot message each other.
- **Budget:** 6 hours of model time per attempt, up to 3 attempts per paper. A retry would start a fresh
  session with the failure reason and the previous `solution.lisp`. No retries were needed.
- **Anonymized prompts.** No title, authors or venue. Session titles are neutral ("task-01" …).
- Experiment 1 ran on 2026-11-12, and experiment 2 on 2026-11-12/13. The experiment-1 AC-machine run was the
  pilot.

### ACL2 version and books
- **ACL2 8.7** (tag `8.7`, commit bc6f4f49e8, released 2026-03-23) and **ACL2(r) 8.7** from the same
  sources, both built with SBCL 2.2.9. 8.7 predates almost all of the 2026 papers' material in the
  community books: fields, Linear III, Remora, definductive, Rust/MIR and `workshops/2026` were all added
  later.
- The checkout has its **git history removed**, so later commits cannot be inspected.
- **Pre-certified books:** `std`, `arithmetic`, `arithmetic-5`, `ihs`, `misc/records` (ACL2), and
  `arithmetic-5`, `nonstd/{nsa,integrals,circles}`, the Reid–Gamboa differentiator and
  `arithmetic/factorial` (ACL2(r)). The model certifies any other book on demand, in its own time.
- Setup takes 11–14 minutes per session. It is not counted in the model's time.

### Network and leakage controls
A fully offline sandbox was not possible. The cloud environment discards its saved setup whenever the
network setting changes, so setup and run must share one network, and setup needs Ubuntu packages and
GitHub. The runs therefore used the environment's "Limited" network with package registries allowed, and no
extra hosts. We did not add GitHub ourselves: in this setting it comes with the package-registry access, which
setup needs anyway (`apt` for SBCL, GitHub for the ACL2 8.7 sources). So github.com and
raw.githubusercontent.com stayed reachable during the runs. We used these controls:

1. **The prompt forbids internet use.**
2. **`git` access to GitHub is redirected** to an invalid host inside the container (`git config --system
   url.https://github.invalid/.insteadOf …`).
3. **A network probe** at the end of every setup logs what the model can reach: github.com and
   raw.githubusercontent.com over HTTPS: yes; `git` to GitHub: no; arxiv.org, example.com, the UT ACL2 site:
   no; PyPI and other package registries: yes. (The pilot run, experiment-1 AC machine, used an earlier version of the environment without the
   probe.)
4. **A deterministic transcript audit** (`tools/audit.py`) runs on the full saved transcript of every run. It
   flags any tool outside a fixed local allowlist (web search/fetch and repository tools are not on it), and
   any command or input that matches network patterns: `curl`, `wget`, `pip`, `apt`, `npm`, `git
   clone/fetch/…`, `ssh`, `nc`, Python HTTP libraries, any URL, "github", "arxiv", "pypi". It also checks the
   server-side web-search/fetch counters, and that the transcript is complete.
5. **Proof shortcuts are rejected mechanically**: `skip-proofs`, `defaxiom`, trust tags, redefinition,
   trusted clause processors, `sys-call`, `progn!`, and the like.
6. **Independent re-certification**: every solution is copied to a clean directory and certified on our own
   build.

Leakage sources we know of, which the audit looks for: ACL2 master (Linear III, fields, AC machine), the
unmerged pull requests #2103 (flip graph) and #2105 (Chandy–Lamport), the authors' GitHub repositories (AC
machine, rectifiers, Erlang), the AES proofs on GitHub, and the informal flip-graph proof on arXiv
(2609.17533). Their content was reachable over HTTPS during the runs. The audit found no access to any of
them.

## 3. Reproducing

All scripts are in [`tools/`](tools/); see [`tools/README.md`](tools/README.md) for details.

1. **Environment.** Create a cloud environment with network access to Ubuntu packages and GitHub (HTTPS),
   and use `tools/setup.sh` as its setup script. It installs SBCL, clones ACL2 8.7 without history, builds
   ACL2 and ACL2(r), certifies the books listed above, redirects `git` access to GitHub, and logs the network
   probe. To run it on a local machine instead, set `ACL2_ROOT` (default `/opt`).
2. **Start one session per paper** with the model at medium effort, and send `NN-<paper>/exp1/prompt.txt` (or
   `exp2/prompt.txt`) verbatim as the first and only message.
3. **Collect** the final `/work/solution.lisp`: the prompt asks the model to print it at the end. Save the
   transcript.
4. **Audit:** `python3 -I tools/audit.py <transcripts-dir> [task …]`, where each task directory holds the
   raw transcript pages.
5. **Check:**
   - Experiment 1: `tools/check-exp1.sh solution.lisp`. This scans for banned events, requires the last event
     to be `(defthm MAIN …)`, and certifies with ACL2, then ACL2(r).
   - Experiment 2: `python3 -I tools/check-exp2.py solution.lisp harness/NN-<paper>/exp2/checker [acl2|acl2r]`. This
     copies the checker's `defs.lisp` (and `cert.acl2`) next to the solution, scans for banned events,
     allows only `(include-book "defs")` and `:dir :system` books, requires every target with exactly its
     statement, and certifies.

Experiments 3–4:

1. **Environment.** Use the setup script of [EXPERIMENT-4.md](EXPERIMENT-4.md#harness-shared-by-experiments-3-and-4):
   it runs `setup/install.sh` from the public toolchain repository with `--acl2 8.7` or `--acl2 master`.
2. **Start one session per task** on the branch `task/<task>` and send "Your task is in the file TASK.md in
   your working directory. Read all of it, then do exactly what it says." The model saves its work with
   `submit <task>`.
3. **Audit** as above.
4. **Check:** prove tasks with `python3 -I tools/check-prove.py <solution-dir> <task-folder>`; build tasks with
   `bash tools/graders/<task>/grade.sh <solution-dir>`.

Paths inside the scripts (`/opt/acl2`, `/opt/acl2r`, `/opt/acl2-master`, `/home/user/acl2-exp`) are the ones
we used. Adjust them for another machine.

## 4. Re-checking on current ACL2

Several soundness bugs were fixed after 8.7. All seven experiment-1 solutions also certify on ACL2 master
(commit 1d2b39a424, 2026-11-12), and so do all seven experiment-2 solutions, checked by `tools/check-exp2.py`
against the same checker definitions, with every target matched (`harness/master-recheck.txt`).
