# Tools

Every script used to run and check the experiments. Paths inside them (`/opt/acl2`, `/opt/acl2r`,
`/home/user/acl2-exp`) are the ones we used; adjust them for another machine. Python scripts are meant to be
run with `python3 -I`.

## Environment

| File | Purpose |
|---|---|
| `setup.sh` | The cloud environment's setup script used for every run. It installs SBCL; shallow-clones ACL2 tag 8.7 and deletes `.git`; builds ACL2 and ACL2(r); certifies the pre-certified books; redirects `git` access to GitHub to an invalid host; logs a network probe. Takes 11–14 minutes. |
| `setup-full-unused.sh` | Our first, larger setup script (more pre-certified books). It exceeded the setup time limit and was **not** used for any run. Kept for reference. |

## Running and auditing

| File | Purpose |
|---|---|
| `audit.py` | Deterministic transcript audit. Input: a directory per task holding the raw transcript pages (`page-*.txt`, as returned by the session event API). Extracts every tool call; flags any tool outside a local allowlist and any input that matches network patterns (`curl`, `wget`, `pip`, `apt`, `git clone/fetch/…`, `ssh`, `nc`, HTTP libraries, URLs, "github", "arxiv", "pypi"); checks the server-side web search/fetch counters and transcript completeness. `--until=<task>@<time>` cuts a run off at a time (used for the pilot, which we messaged after its run). |

## Checking

| File | Purpose |
|---|---|
| `check-exp1.sh` | Experiment 1. Copies the solution into a fresh directory, rejects banned events, requires the last event to be `(defthm MAIN …)`, certifies with ACL2 8.7 and then with ACL2(r) 8.7. |
| `check-exp2.py` | Experiment 2. Copies the solution and the checker's `defs.lisp`/`cert.acl2`, rejects banned events, requires `(include-book "defs")` and allows only community books otherwise, requires every target with exactly its statement (top level or exported from `encapsulate`/`progn`, never `local`), certifies. |

## Building the experiment-2 packages

| File | Purpose |
|---|---|
| `make-prompt-defs.py` | Makes the model-facing definitions file from a verified `defs.lisp`: drops local lemmas, strips hints and comments, wraps events in `skip-proofs`, writes a `cert.acl2` that allows `skip-proofs`. |
| `make-prompt.py` | Builds the experiment-2 prompt from the (model-facing) definitions and `targets.lisp`. |
| `world-dump.lsp` | Dumps every name a `defs` book introduces (formals, body, theorem, constraints, guard, class, measure, macro, constant). Run once for each version and `diff` the outputs; used to show that the model-facing and checker copies define the same world. |
| `annotate-defs.py` | Adds a source-location comment (`;;; <file>, lines a-b`) before each form of a `defs.lisp`, by matching it against the authors' sources. |
| `check-comments-only.py` | Confirms that two Lisp files differ only in comments and whitespace. |

The per-paper scripts used to compute definitional closures and to verify each package (V1–V3) are in each
`harness/NN-<paper>/exp2/extraction/verify/`.

## Reporting

| File | Purpose |
|---|---|
| `sizes.py` | Uniform size counts (lines, definitions, theorems) for the tables. |
