# Experiment 1: English definitions and theorem → ACL2

The model gets a paper's definitions and main theorem in English. It must write the ACL2 definitions, the
ACL2 statement and the proof, in one book that certifies. The harness (model, ACL2 version, network, audit)
is described in the [top-level README](README.md#2-the-harness-common-to-both-experiments).

## Prompt

The definitions and the theorem are copied from the paper as close to verbatim as possible, and every edit is
recorded in `harness/NN-<paper>/NOTES.md`. The rules:
- No proof sketch, no intermediate lemmas, no ACL2 code. Where the paper's definitions are given only as ACL2
  code, they are translated to English, and ACL2 names are replaced with mathematical notation.
- Remove text that identifies the paper (authorial "we", citations, numbering) and text that hints at the
  proof or the encoding.
- Where the paper has no single English sentence for the result (Linear III, fields, Chandy–Lamport), the
  theorem is composed from the paper's own sentences. These three prompts in particular deserve a careful
  look.

Template:

```
Formalize the definitions and the theorem below in ACL2, and prove the theorem.

<definitions>
{from the paper}
</definitions>

<theorem>
{from the paper}
</theorem>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
Put your work in /work/solution.lisp; it must certify with `cert.pl` (add `--acl2 acl2r` for ACL2(r)), and its last
event must be the theorem, named MAIN.
Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done. When you are done, print the final contents of /work/solution.lisp.
```

Every prompt lists both ACL2 and ACL2(r), so mentioning ACL2(r) is not a hint. The pilot (AC machine)
prompt lacks the last sentence, which was added after the pilot. The exact prompts are in each
`NN-<paper>/exp1/prompt.txt`.

## Checking

- `tools/check-exp1.sh` copies the solution to a fresh directory and rejects it if it uses a banned event or
  if its last event is not `(defthm MAIN …)`. It then certifies the solution with ACL2 8.7, and, if that
  fails, with ACL2(r) 8.7.
- `tools/audit.py` audits the transcript (see the top-level README).
- Re-certification on ACL2 master (commit 1d2b39a424): all seven pass.
- **Faithfulness of the statements is not checked by any tool.** The model chose its own definitions and
  statement. Whether these match the paper is for the reviewers to judge, and this repository gives no
  verdict. `harness/NN-<paper>/NOTES.md` records where each part of the prompt came from.

## Results

All runs were first attempts, on 2026-11-12.

| # | Paper | Model time | Tool calls | Certified (8.7) | Cert. time | Audit | solution.lisp lines / defs / theorems |
|---|---|---|---|---|---|---|---|
| 07 | AC machine | 6 min | 41 | ACL2(r) | 7.1 s | clean | 240 / 5 / 30 |
| 04 | Chandy–Lamport | 14 min | 38 | ACL2 | 0.8 s | clean | 754 / 60 / 60 |
| 05 | Linear III | 16 min | 53 | ACL2 | 1.2 s | clean | 934 / 101 / 201 |
| 06 | Fields | 38 min | 91 | ACL2 | 2.6 s | clean | 1541 / 58 / 230 |
| 03 | Flip graph | 50 min | 177 | ACL2 | 26.7 s | clean | 1750 / 98 / 255 |
| 01 | Basel | 52 min | 84 | ACL2(r) | 133.8 s | clean | 537 / 12 / 64 |
| 02 | Stirling | 58 min | 183 | ACL2(r) | 45.9 s | ⚠️ `pip install sympy` | 1387 / 27 / 213 |

- *Model time* runs from when the model received the prompt to the end of its run (setup excluded).
- *Cert. time* is `cert.pl` on `solution.lisp` alone, with its community-book dependencies already
  certified.
- Sizes come from `tools/sizes.py`. *Definitions* counts `defun`, `define`, `defun-sk`, `defmacro`, … and
  functions introduced by `encapsulate`. *Theorems* counts `defthm`, `defrule`, …, including local ones.
  (An earlier report counted definitions differently: it gave 52 / 72 / 51 for Chandy–Lamport / Linear III /
  Fields.)

**Stirling audit finding.** About 9 minutes in, the model ran `pip install sympy` (from PyPI) and used it
once, as a scratch calculator, to factor one algebraic expression while planning a lemma. ACL2 never trusts
outside computation: the certified file proves that step, like every step, in ACL2. The model fetched no
information about the problem. Still, the run breaks the "no internet" instruction, and the team has to
decide whether to count it with a footnote or rerun it.

**For comparison.** The flip-graph paper reports that its connectivity proof (19 of its 29 books) has 137
functions and 527 theorems, and that an unassisted LLM formalization of the companion paper proved
connectivity in 9 books with 409 theorems. For the other papers, the authors' developments prove much more
than the one theorem posed here, so their sizes are not comparable. `harness/NN-<paper>/NOTES.md` gives
the authors' size for scale.

## What the models did

The model chose its own route each time. Some routes differ from the paper's: for example, Basel used the
elementary cosecant-sum proof, and Basel and Stirling were both stated classically (ε–N) with non-standard
analysis used only inside the proof. Each `harness/NN-<paper>/exp1/run.md` summarizes the route and where the
model struggled.

## Next step: reviewing the statements

Each experiment-1 solution states its theorem in its own definitions. Before the results can be reported,
reviewers need to check, paper by paper, that the definitions and `MAIN` mean what the paper's theorem says:
the right objects, no hypothesis that is too strong or unsatisfiable, and no constrained function that is too
weak. Experiment 2 avoids this question by fixing the statements.
