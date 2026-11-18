# fw-definductive-exec: human checklist

R1-R4 are graded mechanically. A person reviews the items below.

1. R1 "other changed files are also in /work": read the `R1INFO` lines. If the model changed other books
   files (e.g. definductive-doc.lisp), check that each one is in /work. A changed books file that is used
   but missing from /work would make grading impossible: `grade.sh` cannot see such a file, so R2/R3 would
   already fail.
2. R3 (ii) is checked by shape: at least 3 predicates, a singleton clique plus a mutual clique, and cons in
   a conclusion. Read the call and confirm that it really defines naturals plus finitely branching trees
   of naturals. If it does not, record R3 as FAIL.
3. R3 (iii): confirm that the 3-predicate clique is a typing judgement for an expression language, not an
   unrelated mutual definition.
4. R4: if it fails only in `...-run` checks with a guard violation (see grade-hidden.cert.out), the cause is
   that guard checking is on, not that the tool is wrong. The inputs were chosen to avoid this, so record
   the case and decide. H2 is informative: report it next to R1-R4.
5. Optional, not a requirement: in grade-hidden.cert.out or exec-tests.cert.out, check that a failed
   termination or adequacy obligation is reported with the obligation shown, as the prompt says.
