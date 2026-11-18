# tool-definductive: human checklist

All six requirements are graded mechanically. A person reviews only the cases below.

1. R1 FAIL whose only failed checks are formula or formals checks reported as "ONLY UP TO VARIABLE RENAMING"
   (or `...-FORMALS`). The grader requires the paper's variable names (see NOTES.md). This is a deliberate
   strict reading. The authors' own tool fails it the same way. If the experiment decides that names do not
   matter, count R1 as PASS when every other R1 check passes. Record the decision.
2. R3 FAIL where only `grade-r3-paper` fails (the model's examples.lisp passes both its static check and
   grade-r3). Open `grade-r3-paper.cert.out`, find the failing label, and see whether the failing hint is one
   of our FILLs (NOTES.md lists them). Count R3 as PASS only if the model's examples.lisp proves the same
   theorem with the hint parts the paper shows plus omitted details of the same kind (enabling generated
   definitions, expanding, arithmetic lemmas). Otherwise the failure stands.
3. R4 FAIL from the top-level run only (`r4-run-K.out`). Read the output after `@@@BEGIN@@@`. A raw Lisp
   error, an abort, or an ACL2 session that ends before `@@@END@@@` stands as FAIL. Count it as PASS only if
   the grader misread a genuine ACL2 error, e.g. an error message printed in an unusual format.
4. Any `SETUP:` line (the model shipped a file whose name collides with ours) or `R2NOTE` line (the model's
   calls add options to the paper's calls). Inspect these, but they do not change the result unless the
   option weakens the call (e.g. an option that skips proofs).
