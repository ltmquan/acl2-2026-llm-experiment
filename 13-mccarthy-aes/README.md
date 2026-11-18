# 13 — McCarthy — fixsliced AES-128

**Paper:** Eric McCarthy, *Verifying RustCrypto’s Fixsliced AES-128 in ACL2: An Aeneas Backend and an Executable MIR Semantics*. PDF: `source/paper.pdf`.

Three artifacts: an ACL2 backend for Aeneas, the RustCrypto fixsliced AES-128 extracted and proved equal to the AES specification, and an executable MIR semantics that runs the compiled crate. The experiment covers the third only.

Not in experiments 1–2: the definitions are about 2,000 lines of compiler output and cannot be stated in English.

## Experiment 3 — the model built the tool from the paper

The model received `exp3/prompt.txt`: the paper's text (links to the authors' code removed) and a numbered
list of requirements. Its work is in `exp3/solution/`. The grader is [`tools/graders/tool-aes-mir/`](../tools/graders/tool-aes-mir/);
its `CHECKLIST.md` says how to judge each MANUAL requirement.

**Result:** 5 PASS (Charon JSON regenerates identically; entry points; FIPS-197 C.1 and B; 66 of our inputs agree with the AES specification), 2 MANUAL, 0 FAIL.

**To review:** R1: does `solution/subject/ADAPTATION.md` list every difference from the pristine `fixslice32.rs`? R3: the import test.
