# 14 — Cayuela — q-pulse rectifiers

**Paper:** P. O. Cayuela, *Mechanized Verification of q-Pulse Rectifier Voltage Equations in ACL2(r): Certified Results and a Refined Roadmap*. PDF: `source/paper.pdf`.

Thirteen ACL2(r) theorems on the exact-value layer of a unified rectifier model: exact values of Sa(x) = sin(x)/x, per-topology instances, a confirmed coefficient error and a table inconsistency. The integral-based master theorem is left as future work.

Not in experiments 1–2: the proved results are exact evaluations of sin(x)/x at fixed points; the interesting integral theorem is not proved in the paper.

## Experiment 4 — future work

### Six-phase and twelve-pulse rows (Section 8 future work)

`exp4/rectifier-rows/`: the prompt (`prompt.txt`), our definitions (`defs.lisp`), the theorems to prove
(`targets.lisp`), and the model's work (`solution/`). The checker (`tools/check-prove.py`) requires
every target verbatim against our `defs.lisp`.

**Result:** 6 / 6 targets. The task fixes explicit conventions for the peak, since the printed twelve-pulse entry does not fit the master equation; the task does not mention this.

**To review:** whether our statement captures the future-work item. The checker settles the proof.

### The integral master theorem (Section 6)

`exp4/rectifier-master/`: the prompt (`prompt.txt`), our definitions (`defs.lisp`), the theorems to prove
(`targets.lisp`; `admit.lisp`: the integrals, to admit verbatim), and the model's work (`solution/`). The checker (`tools/check-prove.py`) requires
every target verbatim against our `defs.lisp`.

**Result:** 4 / 4 targets: V_DC and V_RMS as integrals equal the closed forms for every real firing angle, plus the three-phase midpoint and bridge instances.

**To review:** whether our statement captures the future-work item. The checker settles the proof.
