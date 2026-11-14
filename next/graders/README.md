# Graders (written before any run)

- `check-prove.py <work-dir> <task-dir>`: the checker for the 17 prove tasks (`fw-euler-product`,
  `fw-trapezoid`, `fw-stirling-bounds`, `fw-inductance`, `fw-rectifier-rows`, `fw-rectifier-master`, `zfc-t1`
  … `zfc-t11`). It extends the experiment-2 checker:
  - definitions in `admit.lisp` must be admitted with the same kind, name, formals and body;
  - ZFC targets are `defthmz` with open `:props`, and direct `zfc-table` edits, `table-redo` and `with-props`
    are banned;
  - certification uses default cert flags, so `defthme`'s silent `skip-proofs` fallback fails.
  It was tested on toy tasks: it accepts a correct solution, and rejects a changed definition body, a local
  target, `skip-proofs`, a changed statement, a direct `zfc-table` edit, and a `defthm` given in place of a
  `defthmz`. On every real task it reports an empty solution as missing all targets and definitions.
- `<id>/` for each of the nine build tasks: `grade.sh <work-dir>` with grader books, `CHECKLIST.md` for what a
  person must inspect, and `NOTES.md` for how the grader was validated.
