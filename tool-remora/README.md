# Lifting of binary primitive operations in the ACL2 Remora interpreter

This formalizes, in ACL2, the work in "Towards Formalizing the Semantics of
Lifting Argument Frames When Evaluating Remora Expressions" (Gamboa,
ACL2-2026). It reasons about the Kestrel Remora interpreter in the community
books (`books/kestrel/remora`, in particular `eval-app`, `eval-app-list` and
`eval-app-cell` in `expression-evaluation.lisp`). Everything is in package
`REMORA`.

There are no `skip-proofs`, `defaxiom`, trust tags or redefinitions.

## Files

| File | Contents |
|------|----------|
| `cert.acl2` | Portcullis: the `REMORA` package from `kestrel/remora/portcullis`. |
| `helpers.lisp` | The paper's helper functions (requirement 1). |
| `lifting.lisp` | The paper's five theorems and the supporting lemmas (requirement 2). |
| `commutativity.lisp` | The commutativity corollary at the end of Section 3 (requirement 3). |
| `commutativity-total.lisp` | A stronger form of the commutativity corollary. |
| `examples.lisp` | The examples of Section 2, checked by evaluation (requirement 4). |
| `top.lisp` | Includes everything. |

To certify, run `cert.pl top.lisp` here (requirement 5). The Remora books
`kestrel/remora/evaluation-rules`, `parser-interface` and `validator` are
certified on the way if they are not certified yet.

## Helper functions (`helpers.lisp`)

* `list-of-primop-int-binary`: every cell is an integer binary primitive
  operation before it has received any argument (`:int-binary` stage, e.g. `+`).
* `list-of-base-values`: every cell is a base value.
* `expr-is-nested-vectors-of-base-values`: the value is a base value or a
  vector of such nested vectors. Empty vectors (`:vector-empty`) are excluded,
  so every dimension of such a well-formed value is positive. That rules out
  the `eval-app-empty` branch of `eval-app` (see below).
* `get-cells-from-expr-value`: all rank-0 cells, in row-major order. It is
  `(cells-at-depth-in-expr-value val (len (dims-of-expr-value val)))`.
* `pairwise-curry-binary-fn`: applies each binary operation to its first
  argument and gives the curried `:int-binary-x` operations. This is the
  `:int-binary` case of `eval-primop-fun-fo`.
* `pairwise-curry-binary-x-fn`: applies each curried operation to its second
  argument and gives the results. Errors propagate, as in `eval-app-list`.
* `pairwise-binary-args-fn`: applies each binary operation to both arguments
  at once. This is the plain ACL2 "map" in the paper's commutative diagram.
* Auxiliary functions: `int-binary-op-apply`, which applies an
  `int-binary-primop` to two values as the interpreter does through the
  `prim-int-...` functions, and `list-of-primop-int-binary-x`.

## Theorems of the paper (`lifting.lisp`)

All five are proved with the paper's names and statements, against the
current interpreter:

* `propagate-not-reserrp-cells-at-depth-in-expr-value-list-when-vector`
* `eval-app-list-when-primop-binary-and-bases`
* `eval-app-when-funval-is-binary-op`
* `undo-expr-value-with-nonempty-dims-3`
* `eval-app-when-funval-is-binary-op-fully`

The task allows two readings, and both are used: `arg2l` in the paper's
`eval-app-when-funval-is-binary-op-fully` is read as `arg2`, and `pos-listp`
in `undo-expr-value-with-nonempty-dims-3` is written `acl2::pos-listp`.

**Changes to the statements: none.** No statement had to change because of
changes in the interpreter. Two changes in the interpreter matter, and both
are handled by definitions and lemmas, not by changing a statement:

* `eval-app` now checks the argument's shape with `check-list-suffix`.
* `eval-app` now sends principal frames with a zero dimension to
  `eval-app-empty`. The hypothesis `expr-is-nested-vectors-of-base-values`
  excludes empty vectors, so the frames never contain 0 (lemma
  `pos-listp-of-dims-when-nested`).

The interpreter also has its own result checks in `eval-app` ("TODO:
eliminate via proof"). These are discharged by the `(not (reserrp ...))`
hypotheses, in the partial-correctness style of the paper.

Main supporting lemmas, besides those of the paper:

* `cells-at-depth-when-nested`: the cells of a nested vector of base values,
  and how many there are.
* `cells-at-depth-of-expr-value-with-nonempty-dims`: the round trip from cells
  to an array and back to cells, with no error hypothesis.
* `eval-app-when-funval-is-curried-binary-op-vector`: one `eval-app` step when
  the function is an array of curried operations. These are the "similar but
  more complex" theorems mentioned in the paper.
* List glue lemmas, such as `repeat-each-of-pairwise-curry-binary-fn` and
  `pairwise-curry-binary-x-fn-of-pairwise-curry-binary-fn`.

`eval-app-when-funval-is-binary-op-fully` is proved by chaining the one-step
theorems. The glue lemmas then reduce the curried computation to
`pairwise-binary-args-fn`.

## Commutativity (`commutativity.lisp`, `commutativity-total.lisp`)

* `eval-app-of-int-add-commutative`: suppose `funval` is integer addition,
  and `arg1` and `arg2` are well-formed nested vectors of base values with
  compatible (prefix-related) shapes. If both `(+ arg1 arg2)` and
  `(+ arg2 arg1)` evaluate without error, they are equal. The proof follows
  the paper. It applies `eval-app-when-funval-is-binary-op-fully` to both
  sides, then uses pure list reasoning: `pairwise-binary-args-fn-commutative-for-add`,
  and the fact that the principal frame does not depend on the order of the
  two frames.
* `eval-app-of-int-add-commutative-strong`: the stronger form. Its only
  hypotheses are the operator, well-formedness and the nested-vector
  conditions, plus success of `(eval-app funval (list arg1 arg2) limit)`. From
  these it proves that `(eval-app funval (list arg2 arg1) limit)` also
  succeeds and gives the same value.
  - Shape compatibility is derived from success (`join-when-...`).
  - So are the integer-ness of all cells and a lower bound on `limit`
    (`facts-when-...`).
  - A sufficient condition for success (`eval-app-of-int-add-not-reserrp`)
    then gives success in the other order.

## Examples (`examples.lisp`)

The examples are checked by evaluation (`assert-event`), in two ways: directly
with `eval-app` on the value of `+` (which is checked to be the value of `"+"`
in `primop-values`), and from Remora syntax through the parser, the static
checker and the evaluator. The ill-formed cases are also run through the
evaluator alone.

* `(+ 1 2)` gives `3`, and `[1 2 3] + [4 5 6]` gives `[5 7 9]`.
* `[1 2] + [[1 2] [3 4]]` gives `[[2 3] [5 6]]`, in both argument orders.
* These ill-formed additions give errors:
  - `[1 2 3] + [4 5]`
  - `[1 2 3 4] + [[1 2] [3 4]]`
  - `[1 2] + [[1 2] [3 4] [5 6]]`, which has the shapes `[2]` and `[3 2]`
    that the paper describes.
  - `[1 2] + [[1 2] [[5 6]]]` as literally written in the paper. Its second
    argument is not even a well-formed array. It is checked to be ill-formed,
    and to give an error from Remora syntax.
* The right-hand side of `eval-app-when-funval-is-binary-op-fully`, evaluated
  on `[1 2] + [[1 2] [3 4]]`, equals the interpreter's result.
