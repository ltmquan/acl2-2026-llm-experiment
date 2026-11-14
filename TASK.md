Work in ACL2. Using the ordered-map library `std/omaps` (`omap::mapp`, `omap::update`, `omap::lookup`,
`omap::assoc`, `omap::delete`, `omap::keys`, ...), implement a library of finite multisets (bags) in a new
package `MSET`. A bag is an `omap::mapp` whose values are all positive integers (the multiplicities); the empty
map is the empty bag.

Required functions, all guard-verified. Their behavior on non-bags is your choice, but document it.
- `bagp`, `bfix` and `bequiv`, with `bequiv` an equivalence that every function below respects;
- `empty` and `emptyp`;
- `count a b` (a natural; 0 when absent) and `in a b`;
- `insert a b` (count + 1), `insert-n a n b` (count + n, for natural n), `delete a b` (count − 1, removing the
  key at 0) and `delete-all a b`;
- `cardinality b` (the sum of the counts) and `support b` (the keys, as an oset);
- `subbag x y`;
- `sum x y` (counts add), `union x y` (max), `intersect x y` (min) and `diff x y` (truncated subtraction);
- `from-list l` and `to-list b` (each element repeated by its count, in key order).

Required theorems, as rewrite rules unless that is impossible:
- closure: `bagp` of every function above that returns a bag;
- `count-of-X` for every X in {empty, insert, insert-n, delete, delete-all, sum, union, intersect, diff,
  from-list}, giving the count in terms of the counts of the arguments (for `from-list`, in terms of `duplicity`
  from `std/lists/duplicity`);
- `in` iff count > 0;
- extensionality, with a witness function `(count-diff-witness x y)` and the theorem `bag-extensionality`:
  for bags x and y, if (count (count-diff-witness x y) x) = (count (count-diff-witness x y) y), then x = y;
- `subbag` iff pointwise ≤ of counts: `subbag-when-counts-le`, with a witness function
  `(subbag-witness x y)`: if (count (subbag-witness x y) x) ≤ (count (subbag-witness x y) y) then
  (subbag x y); and `count-le-when-subbag`: if (subbag x y) then (count a x) ≤ (count a y). Also
  reflexivity, antisymmetry (for bags) and transitivity;
- `cardinality` of empty, insert, delete (when in) and sum;
- `(equal (from-list (to-list b)) (bfix b))` and `(equal (len (to-list b)) (cardinality b))`;
- commutativity and associativity of `sum`, `union` and `intersect`.

`count`, `insert` and `delete` must be implemented directly by map operations, with no conversion to lists.

Requirements:
1. The library is /work/mset.lisp, with the package in /work/package.lsp and a /work/cert.acl2 that loads it.
   It meets the specification above: the functions, guard verification, `bequiv` congruences, the theorems, and
   the implementation requirement. The checker will state the theorems in its own form and prove them from
   your rules.
2. /work/mset-tests.lisp includes the library and evaluates each function on concrete bags with `assert-event`.
3. Both books certify with `cert.pl`.

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
Books are certified with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
Put all your work in /work. Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done.
When you are done, run `submit fw-multisets`, which saves /work. Then print a short summary: the files you
wrote, and for each numbered requirement whether it is met.
