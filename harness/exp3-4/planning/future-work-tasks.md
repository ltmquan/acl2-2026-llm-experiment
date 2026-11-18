# Future-work tasks from the ACL2-2026 papers (draft for approval)

Status: DRAFT, 2026-11-13. Nothing here has been proved. The candidate ACL2 statements were checked only
for parsing and admission under `skip-proofs` (scratch files in `/home/user/acl2-exp/ext/scratch/`).
Leakage was checked against `/opt/acl2` `origin/master` @ `1d2b39a` (2026-11-12) and against the local copies of
the authors' books. There was no network access, so the authors' public GitHub repositories were **not** checked.

Conventions:

* "Task statement" is the text we would give the model. It is written for the default condition
  (English definitions plus English theorem; the model writes the definitions, the statement and the proof). It
  names no paper, author or venue, and it gives no proof hints.
* "Candidate ACL2 statement" is our reference formalization. It is used for grading and, if we decide so,
  for a prove-only variant. Unless noted, it uses only names that exist in 8.7.
* ACL2(r) 8.7 = `/opt/acl2r/saved_acl2r` with `/opt/acl2r/books`; ACL2 8.7 = `/opt/acl2/saved_acl2` with `/opt/acl2/books`.
* Global rules, as in the earlier experiment: no ttags, no `skip-proofs`, no `defaxiom` (except the "given"
  axioms named below, which we would supply).

Library names used below, checked in 8.7 (ACL2(r) tree):

| Name | File |
|---|---|
| `i-small`, `i-close`, `i-large`, `i-limited`, `standard-part`, `standardp`, `defun-std`, `defthm-std` | built into ACL2(r) (`/opt/acl2r/axioms.lisp`) |
| `acl2-sine`, `acl2-cosine`, `acl2-pi` | `nonstd/nsa/trig.lisp` |
| `acl2-exp` | `nonstd/nsa/exp.lisp` |
| `acl2-ln` | `nonstd/nsa/ln.lisp` |
| `acl2-sqrt` | `nonstd/nsa/sqrt.lisp` |
| `interval`, `interval-p`, `inside-interval-p`, `interval-left-endpoint`, ... | `nonstd/nsa/intervals.lisp` |
| `partitionp`, `deltas`, `dotprod`, `mesh` | `nonstd/integrals/integrable-functions.lisp` |
| `make-small-partition` | `nonstd/integrals/make-partition.lisp` |
| `ftc-2` (generic FTC over constrained `rcdfn`/`rcdfn-prime`/`rcdfn-domain`), `int-rcdfn-prime` | `nonstd/integrals/ftc-2.lisp` |
| `factorial` | `arithmetic/factorial.lisp` |

`git diff 8.7 origin/master -- books/nonstd books/arithmetic/factorial.lisp` is empty. So the ACL2(r) analysis
library is the same in 8.7 and on master, and none of the analysis items has been done there since.

---

## 1. Euler product for ζ(2)

**Source:** conclusion of the Basel paper, which plans to formalize the Euler product.

### Task statement

> Work in ACL2(r) 8.7. Define:
>
> * `basel-series(i, n)` = Σ_{k=i}^{n−1} 1/k² (0 when n ≤ i). Use exactly the definition below; the upper bound is exclusive.
> * `primep(n)`: n is an integer ≥ 2 whose only positive divisors are 1 and n.
> * `euler-zeta2-product(i, n)` = ∏ over the primes p with i ≤ p < n of 1/(1 − p^(−2)). The empty product is 1.
>
> Prove these two theorems:
>
> 1. (Finite two-sided bound; this is a statement about rationals.) For every integer n ≥ 2,
>    basel-series(1, n) ≤ euler-zeta2-product(2, n) ≤ basel-series(1, n) + 1/(n − 1).
> 2. (Euler product, nonstandard form.) For every positive integer n that is infinitely large,
>    euler-zeta2-product(2, n) is infinitely close to basel-series(1, n).
>
> Optional third theorem. Assume as given the theorem "for every infinitely large positive integer n,
> basel-series(1, n) is infinitely close to π²/6". Prove that euler-zeta2-product(2, n) is infinitely close to
> π²/6 for every infinitely large positive integer n.
>
> You may define `primep` and any helper functions yourself. You may also use any book in the 8.7 distribution.

Definition we would give verbatim (it fixes the indexing convention):

```lisp
(defun basel-series (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      0
    (+ (expt i -2)
       (basel-series (1+ i) n))))
```

### Dependencies and base

* Base: **ACL2(r) 8.7 as is.** Theorem 1 is plain-ACL2 content: it also admits in ACL2 8.7, and the model may
  prove it there and then port it, or prove it directly in ACL2(r).
* The statement uses only built-ins plus `acl2-pi` (`nonstd/nsa/trig`, needed only for the optional theorem 3).
* The "given" in theorem 3 is the Basel main theorem, `basel-series-closed-form-close`. It is a separate,
  very hard task in the main experiment, so we would supply it as an axiom. Theorem 3 is then a one-step corollary.
* Possibly useful 8.7 material (not given, not mentioned to the model): `projects/numbers/euclid.lisp`
  (package `DM`, `primep`, `prime-fact-uniqueness`). Under ACL2(r) it is not certified, and it is not known whether it certifies there.

### Candidate ACL2 statement

The statement admits under `skip-proofs` in ACL2(r) 8.7. The defs and theorem 1 also admit in ACL2 8.7.
`assert-event` checks passed: `(euler-zeta2-product 2 10)` = 4/3·9/8·25/24·49/48, and the bound holds for all
2 ≤ n < 80 with exact rationals. File: `scratch/t1-euler.lisp`, `scratch/t1-plain.lisp`.

```lisp
(include-book "nonstd/nsa/trig" :dir :system)   ; only for acl2-pi (theorem 3)

(defun least-divisor-from (k n)
  (declare (xargs :measure (nfix (- (1+ n) k))))
  (if (and (integerp k) (integerp n) (< 1 k) (<= k n))
      (if (integerp (/ n k)) k (least-divisor-from (1+ k) n))
    nil))

(defun primep (n)
  (and (integerp n) (<= 2 n) (equal (least-divisor-from 2 n) n)))

(defun euler-zeta2-product (i n)          ; prod over primes p, i <= p < n
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      1
    (* (if (primep i) (/ (- 1 (expt i -2))) 1)
       (euler-zeta2-product (1+ i) n))))

(defthm euler-zeta2-product-lower
  (implies (and (integerp n) (<= 2 n))
           (<= (basel-series 1 n) (euler-zeta2-product 2 n))))

(defthm euler-zeta2-product-upper
  (implies (and (integerp n) (<= 2 n))
           (<= (euler-zeta2-product 2 n)
               (+ (basel-series 1 n) (/ (- n 1))))))

(defthm euler-product-close-to-basel-series
  (implies (and (posp n) (i-large n))
           (i-close (euler-zeta2-product 2 n) (basel-series 1 n))))

;; optional, with GIVEN axiom basel-series-closed-form-close
(defthm euler-product-zeta-2
  (implies (and (posp n) (i-large n))
           (i-close (euler-zeta2-product 2 n) (/ (expt (acl2-pi) 2) 6))))
```

Grading note: the model's own `primep` must be shown equivalent to ours, or must be checked by hand to mean
"prime". The numeric checks above pin down the intended semantics.

### Leakage

* No hits on master for `euler-product`, `zeta`, `basel`, or `stirling` outside unrelated files.
  `books/doc/100-theorems.lisp` still has entry 14 (Basel) commented out.
* No author books exist for this paper.
* **Not leaked.**

### Difficulty and recommendation

* **Hard.** The upper bound needs the unique-factorization correspondence between products of truncated
  geometric series and sums over smooth numbers, together with a finitary limit argument. The nonstandard
  corollary is easy once theorem 1 is proved.
* **Include.** It is well-posed, the numerics have been checked, and theorem 1 is plain ACL2, which gives a
  clean statement that is not about limits.

---

## 2. Trapezoid rule, FTC macro, and explicit Stirling bounds

**Source:** conclusion of the Stirling paper.

### 2a. General trapezoid-rule error theorem

#### Task statement

> Work in ACL2(r) 8.7. Let f be a real function on an interval D (an `interval` in the sense of
> `nonstd/nsa/intervals`, with nonempty interior). Assume f is differentiable on D with derivative f₁, and
> f₁ is differentiable on D with derivative f₂, where "g' is the derivative of g on D" means the usual
> nonstandard condition: for standard x in D and every x₁ in D with x₁ ≈ x and x₁ ≠ x,
> (g(x) − g(x₁))/(x − x₁) ≈ g'(x). Assume |f₂(x)| ≤ M on D for a real constant M ≥ 0.
> Introduce f, f₁, f₂, D and M as constrained functions with exactly these constraints. Define the
> Riemann integral ∫_a^b f in the style of `nonstd/integrals`: the standard part of the Riemann sum over
> `make-small-partition`, with right endpoints, extended to all a, b by `defun-std`, and negated when a > b.
>
> For a partition P = (x₀ < x₁ < … < x_n) (a `partitionp` list) whose endpoints lie in D, let
> T(P) = Σ_i (x_{i+1} − x_i)·(f(x_i) + f(x_{i+1}))/2 be the composite trapezoid sum. Prove:
>
> 1. |∫_{x₀}^{x_n} f − T(P)| ≤ (M/12)·Σ_i (x_{i+1} − x_i)³.
> 2. Consequently |∫_{x₀}^{x_n} f − T(P)| ≤ (M/12)·(x_n − x₀)·mesh(P)².
>
> Both hold for every partition, not only for standard ones, and widths need not be equal.

#### Dependencies and base

* Base: **ACL2(r) 8.7 as is.**
* Uses `interval`, `inside-interval-p`, `interval-p`, `interval-left-endpoint` and `interval-right-endpoint`
  (`nonstd/nsa/intervals`); `partitionp`, `deltas`, `dotprod` and `mesh`
  (`nonstd/integrals/integrable-functions`); `make-small-partition` (`nonstd/integrals/make-partition`).
* The encapsulate mirrors the `rcdfn` encapsulate of `nonstd/integrals/ftc-2.lisp`, so the model can
  functionally instantiate the library.

#### Candidate ACL2 statement

The encapsulate admits for real, with local `arithmetic-5` and `nonstd/nsa/nsa`. Only the `defun-std` and the two
theorems were skipped. File: `scratch/t2a-trap.lisp`.

```lisp
(include-book "nonstd/integrals/integrable-functions" :dir :system)
(include-book "nonstd/integrals/make-partition" :dir :system)
(include-book "nonstd/nsa/intervals" :dir :system)
(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "nonstd/nsa/nsa" :dir :system))

(encapsulate
  (((tf *) => *) ((tf1 *) => *) ((tf2 *) => *)
   ((tf-domain) => *) ((tf2-bound) => *))
  (local (defun tf (x) (declare (ignore x)) 0))
  (local (defun tf1 (x) (declare (ignore x)) 0))
  (local (defun tf2 (x) (declare (ignore x)) 0))
  (local (defun tf-domain () (interval 0 1)))
  (local (defun tf2-bound () 0))
  (defthm intervalp-tf-domain (interval-p (tf-domain))
    :rule-classes (:type-prescription :rewrite))
  (defthm tf-domain-real
    (implies (inside-interval-p x (tf-domain)) (realp x))
    :rule-classes (:forward-chaining))
  (defthm tf-domain-non-trivial
    (or (null (interval-left-endpoint (tf-domain)))
        (null (interval-right-endpoint (tf-domain)))
        (< (interval-left-endpoint (tf-domain))
           (interval-right-endpoint (tf-domain))))
    :rule-classes nil)
  (defthm tf-real  (realp (tf x))  :rule-classes (:rewrite :type-prescription))
  (defthm tf1-real (realp (tf1 x)) :rule-classes (:rewrite :type-prescription))
  (defthm tf2-real (realp (tf2 x)) :rule-classes (:rewrite :type-prescription))
  (defthm tf1-is-derivative-of-tf
    (implies (and (standardp x)
                  (inside-interval-p x (tf-domain))
                  (inside-interval-p x1 (tf-domain))
                  (i-close x x1) (not (= x x1)))
             (i-close (/ (- (tf x) (tf x1)) (- x x1)) (tf1 x))))
  (defthm tf2-is-derivative-of-tf1
    (implies (and (standardp x)
                  (inside-interval-p x (tf-domain))
                  (inside-interval-p x1 (tf-domain))
                  (i-close x x1) (not (= x x1)))
             (i-close (/ (- (tf1 x) (tf1 x1)) (- x x1)) (tf2 x))))
  (defthm tf2-bound-type (and (realp (tf2-bound)) (<= 0 (tf2-bound)))
    :rule-classes (:rewrite (:type-prescription :corollary (realp (tf2-bound)))))
  (defthm tf2-bounded
    (implies (inside-interval-p x (tf-domain))
             (<= (abs (tf2 x)) (tf2-bound)))))

(defun map-tf (p) (if (consp p) (cons (tf (car p)) (map-tf (cdr p))) nil))
(defun riemann-tf (p) (dotprod (deltas p) (map-tf (cdr p))))
(defun-std strict-int-tf (a b)                         ; admission needs a proof
  (if (and (realp a) (realp b)
           (inside-interval-p a (tf-domain)) (inside-interval-p b (tf-domain))
           (< a b))
      (standard-part (riemann-tf (make-small-partition a b)))
    0))
(defun int-tf (a b) (if (<= a b) (strict-int-tf a b) (- (strict-int-tf b a))))

(defun trapezoid-tf (p)
  (if (and (consp p) (consp (cdr p)))
      (+ (* (- (cadr p) (car p)) (/ (+ (tf (car p)) (tf (cadr p))) 2))
         (trapezoid-tf (cdr p)))
    0))
(defun sum-cubed-deltas (p)
  (if (and (consp p) (consp (cdr p)))
      (+ (expt (- (cadr p) (car p)) 3) (sum-cubed-deltas (cdr p)))
    0))

(defthm trapezoid-rule-error
  (implies (and (partitionp p)
                (inside-interval-p (car p) (tf-domain))
                (inside-interval-p (car (last p)) (tf-domain)))
           (<= (abs (- (int-tf (car p) (car (last p))) (trapezoid-tf p)))
               (* (/ (tf2-bound) 12) (sum-cubed-deltas p)))))

(defthm trapezoid-rule-error-mesh
  (implies (and (partitionp p)
                (inside-interval-p (car p) (tf-domain))
                (inside-interval-p (car (last p)) (tf-domain)))
           (<= (abs (- (int-tf (car p) (car (last p))) (trapezoid-tf p)))
               (* (/ (tf2-bound) 12) (- (car (last p)) (car p)) (expt (mesh p) 2)))))
```

Decision for us: we could give the encapsulate and the integral definitions verbatim, so that the model only
admits the `defun-std` and proves the two theorems. This changes the condition, but it removes ambiguity about how
"bounded second derivative" is encoded. Recommendation: give them.

#### Leakage

* No `trapez*` anywhere on master or in 8.7.
* The 8.7 library has Rolle's theorem and the MVT (`nonstd/nsa/derivatives.lisp`), but no integration by parts
  (the paper says it formalized integration by parts itself; those books are not public).
* **Not leaked.**

#### Difficulty and recommendation

* **Hard.**
* **Include**, with the encapsulate and the integral definitions given verbatim. The statement is general, well-posed and checkable.

### 2b. FTC boilerplate macro (tool task)

#### Task statement

> Work in ACL2(r) 8.7. Write an event macro `def-ftc-integral` that, given an integrand and a
> user-supplied antiderivative, introduces the definite integral of the integrand and proves its value by the
> Fundamental Theorem of Calculus (`ftc-2` in `nonstd/integrals/ftc-2.lisp`, by functional instantiation).
>
> Required interface:
>
> ```lisp
> (def-ftc-integral name
>   :integrand      f          ; unary function symbol, or (lambda (x) term)
>   :antiderivative F          ; unary function symbol, or (lambda (x) term)
>   :domain         dom        ; a ground term evaluating to an interval, e.g. (interval 1 nil)
>   :derivative-thm thm1       ; optional: name of an existing theorem of the form below
>   :continuity-thm thm2       ; optional: name of an existing theorem of the form below
>   :hints          hints)     ; optional: hints for the obligations the macro must prove
> ```
>
> The derivative theorem has this form:
> `(implies (and (standardp x) (inside-interval-p x dom) (inside-interval-p x1 dom) (i-close x x1) (not (= x x1)))
>  (i-close (/ (- (F x) (F x1)) (- x x1)) (f x)))`.
> The continuity theorem has the analogous continuity form for f.
>
> Generated events, with the same names for every call:
>
> * `name-integrand` (when f is a lambda), `map-name`, `riemann-name`, `strict-int-name` (a `defun-std`), and `int-name`, defined as in `ftc-2.lisp`;
> * `int-name-is-integral`: for standard a ≤ b in dom and a partition p of [a, b] with infinitesimal mesh,
>   `(riemann-name p)` ≈ `(strict-int-name a b)`;
> * `int-name-ftc`: `(implies (and (inside-interval-p a dom) (inside-interval-p b dom)) (equal (int-name a b) (- (F b) (F a))))`.
>
> Two more requirements:
>
> * If `:derivative-thm` or `:continuity-thm` is omitted, the macro must try to prove that obligation itself.
>   On failure it must stop with an error that prints the obligation.
> * The macro must also prove the side conditions `ftc-2` needs (realness of f and F on the domain, that the
>   domain is an interval, non-triviality).
>
> The deliverable includes a test book that certifies and contains at least these calls:
>
> 1. f(x) = x², F(x) = x³/3, dom = (interval nil nil), with no theorems supplied;
> 2. f = `acl2-cosine`, F = `acl2-sine`, dom = (interval nil nil);
> 3. f(x) = 1/x², F(x) = −1/x, dom = (interval 1 nil);
> 4. f = `acl2-ln`, F(x) = x·ln x − x, dom = (interval 1 nil);
> 5. one call that must fail cleanly, with a wrong antiderivative (wrapped in `must-fail`).
>
> Each call must be followed by a check that `int-name-ftc` instantiates to the expected closed form at concrete endpoints.

#### Dependencies and base

* Base: **ACL2(r) 8.7 as is.**
* Relevant 8.7 books:
  * `nonstd/integrals/ftc-2.lisp`, `ftc-1.lisp` and `continuous-function.lisp`;
  * the differentiator `nonstd/workshops/2011/reid-gamboa-differentiator/support/differentiator.lisp`
    (`defderivative`, `def-elem-derivative` for `acl2-exp`, `acl2-ln`, `acl2-sine`, `acl2-cosine`, `acl2-sqrt`, ...);
  * `acl2-sine-derivative` and `acl2-cosine-derivative` in `nonstd/circles/circumference-of-a-circle.lisp`.
* All are certified in `/opt/acl2r/books`.

#### Candidate ACL2 statement

Not applicable; this is a tool task. Grading is by certifying the test book, plus inspection that `int-name`
really is the library-style Riemann integral (no `defaxiom`, no `skip-proofs`).

Optional stretch, which covers items 3 and 4: an `:params (c1 ... ck)` option for parameterized integrands
such as cos(x − c). Here the extra arguments must be handled by `defun-std` with standard parameters, and the
generated theorem must hold for all parameter values.

#### Leakage

* No integration macro in 8.7 or on master (`grep defmacro` over `nonstd/integrals` finds none; no `def-ftc`, `defintegral` or `antiderivative`).
* **Not leaked.**

#### Difficulty and recommendation

* **Hard** (macro engineering: functional-instantiation hints, `defun-std` limitedness obligations, robust hint generation).
* **Include with changes**:
  * fix the interface exactly as above;
  * make automatic discharge of the derivative obligation "best effort", so that tests 1–3 must work without supplied
    theorems and test 4 may supply them;
  * keep the tool task separate from the math tasks.

### 2c. Explicit error bounds for Stirling's approximation

**Well-posed?**

* As stated in the paper ("explore the size of the error term") it is not a theorem.
* It becomes well-posed in either of two forms:
  * (i) the classical, limit-free monotonicity facts about r(n) = n!/(√n·nⁿ·e⁻ⁿ);
  * (ii) the Robbins-type explicit bound √(2πn)(n/e)ⁿ < n! < √(2πn)(n/e)ⁿ·e^{1/(12n)}.
* (ii) needs the value of the limit √(2π), which is the main Stirling theorem (a separate, very hard task).
  It is therefore stated with that theorem as a given.

#### Task statement

> Work in ACL2(r) 8.7. For a positive integer n let r(n) = n! / (√n · nⁿ · e^(−n)). Use `factorial` from
> `arithmetic/factorial`, `acl2-sqrt`, and `acl2-exp`. Prove, for every positive integer n:
>
> 1. r(n+1) < r(n);
> 2. r(n) < r(n+1) · exp(1/(12n) − 1/(12(n+1))).
>
> Part B, optional. Assume as given: for every infinitely large natural n,
> n! / (√(2π)·nⁿ·e^(−n)·√n) ≈ 1. Prove that for every positive integer n,
> √(2πn)·nⁿ·e^(−n) < n! < √(2πn)·nⁿ·e^(−n)·exp(1/(12n)).

#### Dependencies and base

* Base: **ACL2(r) 8.7 as is** (`arithmetic/factorial`, `nonstd/nsa/exp`, `nonstd/nsa/sqrt`, `nonstd/nsa/trig`, `nonstd/nsa/ln`).
* The Part B given is the Stirling paper's main theorem, `stirling-approximation-to-factorial`. It would be supplied as an axiom.

#### Candidate ACL2 statement

Admits under `skip-proofs` (`scratch/t2c-stirling-bounds.lisp`). The numerics agree for n < 300 to within float
rounding, and the inequality in (2) is the classical Robbins bound
d_n − d_{n+1} = Σ_k 1/((2k+1)(2n+1)^{2k}) < 1/(12n(n+1)).

```lisp
(include-book "arithmetic/factorial" :dir :system)
(include-book "nonstd/nsa/exp" :dir :system)
(include-book "nonstd/nsa/sqrt" :dir :system)
(include-book "nonstd/nsa/trig" :dir :system)

(defun stirling-ratio (n)
  (/ (factorial n) (* (acl2-sqrt n) (expt n n) (/ (acl2-exp n)))))

(defthm stirling-ratio-decreasing
  (implies (posp n) (< (stirling-ratio (1+ n)) (stirling-ratio n))))

(defthm stirling-ratio-decrease-bounded
  (implies (posp n)
           (< (stirling-ratio n)
              (* (stirling-ratio (1+ n))
                 (acl2-exp (- (/ (* 12 n)) (/ (* 12 (1+ n)))))))))

;; Part B (GIVEN: stirling-approximation-to-factorial, as in the main experiment)
(defthm stirling-explicit-bounds
  (implies (posp n)
           (let ((s (* (acl2-sqrt (* 2 (acl2-pi) n)) (expt n n) (/ (acl2-exp n)))))
             (and (< s (factorial n))
                  (< (factorial n) (* s (acl2-exp (/ (* 12 n)))))))))
```

#### Leakage

* No hits for stirling or robbins on master; the 100-theorems entry 90 (Stirling) is still commented out.
* **Not leaked.**

#### Difficulty and recommendation

* **Hard.** Part 2 needs sharp inequalities for `acl2-ln(1 + 1/n)`, which are absent from the library. Part B adds a short nonstandard argument.
* **Include** parts 1–2. Part B is optional; it is only meaningful with the Stirling theorem given.

---

## 3. Air-gap inductance integral (AC machine paper)

**Source:** Sections 5, 5.1 and 9 of the AC-machine paper. The authors' `08-inductance-integral.lisp` stops before the derivative step and the `ftc-2` instantiation.

### Task statement

> Work in ACL2(r) 8.7. Let γ = 2π/3. For integers m, n let
> g_{m,n}(x) = cos(x − mγ)·cos(x − nγ), using `acl2-cosine` and `acl2-pi`.
> Define the Riemann integral of g_{m,n} over [a, b], with m, n as parameters, in the style of `nonstd/integrals`
> (the standard part of the right-endpoint Riemann sum over `make-small-partition`, introduced with `defun-std`).
> Prove that for all integers m and n
>
>  ∫₀^{2π} cos(x − mγ) cos(x − nγ) dx = π·cos((m − n)γ).
>
> Also prove the limit form: for all integers m, n (standard or not) and every partition P of [0, 2π] with
> infinitesimal mesh, the right-endpoint Riemann sum of g_{m,n} over P is infinitely close to π·cos((m − n)γ).

### Dependencies and base

* Base: **ACL2(r) 8.7 as is.**
* Statement names:
  * `acl2-cosine` and `acl2-pi` (`nonstd/nsa/trig`);
  * `partitionp`, `deltas`, `dotprod` and `mesh` (`nonstd/integrals/integrable-functions`);
  * `make-small-partition`.
* Authors' definitions that we could give (all are also derivable from the English):
  `winding-gamma` and `inductance-integrand` from
  `reference-books/workshop-2026/cayuela-ac-machine/08-inductance-integral.lisp`. Giving `inductance-antideriv`
  or the book's lemmas would be a proof hint, so do not give them.
* Prior art in 8.7, not to be mentioned:
  * `workshops/2015/chau-kaufmann-hunt/support/cosines-orthog.lisp` (∫ cos(mx)cos(nx) over [−π, π] with standard parameters);
  * `acl2-sine-derivative` in `nonstd/circles/circumference-of-a-circle.lisp`;
  * the differentiator.

  These make the task noticeably easier than the paper suggests.

### Candidate ACL2 statement

Admits under `skip-proofs` (`scratch/t3-inductance.lisp`). The value was checked numerically for (m, n) = (0,1), (1,1), (2,0) and (5,−3).

```lisp
(include-book "nonstd/nsa/trig" :dir :system)
(include-book "nonstd/integrals/integrable-functions" :dir :system)
(include-book "nonstd/integrals/make-partition" :dir :system)

(defun winding-gamma () (* 2/3 (acl2-pi)))
(defun inductance-integrand (x m n)
  (* (acl2-cosine (- x (* m (winding-gamma))))
     (acl2-cosine (- x (* n (winding-gamma))))))
(defun map-inductance-integrand (p m n)
  (if (consp p)
      (cons (inductance-integrand (car p) m n) (map-inductance-integrand (cdr p) m n))
    nil))
(defun riemann-inductance-integrand (p m n)
  (dotprod (deltas p) (map-inductance-integrand (cdr p) m n)))

(defthm inductance-integral-riemann-form
  (implies (and (integerp m) (integerp n)
                (partitionp p)
                (equal (car p) 0)
                (equal (car (last p)) (* 2 (acl2-pi)))
                (i-small (mesh p)))
           (i-close (riemann-inductance-integrand p m n)
                    (* (acl2-pi) (acl2-cosine (* (- m n) (winding-gamma)))))))

(defun-std int-inductance-integrand (a b m n)          ; admission needs a proof
  (if (and (realp a) (realp b) (< a b) (realp m) (realp n))
      (standard-part (riemann-inductance-integrand (make-small-partition a b) m n))
    0))

(defthm inductance-integral-value
  (implies (and (integerp m) (integerp n))
           (equal (int-inductance-integrand 0 (* 2 (acl2-pi)) m n)
                  (* (acl2-pi) (acl2-cosine (* (- m n) (winding-gamma)))))))
```

### Leakage

* Master `books/workshops/2026/cayuela-ac-machine/` is byte-identical to our reference copy. It has no `ftc-2`
  instantiation and no derivative of sin(2x − c) in trig form.
* The paper itself says that after acceptance an AI agent proved the derivative step outside the books. That
  proof could now be in the author's public GitHub repository (`pcayuela/ACL2-ACmotormodel-check`), which we
  could **not** check offline. Treat it as possibly leaked on GitHub. Runs must stay off the network, and the
  transcript audit should look for it.

### Difficulty and recommendation

* **Medium.** It needs the derivative of the antiderivative through the chain rule, `ftc-2` instantiation
  with parameters, and `defun-std` admission. The 8.7 prior art covers most of the pattern.
* **Include.** It fills the paper's open gap, is cleanly checkable, and is a good medium-tier item.
  Either form is acceptable; require both.

---

## 4. Rectifier equations

**Source:** Sections 6 and 8 of the rectifier paper.

Shared definition (the authors' own, from `reference-books/workshop-2026/cayuela-rectifiers/00-sampling-function.lisp`; give it verbatim):

```lisp
(defun sa (x) (if (equal x 0) 1 (/ (acl2-sine x) x)))
```

### 4a. Exact-value layer for the six-phase and twelve-pulse rows

The paper's rows are not well-posed as printed:

* The paper says these rows need "an additional circuit-topology argument" for the peak V_m.
* The printed twelve-pulse V_DC entry, (6/π)·sin(π/12)·√3·V_max·cos α ≈ 0.856·V_max at α = 0, does not fit
  the master equation with any natural choice of V_m:
  * series connection: V_m = 2√3·cos(π/12)·V_max, giving (6√3/π)·V_max ≈ 3.308·V_max (confirmed by direct numerical integration of the waveform);
  * parallel connection: (3√3/π)·V_max ≈ 1.654·V_max.
* The printed entry is exactly half of √3·V_max·Sa(π/12), so it is probably another table erratum.
* The six-phase entry (3√3/π)·V_max holds only if V_max is reinterpreted as the source peak of the "equivalent
  three-phase bridge". With V_max taken as the six-phase phase peak it is (3/π)·V_max.

The task therefore fixes the conventions explicitly and adds the missing waveform argument as part 2. We do **not** tell the model about the suspected erratum.

#### Task statement

> Work in ACL2(r) 8.7. Let Sa be as defined above. For a peak V_m, a pulse width T > 0 and a firing angle α, the
> closed-form average and normalized RMS output are
> V_DC(V_m, T, α) = V_m·Sa(T/2)·cos α and R(T, α) = √(1 + Sa(T)·cos 2α).
>
> Part 1 (exact values). Prove, for all real V_max and α:
>
> * (Six-phase midpoint: T = π/3, V_m = V_max.) V_DC = (3/π)·V_max·cos α and
>   R = √(1 + (3√3/(2π))·cos 2α).
> * sin(π/12) = (√6 − √2)/4 and 2√3·cos(π/12) = (3√2 + √6)/2.
> * (Twelve-pulse, two series-connected six-pulse bridges 30° apart: T = π/6,
>   V_m = 2√3·cos(π/12)·V_max.) V_DC = (6√3/π)·V_max·cos α and R = √(1 + (3/π)·cos 2α).
>
> Part 2 (waveforms). Let E(θ, V) = max_{k=0..5} V·cos(θ − kπ/3).
>
> * The six-phase midpoint output with phase peak V_max is E(θ, V_max).
> * The three-phase bridge output with phase peak V_max is E(θ, √3·V_max).
> * The series twelve-pulse output is W(θ) = E(θ, √3·V_max) + E(θ − π/6, √3·V_max).
>
> Prove, for V_max ≥ 0:
>
> * E(θ, V_max) = V_max·cos θ for −π/6 ≤ θ ≤ π/6;
> * W(θ) = 2√3·cos(π/12)·V_max·cos(θ − π/12) for 0 ≤ θ ≤ π/6.

#### Dependencies and base

* Base: **ACL2(r) 8.7 as is** (`nonstd/nsa/trig`, `nonstd/nsa/sqrt`).
* Authors' `sa` is given. Their exact-value lemmas (`sine-2pi/3`, `sa-pi/3`, ...) need not be given; they are easy.

#### Candidate ACL2 statement

Admits under `skip-proofs` (`scratch/t4-rectifiers.lisp`). All closed forms and both waveform identities were checked numerically.

```lisp
(defun vdc-closed (vm tt alpha) (* vm (sa (/ tt 2)) (acl2-cosine alpha)))
(defun vrms-ratio-closed (tt alpha)
  (acl2-sqrt (+ 1 (* (sa tt) (acl2-cosine (* 2 alpha))))))

(defthm six-phase-midpoint-row
  (implies (and (realp vmax) (realp alpha))
           (and (equal (vdc-closed vmax (* 2/6 (acl2-pi)) alpha)
                       (* (/ 3 (acl2-pi)) vmax (acl2-cosine alpha)))
                (equal (vrms-ratio-closed (* 2/6 (acl2-pi)) alpha)
                       (acl2-sqrt (+ 1 (* (/ (* 3 (acl2-sqrt 3)) (* 2 (acl2-pi)))
                                          (acl2-cosine (* 2 alpha)))))))))
(defthm sine-pi/12
  (equal (acl2-sine (* 1/12 (acl2-pi))) (/ (- (acl2-sqrt 6) (acl2-sqrt 2)) 4)))
(defthm twelve-pulse-peak
  (equal (* 2 (acl2-sqrt 3) (acl2-cosine (* 1/12 (acl2-pi))))
         (/ (+ (* 3 (acl2-sqrt 2)) (acl2-sqrt 6)) 2)))
(defthm twelve-pulse-row
  (implies (and (realp vmax) (realp alpha))
           (and (equal (vdc-closed (* 2 (acl2-sqrt 3) (acl2-cosine (* 1/12 (acl2-pi))) vmax)
                                   (* 1/6 (acl2-pi)) alpha)
                       (* (/ (* 6 (acl2-sqrt 3)) (acl2-pi)) vmax (acl2-cosine alpha)))
                (equal (vrms-ratio-closed (* 1/6 (acl2-pi)) alpha)
                       (acl2-sqrt (+ 1 (* (/ 3 (acl2-pi)) (acl2-cosine (* 2 alpha)))))))))

(defun envelope6 (theta vpk k)
  (declare (xargs :measure (nfix (- 6 k))))
  (if (or (not (natp k)) (>= k 5))
      (* vpk (acl2-cosine (- theta (* 5/3 (acl2-pi)))))
    (max (* vpk (acl2-cosine (- theta (* k 1/3 (acl2-pi)))))
         (envelope6 theta vpk (1+ k)))))
(defun six-phase-midpoint-output (theta vmax) (envelope6 theta vmax 0))
(defun three-phase-bridge-output (theta vmax) (envelope6 theta (* (acl2-sqrt 3) vmax) 0))
(defun twelve-pulse-series-output (theta vmax)
  (+ (three-phase-bridge-output theta vmax)
     (three-phase-bridge-output (- theta (* 1/6 (acl2-pi))) vmax)))

(defthm six-phase-midpoint-output-pulse
  (implies (and (realp vmax) (<= 0 vmax) (realp theta)
                (<= (- (* 1/6 (acl2-pi))) theta) (<= theta (* 1/6 (acl2-pi))))
           (equal (six-phase-midpoint-output theta vmax) (* vmax (acl2-cosine theta)))))
(defthm twelve-pulse-series-output-pulse
  (implies (and (realp vmax) (<= 0 vmax) (realp theta)
                (<= 0 theta) (<= theta (* 1/6 (acl2-pi))))
           (equal (twelve-pulse-series-output theta vmax)
                  (* 2 (acl2-sqrt 3) (acl2-cosine (* 1/12 (acl2-pi))) vmax
                     (acl2-cosine (- theta (* 1/12 (acl2-pi))))))))
```

#### Leakage

* Master `books/workshops/2026/cayuela-rectifiers/` is identical to our reference copy. It has no six-phase,
  twelve-pulse or π/12 material, and `nonstd/nsa/trig` has no π/12 values.
* The author's GitHub repository could not be checked.
* **Not leaked** locally.

#### Difficulty and recommendation

* **Easy** (part 1) to **medium** (part 2: maxima of cosines).
* **Include with changes.** Use it only as a calibration or easy-tier item with the conventions above. Part 1 alone is too
  close to the paper's existing 13 theorems to be interesting.

### 4b. Integral-based master theorem

#### Task statement

> Work in ACL2(r) 8.7. Define the Riemann integrals ∫_a^b cos θ dθ and ∫_a^b cos² θ dθ (`acl2-cosine`) in the
> style of `nonstd/integrals`: the standard part of the right-endpoint Riemann sum over `make-small-partition`, via
> `defun-std`, negated when a > b. For a peak V_m ≥ 0, a pulse width T > 0 and a real firing angle α, let the
> output over the conduction window [α − T/2, α + T/2] have
>
>  V_DC(V_m, T, α) = (V_m/T)·∫_{α−T/2}^{α+T/2} cos θ dθ, V_RMS(V_m, T, α) = √((V_m²/T)·∫_{α−T/2}^{α+T/2} cos² θ dθ).
>
> Prove, for all real V_m ≥ 0, T > 0 and α (standard or not):
>
>  V_DC = V_m·Sa(T/2)·cos α and V_RMS = (V_m/√2)·√(1 + Sa(T)·cos 2α).
>
> Then derive, as instances, the controlled three-phase midpoint (T = 2π/3) and three-phase bridge (T = π/3,
> V_m = √3·V_max) formulas: V_DC = (3√3/(2π))·V_max·cos α and (3√3/π)·V_max·cos α respectively, with
> V_RMS/(V_m/√2) = √(1 + (3√3/(4π))·cos 2α) and √(1 + (3√3/(2π))·cos 2α) respectively.

#### Dependencies and base

* Base: **ACL2(r) 8.7 as is.**
* Statement names: `acl2-sine`, `acl2-cosine`, `acl2-pi` and `acl2-sqrt`; `deltas`, `dotprod` and `make-small-partition`; authors' `sa` (given).
* The semi-controlled regime (piecewise waveform) is deliberately excluded. It could be a stretch item.

#### Candidate ACL2 statement

Admits under `skip-proofs` (`scratch/t4-rectifiers.lisp`).

```lisp
(defun map-cos (p) (if (consp p) (cons (acl2-cosine (car p)) (map-cos (cdr p))) nil))
(defun riemann-cos (p) (dotprod (deltas p) (map-cos (cdr p))))
(defun map-cos-sq (p)
  (if (consp p) (cons (expt (acl2-cosine (car p)) 2) (map-cos-sq (cdr p))) nil))
(defun riemann-cos-sq (p) (dotprod (deltas p) (map-cos-sq (cdr p))))
(defun-std strict-int-cos (a b)
  (if (and (realp a) (realp b) (< a b))
      (standard-part (riemann-cos (make-small-partition a b)))
    0))
(defun int-cos (a b) (if (<= a b) (strict-int-cos a b) (- (strict-int-cos b a))))
(defun-std strict-int-cos-sq (a b)
  (if (and (realp a) (realp b) (< a b))
      (standard-part (riemann-cos-sq (make-small-partition a b)))
    0))
(defun int-cos-sq (a b) (if (<= a b) (strict-int-cos-sq a b) (- (strict-int-cos-sq b a))))

(defun vdc-integral (vm tt alpha)
  (* vm (/ tt) (int-cos (- alpha (/ tt 2)) (+ alpha (/ tt 2)))))
(defun vrms-integral (vm tt alpha)
  (acl2-sqrt (* (expt vm 2) (/ tt) (int-cos-sq (- alpha (/ tt 2)) (+ alpha (/ tt 2))))))

(defthm master-theorem-vdc
  (implies (and (realp vm) (realp tt) (< 0 tt) (realp alpha))
           (equal (vdc-integral vm tt alpha) (* vm (sa (/ tt 2)) (acl2-cosine alpha)))))
(defthm master-theorem-vrms
  (implies (and (realp vm) (<= 0 vm) (realp tt) (< 0 tt) (realp alpha))
           (equal (vrms-integral vm tt alpha)
                  (* (/ vm (acl2-sqrt 2))
                     (acl2-sqrt (+ 1 (* (sa tt) (acl2-cosine (* 2 alpha)))))))))
```

The paper raises the standardness of α as an obstacle. In this formulation the integrand has no parameters
and α enters only through the endpoints, so the obstacle does not arise (`defun-std` with transfer).

#### Leakage

* Same as 4a: nothing on master; GitHub not checked.
* Prior art in 8.7, not mentioned: `acl2-sine-derivative` and `acl2-cosine-derivative`
  (`nonstd/circles/circumference-of-a-circle.lisp`), `ftc-2`, and the Fourier-series books in `workshops/2015/chau-kaufmann-hunt`.

#### Difficulty and recommendation

* **Medium.**
* **Include.** It is the paper's real open item, it is well-posed for all α, and it pairs naturally with item 3.
  Avoid running 3 and 4b in the same session.

---

## 5. Executable predicates for the inductive-definition tool (tool extension)

**Source:** Section 8 of the inductive-definitions paper: "optionally generate executable definitions of the predicates ... also proving their equivalence".

### Task statement

> You are given the event macro `definductive` (files `std/util/definductive.lisp`, `definductive-doc.lisp`
> and `definductive-tests.lisp`). It defines predicates p₁, …, p_k from inference rules as `defun-sk`
> existentials over proof trees, and generates rule theorems and induction principles. Extend it with an
> optional facility that also generates an executable definition of each predicate and proves it equivalent to
> the original predicate.
>
> Required interface (new optional inputs, default `nil`; existing behavior must be unchanged when they are absent):
>
> ```lisp
> :exec ((p1 :name p1-exec :measure m1)       ; one entry per predicate in :preds, or :exec absent
>        (p2 :name p2-exec :measure m2) ...)  ; mi: term over pi's formals (o-p valued)
> :exec-binds ((rule-name (v term) ...) ...)  ; per rule: how to compute each rule variable that is
>                                             ; not literally a conclusion argument, as a term over the
>                                             ; formals of the conclusion's predicate
> :exec-hints ...                             ; optional hints for the generated obligations
> ```
>
> Semantics. For a rule r with conclusion (p t₁ … t_n) and the formals x₁ … x_n of p, each rule variable v gets
> a value: from `:exec-binds`, or x_i when t_i is literally v. A rule variable with no value is an error.
> Under those values, `p-exec` holds iff for some rule with conclusion predicate p:
>
> * each x_i equals the instantiated t_i, and
> * the instantiated premises hold, in order, where a premise on a defined predicate q is evaluated by `q-exec`.
>
> The `p-exec` functions of a clique are mutually recursive and use the given measures.
>
> The tool must state and prove, automatically, with an error showing the failed obligation otherwise:
>
> * (a) termination, for each recursive premise under the preceding tests;
> * (b) binding adequacy: if the x_i equal the t_i under some values of the rule variables and the non-predicate
>   premises hold, then the bound terms evaluate to those values.
>
> It must then generate and prove:
>
> * `p-exec-correct`: `(iff (p-exec x1 ... xn) (p x1 ... xn))`, for every p;
> * `booleanp-of-p-exec`.
>
> The `p-exec` functions must not call the `defun-sk` predicates, their witnesses or any `defchoose`, so they
> must be executable on concrete data.
>
> Acceptance:
>
> 1. `definductive-tests.lisp` still certifies unchanged.
> 2. A new test book certifies with:
>    * (i) even/odd on naturals (rules with conclusions (even 0), (odd (1+ n)) and (even (1+ n)), with premise (natp n) added before the recursive premise);
>    * (ii) naturals plus finitely branching trees of naturals (conclusions using `cons`);
>    * (iii) a typing judgement for a small expression language of your choice with at least three predicates in one clique;
>    * (iv) `must-fail` on reflexive-transitive closure with the transitivity rule and no binding for its middle variable;
>    * (v) `assert-event` evaluations of each `p-exec` on concrete inputs.

### Dependencies and base

* `definductive` is **not in 8.7.** It exists only on master: `books/std/util/definductive{,-doc,-tests}.lisp`,
  6,940 lines, last change 2026-11-03. It needs more than an overlay of book files. On master its include
  closure (`std/util/definductive` + tests) has 511 books, 63 of which are new or changed relative to 8.7,
  including `centaur/fty/*`, `ihs/*` and `std/omaps/core`.
* I tried certifying master `definductive` on the 8.7 image with the 7 new and 6 changed direct dependencies copied locally (`scratch/di/`).
  It fails in `std/system/check-user-term-dollar.lisp` because `in-logic-mode` is undefined, which is a
  master *system* (not books) feature. Side effect: cert.pl also certified a few unchanged 8.7 books in
  `/opt/acl2/books` on demand (`kestrel/event-macros/event-generation`, `kestrel/fty/defset`, `kestrel/fty/set`).
* **Required base: an ACL2 master build (image + books) at a pinned commit, e.g. `1d2b39a` (2026-11-12).** This is
  not 8.7. Given files: the three definductive files plus the examples in `reference-books/workshop-2026/coglio-jurgensen/`.
  Keep `kestrel/remora` in the tree; it uses definductive and contains manual executable-checker equivalence
  proofs, which is legitimate prior art.

### Candidate ACL2 statement

Not applicable (tool task). Grading:

* certify the acceptance test book, plus a hidden test book of ours with 2–3 further definitions;
* inspect that `p-exec-correct` has exactly the stated form and that no `skip-proofs`, `defaxiom` or ttag is used.

### Leakage

* No `:exec` or executable-predicate option on master. The only `execut*` mention in the definductive log is
  unrelated ("validity predicates for the second representation").
* Other Section-8 items **are** already on master: guard verification (`:verify-guards` and `:guard-hints` inputs, Oct 2026) and induction-function generation.
* So this item is **not leaked**, but its neighbors are.

### Difficulty and recommendation

* **Hard** (an extension of a large generator with fully automatic proof generation; the soundness and completeness proofs are by proof-tree induction).
* **Include with changes** only if we are willing to build and pin an ACL2 master image. Otherwise **drop**, because
  it cannot run on 8.7. If included, it is the only item outside 8.7, so report it separately.

---

## 6. Finite multisets as maps to positive integers (library task)

**Source:** Section 9 of the treesets paper: "model finite multi-sets as treemaps to positive numbers".

### Task statement

Variant A (recommended), on 8.7 `std/omaps`:

> Work in ACL2 8.7. Using the ordered-map library `std/omaps` (`omap::mapp`, `omap::update`, `omap::lookup`,
> `omap::assoc`, `omap::delete`, `omap::keys`, ...), implement a library of finite multisets (bags) in a new
> package `MSET`. A bag is an `omap::mapp` whose values are all positive integers (the multiplicities). The empty map is the empty bag.
>
> Required functions, all guard-verified, with fixing behavior on non-bags as you choose but documented:
>
> * `bagp`, `bfix` and `bequiv`, with `bequiv` an equivalence and every function below respecting it;
> * `empty` and `emptyp`;
> * `count a b` (natural; 0 when absent) and `in a b`;
> * `insert a b` (count + 1), `insert-n a n b` (count + n, n natural), `delete a b` (count − 1, dropping the key at 0) and `delete-all a b`;
> * `cardinality b` (sum of counts) and `support b` (an `omap`-key set, i.e. an oset);
> * `subbag x y`;
> * `sum x y` (counts add), `union x y` (max), `intersect x y` (min) and `diff x y` (truncated subtraction);
> * `from-list l` and `to-list b` (each element repeated by its count, in key order).
>
> Required theorems, all as rewrite rules unless impossible:
>
> * closure (`bagp` of every constructor);
> * `count-of-X` for every X in {empty, insert, insert-n, delete, delete-all, sum, union, intersect, diff,
>   from-list}, giving the count in terms of the counts of the arguments (`from-list`: `duplicity` from `std/lists/duplicity`);
> * `in` ⇔ count > 0;
> * extensionality: for bags x and y, `(equal x y)` iff counts agree on a witness element (stated with a `defun-sk` or witness function);
> * `subbag` ⇔ pointwise ≤ of counts, plus reflexivity, antisymmetry (with bagp) and transitivity;
> * `cardinality` of empty, insert, delete (when in) and sum;
> * `to-list`/`from-list` round trip: `(equal (from-list (to-list b)) (bfix b))`, and `(len (to-list b)) = (cardinality b)`;
> * commutativity and associativity of `sum`, `union` and `intersect`.
>
> Non-functional requirement: `count`, `insert` and `delete` must be implemented directly by map operations,
> with no conversion to lists.

Variant B (faithful to the paper): the same interface on the treemap library (`treemap::mapp`, `treemap::lookup` with `:default`, `treemap::update`, `treemap::delete`, `treemap::keys` returning a treeset). `support` returns a treeset.

### Dependencies and base

* Variant A: **ACL2 8.7 as is.** `std/omaps/core` (with `mapp`, `update`, `delete`, `lookup`, `keys`, `size`, `submap`,
  `from-lists`), `std/omaps/extensionality` and `std/lists/duplicity` are all in 8.7.
* Variant B: `treemap` is **not in 8.7.** `/opt/acl2/books/kestrel/data/` has only `treeset`, `hash` and `utilities`;
  the initial treemap commit (2026-02-28) is not in the 8.7 tag. Master treemap needs master `treeset`, `hash`,
  `utilities`, `std/omaps/{defs,inverse}`, `std/osets/defs` and `misc/total-order-defs`. Its include closure has 674 books, 240
  of them new or changed versus 8.7. So Variant B needs a **pinned ACL2 master build with
  `books/kestrel/data/treebag/` (and arguably `graph/`, `deque/`) deleted**, and the `treebag` references removed from
  `kestrel/data/{top,doc}.lisp`.
* Prior art in 8.7, not mentioned: `std/obags` (list-based ordered bags), `coi/bags` and `kestrel/fty/bag`.

### Candidate ACL2 statement

Not applicable as a single statement (library task). The theorem list above is the grading spec, and we would
write a hidden check book that states each required theorem in our exact form and proves it `:by` the model's
lemma or with trivial hints. The real `count-of-insert` would be:

```lisp
(defthm count-of-insert
  (equal (mset::count a (mset::insert x b))
         (if (equal a x) (+ 1 (mset::count a b)) (mset::count a b))))
```

(Not admitted; it depends on the model's definitions.)

### Leakage

**Leaked on master (Variant B).** `books/kestrel/data/treebag/` was added between 2026-08-10 and 2026-11-09 by the treeset author:

* `bagp`, `count`, `insert`, `delete`, `cardinality`, `subbag`, `sum`, `union`, `intersect`, `diff`, extensionality and fty integration;
* internal `map-values-all-posp`;
* "A tree-based implementation of finite multisets".

That is exactly this future-work item. The graph future-work item is also on master (`books/kestrel/data/graph/`, Nov 2026).

* Variant A is a different substrate. 8.7 has no omap-based bag library, so it is not directly leaked, but the
  master treebag is a near-complete reference solution in spirit. This is useful for grading, and a risk only if the model can reach master or GitHub.

### Difficulty and recommendation

* **Medium** (many routine lemmas; extensionality and the round trip are the only nontrivial parts).
* **Include with changes:** Variant A on 8.7. Variant B is not worth a master build, given that it is already leaked on master.

---

## Summary

| # | Item | Base | ACL2 statement now? | Sanity check | Leakage (master / other) | Difficulty | Recommendation |
|---|---|---|---|---|---|---|---|
| 1 | Euler product ζ(2) (finite two-sided bound + i-close form; π²/6 form with Basel given) | ACL2(r) 8.7 as is (bound also plain ACL2 8.7) | Yes | admits (skip-proofs) in both images; numerics OK n<80 | none | hard | **Include** |
| 2a | Trapezoid error ≤ (M/12)Σh³, arbitrary partitions | ACL2(r) 8.7 as is | Yes (give encapsulate + integral defs) | encapsulate admits for real; rest skip-proofs OK | none | hard | **Include** (give constrained setup verbatim) |
| 2b | FTC boilerplate macro `def-ftc-integral` | ACL2(r) 8.7 as is | n/a (tool; interface + 5 acceptance tests fixed) | — | none | hard | **Include with changes** (fixed interface; auto-derivative best effort) |
| 2c | Explicit Stirling bounds: r(n) decreasing, Robbins step bound; optional √(2πn)(n/e)ⁿ<n!<…e^{1/12n} | ACL2(r) 8.7 as is (+ Stirling theorem as given for the optional part) | Yes | admits (skip-proofs); numerics OK | none | hard | **Include** parts 1–2; optional part only with given Stirling |
| 3 | AC machine air-gap integral ∫₀^{2π}cos(x−mγ)cos(x−nγ)=π cos((m−n)γ) | ACL2(r) 8.7 as is | Yes (Riemann form + defun-std form) | admits (skip-proofs); numerics OK | none on master (books identical); author GitHub unchecked, paper says derivative step done post-acceptance | medium | **Include** |
| 4a | Rectifiers: six-phase & twelve-pulse rows (+ waveform envelopes) | ACL2(r) 8.7 as is | Yes, after fixing V_m conventions | admits (skip-proofs); numerics OK | none on master; GitHub unchecked. Printed 12-pulse row looks erroneous | easy / medium | **Include with changes** (explicit conventions; calibration tier) |
| 4b | Rectifiers: integral master theorem V_DC, V_RMS for all α | ACL2(r) 8.7 as is | Yes | admits (skip-proofs) | none on master; GitHub unchecked | medium | **Include** (not in same session as 3) |
| 5 | definductive: executable predicates + equivalence proofs | **ACL2 master image+books pinned (e.g. 1d2b39a)**; cannot run on 8.7 (needs master system feature) | n/a (tool; interface + acceptance fixed) | master definductive fails on 8.7 image | this option not on master; guard-verification and induction-function items already are | hard | **Include with changes** only if we build a master image; else **drop** |
| 6 | Multisets as maps to positive integers | Variant A: ACL2 8.7 as is (`std/omaps`); Variant B: master minus `treebag/` | n/a (library; interface + theorem list fixed) | — | **Leaked on master**: `kestrel/data/treebag` (Aug–Nov 2026) is this item; `graph/` too | medium | **Include with changes** (Variant A on 8.7) |

Scratch files: `/home/user/acl2-exp/ext/scratch/` (`t1-euler.lisp`, `t1-plain.lisp`, `t2a-trap.lisp`,
`t2c-stirling-bounds.lisp`, `t3-inductance.lisp`, `t4-rectifiers.lisp`, the `di/` definductive overlay attempt, and `tools/closure.py`).
