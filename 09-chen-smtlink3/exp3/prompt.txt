Build, in ACL2, the system described in the paper below. The authors' implementation is not available;
write your own, following the paper. Where the paper gives names, interfaces, generated events or example
inputs, use them exactly. The requirements after the paper say what will be checked.

<paper>
Smtlink 3: Rewrite-driven Compilation to SMT- LIB

                  Christopher K. Chen           Mark R. Greenstreet         Margo I. Seltzer
                                       Department of Computer Science
                                      The University of British Columbia
                                             Vancouver, Canada
                         cchen@nougat.org    mrg@cs.ubc.ca        mseltzer@cs.ubc.ca



      There is a long history of integration between the ACL 2 theorem prover and satisfiability modulo
      theories (SMT) solvers. While both systems operate over first-order logic, translating between their
      languages requires careful consideration of their differing semantics and typing disciplines. Many
      projects have taken an ad hoc approach to translation, validating the results through proof reconstruc-
      tion. Another approach is to write a compiler and verify it, but this poses a substantial proof burden.
      In this paper, we present Smtlink 3, which uses the ACL 2 rewriter to infer types and translate proof
      terms by applying known theorems. We show a substantial reduction in complexity and trusted code
      compared to previous versions of Smtlink.


1    Introduction
ACL 2 has a rich tradition of integration with external decision procedures; these include symbolic evalu-
ation efforts, reasoning support for sub-theories, and general-purpose integrations with external solvers.
     Smtlink is an ACL 2 book for discharging proof goals with SMT solvers, using the solver’s decision
procedures for theories that are challenging for ACL 2, such as nonlinear real arithmetic. Smtlink 2.0 [17]
is structured as a multi-pass compiler, with verified clause processors on the frontend and a trusted clause
processor targetting the Z 3 Python API.
     The trusted base in Smtlink 2.0, while carefully-written, exposes the user to errors in translation,
either by bugs in Smtlink or by unaccounted-for semantic gaps between the semantics of ACL 2, SMT
theory, and Python. Unlike most interactive theorem prover/SMT solver integrations such as Sledgeham-
mer for Isabelle/HOL and CoqSMT, one of Smtlink’s design goals was to support automatic, non-trivial
translation of expressions not directly expressible in an underlying SMT theory, for instance, by support-
ing FTY-defined types and a translation from alists to SMT arrays. Unfortunately, these non-trivial trusted
components, which include hard-coded translation logic, have made it difficult to extend Smtlink. Addi-
tionally, while ACL 2 facilities such as meta-extract allow reflection on the currently logical world from
a verified clause processor, the problem of verifying non-trivial formula translations poses a substantial
proof burden.
     We describe Smtlink 3, a compiler that uses the ACL 2 rewriter to normalize ACL 2 proof goals to a
quantifier-free subset of SMT- LIB. Initially, we wanted the rewriter to apply rewrite rules between the
functions existent in the goal term and constrained functions that model an SMT theory, such as real
arithmetic. After successful trials using the rewrite$ interface, we expanded its use to type inference
and goal simplification before the SMT- LIB backend. Using the rewriter for type inference allows us to
bring the ACL 2 prover’s reasoning capabilities to bear on the task. Our implementation of type inference,
term rewriting, and simplification have reduced the complexity of Smtlink and made it possible to inte-
grate user-provided translation theories using existing, idiomatic ACL 2 rewrite rules. Such user-provided
theories, i.e., collections of rewrite rules, make Smtlink 3 readily extensible; thus many features such as

                                                                        © C.K. Chen, M.R. Greenstreet & M.I. Seltzer
A. Coglio and S. Srinivasan (Eds.): 20th ACL2 Workshop (ACL2-2026)
                                                                        This work is licensed under the
EPTCS ??, 2026, pp. 1–18, doi:10.4204/EPTCS.??.??
                                                                        Creative Commons Attribution License.

2                                                                                                Smtlink 3


FTY support that were hard-coded in Smtlink 2 can be handled by constructing an appropriate translation
theory. Additionally, by targetting the SMT- LIB query language, Smtlink can now use any supporting
SMT solver while removing Python from the trusted computing base.




2    Background
The original Smtlink [15] translated ACL 2 formulas to the Z 3 Python API using trusted clause processors.
The Smtlink frontend simplifies the proof goal, e.g., by function expansion, while the backend emits a
Python file for Z 3 to consume. Because Smtlink consists of trusted clause processors, it uses the ACL 2
prover to validate the output of the frontend a posterori. For example, if goal A is transformed by the
frontend to A′ a new subgoal, A′ =⇒ A, is added from the prover to show that the frontend was validity
preserving.
     Smtlink 2.0 [17] shifts from a trusted frontend-backend architecture to a multi-pass approach, where
the frontend is decomposed into smaller, verified clause processors. Smtlink 2.0 also adds support for
the FTY [2] ADT library, to translate FTY datatype definitions into their SMT equivalents. Like Smtlink,
Smtlink 2.0 only supports the Z 3 Python API.
     While all these efforts showed the power and efficiency of a verified clause processor frontend to
Z 3, our focus is on simplifying Smtlink, improving its extensibility through user-provided translation
theories, reducing the trusted computing base, and moving from the Z 3 Python API to SMT- LIB.



3    Related work
Both Isabelle/HOL’s SMT tactic [5, 6] and Rocq’s SMTCoq tactic [10] provide mechanisms to discharge
proof goals using an SMT solver. Both efforts concern foundational provers, e.g., those built around a
small kernel, so both focus on proof reconstruction: translating the SMT solver’s proof into a resolution
proof in the kernel. Both tactics’ backend translators to SMT- LIB are unverified, because proof recon-
struction removes the requirement to trust the SMT solver. Unfortunately, proof reconstruction is not
always possible, for example, when a solver proof contains a “theory lemma”, a meta proof rule that rep-
resents a fact from the theory solver the host system is unable to prove independently. Additionally, both
efforts’ translation facilities are limited: the proof goals are expected to be SMT-expressible. Smtlink 3
differs from these efforts by focusing on automation for proof goals not directly expressible in the theory
of the SMT solver. We leave proof reconstruction for future work.
     Another alternative use of SMT solvers is as hammers: fast boolean and equality reasoning machines
that identify relevant facts from a theorem prover’s universe of theorems. Rather than use heuristics
to select which rules to apply, ITPs such as Isabelle/HOL, Rocq, and Lean have settled on the use of
hammers, named after the first, Isabelle/HOL’s Sledgehammer [4]. Sledgehammer operates on an en-
semble approach, using SMT solvers such as CVC 4 and first-order ATPs such as Vampire [19] and E [20]
in parallel. Here external solvers are used as “lemma filters”, and not for augmenting host system the-
ory reasoning capabilities, as in Smtlink. The Sledgehammer approach has proven successful because
it augments Isabelle/HOL’s limited automation facilities; indeed, the tool allows the user to select from
three rule-matching heuristics to populate the initial set of facts given to the provers [14]. Because ACL 2
is an automated prover with existing induction and rewrite heuristics, the hammer approach would be
redundant.

C.K. Chen, M.R. Greenstreet & M.I. Seltzer                                                               3


3.1   Decision procedure integrations in ACL 2
The first related area in ACL 2 are decision procedure integrations such as ACL 2-UCLID [13], ACL 2-SMT
[22], SULFA [18], GL [23], and Lisp-Z 3 [26]. The first four target decidable subsets of the ACL 2 logic:
   1. ACL 2-UCLID [13]: CLU, where counter arithmetic refers to peano-style increment/decrement.
   2. ACL 2-SMT [22]: AUFLIA from SMT- LIB: Formulas over the theory of linear integer arithmetic and
      arrays extended with free sort and function symbols but restricted to arrays with integer indices
      and values [3].
   3. SULFA [18]: the subclass of unrollable list formulas in ACL 2, where all non-list arguments to
      functions are constant.
    4. GL [23]: The finite subset of ACL 2, e.g., terms over booleans, bitvectors, etc.
     Only ACL 2-SMT targets SMT- LIB, although UCLID is considered an early example of an eager SMT
solver. SULFA uses a SAT solver, while GL can use either an internal BDD procedure or an external SAT
solver. In terms of soundness, all except GL trust the external decision procedure; GL in SAT mode can
reconstruct proofs from the solver.
     Like Smtlink, ACL 2-UCLID, ACL 2-SMT, and SULFA apply transformations to the proof goal in the
manner of a compiler or static analyzer before calling the decision procedure. GL uses symbolic execu-
tion to yield a verification condition, much like Rosette [25].
     Lisp-Z 3 [26]focuses on a different problem: providing a high-performance SMT- LIB interface to the
Z 3 SMT solver usable from Common Lisp, including ACL 2. Here the focus is on a useful and efficient
foreign function interface between Common Lisp and the Z 3 C API. Using Lisp-Z 3, a user can inter-
act with the solver statefully, adding and removing assertions using SMT- LIB as a command language.
Depending on the circumstances, Smtlink could benefit from a high-performance solver interface like
Lisp-Z 3.
     Our work focuses on extensible, automatic translation of proof goals to SMT- LIB, where the target
language is specified using ACL 2 constrained functions, because this allows us to succinctly and precisely
define our understanding of the smt-lib semantics.

3.2   Specification inference and stepwise refinement frameworks
Axe [21] and APT [7, 8, 12] transform programs and apply some of the same techniques we explore in
Smtlink, namely automatic, verified lifting. The main differences revolve around their objects and the
relations they prove and preserve.
     Axe is a toolkit to prove the functional equivalence of some machine code to some local specification,
e.g., that some JVM bytecode implements a cryptographic algorithm. It works via symbolic execution to
lift a program to a logical object in ACL 2, followed by transformations and equivalence checking against
an existing specification. Transformations are handled by the axe rewriter, which operates over graph
structures. Equivalence checking uses the STP [11] SMT solver. The Axe rewriter and STP interface are
implemented using trusted clause processors. In contrast, the only trusted component in Smtlink 3 is the
SMT solver interface.
     A PT is a flexible toolkit for generating new ACL 2 functions given known isomorphisms. For instance
for function f : A → B, if isomorphisms A ≃ A′ and B ≃ B′ can be shown, APT can generate a function f ′ :
A′ → B′ . In addition to specification inference, APT can also use isomorphisms to transform specifications
to implementations using stepwise refinement. Because APT verifies isomorphisms, which are a very
strong correspondence, it could be used to build translation theories for use by Smtlink. Our work
addresses this problem differently, transforming proof goals, not function definitions.

    4                                                                                                   Smtlink 3


    4     Design
    At the highest level, Smtlink is a partial function from the set of ACL 2 terms to a subset of SMT- LIB
    expressible terms.
                                        S : TACL2 ⇀ TSMT , TSMT ⊆ TACL2
    Where S is validity-preserving:
                                                  ∀t ∈ TACL2 .S(t) =⇒ t.
    Validity-preservation is also the property of a valid clause processor. Simply, a proof of the output of
    Smtlink is a proof of the original conjecture.
        Smtlink is a partial function because it may fail. For instance, a goal may contain functions that
    operate over types unknown to Smtlink, contain free variables whose types cannot be inferred, or trigger
    a rewrite loop that violates the rewrite-stack-limit, aborting the proof attempt.
        Figure 1 is a flowchart showing the pathway a proof goal takes through Smtlink 3. Each subsection
    corresponds to a different class of transformation and their relevant correctness condition.

    4.1   Type inference
    Smtlink 3 uses type inference to inform the process of transforming an ACL 2 proof goal to well-typed
    query in SMT- LIB, even for goals that lack explicit type hypotheses, such as those that follow fixtype
    discipline [24]. Such theorems would fail under Smtlink 2.0, which requires explicit type hypotheses.
    While both ACL 2 and SMT- LIB describe objects in first-order logic, their typing disciplines differ: the
    former is dynamically-typed where all functions effectively operate over a single universe, and the latter
    is a statically-typed, many-sorted logic where typing judgements are required for every constant and
    function. Typing information is often encoded as a hypothesis for a term of interest. This is common
    in ACL 2 where type hypotheses can help with proofs by constraining variables to a subset of the logical
    universe, for example, by restricting the arguments of a function to the integers.
1   ( implies ( and ( integerp x )
2                   ( integerp y ) )
3             ( foo x y ) )

        Correctness conditions for type inference clause processors are couched with a separate type cor-
    rectness hypothesis. The generic type inference clause processor is now a function over pairs of ACL 2
    terms: (t1 ,t2 ) ∈ TACL2 × TACL2 , for the type correctness hypothesis in the first and the original proof goal
    in the second. For a new goal entering Smtlink, the first element of the pair is the trivial type judgement
    T, for true. We can prove that a type inference clause processor is validity-preserving if the original type
    judgement implies the new type judgement, and the original goal is implied by the new goal.

                       ∀torig , gorig ∈ TACL2 .
                                                                                                               (1)
                             S(torig , gorig ) = (tnew , gnew ).(torig =⇒ tnew ) ∧ (gnew =⇒ gorig ).

    For example, it would be invalid to transform a typing judgement (integerp x) in the example above
    to (evenp x) the even integers, because that over-constrains the new problem, i.e., a proof of the new
    problem is not necessarily a proof of the original.
        Common idioms in ACL 2 omit some or all of the type hypotheses needed for translation to SMT- LIB.
    For example when using a type-fixing discipline such as FTY [24], all functions may have congruences
    over the fixing functions for their arguments, and it suffices to prove the theorem assuming that all free

C.K. Chen, M.R. Greenstreet & M.I. Seltzer                                    5




                         Figure 1: Smtlink 3 clause processor architecture.

    6                                                                                                Smtlink 3


    variables are of their “correct” types. Smtlink 3 provides two mechanisms to support such type-terse
    formulations of theorems. As elaborated in Section 5.2, type inference in Smtlink 3 is implemented
    using the ACL 2 rewriter. Continuing the previous example, given a goal
1   ( implies ( and ( integerp y )
2                   (= x (* 2 y ) ) )
3             ( foo x y ) )

    Smtlink 3 will infer that x satisfies integerp and evenp even though their are no explicit hypotheses for
    these type judgements. In the case that the type inference stage cannot infer an “obvious” type, the user
    may add it using a :hypothesize hint that adds the hypothesis for generating SMT- LIB code and will
    produce an additional subgoal to prove that the negation of the goal implies the added hypothesis.

    4.2   Term rewriting
    Due to restrictions on the use of the rewrite$ interface from logic mode functions, which include clause
    processors, we need to treat rewritten terms as untrusted hints. Our correctness condition depends on
    proving that, assuming the input type correctness condition, the new goal expression grewrite is equivalent
    to the original gorig .

                            ∀torig , gorig , grewrite ∈ TACL2 .
                                                                                                            (2)
                                  (torig =⇒ (gorig ≡ grewrite )) =⇒ grewrite =⇒ gorig .

    4.3   Type extraction
    When a proof goal reaches the end of the chain of verified clause processors, its variable and function
    types have been inferred and it has been through the translation step at least once. To successfully
    translate a goal into a valid SMT- LIB query, the functions within must be monomorphic, and variable
    judgements must be unambiguous. These properties determine the subset TSMT ⊂ TACL2 introduced at
    the beginning of the section.
        Notice that the type correctness hypothesis exists to communicate typing information between clause
    processors, to enable rewrite rules to transform terms, and to communicate the final judgement of vari-
    ables and functions for translation to SMT- LIB, but logically speaking, in the ACL 2 world, they are
    superfluous to the validity of the goal itself. The final step, translating the goal expression into a SMT-
    LIB query, requires an unconditional i.e., path-condition-free type correctness hypothesis that provides
    a unambiguous, consistent type judgement to every function and variable in the goal. The final correct-
    ness condition reflects the assertion that the unconditional type correctness hypothesis tuncond does not
    over-constrain the simplified goal expression gsmt .

                                           ∀tuncond , gorig , gsmt ∈ TACL2 .
                                                                                                            (3)
                                                 (tuncond =⇒ gsmt ) =⇒ gorig


    5     Implementation and application
    Smtlink 3 is implemented in 6 clause processors; all but the last are verified. The first two carry out type
    inference and type fixing. Term rewriting comes next; if the term changes, it is re-processed again until
    the proof goal is normalized. Once this is complete, Smtlink extracts unconditional type judgements for

    C.K. Chen, M.R. Greenstreet & M.I. Seltzer                                                              7


    the goal and simplifies the goal expression. Finally, the trusted clause processor translates judgements
    and the goal into a SMT- LIB script, then executes the SMT solver.
        Our running example is simple system of nonlinear inequalities from the Smtlink 2.0 paper [16].
                                                    9x2
                                  ∀x ∈ R, ∀y ∈ R.        + y2 ≤ 1
                                                     8
                                                    ∧ x 2 − y2 ≤ 1                                         (4)
                                                                   17 2
                                                                    
                                                     =⇒ y < 3 x −       −3
                                                                   8
    This formula is illustrated in Figure 2 and expressed as a defthm event, with the hints elided.




    Figure 2: A system of three nonlinear inequalities, separately and together: An ovaloid region bounded
          2
    by 9x8 + y2 ≤ 1 in blue, a hyperbolic region bounded by x2 − y2 ≤ 1 in green, and the region below the
    parabola y < 3(x − 17  2
                        8 ) − 3 in purple. Note that the first two inequalities imply the third.

1   ( defthm poly-ineq-example
2      ( implies ( and ( real / rationalp x )
3                        ( real / rationalp y )
4                        ( <= (+ (* (/ 9 8) x x ) (* y y ) ) 1)
5                        ( <= ( x ^2- y ^2 x y ) 1) )
6                 (< y
7                     (- (* 3 (- x (/ 17 8) ) (- x (/ 17 8) ) )
8                          3) ) )
9      : hints (( " Goal ’ ’ " : smtlink ...) ) )


    5.1   A note on using rewrite$ from a clause processor
    Smtlink 3 uses the rewrite$ function to call the rewriter. Unfortunately, clause processors cannot
    contain program mode functions that traffic in state, such as rewrite$. Instead, we install a computed
    hint that only fires before the clause processor of interest. The computed hint, itself a program mode
    function, calls rewrite$ and passes the rewritten term as a hint to the next clause processor. As noted
    in subsection 4.2, to preserve soundness, the clause processor generates a proof subgoal to validate the
    rewritten term it was given.

    5.2   Type inference
    Type-inference is performed by a computed hint and a clause processor. The computed hint uses
    rewrite$ to obtain type judgements for the clause and each of its subterms. Following the conven-
    tions of the ACL 2 waterfall, Smtlink 3 performs type inference separately for each disjunct of the clause

    8                                                                                                              Smtlink 3


    under the hypothesis that the all of the other disjuncts are equivalent to nil. This improves execution ef-
    ficiency and ensures that type inference in Smtlink 3 does not depend on the ordering of the hypotheses.
    For each (sub-)term, x, of the disjunct, the computed hint generates an expression of the following form.
1   ( implies x . path-cond
2             ( and ( ti-equal ( hide ( cdr ( cons x . id ( type-recognizer-1 x ) ) ) )
3                               ( type-recognizer-1 x ) )
4                    ( ti-equal ( hide ( cdr ( cons x . id ( type-recognizer-2 x ) ) ) )
5                               ( type-recognizer-3 x ) )
6                    . . .) )

    The basic idea is to pair a hidden application of each (type-recognizer-i x) with an application
    that can be exposed to rewrite$. If the exposed application rewrites to t, then we infer that the type
    judgement holds. The terms are written so that if we had a metaextract-like theorem that showed
         (equal (ev (rewrite$ x)) (ev x))
    then we could prove the correctness of the type judgements. Briefly,
        x.pathcond is the context given by all enclosing if expressions controlling this expression.
        x.id a unique integer tag for each (sub-)term of the clause.
        type-recognizer-i: we generate a test for each type-recognizer specified in the Smtlink hint1
    The computed hint specifies that the type inference clause processor should be used and adds the expres-
    sion returned by rewrite$ to the hint for the clause-processor.
         The type inference clause processor creates a “typed-term” that pairs each (sub-term) of the goal with
    its type-judgements from the clause-processor hint and returns two clauses:
         1. A clause that bundles the typed-term with the original clause for use by the next clause processor.
         2. A clause that asserts that the type-annotations are correct. This effectively asks ACL 2 to verify the
            result from rewrite$.

    5.3     Type fixing
    The type-fixing clause processor chooses a “SMT judgement” from the possible judgements inferred
    by the type inference phase, corresponding to a type that is either directly expressible in SMT- LIB, or
    one that can be rewritten to one directly expressible. For example, the literal constant 3 satisfies not
    just INTEGERP, but all of its supertypes, including RATIONALP and ACL2-NUMBERP, which includes the
    complex numbers. Top-down selects a single judgement at each node, and for function call nodes,
    propagates a selection downwards, informed by typing rules gleaned from the environment using the
    ACL 2 meta-extract facility. If 3 was the argument of binary-+ in (binary-+ 3 2), and top-down
    had chosen to propagate down an INTEGERP judgement at binary-+, then both 3 and 2 would receive
    INTEGERP judgements to keep the judgements consistent, since there is no theorem in our world that
    allows us to infer an integer from the sum of two arbitrary rationals. Therefore, the node for 3 would
    look like the following, where the chosen judgement occupies the SMT-JUDGEMENTS field.
1   ( SMT :: JUDGEMENTS ( INTEGERP SMT :: X ) ( RATIONALP SMT :: X ) )
2   ( SMT :: SMT-JUDGEMENTS ( INTEGERP SMT :: X ) )
3   ( SMT :: GUTS : QUOTE 3)

       1 Creating tests for the cross-product of sub-terms and recognizers may create a performance bottleneck. We will explore

    performance optimization when we have more usage data.

     C.K. Chen, M.R. Greenstreet & M.I. Seltzer                                                               9


         One invariant of a typed term is that SMT-JUDGEMENTS is a subset of JUDGEMENTS. Both judgements
     and smt-judgements are modelled with ordered sets [9], whose theory includes theorems about subset
     relations that helped with the clause processor proof.

     5.4   Term rewriting
     Our use of the rewriter to transform terms comes from the insight that if a theorem shows that some SMT
     theory function simulates an ACL 2 function, then that rule can be used to rewrite ACL 2 terms to SMT
     terms. For example, here is an encapsulation that constrains a clique of functions representing the SMT
     real theory, noting that subtraction and division are macros for unary negation with addition and unary
     reciprocation with multiplication.
 1   ( encapsulate
 2        ((( rational- +           * *) = > *)
 3         (( rational--            *) = > *)
 4         (( rational- *           * *) = > *)
 5         (( rational- /           *) = > *)
 6         (( rational- <           * *) = > *) )
 7
 8     ( local
 9         ( defun rational- + ( x y )
10            ( binary- + x y ) ) )
11     ...
12     ( local
13         ( defun rational- < ( x y )
14            (< x y)))
15
16     ( defthm return-of-rational- +
17         ( implies ( and ( rationalp x )
18                         ( rationalp y ) )
19                   ( rationalp ( rational- + x y ) ) ) )
20     ...
21     ( defthm return-of-rational- <
22         ( implies ( and ( rationalp x )
23                         ( rationalp y ) )
24                   ( booleanp ( rational- < x y ) ) ) )
25
26     ( defthmd s p e c i a l i z e - b i n a r y - r a t i o n a l - o p e r a t o r s
27         ( implies ( and ( rationalp x )
28                             ( rationalp y ) )
29                   ( and ( equal ( binary- + x y )
30                                           ( rational- + x y ) )
31                             ( equal ( binary- * x y )
32                                           ( rational- * x y ) )
33                             ( equal ( < x y )
34                                           ( rational- < x y ) ) ) ) )
35     ...
36     ( defthmd s p e c i a l i z e - u n a r y - r a t i o n a l - /
37         ( implies ( and ( rationalp x )
38                             ( not (= x 0) ) )
39                   ( equal ( unary- / x )
40                                 ( rational- / x ) ) ) ) )

         This encapsulation has three goals: first, it introduces fresh function symbols to represent an SMT
     theory. Second, it establishes typing constraints useful for inferring types over SMT expressions. Finally,

     10                                                                                                                Smtlink 3


     it establishes rewrite rules, disabled by default, that allow us to specialize ACL 2 arithmetic functions to
     their singly-typed SMT counterparts, and enumerates preconditions. In the case of the unary reciprocal
     function unary-/, we can rewrite it to rational-/ only if we can show that the argument is a non-
     zero rational number. The non-zero constraint stems from differences between the ACL 2 and SMT- LIB
     semantics, where ACL 2 (unary-/ 0) is 0 but SMT- LIB (rational-/ 0) is an unspecified rational
     number.
          The Smtlink hint interface takes a :translation-theory keyword argument that takes a standard
     ACL 2 :in-theory hint. In this case, the hint enables the specialization theorems that let us rewrite
     generic numeric functions into rational functions.
 1   ( defthm poly-ineq-example
 2      ( implies ( and ( real / rationalp x )
 3                        ( real / rationalp y )
 4                        ( <= (+ (* (/ 9 8) x x ) (* y y ) ) 1)
 5                        ( <= ( x ^2- y ^2 x y ) 1) )
 6                 (< y
 7                     (- (* 3 (- x (/ 17 8) ) (- x (/ 17 8) ) )
 8                          3) ) )
 9      : hints (( " Goal ’ ’ " : smtlink
10                            (: translation-theory
11                             ( union-theories
12                                 ( theory ’ minimal-theory )
13                                 ’( smt :: return-of-rational- +
14                                    smt :: return-of-rational--
15                                    smt :: return-of-rational- *
16                                    smt :: return-of-rational- /
17                                    smt :: return-of-rational- <
18                                    smt :: s p e c i a l i z e - b i n a r y - r a t i o n a l - o p e r a t o r s
19                                    smt :: s p e c i a l i z e - u n a r y - r a t i o n a l -
20                                    smt :: s p e c i a l i z e - u n a r y - r a t i o n a l - /) ) ) ) ) )

        Within this constrained theory, the rewriter is able to specialize the arithmetic operators to their SMT
     counterparts, using the correctness hypotheses from type inference.
 1   ( IF
 2     ( RATIONALP X )
 3     ( IF
 4       ( RATIONALP Y )
 5       ( IF
 6         ( IF
 7           ( SMT :: RATIONAL- < ’1
 8                                   ( SMT :: RATIONAL- + ( SMT :: RATIONAL- * ’9/8
 9                                                                               ( SMT :: RATIONAL- * X X ) )
10                                                          ( SMT :: RATIONAL- * Y Y ) ) )
11           ’ NIL
12           ( IF ( SMT :: RATIONAL- <
13                        ’1
14                        ( SMT :: RATIONAL- + ( SMT :: RATIONAL- * X X )
15                                               ( SMT :: RATIONAL-- ( SMT :: RATIONAL- * Y Y ) ) ) )
16                 ’ NIL
17              ’T ) )
18         ( SMT :: RATIONAL- <
19                 Y
20                 ( SMT :: RATIONAL- +
21                        ’-3
22                        ( SMT :: RATIONAL- * ’3

     C.K. Chen, M.R. Greenstreet & M.I. Seltzer                                                               11


23                                           ( SMT :: RATIONAL- * ( SMT :: RATIONAL- + X ’-17/8)
24                                                                ( SMT :: RATIONAL- + X ’-17/8) ) ) ) )
25       ’T )
26     ’T )
27    ’T )

         If the rewriter were able to change the term, then the typing information and path conditions in the
     correctness conditions could refer to functions and variables that no longer exist. To re-infer proper
     typing judgements, we re-introduce the new goal through function expansion and the remainder of the
     frontend, before trying to rewrite again. If the rewriter returns an unmodified term, then we consider the
     term fully transformed and pass it along to type extraction. We note that this admits rewrite cycles, if the
     translation theory admits them.

     5.5   Type extraction and term simplification
     At this point in the pipeline, the types in the goal should be in the target SMT logic. Before we write a
     SMT- LIB form, we need to extract all variable and function judgements. We require typing judgements
     that apply unconditionally across the entire term, e.g., a formula cannot re-use the same variable and
     give it different types according to some condition, because SMT- LIB is a static, monomophically typed
     language. Type extraction works by walking the typed term and gathering up all the variable and function
     judgements into a smt-judgement form.
 1   ’(( SMT :: VARS (( SMT :: NAME . X )
 2                     ( SMT :: JUDGEMENT . RATIONALP ) )
 3                   (( SMT :: NAME . Y )
 4                     ( SMT :: JUDGEMENT . RATIONALP ) ) )
 5     ( SMT :: FNS (( SMT :: NAME . SMT :: RATIONAL- *)
 6                   ( SMT :: DOMAIN RATIONALP RATIONALP )
 7                   ( SMT :: RANGE . RATIONALP ) )
 8                  (( SMT :: NAME . SMT :: RATIONAL- +)
 9                   ( SMT :: DOMAIN RATIONALP RATIONALP )
10                   ( SMT :: RANGE . RATIONALP ) )
11                  (( SMT :: NAME . SMT :: RATIONAL-- )
12                   ( SMT :: DOMAIN RATIONALP )
13                   ( SMT :: RANGE . RATIONALP ) )
14                  (( SMT :: NAME . SMT :: RATIONAL- <)
15                   ( SMT :: DOMAIN RATIONALP RATIONALP )
16                   ( SMT :: RANGE . BOOLEANP ) )
17                  (( SMT :: NAME . RATIONALP )
18                   ( SMT :: DOMAIN ACL2 :: ANY-P$INLINE )
19                   ( SMT :: RANGE . BOOLEANP ) ) ) ) )

         After extraction, ambiguous judgements can be detected and reported to the user. A smt-judgement
     can be interpreted with smt-judgement->expr to an IF-encoded conjunction of variable judgements
     and function judgements.
 1   ( IF ( IF ( RATIONALP X )
 2              ( IF ( RATIONALP Y ) ’T ’ NIL )
 3           ’ NIL )
 4        ( IF ( IF ( IF ( RATIONALP SMT :: X2 )
 5                         ( IF ( RATIONALP SMT :: X1 ) ’T ’ NIL )
 6                      ’ NIL )
 7                   ( IF ( RATIONALP ( SMT :: RATIONAL- * SMT :: X2 SMT :: X1 ) )
 8                         ’T

     12                                                                                                Smtlink 3


 9                           ’ NIL )
10                    ’T )
11                 ( IF ( IF ( IF ( RATIONALP SMT :: X2 )
12                                    ( IF ( RATIONALP SMT :: X1 ) ’T ’ NIL )
13                                 ’ NIL )
14                              ( IF ( RATIONALP ( SMT :: RATIONAL- + SMT :: X2 SMT :: X1 ) )
15                                    ’T
16                                 ’ NIL )
17                           ’T )
18                       ...
19                    ’ NIL )
20              ’ NIL )
21        ’ NIL )

            This IF form is rather busy, but it is one conjunct of judgements equivalent to the following term.
 1   ( AND ( RATIONALP X )
 2         ( RATIONALP Y )
 3         ( IMPLIES ( AND ( RATIONALP SMT :: X2 )
 4                         ( RATIONALP SMT :: X1 ) )
 5                   ( RATIONALP ( SMT :: RATIONAL- * SMT :: X2 SMT :: X1 ) ) )
 6         ...
 7         )

         The last transformation simplifies the goal by erasing type recognizers such as RATIONALP. We
     achieve this by applying the rewriter to the goal expression with the smt judgement hypothesis, yielding
     the following fully-translated term.
 1   ( IF
 2           ( IF ( RATIONAL- < ’1
 3                               ( RATIONAL- + ( RATIONAL- * ’9/8 ( RATIONAL- * X X ) )
 4                                              ( RATIONAL- * Y Y ) ) )
 5                 ’ NIL
 6              ( IF ( RATIONAL- < ’1
 7                                  ( RATIONAL- + ( RATIONAL- * X X )
 8                                                 ( RATIONAL-- ( RATIONAL- * Y Y ) ) ) )
 9                    ’ NIL
10                 ’T ) )
11           ( RATIONAL- < Y
12                          ( RATIONAL- + ’-3
13                                         ( RATIONAL- * ’3
14                                                        ( RATIONAL- * ( RATIONAL- + X ’-17/8)
15                                                                      ( RATIONAL- + X ’-17/8) ) ) ) )
16        ’T )



     5.6      Translation to SMT- LIB
     The final, trusted clause processor is responsible for translating the smt-judgement into a sequence of
     SMT- LIB declarations.

 1   ((| set-logic | AUFNIRA )
 2    (| declare-sort | ANY-P$INLINE 0)
 3    (| declare-fun | RATIONALP ( ANY-P$INLINE ) | Bool |)
 4    (| declare-const | X | Real |)
 5    (| declare-const | Y | Real |)

     C.K. Chen, M.R. Greenstreet & M.I. Seltzer                                                                               13


     Note the vestigial declarations: the RATIONALP and ANY-P type recognizers no longer occur in the goal;
     they were pruned away in the last simplification pass. The second translation turns the goal expression
     into an assertion of its negation.
 1   (| assert | (| not | (| ite | (| ite | ( < 1 (+ (* (/ 9 8) (* X X ) ) (* Y Y ) ) )
 2                                           | false |
 3                                           (| ite | ( < 1 (+ (* X X ) (- (* Y Y ) ) ) )
 4                                                     | false | | true |) )
 5                                 (< Y
 6                                     (+ (- 3)
 7                                         (* 3
 8                                               (* (+ X (/ (- 17) 8) )
 9                                                  (+ X (/ (- 17) 8) ) ) ) ) )
10                                 | true |) ) )
11   (| check-sat |)

     The Z 3 prover quickly determines that the negation of the goal is unsatisfiable, ACL 2 proves the side
     conditions generated during term rewriting and type extraction, and the proof is done. If the solver
     returned sat or an unknown result, the clause processor returns the empty clause, causing the proof to
     fail.

     5.7    Term rewriting beyond function specialization
     So far we have discussed transformations that replace particular function symbols in place. In the exam-
     ple above, transforming an arithmetic expression from polymorphic functions to monomorphic functions
     in a single bottom-up sweep shows how function specialization is a good fit for the ACL 2 rewriter. Here,
     we discuss an additional strategy we call indirect term rewriting, where the rules of the translation theory
     rewrite terms in a top-down fashion. Our example covers the partial translation from ACL 2 associative
     lists to the SMT- LIB theory of functional arrays with extensionality.
          This technique is motivated by the observation that even if a SMT- LIB theory is insufficient to model
     an entire ACL 2 (sub-)theory, a simulation is possible for a subset of terms. For example, ACL 2 associative
     lists, or alists, are an algebraic datatype with two constructors: nil and nested acons pairs, and one
     destructor, assoc. They are widely used as mapping structures, e.g., from keywords to values, or for
     modelling state, such as a random-access memory. Similarly, SMT- LIB functional arrays also axiomatize
     maps from keys to values via store and select functions, but have a much weaker theory, e.g., assoc
     will return nil by default for absent keys, whereas the behaviour of select is only constrained to return
     a value in the range of the function2 .
          Furthermore, because alists are just Lisp cons structures, their API admits richer interactions. For
     example, we can recurse over the structure of an alist to examine all mappings and even “look back
     in time” at previous mappings, because alists are non-destructive, functional structures. Constructing
     a valid translation theory for these richer interactions requires building complex array structures; this
     reflects the fact that an alist captures more information than an axiomatic functional array. Nevertheless,
     if an alist expression restricts itself to assoc and acons functions, where the topmost alist function is an
     assoc, it is a straightforward matter to construct a valid translation theory to arrays.
          For this example, the user constructs a simple theory of type alists and arrays within ACL 2and arrays
     within ACL 2 and a translation theory that rewrites assoc terms from the top down, incrementally trans-
     forming the alist subtrees into array subtrees. This theory is expressed as a set of rewrite rules that are
        2 Some solvers, like Z 3 extend the theory of arrays to include “constant arrays”, which can be used to model default be-

     haviour.

     14                                                                                                 Smtlink 3


     made available to the term replacement clause processor. For a given alist from the integers to symbols,
     the rewrite rule for assoc is as follows.
 1   ( defthmd i n t - s y m - t o p - d o w n - t r a n s l a t i o n - o f - a s s o c - e q u a l
 2        ( implies ( int-sym-alist-p al )
 3                     ( equal ( assoc-equal k al )
 4                                   ( int-sym-array-select ( int-sy m-arra y-fro m-al al )
 5                                                                               k))))

     Note that the rule wraps the alist subexpression with a lifting function, int-sym-array-from-al. We
     then introduce a lifting rule for lifting cons terms.
 1   ( defthmd i n t - s y m - t o p - d o w n - t r a n s l a t i o n - o f - a c o n s
 2        ( implies ( and ( integerp k )
 3                               ( symbolp v ) )
 4                     ( equal ( in t-sym- array -from- al ( cons ( cons k v ) al ) )
 5                                   ( int-sym-array-store ( int-sy m-arr ay-fro m-al al )
 6                                                                             k
 7                                                                             ( cons k v ) ) ) ) )

     Note also that our translation theory lacks a rule for translating terminals. This is to say that, given the
     following alist goal,
 1   ( implies ( and ( integerp k1 )
 2                   ( integerp k2 )
 3                   ( symbolp v1 )
 4                   ( symbolp v2 )
 5                   ( int-sym-alist-p al ) )
 6             ( equal ( assoc-equal k1
 7                                       ( cons ( cons k1 v1 )
 8                                              ( cons ( cons k2 v2 ) al ) ) )
 9                      ( cons k1 v1 ) ) )

     our translation theory will converge on the following term.
 1   ( implies ( and ( integerp k1 )
 2                   ( integerp k2 )
 3                   ( symbolp v1 )
 4                   ( symbolp v2 )
 5                   ( int-sym-alist-p al ) )
 6             ( equal ( int-sym-array-select
 7                        ( int-sym-array-store
 8                          ( int-sym-array-store ( int-sy m-arr ay-fro m-al al )
 9                                                      k2 ( cons k2 v2 ) )
10                          k1 ( cons k1 v1 ) )
11                        k1 )
12                      ( cons k1 v1 ) ) )

     Our final translation to SMT- LIB declares both the alist types and lifting function as uninterpreted, in lieu
     of introducing a fresh array constant. Smtlink 3 processes and proves the goal above automatically. This
     translation of of ACL 2 alists to SMT- LIB arrays is not hard-coded into Smtlink 3 but is effected by the
     user providing a suitable set of rewrite rules.


     6    Discussion/future work
     In this section we compare Smtlink 3 with its predecessor, and discuss future work.

C.K. Chen, M.R. Greenstreet & M.I. Seltzer                                                                15


6.1   Features compared to Smtlink 2.0
Smtlink 3 targets the AUFNIRA “Closed formulas built over arbitrary expansions of the Reals_Ints and
ArraysEx signatures with free sort and function symbols” [1] SMT- LIB logic, as opposed to the default
“autodetect” Z 3 logic targeted by Smtlink 2.0, where the solver tries to match the logic to the query. In
both cases, the basic functions are the same: the boolean core with equality plus integer/real arithmetic.
Neither Smtlink 2.0 or 3 support quantification.
    Smtlink 2.0 has minimal, hardcoded support for Z 3 arrays, while Smtlink 3.0 can handle arbitrary
arrays, given a translation theory as shown in Section 5.7. Smtlink 2 supports FTY types and reporting
counterexample models from the solver, two features that Smtlink 3 lacks. We discuss these omissions in
Section 6.4. Finally, Smtlink 3 adds verified type inference and term rewriting for non-trivial translations;
as described in Section 4.1, features like type inference make Smtlink applicable to a wider range of
theorems, such as those that follow fixtype discipline and lack explicit type hypotheses.

6.2   Reduction in the trusted computing base
A primary goal of Smtlink 3 is a reduction in the trusted computing base, including the elimination of
Python as a runtime requirement. The trusted clause processor in Smtlink 3 occupies 459 lines of ACL 2,
which is a 81% reduction from Smtlink 2.0 in ACL 2/Lisp terms. If the 555 lines of Python are included,
the reduction is 84%. Approximately half of the trusted code base in Smtlink 2.0 forms the ACL 2 to z3
Python translator, whereas in Smtlink 3, the bulk of translation is done before entering the trusted clause
processor. We do not expect major expansions of the trusted computing base for future work, such as
FTY , counterexample, or additional theory support.


6.3   Overhead of type inference and term rewriting
The example at the beginning of Section 5 was taken from the Smtlink 2.0 [17] paper, which allows us
to compare relative performance, in terms of real time and prover steps. Smtlink 2.0 took 0.06 seconds
of wall-clock time and 1383 steps to prove the theorem on an Apple M 5 with ACL 2 8.7 on Steel Bank
Common Lisp 2.6.9 with Z 3 5.3.1. Initially, Smtlink 3 took 0.18 seconds and 32,688 steps. Much of this
is due to the 3.2× increase in the subgoals generated: Smtlink 2.0 at 20 and Smtlink 3 at 64. For Smtlink
3, proving the type inference side condition alone took over 30 subgoals. We expected some overhead
recertifying the output of the rewriter, but not to this degree.
    We theorized the additional proof complexity was due to an earlier design decision to operate over
monolithic goals. Normally during preprocessing, the prover transforms a goal containing a conjunction
of hypotheses and a conclusion such as (IMPLIES (AND (INTEGERP X) (INTEGERP Y)) (INTEGERP
(+ X Y))) into a list of discrete terms representing a clause of disjuncts: (LIST (NOT (INTEGERP
X)) (NOT (INTEGERP Y)) (INTEGERP (+ X Y))) noting that p =⇒ q ≡ ¬p ∨ q. This allows the
prover to simplify each clause member separately while assuming that the other disjuncts in the clause
are false. For example, when considering (NOT (INTEGERP X)), we can assume the falsity of the other
disjuncts, e.g., (INTEGERP Y) and (NOT (INTEGERP (+ X Y))). When Smtlink 2.0 starts on a proof
goal, it transforms the clause back into a monolithic disjunction, internally represented as a nested IF
expression: (IF (NOT (INTEGERP X)) ’T (IF (NOT (INTEGERP Y)) ’T (INTEGERP (+ X Y)))
’NIL). When type inference operates over a conditional expression, it has to account for path conditions,
which requires case-splitting, increasing the number of subgoals. Monolithic goals also have the down-
side of fixing an evaluation order for hypotheses, making the goal order-dependent, which is one reason
that Smtlink 2.0 used heuristics to reorder hypotheses.

16                                                                                                Smtlink 3


    We removed the monolithic clause treatment, and Smtlink now processes clauses in the conventional
fashion: each disjunct separately, assuming that the other members of the clause are false. This makes
Smtlink order-agnostic with regards to hypotheses, and no longer requires heuristics to reorder them.
This change has the side benefit of simplifying side conditions: for the same example, order-agnostic
Smtlink 3 takes 0.09 seconds and 10673 steps over 33 subgoals, four of which proved the type inference
side condition. We should note that matching the Smtlink 2 baseline is not the goal: type inference and
verified translation are non-trivial tasks.

6.4     Future work
Two long-term goals for Smtlink are extensibility and improving the user interface.

6.4.1    Extensibility
Smtlink 3 does not currently support translation of FTY types. Given the extensive amount of metadata
about type definitions in the FTY tables, it appears straightforward for Smtlink in future to infer their
existence in a goal and construct corresponding SMT- LIB datatype definitions, in a similar way to how it
constructs uninterpreted function declarations. This should not expand the trusted computing base.
    We plan to add support for more theories, such as bitvectors and strings, to make Smtlink more useful
for systems verification. Part of this goes with detaching the SMT- LIB model from the trusted clause
processor into a separate book, where standard SMT- LIB theories and logics can be formally described.

6.4.2    Improving the user interface
Smtlink 3 does not currently translate SMT models back to ACL 2, but nothing in the execution model
prevents us from reading or parsing a model from the solver. An interesting approach would be to apply
Smtlink’s translation steps, but in the reverse direction, so instead of abstracting ACL 2 terms to SMT- LIB,
we refine models back to ACL 2.
    Smtlink 2.0 is configured via a combination of custom keyword hints and a smt-hint table. These
declarations specify all manner of hints, such as:
   1. The supported type recognizers, used by type inference to construct the typing judgement for the
      rewriter to simplify.
     2. Returns theorems and their formals, used by meta-extraction during type-selection to push typing
        judgements down.
    3. User hypotheses for Smtlink to attach to the SMT query.
Our goal is to reduce the scope of Smtlink to handling translation, and move as much functionality back
to the waterfall. For instance, user hypotheses can be added using :use hints, and Smtlink will handle the
clause without any special considerations. Future work includes continuing to rationalize the interface,
and automating as much of the population of metadata such as type recognizers and returns theorems as
possible, to make interacting with Smtlink less cumbersome.


7     Conclusion
Smtlink is a book for integrating SMT solvers into the ACL 2 theorem prover. One of the goals of Smtlink
is proof automation, namely the automatic translation of idiomatic ACL 2 goals into SMT queries. Build-
ing and verifying non-trivial transformations, namely, compilers, poses a substantial proof burden. With

C.K. Chen, M.R. Greenstreet & M.I. Seltzer                                                                      17


Smtlink 3, we show a method for using the ACL 2 rewriter to assist with type inference, function special-
ization, and simplification. This not only simplifies Smtlink, but it allows users to provide translation
theories from the corpus of ACL 2 theorems that already exist.
    We acknowledge the support of the Natural Sciences and Engineering Research Council of Canada
(NSERC).


References
 [1] AUFNIRA. Available at https://smt-lib.org/logics-all.shtml#AUFNIRA.
 [2] ACL2 Foundation (2025): XDOC — Fty. webpage. Available at https://acl2.org/doc/index.html?
     topic=ACL2____FTY.
 [3] Clark Barrett, Pascal Fontaine & Cesare Tinelli (2016): The Satisfiability Modulo Theories Library (SMT-
     LIB). www.SMT-LIB.org.
 [4] Jasmin Christian Blanchette, Sascha Böhme & Lawrence C. Paulson (2011): Extending Sledgehammer with
     SMT solvers. In: Proceedings of the 23rd International Conference on Automated Deduction, CADE’11,
     Springer-Verlag, Berlin, Heidelberg, pp. 116–130, doi:10.1007/978-3-642-22438-6_11.
 [5] Sascha Böhme, Rustan Leino & Burkhart Wolff (2008): HOL-Boogie An Interactive Prover for the
     Boogie Program-Verifier. In: TPHOLs ’08 Proceedings of the 21st International Conference on Theo-
     rem Proving in Higher Order Logics, Springer-Verlag Berlin, Heidelberg, pp. 150–166, doi:10.1007/978-
     3-540-71067-7_15.     Available at https://www.microsoft.com/en-us/research/publication/
     hol-boogie-interactive-prover-boogie-program-verifier/.
 [6] Sascha Böhme & Tjark Weber (2010): Fast LCF-Style Proof Reconstruction for Z3. In Matt Kaufmann &
     Lawrence C. Paulson, editors: Interactive Theorem Proving, Springer Berlin Heidelberg, Berlin, Heidelberg,
     pp. 179–194, doi:10.1007/978-3-642-14052-5_14.
 [7] Alessandro Coglio, Matt Kaufmann & Eric Whitman Smith (2017): A Versatile, Sound Tool for Simplifying
     Definitions. In Anna Slobodová & Warren A. Hunt Jr., editors: Proceedings 14th International Workshop on
     the ACL2 Theorem Prover and its Applications, Austin, Texas, USA, May 22-23, 2017, EPTCS, pp. 61–77,
     doi:10.4204/EPTCS.249.5.
 [8] Alessandro Coglio & Stephen Westfold (2020): Isomorphic Data Type Transformations. Electronic Proceed-
     ings in Theoretical Computer Science 327, pp. 125–141, doi:10.4204/eptcs.327.12.
 [9] Jared Davis (2004): Finite set theory based on fully ordered lists. In: Fifth International Workshop on
     the ACL2 Theorem Prover and Its Applications (ACL2-2004), pp. 1–14. Available at https://www.cs.
     utexas.edu/~moore/acl2/workshop-2004/contrib/davis/set-theory.pdf.
[10] Burak Ekici, Alain Mebsout, Cesare Tinelli, Chantal Keller, Guy Katz, Andrew Reynolds & Clark Barrett
     (2017): SMTCoq: A Plug-In for Integrating SMT Solvers into Coq. In Rupak Majumdar & Viktor Kunčak, ed-
     itors: Computer Aided Verification, Springer International Publishing, Cham, pp. 126–133, doi:10.1007/978-
     3-319-63390-9_7.
[11] Vijay Ganesh & David L. Dill (2007): A Decision Procedure for Bit-Vectors and Arrays. In Werner Damm
     & Holger Hermanns, editors: Computer Aided Verification, 19th International Conference, CAV 2007,
     Berlin, Germany, July 3-7, 2007, Proceedings, Lecture Notes in Computer Science, Springer, pp. 519–531,
     doi:10.1007/978-3-540-73368-3_52.
[12] Kestrel Institute: Automated Program Transformations. webpage. Available at https://www.kestrel.
     edu/research/apt/.
[13] P. Manolios & S.K. Srinivasan (2005): Verification of executable pipelined machines with bit-level interfaces.
     In: ICCAD-2005. IEEE/ACM International Conference on Computer-Aided Design, 2005., pp. 855–862,
     doi:10.1109/ICCAD.2005.1560182.

18                                                                                                Smtlink 3


[14] Lawrence C. Paulson & Jasmin Christian Blanchette (2010): Three years of experience with Sledgeham-
     mer, a Practical Link Between Automatic and Interactive Theorem Provers. In Geoff Sutcliffe, Stephan
     Schulz & Eugenia Ternovska, editors: The 8th International Workshop on the Implementation of Logics,
     IWIL 2010, Yogyakarta, Indonesia, October 9, 2011, EPiC Series in Computing 2, EasyChair, pp. 1–11,
     doi:10.29007/36DT.
[15] Yan Peng & Mark Greenstreet (2015): Extending ACL2 with SMT Solvers. Electronic Proceedings in Theo-
     retical Computer Science 192, pp. 61–77, doi:10.4204/eptcs.192.6.
[16] Yan Peng & Mark Greenstreet (2015): Integrating SMT with Theorem Proving for Analog/Mixed-Signal
     Circuit Verification. In Klaus Havelund, Gerard Holzmann & Rajeev Joshi, editors: NASA Formal Methods,
     Springer International Publishing, pp. 310–326, doi:10.1007/978-3-319-17524-9_22.
[17] Yan Peng & Mark R. Greenstreet (2018): Smtlink 2.0. Electronic Proceedings in Theoretical Computer
     Science 280, pp. 143–160, doi:10.4204/eptcs.280.11.
[18] Erik Reeber & Warren A. Hunt (2006): A SAT-based decision procedure for the subclass of unrollable list
     formulas in ACL2 (SULFA). In: Proceedings of the Third International Joint Conference on Automated
     Reasoning, IJCAR’06, Springer-Verlag, Berlin, Heidelberg, pp. 453–467, doi:10.1007/11814771_38.
[19] Alexandre Riazanov & Andrei Voronkov (2002):                     The design and implementation
     of VAMPIRE.               AI Communications 15(2-3), pp. 91–110, doi:10.3233/EAI-2002-259.
     arXiv:https://journals.sagepub.com/doi/pdf/10.3233/EAI-2002-259.
[20] Stephan Schulz (2004): System Description: E 0.81. In David Basin & Michaël Rusinowitch, editors: Au-
     tomated Reasoning, Springer Berlin Heidelberg, Berlin, Heidelberg, pp. 223–228, doi:10.1007/978-3-540-
     25984-8_15.
[21] Eric Smith & David L. Dill (2008): Automatic Formal Verification of Block Cipher Implementations. In:
     2008 Formal Methods in Computer-Aided Design, pp. 1–7, doi:10.1109/FMCAD.2008.ECP.10.
[22] Sudarshan Kumar Srinivasan (2007): Efficient Verification of Bit-Level Pipelined Machines Using Refine-
     ment. Ph.D. thesis, Georgia Institute of Technology.
[23] Sol Swords & Jared Davis (2011): Bit-Blasting ACL2 Theorems. In David S. Hardin & Julien Schmaltz,
     editors: Proceedings 10th International Workshop on the ACL2 Theorem Prover and its Applications, ACL2
     2011, Austin, Texas, USA, November 3-4, 2011, EPTCS, pp. 84–102, doi:10.4204/EPTCS.70.7.
[24] Sol Swords & Jared Davis (2015): Fix your types. In Matt Kaufmann & David L. Rager, editors: Proceedings
     13th International Workshop on the ACL2 Theorem Prover and its Applicagtions, ACL2 2015, Austin, Texas,
     USA, October 1-2, 2015, pp. 3–16, doi:10.4204/EPTCS.192.2.
[25] Emina Torlak & Rastislav Bodik (2014): A lightweight symbolic virtual machine for solver-aided host
     languages. In: Proceedings of the 35th ACM SIGPLAN Conference on Programming Language Design
     and Implementation, PLDI ’14, Association for Computing Machinery, New York, NY, USA, pp. 530–541,
     doi:10.1145/2594291.2594340.
[26] Andrew T. Walter & Panagiotis Manolios (2025): An ACL2s Interface to Z3. In Ruben Gamboa & Panagiotis
     Manolios, editors: Proceedings 19th International Workshop on the ACL2 Theorem Prover and Its Appli-
     cations, Austin, TX, 12-13 May, 2025, Electronic Proceedings in Theoretical Computer Science 423, Open
     Publishing Association, pp. 104–123, doi:10.4204/EPTCS.423.10.
</paper>

<requirements>
1. `/work/smtlink.lisp` (and books it includes) implements the `:smtlink` hint as the chain of clause
   processors of Section 5: type inference with `rewrite$` (5.1–5.2), type fixing and judgement selection
   (5.3), term rewriting with a user `:translation-theory` (5.4), extraction of type judgements,
   simplification (5.5), and a final trusted clause processor that writes an SMT-LIB script and runs Z3 (5.6).
   Do not use Python.
2. Only the final clause processor is trusted. The earlier clause processors are verified clause processors
   (`:clause-processor` rules proved against an evaluator), each returning the side goals the paper describes.
3. The final clause processor proves its goal only when Z3 answers `unsat`; `sat`, `unknown` and errors make
   the proof fail. The script uses logic AUFNIRA.
4. `/work/examples.lisp` proves `poly-ineq-example` of Section 5 with the `:smtlink` hint shown, using the
   `rational-+`, `rational-*`, ... encapsulate of Section 5.4, and the same goal with its hypotheses permuted.
5. `/work/examples.lisp` contains a false variant of that goal wrapped in `must-fail`.
6. `/work/examples.lisp` proves the type-terse goal of Section 4.1 and a goal using the `:hypothesize` hint.
7. `/work/examples.lisp` proves the alist-to-array goal of Section 5.7 automatically, with a user translation
   theory containing the two translation theorems the paper names.
8. There is a way to print the SMT-LIB script and the term after rewriting for a goal, and `/work/README.md`
   says how.
9. All books certify with `cert.pl`.
</requirements>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
Books are certified with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
Z3 4.8.12 is installed as `z3`.
Put all your work in /work. Trust tags are allowed only in the book that defines the final, trusted clause processor that calls the SMT
solver, and in books it includes to run shell commands. Do not use skip-proofs, defaxiom, or redefinition.
Do not use the internet. No one will answer questions; work until you are done.
When you are done, run `submit tool-smtlink3`, which saves /work. Then print a short summary: the files you
wrote, and for each numbered requirement whether it is met.
