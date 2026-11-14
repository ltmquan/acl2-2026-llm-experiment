Build, in ACL2, the system described in the paper below. The authors' implementation is not available;
write your own, following the paper. Where the paper gives names, interfaces, generated events or example
inputs, use them exactly. The requirements after the paper say what will be checked.

<paper>
Erlang in ACL2: A Continuation-Passing Style Evaluator

                               Kuter Bora                               Mark R. Greenstreet
                Max Planck Institute for Security and Privacy         Department of Computer Science
                            Bochum, Germany                          The University of British Columbia
                        kuter.bora@mpi-sp.org                               Vancouver, Canada
                                                                             mrg@cs.ubc.ca



      We present an evaluator in ACL2 for Erlang, a functional language for concurrent programming.
      The evaluator is written in two parts: an AST evaluator and a scheduler. The AST evaluator uses
      continuation-passing style. At each point in an execution, each process has a current continuation
      that holds all state needed for further execution of the process. Thus, the global state of an Erlang
      program is a mapping from Erlang process identiﬁers to their continuations. The scheduler provides a
      non-deterministic interleaving of processes between globally visible actions such as process spawns
      and message sends and receives. We demonstrate the evaluator by proving some properties of a few
      simple Erlang programs.


1    Introduction
“Erlang is a concurrent language consisting of communicating components where the components are
written in a functional language.” [4]. Erlang supports concurrent computing by providing lightweight
processes that communicate through message passing. Erlang has been widely used, especially for
telecommunications applications – see https://erlang-companies.org.
    There are many static analysis tools for Erlang, including Dialyzer [21], a linter; Typer [17], a type
annotation tool; and Wrangler [16], a refactoring tool. The only other theorem proving approach to
veriﬁcation of Erlang programs that we are aware of is the Erlang Veriﬁcation Tool (EVT) [11] which is
a language speciﬁc (i.e. Erlang) proof assistant based on the µ -calculus.
    Using continuations with ACL2 has several motivations. First, continuations provide a uniﬁed ap-
proach for modeling concurrency, communication, and exceptions. Second, ACL2 offers a high degree
of proof automation. These two properties appear to be a good ﬁt for reasoning about Erlang programs.
Erlang is often used for systems with stringent reliability requirements, including fault tolerance. Being
able to formally verify such software can contribute to reliability. Like ACL2, Erlang is an untyped,
functional language – there is a natural semantic match. Finally, Erlang is used in industrial development
environments including dynamic updates to running code. There is a need to be able to quickly re-verify
systems when the code is changed; thus, veriﬁcation is not a once-and-done, but a process that needs to
be included in regression tests, an area where ACL2 excels.
    This paper presents our initial foray into using ACL2 and continuations to reason about Erlang pro-
grams. Our contributions are:
    • An Erlang to ACL2 translator. We use the front-end of the Erlang compiler to generate abstract
      syntax trees that are then output in ACL2 syntax for use by our evaluator.
    • A continuation passing style evaluator for these ASTs.
    • Two examples to demonstrate that our method works end-to-end: showing that a simple, recur-
      sive function for computing the sum of natural numbers up to N returns the same value as the

                                                                                 © K. Bora, M.R. Greenstreet
A. Coglio and S. Srinivasan (Eds.): 20th ACL2 Workshop (ACL2-2026)
                                                                                 This work is licensed under the
EPTCS ??, 2026, pp. 1–15, doi:10.4204/EPTCS.??.??
                                                                                 Creative Commons Attribution License.

2                                                                                         Erlang in ACL2


       closed-form formula; and a parallel implementation of reduce. These examples both show that our
       evaluator works both to run Erlang code and to provide a semantics for reasoning about it. They
       also point to the next steps for this line of research.


2     Background and Related Work
2.1 Erlang
Erlang is a language for concurrent programming using message passing where individual processes are
deﬁned functionally [4]. In other words, it’s a functional language extended with operations for spawning
processes and sending and receiving messages. Erlang makes extensive use of pattern matching. For
example, to compute the sum of the ﬁrst n natural numbers, one can write:
    sum of nats(0) -> 0;
    sum of nats(N) when is integer(N), 0 < N ->
      N + sum of nats(N-1).
Functions are deﬁned as a list of clauses separated by semicolons. Each clause has a pattern for each ar-
gument. In the deﬁnition of sum of nats above, there are two clauses: sum of nats(0) matches when
the value of N is 0; and sum of nats(N) when . . . matches when the value of N is a positive integer. If
sum of nats is called with an argument that is not a natural number, then it throws a function clause
exception.
    The spawn function in Erlang, spawn(F) creates a new process, returns the Erlang pid for the process
to the caller of spawn, and executes F in the child process. F is a function of no arguments – data can
be passed to the child process by lambda capture. When F returns, the return value is discarded and the
child process exits. There are several variants on the spawn call that take additional arguments; see the
Erlang documentation for more details.
Messages are sent with a send expression:
     DestinationPid ! ValueToBeSent.

Receive expressions have the form:
    receive
      Pattern1 -> Expr1;
      Pattern2 -> Expr2;
      ...
    end.
where each expression can use the values of variables bound by the corresponding pattern. Message
delivery is reliable as with TCP-IP. Each process has a message queue. For any two (not necessarily
distinct) pids, pid1 and pid2, Erlang guarantees the messages sent from pid1 to pid2 are enqueued in
pid2’s message queue in the order that they were sent by pid1. When a receive expression is evaluated,
messages in the queue are matched against the patterns of the receive from the oldest message to the
newest. For each message, the patterns are matched from top to bottom. Erlang provides no other
ordering guarantees. If no message matches, a receive blocks until such a message is received. Erlang
provides time-outs to prevent indeﬁnite blocking and priority messages that can be delivered before
regular messages that arrived earlier; we don’t discuss time-outs or priority messages further in this
paper.
    Figure 1 shows a simple example of Erlang processes. First, we will decode the syntax for readers
who are new to Erlang. In Erlang, identiﬁers that start with a capital letter are variables, and those that

K. Bora, M.R. Greenstreet                                                                               3


  add pairs(NumberList) ->
    WorkerPid = spawn(fun() -> server(none) end),
    Result = helper(WorkerPid, NumberList),
    WorkerPid ! exit,
    Result.

  server(Left) -> % a simple reactive process
    receive % receive two numbers and send their sum back to the requester
      X when (Left == none), is number(X) ->
        server(X);
      {Requester, Right} when is number(Right) ->
        Requester ! Left + Right,
        server(none);
      exit -> exit
    end.

  helper(WorkerPid, [X, Y | Rest]) ->
    WorkerPid ! X,
    WorkerPid ! {self(), Y},
    receive Sum -> [Sum | helper(WorkerPid, Rest)] end;
  helper( , []) -> []. % empty list, nothing to do


                               Figure 1: An example of Erlang Processes


start with a lowercase letter are atoms; an Erlang atom is analogous to a Lisp symbol. An expression of
the form
      Pattern = Expression
is a pattern match. If the pattern matches, free variables in Pattern will be bound to the value of the
term in Expression to which they matched. The pattern [X, Y | Rest] matches any list with two or
more elements, binding X and Y to the ﬁrst two elements and Rest to the possibly empty remainder of the
list. If a variable in Pattern is already bound to a value, then the corresponding term in Expression
must have the same value. A comma-separated sequence of expressions is like a Lisp progn. The value
of the list of expressions is the value of the last expression in the sequence. An Erlang tuple can be
written as {A, B, C}; tuples are often used to represent a ﬁxed number of heterogeneous data values.
An Erlang lambda expression is written as
  fun(ArgsPattern1) -> Body1;
     (ArgsPattern2) -> Body2;
     ...
  end
    The function add pairs(NumberList) takes a list (of even length) of numbers, treats it as a list of
pairs, and returns a list of the sums of each pair. For example,
     add pairs([1,2,3,4,5,6,7,8]) -> [3,7,11,15].
The function server implements a reactive process. It waits to receive a request, handles the request,
and unless the request is exit, it makes a recursive call to await the next request. By design, the server
function can handle an arbitrary number of requests without exiting. We can’t prove termination of
server because it may not terminate. We address this in Section 3.3. The server function is tail-
recursive to avoid stack overﬂow; The Erlang compiler is required to perform tail-call elimination.
    Spawn, send, receive, and exit are not applicative. For example, the ordering of operations by dif-

4                                                                                           Erlang in ACL2


    add pairs nd(NumberList) ->
      MyPid = self(),
      List1, List2 = lists:split(length(NumberList) div 2, NumberList),
      WorkerPid = spawn(fun() -> server(none) end),
      spawn(fun() -> MyPid ! helper(WorkerPid, List1) end),
      spawn(fun() -> MyPid ! helper(WorkerPid, List2) end),
      Result = receive Sum1 -> Sum1 end ++ receive Sum2 -> Sum2 end,
      WorkerPid ! exit,
      Result.

                                    Figure 2: Adding pairs in parallel.


ferent processes is non-deterministic, as is the ordering of message delivery for messages from different
processes. Consider Figure 2. We can evaluate
     add pairs nd(lists:seq(1, 1000000)) == add pairs nd(lists:seq(1, 1000000)).
and ﬁnd that it often evaluates to false. This clearly violates referential transparency. This is because
the order in which server receives messages from each of the two processes calling helper is unspec-
iﬁed.
    While Erlang processes are non-applicative, they provide a simple and elegant logical story for ﬁles
and other operating services. To model processes and their related operations in our evaluator, we use
continuations as described below.
For a more complete introduction to Erlang see [10, 15, 6].


2.2 Continuation Passing Style
Continuation Passing Style (CPS) provides a very general method for describing computations, including
concurrent processes, sending and receiving of messages, and exceptions as well as expression evalua-
tion, control ﬂow, and assignments. A continuation is a function that says “what to do next” [3, p. 2].
In a CPS program, each continuation, C, performs a single action to get a new value and calls the next
continuation with that value. A terminal continuation just returns the value with which it was called.
     As an example, Figure 3 shows a CPS version of the sum of nats function. Functions C1 through
C5 are continuations. To see how CPS “works”, consider the execution of sum of nats cps(N) when
N=0, when N is a positive integer, and when N is not a natural number.
     Each continuation is called with the value computed by the previously executed continuation; per-
forms an operation, i.e., it updates Val; and then calls the next continuation. The actual parameter for
each call is either a constant or a single variable, no complicated expressions. This makes control ﬂow
explicit. Furthermore, each continuation has all of the data needed for the rest of the computation. In Fig-
ure 3, results from previous continuations that are needed in the future are part of each function’s closure.
Of course, ACL2 does not support higher-order functions; Section 3.2 describes our implementation.
     Continuations provide a uniﬁed way to model concurrency, communication, and exceptions, as well
as modeling “ordinary” sequential computation. Because a continuation holds all of the information
needed for the rest of the computation, we can represent a collection of concurrently executing processes
as a mapping from each pid to its current continuation. When a process is preempted or blocked, its
current continuation is simply returned to the scheduler. When the process is run again, it just resumes
at that continuation. Exceptions are also simple – if an operation throws an exception, the value that it
passes to the next continuation is tagged as being an exception. A continuation for an exception handler

K. Bora, M.R. Greenstreet                                                                                5


  sum of nats cps(N, C0) ->
    C1 = fun(true) -> C0(0); % N == 0
             (false) -> % N /= 0
               C2 = fun(true) -> % is integer(N) and (0 ¡ N)
                      C3 = fun(Sum N minus 1) ->
                              Val = N + Sum N minus 1,
                              C0(Val)
                           end,
                      Val = N-1,
                      sum of nats cps(Val, C3)
                    end,
               C4 = fun(N is integer) ->
                      C5 = fun(N is pos) ->
                              Val = N is integer and N is pos,
                              C2(Val)
                           end,
                      Val = 0 < N,
                      C5(Val)
                    end,
               Val = is integer(N),
               C4(Val)
          end,
    Val = N == 0,
    C1(Val).

              Figure 3: Sum of the natural numbers up to N in Continuation Passing Style


chooses from a set of possible successors depending on whether or not an exception was encountered,
and if so, whether or not this continuation has a handler that matches the exception. If a continuation
cannot handle an exception, it just passes it to its successor.

2.3 Related Work
The most closely related work that we know of is Turán et al. [24] that derives an interpreter for Core
Erlang [8]. For historical and pragmatic reasons, Erlang has a signiﬁcant amount of syntactic sugar. Core
Erlang is a desugared variant of Erlang to which Erlang code can be readily translated. The goal of Turán
et al. is roughly the dual of what we have done: given an operational semantics for Core Erlang [7], they
automatically generate an interpreter in Haskell; in contrast, we present an evaluator for Erlang which
gives it a semantics for reasoning about Erlang programs in ACL2.
    Using evaluators to deﬁne the semantics of a language is common practice in ACL2, including the
JVM [18], Verilog [23], and the x86 instruction set [12]. In [19], Manolios and Moore present a way to
introduce non-terminating, tail-recursive functions into ACL2 as partial (i.e. constrained) functions. The
functions leave the behaviour of the function unspeciﬁed in the case of non-termination. They then show
how an induction schema can be introduced based on these deﬁnitions. Greve builds on [19] in [13]
and shows a construction to introduce induction schema for tail-recursive functions where the induction
schema follows the structure of the function deﬁnition. Greve uses a continuation-passing style evaluator
to extend this approach to arbitrary recursive functions. [13] does not explore the use of continuations to
model concurrent software, which is the focus of this paper.

6                                                                                           Erlang in ACL2


3    The CPS Evaluator
Our Erlang-to-ACL2 translator uses the components of the Erlang compiler that are provided by the
standard Erlang library, OTP. The scanner, erl scan:string(String), attempts to tokenize a String,
returning a list of tokens if successful. The parsers, parse exprs(Tokens) and parse form(Tokens)
from the erl parse module attempt to parse a list of tokens for a list of Erlang expressions or for
an Erlang term respectively, returning the corresponding ASTs if successful. Forms include module
attributes and function deﬁnitions. In short, expressions are Erlang code that can be evaluated, while
forms deﬁne entities such as functions in the logical world.
For example: parse exprs of "2 + 2." becomes
      [{:op, , ’+’, {:integer, , 2}, {:integer, , 2}}].
     Having parsed Erlang into an AST, we then deﬁne a ﬁxtype in ACL2 that models it. The Erlang and
ACL2 ASTs are almost one-to-one equivalent: for example, the ACL2 equivalent for ”2 + 2.” is (:binop
+ (:integer 2) (:integer 2))). There are two exceptions. First, erl parse represents some lists
(function arguments, tuple elements) as Erlang lists, [ast1, ast2 ...] rather than as parsed Erlang
lists {cons, ast1, {cons, ast2, ...}}. We normalize the ASTs to match the latter case. Second,
erl parse represents all function calls with the call keyword. The type of a call expression can
be determined statically, so, for ease of implementation, we tag each call as a local, remote, or fun
call. Currently, we support Erlang’s primitive types other than maps and ﬂoats; binary operations; match
statements; if, case-of, and try-catch expressions; fun expressions (closures); calls to local and
remote functions and funs; and send and receive expressions. We have partial support for spawn; for
the examples in this paper, we construct the ACL2 representations of Erlang pids as needed in theorem
statements or AST evaluation.
     Deﬁnitions of modules and function deﬁnitions closely follow the Erlang equivalent. In our ACL2
representation, an Erlang module is a defprod containing its attributes and function deﬁnitions. An Er-
lang logical world is deﬁned as a map from module names to modules. The module erl to acl2.erl
provides functionality for parsing Erlang expressions and modules to their ACL2 equivalents. Our cur-
rent implementation of the parser does not support importing or exporting efunctions. Until support is
added, module attributes need to be constructed manually. Functions deﬁned in other modules can be
called as mod:f(X, Y, Z) or can be imported as -import(mod, [f/3]) and called locally.
     The ACL2 evaluator consists of two parts: an AST evaluator that interprets an AST within the context
of a single Erlang process, and a scheduler that interleaves the computations of multiple processes. The
remainder of this section describes this design in more detail.

3.1 Processes, Scheduling, and Traces
A continuation is often deﬁned as a closure that performs the next operation of the program and then
invokes the continuation for the rest of the program; see Figure 3 for an example. Such a representation
uses function-valued variables. To represent this in ACL2, we use lists of continuations. The head of the
continuation list is the next operation to be performed, and the tail of the list is the continuation for the
rest of the program. If the continuation list is empty, then the computation terminates.
    We model the execution of an Erlang program as a trace [9, 20]. A trace is a sequence of states
where each state is a mapping from process identiﬁers to the current continuation list for that process.
As described later in this section, the process state also includes an inbox and outbox for messages and
a logical world. When the scheduler takes an action, it can deliver a pending message to a process,
or it can continue the execution of a process. When a process executes, the evaluator interprets its

K. Bora, M.R. Greenstreet                                                                                 7


continuations until either the process exits or until it performs a receive operation. When the AST
evaluator encounters a receive expression, it returns the current continuation to the scheduler. This
continuation includes per-destination lists of messages that were sent during this execution segment.
There is a separate message-send queue for each destination pid to implement Erlang’s message ordering
guarantees.
    To model non-determinism, we describe the scheduler as a constrained function using an encapsula-
tion. In the present implementation, the only fairness condition that we ensure is that if there is a non-
stuttering action available, the scheduler will choose some non-stuttering action. Theorems about Erlang
programs must hold for all possible schedules that satisfy this very weak condition. Using defattach,
one can provide an executable scheduler for the abstract version described above. This allows our evalu-
ator to be used both to execute Erlang programs and to reason about them.
    We plan to strengthen this to require weakly fair scheduling: if a process is runnable, then it will
eventually be selected to run, or the process will be terminated. Likewise, if a message is pending
delivery, then it will eventually be selected to be delivered, or the destination process will exit. If no
processes fail during execution, then weak-fairness captures Erlang semantics. We note that Erlang
excels for implementing fault-tolerant systems – a process could fail due to hardware or other failures
that are not properties of the code. Stronger fairness guarantees would be needed to reason about recovery
from such failures; That is beyond the scope of the work described in this paper.
    The current spawn is an ACL2 function that needs to be invoked to create all Erlang processes before
evaluation begins – no new processes can be spawned during evaluation. We are currently completing
support for spawn calls during AST evaluation. Spawning a process requires ﬁnding an unused pid to
assign to the new process. This is a globally visible action, because any other process can see that a
new process has come into existence (e.g., with the erlang:processes() built-in function), and could,
for example, send messages to it. Therefore, the Erlang spawn will need to pass control back to the
scheduler, similar to receive.

3.2 The AST evaluator
Within a single process, Erlang is an almost purely functional language. As described in Section 2.1,
referential transparency is trivially violated by message passing. To model execution within a single pro-
cess, we use continuation passing style evaluation of an abstract syntax tree (AST). Figure 3 implements
continuations using closures. Our evaluator constructs a list of these continuations, where each contin-
uation is a tag-sum data structure [2]. Each continuation performs a single primitive Erlang operation,
and then the next continuation in the list is evaluated with the result. For each class of Erlang operations
– e.g. binary operations, unary operations, case expressions, receive expressions, function calls, etc. –
the corresponding product structure (see [1]) has ﬁelds according to the data needed by the operation.
Figure 4 illustrates this by showing a somewhat simpliﬁed evaluation of the AST corresponding to
     (X + Y) * (receive Z -> Z end).
    A few explanatory remarks about the code. The AST to be evaluated comes from the Erlang compiler
front-end as described above. For clarity and succinctness, we write (ast QuotedExpression) to de-
note the AST for QuotedExpression. Likewise, the evaluator has a tag-sum data structure to represent
Erlang data values, but we write, for example, (* C5.left RightValue), as if these values were their
Lisp counterparts, again for clarity and succinctness. The functions cont-expr, cont-binop1, etc. are
continuation constructors for the expr variant, the binop1 variant, etc.
    The continuation list of each process is paired with an estate (Erlang state) which stores aspects of
the program state produced by the previous continuation, including the latest value retrieved by executing

8                                                                                                       Erlang in ACL2


    % Initialize ContTail and C1 for an example of evaluation with continuations.
    ContTail = whatever follows the evaluation of (X + Y) * (receive Z -> Z end).
    C1 = (cont-expr :expr (ast ’((X + Y) * (receive Z -> Z end)))).
    Initial continuation list: (list* C1 ContTail).
    eval cont list((list* C1 ContTail) EState) → ; C1.tag = ’expr
      (let ((C2 (cont-expr :expr (ast ’(X + Y))))
            (C3 (cont-binop1 :op ’*
                              :right expr (ast ’(receive Z -> Z end))
            (NewState (update-estate->val EState ’none)))
        eval cont list((list* C2 C3 ContTail) NewState))).
    eval cont list((list* C2 C3 ContTail) EState) → ; C2.tag = ’expr
      ; Evaluating C2 may produce a value directly, or it may prepend additional continuations
      ; to (list* ContTail) and continue execution from there. Eventually (assuming the evaluator
      ; does not run out of fuel), we will reach a state where the pending continuation list is (list* C3 ContTail)
      ; and the val ﬁeld of NewState is the value from evaluating (ast ’(X + Y)). We skip the
      ; details and continue after the evaluation of C2 and its children is complete.
      (let ((NewState (as described in the comments above)))
              eval cont list((list* C3 ContTail) NewState).
    eval cont list((list* C3 ContTail) EState) → ; C3.tag = ’binop1
      (let ((C4 (cont-expr :expr (ast ’(receive Z -> Z end))))
            (C5 (cont-binop2 :op ’*
                              :left (estate->val EState)))
            (NewState (update-estate->val EState ’none)))
        eval cont list((list* C4 C5 ContTail) NewState)).
    eval cont list((list* C4 C5 ContTail) EState) → ; C4.tag = ’expr
      (let ((C6 (cont-receive :clauses (list (ast ’(Z -> Z)))))
            (NewState (update-estate->val EState ’none)))
            eval cont list((list* C6 C5 ContTail) NewState)).
    eval cont list((list* C6 C5 ContTail) EState) → ; C6.tag = ’receive
      (let ((RecState
                 (update-estate->val EState
                      (’receive :klst (list* C5 ContTail)
                            :clauses C6.clauses)))
            ; yield to the scheduler by returning the continuation list, wrapped inside the state
            RecState).
    ; when the scheduler runs this process again, it makes the following call to eval cont list.
    eval cont list((list* C7 C5 ContTail) EState) ->; C7.tag = ’receive2
      if there is a message in inbox matching Z
             Dequeue the matching message binding the val ﬁeld of NewState to the value of that message.
             eval cont list((list* C5 ContTail) NewState)
      else
             EState ; No matching message. Yield to the scheduler again.
      end.
    eval cont list((list* C5 ContTail) Estate) → ; C5.tag = ’binop2
      (let ((ExprVal (case-match C5.op
                        (’* (* C5.left (estate->val EState)))
                        . . . )))
      eval cont list(ContTail (update-estate->val EState ExprVal)).

                           Figure 4: Evaluating (X + Y) * (receive Z -> Z end)

K. Bora, M.R. Greenstreet                                                                                  9


an expression, current bindings of variable names to values, module and logical world, as well as the
outbox to be handed off to the scheduler. The inbox of a process is maintained by the scheduler rather
than the evaluator. The logical world is a map from names to modules, where a module is a defprod
containing the attributes and a map from function names to their Lisp AST clauses.
    To evaluate a binary operation such as the multiplication in (X + Y) * (receive Z -> Z end),
the evaluator creates two continuations. The ﬁrst, C2 in Figure 4, is a continuation to evaluate X + Y.
The second, C3, is a binop1 continuation that has ﬁelds for the operation to be performed and the AST
for the right operand. Evaluation of a binop1 continuation receives the value for the left operand from
the previous continuation (i.e. C2) and constructs two more continuations C4 and C5. Continuation C4
evaluates the right operand. Evaluation of C5 receives the value for the right operand. The operator and
the value for the left operand are stored in the op and left ﬁelds respectively of C5. C5 performs the
operation and provides the result to the next continuation.
    The receive expression shows how the AST evaluator interacts with the scheduler. When the
receive is ﬁrst encountered, (C6 in the example), the evaluator wraps the remaining continuations along
with the current estate in RecState and yields to the scheduler.
    All process state is contained in RecState. The val ﬁeld holds the value generated by the previous
continuation, which could possibly be none. When the scheduler runs this process again, it simply
calls eval cont list on the continuation list for the process obtained from RecState. This starts by
checking to see if there is a suitable message in the process’s inbox. If so, the value from that message is
provided to the next continuation in the list. Otherwise, the process yields to the scheduler again to wait
for new messages to arrive.


3.3 Fuel
For our evaluator to be admissible in ACL2, we must show that it always terminates. We give up imme-
diately. The most common use-case for Erlang is to implement reactive processes. In the simplest form,
the process waits to receive a request, processes the request, and then calls itself to be ready for the next
request. By design, such a process never terminates. Thus, attempts to prove termination are doomed to
failure.
    Instead of proving termination, the continuation structure includes a fuel ﬁeld, where (natp fuel).
The evaluator decrements fuel for each new continuation, and exits with an out-of-fuel status if (zp
fuel). In Section 4 we show how we can prove interesting properties of programs by showing that there
is an amount of fuel that is sufﬁcient to complete speciﬁc tasks.


4    Examples
We show two examples of proving properties of Erlang programs using our evaluator.
                                                               2
    1. Show that the sum of the natural numbers up to N is N 2+N .

    2. Show that Schwartz’s parallel algorithm for reduce [22] computes the sum of the values contributed
       by each worker process.

The code for the Erlang front-end, our evaluator, and the examples in this section is on Github at
    [removed]

10                                                                                           Erlang in ACL2


4.1 sum of nats
We show that for the Erlang function sum of nats(N), if N is a natural number then

                                  sum of nats(N) = 12 N2 + N
                                                                  
                                                                                                          (1)

     The code is in the book Erlang-in-ACL2/books/erl-arithmetic/sum of nats.lisp.
     The preconditions of the theorem are that N must be an Erlang AST of type :integer, and that the
process’s logical world must contain the entry for sum of nats. Additionally, there must be enough fuel
for the evaluation to terminate.
     Our proof strategy is to introduce the corresponding function, sum-of-nats in Lisp, and prove that
if N is the Erlang representation of a natural number, then:
     sum of nats(N) =
       (make-erl-val-integer :val (sum-of-nats (erl-val-integer->val N)))
In other words, the result of applying sum of nats to N is the same as converting N from our represen-
tation of an Erlang integer to a Lisp integer, applying sum-of-nats to that integer, and converting the
result back to an Erlang integer. Then, we can simply use the existing arithmetic books to prove the
theorem for the Lisp sum-of-nats. The key functions and lemmas are:
 sum-of-nats: the sum of nats function in ACL2 lisp.
 sum-test-world-p: predicate for a logical world that has a mapping for the sum of nats function
     in the local module. It makes no other claims about the world, i.e., there could be other function
     deﬁnitions.
 eval-sum-of-nats-induct: does a beta-reduction of sum of nats(N) for the case when N is a
     positive integer.
 eval-sum-of-nats-base-case: The base case of the above induction, when N=0.
 eval-sum-of-nats-inductive-case: The inductive step of the above induction, when N is greater
     than zero. This is the more difﬁcult part of the proof, where evaluation needs to be stepped up to
     next recursive call with speciﬁc rewrite rules.
Now, we have enough machinery to prove that if the evaluation of sum of nats(N) has enough fuel,
then it returns
     (make-erl-val-integer :val (sum-of-nats (erl-val-integer->val N)))
Furthermore, we show that if the fuel for the initial continuation is at least 8 ∗ (1 + N), then the evaluator
will not run out of fuel. From here, it is simple to show that sum-of-nats(N) matches the closed form
formula and therefore, with sufﬁcient fuel for the evaluator, sum of nats(N) does as well.
    While there were many lemmas in the proof, most were straightforward. We expect that the lem-
mas that“translate” Erlang expressions into Lisp equivalents could be automated. The main challenge
here is that this translation requires the hypothesis that the evaluation does not encounter an exception
or out-of-fuel condition, i.e., the result is well-formed. This is a reasonable hypothesis, as we expect
that veriﬁcation of Erlang code will often be separated into arguments about the well-formed case and
arguments about error handling. When trying to automate the well-formed case, we needed a reasoning
that showed that if the result was well-formed, then so was the value of each sub-expression – until a
try-catch expression, though there were no exception handlers in this example. The difﬁculty was that
      • When rewriting a term, a rewrite rule can’t introduce new hypotheses about formulas produced by
        the rewrite rule, i.e., assertions about the sub-terms.

K. Bora, M.R. Greenstreet                                                                               11


    • We might hope to establish the hypotheses for rewriting the sub-terms by back-chaining, but this
      runs into a :match-free problem – what term is my parent?
    • Forward chaining works, but for only one level of the AST. As :doc forward-chaining ex-
      plains:
           “Heuristic approval of each new addition is necessary to avoid inﬁnite looping. . . ”
      and these heuristics block forward-chaining from propagating the well-formed hypothesis to all
      the nodes of the AST.
One “solution” to these problems was simply to enable a large number of rewrite rules about ASTs. This
turned out to be impractical due to the many variants for each of the tag-sum types representing Erlang
ASTs and values. The rewriter can generate extremely large numbers of cases and grind to a halt. We
have tried some experiments using extended meta-functions with a simpliﬁed version of the evaluator.
The results look very promising. We need to try this with the full evaluator.
    The measure function for sum of nats, i.e. 8 ∗ (1 + N) was manually derived. We believe that this
could be automated in many cases.
    Introducing the Lisp version of sum of nats simpliﬁed reasoning tremendously. We need to exam-
ine more examples to ﬁnd out if we should generate these functions automatically, or if the need for such
functions can be eliminated or greatly reduced if we provide customized simpliﬁers for continuations
and continuation lists.

4.2 Reduce
We implemented Schwartz’s parallel algorithm for reduce [22] to compute the sum of values provided
by workers each calling their local reduce function. The algorithm organizes the processes as a tree, and
the grand-total is produced at the top of the tree. In Schwartz’s approach, this value should be propagated
back to each worker so that their call to reduce returns the grand total. The reduce we use in the proofs
is a constrained and simpliﬁed version of Schwartz’s algorithm. It does not propagate values back to each
worker. This example is very much a demonstration that we can reason with processes. It also shows
that there are many opportunities for improvement.
  reduce(none, [], GrandTotal) -> GrandTotal;
  reduce(ParentPid, [], MyTotal) ->
      ParentPid ! {self(), MyTotal};
  reduce(ParentPid, [ChildHd | ChildTl], LeftTotal) ->
      receive
          {ChildHd, RightTotal} ->
              reduce(ParentPid, ChildTl, LeftTotal + RightTotal)
      end.

                                     Figure 5: The simpliﬁed reduce

     We ﬁrst deﬁne functions wtree-p and create-wtree, a recognizer and a constructor for processes
that make up a reduce ”worker tree” consisting of n nodes. Each node has a list of the pids for branches
connected to subtrees that communicate with that node. They are ordered from the closest (and smallest
indexed) such subtree to the furthest (and largest indexed). Each worker must have a unique index; a
natural number from 0 to n-1 in left-to-right order of the tree leaves. At this point in development, each
worker calls the reduce function with its index, so the master process will receive the sum of all indices,
as if it had called sum of nats(n-1).

12                                                                                           Erlang in ACL2




                                           Figure 6: Worker Tree


    To show that the grand-total is produced at the root node, we use an invariant; see
     Erlang-in-ACL2/books/reduce-v2/proofs/inv.lisp.
In the current implementation, each process terminates when it sends a value to its parent. The invariant
states that the value held by the process when it reaches termination is the sum of the values at the leaves
of the subtree for which the process is the root. This implies that the value of the root of the tree, the
process whose index is 0, upon termination, is the sum of the values with which each process called
reduce.
     We have proven that if a worker tree satisﬁes the invariant, then the invariant still holds after deliver-
ing a message or running a process. We have also shown that if the invariant is satisﬁed and if there are
no more non-stuttering actions left for the scheduler to take, then no process in the worker tree is blocked
(i.e., no deadlocks). Using these facts, we proved that if the root process terminates, it will contain the
sum of all indices. Currently, there is no guarantee that the reduce algorithm will terminate, though such
a proof should be possible for this implementation using the fairness condition of our scheduler. This
proof also assumes that every worker has already been spawned by the time reduce is called, which is
not always the case in practice.
     The proof of reduce shows that we can reason about parallel computations using our continuation-
passing-style evaluator. The issues with needing to guide the ACL2 rewriter carefully that we described
for the sum of nats example also apply here. We believe that this can be largely automated and greatly
simpliﬁed, but that remains as future work.




4.3 The Evaluator is Executable

While the scheduler is abstract, it has an executable counterpart. The executable scheduler goes through
the existing processes in order until it ﬁnds a runnable process or a pending message in an outbox. This
makes it possible to run and test the concurrent Erlang evaluation in ACL2. A very simple example of
message passing is presented in Erlang-in-ACL2/scheduler/examples/Joe-Robert.lisp. In this example,
two processes send messages to each other, acknowledge that they have received them, and then exit. A
more complete reduce implementation, which sends the grand total back to every worker, is presented in
Erlang-in-ACL2/scheduler/examples/reduce-v2.lisp. This implementation uses Erlang’s fun expressions
(closures) instead of the inlined +, allowing the user to provide an arbitrary combine function.
    As the executable scheduler runs, it prints the actions taken. When complete (or out of fuel), the
scheduler returns the updated list of processes. This can be very verbose. For testing purposes, it is
better to retrieve only the exit values of each process. Helper functions for this are included in the ﬁles.

K. Bora, M.R. Greenstreet                                                                                13


5    Conclusions and Future Work

We have presented a continuation-passing style evaluator for Erlang in ACL2. Continuations are a natural
choice for Erlang because they handle concurrency, communication, exceptions, and simple, ordinary
sequential evaluation in a uniﬁed way. ACL2 is a natural choice for reasoning about Erlang because many
Erlang applications have stringent reliability requirements, while dynamic updates mean the code can
change after deployment. A formal veriﬁcation tool for Erlang must be suitable for running regression
tests in a timely manner. This is an area where ACL2 excels.
     We demonstrated our evaluator by proving properties of two programs. The ﬁrst was a simple, re-
cursive function to compute the sum of the natural numbers up to N. We showed that the Erlang function
computed the same value (up to mappings between data representations) as a native ACL2 implemen-
tation. From that, we showed that the value returned by the Erlang function matched a closed-form
expression for the sum. The second example was a parallel reduce. We used an invariant to show that it
correctly computed the sum of the values provided by each worker process.



Future Work

In this paper, we have shown an evaluator for a large subset of Erlang. Proofs are possible in this
framework, and there is substantial room for improvement. For segments of code where exceptions and
process preemption do not occur, reasoning is simpler when the continuation-passing style is rewritten
into more familiar Lisp expressions. We noted technical reasons that prevent these transformations from
being performed automatically by the ACL2 waterfall. We are exploring the use of meta-functions and/or
clause processors to automate these transformations.
    Presently, reasoning about evaluations of Erlang programs requires calling the evaluator with sufﬁ-
cient fuel. Manolios and Moore [19] present a way to use defchoose to obtain such an amount of fuel
for a tail-recursive function when the function terminates. It seems likely that a similar approach could be
used here. A key difference is that when using recursive functions to implement reactive processes, the
intention is that the function never terminates. Instead, we want to reason about relationships between
successive recursive calls. This remains a topic for future research.
    Our current scheduler only provides extremely weak fairness conditions. A weakly-fair scheduler
would match the guarantees of the Erlang runtime and would allow us to reason about more realistic
reactive programs. Further work could explore Erlang’s support for fault-tolerant computing.
    Most software veriﬁcation tools focus on sequential programs. Concurrent programs are notorious
for their Heisenbugs – just thinking about possible execution interleavings is rarely sufﬁcient. Erlang is
a functional language designed for implementing robust, concurrent software. We expect that further de-
velopment of veriﬁcation frameworks, such as our work with ACL2, will enable more practical methods
for developing robust, concurrent software.



Acknowledgements

We are grateful for the excellent feedback from the anonymous reviewers. Pointing us to [19, 13, 14]
was especially helpful. Thanks for the hint!

14                                                                                          Erlang in ACL2


References
 [1] ACL2 Foundation (2025): XDOC — Defprod.           Available at https://acl2.org/doc/index.html?
     topic=FTY____DEFPROD.
 [2] ACL2 Foundation (2025): XDOC — Deftagsum. Available at https://acl2.org/doc/index.html?
     topic=FTY____DEFTAGSUM.
 [3] Andrew W Appel (2007): Compiling with continuations. Cambridge University Press, doi:10.1017/
     CBO9780511609619.
 [4] Joe Armstrong (2007): A history of Erlang. In: Proceedings of the third ACM SIGPLAN conference on
     History of programming languages, pp. 6–1–6–26, doi:10.1145/1238844.1238850.
 [5] Joe Armstrong (2010): Erlang. Communications of the ACM 53(9), pp. 68–75, doi:10.1145/1810891.
     1810910.
 [6] Joe Armstrong (2013): Programming Erlang: Software for a Concurrent World. Pragmatic Bookshelf.
 [7] Péter Bereczky, Dániel Horpácsi & Simon Thompson (2023): A frame stack semantics for sequential Core
     Erlang. In: Proceedings of the 35th Symposium on Implementation and Application of Functional Lan-
     guages, pp. 1–13, doi:10.1145/3652561.3652566.
 [8] Richard Carlsson (2001): An Introduction to Core Erlang. Colloquium on Principles, Logics, and Implemen-
     tation of high-level programming languages. Available at https://erlang.org/workshop/carlsson.
     ps.
 [9] David L. Dill (1988): Trace Theory for Automatic Hierarchical Veriﬁcation of Speed-Independent Circuits.
     Ph.D. thesis, School of Computer Science, Carnegie Mellon University, doi:10.7551/mitpress/6874.
     001.0001. Published in book form as part of the ACM Doctoral Dissertation Award Series by the MIT
     Press, Cambridge, MA, 1989.
[10] erlang.org: Erlang Quick Start. web page. Available at https://www2.erlang.org/documentation/
     doc-8.0/doc/getting_started/intro.html.
[11] Lars-Åke Fredlund, Dilian Gurov, Thomas Noll, Mads Dam, Thomas Arts & Gennady Chugunov (2003):
     A veriﬁcation tool for Erlang. International Journal on Software Tools for Technology Transfer 4(4), pp.
     405–420, doi:10.1007/s100090100071.
[12] Shilpi Goel, Warren A Hunt Jr & Matt Kaufmann (2017): Engineering a formal, executable x86 ISA
     simulator for software veriﬁcation. In: Provably Correct Systems, Springer, pp. 173–209, doi:10.1007/
     978-3-319-48628-4_8.
[13] David Greve (2009): Assuming termination. In: Proceedings of the Eighth International Workshop on the
     ACL2 Theorem Prover and its Applications, pp. 114–122, doi:10.1145/1637837.1637856.
[14] David Greve & Konrad Slind (2013): A step-indexing approach to partial functions. In: Proceedings of the
     Tenth International Workshop on the ACL2 Theorem Prover and its Applications, pp. 42–53, doi:10.4204/
     EPTCS.114.4.
[15] Fred Hébert (2013): Learn You Some Erlang for Great Good!: a Beginner’s Guide. No Starch Press. Avail-
     able at https://learnyousomeerlang.com.
[16] Huiqing Li, Simon Thompson, György Orosz & Melinda Tóth (2008): Refactoring with Wrangler, updated:
     Data and process refactorings, and integration with Eclipse. In: Proceedings of the 7th ACM SIGPLAN
     Workshop on Erlang, pp. 61–72, doi:10.1145/1411273.1411283.
[17] Tobias Lindahl & Konstantinos Sagonas (2005): Typer: a type annotator of Erlang code. In: Proceedings of
     the 2005 ACM SIGPLAN workshop on Erlang, pp. 17–25, doi:10.1145/1088361.1088366.
[18] Hanbing Liu & J. Strother Moore (2004): Java Program Veriﬁcation via a JVM Deep Embedding in ACL2. In
     Konrad Slind, Annette Bunker & Ganesh Gopalakrishnan, editors: Theorem Proving in Higher Order Logics,
     Springer Berlin Heidelberg, Berlin, Heidelberg, pp. 184–200, doi:10.1007/978-3-540-30142-4_14.

K. Bora, M.R. Greenstreet                                                                                 15


[19] Panagiotis Manolios & J Strother Moore (2003): Partial functions in ACL2. Journal of Automated Reasoning
     31(2), pp. 107–127, doi:10.1023/B:JARS.0000009505.07087.34.
[20] Y. Peng & M.R. Greenstreet (2019): Verifying Timed, Asynchronous Circuits using ACL2. In: Proceedings
     of the 25th International Symposium on Asynchronous Circuits and Systems, IEEE Computer Society, pp.
     96–104, doi:10.1109/ASYNC.2019.00021.
[21] Konstantinos Sagonas (2005): Experience from developing the Dialyzer: A static analysis tool detecting
     defects in Erlang applications. In: Proceedings of the ACM SIGPLAN Workshop on the Evaluation of
     Software Defect Detection Tools, pp. 1–5.
[22] Jacob T Schwartz (1980): Ultracomputers. ACM Transactions on Programming Languages and Systems
     (TOPLAS) 2(4), pp. 484–521, doi:10.1145/357114.357116.
[23] A. Slobodova, J. Davis, S. Swords & W.A. Hunt, Jr. (2011): A ﬂexible formal veriﬁcation framework
     for industrial scale validation. In: Formal Methods and Models for Codesign (MEMOCODE), 2011 9th
     IEEE/ACM International Conference on, pp. 89–97, doi:10.1109/MEMCOD.2011.5970515.
[24] Gergő Lajos Turán, Arsenii Fomin, Péter Bereczky, Dániel Horpácsi & Simon Thompson (2025): Deriving
     an Erlang interpreter from a mechanised formal semantics of Core Erlang. In: Proceedings of the 24th ACM
     SIGPLAN International Workshop on Erlang, pp. 26–39, doi:10.1145/3759161.3763046.
</paper>

<requirements>
1. A front end turns Erlang source into the ACL2 AST of Section 3 (with `erl_scan`/`erl_parse` or your own
   parser for the subset): `2 + 2.` becomes `(:binop + (:integer 2) (:integer 2))` or an FTY value of that
   shape. The subset covers integers, atoms, tuples, lists, binary operators, match, `if`, `case`,
   `try`/`catch`, funs and closures, local, remote and fun calls, send and receive. `/work/README.md` gives
   the exact command that turns a `.erl` file into ACL2 forms, and the ACL2 form that runs a function of a
   loaded module on given arguments with given fuel, under the executable scheduler.
2. The CPS evaluator `eval-cont-list` of Sections 3.2–3.3 is admitted in logic mode with a natural-number fuel
   argument; running out of fuel returns an out-of-fuel status. On `receive` it yields to the scheduler.
3. The scheduler is an `encapsulate` whose exported constraint is the fairness condition of Section 3.1, with
   an executable version attached by `defattach`.
4. `/work/examples.lisp` runs `add_pairs([1,2,3,4,5,6,7,8])` (Figure 1) to `[3,7,11,15]`, the two-process
   exchange of Section 4.3 to completion with both exit values, and the reduce of Section 4.3 on a small tree,
   with `assert-event`.
5. `/work/sum-of-nats.lisp` proves the theorem of Section 4.1 (equation 1) for `sum_of_nats`, named
   `sum-of-nats-correct`, with your own explicit fuel bound linear in N, and `(equal (sum-of-nats n) (/ (+ (*
   n n) n) 2))` for natural n.
6. `/work/reduce.lisp` proves the three reduce properties of Section 4.2 for every scheduler satisfying the
   constraint, named `reduce-invariant-preserved`, `reduce-no-blocked-worker` and `reduce-root-value`: the
   invariant is preserved by message delivery and by running a process, invariant plus no non-stuttering
   action implies no blocked worker, and if the root (index 0) terminates its value is the sum of the indices.
7. All books certify with `cert.pl`.
</requirements>

ACL2 8.7 (`acl2`) and ACL2(r) 8.7 (`acl2r`) are installed, with the community books.
Books are certified with `cert.pl` (add `--acl2 acl2r` for ACL2(r)).
Erlang/OTP 25 is installed (`erl`, `erlc`, with `erl_scan` and `erl_parse`).
Put all your work in /work. Do not use skip-proofs, defaxiom, trust tags, or redefinition. Do not use the internet. No one will answer
questions; work until you are done.
When you are done, run `submit tool-erlang`, which saves /work. Then print a short summary: the files you
wrote, and for each numbered requirement whether it is met.
