%% Grader test input for R1 (not from the paper): one function per construct the requirement lists.
-module(subset).
-export([integers/0, atoms/0, tuples/0, lists/1, binops/2, match/1, iff/1, cases/1, tries/1,
         funs/1, calls/1, sendrecv/1]).

integers() -> 42.
atoms() -> hello.
tuples() -> {1, two, {3}}.
lists(L) -> [0, 1 | L].
binops(X, Y) -> (X + Y) * (X - Y) div 2.
match(T) -> {A, B} = T, A + B.
iff(X) -> if X > 0 -> pos; X < 0 -> neg; true -> zero end.
cases(X) -> case X of {ok, V} -> V; [H | _] -> H; _ -> none end.
tries(X) -> try 10 div X catch error:badarith -> infinity; throw:T -> T end.
funs(N) -> F = fun(Y) -> Y + N end, F(1).
calls(X) -> {integers(), lists:reverse([X, 2]), (fun(Z) -> Z end)(X)}.
sendrecv(Pid) -> Pid ! {self(), ping}, receive {_, pong} -> ok; Other -> Other end.
