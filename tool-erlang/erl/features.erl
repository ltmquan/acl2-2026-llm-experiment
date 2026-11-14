-module(features).
-export([all/0, fact/1, classify/1, safe_div/2, adder/1, apply_twice/2, sum/1,
         len/1, bump/1, area/1, tryof/1, thrower/1, catcher/1, pairs/1, maxl/1,
         ping/0, echo/0, counter/1]).
-import(lists, [reverse/1]).

%% Exercises the supported subset: integers, atoms, tuples, lists,
%% binary operators, match, if, case, try/catch, funs and closures, local,
%% remote and fun calls, send and receive.
fact(0) -> 1;
fact(N) when N > 0 -> N * fact(N - 1).

classify(X) ->
    if X < 0 -> negative;
       X =:= 0 -> zero;
       true -> positive
    end.

safe_div(A, B) ->
    try A div B of
        Q -> {ok, Q}
    catch
        error:badarith -> {error, divide_by_zero}
    end.

adder(N) -> fun(X) -> X + N end.

apply_twice(F, X) -> F(F(X)).

sum([]) -> 0;
sum([H | T]) -> H + sum(T).

len(L) -> length(L).

bump({point, X, Y}) -> {point, X + 1, Y + 1}.

area(Shape) ->
    case Shape of
        {square, S} -> S * S;
        {rect, W, H} -> W * H;
        _ -> unknown
    end.

tryof(X) ->
    try thrower(X) of
        V -> {value, V}
    catch
        throw:T -> {thrown, T};
        exit:E -> {exited, E}
    after
        ok
    end.

thrower(0) -> throw(zero);
thrower(1) -> exit(one);
thrower(N) -> N * 10.

catcher(X) -> catch thrower(X).

pairs(L) -> zip(L, reverse(L)).

zip([], []) -> [];
zip([A | As], [B | Bs]) -> [{A, B} | zip(As, Bs)].

maxl([X]) -> X;
maxl([X | Xs]) -> max(X, maxl(Xs)).

%% a process that answers pings
echo() ->
    receive
        {From, Msg} -> From ! {self(), Msg}, echo();
        stop -> stopped
    end.

ping() ->
    E = spawn(fun echo/0),
    E ! {self(), hello},
    R1 = receive {E, M1} -> M1 end,
    E ! {self(), [1, 2, 3]},
    R2 = receive {E, M2} -> M2 end,
    E ! stop,
    {R1, R2}.

%% a closure capturing a pid
counter(N) ->
    Self = self(),
    Pids = spawn_all(lists:seq(1, N), Self),
    collect(length(Pids), 0).

spawn_all([], _) -> [];
spawn_all([I | Is], Self) ->
    [spawn(fun() -> Self ! {done, I * I} end) | spawn_all(Is, Self)].

collect(0, Acc) -> Acc;
collect(K, Acc) -> receive {done, V} -> collect(K - 1, Acc + V) end.

all() ->
    Add5 = adder(5),
    {A, B} = {x, y},
    {fact(10), classify(-3), classify(0), classify(7),
     safe_div(7, 2), safe_div(1, 0),
     apply_twice(Add5, 1), apply_twice(fun(X) -> X * X end, 3),
     sum([1, 2, 3, 4]), len("abc"), bump({point, 1, 2}),
     area({square, 3}), area({rect, 2, 5}), area(circle),
     tryof(0), tryof(1), tryof(2), catcher(0), catcher(5),
     [1, 2] ++ [3], lists:reverse([1, 2, 3]), maxl([3, 9, 2]),
     (1 < 2) andalso (2 < 3), (1 > 2) orelse false,
     element(2, {a, b, c}), A, B, pairs([1, 2]),
     7 rem 3, -7 div 2, 1 == 1, a < b, {1, 2} < {1, 3}, [] < [1]}.
