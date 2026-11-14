-module(reduce_v2).
-export([run/1, start/2, worker/4, reduce/5, tree/3]).

%% Schwartz's parallel reduce [22], with the grand total sent back to every
%% worker.  Combine is a fun of two arguments (a closure), not an inlined +.
%% start(N, Combine) spawns N workers organized as a tree; worker I
%% contributes the value I.  Returns the list of the totals seen by the workers.
run(N) -> start(N, fun(A, B) -> A + B end).

start(N, Combine) ->
    Master = self(),
    Pids = spawn_workers(N, Master, Combine),
    tree(Pids, Master, none),
    collect(Pids).

spawn_workers(0, _, _) -> [];
spawn_workers(N, Master, Combine) ->
    Rest = spawn_workers(N - 1, Master, Combine),
    Me = N - 1,
    Pid = spawn(fun() -> worker(Master, Me, Combine, none) end),
    Rest ++ [Pid].

%% Send each worker its parent and its children (a binomial-style tree:
%% the children of the node covering Pids are the roots of the halves).
tree([], _, _) -> ok;
tree([Pid | Rest], Master, Parent) ->
    Children = split(Rest),
    Pid ! {Master, tree, Parent, heads(Children)},
    tree_children(Children, Master, Pid).

heads([]) -> [];
heads([C | Cs]) -> [hd(C) | heads(Cs)].

tree_children([], _, _) -> ok;
tree_children([C | Cs], Master, Parent) ->
    tree(C, Master, Parent),
    tree_children(Cs, Master, Parent).

%% split a list into consecutive chunks of sizes 1, 2, 4, ... (last may be short)
split(L) -> split(L, 1).
split([], _) -> [];
split(L, K) ->
    case length(L) =< K of
        true -> [L];
        false ->
            {A, B} = lists:split(K, L),
            [A | split(B, 2 * K)]
    end.

worker(Master, Me, Combine, _) ->
    receive
        {Master, tree, Parent, Children} ->
            Total = reduce(Parent, Children, Me, Combine, Children),
            Master ! {self(), result, Total}
    end.

%% reduce(Parent, ChildrenToWaitFor, Acc, Combine, AllChildren)
reduce(Parent, [C | Cs], Acc, Combine, All) ->
    receive
        {C, up, V} -> reduce(Parent, Cs, Combine(Acc, V), Combine, All)
    end;
reduce(none, [], Acc, _, All) ->
    broadcast(All, Acc),
    Acc;
reduce(Parent, [], Acc, _, All) ->
    Parent ! {self(), up, Acc},
    receive
        {Parent, down, Grand} ->
            broadcast(All, Grand),
            Grand
    end.

broadcast([], _) -> ok;
broadcast([C | Cs], V) ->
    C ! {self(), down, V},
    broadcast(Cs, V).

collect([]) -> [];
collect([P | Ps]) ->
    receive {P, result, T} -> [T | collect(Ps)] end.
