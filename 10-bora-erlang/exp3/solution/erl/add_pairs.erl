-module(add_pairs).
-export([add_pairs/1, server/1, helper/2]).

add_pairs(NumberList) ->
  WorkerPid = spawn(fun() -> server(none) end),
  Result = helper(WorkerPid, NumberList),
  WorkerPid ! exit,
  Result.

server(Left) -> % a simple reactive process
  receive % receive two numbers and send their sum back to the requester
    X when (Left == none), is_number(X) ->
      server(X);
    {Requester, Right} when is_number(Right) ->
      Requester ! Left + Right,
      server(none);
    exit -> exit
  end.

helper(WorkerPid, [X, Y | Rest]) ->
  WorkerPid ! X,
  WorkerPid ! {self(), Y},
  receive Sum -> [Sum | helper(WorkerPid, Rest)] end;
helper(_, []) -> []. % empty list, nothing to do
