%% Figure 5 of the paper (bora-erlang). Only -module/-export added.
-module(reduce).
-export([reduce/3]).

reduce(none, [], GrandTotal) -> GrandTotal;
reduce(ParentPid, [], MyTotal) ->
    ParentPid ! {self(), MyTotal};
reduce(ParentPid, [ChildHd | ChildTl], LeftTotal) ->
    receive
        {ChildHd, RightTotal} ->
            reduce(ParentPid, ChildTl, LeftTotal + RightTotal)
    end.
