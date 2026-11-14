-module(reduce).
-export([reduce/3]).

%% The simplified reduce of Figure 5.
reduce(none, [], GrandTotal) -> GrandTotal;
reduce(ParentPid, [], MyTotal) ->
    ParentPid ! {self(), MyTotal};
reduce(ParentPid, [ChildHd | ChildTl], LeftTotal) ->
    receive
        {ChildHd, RightTotal} ->
            reduce(ParentPid, ChildTl, LeftTotal + RightTotal)
    end.
