-module(joe_robert).
-export([start/0, joe/1, robert/0]).

%% Two processes send messages to each other, acknowledge that they have
%% received them, and then exit.
start() ->
    Robert = spawn(fun() -> robert() end),
    Joe = spawn(fun() -> joe(Robert) end),
    {Joe, Robert}.

joe(Robert) ->
    Robert ! {self(), hello_robert},
    receive
        {Robert, ack} -> ok
    end,
    receive
        {Robert, hello_joe} ->
            Robert ! {self(), ack},
            {joe, done}
    end.

robert() ->
    receive
        {Joe, hello_robert} ->
            Joe ! {self(), ack},
            Joe ! {self(), hello_joe},
            receive
                {Joe, ack} -> {robert, done}
            end
    end.
