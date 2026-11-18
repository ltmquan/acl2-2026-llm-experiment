-module(sum_of_nats).
-export([sum_of_nats/1]).

sum_of_nats(0) -> 0;
sum_of_nats(N) when is_integer(N), 0 < N ->
  N + sum_of_nats(N-1).
