-module(fac).
-export([main/0]).

main() ->
    erlang:display(fac(10)).

fac(0) -> 1;
fac(N) -> N * fac(N - 1).
