-module(fib).
-export([main/0]).

main() ->
    erlang:display(fib(20)).

fib(0) -> 0;
fib(1) -> 1;
fib(N) -> fib(N - 1) + fib(N - 2).
