-module(hello).
-export([main/0]).

main() ->
    erlang:display(hello),
    erlang:display(42),
    erlang:display({ok, [1,2,3]}).
