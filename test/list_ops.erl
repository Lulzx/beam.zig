-module(list_ops).
-export([main/0]).

main() ->
    erlang:display(sum([1,2,3,4,5])),
    erlang:display(reverse([1,2,3,4,5])).

sum([]) -> 0;
sum([H|T]) -> H + sum(T).

reverse(L) -> reverse(L, []).
reverse([], Acc) -> Acc;
reverse([H|T], Acc) -> reverse(T, [H|Acc]).
