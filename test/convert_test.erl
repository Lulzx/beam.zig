-module(convert_test).
-export([main/0]).

main() ->
    %% atom_to_list / list_to_atom
    L = atom_to_list(hello),
    erlang:display(L),
    A = list_to_atom("world"),
    erlang:display(A),
    %% integer_to_list / list_to_integer
    IL = integer_to_list(12345),
    erlang:display(IL),
    I = list_to_integer("678"),
    erlang:display(I),
    %% tuple/list conversion
    T = list_to_tuple([a, b, c]),
    erlang:display(T),
    TL = tuple_to_list({1, 2, 3}),
    erlang:display(TL),
    %% min/max
    erlang:display(max(3, 7)),
    erlang:display(min(3, 7)),
    %% list ops
    L2 = [1,2,3] ++ [4,5],
    erlang:display(L2),
    L3 = [1,2,3,2,1] -- [2,1],
    erlang:display(L3),
    %% lists:reverse
    erlang:display(lists:reverse([1,2,3])),
    %% lists:member
    erlang:display(lists:member(2, [1,2,3])),
    erlang:display(lists:member(5, [1,2,3])),
    ok.
