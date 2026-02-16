-module(binary_test).
-export([main/0]).

main() ->
    B = <<"hello">>,
    erlang:display(B),
    erlang:display(byte_size(B)),
    erlang:display(is_binary(B)),
    B2 = integer_to_binary(42),
    erlang:display(B2),
    B3 = atom_to_binary(world),
    erlang:display(B3),
    ok.
