-module(map_test).
-export([main/0]).

main() ->
    M1 = #{a => 1, b => 2, c => 3},
    erlang:display(M1),
    erlang:display(map_size(M1)),
    %% Update existing key
    M2 = M1#{a => 10},
    erlang:display(maps:get(a, M2)),
    %% Pattern match
    #{b := B} = M1,
    erlang:display(B),
    %% maps functions
    erlang:display(maps:keys(M1)),
    erlang:display(maps:values(M1)),
    erlang:display(maps:is_key(a, M1)),
    erlang:display(maps:is_key(z, M1)),
    erlang:display(is_map(M1)),
    ok.
