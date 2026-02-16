-module(spawn_test).
-export([main/0, worker/1]).

main() ->
    Pid = spawn(spawn_test, worker, [hello]),
    Pid ! {greeting, world},
    erlang:display(done).

worker(Name) ->
    receive
        {greeting, Msg} ->
            erlang:display({Name, Msg})
    end.
