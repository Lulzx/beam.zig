-module(float_test).
-export([main/0]).

main() ->
    %% Basic float arithmetic
    X = 3.14,
    erlang:display(X),
    Y = X * 2.0,
    erlang:display(Y),
    %% Float division
    Z = 10 / 3,
    erlang:display(Z),
    %% Mixed int/float
    W = X + 1,
    erlang:display(W),
    %% Comparisons
    erlang:display(X > 3.0),
    erlang:display(is_float(X)),
    erlang:display(is_number(X)),
    erlang:display(abs(-5.5)),
    ok.
