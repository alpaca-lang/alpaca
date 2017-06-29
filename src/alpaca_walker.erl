-module(alpaca_walker).

-export([walk/2, fmt/1]).

-include("alpaca_ast.hrl").

walk([functions | R], #alpaca_module{functions = Fns}) ->
    walk(R, Fns);
walk([N | R], L) when is_list(L), is_integer(N), N > 0 ->
    walk(R, lists:nth(N + 1, L));
walk([binding | R], #alpaca_binding{bound_expr = Expr}) ->
    walk(R, Expr);
walk(['fun' | R], #alpaca_fun{versions = [#alpaca_fun_version{body = Body}]}) ->
    walk(R, Body);
walk([_], Ast) ->
    {ok, Ast};
walk(Path, Ast) ->
    {error, Path, Ast}.


%% {alpaca_apply,undefined,3,
%%                           {'Symbol',#{'__struct__' => record,line => 3,
%%                                       name => <<"add">>,original => 'None'}},
%%                           [{'Symbol',#{'__struct__' => record,line => 3,
%%                                        name => <<"svar_2">>,
%%                                        original => {'Some',<<"x">>}}},
%%                            {'Float',#{'__struct__' => record,line => 3,
%%                                       val => 2.0}}]}
fmt(B) when is_binary(B) ->
    binary_to_list(B);
fmt(I) when is_integer(I) ->
    integer_to_list(I);
fmt(#alpaca_apply{expr = Expression, args = Args}) ->
    [fmt(Expression), $\s | fmt_(Args)];
fmt({'Symbol', S}) ->
    fmt(S);
fmt(#{original := 'None', name := N}) ->
    fmt(N);
fmt(#{original := O}) ->
    fmt(O);
fmt(#{val := V}) ->
    fmt(V);
fmt({'Float', #{val := F}}) ->
    float_to_list(F, [{decimals, 2}]);
fmt({'Some', V}) ->
    fmt(V).


fmt_(L) ->
    string:join([fmt(E) || E <- L], " ").
