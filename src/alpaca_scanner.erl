%%% -*- mode: erlang;erlang-indent-level: 4;indent-tabs-mode: nil -*-
%%% ex: ft=erlang ts=4 sw=4 et
-module(alpaca_scanner).
-export([scan/1]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

scan(Code) ->
    % Sanitize break tokens with a regular expression
    {ok, Re} = re:compile("\n(\s+)\n", [unicode]),
    Sanitized = re:replace(Code, Re, "\n\n", [{return,list},global]),
    alpaca_scan:string(Sanitized).

-ifdef(TEST).

number_test_() ->
    [
     ?_assertEqual({ok, [{int, 1, 5}], 1}, scan("5")),
     ?_assertEqual({ok, [{float, 1, 3.14}], 1}, scan("3.14")),
     ?_assertEqual({ok, [{float, 1, 102.0}], 1}, scan("102.0"))
    ].

tuple_test_() ->
    EmptyTupleExpected = {ok, [{'(', 1}, {')', 1}], 1},
    [
     ?_assertEqual({ok, [
                         {'(', 1},
                         {int, 1, 1},
                         {')', 1}], 1},
                   scan("(1)")),
     ?_assertEqual(EmptyTupleExpected, scan("()")),
     ?_assertEqual(EmptyTupleExpected, scan("( )")),
     ?_assertEqual({ok, [
                         {'(', 1},
                         {int, 1, 1},
                         {',', 1},
                         {int, 1, 2},
                         {',', 1},
                         {int, 1, 3},
                         {')', 1}], 1},
                   scan("(1, 2, 3)"))
    ].

symbol_test_() ->
    [?_assertEqual({ok, [{symbol, 1, "mySym"}], 1}, scan("mySym")),
     ?_assertEqual({ok, [{symbol, 1, "mySym1"}], 1}, scan("mySym1")),
     ?_assertEqual({ok, [{symbol, 1, "mysym"}], 1}, scan("mysym"))].

atom_test_() ->
    [?_assertEqual({ok, [{atom, 1, "myAtom"}], 1}, scan(":myAtom"))].

let_test() ->
    Code = "let symbol = 5",
    ExpectedTokens = [{'let', 1},
                      {symbol, 1, "symbol"},
                      {assign, 1},
                      {int, 1, 5}],
    ?assertEqual({ok, ExpectedTokens, 1}, scan(Code)).

-endif.
