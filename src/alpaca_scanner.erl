%%% -*- mode: erlang;erlang-indent-level: 4;indent-tabs-mode: nil -*-
%%% ex: ft=erlang ts=4 sw=4 et
-module(alpaca_scanner).
-export([scan/1]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

scan(Code) ->    
    %% Scan and infer break tokens if not provided
    case alpaca_scan:string(Code) of
        {ok, Tokens, Num} -> {ok, infer_breaks(Tokens), Num};    
        Error -> Error
    end.

infer_breaks(Tokens) ->
    %% Reduce tokens from the right, inserting a break (i.e. ';;') before
    %% top level constructs including let, type, exports, imports and module.
    %% To avoid inserting breaks in let... in... we track the level of these
    %% (as we're folding right, an 'in' increases the level by one, a 'let'
    %% decreases by one if the current level > 0)
    
    Reducer = fun(Token, {Level, Acc}) -> 
                    %% TODO use line number from Token
                    InferBreak = fun() -> {0, [{break, 0} | [ Token | Acc]]} end,
                    case {Token, Level} of
                        {{'in', _}, _} -> {Level + 1, [Token | Acc]};
                        {{'let', _}, 0} -> InferBreak();
                        {{'let', _}, _} -> {Level - 1, [Token | Acc]};
                        {{'type_declare', _}, _} -> InferBreak();
                        {{'module', _}, _} -> InferBreak();
                        {{'export', _}, _} -> InferBreak();
                        {{'export_type', _}, _} -> InferBreak();
                        {{'import_type', _}, _} -> InferBreak();
                        %% TODO - imports and exports
                        _ -> {Level, [Token | Acc]}
                    end      
              end,
    {0, Output} = lists:foldr(Reducer, {0, []}, Tokens),
    %% Remove initial 'break' if one was inferred
    case Output of
        [{break, 0} | Rest] -> Rest;
        _ -> Output
    end. 

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
