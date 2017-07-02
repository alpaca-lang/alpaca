%%% -*- mode: erlang;erlang-indent-level: 4;indent-tabs-mode: nil -*-
%%% ex: ft=erlang ts=4 sw=4 et
-module(alpaca_scanner).
-export([scan/1]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

scan(Code) when is_list(Code) -> 
    case alpaca_scan:string(Code) of
        {ok, Tokens, Num} -> {ok, infer_breaks(Tokens), Num};    
        Error -> Error
    end;
scan(Code) when is_binary(Code) ->
    scan(binary:bin_to_list(Code)).

infer_breaks(Tokens) ->
    %% Reduce tokens from the right, inserting a break (i.e. ';;') before
    %% top level constructs including let, type, exports, imports and module.
    %% To avoid inserting breaks in let... in... we track the level of these
    %% (as we're folding right, an 'in' increases the level by one, a 'let'
    %% decreases by one if the current level > 0)
    %% We also track whether we're in a binary as 'type' has a different
    %% semantic there
    
    Reducer = fun(Token, {LetLevel, InBinary, Acc}) ->                     
        {Symbol, Line} = case Token of
            {S, L} when is_integer(L) -> {S, L};
            _Other -> {other, 0}
        end,
        InferBreak = fun() -> 
            {0, InBinary, [{break, Line} | [ Token | Acc]]} 

        end,
        Pass = fun() -> 
            {LetLevel, InBinary, [Token | Acc]} 
        end,
        ChangeLetLevel = fun(Diff) -> 
            {LetLevel + Diff, InBinary, [Token | Acc]}
        end,                   
        BinOpen = fun(State) ->
            {LetLevel, State, [Token | Acc]}
        end,
        case Symbol of
            'in'           -> ChangeLetLevel(+1);                     
            'let'          -> case LetLevel of                                            
                                0 -> InferBreak();
                                _ -> ChangeLetLevel(-1)
                              end;
            'type_declare' -> case InBinary of 
                                true -> Pass();
                                false -> InferBreak()
                              end;
            'bin_open'     -> BinOpen(false);
            'bin_close'    -> BinOpen(true);
            'test'         -> InferBreak();
            'module'       -> InferBreak();
            'export'       -> InferBreak();
            'export_type'  -> InferBreak();
            'import_type'  -> InferBreak();
            'import'       -> InferBreak();
            'val'          -> InferBreak();
            _              -> Pass()
        end      
    end,
    {0, false, Output} = lists:foldr(Reducer, {0, false, []}, Tokens),
    %% Remove initial 'break' if one was inferred
    case Output of
        [{break, _} | Rest] -> Rest;
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
    [?_assertMatch({ok, [{symbol,
                          {'Symbol', #{line := 1, name := <<"mySym">>}}}], 1},
                   scan("mySym")),
     ?_assertMatch({ok, [{symbol,
                          {'Symbol', #{line := 1, name := <<"mySym1">>}}}], 1},
                   scan("mySym1")),
     ?_assertMatch({ok, [{symbol,
                          {'Symbol', #{line := 1, name := <<"mysym">>}}}], 1},
                   scan("mysym"))].

atom_test_() ->
    [?_assertEqual({ok, [{atom, 1, "myAtom"}], 1}, scan(":myAtom"))].

quoted_atom_test_() ->
    [?_assertEqual({ok, [{atom, 1, "Quoted.Atom-Value"}], 1},
                   scan(":\"Quoted.Atom-Value\""))].

string_escape_test_() ->
    [?_assertEqual({ok, [{string, 1, "one\ntwo\n\tthree"}], 1}, 
                   scan("\"one\\ntwo\\n\\tthree\"")),
     ?_assertEqual({ok, [{string, 1, "this is a \"quoted\" string"}], 1}, 
                   scan("\"this is a \\\"quoted\\\" string\"")),
     ?_assertEqual({ok, [{string, 1, "C:\\MYCMD.BAT"}], 1}, 
                   scan("\"C:\\\\MYCMD.BAT\"")),
     ?_assertMatch({error,{1,alpaca_scan,
                         {user,{{error,"Bad control sequence"},
                                1, _}}},
                        1},
                   scan("\"\\! \\} \\<\""))].
            

let_test() ->
    Code = "let symbol = 5",
    ExpectedTokens = [{'let', 1},
                      {symbol, {'Symbol', #{'__struct__' => record,
                                            line => 1,
                                            name => <<"symbol">>,
                                            original => 'None'}}},
                      {assign, 1},
                      {int, 1, 5}],
    ?assertEqual({ok, ExpectedTokens, 1}, scan(Code)).

infer_test() ->
    Code = "module hello\nlet a = 0\nlet b = 1",
    ExpectedTokens = [{'module', 1}, {symbol, 
                                      {'Symbol', 
                                       #{'__struct__' => record,
                                         line => 1,
                                         name => <<"hello">>,
                                         original => 'None'}}},
                      {break, 2}, 
                      {'let', 2}, {symbol, {'Symbol',
                                            #{'__struct__' => record,
                                              line => 2,
                                              name => <<"a">>,
                                              original => 'None'}}},
                      {assign, 2}, {int, 2, 0}, 
                      {break, 3},
                      {'let', 3}, {symbol, {'Symbol',
                                            #{'__struct__' => record,
                                              line => 3,
                                              name => <<"b">>,
                                              original => 'None'}}},
                      {assign, 3}, {int, 3, 1}
                     ],
    ?assertEqual({ok, ExpectedTokens, 3}, scan(Code)).

infer_bin_test() ->
    Code = "module bin_test\nlet a = << 10 : type = int >>",
    ExpectedTokens = [{'module', 1},
                      {symbol, {'Symbol', #{'__struct__' => record,
                                            line => 1,
                                            name => <<"bin_test">>,
                                            original => 'None'}}},
                      {break, 2},
                      {'let', 2}, {symbol, {'Symbol',
                                            #{'__struct__' => record,
                                              line => 2,
                                              name => <<"a">>,
                                              original => 'None'}}},
                       {assign, 2}, 
                       {bin_open, 2}, {int, 2, 10},
                       {':', 2}, {type_declare, 2},
                       {assign, 2}, {symbol, {'Symbol',
                                              #{'__struct__' => record,
                                                line => 2,
                                                name => <<"int">>,
                                                original => 'None'}}},
                       {bin_close, 2}
                     ],
    ?assertEqual({ok, ExpectedTokens, 2}, scan(Code)).

unexpected_token_test_() ->
    [?_assertMatch(
        {error, {1,alpaca_scan,{user, "Unexpected token: ;"}}, 1},
        scan("module bin ; hello")),
     ?_assertMatch(
        {error, {1,alpaca_scan,{user, "Unexpected token: '"}}, 1},
        scan("module bin ' hello"))].
-endif.
