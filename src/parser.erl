-module(parser).
-export([parse/1, parse_module/1]).

-include("mlfe_ast.hrl").

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

parse({ok, Tokens, _}) ->
    parse(Tokens);
parse(Tokens) when is_list(Tokens) ->
    io:format("Parsing ~w~n", [Tokens]),
    mlfe_parser:parse(Tokens).

parse_module(Text) ->
    {ok, Tokens, _} = scanner:scan(Text),
    parse_module(Tokens, {no_module, [], []}).

parse_module([], {no_module, _, _}) ->
    {error, no_module_defined};
parse_module([], {Mod, Exports, Funs}) ->
    {ok, Mod, Exports, lists:reverse(Funs)};
parse_module([{break, _}], Memo) ->
    parse_module([], Memo);
parse_module(Tokens, Memo) ->
    {NextBatch, Rem} = next_batch(Tokens, []),
    {ok, Parsed} = parse(NextBatch),
    case update_memo(Memo, Parsed) of
        {ok, NewMemo} ->
            parse_module(Rem, NewMemo);
        {error, Err} ->
            Err
    end.

update_memo({no_module, Exports, Funs}, {module, Name}) ->
    {ok, {Name, Exports, Funs}};
update_memo({Name, _Exports, _Funs}, {module, DupeName}) ->
    {error, "You are trying to rename the module " ++
         Name ++ " to " ++ DupeName ++ " which is not allowed."};
update_memo({Name, Exports, Funs}, {export, Es}) ->
    {ok, {Name, Es ++ Exports, Funs}};
update_memo({Name, Exports, Funs}, {defn, Args, Body}) ->
    {ok, {Name, Exports, [{Args, Body}|Funs]}};
update_memo(_, Bad) ->
    {error, {"Top level requires defs, module, and export declarations", Bad}}.

next_batch([{break, _}|Rem], Memo) ->
    {lists:reverse(Memo), Rem};
next_batch([], Memo) ->
    {lists:reverse(Memo), []};
next_batch([Token|Tail], Memo) ->
    next_batch(Tail, [Token|Memo]).

-ifdef(TEST).

symbols_test_() ->
    [?_assertEqual({ok, {symbol, 1, "oneSymbol"}}, 
                   parse(scanner:scan("oneSymbol")))
    ].

infix_test_() ->
    [?_assertEqual({ok, #mlfe_infix{type=undefined,
                                    operator={add, 1},
                                    left={symbol, 1, "x"},
                                    right={symbol, 1, "x"}}},
                   begin
                       Res = scanner:scan("x + x"),
                       io:format("RES is ~w~n", [Res]),
                       parse(Res)
                   end),
     ?_assertEqual({ok, #mlfe_infix{type=undefined,
                                   operator={minus, 1},
                                   left={int, 1, 5},
                                   right={int, 1, 3}}},
                   parse(scanner:scan("5 - 3")))
    ].

defn_test_() ->
    [
     ?_assertEqual({ok, {defn, [{symbol, 1, "x"}], {int, 1, 5}}},
                   parse(scanner:scan("x=5"))),
     ?_assertEqual({ok, {defn, 
                         [{symbol, 1, "double"}, {symbol, 1, "x"}],
                         #mlfe_infix{type=undefined,
                                     operator={add, 1}, 
                                     left={symbol, 1, "x"},
                                     right={symbol, 1, "x"}}}},
                  parse(scanner:scan("double x = x + x"))),
     ?_assertEqual({ok, {defn,
                         [{symbol, 1, "add"}, {symbol, 1, "x"}, {symbol, 1, "y"}],
                         #mlfe_infix{type=undefined,
                                     operator={add, 1},
                                     left={symbol, 1, "x"},
                                     right={symbol, 1, "y"}}}},
                   parse(scanner:scan("add x y = x + y")))
    ].

let_binding_test_() ->
    [?_assertEqual({ok, {bind_in,
                         {defn,
                          [{symbol, 1, "double"}, {symbol, 1, "x"}],
                          #mlfe_infix{type=undefined,
                                      operator={add, 1},
                                      left={symbol, 1, "x"},
                                      right={symbol, 1, "x"}}},
                        {apply, {symbol, 1, "double"}, [{int, 1, 2}]}}}, 
                   parse(scanner:scan("let double x = x + x in double 2"))),
     ?_assertEqual({ok, {defn,
                         [{symbol, 1, "doubler"}, {symbol, 1, "x"}],
                         {bind_in,
                          {defn,
                           [{symbol, 2, "double"}, {symbol, 2, "x"}],
                           #mlfe_infix{type=undefined, 
                                       operator={add, 2}, 
                                       left={symbol, 2, "x"}, 
                                       right={symbol, 2, "x"}}},
                          {apply, {symbol, 3, "double"}, [{int, 3, 2}]}}}}, 
                   parse(scanner:scan(
                           "doubler x =\n"
                           "  let double x = x + x in\n"
                           "  double 2"))),
     ?_assertEqual({ok,
                    {defn,
                     [{symbol,1,"my_fun"},{symbol,1,"x"},{symbol,1,"y"}],
                     {bind_in,
                      {defn,
                       [{symbol,1,"xer"},{symbol,1,"a"}],
                       #mlfe_infix{type=undefined,
                                   operator={add,1},
                                   left={symbol,1,"a"},
                                   right={symbol,1,"a"}}},
                      {bind_in,
                       {defn,
                        [{symbol,1,"yer"},{symbol,1,"b"}],
                        #mlfe_infix{type=undefined,
                                    operator={add,1},
                                    left={symbol,1,"b"},
                                    right={symbol,1,"b"}}},
                       #mlfe_infix{type=undefined,
                                   operator={add,1},
                                   left={apply,{symbol,1,"xer"},[{symbol,1,"x"}]},
                                   right={apply,{symbol,1,"yer"},[{symbol,1,"y"}]}}}}}},
                   parse(scanner:scan(
                           "my_fun x y ="
                           "  let xer a = a + a in"
                           "  let yer b = b + b in"
                           "  (xer x) + (yer y)")))
    ].

application_test_() ->
    [?_assertEqual({ok, {apply, {symbol, 1, "double"}, [{int, 1, 2}]}},
                  parse(scanner:scan("double 2"))),
     ?_assertEqual({ok, {apply, {symbol, 1, "two"}, [{symbol, 1, "symbols"}]}},
                   parse(scanner:scan("two symbols"))),
     ?_assertEqual({ok, {apply, {symbol, 1, "x"}, [{symbol, 1, "y"}, {symbol, 1, "z"}]}},
                   parse(scanner:scan("x y z")))
    ].


module_parse_test() ->
    Module =
        "module test_mod\n\n"
        "export add/2\n\n"
        "add x y = x + y\n\n",
    Expected = {ok,
                "test_mod",
                [{"add",2}],
                [{
                   % name and args:
                   [{symbol,5,"add"},{symbol,5,"x"},{symbol,5,"y"}],
                   % body:
                   #mlfe_infix{type=undefined,
                               operator={add,5},
                               left={symbol,5,"x"},
                               right={symbol,5,"y"}}}]},
    ?assertEqual(Expected, parse_module(Module)).

module_def_test_() ->
    [?_assertEqual({ok, {module, "test_mod"}}, 
                   parse(scanner:scan("module test_mod"))),
     ?_assertEqual({ok, {module, "myMod"}}, 
                   parse(scanner:scan("module myMod")))
    ].

export_test_() ->
    [?_assertEqual({ok, {export, [{"add", 2}]}},
                  parse(scanner:scan("export add/2")))
    ].

expr_test_() ->
    [?_assertEqual({ok, {int, 1, 2}}, parse(scanner:scan("2"))),
     ?_assertEqual({ok, #mlfe_infix{type=undefined,
                                    operator={add, 1}, 
                                    left={int, 1, 1}, 
                                    right={int, 1, 5}}},
                  parse(scanner:scan("1 + 5"))),
     ?_assertEqual({ok, {apply,
                         {symbol, 1, "add"}, 
                         [{symbol, 1, "x"},
                          {int, 1, 2}]}},
                   parse(scanner:scan("add x 2"))),
     ?_assertEqual({ok, {apply,
                         {symbol, 1, "tuple_func"},
                         [{tuple, [{symbol, 1, "x"}, {int, 1, 1}]},
                          {symbol, 1, "y"}]}},
                   parse(scanner:scan("tuple_func (x, 1) y")))
    ].

nesting_test_() ->
    [?_assertEqual({ok, 
                    {apply, 
                     {symbol, 1, "double"},
                     [{symbol, 1, "x"}]}}, 
                   parse(scanner:scan("(double x)"))),
     ?_assertEqual({ok, {apply, 
                         {symbol, 1, "add"},
                         [{apply,{symbol, 1, "double"}, [{symbol, 1, "x"}]},
                          {int, 1, 2}]}},
                   parse(scanner:scan("add (double x) 2")))
    ].


module_with_let_test() ->
    Code =
        "module test_mod\n\n"
        "export add/2\n\n"
        "add x y =\n"
        "  let adder a b = a + b in\n"
        "  adder x y",
    ?assertEqual({ok,"test_mod",
                  [{"add",2}],
                  [{[{symbol,5,"add"},{symbol,5,"x"},{symbol,5,"y"}],
                    {bind_in,
                     {defn,
                      [{symbol,6,"adder"},
                       {symbol,6,"a"},
                       {symbol,6,"b"}],
                      #mlfe_infix{type=undefined,
                                  operator={add,6},
                                  left={symbol,6,"a"},
                                  right={symbol,6,"b"}}},
                     {apply,
                      {symbol,7,"adder"},
                      [{symbol,7,"x"},{symbol,7,"y"}]}}}]}, 
                 parse_module(Code)).

match_test_() ->
    [?_assertEqual({ok, {match, {symbol, 1, "x"},
                         [{match_clause, {int, 2, 0}, {symbol, 2, "zero"}},
                          {match_clause, {'_', 3}, {symbol, 3, "non_zero"}}]}},
                   parse(scanner:scan(
                           "match x with\n"
                           "| 0 -> zero\n"
                           "| _ -> non_zero\n"))),
     ?_assertEqual({ok, {match, 
                         {apply, 
                          {symbol, 1, "add"}, 
                          [{symbol, 1, "x"}, {symbol, 1, "y"}]},
                         [{match_clause, {int, 2, 0}, {atom, 2, "zero"}},
                          {match_clause, {int, 3, 1}, {atom, 3, "one"}},
                          {match_clause, {'_', 4}, {atom, 4, "more_than_one"}}
                         ]}},
                   parse(scanner:scan(
                           "match add x y with\n"
                           "| 0 -> 'zero\n"
                           "| 1 -> 'one\n"
                           "| _ -> 'more_than_one\n"))),
     ?_assertEqual({ok, {match,
                         {symbol, 1, "x"},
                         [{match_clause, 
                          {tuple, [{'_', 2}, {symbol, 2, "x"}]},
                          {atom, 2, "anything_first"}},
                         {match_clause,
                          {tuple, [{int, 3, 1}, {symbol, 3, "x"}]},
                          {atom, 3, "one_first"}}]}},
                   parse(scanner:scan(
                           "match x with\n"
                           "| (_, x) -> 'anything_first\n"
                           "| (1, x) -> 'one_first\n"))),
     ?_assertEqual({ok, {match,
                         {tuple, [{symbol, 1, "x"}, {symbol, 1, "y"}]},
                         [{match_clause, {tuple, 
                                          [{tuple, [{'_', 2}, {int, 2, 1}]},
                                           {symbol, 2, "a"}]},
                           {atom, 2, "nested_tuple"}}]}},
                   parse(scanner:scan(
                           "match (x, y) with\n"
                           "| ((_, 1), a) -> 'nested_tuple")))
    ].

tuple_test_() ->
    %% first no unary tuples:
    [?_assertEqual({ok, {int, 1, 1}}, parse(scanner:scan("(1)"))),
     ?_assertEqual({ok, {tuple, [{int, 1, 1}, {int, 1, 2}]}},
                   parse(scanner:scan("(1, 2)"))),
     ?_assertEqual({ok, {tuple, [{symbol, 1, "x"}, {int, 1, 1}]}},
                   parse(scanner:scan("(x, 1)"))),
     ?_assertEqual({ok, {tuple, [{tuple, [{int, 1, 1}, {symbol, 1, "x"}]},
                                 {int, 1, 12}]}},
                   parse(scanner:scan("((1, x), 12)")))
    ].

list_test_() ->
    [?_assertEqual({ok, {nil, 1}}, parse(scanner:scan("[]"))),
     ?_assertEqual({ok, {cons, {int, 1, 1}, {nil, 1}}},
                   parse(scanner:scan("[1]"))),
     ?_assertEqual({ok, {cons,  
                         {symbol, 1, "x"},
                         {cons, {int, 1, 1}, {nil, 1}}}},
                   parse(scanner:scan("x : [1]"))),
     ?_assertEqual({ok, {cons,
                         {int, 1, 1},
                         {symbol, 1, "y"}}},
                   parse(scanner:scan("1 : y"))),
     ?_assertEqual({ok,{match,
                        {symbol,1,"x"},
                        [{match_clause,{nil,2},{nil,2}},
                         {match_clause,
                          {cons,{symbol,3,"h"},{symbol,3,"t"}},
                          {symbol,3,"h"}}]}},
                   parse(scanner:scan(
                           "match x with\n"
                           "| [] -> []\n"
                           "| h : t -> h\n")))
    ].
                         
                         

simple_module_test() ->
    Code =
        "module test_mod\n\n"
        "export add/2, sub/2\n\n"
        "adder x y = x + y\n\n"
        "add1 x = adder x 1\n\n"
        "add x y = adder x y\n\n"
        "sub x y = x - y",
    ?assertEqual({ok,"test_mod",
                  [{"add",2},{"sub",2}],
                  [{[{symbol,5,"adder"},{symbol,5,"x"},{symbol,5,"y"}],
                    #mlfe_infix{type=undefined,
                                operator={add,5},
                                left={symbol,5,"x"},
                                right={symbol,5,"y"}}},
                   {[{symbol,7,"add1"},{symbol,7,"x"}],
                    {apply,{symbol,7,"adder"},[{symbol,7,"x"},{int,7,1}]}},
                   {[{symbol,9,"add"},{symbol,9,"x"},{symbol,9,"y"}],
                    {apply,{symbol,9,"adder"},
                     [{symbol,9,"x"},{symbol,9,"y"}]}},
                   {[{symbol,11,"sub"},{symbol,11,"x"},{symbol,11,"y"}],
                    #mlfe_infix{type=undefined,
                                operator={minus,11},
                                left={symbol,11,"x"},
                                right={symbol,11,"y"}}}]}, 
                 parse_module(Code)).


-endif.
