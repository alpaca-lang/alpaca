-module(mlfe_compile).
-export([compile/1]).

-include("mlfe_ast.hrl").

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

compile(Code) when is_list(Code) ->
    AST = parser:parse_module(Code),
    io:format("AST is ~w~n", [AST]),
    {ok, Forms} = compile(AST),
    io:format("Forms for ~s~n ARE ~n~w~n", [Code, Forms]),
    compile:forms(Forms, [report_errors, verbose, from_core]);
compile({error, _} = E) ->
    io:format("Error was ~w~n", [E]),
    E;
compile({ok, ModuleName, Exports, Funs}) ->
    {_Env, CompiledFuns} = compile_funs([], [], Funs),
    CompiledExports = [compile_export(E) || E <- Exports],
    {ok, cerl:c_module(
           cerl:c_atom(list_to_atom(ModuleName)),
           CompiledExports,
           [],
           CompiledFuns)
    }.

compile_export({N, A}) ->
    cerl:c_fname(list_to_atom(N), A).

compile_funs(Env, Funs, []) ->
    {Env, Funs};
compile_funs(Env, Funs, [{ArgList, _}=F|T]) ->
    [{symbol, _, N} | Args] = ArgList,
    NewEnv = [{N, length(Args)}|Env],
    io:format("Env is ~w~n", [NewEnv]),
    NewF = compile_fun(NewEnv, F),
    compile_funs(NewEnv, [NewF|Funs], T).

compile_fun(Env, {ArgList, Body}) ->
    [{symbol, _, N} | Args] = ArgList,
    FName = cerl:c_fname(list_to_atom(N), length(Args)),
    A = [cerl:c_var(list_to_atom(X)) || {symbol, _, X} <- Args],
    B = compile_expr(Env, Body),
    {FName, cerl:c_fun(A, B)}.

compile_expr(Env, #mlfe_infix{operator=Op, left=A, right=B}) ->
    cerl:c_call(
      cerl:c_atom('erlang'),
      compile_expr(Env, Op),
      [compile_expr(Env, A), compile_expr(Env, B)]);
compile_expr(_, {add, _}) ->
    cerl:c_atom('+');
compile_expr(_, {minus, _}) ->
    cerl:c_atom('-');
compile_expr(_, {int, _, I}) ->
    cerl:c_int(I);
compile_expr(_, {float, _, F}) ->
    cerl:c_float(F);
compile_expr(_, {atom, _, A}) ->
    cerl:c_atom(list_to_atom(A));
compile_expr(_, {'_', _}) ->
    cerl:c_var("_");
compile_expr(_Env, [{symbol, _, V}]) ->
    cerl:c_var(list_to_atom(V));
compile_expr(_Env, {symbol, _, V}) ->
    cerl:c_var(list_to_atom(V));
compile_expr(_, {nil, _}) ->
    cerl:c_nil();
compile_expr(Env, {cons, H, T}) ->
    cerl:c_cons(compile_expr(Env, H), compile_expr(Env, T));
compile_expr(Env, {apply, {symbol, _Line, Name}, Args}) ->
    io:format("~nCompiling apply for ~s env is ~w~n", [Name, Env]),
    FName = case proplists:get_value(Name, Env) of
                undefined ->
                    cerl:c_var(list_to_atom(Name));
                Arity ->
                    cerl:c_fname(list_to_atom(Name), Arity)
            end,
    cerl:c_apply(FName, [compile_expr(Env, E) || E <- Args]);
%% Pattern, expression
compile_expr(Env, {match_clause, P, E}) ->
    cerl:c_clause([compile_expr(Env, P)], compile_expr(Env, E));
compile_expr(Env, {pattern_tuple, T}) ->
    cerl:c_tuple([compile_expr(Env, E) || E <- T]);
compile_expr(Env, {tuple, T}) ->
    cerl:c_tuple([compile_expr(Env, E) || E <- T]);
%% Expressions, Clauses
compile_expr(Env, {match, E, Cs}) ->
    cerl:c_case(compile_expr(Env, E), [compile_expr(Env, X) || X <- Cs]);
compile_expr(Env, {bind_in, {defn, Args, Body}, E}) ->
    [{symbol, _, N} | RemArgs] = Args,
    NewEnv = [{N, length(RemArgs)}|Env],
    cerl:c_letrec([compile_fun(NewEnv, {Args, Body})], compile_expr(NewEnv, E)).
    

-ifdef(TEST).

simple_compile_test() ->
    Code =
        "module test_mod\n\n"
        "export add/2, sub/2\n\n"
        "add x y = x + y\n\n"
        "sub x y = x - y\n\n",
    {ok, _, _Bin} = compile(Code).

module_with_internal_apply_test() ->
    Code =
        "module test_mod\n\n"
        "export add/2\n\n"
        "adder x y = x + y\n\n"
        "add x y = adder x y",
    {ok, _, Bin} = compile(Code).

parser_compilation_test() ->
    Code =
        "module test_mod\n\n"
        "export add/2, sub/2, add1/1\n\n"
        "adder x y = x + y\n\n"
        "add1 x = adder x 1\n\n"
        "add x y = adder x y\n\n"
        "sub x y = x - y",
    {ok, _, Bin} = compile(Code).

parser_letrec_test() ->
    Code =
        "module test_mod\n\n"
        "export add/2\n\n"
        "add x y =\n"
        "  let adder a b = a + b in\n"
        "  adder x y",
    {ok, _, Bin} = compile(Code).

parser_nested_letrec_test() ->
    Code =
        "module test_mod\n\n"
        "export add/2\n\n"
        "add x y =\n"
        "  let adder1 a b = a + b in\n"
        "  let adder2 c d = adder1 c d in\n"
        "  adder2 x y",
    {ok, _, Bin} = compile(Code).

module_with_match_test() ->
    Name = compile_module_with_match,
    FN = atom_to_list(Name) ++ ".beam",
    io:format("Fake name is ~s~n", [FN]),
    Code = 
        "module compile_module_with_match\n\n"
        "export test/1, first/1\n\n"
        "test x = match x with\n"
        "| 0 -> 'zero\n"
        "| 1 -> 'one\n"
        "| _ -> 'more_than_one\n\n"
        "first t =\n"
        "  match t with\n"
        "  | (f, _) -> f\n"
        "  | _ -> 'not_a_2_tuple\n",
    {ok, _, Bin} = compile(Code),
    {module, Name} = code:load_binary(Name, FN, Bin),
    ?assertEqual(one, Name:test(1)),
    ?assertEqual(1, Name:first({1, a})),
    ?assertEqual(not_a_2_tuple, Name:first(an_atom)),
    true = code:delete(Name).

cons_test() ->
    Name = compiler_cons_test,
    FN = atom_to_list(Name) ++ ".beam",
    Code = 
        "module compiler_cons_test\n\n"
        "export make_list/2, map/2\n\n"
        "make_list h t =\n"
        "  match t with\n"
        "  | a : b -> h : t\n"
        "  | term -> h : term : []\n\n"
        "map f x =\n"
        "  match x with\n"
        "  | [] -> []\n"
        "  | h : t -> (f h) : (map f t)",
    {ok, _, Bin} = compile(Code),
    {module, Name} = code:load_binary(Name, FN, Bin),
    ?assertEqual([1, 2], Name:make_list(1, 2)),
    ?assertEqual([1, 2, 3], Name:make_list(1, [2, 3])),
    ?assertEqual([2, 3], Name:map(fun(X) -> X+1 end, [1, 2])),
    ?assertEqual([3, 4], Name:map(fun(X) -> X+1 end, Name:make_list(2, 3))),
    true = code:delete(Name).

-endif.
