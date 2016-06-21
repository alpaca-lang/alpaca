-module(mlfe_codegen).
-export([gen/1]).

-include("mlfe_ast.hrl").

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

gen(#mlfe_module{}=Mod) ->
    #mlfe_module{
       name=ModuleName, 
       function_exports=Exports, 
       functions=Funs} = Mod,
    {_Env, CompiledFuns} = gen_funs([], [], Funs),
    CompiledExports = [gen_export(E) || E <- Exports],
    {ok, cerl:c_module(
           cerl:c_atom(ModuleName),
           CompiledExports,
           [],
           CompiledFuns)
    }.

gen_export({N, A}) ->
    cerl:c_fname(list_to_atom(N), A).

gen_funs(Env, Funs, []) ->
    {Env, Funs};
gen_funs(Env, Funs, [#mlfe_fun_def{name={symbol, _, N}, args=[{unit, _}]}=F|T]) ->
    NewEnv = [{N, 0}|Env],
    io:format("Env is ~w~n", [NewEnv]),
    NewF = gen_fun(NewEnv, F),
    gen_funs(NewEnv, [NewF|Funs], T);
gen_funs(Env, Funs, [#mlfe_fun_def{name={symbol, _, N}, args=A}=F|T]) ->
    NewEnv = [{N, length(A)}|Env],
    io:format("Env is ~w~n", [NewEnv]),
    NewF = gen_fun(NewEnv, F),
    gen_funs(NewEnv, [NewF|Funs], T).

gen_fun(Env, #mlfe_fun_def{name={symbol, _, N}, args=[{unit, _}], body=Body}) ->
    io:format("~nCompiling unit function ~s~n", [N]),
    FName = cerl:c_fname(list_to_atom(N), 0),
    A = [],
    B = gen_expr(Env, Body),
    {FName, cerl:c_fun(A, B)};
gen_fun(Env, #mlfe_fun_def{name={symbol, _, N}, args=Args, body=Body}) ->
    FName = cerl:c_fname(list_to_atom(N), length(Args)),
    A = [cerl:c_var(list_to_atom(X)) || {symbol, _, X} <- Args],
    B = gen_expr(Env, Body),
    {FName, cerl:c_fun(A, B)}.

gen_expr(_, {add, _}) ->
    cerl:c_atom('+');
gen_expr(_, {minus, _}) ->
    cerl:c_atom('-');
gen_expr(_, {int, _, I}) ->
    cerl:c_int(I);
gen_expr(_, {float, _, F}) ->
    cerl:c_float(F);
gen_expr(_, {atom, _, A}) ->
    cerl:c_atom(list_to_atom(A));
gen_expr(_, {chars, _, Cs}) ->
    cerl:c_string(Cs);
gen_expr(_, {string, _, S}) ->
    cerl:c_string(S);
gen_expr(_, {'_', _}) ->
    cerl:c_var("_");
gen_expr(_Env, [{symbol, _, V}]) ->
    cerl:c_var(list_to_atom(V));
gen_expr(_Env, {symbol, _, V}) ->
    cerl:c_var(list_to_atom(V));
gen_expr(_, {nil, _}) ->
    cerl:c_nil();
gen_expr(Env, #mlfe_cons{head=H, tail=T}) ->
    cerl:c_cons(gen_expr(Env, H), gen_expr(Env, T));
gen_expr(Env, #mlfe_type_check{type=is_string, expr={symbol, _, _}=S}) ->
    cerl:c_call(
      cerl:c_atom('erlang'),
      cerl:c_atom('is_list'),
      [gen_expr(Env, S)]);
gen_expr(Env, #mlfe_type_check{type=T, expr={symbol, _, _}=S}) ->
    cerl:c_call(
      cerl:c_atom('erlang'),
      cerl:c_atom(T),
      [gen_expr(Env, S)]);
gen_expr(Env, #mlfe_apply{name={bif, _, _L, Module, FName}, args=Args}) ->
    cerl:c_call(
      cerl:c_atom(Module),
      cerl:c_atom(FName),
      [gen_expr(Env, E) || E <- Args]);      
gen_expr(Env, #mlfe_apply{name={Module, {symbol, _L, N}, _}, args=Args}) ->
    FName = cerl:c_atom(N),
    cerl:c_call(
      cerl:c_atom(Module),
      FName,
      [gen_expr(Env, E) || E <- Args]);
    
gen_expr(Env, #mlfe_apply{name={symbol, _Line, Name}, args=[{unit, _}]}) ->
    FName = case proplists:get_value(Name, Env) of
                undefined ->
                    cerl:c_var(list_to_atom(Name));
                0 ->
                    cerl:c_fname(list_to_atom(Name), 0)
            end,
    cerl:c_apply(FName, []);
gen_expr(Env, #mlfe_apply{name={symbol, _Line, Name}, args=Args}) ->
    io:format("~nCompiling apply for ~s env is ~w~n", [Name, Env]),
    FName = case proplists:get_value(Name, Env) of
                undefined ->
                    cerl:c_var(list_to_atom(Name));
                Arity ->
                    cerl:c_fname(list_to_atom(Name), Arity)
            end,
    cerl:c_apply(FName, [gen_expr(Env, E) || E <- Args]);
gen_expr(Env, #mlfe_apply{name={{symbol, _L, N}, Arity}, args=Args}) ->
    FName = cerl:c_fname(list_to_atom(N), Arity),
    cerl:c_apply(FName, [gen_expr(Env, E) || E <- Args]);

gen_expr(Env, #mlfe_ffi{}=FFI) ->
    #mlfe_ffi{
       module=M,
       function_name=FN,
       args=Cons,
       clauses=Clauses} = FFI,

    %% calling apply/3 with the compiled cons cell is simpler
    %% than unpacking the cons cell into an actual list of args:
    Apply = cerl:c_call(
              cerl:c_atom('erlang'),
              cerl:c_atom('apply'),
              [gen_expr(Env, M),
               gen_expr(Env, FN), 
               gen_expr(Env, Cons)]),

   cerl:c_case(Apply, [gen_expr(Env, X) || X <- Clauses]);

%% Pattern, expression
gen_expr(Env, #mlfe_clause{pattern=P, guards=[], result=E}) ->
    cerl:c_clause([gen_expr(Env, P)], gen_expr(Env, E));
gen_expr(Env, #mlfe_clause{pattern=P, guards=Gs, result=E}) ->
    NestG = fun(G, Acc) ->
                    cerl:c_call(
                      cerl:c_atom('erlang'),
                      cerl:c_atom('and'),
                      [gen_expr(Env, G), Acc])
            end,
    F = fun
            ([], G) -> G;
            (G, Acc) -> NestG(G, Acc)
        end,
    [H|T] = lists:reverse(Gs),
    G = lists:foldl(F, gen_expr(Env, H), T),
    cerl:c_clause([gen_expr(Env, P)], 
                  G,
                  gen_expr(Env, E));
                
gen_expr(Env, #mlfe_tuple{values=Vs}) ->
    cerl:c_tuple([gen_expr(Env, E) || E <- Vs]);
gen_expr(_Env, #mlfe_type_apply{name={type_constructor, _, N}, arg=none}) ->
    cerl:c_atom(N);
gen_expr(Env, #mlfe_type_apply{name={type_constructor, _, N}, arg=A}) ->
    cerl:c_tuple([cerl:c_atom(N), gen_expr(Env, A)]);
%% Expressions, Clauses
gen_expr(Env, #mlfe_match{match_expr=E, clauses=Cs}) ->
    cerl:c_case(gen_expr(Env, E), [gen_expr(Env, X) || X <- Cs]);

gen_expr(Env, #fun_binding{def=F, expr=E}) -> %{defn, Args, Body}, E}) ->
    #mlfe_fun_def{name={symbol, _, N}, args=A} = F,
    Arity = case A of
                [{unit, _}] -> 0;
                L -> length(L)
            end,
    NewEnv = [{N, Arity}|Env],
    cerl:c_letrec([gen_fun(NewEnv, F)], gen_expr(NewEnv, E));
gen_expr(Env, #var_binding{name={symbol, _, N}, to_bind=E1, expr=E2}) -> 
    %% TODO:  environment supporting vars
    cerl:c_let([cerl:c_var(list_to_atom(N))], 
               gen_expr(Env, E1),
               gen_expr(Env, E2)).
    

-ifdef(TEST).

parse_and_gen(Code) ->
    {ok, _, _, Mod} = mlfe_ast_gen:parse_module(0, Code),
    {ok, Forms} = mlfe_codegen:gen(Mod),
    compile:forms(Forms, [report, verbose, from_core]).

simple_compile_test() ->
    Code =
        "module test_mod\n\n"
        "export add/2, sub/2\n\n"
        "add x y = x + y\n\n"
        "sub x y = x - y\n\n",
    {ok, _, _Bin} = parse_and_gen(Code).

module_with_internal_apply_test() ->
    Code =
        "module test_mod\n\n"
        "export add/2\n\n"
        "adder x y = x + y\n\n"
        "add x y = adder x y\n\n"
        "eq x y = x == y",
    {ok, _, Bin} = parse_and_gen(Code).

fun_and_var_binding_test() ->
    Name = fun_and_var_binding,
    FN = atom_to_list(Name) ++ ".beam",
    Code =
        "module fun_and_var_binding\n\n"
        "export test_func/1\n\n"
        "test_func x =\n"
        "  let y = x + 2 in\n"
        "  let double z = z + z in\n"
        "  double y",
    {ok, _, Bin} = parse_and_gen(Code),
    {module, Name} = code:load_binary(Name, FN, Bin),
    ?assertEqual(8, Name:test_func(2)),
    true = code:delete(Name).

unit_function_test() ->
    Name = unit_function,
    FN = atom_to_list(Name) ++ ".beam",
    Code =
        "module unit_function\n\n"
        "export test_func/1\n\n"
        "test_func x =\n"
        "  let y () = 5 in\n"
        "  let z = 3 in\n"
        "  x + ((y ()) + z)",
    {ok, _, Bin} = parse_and_gen(Code),
    {module, Name} = code:load_binary(Name, FN, Bin),
    ?assertEqual(10, Name:test_func(2)),
    true = code:delete(Name).

parser_nested_letrec_test() ->
    Code =
        "module test_mod\n\n"
        "export add/2\n\n"
        "add x y =\n"
        "  let adder1 a b = a + b in\n"
        "  let adder2 c d = adder1 c d in\n"
        "  adder2 x y",
    {ok, _, Bin} = parse_and_gen(Code).

%% This test will fail until I have implemented equality guards:
module_with_match_test() ->
    Name = compile_module_with_match,
    FN = atom_to_list(Name) ++ ".beam",
    io:format("Fake name is ~s~n", [FN]),
    Code = 
        "module compile_module_with_match\n\n"
        "export test/1, first/1, compare/2\n\n"
        "test x = match x with\n"
        "  0 -> :zero\n"
        "| 1 -> :one\n"
        "| _ -> :more_than_one\n\n"
        "first t =\n"
        "  match t with\n"
        "    (f, _) -> f\n"
        "  | _ -> :not_a_2_tuple\n\n"
    %% This is the failing section in particular:
        "compare x y = match x with\n"
        "  a, a == y -> :matched\n"
        "| _ -> :not_matched",
    {ok, _, Bin} = parse_and_gen(Code),
    {module, Name} = code:load_binary(Name, FN, Bin),
    ?assertEqual(one, Name:test(1)),
    ?assertEqual(1, Name:first({1, a})),
    ?assertEqual(not_a_2_tuple, Name:first(an_atom)),
    ?assertEqual('matched', Name:compare(1, 1)),
    ?assertEqual('not_matched', Name:compare(1, 2)),
    true = code:delete(Name).

cons_test() ->
    Name = compiler_cons_test,
    FN = atom_to_list(Name) ++ ".beam",
    Code = 
        "module compiler_cons_test\n\n"
        "export make_list/2, map/2\n\n"
        "make_list h t =\n"
        "  match t with\n"
        "    a :: b -> h :: t\n"
        "  | term -> h :: term :: []\n\n"
        "map f x =\n"
        "  match x with\n"
        "    [] -> []\n"
        "  | h :: t -> (f h) :: (map f t)",
    {ok, _, Bin} = parse_and_gen(Code),
    {module, Name} = code:load_binary(Name, FN, Bin),
    ?assertEqual([1, 2], Name:make_list(1, 2)),
    ?assertEqual([1, 2, 3], Name:make_list(1, [2, 3])),
    ?assertEqual([2, 3], Name:map(fun(X) -> X+1 end, [1, 2])),
    ?assertEqual([3, 4], Name:map(fun(X) -> X+1 end, Name:make_list(2, 3))),
    true = code:delete(Name).

call_test() ->
    Code1 =
        "module call_test_a\n\n"
        "export a/1\n\n"
        "a x = call_test_b.add x 1",
    Code2 =
        "module call_test_b\n\n"
        "export add/2\n\n"
        "add x y = x + y",

    {ok, _, Bin1} = parse_and_gen(Code1),
    {ok, _, Bin2} = parse_and_gen(Code2),
    {module, call_test_a} = code:load_binary(call_test_a, "call_test_a.beam", Bin1),
    {module, call_test_b} = code:load_binary(call_test_b, "call_test_b.beam", Bin2),


    Name = call_test_a,
    ?assertEqual(3, Name:a(2)),
    true = code:delete(call_test_a),
    true = code:delete(call_test_b).

ffi_test() ->
    Code =
        "module ffi_test\n\n"
        "export a/1\n\n"
        "a x = call_erlang :erlang :list_to_integer [x] with\n"
        "  1 -> :one\n"
        "| _ -> :not_one\n",
    {ok, _, Bin} = parse_and_gen(Code),
    {module, ffi_test} = code:load_binary(ffi_test, "ffi_test.beam", Bin),
    
    Mod = ffi_test,
    ?assertEqual('one', Mod:a("1")),
    ?assertEqual('not_one', Mod:a("2")),
    true = code:delete(ffi_test).

%% TODO:  with union types, test/1 should return integers and floats
%% just tagged with different type constructors.
type_guard_test() ->
    Code = 
        "module type_guard_test\n\n"
        "export test/1\n\n"
        "test x = \n"
        "call_erlang :erlang :* [x, x] with\n"
        "   i, is_integer i -> i\n"
        " | f -> 0",
    {ok, _, Bin} = parse_and_gen(Code),
    Mod = type_guard_test,
    {module, Mod} = code:load_binary(Mod, "type_guard_test.beam", Bin),
    
    %% Checking that when the result is NOT an integer we're falling back
    %% to integer 0 as expected in the code above:
    ?assertEqual(4, Mod:test(2)),
    ?assertEqual(0, Mod:test(1.3)),
    true = code:delete(Mod).

multi_type_guard_test() ->
    Code = 
        "module multi_type_guard_test\n\n"
        "export test/1\n\n"
        "test x = \n"
        "call_erlang :erlang :* [x, x] with\n"
        "   i, is_integer i, i == 4 -> :got_four\n"
        " | i, is_integer i, i > 5, i < 20 -> :middle\n"
        " | i, is_integer i -> :just_int\n"
        " | f -> :not_int",
    {ok, _, Bin} = parse_and_gen(Code),
    Mod = multi_type_guard_test,
    {module, Mod} = code:load_binary(Mod, "multi_type_guard_test.beam", Bin),
    
    ?assertEqual('got_four', Mod:test(2)),
    ?assertEqual('middle', Mod:test(4)),
    ?assertEqual('just_int', Mod:test(5)),
    ?assertEqual('not_int', Mod:test(1.3)),
    true = code:delete(Mod).
    
-endif.
