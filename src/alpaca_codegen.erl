%%% -*- mode: erlang;erlang-indent-level: 4;indent-tabs-mode: nil -*-
%%% ex: ft=erlang ts=4 sw=4 et
%%% Copyright 2016 Jeremy Pierre
%%%
%%% Licensed under the Apache License, Version 2.0 (the "License");
%%% you may not use this file except in compliance with the License.
%%% You may obtain a copy of the License at
%%%
%%%     http://www.apache.org/licenses/LICENSE-2.0
%%%
%%% Unless required by applicable law or agreed to in writing, software
%%% distributed under the License is distributed on an "AS IS" BASIS,
%%% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
%%% See the License for the specific language governing permissions and
%%% limitations under the License.

-module(alpaca_codegen).
-export([gen/2]).

-include("alpaca_ast.hrl").

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

%% Simple code generation environment.
%% Tracks:
%%   - names of top-level functions with their arity
%%   - incrementing variable number for wildcard variables (underscores)
%%   - numbers for synthesized function name generation
%%
%% The top-level functions get looked up for correct Core Erlang call
%% construction.  Renaming instances of "_" (the wildcard or "don't care"
%% variable name) is necessary because "_" is actually a legitimate variable
%% name in Core Erlang.  If we don't rename it when there are multiple
%% occurrences in the same pattern there will be a compilation error from
%% the 'cerl' module.
-record(env, {
          module_funs=[] :: list({string(), integer()}),
          wildcard_num=0 :: integer(),
          synthetic_fun_num=0 :: integer()
         }).

make_env(#alpaca_module{functions=Funs}=_Mod) ->
    TopLevelFuns = [{N, A} || #alpaca_fun_def{name={symbol, _, N}, arity=A} <- Funs],
    #env{module_funs=TopLevelFuns, wildcard_num=0}.

prefix_modulename(Name) ->
    case Name of
        erlang -> erlang;
        _ -> list_to_atom("alpaca_" ++ atom_to_list(Name))
    end.

gen(#alpaca_module{}=Mod, Opts) ->
    #alpaca_module{
       name=ModuleName,
       function_exports=Exports,
       functions=Funs,
       tests=Tests} = Mod,
    Env = make_env(Mod),
    PrefixModuleName = prefix_modulename(ModuleName),
    {Env2, CompiledFuns} = gen_funs(Env, [], Funs),
    CompiledTests = gen_tests(Env2, Tests),

    CompiledExports =
        [gen_export(E) || E <- Exports] ++ gen_test_exports(Tests, Opts, []),
    {ok, cerl:c_module(
           cerl:c_atom(PrefixModuleName),
           [gen_export({"module_info", 0}),
            gen_export({"module_info", 1})] ++
               CompiledExports,
           [],
           [module_info0(PrefixModuleName),
            module_info1(PrefixModuleName)] ++
               CompiledFuns ++ CompiledTests)
    }.

gen_export({N, A}) ->
    cerl:c_fname(list_to_atom(N), A).

gen_test_exports([], _, Memo) ->
    Memo;
gen_test_exports(_, [], Memo) ->
    Memo;
gen_test_exports([#alpaca_test{name={string, _, N}}|RemTests], [test|_]=Opts,
                 Memo) ->
    gen_test_exports(
      RemTests, Opts, [gen_export({clean_test_name(N), 0})|Memo]);
gen_test_exports(Tests, [_|Rem], Memo) ->
    gen_test_exports(Tests, Rem, Memo).

gen_funs(Env, Funs, []) ->
    {Env, lists:reverse(Funs)};
gen_funs(Env, Funs, [#alpaca_fun_def{}=F|T]) ->
    NewF = gen_fun(Env, F),
    gen_funs(Env, [NewF|Funs], T).

gen_fun(Env,
        #alpaca_fun_def{
           name={symbol, _, N},
           versions=[#alpaca_fun_version{args=[{unit, _}], body=Body}]}) ->

    FName = cerl:c_fname(list_to_atom(N), 1),
    A = [cerl:c_var('_unit')],
    {_, B} = gen_expr(Env, Body),
    {FName, cerl:c_fun(A, B)};
gen_fun(Env, #alpaca_fun_def{name={symbol, _, N}, versions=Vs}=Def) ->
    case Vs of
        %% If there's a single version with only symbol and/or unit
        %% args, don't compile a pattern match:
        [#alpaca_fun_version{args=Args, body=Body}] ->
            case needs_pattern(Args) of
                false ->
                    FName = cerl:c_fname(list_to_atom(N), length(Args)),
                    A = [cerl:c_var(list_to_atom(X)) || {symbol, _, X} <- Args],
                    {_, B} = gen_expr(Env, Body),
                    {FName, cerl:c_fun(A, B)};
                true ->
                    %% our single version has more than symbols and unit:
                    gen_fun_patterns(Env, Def)
            end;
        _ ->
            %% more than one version:
            gen_fun_patterns(Env, Def)
    end.

needs_pattern(Args) ->
    case lists:filter(fun({unit, _})      -> false;
                         ({symbol, _, _}) -> false;
                         (_)              -> true
                      end, Args) of
        [] -> false;
        _  -> true
    end.

gen_fun_patterns(Env, #alpaca_fun_def{name={symbol, _, N}, arity=A, versions=Vs}) ->
    %% We need to manufacture variable names that we'll use in the
    %% nested pattern matches:
    VarNames = ["pat_var_" ++ integer_to_list(X) || X <- lists:seq(1, A)],
    %% Nest matches:
    FName = cerl:c_fname(list_to_atom(N), A),
    Args = [cerl:c_var(list_to_atom(X)) || X <- VarNames],
    [_TopVar|_] = VarNames,
    B = cerl:c_case(
          cerl:c_values(Args),
          [gen_fun_version(Env, Version) || Version <- Vs]),
    {FName, cerl:c_fun(Args, B)}.

gen_fun_version(Env, #alpaca_fun_version{args=Args, body=Body}) ->
    Patt = [Expr || {_, Expr} <- [gen_expr(Env, A) || A <- Args]],
    {_, BodyExp} = gen_expr(Env, Body),
    cerl:c_clause(Patt, BodyExp).

gen_tests(Env, Tests) ->
    gen_tests(Env, Tests, []).

gen_tests(_Env, [], Memo) ->
    Memo;
gen_tests(Env, [#alpaca_test{name={_, _, N}, expression=E}|Rem], Memo) ->
    FName = cerl:c_fname(list_to_atom(clean_test_name(N)), 0),
    {_, Body} = gen_expr(Env, E),
    TestFun = {FName, cerl:c_fun([], Body)},
    gen_tests(Env, Rem, [TestFun|Memo]).

%% eunit will skip tests with spaces in the name, this may not be the best
%% way to handle it though:
clean_test_name(N) ->
    Base = lists:map(fun(32) -> 95; (C) -> C end, N),
    Base ++ "_test".

gen_expr(Env, {add, _}) ->
    {Env, cerl:c_atom('+')};
gen_expr(Env, {minus, _}) ->
    {Env, cerl:c_atom('-')};
gen_expr(Env, {int, _, I}) ->
    {Env, cerl:c_int(I)};
gen_expr(Env, {float, _, F}) ->
    {Env, cerl:c_float(F)};
gen_expr(Env, {boolean, _, B}) ->
    {Env, cerl:c_atom(B)};
gen_expr(Env, {atom, _, A}) ->
    {Env, cerl:c_atom(list_to_atom(A))};
gen_expr(Env, {chars, _, Cs}) ->
    {Env, cerl:c_string(Cs)};
gen_expr(Env, {string, _, S}) ->
    {Env, cerl:c_binary(literal_binary(S, utf8))};
gen_expr(Env, {unit, _}) ->
    {Env, cerl:c_tuple([])};
gen_expr(#env{wildcard_num=N}=Env, {'_', _}) ->
    %% We produce a unique variable name for each wildcard
    %% "throwaway" variable.  Not doing so causes errors when
    %% compiling forms later due to duplicate names.
    Name = list_to_atom("_" ++ integer_to_list(N)),
    {Env#env{wildcard_num=N+1}, cerl:c_var(Name)};
gen_expr(#env{module_funs=Funs}=Env, {symbol, _, V}) ->
    case proplists:get_value(V, Funs) of
        %% Switch out references to zero-arg funs to applications
        %% of them, simulating constant values
        0 ->
            {Env, cerl:c_apply(cerl:c_fname(list_to_atom(V), 0), [])};
        Arity when is_integer(Arity) ->
            %% Do we have a function with the right arity?
            {Env, cerl:c_fname(list_to_atom(V), Arity)};
        undefined ->
            {Env, cerl:c_var(list_to_atom(V))}
    end;
gen_expr(Env, #alpaca_far_ref{module=M, name=N, arity=A}) ->
    MakeFun = #alpaca_apply{
                 expr={'erlang', {symbol, 0, "make_fun"}, 3},
                 args=[{atom, 0, "alpaca_" ++ atom_to_list(M)},
                       {atom, 0, N},
                       {int, 0, A}]},
    gen_expr(Env, MakeFun);
gen_expr(Env, {raise_error, _, Kind, Expr}) ->
    {Env2, ExprAST} = gen_expr(Env, Expr),
    {Env2, cerl:c_call(cerl:c_atom(erlang), cerl:c_atom(Kind), [ExprAST])};

gen_expr(Env, {nil, _}) ->
    {Env, cerl:c_nil()};
gen_expr(Env, #alpaca_cons{head=H, tail=T}) ->
    {Env2, H2} = gen_expr(Env, H),
    {Env3, T2} = gen_expr(Env2, T),
    {Env3, cerl:c_cons(H2, T2)};
gen_expr(Env, #alpaca_binary{segments=Segs}) ->
    {Env2, Bits} = gen_bits(Env, Segs),
    {Env2, cerl:c_binary(Bits)};
gen_expr(Env, #alpaca_map{is_pattern=true}=M) ->
    Annotated = annotate_map_type(M),
    F = fun(P, {E, Ps}) ->
                {E2, P2} = gen_expr(E, P),
                {E2, [P2|Ps]}
        end,
    {Env2, Pairs} = lists:foldl(F, {Env, []}, Annotated),
    {Env2, cerl:c_map_pattern(lists:reverse(Pairs))};
gen_expr(Env, #alpaca_map{}=M) ->
    %% If the map isn't a pattern we're not worried about underscores:
    Pairs = [PP || {_, PP} <- [gen_expr(Env, P) || P <- annotate_map_type(M)]],
    {Env, cerl:c_map(Pairs)};
gen_expr(Env, #alpaca_map_add{to_add=#alpaca_map_pair{key=K, val=V}, existing=B}) ->
    %% In R19 creating map expression like core erlang's parser does
    %% doesn't seem to work for me, neither with ann_c_map nor a simple
    %% c_map([ThePair|TheMap]).  The following seems fine and is mostly
    %% a convenience:
    {_, M} = gen_expr(Env, B),
    {_, KExp} = gen_expr(Env, K),
    {_, VExp} = gen_expr(Env, V),
    {Env, cerl:c_call(cerl:c_atom(maps), cerl:c_atom(put), [KExp, VExp, M])};
gen_expr(Env, #alpaca_map_pair{is_pattern=true, key=K, val=V}) ->
    {Env2, KExp} = gen_expr(Env, K),
    {Env3, VExp} = gen_expr(Env2, V),

    %% R19 has cerl:c_map_pair_exact/2 which is much more brief than
    %% the following but that doesn't work for 18.2 nor 18.3.
    %% The LFE source put me on to the following:
    {Env3, cerl:ann_c_map_pair([], cerl:abstract(exact), KExp, VExp)};
gen_expr(Env, #alpaca_map_pair{key=K, val=V}) ->
    {_, K2} = gen_expr(Env, K),
    {_, V2} = gen_expr(Env, V),
    {Env, cerl:c_map_pair(K2, V2)};
gen_expr(Env, #alpaca_record{}=R) ->
    {_, RExp} = gen_expr(Env, record_to_map(R)),
    {Env, RExp};
gen_expr(Env, #alpaca_record_transform{additions=Adds, existing=Existing}) ->
    F = fun(#alpaca_record_member{line=L, name=N, val=V}, {E, RExp}) ->
                Add = #alpaca_map_add{
                         to_add=#alpaca_map_pair{
                                   key={atom, L, atom_to_list(N)},
                                   val=V},
                         existing=RExp},
                {E, Add}
        end,
    {Env2, RecAst} = lists:foldl(F, {Env, Existing}, Adds),
    {_, RecExp} = gen_expr(Env2, RecAst),

    %% Generating the update as a sequence of map additions re-labels the
    %% structure as a map, here we're just moving it back to a record.
    {_, KExp} = gen_expr(Env2, {atom, 0, "__struct__"}),
    {_, VExp} = gen_expr(Env2, {atom, 0, "record"}),

    {Env2, cerl:c_call(
             cerl:c_atom(maps),
             cerl:c_atom(put),
             [KExp, VExp, RecExp])};

gen_expr(Env, #alpaca_type_check{type=is_string, expr={symbol, _, _}=S}) ->
    {_, Exp} = gen_expr(Env, S),
    TC = cerl:c_call(cerl:c_atom('erlang'), cerl:c_atom('is_binary'), [Exp]),
    {Env, TC};
gen_expr(Env, #alpaca_type_check{type=is_chars, expr={symbol, _, _}=S}) ->
    {_, Exp} = gen_expr(Env, S),
    TC = cerl:c_call(cerl:c_atom('erlang'), cerl:c_atom('is_list'), [Exp]),
    {Env, TC};
gen_expr(Env, #alpaca_type_check{type=T, expr={symbol, _, _}=S}) ->
    {_, Exp} = gen_expr(Env, S),
    TC = cerl:c_call(cerl:c_atom('erlang'), cerl:c_atom(T), [Exp]),
    {Env, TC};
gen_expr(Env, #alpaca_apply{expr={bif, _, _L, Module, FName}, args=Args}) ->
    Apply = cerl:c_call(
              cerl:c_atom(prefix_modulename(Module)),
              cerl:c_atom(FName),
              [A || {_, A} <- [gen_expr(Env, E) || E <- Args]]),
    {Env, Apply};
gen_expr(Env, #alpaca_apply{expr={Module, {symbol, _L, N}, _}, args=Args}) ->
    FName = cerl:c_atom(N),
    Apply = cerl:c_call(
              cerl:c_atom(prefix_modulename(Module)),
              FName,
              [A || {_, A} <- [gen_expr(Env, E) || E <- Args]]),
    {Env, Apply};
gen_expr(Env, #alpaca_apply{expr={symbol, _Line, Name}, args=[{unit, _}]}) ->
    FName = case proplists:get_value(Name, Env#env.module_funs) of
                undefined -> cerl:c_var(list_to_atom(Name));
                1 -> cerl:c_fname(list_to_atom(Name), 1)
            end,
    {Env, cerl:c_apply(FName, [cerl:c_atom(unit)])};
gen_expr(Env, #alpaca_apply{expr={symbol, L, Name}=FExpr, args=Args}) ->
    DesiredArity = length(Args),
    {FName, Curry, Arity} = case proplists:get_all_values(Name, Env#env.module_funs) of
        [] -> {cerl:c_var(list_to_atom(Name)), false, 0};
        AvailFuns ->
            %% If we have an exact arity match, use that, otherwise curry
            case lists:filter(fun(X) -> X =:= DesiredArity end, AvailFuns) of
                [A] -> {cerl:c_fname(list_to_atom(Name), A), false, A};
                _ ->
                    %% The typer ensures that we can curry unambiguously
                    [CurryArity] = lists:filter(fun(X) -> X > DesiredArity end, AvailFuns),
                    {cerl:c_fname(list_to_atom(Name), CurryArity), true, CurryArity}
            end
    end,
    case Curry of
        true -> %% generate an anonymous fun
           CurryFunName = "curry_fun_" ++ integer_to_list(Env#env.synthetic_fun_num),
           Env2 = Env#env{synthetic_fun_num=Env#env.synthetic_fun_num + 1},
           CArgs = lists:map(
               fun(A) ->
                    {symbol, L, "carg_" ++ integer_to_list(A)}
               end,
               lists:seq(DesiredArity+1, Arity)),
           CurryExpr = #alpaca_fun_def{
                             name={symbol, L, CurryFunName},
                             arity=DesiredArity,
                             versions=[#alpaca_fun_version{
                                          args=CArgs,
                                          body=#alpaca_apply{
                                            line=L,
                                            expr=FExpr,
                                            args=Args ++ CArgs}}]},
           Binding = #fun_binding{
                        expr={symbol, L, CurryFunName},
                        def=CurryExpr},

           gen_expr(Env2, Binding);

        false ->
            Apply = cerl:c_apply(
                        FName,
                        [A || {_, A} <- [gen_expr(Env, E) || E <- Args]]),
                        {Env, Apply}
    end;
gen_expr(Env, #alpaca_apply{expr={{symbol, _L, N}, Arity}, args=Args}) ->
    FName = cerl:c_fname(list_to_atom(N), Arity),
    Apply = cerl:c_apply(
              FName,
              [A || {_, A} <- [gen_expr(Env, E) || E <- Args]]),
    {Env, Apply};
gen_expr(Env, #alpaca_apply{line=L, expr=Expr, args=Args}) ->
    FunName = "synth_fun_" ++ integer_to_list(Env#env.synthetic_fun_num),
    Env2 = Env#env{synthetic_fun_num=Env#env.synthetic_fun_num + 1},
    case Expr of
        %% Detect far refs that require currying
        #alpaca_far_ref{arity=Arity} when Arity > length(Args) ->
            CArgs = lists:map(
               fun(A) ->
                    {symbol, L, "carg_" ++ integer_to_list(A)}
               end,
               lists:seq(length(Args)+1, Arity)),
               CurryExpr = #alpaca_fun_def{
                             name={symbol, L, FunName},
                             arity=length(Args),
                             versions=[#alpaca_fun_version{
                                          args=CArgs,
                                          body=#alpaca_apply{
                                            line=L,
                                            expr=Expr,
                                            args=Args ++ CArgs}}]},
               Binding = #fun_binding{
                        expr={symbol, L, FunName},
                        def=CurryExpr},
               gen_expr(Env2, Binding);
        _ ->
            SynthBinding = #var_binding{
                              name={symbol, L, FunName},
                              to_bind=Expr,
                              expr=#alpaca_apply{
                                        line=L, expr={symbol, L, FunName},
                                        args=Args}},

            gen_expr(Env2, SynthBinding)
    end;

gen_expr(Env, #alpaca_ffi{}=FFI) ->
    #alpaca_ffi{
       module=M,
       function_name=FN,
       args=Cons,
       clauses=Clauses} = FFI,

    {Env2, MExp} = gen_expr(Env, M),
    {Env3, FNExp} = gen_expr(Env2, FN),
    {Env4, ConsExp} = gen_expr(Env3, Cons),
    %% calling apply/3 with the compiled cons cell is simpler
    %% than unpacking the cons cell into an actual list of args:
    Apply = cerl:c_call(
              cerl:c_atom('erlang'),
              cerl:c_atom('apply'),
              [MExp, FNExp, ConsExp]),

    F = fun(C, {E, Cs}) ->
                {E2, C2} = gen_expr(E, C),
                {E2, [C2|Cs]}
        end,
    {Env5, Clauses2} = lists:foldl(F, {Env4, []}, Clauses),

    {Env5, cerl:c_case(Apply, lists:reverse(Clauses2))};

%% Pattern, expression
gen_expr(Env, #alpaca_clause{pattern=P, guards=[], result=E}) ->
    {Env2, PExp} = gen_expr(Env, P),
    {Env3, EExp} = gen_expr(Env2, E),
    {Env3, cerl:c_clause([PExp], EExp)};
gen_expr(Env, #alpaca_clause{pattern=P, guards=Gs, result=E}) ->
    NestG = fun(G, Acc) ->
                    {_, GExp} = gen_expr(Env, G),
                    cerl:c_call(
                      cerl:c_atom('erlang'),
                      cerl:c_atom('and'),
                      [GExp, Acc])
            end,
    F = fun([], G) -> G;
           (G, Acc) -> NestG(G, Acc)
        end,
    [H|T] = lists:reverse(Gs),
    {_, HExp} = gen_expr(Env, H),
    G = lists:foldl(F, HExp, T),

    {Env2, PExp} = gen_expr(Env, P),
    {Env3, EExp} = gen_expr(Env2, E),
    {Env3, cerl:c_clause([PExp], G, EExp)};

gen_expr(Env, #alpaca_tuple{values=Vs}) ->
    {Env2, Vs2} = lists:foldl(fun(V, {E, VV}) ->
                                      {E2, V2} = gen_expr(E, V),
                                      {E2, [V2|VV]}
                              end, {Env, []}, Vs),
    {Env2, cerl:c_tuple(lists:reverse(Vs2))};
gen_expr(Env, #alpaca_type_apply{name=#type_constructor{name=N}, arg=none}) ->
    {Env, cerl:c_atom(N)};
gen_expr(Env, #alpaca_type_apply{name=#type_constructor{name=N}, arg=A}) ->
    {Env2, AExp} = gen_expr(Env, A),
    {Env2, cerl:c_tuple([cerl:c_atom(N), AExp])};
%% Expressions, Clauses
gen_expr(Env, #alpaca_match{match_expr=Exp, clauses=Cs}) ->
    {Env2, EExp} = gen_expr(Env, Exp),
    {Env3, Cs2} = lists:foldl(fun(C, {E, CC}) ->
                                      {E2, C2} = gen_expr(E, C),
                                      {E2, [C2|CC]}
                              end, {Env2, []}, Cs),
    {Env3, cerl:c_case(EExp, lists:reverse(Cs2))};

gen_expr(Env, #alpaca_spawn{from_module=M,
                          module=undefined,
                          function={symbol, _, FN},
                          args=Args}) ->

    ArgCons = lists:foldl(fun(A, L) ->
                                  {_, AExp} = gen_expr(Env, A),
                                  cerl:c_cons(AExp, L)
                          end, cerl:c_nil(), lists:reverse(Args)),
    PrefixModuleName = prefix_modulename(M),
    {Env, cerl:c_call(
            cerl:c_atom('erlang'),
            cerl:c_atom('spawn'),
            [cerl:c_atom(PrefixModuleName), cerl:c_atom(FN), ArgCons])};

gen_expr(Env, #alpaca_receive{clauses=Cs, timeout_action=undefined}) ->
    {Env2, Cs2} = lists:foldl(fun(C, {E, CC}) ->
                                      {E2, C2} = gen_expr(E, C),
                                      {E2, [C2|CC]}
                              end, {Env, []}, Cs),
    {Env2, cerl:c_receive(lists:reverse(Cs2))};
gen_expr(Env, #alpaca_receive{
                 clauses=Cs,
                 timeout=TO,
                 timeout_action=TA}) ->
    X = case TO of
            infinity -> cerl:c_atom(TO);
            I -> cerl:c_int(I)
        end,
    {Env2, Cs2} = lists:foldl(fun(C, {E, CC}) ->
                                      {E2, C2} = gen_expr(E, C),
                                      {E2, [C2|CC]}
                              end, {Env, []}, Cs),
    {_, TA2} = gen_expr(Env, TA),
    {Env2, cerl:c_receive(lists:reverse(Cs2), X, TA2)};

gen_expr(Env, #alpaca_send{message=M, pid=P}) ->
    {_, PExp} = gen_expr(Env, P),
    {_, MExp} = gen_expr(Env, M),
    {Env, cerl:c_call(cerl:c_atom('erlang'), cerl:c_atom('!'), [PExp, MExp])};

gen_expr(#env{module_funs=Funs}=Env, #fun_binding{def=F, expr=E}) ->
    #alpaca_fun_def{name={symbol, _, N}, arity=Arity} = F,
    NewEnv = Env#env{module_funs=[{N, Arity}|Funs]},
    {_, Exp} = gen_expr(NewEnv, E),
    {Env, cerl:c_letrec([gen_fun(NewEnv, F)], Exp)};
gen_expr(Env, #var_binding{name={symbol, _, N}, to_bind=E1, expr=E2}) ->
    {_, E1Exp} = gen_expr(Env, E1),
    {_, E2Exp} = gen_expr(Env, E2),
    {Env, cerl:c_let([cerl:c_var(list_to_atom(N))], E1Exp, E2Exp)}.

module_info0(ModuleName) ->
    gen_module_info(ModuleName, []).

module_info1(ModuleName) ->
    gen_module_info(ModuleName, [cerl:c_var(item)]).

gen_module_info(ModuleName, Params) ->
    Body = cerl:c_call(cerl:c_atom(erlang),
                       cerl:c_atom(get_module_info),
                       [cerl:c_atom(ModuleName) | Params]),
    NewF = cerl:c_fun(Params, Body),
    {cerl:c_fname(module_info, length(Params)), NewF}.

gen_bits(Env, Segs) -> gen_bits(Env, Segs, []).

gen_bits(Env, [], AllSegs) ->
    {Env, lists:reverse(AllSegs)};
gen_bits(Env, [#alpaca_bits{type=T, default_sizes=true}=TailBits], Segs)
  when T == binary; T == utf8 ->
    #alpaca_bits{value=V, type=T, sign=Sign, endian=E} = TailBits,
    {Env2, VExp} = gen_expr(Env, V),
    B = cerl:c_bitstr(VExp, cerl:c_atom('all'), cerl:c_int(8),
                      get_bits_type(T), bits_flags(Sign, E)),
    {Env2, lists:reverse([B|Segs])};

gen_bits(Env,
         [#alpaca_bits{value={string, _, S}, type=utf8, default_sizes=true}|Rem],
         Segs) ->
    Lit = lists:reverse(literal_binary(S, utf8)),
    gen_bits(Env, Rem, Lit ++ Segs);

gen_bits(Env, [Bits|Rem], Memo) ->
    #alpaca_bits{value=V, size=S, unit=U, type=T, sign=Sign, endian=E} = Bits,
    {_Env2, VExp} = gen_expr(Env, V),
    B = cerl:c_bitstr(VExp, cerl:c_int(S), cerl:c_int(U),
                      get_bits_type(T), bits_flags(Sign, E)),
    gen_bits(Env, Rem, [B|Memo]).

get_bits_type(int) -> cerl:c_atom(integer);
get_bits_type(float) -> cerl:c_atom(float);
get_bits_type(utf8) -> cerl:c_atom(binary);
get_bits_type(binary) -> cerl:c_atom(binary).

bits_flags(Sign, Endian) ->
    cerl:c_cons(
      cerl:c_atom(Sign), cerl:c_cons(cerl:c_atom(Endian), cerl:c_nil())).

literal_binary(Chars, Encoding) when Encoding =:= utf8; Encoding =:= latin1 ->
    Bin = unicode:characters_to_binary(Chars, Encoding),
    F = fun(I) ->
                cerl:c_bitstr(
                  cerl:c_int(I), cerl:c_int(8), cerl:c_int(1),
                  cerl:c_atom(integer),
                  cerl:c_cons(cerl:c_atom(unsigned),
                              cerl:c_cons(cerl:c_atom(big), cerl:c_nil())))
        end,
    [F(I) || I <- binary_to_list(Bin)].

record_to_map(#alpaca_record{line=RL, is_pattern=Patt, members=Ms}) ->
    F = fun(#alpaca_record_member{name=N, val=V, line=L}) ->
                MapV = record_to_map(V),
                MapK = {atom, L, atom_to_list(N)},
                #alpaca_map_pair{line=L, is_pattern=Patt, key=MapK, val=MapV}
        end,
    #alpaca_map{is_pattern=Patt,
              structure=record,
              line=RL,
              pairs=lists:map(F, Ms)};
record_to_map(NotRecord) ->
    NotRecord.

annotate_map_type(#alpaca_map{is_pattern=IsP, structure=S, pairs=Ps}) ->
    V = {atom, 0, atom_to_list(S)},
    K = {atom, 0, "__struct__"},
    P = #alpaca_map_pair{is_pattern=IsP, key=K, val=V},
    [P|Ps].

-ifdef(TEST).

parse_and_gen(Code) ->
    {ok, [Mod]} = alpaca_ast_gen:make_modules([{?FILE, Code}]),
    {ok, Forms} = alpaca_codegen:gen(Mod, []),
    compile:forms(Forms, [report, verbose, from_core]).

simple_compile_test() ->
    Code =
        "module test_mod\n\n"
        "export add/2, sub/2\n"
        "let add x y = x + y\n"
        "let sub x y = x - y\n",
    {ok, _, _Bin} = parse_and_gen(Code).

module_with_internal_apply_test() ->
    Code =
        "module test_mod\n\n"
        "export add/2\n\n"
        "let adder x y = x + y\n\n"
        "let add x y = adder x y\n\n"
        "let eq x y = x == y",
    {ok, _, Bin} = parse_and_gen(Code).

infix_fun_test() ->
    Name = alpaca_infix_fun,
    FN = atom_to_list(Name) ++ ".beam",
    Code =
        "module infix_fun\n\n"
        "export adder/1 \n\n"
        "let (|>) v f = f v\n\n"
        "let add_ten x = x + 10\n\n"
        "let adder val = val |> add_ten",
    {ok, _, Bin} = parse_and_gen(Code),
    {module, Name} = code:load_binary(Name, FN, Bin),
    ?assertEqual(20, Name:adder(10)),
    true = code:delete(Name).

fun_and_var_binding_test() ->
    Name = alpaca_fun_and_var_binding,
    FN = atom_to_list(Name) ++ ".beam",
    Code =
        "module fun_and_var_binding\n\n"
        "export test_func/1\n\n"
        "let test_func x =\n"
        "  let y = x + 2 in\n"
        "  let double z = z + z in\n"
        "  double y",
    {ok, _, Bin} = parse_and_gen(Code),
    {module, Name} = code:load_binary(Name, FN, Bin),
    ?assertEqual(8, Name:test_func(2)),
    true = code:delete(Name).

value_test() ->
    Name = alpaca_value_function,
    FN = atom_to_list(Name) ++ ".beam",
    Code =
        "module value_function\n\n"
        "export test_func/1\n\n"
        "let test_int = 42\n\n"
        "let test_func () =\n"
        "  test_int\n\n",

    {ok, _, Bin} = parse_and_gen(Code),
    {module, Name} = code:load_binary(Name, FN, Bin),
    ?assertEqual(42, Name:test_func({})),
    true = code:delete(Name).

unit_function_test() ->
    Name = alpaca_unit_function,
    FN = atom_to_list(Name) ++ ".beam",
    Code =
        "module unit_function\n\n"
        "export test_func/1\n\n"
        "let test_func x =\n"
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
        "let add x y =\n"
        "  let adder1 a b = a + b in\n"
        "  let adder2 c d = adder1 c d in\n"
        "  adder2 x y",
    {ok, _, Bin} = parse_and_gen(Code).

%% This test will fail until I have implemented equality guards:
module_with_match_test() ->
    Name = alpaca_compile_module_with_match,
    FN = atom_to_list(Name) ++ ".beam",
    Code =
        "module compile_module_with_match\n\n"
        "export check/1, first/1, compare/2\n\n"
        "let check x = match x with\n"
        "  0 -> :zero\n"
        "| 1 -> :one\n"
        "| _ -> :more_than_one\n\n"
        "let first t =\n"
        "  match t with\n"
        "    (f, _) -> f\n"
        "  | _ -> :not_a_2_tuple\n\n"
    %% This is the failing section in particular:
        "let compare x y = match x with\n"
        "  a, a == y -> :matched\n"
        "| _ -> :not_matched",
    {ok, _, Bin} = parse_and_gen(Code),
    {module, Name} = code:load_binary(Name, FN, Bin),
    ?assertEqual(one, Name:check(1)),
    ?assertEqual(1, Name:first({1, a})),
    ?assertEqual(not_a_2_tuple, Name:first(an_atom)),
    ?assertEqual('matched', Name:compare(1, 1)),
    ?assertEqual('not_matched', Name:compare(1, 2)),
    true = code:delete(Name).

cons_test() ->
    Name = alpaca_compiler_cons_test,
    FN = atom_to_list(Name) ++ ".beam",
    Code =
        "module compiler_cons_test\n\n"
        "export make_list/2, my_map/2\n\n"
        "let make_list h t =\n"
        "  match t with\n"
        "    a :: b -> h :: t\n"
        "  | term -> h :: term :: []\n\n"
        "let my_map f x =\n"
        "  match x with\n"
        "    [] -> []\n"
        "  | h :: t -> (f h) :: (my_map f t)",
    {ok, _, Bin} = parse_and_gen(Code),
    {module, Name} = code:load_binary(Name, FN, Bin),
    ?assertEqual([1, 2], Name:make_list(1, 2)),
    ?assertEqual([1, 2, 3], Name:make_list(1, [2, 3])),
    ?assertEqual([2, 3], Name:my_map(fun(X) -> X+1 end, [1, 2])),
    ?assertEqual([3, 4], Name:my_map(fun(X) -> X+1 end, Name:make_list(2, 3))),
    true = code:delete(Name).

call_test() ->
    Code1 =
        "module call_test_a\n\n"
        "export a/1\n\n"
        "let a x = call_test_b.add x 1",
    Code2 =
        "module call_test_b\n\n"
        "export add/2\n\n"
        "let add x y = x + y",

    {ok, _, Bin1} = parse_and_gen(Code1),
    {ok, _, Bin2} = parse_and_gen(Code2),
    {module, alpaca_call_test_a} =
        code:load_binary(alpaca_call_test_a, "alpaca_call_test_a.beam", Bin1),
    {module, alpaca_call_test_b} =
        code:load_binary(alpaca_call_test_b, "alpaca_call_test_b.beam", Bin2),

    Name = alpaca_call_test_a,
    ?assertEqual(3, Name:a(2)),
    true = code:delete(alpaca_call_test_a),
    true = code:delete(alpaca_call_test_b).

ffi_test() ->
    Code =
        "module ffi_test\n\n"
        "export a/1\n\n"
        "let a x = beam :erlang :list_to_integer [x] with\n"
        "  1 -> :one\n"
        "| _ -> :not_one\n",
    {ok, _, Bin} = parse_and_gen(Code),
    {module, alpaca_ffi_test} = code:load_binary(alpaca_ffi_test,
                                                 "alpaca_ffi_test.beam", Bin),

    Mod = alpaca_ffi_test,
    ?assertEqual('one', Mod:a("1")),
    ?assertEqual('not_one', Mod:a("2")),
    true = code:delete(alpaca_ffi_test).

%% TODO:  with union types, test/1 should return integers and floats
%% just tagged with different type constructors.
type_guard_test() ->
    Code =
        "module type_guard_test\n\n"
        "export check/1\n\n"
        "let check x = \n"
        "beam :erlang :* [x, x] with\n"
        "   i, is_integer i -> i\n"
        " | f -> 0",
    {ok, _, Bin} = parse_and_gen(Code),
    Mod = alpaca_type_guard_test,
    {module, Mod} = code:load_binary(Mod, "alpaca_type_guard_test.beam", Bin),

    %% Checking that when the result is NOT an integer we're falling back
    %% to integer 0 as expected in the code above:
    ?assertEqual(4, Mod:check(2)),
    ?assertEqual(0, Mod:check(1.3)),
    true = code:delete(Mod).

multi_type_guard_test() ->
    Code =
        "module multi_type_guard_test\n\n"
        "export check/1\n\n"
        "let check x = \n"
        "beam :erlang :* [x, x] with\n"
        "   i, is_integer i, i == 4 -> :got_four\n"
        " | i, is_integer i, i > 5, i < 20 -> :middle\n"
        " | i, is_integer i -> :just_int\n"
        " | f -> :not_int",
    {ok, _, Bin} = parse_and_gen(Code),
    Mod = alpaca_multi_type_guard_test,
    {module, Mod} = code:load_binary(Mod, "alpaca_multi_type_guard_test.beam", Bin),

    ?assertEqual('got_four', Mod:check(2)),
    ?assertEqual('middle', Mod:check(4)),
    ?assertEqual('just_int', Mod:check(5)),
    ?assertEqual('not_int', Mod:check(1.3)),
    true = code:delete(Mod).

module_info_helpers_test() ->
    Code = "module module_info_helpers_test\n",
    {ok, _, Bin} = parse_and_gen(Code),
    Mod = alpaca_module_info_helpers_test,
    {module, Mod} = code:load_binary(Mod, "alpaca_module_info_helpers_test.beam", Bin),
    ?assertEqual(Mod, Mod:module_info(module)),
    ?assert(is_list(Mod:module_info())),
    true = code:delete(Mod).

curry_test() ->
    Code =
        "module autocurry\n"
        "export main\n"
        "let f x y = x + y\n"
        "let main () = \n"
        "  let f_ = f 5 in\n"
        "  f_ 6",
    {ok, _, Bin} = parse_and_gen(Code),
    Mod = alpaca_autocurry,
    {module, Mod} = code:load_binary(Mod, "alpaca_autocurry.beam", Bin),
    ?assertEqual(Mod:main(unit), 11),
    true = code:delete(Mod).

unit_as_value_test() ->
    Code =
        "module unit_test\n\n"
        "export return_unit/1\n\n"
        "let return_unit () = ()\n\n",
    {ok, _, Bin} = parse_and_gen(Code),
    Mod = alpaca_unit_test,
    {module, Mod} = code:load_binary(Mod, "alpaca_unit_test.beam", Bin),
    ?assertEqual({}, Mod:return_unit({})),
    true = code:delete(Mod).

-endif.
