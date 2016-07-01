-module(mlfe_ast_gen).
-export([parse/1, parse_module/2]).

%% Parse is used by other modules (particularly mlfe_typer) to make ASTs
%% from code that does not necessarily include a module:
-ignore_xref([parse/1]).

-include("mlfe_ast.hrl").

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

parse({ok, Tokens, _}) ->
    parse(Tokens);
parse(Tokens) when is_list(Tokens) ->
    mlfe_parser:parse(Tokens).

parse_module(NextVarNum, Text) when is_list(Text) ->
    {ok, Tokens, _} = scanner:scan(Text),
    rebind_and_validate_module(NextVarNum, parse_module(Tokens, #mlfe_module{}));

parse_module([], #mlfe_module{name=no_module}) ->
    {error, no_module_defined};
parse_module([], #mlfe_module{name=N, functions=Funs, types=Ts}=M) ->
    OrderedFuns = lists:reverse(Funs),
    TypesWithModule = [T#mlfe_type{module=N} || T <- Ts],
    {ok, M#mlfe_module{functions=OrderedFuns,
                       types = TypesWithModule}};
parse_module([{break, _}], Mod) ->
    parse_module([], Mod);
parse_module(Tokens, Mod) ->
    {NextBatch, Rem} = next_batch(Tokens, []),
    {ok, Parsed} = parse(NextBatch),
    case update_memo(Mod, Parsed) of
        {ok, NewMemo} ->
            parse_module(Rem, NewMemo);
        {error, Err} ->
            Err
    end.

rebind_and_validate_module(_, {error, _} = Err) ->
    Err;
rebind_and_validate_module(NextVarNum, {ok, #mlfe_module{}=Mod}) ->
    validate_user_types(rebind_and_validate_functions(NextVarNum, Mod)).

rebind_and_validate_functions(NextVarNum, #mlfe_module{
                                             name=MN,
                                             functions=Funs}=Mod) ->
    F = fun
            (_, {error, _}=Err) ->
                Err;
            (F, {NV, M, Memo}) ->
                case rename_bindings(NV, MN, F) of
                    {error, _}=Err ->
                        Err;
                    {NV2, M2, F2} ->
                        %% We invert the returned map so that it is from 
                        %% synthetic variable name to source code variable
                        %% name for later lookup:
                        Inverted = [{V, K}||{K, V} <- maps:to_list(M2)],
                        {NV2, maps:merge(M, maps:from_list(Inverted)), [F2|Memo]}
                end
        end,
    case lists:foldl(F, {NextVarNum, maps:new(), []}, Funs) of
        {error, _}=Err ->
            Err;
        {NV2, M, Funs2} ->
            %% TODO:  other parts of the compiler might care about that map
            {ok, NV2, M, Mod#mlfe_module{functions=lists:reverse(Funs2)}}
    end.

validate_user_types({error, _}=Err) ->
    Err;
validate_user_types({ok, _, _, #mlfe_module{types=Ts}}=Res) ->
    %% all type names unique

    NameCheck = unique_type_names(Ts),
    %% all type constructors unique
    ConstructorCheck = unique_type_constructors(NameCheck, Ts),

    %% I'm considering checking type variables here but might just leave
    %% it to the type checker itself.
    case ConstructorCheck of
        ok               -> Res;
        {error, _} = Err -> Err
    end.

%% check a list of things for duplicates with a comparison function and
%% a function for creating an error from one element.  The list must be sorted.
check_dupes([A|[B|_]=T], Compare, ErrorF) ->
    case Compare(A, B) of
        true -> ErrorF(A);
        false -> check_dupes(T, Compare, ErrorF)
    end;
check_dupes([_], _, _) ->
    ok;
check_dupes([], _, _) ->
    ok.

unique_type_names(Types) ->
    Names = lists:sort([N || #mlfe_type{name={type_name, _, N}} <- Types]),
    check_dupes(Names, 
                fun(A, B) -> A =:= B end, 
                fun(A) -> {error, {duplicate_type, A}} end).

unique_type_constructors({error, _}=Err, _) ->
    Err;
unique_type_constructors(_, Types) ->
    %% Get the sorted names of only the constructors:
    F = fun (#mlfe_constructor{name={_, _, N}}, Acc) -> [N|Acc];
            (_, Acc) -> Acc
        end,
    ToFlatten = [lists:foldl(F, [], Ms) || #mlfe_type{members=Ms} <- Types],
    %% can't lists:flatten here because strings are lists and we only want
    %% it flattened one level:
    Cs = lists:sort(lists:foldl(fun(A, B) -> A ++ B end, [], ToFlatten)),
    check_dupes(Cs,
                fun(A, B) -> A =:= B end, 
                fun(A) -> {error, {duplicate_constructor, A}} end).                

update_memo(#mlfe_module{name=no_module}=Mod, {module, Name}) ->
    {ok, Mod#mlfe_module{name=Name}};
update_memo(#mlfe_module{name=Name}, {module, DupeName}) ->
    {error, {module_rename, Name, DupeName}};
update_memo(#mlfe_module{type_imports=Imports}=M, #mlfe_type_import{}=I) ->
    {ok, M#mlfe_module{type_imports=Imports ++ [I]}};
update_memo(#mlfe_module{function_exports=Exports}=M, {export, Es}) ->
    {ok, M#mlfe_module{function_exports=Es ++ Exports}};
update_memo(#mlfe_module{functions=Funs}=M, #mlfe_fun_def{} = Def) ->
    {ok, M#mlfe_module{functions=[Def|Funs]}};
update_memo(#mlfe_module{types=Ts}=M, #mlfe_type{}=T) ->
    {ok, M#mlfe_module{types=[T|Ts]}};
update_memo(M, #mlfe_comment{}) ->
    {ok, M};
update_memo(_, Bad) ->
    {error, {"Top level requires defs, module, and export declarations", Bad}}.

%% Select a discrete batch of tokens to parse.  This basically wants a sequence
%% from the beginning of a top-level expression to a recognizable break between
%% it and the next discrete expression (e.g. two newlines).
next_batch([{break, _}|Rem], Memo) ->
    {lists:reverse(Memo), Rem};
%% TODO:  comments should get embedded in the AST for a "go fmt"-like tool as
%%        well as compiler-checked documentation.  This will require new fields
%%        in AST nodes.
next_batch([{comment_lines, _, _}|Rem], Memo) ->
    next_batch(Rem, Memo);
next_batch([{comment_line, _, _}|Rem], Memo) ->
    next_batch(Rem, Memo);
next_batch([], Memo) ->
    {lists:reverse(Memo), []};
next_batch([Token|Tail], Memo) ->
    next_batch(Tail, [Token|Memo]).

%%% Renaming bindings starts with a top-level function from a module and
%%% renames every binding _except_ for the top-level function name itself.
%%% This process is necessary in order to find duplicate definitions and
%%% later to restrict the scope of bindings while type checking.  An example:
%%% 
%%%     f x = let y = 2 in g x y
%%%     
%%%     g a b = let y = 4 in a + b + y
%%% 
%%% When `g` is type checked due to the call from `f`, `y` is already in the
%%% typing environment.  To eliminate potential confusion and to ensure 
%%% bindings are properly scoped we want to guarantee that the set of bindings
%%% for any two functions are disjoint.  The process of renaming bindings
%%% substitutes synthetic names for the original bindings and links these 
%%% names back to the originals via ETS.  We use a monotonic sequence of
%%% integers to create these names.

-spec rename_bindings(
        NextVar::integer(),
        MN::atom(),
        TopLevel::mlfe_fun_def()) -> {integer(), map(), mlfe_fun_def()} | 
                                     {error, term()}.
rename_bindings(NextVar, MN, #mlfe_fun_def{name={symbol, _, Name}, args=As}=TopLevel) ->
    SeedMap = #{Name => Name},
    case rebind_args(NextVar, MN, SeedMap, As) of
        {NV, M, Args} ->
            case rename_bindings(NV, MN, M, TopLevel#mlfe_fun_def.body) of
                {NV2, M2, E} -> {NV2, M2, TopLevel#mlfe_fun_def{
                                            body=E,
                                            args=Args}};
                {error, _} = Err -> Err
            end;
        {error, _} = E -> E
    end.

rebind_args(NextVar, _MN, Map, Args) ->
    F = fun
            ({error, _} = E, _) -> E;
            ({symbol, L, N}, {NV, AccMap, Syms}) -> 
                case maps:get(N, AccMap, undefined) of
                    undefined -> 
                        Synth = next_var(NV),
                        {NV+1, maps:put(N, Synth, AccMap), [{symbol, L, Synth}|Syms]};
                    _ ->
                        {error, {duplicate_definition, N, L}}
                end;
            ({unit, _}=U, {NV, AccMap, Syms}) ->
                {NV, AccMap, [U|Syms]}
        end,
    case lists:foldl(F, {NextVar, Map, []}, Args) of
        {NV, M, Args2} -> {NV, M, lists:reverse(Args2)};
        {error, _}=Err -> Err
    end.

rename_bindings(NextVar, MN, Map, #fun_binding{def=Def, expr=E}) ->
    case rename_bindings(NextVar, MN, Map, Def) of
        {error, _} = Err ->
            Err;
        {NV, M2, Def2} -> case rename_bindings(NV, MN, M2, E) of
                              {error, _} = Err -> Err;
                              {NV2, M3, E2} -> {NV2, 
                                                M3, 
                                                #fun_binding{def=Def2, expr=E2}}
                          end
    end;
rename_bindings(NV, MN, M, #mlfe_fun_def{name={symbol, L, Name}}=Def) ->
    #mlfe_fun_def{args=Args, body=Body} = Def,
    case maps:get(Name, M, undefined) of
        undefined ->
            Synth = next_var(NV),
            M2 = maps:put(Name, Synth, M),
            case rebind_args(NV+1, MN, M2, Args) of
                {error, _}=Err -> Err;
                {NV3, M3, Args2} -> case rename_bindings(NV3, MN, M3, Body) of
                                        {error, _}=Err -> Err;
                                        {NV4, M4, Body2} ->
                                            {NV4, M4, #mlfe_fun_def{
                                                         name={symbol, L, Synth},
                                                         args=Args2,
                                                         body=Body2}}
                                    end
            end;
        _ ->
            {error, {duplicate_definition, Name, L}}
    end;
rename_bindings(NextVar, MN, Map, #var_binding{}=VB) ->
    #var_binding{name={symbol, L, N},
                 to_bind=TB,
                 expr=E} = VB,
    case maps:get(N, Map, undefined) of
        undefined ->
            Synth = next_var(NextVar),
            M2 = maps:put(N, Synth, Map),
            case rename_bindings(NextVar+1, MN, M2, TB) of
                {error, _} = Err -> Err;
                {NV, M3, TB2} -> case rename_bindings(NV, MN, M3, E) of
                                     {error, _} = Err -> Err;
                                     {NV2, M4, E2} -> {NV2,
                                                       M4,
                                                       #var_binding{
                                                          name={symbol, L, Synth},
                                                          to_bind=TB2,
                                                          expr=E2}}
                                 end
            end;
        _ ->
            {error, {duplicate_definition, N, L}}
    end;

rename_bindings(NextVar, MN, Map, #mlfe_apply{name=N, args=Args}=App) ->
    FName = case N of
               {symbol, _, _} = S -> 
                    {_, _, X} = rename_bindings(NextVar, MN, Map, S),
                    X;
               _ -> N
           end,
    {_, _, Name} = rename_bindings(NextVar, MN, Map, FName),
    case rename_binding_list(NextVar, MN, Map, Args) of
        {error, _} = Err -> Err;
        {NV2, M2, Args2} ->
            {NV2, M2, App#mlfe_apply{name=Name, args=Args2}}
    end;

rename_bindings(NextVar, MN, Map, #mlfe_spawn{
                                     function=F,
                                     args=Args}=Spawn) ->
    {_, _, FName} = rename_bindings(NextVar, MN, Map, F),
    FArgs = [X||{_, _, X} <- [rename_bindings(NextVar, MN, Map, A)||A <- Args]],
    {NextVar, Map, Spawn#mlfe_spawn{
                     function=FName, 
                     from_module=MN,
                     args=FArgs}};

rename_bindings(NextVar, MN, Map, #mlfe_send{message=M, pid=P}=Send) ->
    {_, _, M2} = rename_bindings(NextVar, MN, Map, M),
    {_, _, P2} = rename_bindings(NextVar, MN, Map, P),
    {NextVar, Map, Send#mlfe_send{message=M2, pid=P2}};

rename_bindings(NextVar, _MN, Map, #mlfe_type_apply{arg=none}=A) ->
    {NextVar, Map, A};
rename_bindings(NextVar, MN, Map, #mlfe_type_apply{arg=Arg}=A) ->
    case rename_bindings(NextVar, MN, Map, Arg) of
        {error, _}=Err -> Err;
        {NV, M, Arg2} -> {NV, M, A#mlfe_type_apply{arg=Arg2}}
    end;
rename_bindings(NextVar, MN, Map, #mlfe_type_check{expr=E}=TC) ->
    case rename_bindings(NextVar, MN, Map, E) of
        {error, _}=Err -> Err;
        {NV, M, E2} -> {NV, M, TC#mlfe_type_check{expr=E2}}
    end;

rename_bindings(NextVar, MN, Map, #mlfe_cons{head=H, tail=T}=Cons) ->
    case rename_bindings(NextVar, MN, Map, H) of
        {error, _} = Err -> Err;
        {NV, M, H2} -> case rename_bindings(NV, MN, M, T) of
                           {error, _} = Err -> Err;
                           {NV2, M2, T2} -> {NV2, M2, Cons#mlfe_cons{
                                                        head=H2,
                                                        tail=T2}}
                       end
    end;
rename_bindings(NextVar, MN, Map, #mlfe_tuple{values=Vs}=T) ->
    case rename_binding_list(NextVar, MN, Map, Vs) of
        {error, _} = Err -> Err;
        {NV, M, Vals2} -> {NV, M, T#mlfe_tuple{values=Vals2}}
    end;
rename_bindings(NextVar, _MN, Map, {symbol, L, N}=S) ->
    case maps:get(N, Map, undefined) of
        undefined -> {NextVar, Map, S};
        Synthetic -> {NextVar, Map, {symbol, L, Synthetic}}
    end;
rename_bindings(NV, MN, M, #mlfe_ffi{args=Args, clauses=Cs}=FFI) ->
    case rename_bindings(NV, MN, M, Args) of
        {error, _} = Err -> Err;
        {NV2, M2, Args2} -> case rename_clause_list(NV2, MN, M2, Cs) of
                                {error, _} = Err -> 
                                    Err;
                                {NV3, M3, Cs2} ->
                                    {NV3, M3, FFI#mlfe_ffi{args=Args2, clauses=Cs2}}
                            end
    end;
rename_bindings(NV, MN, M, #mlfe_match{}=Match) ->
    #mlfe_match{match_expr=ME, clauses=Cs} = Match,
    case rename_bindings(NV, MN, M, ME) of
        {error, _} = Err -> Err;
        {NV2, M2, ME2} -> 
            case rename_clause_list(NV2, MN, M2, Cs) of
                {error, _} = Err -> 
                    Err;
                {NV3, M3, Cs2} -> 
                    {NV3, M3, Match#mlfe_match{match_expr=ME2, clauses=Cs2}}
            end
    end;

rename_bindings(NV, MN, M, #mlfe_receive{clauses=Cs}=Recv) ->
    case rename_clause_list(NV, MN, M, Cs) of
        {error, _} = Err -> Err;
        {NV2, M2, Cs2}   -> {NV2, M2, Recv#mlfe_receive{clauses=Cs2}}
    end;

rename_bindings(NV, MN, M, #mlfe_clause{pattern=P, guards=Gs, result=R}=Clause) ->
    %% pattern matches create new bindings and as such we don't
    %% just want to use existing substitutions but rather error
    %% on duplicates and create entirely new ones:
    case make_bindings(NV, M, P) of
        {error, _} = Err -> Err;
        {NV2, M2, P2} -> 
            case rename_bindings(NV2, MN, M2, R) of
                {error, _} = Err -> Err;
                {NV3, M3, R2} -> 
                    case rename_binding_list(NV3, MN, M3, Gs) of
                        {error, _}=Err -> Err;
                        {NV4, _M4, Gs2} ->
                    
                            %% we actually throw away the modified map here
                            %% because other patterns should be able to 
                            %% reuse variable names:
                            {NV4, M, Clause#mlfe_clause{
                                       pattern=P2,
                                       guards=Gs2,
                                       result=R2}}
                    end
            end
    end;
rename_bindings(NextVar, _MN, Map, Expr) ->
    {NextVar, Map, Expr}.

rename_binding_list(NextVar, MN, Map, Bindings) ->
    F = fun
            (_, {error, _} = Err) -> Err;
            (A, {NV, M, Memo})    -> case rename_bindings(NV, MN, M, A) of
                                         {error, _} = Err -> Err;
                                         {NV2, M2, A2} -> {NV2, M2, [A2|Memo]}
                                     end
        end,
    case lists:foldl(F, {NextVar, Map, []}, Bindings) of
        {error, _} = Err -> Err;
        {NV, M, Bindings2} -> {NV, M, lists:reverse(Bindings2)}
    end.

%% For renaming bindings in a list of clauses.  Broken out from pattern
%% matching because it will be reused for FFI and receive.
rename_clause_list(NV, MN, M, Cs) ->
    F = fun
            (_, {error, _}=Err) -> Err;
            (C, {X, Y, Memo}) ->
                case rename_bindings(X, MN, Y, C) of
                    {error, _} = Err -> Err;
                    {A, B, C2} -> {A, B, [C2|Memo]}
                end
        end,
    case lists:foldl(F, {NV, M, []}, Cs) of
        {error, _} = Err -> Err;
        {NV2, M2, Cs2} -> {NV2, M2, lists:reverse(Cs2)}
    end.    

%%% Used for pattern matches so that we're sure that the patterns in each
%%% clause contain unique bindings.
make_bindings(NV, M, #mlfe_tuple{values=Vs}=Tup) ->
    F = fun
            (_, {error, _}=E) -> E;
            (V, {NextVar, Map, Memo}) ->
                case make_bindings(NextVar, Map, V) of
                    {error, _} = Err -> Err;
                    {NV2, M2, V2} -> {NV2, M2, [V2|Memo]}
                end
        end,
    case lists:foldl(F, {NV, M, []}, Vs) of
        {error, _} = Err -> Err;
        {NV2, M2, Vs2}   -> {NV2, M2, Tup#mlfe_tuple{values=lists:reverse(Vs2)}}
    end;
make_bindings(NV, M, #mlfe_cons{head=H, tail=T}=Cons) ->
    case make_bindings(NV, M, H) of
        {error, _} = Err -> Err;
        {NV2, M2, H2} -> case make_bindings(NV2, M2, T) of
                             {error, _} = Err -> 
                                 Err;
                             {NV3, M3, T2} -> 
                                 {NV3, M3, Cons#mlfe_cons{head=H2, tail=T2}}
                         end
    end;
make_bindings(NV, M, {symbol, L, Name}) ->
    case maps:get(Name, M, undefined) of
        undefined ->
            Synth = next_var(NV),
            {NV+1, maps:put(Name, Synth, M), {symbol, L, Synth}};
        _ ->
            {error, {duplicate_definition, Name, L}}
    end;
make_bindings(NV, M, Expression) ->
    {NV, M, Expression}.
                                
-define(base_var_name, "svar_").
next_var(X) ->
    ?base_var_name ++ integer_to_list(X).

-ifdef(TEST).

test_parse(S) ->
    parse(scanner:scan(S)).

symbols_test_() ->
    [?_assertMatch({ok, {symbol, 1, "oneSymbol"}}, 
                   parse(scanner:scan("oneSymbol")))
    ].

user_types_test_() ->
    [?_assertMatch({ok, #mlfe_type{name={type_name, 1, "t"}, 
                                   vars=[],
                                   members=[t_int,
                                            #mlfe_constructor{
                                               name={type_constructor, 1, "A"},
                                               arg=t_int}]}},
                   test_parse("type t = int | A int")),
     ?_assertMatch({ok, #mlfe_type{
                          name={type_name, 1, "my_list"},
                          vars=[{type_var, 1, "x"}],
                          members=[#mlfe_constructor{
                                     name={type_constructor, 1, "Nil"},
                                     arg=none},
                                   #mlfe_constructor{
                                      name={type_constructor, 1, "Cons"},
                                      arg=#mlfe_type_tuple{
                                             members=[{type_var, 1, "x"},
                                                      #mlfe_type{
                                                         name={type_name, 1, "my_list"},
                                                         vars=[{type_var, 1, "x"}]}]}
                                     }]}},
                   test_parse("type my_list 'x = Nil | Cons ('x, my_list 'x)")),
     ?_assertMatch({error, {duplicate_type, "t"}},
                   parse_module(0, 
                                "module dupe_types_1\n\n"
                                "type t = A | B\n\n"
                                "type t = C | int")),
     ?_assertMatch({error, {duplicate_constructor, "A"}},
                   parse_module(0,
                                "module dupe_type_constructor\n\n"
                                "type t = A int | B\n\n"
                                "type u = X float | A\n\n")),
     %% Making sure multiple type variables work here:
     ?_assertMatch({ok, #mlfe_type{
                           name={type_name, 1, "either"},
                           vars=[{type_var, 1, "a"}, {type_var, 1, "b"}],
                           members=[#mlfe_constructor{
                                       name={type_constructor, 1, "Left"},
                                       arg={type_var, 1, "a"}
                                      },
                                    #mlfe_constructor{
                                       name={type_constructor, 1, "Right"},
                                       arg={type_var, 1, "b"}
                                      }]
                          }},
                   test_parse("type either 'a 'b = Left 'a | Right 'b"))
    ].

defn_test_() ->
    [
     %% TODO:  I'm not sure if I want to allow nullary functions
     %% at the top level when they're not allowed in let forms.
     %% Strikes me as potentially quite confusing.
     ?_assertMatch({ok, #mlfe_fun_def{name={symbol, 1, "x"},
                                      args=[], 
                                      body={int, 1, 5}}},
                   parse(scanner:scan("x=5"))),
     ?_assertMatch({ok, #mlfe_fun_def{name={symbol, 1, "double"}, 
                                       args=[{symbol, 1, "x"}],
                                       body=#mlfe_apply{
                                               type=undefined,
                                               name={bif, '+', 1, erlang, '+'}, 
                                               args=[{symbol, 1, "x"},
                                                     {symbol, 1, "x"}]}}},
                  parse(scanner:scan("double x = x + x"))),
     ?_assertMatch({ok, #mlfe_fun_def{name={symbol, 1, "add"}, 
                                      args=[{symbol, 1, "x"}, {symbol, 1, "y"}],
                                      body=#mlfe_apply{
                                              type=undefined,
                                              name={bif, '+', 1, erlang, '+'},
                                              args=[{symbol, 1, "x"},
                                                    {symbol, 1, "y"}]}}},
                   parse(scanner:scan("add x y = x + y")))
    ].

float_math_test_() ->
    [?_assertMatch({ok, #mlfe_apply{name={bif, '+', 1, erlang, '+'}}},
                   parse(scanner:scan("2 + 1"))),
     ?_assertMatch({ok, #mlfe_apply{name={bif, '+.', 1, erlang, '+'}}},
                   parse(scanner:scan("2.0 +. 1.3")))
    ].

let_binding_test_() ->
    [?_assertMatch({ok, #fun_binding{
                           def=#mlfe_fun_def{
                                  name={symbol, 1, "double"}, 
                                  args=[{symbol, 1, "x"}],
                                  body=#mlfe_apply{
                                          type=undefined,
                                          name={bif, '+', 1, erlang, '+'},
                                          args=[{symbol, 1, "x"},
                                                {symbol, 1, "x"}]}},
                           expr=#mlfe_apply{
                                   name={symbol, 1, "double"}, 
                                   args=[{int, 1, 2}]}}}, 
                   parse(scanner:scan("let double x = x + x in double 2"))),
     ?_assertMatch({ok, #var_binding{
                           name={symbol, 1, "x"},
                           to_bind=#mlfe_apply{
                                      name={symbol, 1, "double"},
                                      args=[{int, 1, 2}]},
                           expr=#mlfe_apply{
                                   name={symbol, 1, "double"},
                                   args=[{symbol, 1, "x"}]}}},
                    parse(scanner:scan("let x = double 2 in double x"))),
     ?_assertMatch({ok, #mlfe_fun_def{
                           name={symbol, 1, "doubler"}, 
                           args=[{symbol, 1, "x"}],
                           body=#fun_binding{
                                   def=#mlfe_fun_def{
                                          name={symbol, 2, "double"}, 
                                          args=[{symbol, 2, "x"}],
                                          body=#mlfe_apply{
                                                  type=undefined, 
                                                  name={bif, '+', 2, erlang, '+'}, 
                                                  args=[{symbol, 2, "x"}, 
                                                        {symbol, 2, "x"}]}},
                                   expr=#mlfe_apply{
                                           name={symbol, 3, "double"},
                                           args=[{int, 3, 2}]}}}}, 
                   parse(scanner:scan(
                           "doubler x =\n"
                           "  let double x = x + x in\n"
                           "  double 2"))),
     ?_assertMatch({ok, #mlfe_fun_def{
                           name={symbol,1,"my_fun"},
                           args=[{symbol,1,"x"},{symbol,1,"y"}],
                           body=#fun_binding{
                                   def=#mlfe_fun_def{
                                          name={symbol,1,"xer"},
                                          args=[{symbol,1,"a"}],
                                          body=#mlfe_apply{
                                                  type=undefined,
                                                  name={bif, '+', 1, erlang, '+'},
                                                  args=[{symbol,1,"a"},
                                                        {symbol,1,"a"}]}},
                                   expr=#fun_binding{
                                           def=#mlfe_fun_def{
                                                  name={symbol,1,"yer"},
                                                  args=[{symbol,1,"b"}],
                                                  body=#mlfe_apply{
                                                          type=undefined,
                                                          name={bif, '+', 1, erlang, '+'},
                                                          args=[{symbol,1,"b"},
                                                                {symbol,1,"b"}]}},
                                           expr=#mlfe_apply{
                                                   type=undefined,
                                                   name={bif, '+', 1, erlang, '+'},
                                                   args=[#mlfe_apply{
                                                            name={symbol,1,"xer"},
                                                            args=[{symbol,1,"x"}]},
                                                         #mlfe_apply{
                                                            name={symbol,1,"yer"},
                                                            args=[{symbol,1,"y"}]}]}}}}},
                   parse(scanner:scan(
                           "my_fun x y ="
                           "  let xer a = a + a in"
                           "  let yer b = b + b in"
                           "  (xer x) + (yer y)")))
    ].

application_test_() ->
    [?_assertMatch({ok, #mlfe_apply{name={symbol, 1, "double"},
                                    args=[{int, 1, 2}]}},
                  parse(scanner:scan("double 2"))),
     ?_assertMatch({ok, #mlfe_apply{name={symbol, 1, "two"}, 
                                    args=[{symbol, 1, "symbols"}]}},
                   parse(scanner:scan("two symbols"))),
     ?_assertMatch({ok, #mlfe_apply{name={symbol, 1, "x"}, 
                                    args=[{symbol, 1, "y"}, {symbol, 1, "z"}]}},
                   parse(scanner:scan("x y z"))),
     ?_assertMatch({ok, {error, {invalid_fun_application,
                            {int, 1, 1},
                           [{symbol, 1, "x"}, {symbol, 1, "y"}]}}},
                    parse(scanner:scan("1 x y"))),
     ?_assertMatch({ok, #mlfe_apply{
                           name={'module', {symbol, 1, "fun"}, 2},
                           args=[{int, 1, 1}, {symbol, 1, "x"}]}},
                   parse(scanner:scan("module.fun 1 x")))
    ].

module_def_test_() ->
    [?_assertMatch({ok, {module, 'test_mod'}}, 
                   parse(scanner:scan("module test_mod"))),
     ?_assertMatch({ok, {module, 'myMod'}}, 
                   parse(scanner:scan("module myMod")))
    ].

export_test_() ->
    [?_assertMatch({ok, {export, [{"add", 2}]}},
                  parse(scanner:scan("export add/2")))
    ].

expr_test_() ->
    [?_assertMatch({ok, {int, 1, 2}}, parse(scanner:scan("2"))),
     ?_assertMatch({ok, #mlfe_apply{type=undefined,
                                    name={bif, '+', 1, erlang, '+'}, 
                                    args=[{int, 1, 1}, 
                                          {int, 1, 5}]}},
                  parse(scanner:scan("1 + 5"))),
     ?_assertMatch({ok, #mlfe_apply{name={symbol, 1, "add"}, 
                                    args=[{symbol, 1, "x"},
                                          {int, 1, 2}]}},
                   parse(scanner:scan("add x 2"))),
     ?_assertMatch({ok, 
                    #mlfe_apply{name={symbol, 1, "double"},
                                args=[{symbol, 1, "x"}]}}, 
                   parse(scanner:scan("(double x)"))),
     ?_assertMatch({ok, #mlfe_apply{
                           name={symbol, 1, "tuple_func"},
                           args=[#mlfe_tuple{
                                    arity=2,
                                    values=[{symbol, 1, "x"}, 
                                            {int, 1, 1}]},
                                 {symbol, 1, "y"}]}},
                   parse(scanner:scan("tuple_func (x, 1) y")))
    ].

module_with_let_test() ->
    Code =
        "module test_mod\n\n"
        "export add/2\n\n"
        "add x y =\n"
        "  let adder a b = a + b in\n"
        "  adder x y",
    ?assertMatch({ok, _, _,
                  #mlfe_module{
                     name='test_mod',
                     function_exports=[{"add",2}],
                     functions=[
                                #mlfe_fun_def{
                                   name={symbol,5,"add"},
                                   args=[{symbol,5,"svar_0"},{symbol,5,"svar_1"}],
                                   body=#fun_binding{
                                           def=#mlfe_fun_def{
                                                  name={symbol,6,"svar_2"},
                                                  args=[{symbol,6,"svar_3"},
                                                        {symbol,6,"svar_4"}],
                                                  body=#mlfe_apply{
                                                          type=undefined,
                                                          name={bif, '+', 6, erlang, '+'},
                                                          args=[{symbol,6,"svar_3"},
                                                                {symbol,6,"svar_4"}]}},
                                           expr=#mlfe_apply{
                                                   name={symbol,7,"svar_2"},
                                                   args=[{symbol,7,"svar_0"},
                                                         {symbol,7,"svar_1"}]}}}]}},
                  parse_module(0, Code)).

match_test_() ->
    [?_assertMatch({ok, #mlfe_match{match_expr={symbol, 1, "x"},
                                    clauses=[#mlfe_clause{
                                                pattern={int, 2, 0}, 
                                                result={symbol, 2, "zero"}},
                                             #mlfe_clause{
                                                pattern={'_', 3}, 
                                                result={symbol, 3, "non_zero"}}]}},
                   parse(scanner:scan(
                           "match x with\n"
                           " 0 -> zero\n"
                           "| _ -> non_zero\n"))),
     ?_assertMatch({ok, #mlfe_match{match_expr=#mlfe_apply{
                                                  name={symbol, 1, "add"}, 
                                                  args=[{symbol, 1, "x"}, 
                                                        {symbol, 1, "y"}]},
                                    clauses=[#mlfe_clause{pattern={int, 2, 0}, 
                                                          result={atom, 2, "zero"}},
                                             #mlfe_clause{pattern={int, 3, 1}, 
                                                          result={atom, 3, "one"}},
                                             #mlfe_clause{pattern={'_', 4}, 
                                                          result={atom, 4, 
                                                                  "more_than_one"}}
                         ]}},
                   parse(scanner:scan(
                           "match add x y with\n"
                           " 0 -> :zero\n"
                           "| 1 -> :one\n"
                           "| _ -> :more_than_one\n"))),
     ?_assertMatch({ok, #mlfe_match{
                           match_expr={symbol, 1, "x"},
                           clauses=[#mlfe_clause{
                                       pattern=#mlfe_tuple{
                                                   arity=2,
                                                   values=[{'_', 2}, 
                                                           {symbol, 2, "x"}]},
                                                result={atom, 2, "anything_first"}},
                                    #mlfe_clause{
                                       pattern=#mlfe_tuple{
                                                  arity=2,
                                                  values=[{int, 3, 1}, 
                                                          {symbol, 3, "x"}]},
                                       result={atom, 3, "one_first"}}]}},
                   parse(scanner:scan(
                           "match x with\n"
                           "  (_, x) -> :anything_first\n"
                           "| (1, x) -> :one_first\n"))),
     ?_assertMatch({ok, #mlfe_match{
                           match_expr=#mlfe_tuple{
                                         arity=2, 
                                         values=[{symbol, 1, "x"}, 
                                                 {symbol, 1, "y"}]},
                           clauses=[#mlfe_clause{
                                       pattern=#mlfe_tuple{
                                                  arity=2,
                                                  values=[#mlfe_tuple{
                                                             arity=2,
                                                             values=[{'_', 2}, 
                                                                     {int, 2, 1}]},
                                                          {symbol, 2, "a"}]},
                                       result={atom, 2, "nested_tuple"}}]}},
                   parse(scanner:scan(
                           "match (x, y) with\n"
                           " ((_, 1), a) -> :nested_tuple")))
    ].

tuple_test_() ->
    %% first no unary tuples:
    [?_assertMatch({ok, {int, 1, 1}}, parse(scanner:scan("(1)"))),
     ?_assertMatch({ok, #mlfe_tuple{arity=2, 
                                    values=[{int, 1, 1}, {int, 1, 2}]}},
                   parse(scanner:scan("(1, 2)"))),
     ?_assertMatch({ok, #mlfe_tuple{arity=2,
                                    values=[{symbol, 1, "x"}, {int, 1, 1}]}},
                   parse(scanner:scan("(x, 1)"))),
     ?_assertMatch({ok, #mlfe_tuple{
                           arity=2, 
                           values=[#mlfe_tuple{arity=2, 
                                               values=[{int, 1, 1}, 
                                                       {symbol, 1, "x"}]},
                                 {int, 1, 12}]}},
                   parse(scanner:scan("((1, x), 12)")))
    ].

list_test_() ->
    [?_assertMatch({ok, #mlfe_cons{head={int, 1, 1}, 
                                   tail=#mlfe_cons{
                                          head={int, 1, 2},
                                          tail=#mlfe_cons{
                                                  head={int, 1, 3},
                                                  tail={nil, 0}}}}},
                   test_parse("[1, 2, 3]")),
     ?_assertMatch({ok, {nil, 1}}, parse(scanner:scan("[]"))),
     ?_assertMatch({ok, #mlfe_cons{head={int, 1, 1}, tail={nil, 1}}},
                   parse(scanner:scan("[1]"))),
     ?_assertMatch({ok, #mlfe_cons{
                           head={symbol, 1, "x"},
                           tail=#mlfe_cons{head={int, 1, 1}, 
                                           tail={nil, 1}}}},
                   parse(scanner:scan("x :: [1]"))),
     ?_assertMatch({ok, #mlfe_cons{head={int, 1, 1},
                                   tail={symbol, 1, "y"}}},
                   parse(scanner:scan("1 :: y"))),
     ?_assertMatch({ok, #mlfe_match{
                           match_expr={symbol,1,"x"},
                           clauses=[#mlfe_clause{pattern={nil,2},
                                                 result={nil,2}},
                                    #mlfe_clause{pattern=#mlfe_cons{
                                                            head={symbol,3,"h"},
                                                            tail={symbol,3,"t"}},
                                                 result={symbol,3,"h"}}]}},
                   parse(scanner:scan(
                           "match x with\n"
                           "  [] -> []\n"
                           "| h :: t -> h\n")))
    ].

string_test_() ->
    [?_assertMatch({ok, {string, 1, "Hello world"}}, test_parse("\"Hello world\""))%,
%     ?_assertMatch({ok, {string, 1, "Nested \" quotes"}},
%                   test_parse("\"Nested " "\"" " quotes\""))
    ].

ffi_test_() ->                         
    [?_assertMatch({ok, #mlfe_ffi{
                          module={atom, 1, "io"},
                          function_name={atom, 1, "format"},
                          args=#mlfe_cons{
                                  head={string, 1, "One is ~s~n"},
                                  tail=#mlfe_cons{
                                          head=#mlfe_cons{
                                                   head={int, 1, 1},
                                                   tail={nil, 1}},
                                          tail={nil, 0}}}}},
                   test_parse(
                     "call_erlang :io :format [\"One is ~s~n\", [1]] with\n"
                     " _ -> 0"))
    ].

simple_module_test() ->
    Code =
        "module test_mod\n\n"
        "export add/2, sub/2\n\n"
        "adder x y = x + y\n\n"
        "add1 x = adder x 1\n\n"
        "add x y = adder x y\n\n"
        "sub x y = x - y",
    ?assertMatch({ok, _, _, #mlfe_module{
                         name='test_mod',
                         function_exports=[{"add",2},{"sub",2}],
                         functions=[
                                    #mlfe_fun_def{
                                       name={symbol, 5, "adder"},
                                       args=[{symbol, 5, "svar_0"},
                                             {symbol,5 , "svar_1"}],
                                       body=#mlfe_apply{type=undefined,
                                                        name={bif, '+', 5, erlang, '+'},
                                                        args=[{symbol, 5, "svar_0"},
                                                              {symbol,5,"svar_1"}]}},
                                    #mlfe_fun_def{
                                       name={symbol,7,"add1"},
                                       args=[{symbol,7,"svar_2"}],
                                       body=#mlfe_apply{name={symbol,7,"adder"},
                                                        args=[{symbol,7,"svar_2"},
                                                              {int,7,1}]}},
                                     #mlfe_fun_def{
                                        name={symbol,9,"add"},
                                        args=[{symbol,9,"svar_3"},{symbol,9,"svar_4"}],
                                        body=#mlfe_apply{name={symbol,9,"adder"},
                                                         args=[{symbol,9,"svar_3"},
                                                               {symbol,9,"svar_4"}]}},
                                    #mlfe_fun_def{
                                       name={symbol,11,"sub"},
                                       args=[{symbol,11,"svar_5"},{symbol,11,"svar_6"}],
                                       body=#mlfe_apply{type=undefined,
                                                        name={bif, '-', 11, erlang, '-'},
                                                        args=[{symbol,11,"svar_5"},
                                                              {symbol,11,"svar_6"}]}}]}},
                 parse_module(0, Code)).

rebinding_test_() ->
    %% Simple rebinding:
    {ok, A} = test_parse("f x = let y = 2 in x + y"),
    %% Check for duplicate definition error:
    {ok, B} = test_parse("f x = \nlet x = 1 in x + x"),
    %% Check for good pattern match variable names:
    {ok, C} = test_parse("f x = match x with\n"
                         "  (a, 0) -> a\n"
                         "| (a, b) -> b"),
    %% Check for duplication in pattern match variable names:
    {ok, D} = test_parse("f x = match x with\n"
                         " x -> 0"),
    %% Check for good pattern match variable names in lists:
    {ok, E} = test_parse("f x = match x with\n"
                         "  [_, b, 0] -> b\n"
                         "| h :: t -> h"),
    %% Check for dupe variable names in lists:
    {ok, F} = test_parse("f x y = match x with\n"
                         " h :: y -> h"),

    [?_assertMatch({_, _, #mlfe_fun_def{
                            name={symbol, 1, "f"},
                            args=[{symbol, 1, "svar_0"}],
                            body=#var_binding{
                                    name={symbol, 1, "svar_1"},
                                    to_bind={int, 1, 2},
                                    expr=#mlfe_apply{
                                            name={bif, '+', 1, 'erlang', '+'},
                                            args=[{symbol, 1, "svar_0"}, 
                                                  {symbol, 1, "svar_1"}]}}}},
                   rename_bindings(0, undefined, A)),
     ?_assertMatch({error, {duplicate_definition, "x", 2}},
                   rename_bindings(0, undefined, B)),
     ?_assertMatch({_, _, #mlfe_fun_def{
                             name={symbol, 1, "f"},
                             args=[{symbol, 1, "svar_0"}],
                             body=#mlfe_match{
                                     match_expr={symbol, 1, "svar_0"},
                                     clauses=[#mlfe_clause{
                                                 pattern=#mlfe_tuple{
                                                            values=[{symbol, 2, "svar_1"},
                                                                    {int, 2, 0}]},
                                                 result={symbol, 2, "svar_1"}},
                                              #mlfe_clause{
                                                 pattern=#mlfe_tuple{
                                                            values=[{symbol, 3, "svar_2"},
                                                                    {symbol, 3, "svar_3"}]},
                                                 result={symbol, 3, "svar_3"}}]}}},
                   rename_bindings(0, undefined, C)),
     ?_assertMatch({error, {duplicate_definition, "x", 2}}, 
                   rename_bindings(0, undefined, D)),
     ?_assertMatch({_, _, 
                    #mlfe_fun_def{
                       body=#mlfe_match{
                               match_expr={symbol, 1, "svar_0"},
                               clauses=[#mlfe_clause{
                                           pattern=#mlfe_cons{
                                                      head={'_', 2},
                                                      tail=#mlfe_cons{
                                                              head={symbol, 2, "svar_1"},
                                                              tail=#mlfe_cons{
                                                                      head={int, 2, 0},
                                                                      tail={nil, 0}}}},
                                           result={symbol, 2, "svar_1"}},
                                       #mlfe_clause{
                                          pattern=#mlfe_cons{
                                                     head={symbol, 3, "svar_2"},
                                                     tail={symbol, 3, "svar_3"}},
                                          result={symbol, 3, "svar_2"}}]}}}, 
                   rename_bindings(0, undefined, E)),
     ?_assertMatch({error, {duplicate_definition, "y", 2}}, 
                   rename_bindings(0, undefined, F))
    ].

-endif.
