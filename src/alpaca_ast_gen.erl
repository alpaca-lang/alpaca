%%% -*- mode: erlang;erlang-indent-level: 4;indent-tabs-mode: nil -*-
%%% ex: ft=erlang ts=4 sw=4 et
-module(alpaca_ast_gen).
-export([parse/1, parse_module/2]).

%% Parse is used by other modules (particularly alpaca_typer) to make ASTs
%% from code that does not necessarily include a module:
-ignore_xref([parse/1]).

-include("alpaca_ast.hrl").

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

parse({ok, Tokens, _}) ->
    parse(Tokens);
parse(Tokens) when is_list(Tokens) ->
    alpaca_parser:parse(Tokens).

parse_module(NextVarNum, Text) when is_list(Text) ->
    {ok, Tokens, _} = alpaca_scanner:scan(Text),
    rebind_and_validate_module(NextVarNum,
                               parse_module(Tokens, #alpaca_module{}));
parse_module(NextVarNum, Text) when is_binary(Text) ->
    parse_module(NextVarNum, binary:bin_to_list(Text));
parse_module([], #alpaca_module{name=no_module}) ->
    {error, no_module_defined};
parse_module([], #alpaca_module{name=N, functions=Funs, types=Ts}=M) ->
    OrderedFuns = group_funs(Funs, N),
    TypesWithModule = [T#alpaca_type{module=N} || T <- Ts],
    {ok, M#alpaca_module{functions=OrderedFuns,
                       types = TypesWithModule}};
parse_module([{break, _}], Mod) ->
    parse_module([], Mod);
parse_module(Tokens, Mod) ->
    case next_batch(Tokens, []) of
        {[], Rem}        -> parse_module(Rem, Mod);
        {NextBatch, Rem} ->
            {ok, Parsed} = parse(NextBatch),
            case update_memo(Mod, Parsed) of
                {ok, NewMemo} ->
                    parse_module(Rem, NewMemo);
                {error, Err} ->
                    Err
            end
    end.

%% Group all functions by name and arity:
group_funs(Funs, ModuleName) ->
    OrderedKeys = 
        drop_dupes_preserve_order(
          lists:map(
            fun(#alpaca_fun_def{name={symbol, _, N}, arity=A}) -> {N, A} end,
            lists:reverse(Funs)),
          []),
    F = fun(#alpaca_fun_def{name={symbol, _, N}, arity=A, versions=[V]}, Acc) ->
                Key = {N, A},
                Existing = maps:get(Key, Acc, []),
                maps:put(Key, [V|Existing], Acc)
        end,
    Grouped = lists:foldl(F, maps:new(), Funs),
    lists:map(
      fun({N, A}=Key) -> 
              NewVs = lists:reverse(maps:get(Key, Grouped)),
              [#alpaca_fun_version{line=L}|_] = NewVs,
              %% we use the first occurence's line as the function's primary
              %% location:
              #alpaca_fun_def{name={symbol, L, N}, arity=A, versions=NewVs}
      end, 
      OrderedKeys).

drop_dupes_preserve_order([], Memo) ->
    lists:reverse(Memo);
drop_dupes_preserve_order([H|T], [H|_]=Memo) ->
    drop_dupes_preserve_order(T, Memo);
drop_dupes_preserve_order([H|T], Memo) ->
    drop_dupes_preserve_order(T, [H|Memo]).

rebind_and_validate_module(_, {error, _} = Err) ->
    Err;
rebind_and_validate_module(NextVarNum, {ok, #alpaca_module{}=Mod}) ->
    validate_user_types(rebind_and_validate_functions(NextVarNum, Mod)).

rebind_and_validate_functions(NextVarNum, #alpaca_module{}=Mod) ->
    #alpaca_module{name=MN, functions=Funs}=Mod,

    F = fun(_, {error, _}=Err) ->
                Err;
           (F, {NV, M, Memo}) ->
                {NV2, M2, F2} = rename_bindings(NV, MN, F),
                    
                %% We invert the returned map so that it is from
                %% synthetic variable name to source code variable
                %% name for later lookup:
                Inverted = [{V, K}||{K, V} <- maps:to_list(M2)],
                { NV2, maps:merge(M, maps:from_list(Inverted)), [F2|Memo]}
        end,
    case lists:foldl(F, {NextVarNum, maps:new(), []}, Funs) of
        {error, _}=Err ->
            Err;
        {NV2, M, Funs2} ->
            %% TODO:  other parts of the compiler might care about that map
            {ok, NV2, M, Mod#alpaca_module{functions=lists:reverse(Funs2)}}
    end.

validate_user_types({error, _}=Err) ->
    Err;
validate_user_types({ok, _, _, #alpaca_module{types=Ts}}=Res) ->
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
    Names = lists:sort([N || #alpaca_type{name={type_name, _, N}} <- Types]),
    check_dupes(Names,
                fun(A, B) -> A =:= B end,
                fun(A) -> {error, {duplicate_type, A}} end).

unique_type_constructors({error, _}=Err, _) ->
    Err;
unique_type_constructors(_, Types) ->
    %% Get the sorted names of only the constructors:
    F = fun (#alpaca_constructor{name={_, _, N}}, Acc) -> [N|Acc];
            (_, Acc) -> Acc
        end,
    ToFlatten = [lists:foldl(F, [], Ms) || #alpaca_type{members=Ms} <- Types],
    %% can't lists:flatten here because strings are lists and we only want
    %% it flattened one level:
    Cs = lists:sort(lists:foldl(fun(A, B) -> A ++ B end, [], ToFlatten)),
    check_dupes(Cs,
                fun(A, B) -> A =:= B end,
                fun(A) -> {error, {duplicate_constructor, A}} end).

update_memo(#alpaca_module{name=no_module}=Mod, {module, Name}) ->
    {ok, Mod#alpaca_module{name=Name}};
update_memo(#alpaca_module{name=Name}, {module, DupeName}) ->
    {error, {module_rename, Name, DupeName}};
update_memo(#alpaca_module{type_imports=Imports}=M, #alpaca_type_import{}=I) ->
    {ok, M#alpaca_module{type_imports=Imports ++ [I]}};
update_memo(#alpaca_module{type_exports=Exports}=M, #alpaca_type_export{}=I) ->
    #alpaca_type_export{names=Names} = I,
    {ok, M#alpaca_module{type_exports = Exports ++ Names}};
update_memo(#alpaca_module{function_exports=Exports}=M, {export, Es}) ->
    {ok, M#alpaca_module{function_exports=Es ++ Exports}};
update_memo(#alpaca_module{function_imports=Imports}=M, {import, Is}) ->
    {ok, M#alpaca_module{function_imports=Imports ++ Is}};
update_memo(#alpaca_module{functions=Funs}=M, #alpaca_fun_def{} = Def) ->
    {ok, M#alpaca_module{functions=[Def|Funs]}};
update_memo(#alpaca_module{types=Ts}=M, #alpaca_type{}=T) ->
    {ok, M#alpaca_module{types=[T|Ts]}};
update_memo(#alpaca_module{tests=Tests}=M, #alpaca_test{}=T) ->
    {ok, M#alpaca_module{tests=[T|Tests]}};
update_memo(M, #alpaca_comment{}) ->
    {ok, M};
update_memo(_, Bad) ->
    {error, {"Top level requires defs, module, and export declarations", Bad}}.

%% Select a discrete batch of tokens to parse.  This basically wants a sequence
%% from the beginning of a top-level expression to a recognizable break between
%% it and the next discrete expression (e.g. two newlines).
next_batch([{break, _}|Rem], []=Memo) ->
    next_batch(Rem, Memo);
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
        TopLevel::alpaca_fun_def()) -> {integer(), map(), alpaca_fun_def()} |
                                     {error, term()}.
rename_bindings(NextVar, MN, #alpaca_fun_def{}=TopLevel) ->
    #alpaca_fun_def{name={symbol, _, Name}, versions=Vs}=TopLevel,
    SeedMap = #{Name => Name},

    F = fun(#alpaca_fun_version{args=As, body=Body}=FV, {Var, M, Versions}) ->
                case make_bindings(Var, MN, SeedMap, As) of
                    {NV, M2, Args} ->
                        case rename_bindings(NV, MN, M2, Body) of
                            {NV2, M3, E} ->
                                FV2 = FV#alpaca_fun_version{
                                        args=Args,
                                        body=E},
                                {NV2, M3, [FV2|Versions]};
                            {error, _} = Err -> 
                                throw(Err)
                        end;
                    {error, _} = E -> throw(E)
                end
        end,

    {NV, M2, Vs2} = lists:foldl(F, {NextVar, maps:new(), []}, Vs),
    {NV, M2, TopLevel#alpaca_fun_def{versions=Vs2}}.

rebind_args(NextVar, _MN, Map, Args) ->
    F = fun({error, _} = E, _) -> E;
           ({symbol, L, N}, {NV, AccMap, Syms}) ->
                case maps:get(N, AccMap, undefined) of
                    undefined ->
                        Synth = next_var(NV),
                        { NV+1
                        , maps:put(N, Synth, AccMap)
                        , [{symbol, L, Synth}|Syms]
                        };
                    _ ->
                        throw({duplicate_definition, N, L})
                end;
           ({unit, _}=U, {NV, AccMap, Syms}) ->
                {NV, AccMap, [U|Syms]};
           (Arg, {NV, AccMap, Syms}) ->
                {NV, AccMap, [Arg|Syms]}
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
rename_bindings(NextVar, MN, M, #alpaca_fun_def{name={symbol, L, Name}}=Def) ->
    #alpaca_fun_def{versions=Vs}=Def,
    {NewName, M2} = case maps:get(Name, M, undefined) of
                        undefined ->
                            Synth = next_var(NextVar),
                            {Synth, maps:put(Name, Synth, M)};
                        _ ->
                            throw({duplicate_definition, Name, L})
                    end,

    F = fun(#alpaca_fun_version{}=FV, {Map, NV, NewVersions}) ->
                #alpaca_fun_version{args=Args, body=Body} = FV,
                case rebind_args(NV+1, MN, Map, Args) of
                    {error, _}=Err ->
                        throw(Err);
                    {NV3, M3, Args2} ->
                        case rename_bindings(NV3, MN, M3, Body) of
                            {error, _}=Err -> 
                                throw(Err);
                            {NV4, M4, Body2} ->
                                FV2 = FV#alpaca_fun_version{
                                        args=Args2,
                                        body=Body2},
                                {NV4, M4, [FV2|NewVersions]}
                        end
                end
           end,
    {NextVar2, Map2, Vs2} = lists:foldl(F, {M2, NextVar, []}, Vs),
    NewDef = Def#alpaca_fun_def{name={symbol, L, NewName}, versions=lists:reverse(Vs2)},
    {NextVar2, Map2, NewDef};
    
rename_bindings(NextVar, MN, Map, #var_binding{}=VB) ->
    #var_binding{name={symbol, L, N},
                 to_bind=TB,
                 expr=E} = VB,
    case maps:get(N, Map, undefined) of
        undefined ->
            Synth = next_var(NextVar),
            M2 = maps:put(N, Synth, Map),
            case rename_bindings(NextVar+1, MN, M2, TB) of
                {error, _} = Err ->
                    Err;
                {NV, M3, TB2} ->
                    case rename_bindings(NV, MN, M3, E) of
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
            throw({duplicate_definition, N, L})
    end;

rename_bindings(NextVar, MN, Map, #alpaca_apply{expr=N, args=Args}=App) ->
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
            {NV2, M2, App#alpaca_apply{expr=Name, args=Args2}}
    end;

rename_bindings(NextVar, MN, Map, #alpaca_spawn{
                                     function=F,
                                     args=Args}=Spawn) ->
    {_, _, FName} = rename_bindings(NextVar, MN, Map, F),
    FArgs = [X||{_, _, X} <- [rename_bindings(NextVar, MN, Map, A)||A <- Args]],
    {NextVar, Map, Spawn#alpaca_spawn{
                     function=FName,
                     from_module=MN,
                     args=FArgs}};

rename_bindings(NextVar, MN, Map, #alpaca_send{message=M, pid=P}=Send) ->
    {_, _, M2} = rename_bindings(NextVar, MN, Map, M),
    {_, _, P2} = rename_bindings(NextVar, MN, Map, P),
    {NextVar, Map, Send#alpaca_send{message=M2, pid=P2}};

rename_bindings(NextVar, _MN, Map, #alpaca_type_apply{arg=none}=A) ->
    {NextVar, Map, A};
rename_bindings(NextVar, MN, Map, #alpaca_type_apply{arg=Arg}=A) ->
    case rename_bindings(NextVar, MN, Map, Arg) of
        {error, _}=Err -> Err;
        {NV, M, Arg2} -> {NV, M, A#alpaca_type_apply{arg=Arg2}}
    end;
rename_bindings(NextVar, MN, Map, #alpaca_type_check{expr=E}=TC) ->
    case rename_bindings(NextVar, MN, Map, E) of
        {error, _}=Err -> Err;
        {NV, M, E2} -> {NV, M, TC#alpaca_type_check{expr=E2}}
    end;

rename_bindings(NextVar, MN, Map, #alpaca_cons{head=H, tail=T}=Cons) ->
    case rename_bindings(NextVar, MN, Map, H) of
        {error, _} = Err -> Err;
        {NV, M, H2} -> case rename_bindings(NV, MN, M, T) of
                           {error, _} = Err -> Err;
                           {NV2, M2, T2} -> {NV2, M2, Cons#alpaca_cons{
                                                        head=H2,
                                                        tail=T2}}
                       end
    end;
rename_bindings(NextVar, MN, Map, #alpaca_binary{segments=Segs}=B) ->
    %% fold to account for errors.
    F = fun(_, {error, _}=Err) -> Err;
           (#alpaca_bits{value=V}=Bits, {NV, M, Acc}) ->
                case rename_bindings(NV, MN, M, V) of
                    {NV2, M2, V2} -> {NV2, M2, [Bits#alpaca_bits{value=V2}|Acc]};
                    {error, _}=Err -> Err
                end
        end,
    case lists:foldl(F, {NextVar, Map, []}, Segs) of
        {error, _}=Err ->
            Err;
        {NV2, M2, Segs2} ->
            {NV2, M2, B#alpaca_binary{segments=lists:reverse(Segs2)}}
    end;
rename_bindings(NextVar, MN, Map, #alpaca_map{pairs=Pairs}=ASTMap) ->
    Folder = fun(_, {error, _}=Err) -> Err;
                (P, {NV, M, Ps}) ->
                     case rename_bindings(NV, MN, M, P) of
                         {error, _}=Err -> Err;
                         {NV2, M2, P2} -> {NV2, M2, [P2|Ps]}
                     end
             end,
    case lists:foldl(Folder, {NextVar, Map, []}, Pairs) of
        {error, _}=Err -> Err;
        {NV, M, Pairs2} -> {NV, M, ASTMap#alpaca_map{pairs=lists:reverse(Pairs2)}}
    end;
rename_bindings(NextVar, MN, Map, #alpaca_map_add{to_add=A, existing=B}=ASTMap) ->
    case rename_bindings(NextVar, MN, Map, A) of
        {error, _}=Err ->
            Err;
        {NV, M, A2} ->
            case rename_bindings(NV, MN, M, B) of
                {error, _}=Err -> Err;
                {NV2, M2, B2} ->
                    {NV2, M2, ASTMap#alpaca_map_add{to_add=A2, existing=B2}}
            end
    end;
rename_bindings(NextVar, MN, Map, #alpaca_map_pair{key=K, val=V}=P) ->
    case rename_bindings(NextVar, MN, Map, K) of
        {error, _}=Err ->
            Err;
        {NV, M, K2} ->
            case rename_bindings(NV, MN, M, V) of
                {error, _}=Err -> Err;
                {NV2, M2, V2} ->
                    {NV2, M2, P#alpaca_map_pair{key=K2, val=V2}}
            end
    end;
rename_bindings(NextVar, MN, Map, #alpaca_tuple{values=Vs}=T) ->
    case rename_binding_list(NextVar, MN, Map, Vs) of
        {error, _} = Err -> Err;
        {NV, M, Vals2} -> {NV, M, T#alpaca_tuple{values=Vals2}}
    end;

rename_bindings(NextVar, MN, Map, #alpaca_record{members=Members}=R) ->
    F = fun(#alpaca_record_member{val=V}=RM, {NewMembers, NV, M}) ->
                case rename_bindings(NV, MN, M, V) of
                    {error, _}=E -> erlang:error(E);
                    {NV2, M2, V2} ->
                        {[RM#alpaca_record_member{val=V2}|NewMembers], NV2, M2}
                end
        end,
    {NewMembers, NextVar2, Map2} = lists:foldl(F, {[], NextVar, Map}, Members),
    {NextVar2, Map2, R#alpaca_record{members=lists:reverse(NewMembers)}};

rename_bindings(NextVar, _MN, Map, {symbol, L, N}=S) ->
    case maps:get(N, Map, undefined) of
        undefined -> {NextVar, Map, S};
        Synthetic -> {NextVar, Map, {symbol, L, Synthetic}}
    end;
rename_bindings(NV, MN, M, #alpaca_ffi{args=Args, clauses=Cs}=FFI) ->
    case rename_bindings(NV, MN, M, Args) of
        {error, _} = Err ->
            Err;
        {NV2, M2, Args2} ->
            case rename_clause_list(NV2, MN, M2, Cs) of
                {error, _} = Err ->
                    Err;
                {NV3, M3, Cs2} ->
                    {NV3, M3, FFI#alpaca_ffi{args=Args2, clauses=Cs2}}
            end
    end;
rename_bindings(NV, MN, M, #alpaca_match{}=Match) ->
    #alpaca_match{match_expr=ME, clauses=Cs} = Match,
    case rename_bindings(NV, MN, M, ME) of
        {error, _} = Err -> Err;
        {NV2, M2, ME2} ->
            case rename_clause_list(NV2, MN, M2, Cs) of
                {error, _} = Err ->
                    Err;
                {NV3, M3, Cs2} ->
                    {NV3, M3, Match#alpaca_match{match_expr=ME2, clauses=Cs2}}
            end
    end;

rename_bindings(NV, MN, M, #alpaca_receive{clauses=Cs}=Recv) ->
    case rename_clause_list(NV, MN, M, Cs) of
        {error, _} = Err -> Err;
        {NV2, M2, Cs2}   -> {NV2, M2, Recv#alpaca_receive{clauses=Cs2}}
    end;

rename_bindings(NV, MN, M, #alpaca_clause{pattern=P, guards=Gs, result=R}=Clause) ->
    %% pattern matches create new bindings and as such we don't
    %% just want to use existing substitutions but rather error
    %% on duplicates and create entirely new ones:
    case make_bindings(NV, MN, M, P) of
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
                            {NV4, M, Clause#alpaca_clause{
                                       pattern=P2,
                                       guards=Gs2,
                                       result=R2}}
                    end
            end
    end;
rename_bindings(NextVar, _MN, Map, Expr) ->
    {NextVar, Map, Expr}.

rename_binding_list(NextVar, MN, Map, Bindings) ->
    F = fun(_, {error, _} = Err) -> Err;
           (A, {NV, M, Memo}) ->
                case rename_bindings(NV, MN, M, A) of
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
    F = fun(_, {error, _}=Err) -> Err;
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
make_bindings(NV, MN, M, [_|_]=Xs) ->
    {NV2, M2, Xs2} = lists:foldl(
                       fun(X, {NextVar, Map, Memo}) ->
                               case make_bindings(NextVar, MN, Map, X) of
                                   {error, _}=Err -> throw(Err);
                                   {NV2, M2, A2} -> {NV2, M2, [A2|Memo]}
                               end
                       end,
                       {NV, M, []},
                       Xs),
    {NV2, M2, lists:reverse(Xs2)};

make_bindings(NV, MN, M, #alpaca_tuple{values=Vs}=Tup) ->
    F = fun(_, {error, _}=E) -> E;
           (V, {NextVar, Map, Memo}) ->
                case make_bindings(NextVar, MN, Map, V) of
                    {error, _} = Err -> Err;
                    {NV2, M2, V2} -> {NV2, M2, [V2|Memo]}
                end
        end,
    case lists:foldl(F, {NV, M, []}, Vs) of
        {error, _} = Err -> Err;
        {NV2, M2, Vs2}   -> {NV2, M2, Tup#alpaca_tuple{values=lists:reverse(Vs2)}}
    end;
make_bindings(NV, MN, M, #alpaca_cons{head=H, tail=T}=Cons) ->
    case make_bindings(NV, MN, M, H) of
        {error, _} = Err -> Err;
        {NV2, M2, H2} -> case make_bindings(NV2, MN, M2, T) of
                             {error, _} = Err ->
                                 Err;
                             {NV3, M3, T2} ->
                                 {NV3, M3, Cons#alpaca_cons{head=H2, tail=T2}}
                         end
    end;
%% TODO:  this is identical to rename_bindings but for the internal call
%% to make_bindings vs rename_bindings.  How much else in here is like this?
%% Probably loads of abstracting/de-duping potential.
make_bindings(NextVar, MN, Map, #alpaca_binary{segments=Segs}=B) ->
    F = fun(_, {error, _}=Err) ->
                Err;
           (#alpaca_bits{value=V}=Bits, {NV, M, Acc}) ->
                case make_bindings(NV, MN, M, V) of
                    {NV2, M2, V2} ->
                        {NV2, M2, [Bits#alpaca_bits{value=V2}|Acc]};
                    {error, _}=Err ->
                        Err
                end
        end,
    case lists:foldl(F, {NextVar, Map, []}, Segs) of
        {error, _}=Err ->
            Err;
        {NV2, M2, Segs2} ->
            {NV2, M2, B#alpaca_binary{segments=lists:reverse(Segs2)}}
    end;

%%% Map patterns need to rename variables used for keys and create new bindings
%%% for variables used for values.  We want to rename for keys because we want
%%% the following to work:
%%%
%%%     get my_key my_map = match my_map with
%%%       #{my_key => v} -> v
%%%
%%% Map patterns require the key to be something exact already.
make_bindings(NextVar, MN, BindingMap, #alpaca_map{pairs=Ps}=Map) ->
    Folder = fun(_, {error, _}=Err) -> Err;
                (P, {NV, M, Acc}) ->
                     case make_bindings(NV, MN, M, P) of
                         {error, _}=Err -> Err;
                         {NV2, M2, P2} -> {NV2, M2, [P2|Acc]}
                     end
             end,
    case lists:foldl(Folder, {NextVar, BindingMap, []}, Ps) of
        {error, _}=Err -> Err;
        {NV, M, Pairs} ->
            Map2 = Map#alpaca_map{is_pattern=true, pairs=lists:reverse(Pairs)},
            {NV, M, Map2}
    end;
make_bindings(NV, MN, M, #alpaca_map_pair{key=K, val=V}=P) ->
    case rename_bindings(NV, MN, M, K) of
        {error, _}=Err -> Err;
        {NV2, M2, K2} ->
            case make_bindings(NV2, MN, M2, V) of
                {error, _}=Err -> Err;
                {NV3, M3, V2} ->
                    {NV3, M3, P#alpaca_map_pair{is_pattern=true, key=K2, val=V2}}
            end
    end;

%% Records can be compiled as maps so we need the is_pattern parameter
%% on their AST nodes set correctly here too.
make_bindings(NV, MN, M, #alpaca_record{members=Members}=R) ->
    F = fun(#alpaca_record_member{val=V}=RM, {NewVs, NextVar, Map}) ->
                case make_bindings(NextVar, MN, Map, V) of
                    {error, _}=Err -> 
                        erlang:error(Err);
                    {NextVar2, Map2, V2} -> 
                        NewR = RM#alpaca_record_member{val=V2},
                        {[NewR|NewVs], NextVar2, Map2}
                end
        end,
    {Members2, NV2, M2} = lists:foldl(F, {[], NV, M}, Members),
    NewR = R#alpaca_record{
             members=lists:reverse(Members2),
             is_pattern=true},
    {NV2, M2, NewR};

make_bindings(NV, MN, M, #alpaca_type_apply{arg=none}=TA) ->
    {NV, M, TA};
make_bindings(NV, MN, M, #alpaca_type_apply{arg=Arg}=TA) ->
    case make_bindings(NV, MN, M, Arg) of
        {NV2, M2, Arg2} -> {NV2, M2, TA#alpaca_type_apply{arg=Arg2}};
        {error, _}=Err  -> Err
    end;

make_bindings(NV, _MN, M, {symbol, L, Name}) ->
    case maps:get(Name, M, undefined) of
        undefined ->
            Synth = next_var(NV),
            {NV+1, maps:put(Name, Synth, M), {symbol, L, Synth}};
        _ ->
            throw({duplicate_definition, Name, L})
    end;
make_bindings(NV, _MN, M, Expression) ->
    {NV, M, Expression}.

-define(base_var_name, "svar_").
next_var(X) ->
    ?base_var_name ++ integer_to_list(X).

-ifdef(TEST).

test_parse(S) ->
    parse(alpaca_scanner:scan(S)).

symbols_test_() ->
    [?_assertMatch({ok, {symbol, 1, "oneSymbol"}},
                   parse(alpaca_scanner:scan("oneSymbol")))
    ].

user_types_test_() ->
    [?_assertMatch({ok, #alpaca_type{name={type_name, 1, "t"},
                                   vars=[],
                                   members=[t_int,
                                            #alpaca_constructor{
                                               name={type_constructor, 1, "A"},
                                               arg=t_int}]}},
                   test_parse("type t = int | A int")),
     ?_assertMatch(
        {ok, #alpaca_type{
                name={type_name, 1, "my_list"},
                vars=[{type_var, 1, "x"}],
                members=[#alpaca_constructor{
                            name={type_constructor, 1, "Nil"},
                            arg=none},
                         #alpaca_constructor{
                            name={type_constructor, 1, "Cons"},
                            arg=#alpaca_type_tuple{
                                   members=[{type_var, 1, "x"},
                                            #alpaca_type{
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
     ?_assertMatch({ok, #alpaca_type{
                           name={type_name, 1, "either"},
                           vars=[{type_var, 1, "a"}, {type_var, 1, "b"}],
                           members=[#alpaca_constructor{
                                       name={type_constructor, 1, "Left"},
                                       arg={type_var, 1, "a"}
                                      },
                                    #alpaca_constructor{
                                       name={type_constructor, 1, "Right"},
                                       arg={type_var, 1, "b"}
                                      }]
                          }},
                   test_parse("type either 'a 'b = Left 'a | Right 'b"))
    ].

defn_test_() ->
    [
     %% Zero-arg funs are disallowed; these are treated as constant
     %% values. They are only permitted to be literals, at least for now;
     %% this ensures that they are side-effect free and referentially
     %% transparent
     ?_assertMatch(
        {ok, 
         #alpaca_fun_def{name={symbol, 1, "x"},
                       versions=[#alpaca_fun_version{
                                    args=[], 
                                    body={int, 1, 5}}]}},
                   parse(alpaca_scanner:scan("let x=5"))),
     ?_assertMatch(
        {ok, {error, non_literal_value, {symbol, 1, "x"}, 
                     {alpaca_apply,undefined,1,
                       {symbol,1,"sideEffectingFun"},
                       [{int,1,5}]}}},
        parse(alpaca_scanner:scan("let x=sideEffectingFun 5"))),
     ?_assertMatch(
        {ok, {error, non_literal_value, {symbol, 1, "x"},                  
                         {alpaca_record,2,1,false,
                             [{alpaca_record_member,1,one,undefined,
                                  {int,1,10}},
                              {alpaca_record_member,1,two,undefined,
                                  {alpaca_apply,undefined,1,
                                      {symbol,1,"sideEffectingFun"},
                                      [{int,1,5}]}}]}}},
        parse(alpaca_scanner:scan("let x={one = 10, two = (sideEffectingFun 5)}"))),        
     ?_assertMatch(
        {ok, {error, non_literal_value, {symbol, 1, "x"}, 
                     {alpaca_cons,undefined,0,
                             {int,1,1},
                             {alpaca_cons,undefined,0,
                                 {alpaca_apply,undefined,1,
                                     {symbol,1,"sideEffectingFun"},
                                     [{int,1,5}]},
                                 {nil,0}}}}},
        parse(alpaca_scanner:scan("let x=[1, (sideEffectingFun 5)]"))),        
     ?_assertMatch(
        {ok, 
         #alpaca_fun_def{name={symbol, 1, "double"},
                       versions=[#alpaca_fun_version{
                                    args=[{symbol, 1, "x"}],
                                    body=#alpaca_apply{
                                            type=undefined,
                                            expr={bif, '+', 1, erlang, '+'},
                                            args=[{symbol, 1, "x"},
                                                  {symbol, 1, "x"}]}}]}},
        parse(alpaca_scanner:scan("let double x = x + x"))),
     ?_assertMatch(
        {ok, #alpaca_fun_def{name={symbol, 1, "add"},
                           versions=[#alpaca_fun_version{
                                        args=[{symbol, 1, "x"}, 
                                              {symbol, 1, "y"}],
                                        body=#alpaca_apply{
                                                type=undefined,
                                                expr={bif, '+', 1, erlang, '+'},
                                                args=[{symbol, 1, "x"},
                                                      {symbol, 1, "y"}]}}]}},
        parse(alpaca_scanner:scan("let add x y = x + y"))),
        ?_assertMatch(
            {ok, #alpaca_fun_def{name={symbol, 1, "(<*>)"},
                            versions=[#alpaca_fun_version{
                                            args=[{symbol, 1, "x"}, 
                                                {symbol, 1, "y"}],
                                            body=#alpaca_apply{
                                                    type=undefined,
                                                    expr={bif, '+', 1, erlang, '+'},
                                                    args=[{symbol, 1, "x"},
                                                        {symbol, 1, "y"}]}}]}},
        parse(alpaca_scanner:scan("let (<*>) x y = x + y")))
    ].

float_math_test_() ->
    [?_assertMatch({ok, #alpaca_apply{expr={bif, '+', 1, erlang, '+'}}},
                   parse(alpaca_scanner:scan("2 + 1"))),
     ?_assertMatch({ok, #alpaca_apply{expr={bif, '+.', 1, erlang, '+'}}},
                   parse(alpaca_scanner:scan("2.0 +. 1.3")))
    ].

let_binding_test_() ->
    [?_assertMatch(
        {ok, 
         #fun_binding{
            def=#alpaca_fun_def{
                   name={symbol, 1, "double"},
                   versions=[#alpaca_fun_version{
                                args=[{symbol, 1, "x"}],
                                body=#alpaca_apply{
                                        type=undefined,
                                        expr={bif, '+', 1, erlang, '+'},
                                        args=[{symbol, 1, "x"},
                                              {symbol, 1, "x"}]}}]},
            expr=#alpaca_apply{
                    expr={symbol, 1, "double"},
                    args=[{int, 1, 2}]}}},
        parse(alpaca_scanner:scan("let double x = x + x in double 2"))),
     ?_assertMatch({ok, #var_binding{
                           name={symbol, 1, "x"},
                           to_bind=#alpaca_apply{
                                      expr={symbol, 1, "double"},
                                      args=[{int, 1, 2}]},
                           expr=#alpaca_apply{
                                   expr={symbol, 1, "double"},
                                   args=[{symbol, 1, "x"}]}}},
                   parse(alpaca_scanner:scan("let x = double 2 in double x"))),
     ?_assertMatch(
        {ok, 
         #alpaca_fun_def{
            name={symbol, 1, "doubler"},
            versions=[#alpaca_fun_version{
                         args=[{symbol, 1, "x"}],
                         body=#fun_binding{
                                 def=#alpaca_fun_def{
                                        name={symbol, 2, "double"},
                                        versions=[#alpaca_fun_version{
                                                     args=[{symbol, 2, "x"}],
                                                     body=#alpaca_apply{
                                                             type=undefined,
                                                             expr={bif, '+', 2, erlang, '+'},
                                                             args=[{symbol, 2, "x"},
                                                                   {symbol, 2, "x"}]}}]},
                                 expr=#alpaca_apply{
                                         expr={symbol, 3, "double"},
                                         args=[{int, 3, 2}]}}}]}},
        parse(alpaca_scanner:scan(
                "let doubler x =\n"
                "  let double x = x + x in\n"
                "  double 2"))),
     ?_assertMatch(
        {ok, 
         #alpaca_fun_def{
            name={symbol,1,"my_fun"},
            versions=[#alpaca_fun_version{
                         args=[{symbol,1,"x"},{symbol,1,"y"}],
                         body=#fun_binding{
                                 def=#alpaca_fun_def{
                                        name={symbol,1,"xer"},
                                        versions=[#alpaca_fun_version{
                                                     args=[{symbol,1,"a"}],
                                                     body=#alpaca_apply{
                                                             type=undefined,
                                                             expr={bif, '+', 1, erlang, '+'},
                                                             args=[{symbol,1,"a"},
                                                                   {symbol,1,"a"}]}}]},
                                 expr=#fun_binding{
                                         def=#alpaca_fun_def{
                                                name={symbol,1,"yer"},
                                                versions=[#alpaca_fun_version{
                                                             args=[{symbol,1,"b"}],
                                                             body=#alpaca_apply{
                                                                     type=undefined,
                                                                     expr={bif, '+', 1, erlang, '+'},
                                                                     args=[{symbol,1,"b"},
                                                                           {symbol,1,"b"}]}}]},
                                         expr=#alpaca_apply{
                                                 type=undefined,
                                                 expr={bif, '+', 1, erlang, '+'},
                                                 args=[#alpaca_apply{
                                                          expr={symbol,1,"xer"},
                                                          args=[{symbol,1,"x"}]},
                                                       #alpaca_apply{
                                                          expr={symbol,1,"yer"},
                                                          args=[{symbol,1,"y"}]}]}}}}]}},
        parse(alpaca_scanner:scan(
                "let my_fun x y ="
                "  let xer a = a + a in"
                "  let yer b = b + b in"
                "  (xer x) + (yer y)")))
    ].

application_test_() ->
    [?_assertMatch({ok, #alpaca_apply{expr={symbol, 1, "double"},
                                    args=[{int, 1, 2}]}},
                   parse(alpaca_scanner:scan("double 2"))),
     ?_assertMatch({ok, #alpaca_apply{expr={symbol, 1, "two"},
                                    args=[{symbol, 1, "symbols"}]}},
                   parse(alpaca_scanner:scan("two symbols"))),
     ?_assertMatch({ok, #alpaca_apply{expr={symbol, 1, "x"},
                                    args=[{symbol, 1, "y"}, {symbol, 1, "z"}]}},
                   parse(alpaca_scanner:scan("x y z"))),
     ?_assertMatch({ok, #alpaca_apply{
                           expr={'mod', {symbol, 1, "fun"}, 2},
                           args=[{int, 1, 1}, {symbol, 1, "x"}]}},
                   parse(alpaca_scanner:scan("mod.fun 1 x")))
    ].

module_def_test_() ->
    [?_assertMatch({ok, {module, 'test_mod'}},
                   parse(alpaca_scanner:scan("module test_mod"))),
     ?_assertMatch({ok, {module, 'myMod'}},
                   parse(alpaca_scanner:scan("module myMod")))
    ].

export_test_() ->
    [?_assertMatch({ok, {export, [{"add", 2}]}},
                   parse(alpaca_scanner:scan("export add/2")))
    ].

import_test_() ->
    [?_assertMatch({ok, {import, [{"foo", {"some_mod", all}},
                                  {"bar", {"some_mod", 2}}]}},
                   parse(alpaca_scanner:scan("import some_mod.[foo, bar/2]"))),
     ?_assertMatch(
        {ok, {import, [{"foo", {"mod1", all}},
                       {"bar", {"mod2", 1}},
                       {"baz", {"mod2", all}}]}},
        parse(alpaca_scanner:scan("import mod1.foo, mod2.[bar/1, baz]"))),
     fun() ->
             Code =
                 "module two_lines_of_imports\n\n"
                 "import foo.bar/2\n\n"
                 "import math.[add/2, sub/2, mult]",
             ?assertMatch(
                {ok,
                 _,
                 _,
                 #alpaca_module{
                    function_imports=[{"bar", {"foo", 2}},
                                      {"add", {"math", 2}},
                                      {"sub", {"math", 2}},
                                      {"mult", {"math", all}}]}},
                parse_module(0, Code))
     end
    ].

expr_test_() ->
    [?_assertMatch({ok, {int, 1, 2}}, parse(alpaca_scanner:scan("2"))),
     ?_assertMatch({ok, #alpaca_apply{type=undefined,
                                      expr={bif, '+', 1, erlang, '+'},
                                      args=[{int, 1, 1},
                                            {int, 1, 5}]}},
                   parse(alpaca_scanner:scan("1 + 5"))),
     ?_assertMatch({ok, #alpaca_apply{expr={symbol, 1, "add"},
                                      args=[{symbol, 1, "x"},
                                            {int, 1, 2}]}},
                   parse(alpaca_scanner:scan("add x 2"))),
     ?_assertMatch({ok,
                    #alpaca_apply{expr={symbol, 1, "double"},
                                  args=[{symbol, 1, "x"}]}},
                   parse(alpaca_scanner:scan("(double x)"))),
     ?_assertMatch({ok, #alpaca_apply{
                           expr={symbol, 1, "tuple_func"},
                           args=[#alpaca_tuple{
                                    arity=2,
                                    values=[{symbol, 1, "x"},
                                            {int, 1, 1}]},
                                 {symbol, 1, "y"}]}},
                   parse(alpaca_scanner:scan("tuple_func (x, 1) y")))
    ].

module_with_let_test() ->
    Code =
        "module test_mod\n\n"
        "export add/2\n\n"
        "let add x y =\n"
        "  let adder a b = a + b in\n"
        "  adder x y",
    ?assertMatch(
       {ok, _, _,
        #alpaca_module{
           name='test_mod',
           function_exports=[{"add",2}],
           functions=[#alpaca_fun_def{
                         name={symbol,5,"add"},
                         versions=[#alpaca_fun_version{
                                      args=[{symbol,5,"svar_0"},{symbol,5,"svar_1"}],
                                      body=#fun_binding{
                                              def=#alpaca_fun_def{
                                                     name={symbol,6,"svar_2"},
                                                     versions=[#alpaca_fun_version{
                                                                  args=[{symbol,6,"svar_3"},
                                                                        {symbol,6,"svar_4"}],
                                                                  body=#alpaca_apply{
                                                                          type=undefined,
                                                                          expr={bif, '+', 6, erlang, '+'},
                                                                          args=[{symbol,6,"svar_3"},
                                                                                {symbol,6,"svar_4"}]}}]},
                                              expr=#alpaca_apply{
                                                      expr={symbol,7,"svar_2"},
                                                      args=[{symbol,7,"svar_0"},
                                                            {symbol,7,"svar_1"}]}}}]}]}},
       parse_module(0, Code)).

match_test_() ->
    [?_assertMatch(
        {ok, #alpaca_match{match_expr={symbol, 1, "x"},
                         clauses=[#alpaca_clause{
                                     pattern={int, 2, 0},
                                     result={symbol, 2, "zero"}},
                                  #alpaca_clause{
                                     pattern={'_', 3},
                                     result={symbol, 3, "non_zero"}}]}},
        parse(alpaca_scanner:scan(
                "match x with\n"
                " 0 -> zero\n"
                "| _ -> non_zero\n"))),
     ?_assertMatch(
        {ok, #alpaca_match{match_expr=#alpaca_apply{
                                       expr={symbol, 1, "add"},
                                       args=[{symbol, 1, "x"},
                                             {symbol, 1, "y"}]},
                         clauses=[#alpaca_clause{pattern={int, 2, 0},
                                               result={atom, 2, "zero"}},
                                  #alpaca_clause{pattern={int, 3, 1},
                                               result={atom, 3, "one"}},
                                  #alpaca_clause{pattern={'_', 4},
                                               result={atom, 4,
                                                       "more_than_one"}}
                                 ]}},
        parse(alpaca_scanner:scan(
                "match add x y with\n"
                " 0 -> :zero\n"
                "| 1 -> :one\n"
                "| _ -> :more_than_one\n"))),
     ?_assertMatch(
        {ok, #alpaca_match{
                match_expr={symbol, 1, "x"},
                clauses=[#alpaca_clause{
                            pattern=#alpaca_tuple{
                                       arity=2,
                                       values=[{'_', 2},
                                               {symbol, 2, "x"}]},
                            result={atom, 2, "anything_first"}},
                         #alpaca_clause{
                            pattern=#alpaca_tuple{
                                       arity=2,
                                       values=[{int, 3, 1},
                                               {symbol, 3, "x"}]},
                            result={atom, 3, "one_first"}}]}},
        parse(alpaca_scanner:scan(
                "match x with\n"
                "  (_, x) -> :anything_first\n"
                "| (1, x) -> :one_first\n"))),
     ?_assertMatch(
        {ok, #alpaca_match{
                match_expr=#alpaca_tuple{
                              arity=2,
                              values=[{symbol, 1, "x"},
                                      {symbol, 1, "y"}]},
                clauses=[#alpaca_clause{
                            pattern=#alpaca_tuple{
                                       arity=2,
                                       values=[#alpaca_tuple{
                                                  arity=2,
                                                  values=[{'_', 2},
                                                          {int, 2, 1}]},
                                               {symbol, 2, "a"}]},
                            result={atom, 2, "nested_tuple"}}]}},
        parse(alpaca_scanner:scan(
                "match (x, y) with\n"
                " ((_, 1), a) -> :nested_tuple")))
    ].

tuple_test_() ->
    %% first no unary tuples:
    [?_assertMatch({ok, {int, 1, 1}}, parse(alpaca_scanner:scan("(1)"))),
     ?_assertMatch({ok, #alpaca_tuple{arity=2,
                                    values=[{int, 1, 1}, {int, 1, 2}]}},
                   parse(alpaca_scanner:scan("(1, 2)"))),
     ?_assertMatch({ok, #alpaca_tuple{arity=2,
                                    values=[{symbol, 1, "x"}, {int, 1, 1}]}},
                   parse(alpaca_scanner:scan("(x, 1)"))),
     ?_assertMatch({ok, #alpaca_tuple{
                           arity=2,
                           values=[#alpaca_tuple{arity=2,
                                               values=[{int, 1, 1},
                                                       {symbol, 1, "x"}]},
                                   {int, 1, 12}]}},
                   parse(alpaca_scanner:scan("((1, x), 12)")))
    ].

list_test_() ->
    [?_assertMatch({ok, #alpaca_cons{head={int, 1, 1},
                                   tail=#alpaca_cons{
                                           head={int, 1, 2},
                                           tail=#alpaca_cons{
                                                   head={int, 1, 3},
                                                   tail={nil, 0}}}}},
                   test_parse("[1, 2, 3]")),
     ?_assertMatch({ok, {nil, 1}}, parse(alpaca_scanner:scan("[]"))),
     ?_assertMatch({ok, #alpaca_cons{head={int, 1, 1}, tail={nil, 1}}},
                   parse(alpaca_scanner:scan("[1]"))),
     ?_assertMatch({ok, #alpaca_cons{
                           head={symbol, 1, "x"},
                           tail=#alpaca_cons{head={int, 1, 1},
                                           tail={nil, 1}}}},
                   parse(alpaca_scanner:scan("x :: [1]"))),
     ?_assertMatch({ok, #alpaca_cons{head={int, 1, 1},
                                   tail={symbol, 1, "y"}}},
                   parse(alpaca_scanner:scan("1 :: y"))),
     ?_assertMatch(
        {ok, #alpaca_match{
                match_expr={symbol,1,"x"},
                clauses=[#alpaca_clause{pattern={nil,2},
                                      result={nil,2}},
                         #alpaca_clause{pattern=#alpaca_cons{
                                                 head={symbol,3,"h"},
                                                 tail={symbol,3,"t"}},
                                      result={symbol,3,"h"}}]}},
        parse(alpaca_scanner:scan(
                "match x with\n"
                "  [] -> []\n"
                "| h :: t -> h\n")))
    ].

binary_test_() ->
    [?_assertMatch({ok, #alpaca_binary{
                           line=1,
                           segments=[#alpaca_bits{line=1, value={int, 1, 1}}]}},
                   parse(alpaca_scanner:scan("<<1>>"))),
     ?_assertMatch(
        {ok, #alpaca_binary{
                line=1,
                segments=[#alpaca_bits{value={int, 1, 1},
                                     size=8,
                                     unit=1},
                          #alpaca_bits{value={int, 1, 2},
                                     size=16,
                                     unit=1}]}},
        parse(alpaca_scanner:scan("<<1: size=8 unit=1, 2: size=16 unit=1>>"))),
     ?_assertMatch(
        {ok, #alpaca_binary{}},
        parse(alpaca_scanner:scan(
                "<<255: size=16 unit=1 sign=true end=little>>"))
       ),
     ?_assertMatch(
        {ok, #alpaca_binary{
                segments=[#alpaca_bits{value={symbol, 1, "a"}},
                          #alpaca_bits{value={symbol, 1, "b"}}]}},
        parse(alpaca_scanner:scan("<<a: size=8 type=int, b: size=8 type=int>>")))
    ].

string_test_() ->
    [ ?_assertMatch(
         {ok, {string, 1, "Hello world"}}, test_parse("\"Hello world\""))
    %% , ?_assertMatch({ok, {string, 1, "Nested \" quotes"}}),
    %% , test_parse("\"Nested " "\"" " quotes\"")
    ].

ffi_test_() ->
    [?_assertMatch({ok, #alpaca_ffi{
                           module={atom, 1, "io"},
                           function_name={atom, 1, "format"},
                           args=#alpaca_cons{
                                   head={string, 1, "One is ~s~n"},
                                   tail=#alpaca_cons{
                                           head=#alpaca_cons{
                                                   head={int, 1, 1},
                                                   tail={nil, 1}},
                                           tail={nil, 0}}}}},
                   test_parse(
                     "beam :io :format [\"One is ~s~n\", [1]] with\n"
                     " _ -> 0"))
    ].

simple_module_test() ->
    Code =
        "module test_mod\n\n"
        "export add/2, sub/2\n\n"
        "let adder x y = x + y\n\n"
        "let add1 x = adder x 1\n\n"
        "let add x y = adder x y\n\n"
        "let sub x y = x - y",
    ?assertMatch(
       {ok, _, _,
        #alpaca_module{
           name='test_mod',
           function_exports=[{"add",2},{"sub",2}],
           functions=[
                      #alpaca_fun_def{
                         name={symbol, 5, "adder"},
                         versions=[#alpaca_fun_version{
                                      args=[{symbol, 5, "svar_0"},
                                            {symbol,5 , "svar_1"}],
                                      body=#alpaca_apply{type=undefined,
                                                       expr={bif, '+', 5, erlang, '+'},
                                                       args=[{symbol, 5, "svar_0"},
                                                             {symbol,5,"svar_1"}]}}]},
                      #alpaca_fun_def{
                         name={symbol,7,"add1"},
                         versions=[#alpaca_fun_version{
                                      args=[{symbol,7,"svar_2"}],
                                      body=#alpaca_apply{expr={symbol,7,"adder"},
                                                       args=[{symbol,7,"svar_2"},
                                                             {int,7,1}]}}]},
                      #alpaca_fun_def{
                         name={symbol,9,"add"},
                         versions=[#alpaca_fun_version{
                                      args=[{symbol,9,"svar_3"},{symbol,9,"svar_4"}],
                                      body=#alpaca_apply{expr={symbol,9,"adder"},
                                                       args=[{symbol,9,"svar_3"},
                                                             {symbol,9,"svar_4"}]}}]},
                      #alpaca_fun_def{
                         name={symbol,11,"sub"},
                         versions=[#alpaca_fun_version{
                                      args=[{symbol,11,"svar_5"},{symbol,11,"svar_6"}],
                                      body=#alpaca_apply{type=undefined,
                                                       expr={bif, '-', 11, erlang, '-'},
                                                       args=[{symbol,11,"svar_5"},
                                                             {symbol,11,"svar_6"}]}}]}]}},
       parse_module(0, Code)).

break_test() ->
    % We should tolerate whitespace between the two break tokens
    Code = "module test_mod\n\n
            let a = 5\n   \n"
           "let b = 6\n\n",
     ?assertMatch(
       {ok, _, _,
        #alpaca_module{
           name='test_mod',
           function_exports=[],
           functions=[#alpaca_fun_def{
                         name={symbol, 4, "a"},
                         versions=[#alpaca_fun_version{
                                      args=[],
                                    body={int, 4, 5}}]},
                      #alpaca_fun_def{
                         name={symbol, 6, "b"},
                         versions=[#alpaca_fun_version{
                                      args=[],
                                      body={int, 6, 6}}]}               
       ]}},
       parse_module(0, Code)).
    

rebinding_test_() ->
    %% Simple rebinding:
    {ok, A} = test_parse("let f x = let y = 2 in x + y"),
    %% Check for duplicate definition error:
    {ok, B} = test_parse("let f x = \nlet x = 1 in x + x"),
    %% Check for good pattern match variable names:
    {ok, C} = test_parse("let f x = match x with\n"
                         "  (a, 0) -> a\n"
                         "| (a, b) -> b"),
    %% Check for duplication in pattern match variable names:
    {ok, D} = test_parse("let f x = match x with\n"
                         " x -> 0"),
    %% Check for good pattern match variable names in lists:
    {ok, E} = test_parse("let f x = match x with\n"
                         "  [_, b, 0] -> b\n"
                         "| h :: t -> h"),
    %% Check for dupe variable names in lists:
    {ok, F} = test_parse("let f x y = match x with\n"
                         " h :: y -> h"),

    [?_assertMatch({_, _, #alpaca_fun_def{
                             name={symbol, 1, "f"},
                             versions=[#alpaca_fun_version{
                                          args=[{symbol, 1, "svar_0"}],
                                          body=#var_binding{
                                                  name={symbol, 1, "svar_1"},
                                                  to_bind={int, 1, 2},
                                                  expr=#alpaca_apply{
                                                          expr={bif, '+', 1, 'erlang', '+'},
                                                          args=[{symbol, 1, "svar_0"},
                                                                {symbol, 1, "svar_1"}]}}}]}},
                   rename_bindings(0, undefined, A)),
     ?_assertException(throw, 
                       {duplicate_definition, "x", 2},
                       rename_bindings(0, undefined, B)),
     ?_assertMatch(
        {_, _, #alpaca_fun_def{
                  name={symbol, 1, "f"},
                  versions=[#alpaca_fun_version{
                               args=[{symbol, 1, "svar_0"}],
                               body=#alpaca_match{
                                       match_expr={symbol, 1, "svar_0"},
                                       clauses=[#alpaca_clause{
                                                   pattern=#alpaca_tuple{
                                                              values=[{symbol, 2, "svar_1"},
                                                                      {int, 2, 0}]},
                                                   result={symbol, 2, "svar_1"}},
                                                #alpaca_clause{
                                                   pattern=#alpaca_tuple{
                                                              values=[{symbol, 3, "svar_2"},
                                                                      {symbol, 3, "svar_3"}]},
                                                   result={symbol, 3, "svar_3"}}]}}]}},
        rename_bindings(0, undefined, C)),
     ?_assertException(throw,
                       {duplicate_definition, "x", 2},
                       rename_bindings(0, undefined, D)),
     ?_assertMatch(
        {_, _,
         #alpaca_fun_def{
            versions=[#alpaca_fun_version{ 
                         body=#alpaca_match{
                                 match_expr={symbol, 1, "svar_0"},
                                 clauses=[#alpaca_clause{
                                             pattern=#alpaca_cons{
                                                        head={'_', 2},
                                                        tail=#alpaca_cons{
                                                                head={symbol, 2, "svar_1"},
                                                                tail=#alpaca_cons{
                                                                        head={int, 2, 0},
                                                                        tail={nil, 0}}}},
                                             result={symbol, 2, "svar_1"}},
                                          #alpaca_clause{
                                             pattern=#alpaca_cons{
                                                        head={symbol, 3, "svar_2"},
                                                        tail={symbol, 3, "svar_3"}},
                                             result={symbol, 3, "svar_2"}}]}}]}},
        rename_bindings(0, undefined, E)),
     ?_assertException(throw, 
                       {duplicate_definition, "y", 2},
                       rename_bindings(0, undefined, F))
    ].

type_expr_in_type_declaration_test() ->
    ?assertMatch({error, _}, test_parse("type a not_a_var = A not_a_var")).

-endif.
