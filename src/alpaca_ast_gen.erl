%%% -*- mode: erlang;erlang-indent-level: 4;indent-tabs-mode: nil -*-
%%% ex: ft=erlang ts=4 sw=4 et
-module(alpaca_ast_gen).
-export([parse/1, make_modules/1]).

%% Parse is used by other modules (particularly alpaca_typer) to make ASTs
%% from code that does not necessarily include a module:
-ignore_xref([parse/1]).

-include("alpaca_ast.hrl").

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

%% Generating an Alpaca module AST from text source requires the following
%% steps:
%%
%%   1. text to tokens with alpaca_scanner:scan/1
%%   2. tokens to module with parse_module/1
%%   3. expanding and resolving module imports and exports, making pattern
%%      bindings and renaming variable names.
%%
%% This third step requires all parsed modules to be available so that when an
%% statement tries to import all of a function's available arity versions (e.g.
%% `import m.foo` instead of `import m.foo/1, m.foo/2`) the pass can find out
%% which specific function versions should be available.
%%
%% A single function make_modules/1 provides one entry point that can be used
%% to cover all three steps for a list of code strings.

make_modules(Code) ->
    Modules = [parse_module(SourceCode) || SourceCode <- Code],
    rename_and_resolve(Modules).

parse({ok, Tokens, _}) ->
    parse(Tokens);
parse(Tokens) when is_list(Tokens) ->
    alpaca_parser:parse(Tokens).

parse_module(Text) when is_list(Text) ->
    {ok, Tokens, _} = alpaca_scanner:scan(Text),
    rebind_and_validate_module(NextVarNum,
                               parse_module(Tokens, #alpaca_module{}));
parse_module(Text) when is_binary(Text) ->
    parse_module(NextVarNum, binary:bin_to_list(Text)).

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

%% Rename bindings to account for variable names escaping receive, rewrite
%% exports that don't specify arity, resolve missing functions with imports.
%%
%% This doesn't do much in the way of checking validity of exports and imports
%% beyond ensuring that a module exists when all arities of a function are being
%% imported.  We leave proper in-depth checking of the inter-module calls to the
%% typer as it already does a reasonable job.  Checking for the existence of a
%% module for imports with unqualified arity occurs only because we need to know
%% how to rewrite calls to functions that aren't defined within the module being
%% parsed as inter-module function calls.  They're rewritten as such in the AST
%% generation stage so that both the typer and the code generation stages can be
%% ignorant as to how imports should work.
rename_and_resolve(Modules) ->
    Expanded = expand_imports(expand_exports(Modules)),
    F = fun(Mod, {NV, Memo}) ->
                {ok, NV2, Mod2} = rebind_and_validate_module(NV, Mod, Expanded),
                {NV2, [Mod2|Memo]}
        end,
    {_, Ms} = lists:foldl(F, {0, []}, Expanded),
    lists:reverse(Ms).

%% Any export that doesn't specify arity will be transformed into individual
%% exports of each arity.
expand_exports(Modules) ->
    expand_exports(Modules, []).

expand_exports([], Memo) ->
    Memo;
expand_exports([M|Tail], Memo) ->
    F = fun({_, _}=FunWithArity) -> 
                FunWithArity;
           (Name) when is_list(Name) ->
                [{Name, A} || #alpaca_fun_def{
                                 name={symbol, _, N}, 
                                 arity=A
                                } <- M#alpaca_module.functions, N =:= Name]
        end,
    Exports = lists:flatten(lists:map(F, M#alpaca_module.function_exports)),
    expand_exports(Tail, [M#alpaca_module{function_exports=Exports}|Memo]).

%% Assumes that expand_exports has already been run on the supplied modules.
%% Runs through each module's imports and converts any import without arity
%% to individual imports for each arity of that function exported from its
%% defining module.
expand_imports(Modules) ->
    %% Use a map from a module's name to its exported functions to
    %% expand all imports unqualified with arity:
    F = fun(#alpaca_module{}=Mod, Map) ->
                #alpaca_module{name=N, function_exports=FEs} = Mod,
                maps:put(N, FEs, Map)
        end,
    ExportMap = lists:foldl(F, maps:new(), Modules),
    expand_imports(Modules, ExportMap, []).

expand_imports([], _, Memo) ->
    Memo;
expand_imports([M|Tail], ExportMap, Memo) ->
    F = fun({_, {_, _}}=FunWithArity) ->
                FunWithArity;
           ({Fun, Mod}) when is_atom(Mod) ->
                Default = {error, {no_module, Mod}},
                case maps:get(Mod, ExportMap, Default) of
                    {error, _}=Err ->
                        throw(Err);
                    Funs ->
                        [{Fun, {Mod, A}} || {FN, A} <- Funs, FN =:= Fun]
                end
        end,
    Imports = lists:flatten(lists:map(F, M#alpaca_module.function_imports)),
    M2 = M#alpaca_module{function_imports=Imports},
    expand_imports(Tail, ExportMap, [M2|Memo]).

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

rebind_and_validate_module(_, {error, _} = Err, _) ->
    Err;
rebind_and_validate_module(NextVarNum, #alpaca_module{}=Mod, Modules) ->
    validate_user_types(rebind_and_validate_functions(NextVarNum, Mod, Modules)).

%% Used to track a variety of data that both rename_bindings and make_bindings
%% require:
-record(env, {
          %% Used for making replacement names:
          next_var=0 :: integer(),
          %% Tracks new variable name -> old variable name:
          rename_map=maps:new() :: map(),
          %% Tracks bindings in scope so that we can find out if a function
          %% being called is defined locally, in the module, or from an
          %% import:
          current_bindings=[] :: list({string(), arity()}),
          %% The module we're currently working on:
          current_module=#alpaca_module{} :: alpaca_module(),
          %% The other modules that imports could be pulled from:
          modules=[] :: list(alpaca_module())
         }).

%% All available modules required so that we can rewrite applications of
%% functions not in Mod to inter-module calls.
rebind_and_validate_functions(NextVarNum, #alpaca_module{}=Mod, Modules) ->
    #alpaca_module{name=MN, functions=Funs}=Mod,
    Bindings = [{N, A} || #alpaca_fun_def{name={_, _, N}, arity=A} <- Funs],
    Env = #env{next_var=NextVarNum,
               rename_map=maps:new(),
               current_bindings=Bindings,
               current_module=Mod,
               modules=Modules},

    F = fun(_, {error, _}=Err) ->
                Err;
           (F, {E, Memo}) ->
                {#env{next_var=NV2, rename_map=M}, M2, F2} = rename_bindings(E, F),
                    
                %% We invert the returned map so that it is from
                %% synthetic variable name to source code variable
                %% name for later lookup:
                Inverted = [{V, K}||{K, V} <- maps:to_list(M2)],
                M3 = maps:merge(M2, maps:from_list(Inverted)),
                {Env#env{next_var=NV2, rename_map=M3}, [F2|Memo]}
        end,
    case lists:foldl(F, {Env, []}, Funs) of
        {error, _}=Err ->
            Err;
        {#env{next_var=NV2, rename_map=M}, Funs2} ->
            %% TODO:  other parts of the compiler might care about the rename
            %%        map but we do throw away some details deliberately
            %%        when rewriting patterns and different function versions.
            %%        Probably worth expanding the symbol AST node to track
            %%        an original name.
            {ok, NV2, Mod#alpaca_module{functions=lists:reverse(Funs2)}}
    end.

validate_user_types({error, _}=Err) ->
    Err;
validate_user_types({ok, _, #alpaca_module{types=Ts}}=Res) ->
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
        Env::#env{},
        TopLevel::alpaca_fun_def()) -> {integer(), map(), alpaca_fun_def()} |
                                     {error, term()}.
rename_bindings(Environment, #alpaca_fun_def{}=TopLevel) ->
    #alpaca_fun_def{name={symbol, _, Name}, versions=Vs}=TopLevel,
    SeedMap = #{Name => Name},

    F = fun(#alpaca_fun_version{args=As, body=Body}=FV, {Env, Map, Versions}) ->
                case make_bindings(Env, Map, As) of
                    {Env2, M2, Args} ->
                        case rename_bindings(Env2, M2, Body) of
                            {Env3, M3, E} ->
                                FV2 = FV#alpaca_fun_version{
                                        args=Args,
                                        body=E},
                                %% As with patterns and clauses we deliberately
                                %% throw away the rename map here so that the
                                %% same symbols can be reused by distinctly
                                %% different function definitions.
                                {Env3, Map, [FV2|Versions]};
                            {error, _} = Err -> 
                                throw(Err)
                        end;
                    {error, _} = E -> throw(E)
                end
        end,

    {Env, M2, Vs2} = lists:foldl(F, {Environment, maps:new(), []}, Vs),
    {Env, M2, TopLevel#alpaca_fun_def{versions=Vs2}}.

rebind_args(Env, Map, Args) ->
    F = fun({error, _} = E, _) -> E;
           ({symbol, L, N}, {#env{next_var=NV}=E, AccMap, Syms}) ->
                case maps:get(N, AccMap, undefined) of
                    undefined ->
                        Synth = next_var(NV),
                        { E#env{next_var=NV+1}
                        , maps:put(N, Synth, AccMap)
                        , [{symbol, L, Synth}|Syms]
                        };
                    _ ->
                        throw({duplicate_definition, N, L})
                end;
           ({unit, _}=U, {E, AccMap, Syms}) ->
                {E, AccMap, [U|Syms]};
           (Arg, {E, AccMap, Syms}) ->
                {E, AccMap, [Arg|Syms]}
        end,
    case lists:foldl(F, {Env, Map, []}, Args) of
        {Env2, M, Args2} -> {Env2, M, lists:reverse(Args2)};
        {error, _}=Err -> Err
    end.

rename_bindings(Env, Map, #fun_binding{def=Def, expr=E}) ->
    case rename_bindings(Env, Map, Def) of
        {error, _} = Err ->
            Err;
        {Env2, M2, Def2} -> case rename_bindings(Env2, M2, E) of
                              {error, _} = Err ->
                                    Err;
                              {Env3, M3, E2} ->
                                    {Env3, M3, #fun_binding{def=Def2, expr=E2}}
                          end
    end;

rename_bindings(Environment, M, #alpaca_fun_def{name={symbol, L, Name}}=Def) ->
    #alpaca_fun_def{versions=Vs}=Def,
    {NewName, En2, M2} = case maps:get(Name, M, undefined) of
                              undefined ->
                                  #env{next_var=NV} = Environment,
                                  Synth = next_var(NV),
                                  E2 = Environment#env{next_var=NV+1},
                                  {Synth, E2, maps:put(Name, Synth, M)};
                              _ ->
                                  throw({duplicate_definition, Name, L})
                          end,

    F = fun(#alpaca_fun_version{}=FV, {Env, Map, NewVersions}) ->
                #alpaca_fun_version{args=Args, body=Body} = FV,
                case rebind_args(Env, Map, Args) of
                    {error, _}=Err ->
                        throw(Err);
                    {Env2, M3, Args2} ->
                        case rename_bindings(Env2, M3, Body) of
                            {error, _}=Err -> 
                                throw(Err);
                            {Env3, M4, Body2} ->
                                FV2 = FV#alpaca_fun_version{
                                        args=Args2,
                                        body=Body2},
                                %% As with patterns and clauses we deliberately
                                %% throw away the rename map here so that the
                                %% same symbols can be reused by distinctly
                                %% different function definitions.
                                {Env3, Map, [FV2|NewVersions]}
                        end
                end
           end,
    {Env3, Map2, Vs2} = lists:foldl(F, {En2, M2, []}, Vs),
    NewDef = Def#alpaca_fun_def{name={symbol, L, NewName}, versions=lists:reverse(Vs2)},
    {Env3, Map2, NewDef};
    
rename_bindings(#env{next_var=NextVar}=Env, Map, #var_binding{}=VB) ->
    #var_binding{name={symbol, L, N}, to_bind=TB, expr=E} = VB,
    case maps:get(N, Map, undefined) of
        undefined ->
            Synth = next_var(NextVar),
            M2 = maps:put(N, Synth, Map),
            case rename_bindings(Env#env{next_var=NextVar+1}, M2, TB) of
                {error, _} = Err ->
                    Err;
                {Env2, M3, TB2} ->
                    case rename_bindings(Env2, M3, E) of
                        {error, _} = Err -> Err;
                        {Env3, M4, E2} ->
                            VB2 = #var_binding{
                                     name={symbol, L, Synth},
                                     to_bind=TB2,
                                     expr=E2},
                            {Env3, M4, VB2}
                    end
            end;
        _ ->
            throw({duplicate_definition, N, L})
    end;

rename_bindings(Env, Map, #alpaca_apply{expr=N, args=Args}=App) ->
    %% Functions to extract the locally defined top-level functions and
    %% the ones available via imports.  When renaming a function name
    %% comes back unchanged, it's one of the following:
    %%   - a module-local function, no need to rewrite the apply
    %%   - a reference to an imported function, rewrite as an inter-module call
    %%   - a reference to an undefined function.  Leave the error to the typer.
    ModFuns = fun () ->
                      Mod = Env#env.current_module,
                      #alpaca_module{functions=Fs} = Mod,
                      [{{X, A}, local} || #alpaca_fun_def{name={_, _, X}, arity=A} <- Fs]
              end,
    ImpFuns = fun () ->
                      Mod = Env#env.current_module,
                      #alpaca_module{function_imports=Imps} = Mod,
                      [{{X, A}, Mod} || {X, {Mod, A}} <- Imps]
              end,

    FName = case N of
                {symbol, _, FN} = S ->
                    case rename_bindings(Env, Map, S) of
                        %% Not renamed so either calling a top level function
                        %% in the current module or it's a refernce to something
                        %% that might be imported:
                        {_, _, N} ->
                            {symbol, _, FN} = N,
                            Arity = length(Args),
                            AllFuns = ModFuns() ++ ImpFuns(),
                            case proplists:get_value({FN, Arity}, AllFuns, undef) of
                                local -> N;
                                undef -> N;
                                Mod -> {Mod, N, Arity}
                            end;
                        %% Renamed, proceed:
                        {_, _, X} -> X
                    end;
                _ -> N
            end,
    {_, _, Name} = rename_bindings(Env, Map, FName),
    case rename_binding_list(Env, Map, Args) of
        {error, _} = Err -> Err;
        {Env2, M2, Args2} ->
            {Env2, M2, App#alpaca_apply{expr=Name, args=Args2}}
    end;

rename_bindings(Env, Map, #alpaca_spawn{function=F, args=Args}=Spawn) ->
    {_, _, FName} = rename_bindings(Env, Map, F),
    FArgs = [X||{_, _, X} <- [rename_bindings(Env, Map, A)||A <- Args]],
    #env{current_module=#alpaca_module{name=MN}} = Env,
    {Env, Map, Spawn#alpaca_spawn{
                     function=FName,
                     from_module=MN,
                     args=FArgs}};

rename_bindings(Env, Map, #alpaca_send{message=M, pid=P}=Send) ->
    {_, _, M2} = rename_bindings(Env, Map, M),
    {_, _, P2} = rename_bindings(Env, Map, P),
    {Env, Map, Send#alpaca_send{message=M2, pid=P2}};

rename_bindings(Env, Map, #alpaca_type_apply{arg=none}=A) ->
    {Env, Map, A};
rename_bindings(Env, Map, #alpaca_type_apply{arg=Arg}=A) ->
    case rename_bindings(Env, Map, Arg) of
        {error, _}=Err -> Err;
        {Env2, M, Arg2} -> {Env2, M, A#alpaca_type_apply{arg=Arg2}}
    end;
rename_bindings(Env, Map, #alpaca_type_check{expr=E}=TC) ->
    case rename_bindings(Env, Map, E) of
        {error, _}=Err -> Err;
        {Env2, M, E2} -> {Env2, M, TC#alpaca_type_check{expr=E2}}
    end;

rename_bindings(Env, Map, #alpaca_cons{head=H, tail=T}=Cons) ->
    case rename_bindings(Env, Map, H) of
        {error, _} = Err -> Err;
        {Env2, M, H2} -> case rename_bindings(Env2, M, T) of
                             {error, _} = Err -> Err;
                             {Env3, M2, T2} -> {Env3, M2, Cons#alpaca_cons{
                                                            head=H2,
                                                            tail=T2}}
                         end
    end;
rename_bindings(Env, Map, #alpaca_binary{segments=Segs}=B) ->
    %% fold to account for errors.
    F = fun(_, {error, _}=Err) -> Err;
           (#alpaca_bits{value=V}=Bits, {E, M, Acc}) ->
                case rename_bindings(E, M, V) of
                    {E2, M2, V2} -> {E2, M2, [Bits#alpaca_bits{value=V2}|Acc]};
                    {error, _}=Err -> Err
                end
        end,
    case lists:foldl(F, {Env, Map, []}, Segs) of
        {error, _}=Err ->
            Err;
        {Env2, M2, Segs2} ->
            {Env2, M2, B#alpaca_binary{segments=lists:reverse(Segs2)}}
    end;
rename_bindings(Env, Map, #alpaca_map{pairs=Pairs}=ASTMap) ->
    Folder = fun(_, {error, _}=Err) -> Err;
                (P, {E, M, Ps}) ->
                     case rename_bindings(E, M, P) of
                         {error, _}=Err -> Err;
                         {E2, M2, P2} -> {E2, M2, [P2|Ps]}
                     end
             end,
    case lists:foldl(Folder, {Env, Map, []}, Pairs) of
        {error, _}=Err ->
            Err;
        {Env2, M, Pairs2} ->
            {Env2, M, ASTMap#alpaca_map{pairs=lists:reverse(Pairs2)}}
    end;
rename_bindings(Env, Map, #alpaca_map_add{to_add=A, existing=B}=ASTMap) ->
    case rename_bindings(Env, Map, A) of
        {error, _}=Err ->
            Err;
        {Env2, M, A2} ->
            case rename_bindings(Env2, M, B) of
                {error, _}=Err ->
                    Err;
                {Env3, M2, B2} ->
                    {Env3, M2, ASTMap#alpaca_map_add{to_add=A2, existing=B2}}
            end
    end;
rename_bindings(Env, Map, #alpaca_map_pair{key=K, val=V}=P) ->
    case rename_bindings(Env, Map, K) of
        {error, _}=Err ->
            Err;
        {Env2, M, K2} ->
            case rename_bindings(Env2, M, V) of
                {error, _}=Err ->
                    Err;
                {Env3, M2, V2} ->
                    {Env3, M2, P#alpaca_map_pair{key=K2, val=V2}}
            end
    end;
rename_bindings(Env, Map, #alpaca_tuple{values=Vs}=T) ->
    case rename_binding_list(Env, Map, Vs) of
        {error, _} = Err -> Err;
        {Env2, _, Vals2} -> {Env2, Map, T#alpaca_tuple{values=Vals2}}
    end;

rename_bindings(Env, Map, #alpaca_record{members=Members}=R) ->
    F = fun(#alpaca_record_member{val=V}=RM, {NewMembers, E, M}) ->
                case rename_bindings(E, M, V) of
                    {error, _}=E ->
                        erlang:error(E);
                    {E2, M2, V2} ->
                        {[RM#alpaca_record_member{val=V2}|NewMembers], E2, M2}
                end
        end,
    {NewMembers, Env2, Map2} = lists:foldl(F, {[], Env, Map}, Members),
    {Env2, Map2, R#alpaca_record{members=lists:reverse(NewMembers)}};

rename_bindings(Env, Map, {symbol, L, N}=S) ->
    case maps:get(N, Map, undefined) of
        undefined ->
            %% if there's a top-level binding we use that, otherwise
            %% try to resolve the symbol from imports:
            Mod = Env#env.current_module,
            Funs = Mod#alpaca_module.functions,
            case [FN || #alpaca_fun_def{name=FN} <- Funs, FN =:= N] of
                [_|_] -> {Env, Map, S};
                [] ->
                    Imports = Mod#alpaca_module.function_imports,
                    case [{M, A} || {FN, {M, A}} <- Imports, FN =:= N] of
                        [{Module, Arity}|_] ->
                            io:format("Rewriting ~s to ~w~n", [N, Arity]),
                            FR = #alpaca_far_ref{
                                    module=Module,
                                    name=N,
                                    line=L,
                                    arity=Arity},
                            {Env, Map, FR};
                        [] ->
                            {Env, Map, S}
                    end
            end;
        Synthetic -> {Env, Map, {symbol, L, Synthetic}}
    end;
rename_bindings(Env, Map, #alpaca_far_ref{module=M, name=N, arity=none}=FR) ->
    %% Find the first exported occurrence of M:N
    Modules = [Mod || #alpaca_module{name=MN}=Mod <- Env#env.modules, M =:= MN],
    case Modules of
        [Mod] ->
            As = [A || {F, A} <- Mod#alpaca_module.function_exports, F =:= N],
            case As of
                [A|_] -> {Env, Map, FR#alpaca_far_ref{arity=A}};
                _     -> throw({error, {not_exported, M, N}})
            end;
        _ ->
            throw({error, {no_module, M}})
    end;

rename_bindings(Env, M, #alpaca_ffi{args=Args, clauses=Cs}=FFI) ->
    case rename_bindings(Env, M, Args) of
        {error, _} = Err ->
            Err;
        {Env2, M2, Args2} ->
            case rename_clause_list(Env2, M2, Cs) of
                {error, _} = Err ->
                    Err;
                {Env3, M3, Cs2} ->
                    {Env3, M3, FFI#alpaca_ffi{args=Args2, clauses=Cs2}}
            end
    end;
rename_bindings(Env, M, #alpaca_match{}=Match) ->
    #alpaca_match{match_expr=ME, clauses=Cs} = Match,
    case rename_bindings(Env, M, ME) of
        {error, _} = Err -> Err;
        {Env2, M2, ME2} ->
            case rename_clause_list(Env2, M2, Cs) of
                {error, _} = Err ->
                    Err;
                {Env3, M3, Cs2} ->
                    {Env3, M3, Match#alpaca_match{match_expr=ME2, clauses=Cs2}}
            end
    end;

rename_bindings(Env, M, #alpaca_receive{clauses=Cs}=Recv) ->
    case rename_clause_list(Env, M, Cs) of
        {error, _} = Err -> Err;
        {Env2, M2, Cs2}   -> {Env2, M2, Recv#alpaca_receive{clauses=Cs2}}
    end;

rename_bindings(Env, M, #alpaca_clause{pattern=P, guards=Gs, result=R}=Clause) ->
    %% pattern matches create new bindings and as such we don't
    %% just want to use existing substitutions but rather error
    %% on duplicates and create entirely new ones:
    case make_bindings(Env, M, P) of
        {error, _} = Err -> Err;
        {Env2, M2, P2} ->
            case rename_bindings(Env2, M2, R) of
                {error, _} = Err -> Err;
                {Env3, M3, R2} ->
                    case rename_binding_list(Env3, M3, Gs) of
                        {error, _}=Err -> Err;
                        {Env4, _M4, Gs2} ->

                            %% we actually throw away the modified map here
                            %% because other patterns should be able to
                            %% reuse variable names:
                            {Env4, M, Clause#alpaca_clause{
                                       pattern=P2,
                                       guards=Gs2,
                                       result=R2}}
                    end
            end
    end;
rename_bindings(Env, Map, Expr) ->
    {Env, Map, Expr}.

rename_binding_list(Env, Map, Bindings) ->
    F = fun(_, {error, _} = Err) -> Err;
           (A, {E, M, Memo}) ->
                case rename_bindings(E, M, A) of
                    {error, _} = Err -> Err;
                    {E2, M2, A2} -> {E2, M2, [A2|Memo]}
                end
        end,
    case lists:foldl(F, {Env, Map, []}, Bindings) of
        {error, _} = Err -> Err;
        {Env2, M, Bindings2} -> {Env2, M, lists:reverse(Bindings2)}
    end.

%% For renaming bindings in a list of clauses.  Broken out from pattern
%% matching because it will be reused for FFI and receive.
rename_clause_list(Env, M, Cs) ->
    F = fun(_, {error, _}=Err) -> Err;
           (C, {E, Map, Memo}) ->
                case rename_bindings(E, Map, C) of
                    {error, _} = Err -> Err;
                    {E2, Map2, C2} -> {E2, Map2, [C2|Memo]}
                end
        end,
    case lists:foldl(F, {Env, M, []}, Cs) of
        {error, _} = Err -> Err;
        {Env2, M2, Cs2} -> {Env2, M2, lists:reverse(Cs2)}
    end.

%%% Used for pattern matches so that we're sure that the patterns in each
%%% clause contain unique bindings.
make_bindings(Env, M, [_|_]=Xs) ->
    {Env2, M2, Xs2} = lists:foldl(
                        fun(X, {E, Map, Memo}) ->
                                case make_bindings(E, Map, X) of
                                    {error, _}=Err -> throw(Err);
                                    {E2, M2, A2} -> {E2, M2, [A2|Memo]}
                                end
                        end,
                        {Env, M, []},
                        Xs),
    {Env2, M2, lists:reverse(Xs2)};

make_bindings(Env, M, #alpaca_tuple{values=Vs}=Tup) ->
    F = fun(_, {error, _}=E) -> E;
           (V, {E, Map, Memo}) ->
                case make_bindings(E, Map, V) of
                    {error, _} = Err -> Err;
                    {E2, M2, V2} -> {E2, M2, [V2|Memo]}
                end
        end,
    case lists:foldl(F, {Env, M, []}, Vs) of
        {error, _} = Err ->
            Err;
        {Env2, M2, Vs2} ->
            {Env2, M2, Tup#alpaca_tuple{values=lists:reverse(Vs2)}}
    end;
make_bindings(Env, M, #alpaca_cons{head=H, tail=T}=Cons) ->
    case make_bindings(Env, M, H) of
        {error, _} = Err -> Err;
        {Env2, M2, H2} -> case make_bindings(Env2, M2, T) of
                              {error, _} = Err ->
                                  Err;
                              {Env3, M3, T2} ->
                                  {Env3, M3, Cons#alpaca_cons{head=H2, tail=T2}}
                          end
    end;
%% TODO:  this is identical to rename_bindings but for the internal call
%% to make_bindings vs rename_bindings.  How much else in here is like this?
%% Probably loads of abstracting/de-duping potential.
make_bindings(Env, Map, #alpaca_binary{segments=Segs}=B) ->
    F = fun(_, {error, _}=Err) ->
                Err;
           (#alpaca_bits{value=V}=Bits, {E, M, Acc}) ->
                case make_bindings(E, M, V) of
                    {E2, M2, V2} ->
                        {E2, M2, [Bits#alpaca_bits{value=V2}|Acc]};
                    {error, _}=Err ->
                        Err
                end
        end,
    case lists:foldl(F, {Env, Map, []}, Segs) of
        {error, _}=Err ->
            Err;
        {Env2, M2, Segs2} ->
            {Env2, M2, B#alpaca_binary{segments=lists:reverse(Segs2)}}
    end;

%%% Map patterns need to rename variables used for keys and create new bindings
%%% for variables used for values.  We want to rename for keys because we want
%%% the following to work:
%%%
%%%     get my_key my_map = match my_map with
%%%       #{my_key => v} -> v
%%%
%%% Map patterns require the key to be something exact already.
make_bindings(Env, BindingMap, #alpaca_map{pairs=Ps}=Map) ->
    Folder = fun(_, {error, _}=Err) -> Err;
                (P, {E, M, Acc}) ->
                     case make_bindings(E, M, P) of
                         {error, _}=Err -> Err;
                         {E2, M2, P2}   -> {E2, M2, [P2|Acc]}
                     end
             end,
    case lists:foldl(Folder, {Env, BindingMap, []}, Ps) of
        {error, _}=Err -> Err;
        {Env2, M, Pairs} ->
            Map2 = Map#alpaca_map{is_pattern=true, pairs=lists:reverse(Pairs)},
            {Env2, M, Map2}
    end;
make_bindings(Env, M, #alpaca_map_pair{key=K, val=V}=P) ->
    case rename_bindings(Env, M, K) of
        {error, _}=Err -> Err;
        {Env2, M2, K2} ->
            case make_bindings(Env2, M2, V) of
                {error, _}=Err ->
                    Err;
                {Env3, M3, V2} ->
                    {Env3, M3, P#alpaca_map_pair{is_pattern=true, key=K2, val=V2}}
            end
    end;

%% Records can be compiled as maps so we need the is_pattern parameter
%% on their AST nodes set correctly here too.
make_bindings(Env, M, #alpaca_record{members=Members}=R) ->
    F = fun(#alpaca_record_member{val=V}=RM, {NewVs, E, Map}) ->
                case make_bindings(E, Map, V) of
                    {error, _}=Err ->
                        erlang:error(Err);
                    {E2, Map2, V2} ->
                        NewR = RM#alpaca_record_member{val=V2},
                        {[NewR|NewVs], E2, Map2}
                end
        end,
    {Members2, Env2, M2} = lists:foldl(F, {[], Env, M}, Members),
    NewR = R#alpaca_record{
             members=lists:reverse(Members2),
             is_pattern=true},
    {Env2, M2, NewR};

make_bindings(Env, M, #alpaca_type_apply{arg=none}=TA) ->
    {Env, M, TA};
make_bindings(Env, M, #alpaca_type_apply{arg=Arg}=TA) ->
    case make_bindings(Env, M, Arg) of
        {Env2, M2, Arg2} -> {Env2, M2, TA#alpaca_type_apply{arg=Arg2}};
        {error, _}=Err  -> Err
    end;

make_bindings(Env, M, {symbol, L, Name}) ->
    case maps:get(Name, M, undefined) of
        undefined ->
            #env{next_var=NV} = Env,
            Synth = next_var(NV),
            Env2 = Env#env{next_var=NV+1},
            {Env2, maps:put(Name, Synth, M), {symbol, L, Synth}};
        _ ->
            throw({duplicate_definition, Name, L})
    end;
make_bindings(Env, M, Expression) ->
    {Env, M, Expression}.

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
     ?_assertError({badmatch, {error, {duplicate_type, "t"}}},
                   make_modules(["module dupe_types_1\n\n"
                                "type t = A | B\n\n"
                                "type t = C | int"])),
     ?_assertError({badmatch, {error, {duplicate_constructor, "A"}}},
                   make_modules(["module dupe_type_constructor\n\n"
                                 "type t = A int | B\n\n"
                                 "type u = X float | A\n\n"])),
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
    [?_assertMatch({ok, {import, [{"foo", some_mod},
                                  {"bar", {some_mod, 2}}]}},
                   parse(alpaca_scanner:scan("import some_mod.[foo, bar/2]"))),
     ?_assertMatch(
        {ok, {import, [{"foo", mod1},
                       {"bar", {mod2, 1}},
                       {"baz", mod2}]}},
        parse(alpaca_scanner:scan("import mod1.foo, mod2.[bar/1, baz]"))),
     fun() ->
             Code1 =
                 "module two_lines_of_imports\n\n"
                 "import foo.bar/2\n\n"
                 "import math.[add/2, sub/2, mult]",

             ?assertMatch(
                #alpaca_module{
                    function_imports=[{"bar", {foo, 2}},
                                      {"add", {math, 2}},
                                      {"sub", {math, 2}},
                                      {"mult", math}]},
                parse_module(Code1))
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
       [#alpaca_module{
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
                                                            {symbol,7,"svar_1"}]}}}]}]}],
       make_modules([Code])).

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
       [#alpaca_module{
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
                                                             {symbol,11,"svar_6"}]}}]}]}],
       make_modules([Code])).

break_test() ->
    % We should tolerate whitespace between the two break tokens
    Code = "module test_mod\n\n
            let a = 5\n   \n"
           "let b = 6\n\n",
     ?assertMatch(
       [#alpaca_module{
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
       ]}],
       make_modules([Code])).
    

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
                   rename_bindings(#env{}, A)),
     ?_assertException(throw, 
                       {duplicate_definition, "x", 2},
                       rename_bindings(#env{}, B)),
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
        rename_bindings(#env{}, C)),
     ?_assertException(throw,
                       {duplicate_definition, "x", 2},
                       rename_bindings(#env{}, D)),
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
        rename_bindings(#env{}, E)),
     ?_assertException(throw, 
                       {duplicate_definition, "y", 2},
                       rename_bindings(#env{}, F))
    ].

type_expr_in_type_declaration_test() ->
    ?assertMatch({error, _}, test_parse("type a not_a_var = A not_a_var")).

expand_exports_test_() ->
    [fun() ->
             Def = fun(Name, Arity) ->
                           #alpaca_fun_def{name={symbol, 0, Name}, arity=Arity}
                   end,

             Ms = [#alpaca_module{
                      function_exports=["foo", {"bar", 1}],
                      functions=[Def("foo", 1), Def("foo", 2), Def("bar", 1)]}],
             [#alpaca_module{function_exports=FEs}] = expand_exports(Ms, []),
             ?assertEqual([{"foo", 1}, {"foo", 2}, {"bar", 1}], FEs)
     end
    , fun() ->
              Code =
                  "module test_export_all_funs\n\n"
                  "export foo, bar/1\n\n"
                  "foo x = x\n\n"
                  "foo x y = x + y\n\n"
                  "bar x = x",

              [Mod] = make_modules([Code]),
              [#alpaca_module{function_exports=FEs}] = expand_exports([Mod], []),
              ?assertEqual([{"foo", 1}, {"foo", 2}, {"bar", 1}], FEs)
      end
    ].

expand_imports_test_() ->
    [fun() ->
             Code1 =
                 "module m1\n\n"
                 "export foo\n\n"
                 "foo x = x\n\n"
                 "foo x y = x + y",

             Code2 =
                 "module m2\n\n"
                 "import m1.foo",

             [Mod1, Mod2] = make_modules([Code1, Code2]),
             WithExports = expand_exports([Mod1, Mod2]),
             [M1, M2] = expand_imports(WithExports),
             ?assertMatch(
                #alpaca_module{
                   function_exports=[_, _],
                   function_imports=[]},
                M1),
             ?assertMatch(
                #alpaca_module{
                   function_imports=[{"foo", {m1, 1}}, {"foo", {m1, 2}}]},
                M2)
     end
    , fun() ->
              Code =
                  "module m\n\n"
                  "import n.foo",

              Mod = parse_module(Code),
              ?assertThrow({error, {no_module, n}},
                           expand_imports(expand_exports([Mod])))
      end
    ].

import_rewriting_test_() ->
    [fun() ->
             Code1 =
                 "module a\n\n"
                 "export add/2\n\n"
                 "add x y = x + y",
             Code2 =
                 "module b\n\n"
                 "import a.add\n\n"
                 "f () = add 2 3",
             ?assertMatch(
                [#alpaca_module{name=a},
                 #alpaca_module{
                    name=b,
                    functions=[#alpaca_fun_def{
                                  versions=[#alpaca_fun_version{
                                               body=#alpaca_apply{
                                                       expr=#alpaca_far_ref{
                                                               module=a,
                                                               name="add",
                                                               arity=2}
                                                      }}]
                                 }]}],
                make_modules([Code1, Code2]))
     end
    , fun() ->
              Code1 =
                 "module a\n\n"
                  "export (|>)\n\n"
                  "(|>) x y = y x",
              Code2 =
                  "module b\n\n"
                  "import a.(|>)\n\n"
                  "add_ten x = x + 10\n\n"
                  "f () = 2 |> add_ten",
              ?assertMatch(
                 [#alpaca_module{name=a},
                  #alpaca_module{
                     name=b,
                     functions=[_,
                                #alpaca_fun_def{
                                   versions=[#alpaca_fun_version{
                                                body=#alpaca_apply{
                                                        expr=#alpaca_far_ref{
                                                                module=a,
                                                                name="(|>)",
                                                                arity=2}
                                                       }}]
                                  }]}],
                 make_modules([Code1, Code2]))
      end
    ].
-endif.
