%%% -*- mode: erlang;erlang-indent-level: 4;indent-tabs-mode: nil -*-
%%% ex: ft=erlang ts=4 sw=4 et
-module(alpaca_ast_gen).
-export([parse/1, make_modules/1, make_modules/2, make_modules/3, term_line/1, list_dependencies/1]).

%% Parse is used by other modules (particularly alpaca_typer) to make ASTs
%% from code that does not necessarily include a module;
%% make_modules/1 is useful externally for a simple way of compiling
%% multiple source files together; list_dependencies allows external tools
%% to extract module dependencies from source code without compiling.
-ignore_xref([parse/1, make_modules/1, make_modules/2]).

-include("alpaca_ast.hrl").

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

-type parse_error() :: {parse_error, filename(), line(), error_reason()}.

-type builtin_type() :: alpaca_base_type() |
                        alpaca_list_type() |
                        alpaca_map_type() |
                        alpaca_pid_type().

-type error_reason() :: {duplicate_definition, string()} |
                        {duplicate_type, string()} |
                        {function_not_exported, module(), string()} |
                        {invalid_bin_qualifier, string()} |
                        {invalid_bin_type, string()} |
                        {invalid_endianness, string()} |
                        {invalid_fun_parameter, term()} |
                        {invalid_top_level_construct, term()} |
                        {module_rename, module(), module()} |
                        no_module |
                        {no_module, module()} |
                        {syntax_error, string()} |
                        {wrong_type_arity, builtin_type(), non_neg_integer()}.

-type filename() :: string().
-type line() :: integer().

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
%% make_modules/1 provides one entry point that can be used to cover all three
%% steps for a list of code strings.
%%
%% make_modules/2 takes an additional argument of a list of already compiled
%% modules, i.e. the AST containing the type information. This can be
%% retrieved from the module attributes of a BEAM file compiled by Alpaca.
%% This allows the typer to verify against precompiled modules without
%% having to recompile everything from scratch.

-spec make_modules(Sources) -> {ok, [alpaca_module()]} | {error, Error} when
    Sources :: list(Source),
    Source :: {filename(), Code},
    Code :: string() | binary(),
    Error :: parse_error().
make_modules(Code) ->
    try
      Modules = [parse_module(SourceCode) || SourceCode <- Code],
      {ok, rename_and_resolve(Modules)}
    catch
        throw:{parse_error, _, _, _}=Err -> {error, Err}
    end.

-spec make_modules(Sources, PrecompiledMods, DefaultImports) ->
    {ok, [alpaca_module()]} | {error, Error} when
        Sources :: list(Source),
        Source :: {filename(), Code},
        PrecompiledMods :: list(PrecompiledMod),
        PrecompiledMod :: {filename(), alpaca_module()},
        DefaultTypes :: list({string(), {atom(), integer()}|string()}),
        DefaultFuns :: list(alpaca_type_import()),
        DefaultImports :: {DefaultFuns, DefaultTypes},
        Code :: string() | binary(),
        Error :: parse_error().
make_modules(Code, PrecompiledMods, DefaultImports) ->
    try
      Modules = [parse_module(SourceCode) || SourceCode <- Code],
      PCMods = [M || {_FN, M} <- PrecompiledMods],

      {DefaultFuns, DefaultTypes} = DefaultImports,

      DefaultFunsA = lists:map(
          fun ({Mod, F}) -> {F, Mod};
              ({Mod, F, Arity}) -> {F, {Mod, Arity}}
          end,
          DefaultFuns),

      DefaultTypesA = lists:map(
          fun({Mod, T}) -> #alpaca_type_import{module=Mod, type=T} end,
          DefaultTypes),

      %% Inject funs
      ModulesWithDefaults = lists:map(
          fun(#alpaca_module{function_imports=Imports, type_imports=Types}=M) ->
              M#alpaca_module{
                  function_imports=Imports ++ DefaultFunsA,
                  type_imports=Types ++ DefaultTypesA}
          end,
          Modules),

      {ok, rename_and_resolve(PCMods ++ ModulesWithDefaults)}
    catch
        throw:{parse_error, _, _, _}=Err -> {error, Err}
    end.

-spec make_modules(Sources, PrecompiledMods) ->
    {ok, [alpaca_module()]} | {error, Error} when
        Sources :: list(Source),
        Source :: {filename(), Code},
        PrecompiledMods :: list(PrecompiledMod),
        PrecompiledMod :: {filename(), alpaca_module()},
        Code :: string() | binary(),
        Error :: parse_error().
make_modules(Code, PrecompiledMods) ->
    make_modules(Code, PrecompiledMods, {[], []}).

parse_error(#alpaca_module{filename=FileName}, Line, Error) ->
    throw({parse_error, FileName, Line, Error}).

parse({ok, Tokens, _}) ->
    parse(Tokens);
parse(Tokens) when is_list(Tokens) ->
    alpaca_parser:parse(Tokens).

parse_module({FileName, Text}) when is_binary(Text) ->
    parse_module({FileName, binary:bin_to_list(Text)});
parse_module({FileName, Text}) when is_list(Text) ->
    {ok, Tokens, _} = alpaca_scanner:scan(Text),
    Version = proplists:get_value(version, alpaca:compiler_info()),
    Hash = crypto:hash(md5, unicode:characters_to_binary(Text ++ Version)),
    StartMod = #alpaca_module{filename=FileName, hash=Hash},
    Mod = parse_module(Tokens, StartMod),
    {ok, Mod2} = apply_signatures(Tokens, Mod),
    Mod2.

parse_module([], #alpaca_module{name=no_module}=M) ->
    parse_error(M, 1, no_module);
parse_module([], #alpaca_module{name=N, functions=Funs, types=Ts}=M) ->
    OrderedFuns = group_funs(Funs, N),
    TypesWithModule = [T#alpaca_type{module=N} || T <- Ts],
    M#alpaca_module{functions=OrderedFuns, types = TypesWithModule};
parse_module([{break, _}], Mod) ->
    parse_module([], Mod);
parse_module(Tokens, Mod) ->
    case next_batch(Tokens, []) of
        {[], Rem}        -> parse_module(Rem, Mod);
        {NextBatch, Rem} ->
            Parsed = try_parse(NextBatch, Mod),
            parse_module(Rem, update_memo(Mod, Parsed))
    end.

try_parse(Tokens, Mod) ->
    case parse(Tokens) of
        {ok, Res} -> Res;
        {error, {Line, alpaca_parser, ["syntax error before: ", ErrorToken]}} ->
          parse_error(Mod, Line, {syntax_error, ErrorToken});
        {error, {Line, alpaca_parser, Error}} ->
          parse_error(Mod, Line, Error)
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
                {NV2, Mod2} = rebind_and_validate_module(NV, Mod, Expanded),
                {NV2, [Mod2|Memo]}
        end,
    {_, Ms} = lists:foldl(F, {0, []}, Expanded),
    lists:reverse(Ms).

%% Any export that doesn't specify arity will be transformed into individual
%% exports of each arity.
expand_exports(Modules) ->
    expand_exports(Modules, []).

name_and_arity(#alpaca_binding{name=BindingName, bound_expr=E}) ->
    N = alpaca_ast:symbol_name(BindingName),
    case E of
        #alpaca_fun{arity=A} -> {N, A};
        _                    -> {N, 0}
    end.

expand_exports([], Memo) ->
    Memo;
expand_exports([M|Tail], Memo) ->
    F = fun({_, _}=FunWithArity) ->
                FunWithArity;
           (Name) when is_binary(Name) ->
                NameAndArity = [name_and_arity(F) || F <- M#alpaca_module.functions],
                [{Name, A} || {N, A} <- NameAndArity, N =:= Name]
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
                case maps:get(Mod, ExportMap, error) of
                    error ->
                        parse_error(M, 1, {no_module, Mod});
                    Funs ->
                        [{Fun, {Mod, A}} || {FN, A} <- Funs, FN =:= Fun]
                end
        end,
    Imports = lists:flatten(lists:map(F, M#alpaca_module.function_imports)),
    M2 = M#alpaca_module{function_imports=Imports},
    expand_imports(Tail, ExportMap, [M2|Memo]).

%% Group all functions by name and arity:
group_funs(Funs, _ModuleName) ->
    OrderedKeys =
        drop_dupes_preserve_order(
          lists:map(fun name_and_arity/1, lists:reverse(Funs)),
          []),
    F = fun(#alpaca_binding{name=BN, bound_expr=Expr}, Acc) ->
                N = alpaca_ast:symbol_name(BN),
                {N, A, V} = case Expr of
                                #alpaca_fun{arity=Arity, versions=[Ver]} ->
                                    {N, Arity, Ver};
                                _ ->
                                    {N, 0, Expr}
                         end,
                Key = {N, A},
                Existing = maps:get(Key, Acc, []),
                maps:put(Key, [V|Existing], Acc)
        end,
    Grouped = lists:foldl(F, maps:new(), Funs),
    lists:map(
      fun({N, A}=Key) ->
              NewVs = lists:reverse(maps:get(Key, Grouped)),
              [X|_] = NewVs,
              L = term_line(X),
              NewName = alpaca_ast:symbol(L, N),
              %% we use the first occurence's line as the function's primary
              %% location:
              case A of
                  0 ->
                      [OnlyV] = NewVs,
                      #alpaca_binding{name=NewName, line=L, bound_expr=OnlyV};
                  _ ->
                      #alpaca_binding{name=NewName,
                                      line=L,
                                      bound_expr=#alpaca_fun{
                                                    arity=A,
                                                    versions=NewVs}}
              end
      end,
      OrderedKeys).

term_line(Term) ->
    case Term of
        {_, L} when is_integer(L) -> L;
        {_, L, _} when is_integer(L) -> L;
        {C, Map}=ADT when is_atom(C), is_map(Map) -> alpaca_ast:line(ADT);
        {raise_error, L, _, _} -> L;
        {bif, _, L, _, _} -> L;
        #alpaca_apply{line=L} -> L;
        #alpaca_cons{line=L} -> L;
        #alpaca_map_pair{line=L} -> L;
        #alpaca_map{line=L} -> L;
        #alpaca_record{members=[#alpaca_record_member{line=L}|_]} -> L;
        #alpaca_record_transform{line=L} -> L;
        #alpaca_tuple{values=[H|_]} -> term_line(H);
        #alpaca_type_apply{name=N} -> term_line(N);
        #alpaca_fun{line=L} -> L;
        #alpaca_fun_version{line=L} -> L;
        #type_constructor{line=L} -> L
    end.


drop_dupes_preserve_order([], Memo) ->
    lists:reverse(Memo);
drop_dupes_preserve_order([H|T], [H|_]=Memo) ->
    drop_dupes_preserve_order(T, Memo);
drop_dupes_preserve_order([H|T], Memo) ->
    drop_dupes_preserve_order(T, [H|Memo]).

rebind_and_validate_module(NextVarNum, #alpaca_module{}=Mod, Modules) ->
    {_, EndMod}=Res = rebind_and_validate_functions(NextVarNum, Mod, Modules),
    validate_user_types(EndMod),
    Res.

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
    #alpaca_module{name=_MN, functions=Funs, tests=Tests}=Mod,
    BindingF = fun(#alpaca_binding{name=NSym, bound_expr=BE}) ->
                       N = alpaca_ast:symbol_name(NSym),
                       case BE of
                           #alpaca_fun{arity=A} -> {N, A};
                           _ -> {N, 0}
                       end
               end,
    Bindings = [BindingF(F) || F <- Funs],

    Env = #env{next_var=NextVarNum,
               rename_map=maps:new(),
               current_bindings=Bindings,
               current_module=Mod,
               modules=Modules},

    F = fun(F, {E, Memo}) ->
                {#env{next_var=NV2, rename_map=_M}, M2, F2} = rename_bindings(E, F),

                %% We invert the returned map so that it is from
                %% synthetic variable name to source code variable
                %% name for later lookup:
                Inverted = [{V, K}||{K, V} <- maps:to_list(M2)],
                M3 = maps:merge(M2, maps:from_list(Inverted)),
                {Env#env{next_var=NV2, rename_map=M3}, [F2|Memo]}
        end,
    {#env{next_var=NV2, rename_map=_}, Funs2} = lists:foldl(F, {Env, []}, Funs),
    %% Don't need NV from the tests
    {#env{next_var=_NV3, rename_map=_}, Tests2} = lists:foldl(F, {Env, []}, Tests),
    {NV2, Mod#alpaca_module{
            functions=lists:reverse(Funs2),
            tests=lists:reverse(Tests2)}}.

validate_user_types(#alpaca_module{types=Ts}=Mod) ->
    unique_type_names(Mod, Ts),
    unique_type_constructors(Mod, Ts).

%% check a list of things for duplicates with a comparison function and
%% a function for creating an error from one element.  The list must be sorted.
check_dupes([A,B|T], Compare) ->
    case Compare(A, B) of
        true -> {error, B};
        false -> check_dupes(T, Compare)
    end;
check_dupes([_], _) ->
    ok;
check_dupes([], _) ->
    ok.

unique_type_names(Mod, Types) ->
    Names = lists:sort([{N, L} || #alpaca_type{name={type_name, L, N}} <- Types]),
    case check_dupes(Names, fun({A, _}, {B, _}) -> A =:= B end) of
        ok -> ok;
        {error, {N, L}} -> parse_error(Mod, L, {duplicate_type, N})
    end.

unique_type_constructors(Mod, Types) ->
    %% Get the sorted names of only the constructors:
    F = fun (#alpaca_constructor{name=#type_constructor{name=N,line=L}}) ->
                {true, {N, L}};
            (_) -> false
        end,
    ToFlatten = [lists:filtermap(F, Ms) || #alpaca_type{members=Ms} <- Types],
    Cs = lists:sort(lists:flatten(ToFlatten)),
    case check_dupes(Cs, fun({A, _}, {B, _}) -> A =:= B end) of
        ok -> ok;
        {error, {N, L}} -> parse_error(Mod, L, {duplicate_constructor, N})
    end.

update_memo(#alpaca_module{name=no_module}=Mod, {module, Name, _}) ->
    Mod#alpaca_module{name=Name};
update_memo(#alpaca_module{name=Name}=Mod, {module, DupeName, L}) ->
    parse_error(Mod, L, {module_rename, Name, DupeName});
update_memo(#alpaca_module{type_imports=Imports}=M, #alpaca_type_import{}=I) ->
    M#alpaca_module{type_imports=Imports ++ [I]};
update_memo(#alpaca_module{type_exports=Exports}=M, #alpaca_type_export{}=I) ->
    #alpaca_type_export{names=Names} = I,
    M#alpaca_module{type_exports = Exports ++ Names};
update_memo(#alpaca_module{function_exports=Exports}=M, {export, Es}) ->
    M#alpaca_module{function_exports=Es ++ Exports};
update_memo(#alpaca_module{function_imports=Imports}=M, {import, Is}) ->
    M#alpaca_module{function_imports=Imports ++ Is};
update_memo(#alpaca_module{}=M, #alpaca_type_signature{}) ->
    M;
update_memo(#alpaca_module{functions=Funs}=M, #alpaca_binding{} = Def) ->
    M#alpaca_module{functions=[Def|Funs]};
update_memo(#alpaca_module{types=Ts}=M, #alpaca_type{}=T) ->
    M#alpaca_module{types=[T|Ts]};
update_memo(#alpaca_module{tests=Tests}=M, #alpaca_test{}=T) ->
    M#alpaca_module{tests=[T|Tests]};
update_memo(M, #alpaca_comment{}) ->
    M;
update_memo(M, Bad) ->
    %% We can' really report a meaningful line number here without either:
    %%  a) restructuring the parser rules to make this a syntax error.
    %%  b) Tagging all constructs generated the parser with a line number in
    %%     a consistent way.
    parse_error(M, 1, {invalid_top_level_construct, Bad}).

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
        TopLevel::alpaca_binding()) -> {#env{}, map(), alpaca_binding()}.
rename_bindings(Environment, #alpaca_binding{}=TopLevel) ->
    #alpaca_binding{bound_expr=Expr} = TopLevel,
    case Expr of
        #alpaca_fun{versions=Vs} ->
            F = fun(#alpaca_fun_version{
                       args=As,
                       body=Body,
                       guards=Gs}=FV, {Env, Map, Versions}) ->
                        {Env2, M2, Args} = make_bindings(Env, Map, As),
                        {Env3, M3, E} =  rename_bindings(Env2, M2, Body),
                        {Env4, _M4, Gs2} = rename_binding_list(Env3, M3, Gs),
                        FV2 = FV#alpaca_fun_version{
                                args=Args,
                                guards=Gs2,
                                body=E},
                        %% As with patterns and clauses we deliberately
                        %% throw away the rename map M4 here so that the
                        %% same symbols can be reused by distinctly
                        %% different function definitions.
                        {Env4, Map, [FV2|Versions]}
                end,

            {Env, M2, Vs2} = lists:foldl(F, {Environment, maps:new(), []}, Vs),
            {Env, M2, TopLevel#alpaca_binding{bound_expr=Expr#alpaca_fun{versions=Vs2}}};
        _ ->
            {Env, _, E} =  rename_bindings(Environment, maps:new(), Expr),
            {Env, maps:new(), TopLevel#alpaca_binding{bound_expr=E}}
    end;
rename_bindings(Env, #alpaca_test{expression=Expr}=Test) ->
    {Env2, Map, Expr2} = rename_bindings(Env, maps:new(), Expr),
    {Env2, Map, Test#alpaca_test{expression=Expr2}}.

rebind_args(#env{current_module=Mod}=Env, Map, Args) ->
    F = fun({'Symbol', _}=S, {#env{next_var=NV}=E, AccMap, Syms}) ->
                N = alpaca_ast:symbol_name(S),
                L = alpaca_ast:line(S),
                case maps:get(N, AccMap, undefined) of
                    undefined ->
                        Synth = next_var(NV),
                        { E#env{next_var=NV+1}
                        , maps:put(N, Synth, AccMap)
                        , [alpaca_ast:symbol(L, Synth)|Syms]
                        };
                    _ ->
                        parse_error(Mod, L, {duplicate_definition, N})
                end;
           ({unit, _}=U, {E, AccMap, Syms}) ->
                {E, AccMap, [U|Syms]};
           (Arg, {E, AccMap, Syms}) ->
                {E, AccMap, [Arg|Syms]}
        end,
    {Env2, M, Args2} = lists:foldl(F, {Env, Map, []}, Args),
    {Env2, M, lists:reverse(Args2)}.

rename_bindings(#env{current_module=Mod}=StartEnv, M,
                #alpaca_binding{name=NameSym}=Binding) ->
    Name = alpaca_ast:symbol_name(NameSym),
    L = alpaca_ast:line(NameSym),

    #alpaca_binding{bound_expr=Expr, body=Body} = Binding,
    {NewName, En2, M2} = case maps:get(Name, M, undefined) of
                              undefined ->
                                 #env{next_var=NV} = StartEnv,
                                 Synth = next_var(NV),
                                 E2 = StartEnv#env{next_var=NV+1},
                                 {Synth, E2, maps:put(Name, Synth, M)};
                             _ ->
                                 parse_error(Mod, L, {duplicate_definition, Name})
                         end,

    case Expr of
        #alpaca_fun{versions=_Vs}=Def ->
            {Env3, Map2, Vs2} = rewrite_fun_versions(En2, M2, Def),
            {Env4, Map3, Body2} = rename_bindings(Env3, Map2, Body),

            NewDef = Binding#alpaca_binding{
                       name=alpaca_ast:symbol_rename(NameSym, NewName),
                       bound_expr=Def#alpaca_fun{
                                    versions=Vs2},
                       body=Body2},
            {Env4, Map3, NewDef};
        _ ->
            {Env3, Map2, Expr2} = rename_bindings(En2, M2, Expr),
            {Env4, Map3, Body2} = rename_bindings(Env3, Map2, Body),
            {Env4, Map3, Binding#alpaca_binding{
                           name=alpaca_ast:symbol_rename(NameSym, NewName),
                           bound_expr=Expr2,
                           body=Body2}}
    end;

rename_bindings(Env, Map, #alpaca_fun{}=F) ->
    {Env2, Map2, Vs2} = rewrite_fun_versions(Env, Map, F),
    {Env2, Map2, F#alpaca_fun{versions=Vs2}};

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
                      NameAndArity = lists:map(fun name_and_arity/1, Fs),
                      [{{X, A}, local} || {X, A} <- NameAndArity]
              end,
    ImpFuns = fun () ->
                      Mod = Env#env.current_module,
                      #alpaca_module{function_imports=Imps} = Mod,
                      [{{X, A}, Mod1} || {X, {Mod1, A}} <- Imps]
              end,

    FName = case N of
                {'Symbol', _} = S ->
                    FN = alpaca_ast:symbol_name(S),
                    case rename_bindings(Env, Map, S) of
                        %% Not renamed so either calling a top level function
                        %% in the current module or it's a refernce to something
                        %% that might be imported:
                        {_, _, N} ->
                            FN = alpaca_ast:symbol_name(N),
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
    {Env2, M2, Args2} = rename_binding_list(Env, Map, Args),
    {Env2, M2, App#alpaca_apply{expr=Name, args=Args2}};

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
    {Env2, M, Arg2} = rename_bindings(Env, Map, Arg),
    {Env2, M, A#alpaca_type_apply{arg=Arg2}};

rename_bindings(Env, Map, #alpaca_type_check{expr=E}=TC) ->
    {Env2, M, E2} = rename_bindings(Env, Map, E),
    {Env2, M, TC#alpaca_type_check{expr=E2}};

rename_bindings(Env, Map, #alpaca_cons{head=H, tail=T}=Cons) ->
    {Env2, M, H2} = rename_bindings(Env, Map, H),
    {Env3, M2, T2} = rename_bindings(Env2, M, T),
    {Env3, M2, Cons#alpaca_cons{head=H2, tail=T2}};

rename_bindings(Env, Map, #alpaca_binary{segments=Segs}=B) ->
    F = fun(#alpaca_bits{value=V}=Bits, {E, M, Acc}) ->
                {E2, M2, V2} = rename_bindings(E, M, V),
                {E2, M2, [Bits#alpaca_bits{value=V2}|Acc]}
        end,
    {Env2, M2, Segs2} = lists:foldl(F, {Env, Map, []}, Segs),
    {Env2, M2, B#alpaca_binary{segments=lists:reverse(Segs2)}};

rename_bindings(Env, Map, #alpaca_map{pairs=Pairs}=ASTMap) ->
    Folder = fun(P, {E, M, Ps}) ->
                     {E2, M2, P2} = rename_bindings(E, M, P),
                     {E2, M2, [P2|Ps]}
             end,
    {Env2, M, Pairs2} = lists:foldl(Folder, {Env, Map, []}, Pairs),
    {Env2, M, ASTMap#alpaca_map{pairs=lists:reverse(Pairs2)}};

rename_bindings(Env, Map, #alpaca_map_add{to_add=A, existing=B}=ASTMap) ->
    {Env2, M, A2} = rename_bindings(Env, Map, A),
    {Env3, M2, B2} = rename_bindings(Env2, M, B),
    {Env3, M2, ASTMap#alpaca_map_add{to_add=A2, existing=B2}};

rename_bindings(Env, Map, #alpaca_map_pair{key=K, val=V}=P) ->
    {Env2, M, K2} = rename_bindings(Env, Map, K),
    {Env3, M2, V2} = rename_bindings(Env2, M, V),
    {Env3, M2, P#alpaca_map_pair{key=K2, val=V2}};

rename_bindings(Env, Map, #alpaca_tuple{values=Vs}=T) ->
    {Env2, _, Vals2} = rename_binding_list(Env, Map, Vs),
    {Env2, Map, T#alpaca_tuple{values=Vals2}};

rename_bindings(Env, Map, #alpaca_record{members=Members}=R) ->
    F = fun(#alpaca_record_member{val=V}=RM, {NewMembers, E, M}) ->
                {E2, M2, V2} = rename_bindings(E, M, V),
                {[RM#alpaca_record_member{val=V2}|NewMembers], E2, M2}
        end,
    {NewMembers, Env2, Map2} = lists:foldl(F, {[], Env, Map}, Members),
    {Env2, Map2, R#alpaca_record{members=lists:reverse(NewMembers)}};

rename_bindings(Env, Map, #alpaca_record_transform{}=Update) ->
    #alpaca_record_transform{additions=As, existing=E, line=L} = Update,
    FakeRec = #alpaca_record{members=As, line=L},
    {Env2, Map2, #alpaca_record{members=Renamed}} = rename_bindings(Env, Map, FakeRec),
    {Env3, Map3, E2} = rename_bindings(Env2, Map2, E),
    {Env3, Map3, #alpaca_record_transform{additions=Renamed, existing=E2, line=L}};

rename_bindings(Env, Map, {'Symbol', _}=S) ->
    N = alpaca_ast:symbol_name(S),
    L = alpaca_ast:line(S),
    case maps:get(N, Map, undefined) of
        undefined ->
            %% if there's a top-level binding we use that, otherwise
            %% try to resolve the symbol from imports:
            Mod = Env#env.current_module,
            Funs = Mod#alpaca_module.functions,
            case [FN || #alpaca_binding{name=FN} <- Funs, FN =:= N] of
                [_|_] -> {Env, Map, S};
                [] ->
                    Imports = Mod#alpaca_module.function_imports,
                    case [{M, A} || {FN, {M, A}} <- Imports, FN =:= N] of
                        [{Module, Arity}|_] ->
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
        Synthetic -> {Env, Map, alpaca_ast:symbol_rename(S, Synthetic)}
    end;
rename_bindings(#env{current_module=CurrentMod}=Env, Map,
                #alpaca_far_ref{module=M, name=N, arity=none, line=L}=FR) ->
    %% Find the first exported occurrence of M:N
    Modules = [Mod || #alpaca_module{name=MN}=Mod <- Env#env.modules, M =:= MN],
    case Modules of
        [Mod] ->
            As = [A || {F, A} <- Mod#alpaca_module.function_exports, F =:= N],
            case As of
                [A|_] -> {Env, Map, FR#alpaca_far_ref{arity=A}};
                _     -> parse_error(CurrentMod, L,
                                     {function_not_exported, M, N})
            end;
        _ ->
            parse_error(CurrentMod, L, {no_module, M})
    end;

rename_bindings(Env, M, #alpaca_ffi{args=Args, clauses=Cs}=FFI) ->
    {Env2, M2, Args2} = rename_bindings(Env, M, Args),
    {Env3, M3, Cs2} = rename_clause_list(Env2, M2, Cs),
    {Env3, M3, FFI#alpaca_ffi{args=Args2, clauses=Cs2}};

rename_bindings(Env, M, #alpaca_match{}=Match) ->
    #alpaca_match{match_expr=ME, clauses=Cs} = Match,
    {Env2, M2, ME2} = rename_bindings(Env, M, ME),
    {Env3, M3, Cs2} = rename_clause_list(Env2, M2, Cs),
    {Env3, M3, Match#alpaca_match{match_expr=ME2, clauses=Cs2}};

rename_bindings(Env, M, #alpaca_receive{clauses=Cs}=Recv) ->
    {Env2, M2, Cs2} = rename_clause_list(Env, M, Cs),
    {Env2, M2, Recv#alpaca_receive{clauses=Cs2}};

rename_bindings(Env, M, #alpaca_clause{pattern=P, guards=Gs, result=R}=Clause) ->
    %% pattern matches create new bindings and as such we don't
    %% just want to use existing substitutions but rather error
    %% on duplicates and create entirely new ones:
    {Env2, M2, P2} = make_bindings(Env, M, P),
    {Env3, M3, R2} = rename_bindings(Env2, M2, R),
    {Env4, _M4, Gs2} = rename_binding_list(Env3, M3, Gs),
    %% we actually throw away the modified map here
    %% because other patterns should be able to
    %% reuse variable names:
    {Env4, M, Clause#alpaca_clause{
               pattern=P2,
               guards=Gs2,
               result=R2}};

rename_bindings(Env, Map, {raise_error, Line, Kind, Expr}) ->
    {Env2, Map2, Expr2} = rename_bindings(Env, Map, Expr),
    {Env2, Map2, {raise_error, Line, Kind, Expr2}};
rename_bindings(Env, Map, Expr) ->
    {Env, Map, Expr}.

rename_binding_list(Env, Map, Bindings) ->
    F = fun(A, {E, M, Memo}) ->
                {E2, M2, A2} = rename_bindings(E, M, A),
                {E2, M2, [A2|Memo]}
        end,
    {Env2, M, Bindings2} = lists:foldl(F, {Env, Map, []}, Bindings),
    {Env2, M, lists:reverse(Bindings2)}.

%% For renaming bindings in a list of clauses.  Broken out from pattern
%% matching because it will be reused for FFI and receive.
rename_clause_list(Env, M, Cs) ->
    F = fun(C, {E, Map, Memo}) ->
                {E2, Map2, C2} = rename_bindings(E, Map, C),
                {E2, Map2, [C2|Memo]}
        end,
    {Env2, M2, Cs2} = lists:foldl(F, {Env, M, []}, Cs),
    {Env2, M2, lists:reverse(Cs2)}.

%% Renaming/rewriting functions used to occur only within explicit bindings but
%% we need to do it for lambdas (anonymous functions) as well so it's pulled out
%% here now:
rewrite_fun_versions(E, M, #alpaca_fun{versions=Vs}) ->
    F = fun(#alpaca_fun_version{}=FV, {Env, Map, NewVersions}) ->
                #alpaca_fun_version{args=Args, body=FunBody, guards=Gs} = FV,
                {Env2, M3, Args2} = rebind_args(Env, Map, Args),
                {Env3, M4, FunBody2} = rename_bindings(Env2, M3, FunBody),
                {Env4, _M5, Gs2} = rename_binding_list(Env3, M4, Gs),
                FV2 = FV#alpaca_fun_version{
                        args=Args2,
                        guards=Gs2,
                        body=FunBody2},
                %% As with patterns and clauses we deliberately
                %% throw away the rename map here so that the
                %% same symbols can be reused by distinctly
                %% different function definitions.
                {Env4, Map, [FV2|NewVersions]}
        end,
    {E2, M2, Vs2} = lists:foldl(F, {E, M, []}, Vs),
    {E2, M2, lists:reverse(Vs2)}.

%%% Used for pattern matches so that we're sure that the patterns in each
%%% clause contain unique bindings.
make_bindings(Env, M, [_|_]=Xs) ->
    {Env2, M2, Xs2} = lists:foldl(
                        fun(X, {E, Map, Memo}) ->
                                {E2, M2, A2} = make_bindings(E, Map, X),
                                {E2, M2, [A2|Memo]}
                        end,
                        {Env, M, []},
                        Xs),
    {Env2, M2, lists:reverse(Xs2)};

make_bindings(Env, M, #alpaca_tuple{values=Vs}=Tup) ->
    F = fun(V, {E, Map, Memo}) ->
                {E2, M2, V2} = make_bindings(E, Map, V),
                {E2, M2, [V2|Memo]}
        end,
    {Env2, M2, Vs2} = lists:foldl(F, {Env, M, []}, Vs),
    {Env2, M2, Tup#alpaca_tuple{values=lists:reverse(Vs2)}};

make_bindings(Env, M, #alpaca_cons{head=H, tail=T}=Cons) ->
    {Env2, M2, H2} = make_bindings(Env, M, H),
    {Env3, M3, T2} = make_bindings(Env2, M2, T),
    {Env3, M3, Cons#alpaca_cons{head=H2, tail=T2}};
%%
%% TODO:  this is identical to rename_bindings but for the internal call
%% to make_bindings vs rename_bindings.  How much else in here is like this?
%% Probably loads of abstracting/de-duping potential.
make_bindings(Env, Map, #alpaca_binary{segments=Segs}=B) ->
    F = fun(#alpaca_bits{value=V}=Bits, {E, M, Acc}) ->
                {E2, M2, V2} = make_bindings(E, M, V),
                {E2, M2, [Bits#alpaca_bits{value=V2}|Acc]}
        end,
    {Env2, M2, Segs2} = lists:foldl(F, {Env, Map, []}, Segs),
    {Env2, M2, B#alpaca_binary{segments=lists:reverse(Segs2)}};

%%% Map patterns need to rename variables used for keys and create new bindings
%%% for variables used for values.  We want to rename for keys because we want
%%% the following to work:
%%%
%%%     get my_key my_map = match my_map with
%%%       #{my_key => v} -> v
%%%
%%% Map patterns require the key to be something exact already.
make_bindings(Env, BindingMap, #alpaca_map{pairs=Ps}=Map) ->
    Folder = fun(P, {E, M, Acc}) ->
                     {E2, M2, P2} = make_bindings(E, M, P),
                     {E2, M2, [P2|Acc]}
             end,
    {Env2, M, Pairs} = lists:foldl(Folder, {Env, BindingMap, []}, Ps),
    Map2 = Map#alpaca_map{is_pattern=true, pairs=lists:reverse(Pairs)},
    {Env2, M, Map2};

make_bindings(Env, M, #alpaca_map_pair{key=K, val=V}=P) ->
    {Env2, M2, K2} = rename_bindings(Env, M, K),
    {Env3, M3, V2} = make_bindings(Env2, M2, V),
    {Env3, M3, P#alpaca_map_pair{is_pattern=true, key=K2, val=V2}};

%% Records can be compiled as maps so we need the is_pattern parameter
%% on their AST nodes set correctly here too.
make_bindings(Env, M, #alpaca_record{members=Members}=R) ->
    F = fun(#alpaca_record_member{val=V}=RM, {NewVs, E, Map}) ->
                {E2, Map2, V2} = make_bindings(E, Map, V),
                NewR = RM#alpaca_record_member{val=V2},
                {[NewR|NewVs], E2, Map2}
        end,
    {Members2, Env2, M2} = lists:foldl(F, {[], Env, M}, Members),
    NewR = R#alpaca_record{
             members=lists:reverse(Members2),
             is_pattern=true},
    {Env2, M2, NewR};

make_bindings(Env, M, #alpaca_type_apply{arg=none}=TA) ->
    {Env, M, TA};

make_bindings(Env, M, #alpaca_type_apply{arg=Arg}=TA) ->
    {Env2, M2, Arg2} = make_bindings(Env, M, Arg),
    {Env2, M2, TA#alpaca_type_apply{arg=Arg2}};

make_bindings(#env{current_module=Mod}=Env, M, {'Symbol', _}=S) ->
    Name = alpaca_ast:symbol_name(S),
    L = alpaca_ast:line(S),
    case maps:get(Name, M, undefined) of
        undefined ->
            #env{next_var=NV} = Env,
            Synth = next_var(NV),
            Env2 = Env#env{next_var=NV+1},
            {Env2, maps:put(Name, Synth, M), alpaca_ast:symbol_rename(S, Synth)};
        _ ->
            parse_error(Mod, L, {duplicate_definition, Name})
    end;
make_bindings(Env, M, Expression) ->
    {Env, M, Expression}.

-define(base_var_name, "svar_").
next_var(X) ->
    unicode:characters_to_binary(?base_var_name ++ integer_to_list(X), utf8).

list_dependencies(Src) ->
    {ok, Tokens, _} = alpaca_scanner:scan(Src),
    scan_tokens_for_deps(Tokens).

scan_tokens_for_deps(Tokens) ->
    {Mod, Deps} = scan_tokens_for_deps(Tokens, maps:new(), unknown_module),
    {Mod, maps:keys(Deps)}.

scan_tokens_for_deps([], Deps, Mod) ->
    {Mod, Deps};
scan_tokens_for_deps(Tokens, Deps, Mod) ->
    case next_batch(Tokens, []) of
        {[], Rem} -> scan_tokens_for_deps(Rem, Deps, Mod);
        {NextBatch, Rem} ->
            %% If we can't parse the tokens, ignore the error
            case parse(NextBatch) of
                {ok, {module, Name, _}} ->
                    scan_tokens_for_deps(Rem, Deps, Name);
                {ok, Parsed} ->
                    scan_tokens_for_deps(Rem, find_deps(Parsed, Deps), Mod);
                {error, _} ->
                    scan_tokens_for_deps(Rem, Deps, Mod)
            end
    end.

apply_signatures([], Mod) ->
    {ok, Mod};
apply_signatures(Tokens, Mod) ->
    case next_batch(Tokens, []) of
        {[], Rem} -> apply_signatures(Rem, Mod);
        {NextBatch, Rem} ->
            case parse(NextBatch) of
                {ok, #alpaca_type_signature{} = S} ->
                    Mod2 = attach_signature(S, Mod),
                    apply_signatures(Rem, Mod2);
                _ -> apply_signatures(Rem, Mod)
        end
    end.

attach_signature(Sig, #alpaca_module{functions=Funs}=M) ->
    case attach_signature(Sig, Funs, []) of
        {ok, NewFuns} -> M#alpaca_module{functions=NewFuns};
        {error, {L, E}} -> parse_error(M, L, E)
    end.
attach_signature(#alpaca_type_signature{line=L, name=N}, [], _Acc) ->
    {error, {L, {signature_missing_def, N}}};
attach_signature(Sig, [Fun|Rem], Acc) ->
    #alpaca_type_signature{name=SN, type=ST, line=L} = Sig,
    #alpaca_binding{name=FN, signature=ET} = Fun,
    Attach = fun () ->
        %% Only attach signature if not already present
        case ET of
            undefined -> 
                FunWithSig = Fun#alpaca_binding{signature=Sig},
                {ok, lists:reverse([FunWithSig | Acc] ++ Rem)};

            _ ->
                {error, {L, {duplicate_signature, SN}}}
        end
    end,

    case {FN, SN} of
        {{_, #{name := N}}, N} ->
            %% Multi-arity means for t_arrow we need to match
            %% on the length of args
            case ST of
                {t_arrow, Args} ->
                    case Fun of
                        #alpaca_binding{bound_expr=#alpaca_fun{arity=Arity}}
                        when length(Args) =:= Arity ->
                            Attach();
                        _ -> 
                            attach_signature(Sig, Rem, [Fun | Acc])
                    end;
                _ ->
                    Attach()
                end;

        _ -> attach_signature(Sig, Rem, [Fun | Acc])
    end.  

find_deps({import, Is}, Deps) ->
    lists:foldl(
        fun({_, {Mod, _}}, Acc) ->
                maps:put(Mod, Mod, Acc);
           ({_, Mod}, Acc) ->
                maps:put(Mod, Mod, Acc)
        end, Deps, Is);
find_deps(#alpaca_binding{bound_expr=Expr}, Deps) ->
    find_deps(Expr, Deps);
find_deps(#alpaca_type_import{module=Mod}, Deps) ->
    maps:put(Mod, Mod, Deps);
find_deps(#alpaca_fun{versions=Versions}, Deps) ->
    lists:foldl(fun find_deps/2, Deps, Versions);
find_deps(#alpaca_fun_version{body=Body}, Deps) ->
    find_deps(Body, Deps);
find_deps(#alpaca_apply{args=Args, expr=Expr}, Deps) ->
    Deps_ = lists:foldl(fun find_deps/2, Deps, Args),
    case Expr of
        {Mod, _, _} when is_atom(Mod) -> maps:put(Mod, Mod, Deps_);
        _ -> Deps_
    end;
find_deps(#alpaca_match{match_expr=Expr, clauses=Clauses}, Deps) ->
    lists:foldl(fun find_deps/2, find_deps(Expr, Deps), Clauses);
find_deps(#alpaca_clause{result=Result}, Deps) ->
    find_deps(Result, Deps);
find_deps(#alpaca_tuple{values=Values}, Deps) ->
    lists:foldl(fun find_deps/2, Deps, Values);
find_deps(#alpaca_cons{head=Head, tail=Tail}, Deps) ->
    find_deps(Tail, find_deps(Head, Deps));
find_deps(#alpaca_record{members=Members}, Deps) ->
    lists:foldl(fun find_deps/2, Deps, Members);
find_deps(#alpaca_record_member{val=Expr}, Deps) ->
    find_deps(Expr, Deps);
find_deps(#alpaca_map{pairs=Pairs}, Deps) ->
    lists:foldl(fun find_deps/2, Deps, Pairs);
find_deps(#alpaca_map_pair{key=Key, val=Val}, Deps) ->
    find_deps(Key, find_deps(Val, Deps));
find_deps(#alpaca_record_transform{additions=Adds}, Deps) ->
    lists:foldl(fun find_deps/2, Deps, Adds);
find_deps(#alpaca_map_add{to_add=Pair}, Deps) ->
    find_deps(Pair, Deps);
find_deps(#alpaca_receive{clauses=Clauses}, Deps) ->
    lists:foldl(fun find_deps/2, Deps, Clauses);
find_deps(#alpaca_send{message=Msg, pid=Pid}, Deps) ->
    find_deps(Pid, find_deps(Msg, Deps));
find_deps(#alpaca_test{expression=Expr}, Deps) ->
    find_deps(Expr, Deps);
find_deps(#alpaca_spawn{args=Args}, Deps) ->
    lists:foldl(fun find_deps/2, Deps, Args);
find_deps(#alpaca_ffi{args=Args, clauses=Clauses}, Deps) ->
    lists:foldl(fun find_deps/2, find_deps(Args, Deps), Clauses);
find_deps(_, Deps) -> Deps.


-ifdef(TEST).

test_parse(S) ->
    parse(alpaca_scanner:scan(S)).

symbols_test_() ->
    [?_assertMatch({ok, {'Symbol', #{line := 1, name := <<"oneSymbol">>}}},
                   parse(alpaca_scanner:scan("oneSymbol")))
    ].

user_types_test_() ->
    [?_assertMatch({ok, #alpaca_type{name={type_name, 1, <<"t">>},
                                   vars=[],
                                   members=[t_int,
                                            #alpaca_constructor{
                                               name=#type_constructor{line=1, name="A"},
                                               arg=t_int}]}},
                   test_parse("type t = int | A int")),
     ?_assertMatch(
        {ok, #alpaca_type{
                name={type_name, 1, <<"my_list">>},
                vars=[{type_var, 1, "x"}],
                members=[#alpaca_constructor{
                            name=#type_constructor{line=1, name="Nil"},
                            arg=none},
                         #alpaca_constructor{
                            name=#type_constructor{line=1, name="Cons"},
                            arg=#alpaca_type_tuple{
                                   members=[{type_var, 1, "x"},
                                            #alpaca_type{
                                               name={type_name, 1, <<"my_list">>},
                                               vars=[{type_var, 1, "x"}]}]}
                           }]}},
        test_parse("type my_list 'x = Nil | Cons ('x, my_list 'x)")),
     ?_assertEqual({error, {parse_error, ?FILE, 5,
                            {duplicate_type, <<"t">>}}},
                   test_make_modules(["module dupe_types_1\n\n"
                                "type t = A | B\n\n"
                                "type t = C | int"])),
     ?_assertEqual({error, {parse_error, ?FILE, 5,
                            {duplicate_constructor, "A"}}},
                   test_make_modules(["module dupe_type_constructor\n\n"
                                 "type t = A int | B\n\n"
                                 "type u = X float | A\n\n"])),
     %% Making sure multiple type variables work here:
     ?_assertMatch({ok, #alpaca_type{
                           name={type_name, 1, <<"either">>},
                           vars=[{type_var, 1, "a"}, {type_var, 1, "b"}],
                           members=[#alpaca_constructor{
                                       name=#type_constructor{line=1, name="Left"},
                                       arg={type_var, 1, "a"}
                                      },
                                    #alpaca_constructor{
                                       name=#type_constructor{line=1, name="Right"},
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
         #alpaca_binding{
            name={'Symbol', #{line := 1, name := <<"x">>}},
            bound_expr={'Int', #{line := 1, value := 5}}}},
        parse(alpaca_scanner:scan("let x=5"))),
     ?_assertMatch(
        {ok, {error, non_literal_value, {'Symbol',
                                         #{line := 1, name := <<"x">>}},
              {alpaca_apply,undefined,1,
               {'Symbol', #{line := 1, name := <<"sideEffectingFun">>}},
               [{'Int', #{line := 1, value := 5}}]}}},
        parse(alpaca_scanner:scan("let x=sideEffectingFun 5"))),
     ?_assertMatch(
        {ok, {error, non_literal_value, {'Symbol',
                                         #{line := 1, name := <<"x">>}},
              {alpaca_record,2,1,false,
               [{alpaca_record_member,1,one,undefined,
                 {'Int', #{line := 1, value := 10}}},
                {alpaca_record_member,1,two,undefined,
                 {alpaca_apply,undefined,1,
                  {'Symbol', #{line := 1, name := <<"sideEffectingFun">>}},
                  [{'Int', #{line := 1, value := 5}}]}}]}}},
        parse(alpaca_scanner:scan("let x={one = 10, two = (sideEffectingFun 5)}"))),
     ?_assertMatch(
        {ok, {error, non_literal_value, {'Symbol',
                                         #{line := 1, name := <<"x">>}},
              {alpaca_cons,undefined,0,
               {'Int', #{line := 1, value := 1}},
               {alpaca_cons,undefined,0,
                {alpaca_apply,undefined,1,
                 {'Symbol', #{line := 1, name := <<"sideEffectingFun">>}},
                 [{'Int', #{line := 1, value := 5}}]},
                {nil, 0}}}}},
        parse(alpaca_scanner:scan("let x=[1, (sideEffectingFun 5)]"))),

     ?_assertMatch(
        {ok, {error, non_literal_value, {'Symbol',
                                         #{line := 1, name := <<"x">>}},
              {alpaca_apply,undefined,1,
               {'Symbol', #{line := 1, name := <<"sideEffectingFun">>}},
               [{'Int', #{line := 1, value := 5}}]}}},
        parse(alpaca_scanner:scan("let x=sideEffectingFun 5"))),
     ?_assertMatch(
        {ok, {error, non_literal_value, {'Symbol',
                                         #{line := 1, name := <<"x">>}},
              {alpaca_record,2,1,false,
               [{alpaca_record_member,1,one,undefined,
                 {'Int', #{line := 1, value := 10}}},
                {alpaca_record_member,1,two,undefined,
                 {alpaca_apply,undefined,1,
                  {'Symbol', #{line := 1, name := <<"sideEffectingFun">>}},
                  [{'Int', #{line := 1, value := 5}}]}}]}}},
        parse(alpaca_scanner:scan("let x={one = 10, two = (sideEffectingFun 5)}"))),
     ?_assertMatch(
        {ok, {error, non_literal_value, {'Symbol',
                                         #{line := 1, name := <<"x">>}},
                     {alpaca_cons,undefined,0,
                             {'Int', #{line := 1, value := 1}},
                             {alpaca_cons,undefined,0,
                                 {alpaca_apply,undefined,1,
                                  {'Symbol',
                                   #{line := 1,
                                     name := <<"sideEffectingFun">>}},
                                  [{'Int', #{line := 1, value := 5}}]},
                              {nil,0}}}}},
        parse(alpaca_scanner:scan("let x=[1, (sideEffectingFun 5)]"))),
     ?_assertMatch(
        {ok, {error, non_literal_value, {'Symbol',
                                         #{line := 1, name := <<"x">>}},
                         {alpaca_record,2,1,false,
                             [{alpaca_record_member,1,one,undefined,
                               {'Int', #{line := 1, value := 10}}},
                              {alpaca_record_member,1,two,undefined,
                               {alpaca_apply,undefined,1,
                                {'Symbol',
                                 #{line := 1,
                                   name := <<"sideEffectingFun">>}},
                                [{'Int', #{line := 1, value := 5}}]}}]}}},
        parse(alpaca_scanner:scan("let x={one = 10, two = (sideEffectingFun 5)}"))),
     ?_assertMatch(
        {ok, {error, non_literal_value, {'Symbol',
                                         #{line := 1, name := <<"x">>}},
                     {alpaca_cons,undefined,0,
                             {'Int', #{line := 1, value := 1}},
                             {alpaca_cons,undefined,0,
                                 {alpaca_apply,undefined,1,
                                     {'Symbol',
                                      #{line := 1,
                                        name := <<"sideEffectingFun">>}},
                                     [{'Int', #{line := 1, value := 5}}]},
                                 {nil,0}}}}},
        parse(alpaca_scanner:scan("let x=[1, (sideEffectingFun 5)]"))),
     ?_assertMatch(
        {ok,
         #alpaca_binding{
            name={'Symbol', #{line := 1, name := <<"double">>}},
            bound_expr=#alpaca_fun{
                          versions=[#alpaca_fun_version{
                                       args=[{'Symbol',
                                              #{line := 1,
                                                name := <<"x">>}}],
                                       body=#alpaca_apply{
                                               type=undefined,
                                               expr={bif, '+', 1, erlang, '+'},
                                               args=[{'Symbol',
                                                      #{line := 1,
                                                        name := <<"x">>}},
                                                     {'Symbol',
                                                      #{line := 1,
                                                        name := <<"x">>}}]}}]}}},
        parse(alpaca_scanner:scan("let double x = x + x"))),
     ?_assertMatch(
        {ok,
         #alpaca_binding{
            name={'Symbol', #{line := 1, name := <<"add">>}},
            bound_expr=#alpaca_fun{
                          versions=[#alpaca_fun_version{
                                       args=[{'Symbol',
                                              #{line := 1,
                                                name := <<"x">>}},
                                             {'Symbol',
                                              #{line := 1,
                                                name := <<"y">>}}],
                                       body=#alpaca_apply{
                                               type=undefined,
                                               expr={bif, '+', 1, erlang, '+'},
                                               args=[{'Symbol',
                                                      #{line := 1,
                                                        name := <<"x">>}},
                                                     {'Symbol',
                                                      #{line := 1,
                                                        name := <<"y">>}}]}}]}}},
        parse(alpaca_scanner:scan("let add x y = x + y"))),
        ?_assertMatch(
            {ok,
             #alpaca_binding{
                name={'Symbol', #{line := 1, name := <<"(<*>)">>}},
                bound_expr=#alpaca_fun{
                              versions=[#alpaca_fun_version{
                                           args=[{'Symbol',
                                                  #{line := 1,
                                                    name := <<"x">>}},
                                                 {'Symbol',
                                                  #{line := 1,
                                                    name := <<"y">>}}],
                                           body=#alpaca_apply{
                                                   type=undefined,
                                                   expr={bif, '+', 1, erlang, '+'},
                                                   args=[{'Symbol',
                                                          #{line := 1,
                                                            name := <<"x">>}},
                                                         {'Symbol',
                                                          #{line := 1,
                                                            name := <<"y">>}}]}}]}}},
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
         #alpaca_binding{
            name={'Symbol', #{line := 1, name := <<"double">>}},
            bound_expr=#alpaca_fun{
                          versions=[#alpaca_fun_version{
                                       args=[{'Symbol',
                                              #{line := 1,
                                                name := <<"x">>}}],
                                       body=#alpaca_apply{
                                               type=undefined,
                                               expr={bif, '+', 1, erlang, '+'},
                                               args=[{'Symbol',
                                                      #{line := 1,
                                                        name := <<"x">>}},
                                                     {'Symbol',
                                                      #{line := 1,
                                                        name := <<"x">>}}]}}]},
            body=#alpaca_apply{
                    expr={'Symbol', #{line := 1, name := <<"double">>}},
                    args=[{'Int', #{line := 1, value := 2}}]}}},
        parse(alpaca_scanner:scan("let double x = x + x in double 2"))),
     ?_assertMatch({ok, #alpaca_binding{
                           name={'Symbol', #{line := 1, name := <<"x">>}},
                           bound_expr=#alpaca_apply{
                                         expr={'Symbol',
                                               #{line := 1,
                                                 name := <<"double">>}},
                                         args=[{'Int', #{line := 1, value := 2}}]},
                           body=#alpaca_apply{
                                   expr={'Symbol', #{line := 1,
                                                     name := <<"double">>}},
                                   args=[{'Symbol', #{line := 1,
                                                      name := <<"x">>}}]}}},
                   parse(alpaca_scanner:scan("let x = double 2 in double x"))),
     ?_assertMatch(
        {ok,
         #alpaca_binding{
            name={'Symbol', #{line := 1, name := <<"doubler">>}},
            bound_expr=
                #alpaca_fun{
                   versions=
                       [#alpaca_fun_version{
                           args=[{'Symbol', #{line := 1, name := <<"x">>}}],
                           body=
                               #alpaca_binding{
                                  name={'Symbol', #{line := 2,
                                                    name := <<"double">>}},
                                  bound_expr=
                                      #alpaca_fun{
                                         versions=
                                             [#alpaca_fun_version{
                                                 args=[{'Symbol',
                                                        #{line := 2,
                                                          name := <<"x">>}}],
                                                 body=#alpaca_apply{
                                                         type=undefined,
                                                         expr={bif, '+', 2, erlang, '+'},
                                                         args=[{'Symbol',
                                                                #{line := 2,
                                                                  name := <<"x">>}},
                                                               {'Symbol',
                                                                #{line := 2,
                                                                  name := <<"x">>}}]}}]},
                                  body=#alpaca_apply{
                                          expr={'Symbol',
                                                #{line := 3,
                                                  name := <<"double">>}},
                                          args=[{'Int', #{line := 3, value := 2}}]}}}]}}},
        parse(alpaca_scanner:scan(
                "let doubler x =\n"
                "  let double x = x + x in\n"
                "  double 2"))),
     ?_assertMatch(
        {ok,
         #alpaca_binding{
            name={'Symbol', #{line := 1, name := <<"my_fun">>}},
            bound_expr=
                #alpaca_fun{
                   versions=
                       [#alpaca_fun_version{
                           args=[{'Symbol', #{line := 1,
                                              name := <<"x">>}},
                                 {'Symbol', #{line := 1,
                                              name := <<"y">>}}],
                           body=#alpaca_binding{
                                   name={'Symbol', #{line := 1,
                                                     name := <<"xer">>}},
                                   bound_expr=
                                       #alpaca_fun{
                                          versions=
                                              [#alpaca_fun_version{
                                                  args=[{'Symbol',
                                                         #{line := 1,
                                                           name := <<"a">>}}],
                                                  body=#alpaca_apply{
                                                          type=undefined,
                                                          expr={bif, '+', 1, erlang, '+'},
                                                          args=[{'Symbol',
                                                                 #{line := 1,
                                                                   name := <<"a">>}},
                                                                {'Symbol',
                                                                 #{line := 1,
                                                                   name := <<"a">>}}]}}]},
                                   body=#alpaca_binding{
                                           name={'Symbol',
                                                 #{line := 1,
                                                   name := <<"yer">>}},
                                           bound_expr=
                                               #alpaca_fun{
                                                  versions=
                                                      [#alpaca_fun_version{
                                                          args=[{'Symbol',
                                                                 #{line := 1,
                                                                   name := <<"b">>}}],
                                                          body=#alpaca_apply{
                                                                  type=undefined,
                                                                  expr={bif, '+', 1, erlang, '+'},
                                                                  args=[{'Symbol',
                                                                         #{line := 1,
                                                                           name := <<"b">>}},
                                                                        {'Symbol',
                                                                         #{line := 1,
                                                                           name := <<"b">>}}]}}]},
                                           body=#alpaca_apply{
                                                   type=undefined,
                                                   expr={bif, '+', 1, erlang, '+'},
                                                   args=[#alpaca_apply{
                                                            expr={'Symbol',
                                                                  #{line := 1,
                                                                    name := <<"xer">>}},
                                                            args=[{'Symbol',
                                                                   #{line := 1,
                                                                     name := <<"x">>}}]},
                                                         #alpaca_apply{
                                                            expr={'Symbol',
                                                                  #{line := 1,
                                                                    name := <<"yer">>}},
                                                            args=[{'Symbol',
                                                                   #{line := 1,
                                                                     name := <<"y">>}}]}]}}}}]}}},
        parse(alpaca_scanner:scan(
                "let my_fun x y ="
                "  let xer a = a + a in"
                "  let yer b = b + b in"
                "  (xer x) + (yer y)")))
    ].

application_test_() ->
    [?_assertMatch({ok, #alpaca_apply{expr={'Symbol', #{line := 1,
                                                        name := <<"double">>}},
                                    args=[{'Int', #{line := 1, value := 2}}]}},
                   parse(alpaca_scanner:scan("double 2"))),
     ?_assertMatch({ok, #alpaca_apply{expr={'Symbol', #{line := 1,
                                                        name := <<"two">>}},
                                      args=[{'Symbol',
                                             #{line := 1,
                                               name := <<"symbols">>}}]}},
                   parse(alpaca_scanner:scan("two symbols"))),
     ?_assertMatch({ok, #alpaca_apply{expr={'Symbol', #{line := 1,
                                                        name := <<"x">>}},
                                    args=[{'Symbol', #{line := 1,
                                                       name := <<"y">>}},
                                          {'Symbol', #{line := 1,
                                                       name := <<"z">>}}]}},
                   parse(alpaca_scanner:scan("x y z"))),
     ?_assertMatch({ok, #alpaca_apply{
                           expr={'mod',
                                 {'Symbol', #{line := 1,
                                              name := <<"fun">>}},
                                 2},
                           args=[{'Int', #{line := 1, value := 1}},
                                 {'Symbol', #{line := 1,
                                              name := <<"x">>}}]}},
                   parse(alpaca_scanner:scan("mod.fun 1 x")))
    ].

module_def_test_() ->
    [?_assertMatch({ok, {module, 'test_mod', 1}},
                   parse(alpaca_scanner:scan("module test_mod"))),
     ?_assertMatch({ok, {module, 'myMod', 1}},
                   parse(alpaca_scanner:scan("module myMod"))),
     ?_assertThrow({parse_error, ?FILE, 2, {module_rename, mod1, mod2}},
                   parse_module({?FILE, "module mod1\nmodule mod2"}))
    ].

export_test_() ->
    [?_assertMatch({ok, {export, [{<<"add">>, 2}]}},
                   parse(alpaca_scanner:scan("export add/2")))
    ].

import_test_() ->
    [?_assertMatch({ok, {import, [{<<"foo">>, some_mod},
                                  {<<"bar">>, {some_mod, 2}}]}},
                   parse(alpaca_scanner:scan("import some_mod.[foo, bar/2]"))),
     ?_assertMatch(
        {ok, {import, [{<<"foo">>, mod1},
                       {<<"bar">>, {mod2, 1}},
                       {<<"baz">>, mod2}]}},
        parse(alpaca_scanner:scan("import mod1.foo, mod2.[bar/1, baz]"))),
     fun() ->
             Code1 =
                 "module two_lines_of_imports\n\n"
                 "import foo.bar/2\n\n"
                 "import math.[add/2, sub/2, mult]",

             ?assertMatch(
                #alpaca_module{
                    function_imports=[{<<"bar">>, {foo, 2}},
                                      {<<"add">>, {math, 2}},
                                      {<<"sub">>, {math, 2}},
                                      {<<"mult">>, math}]},
                parse_module({?FILE, Code1}))
     end
    ].

expr_test_() ->
    [?_assertMatch({ok, {'Int', #{line := 1, value := 2}}},
                   parse(alpaca_scanner:scan("2"))),
     ?_assertMatch({ok, #alpaca_apply{type=undefined,
                                      expr={bif, '+', 1, erlang, '+'},
                                      args=[{'Int', #{line := 1, value := 1}},
                                            {'Int', #{line := 1, value := 5}}]}},
                   parse(alpaca_scanner:scan("1 + 5"))),
     ?_assertMatch({ok,
                    #alpaca_apply{
                       expr={'Symbol', #{line := 1, name := <<"add">>}},
                       args=[{'Symbol', #{line := 1, name := <<"x">>}},
                             {'Int', #{line := 1, value := 2}}]}},
                   parse(alpaca_scanner:scan("add x 2"))),
     ?_assertMatch({ok,
                    #alpaca_apply{expr={'Symbol', #{line := 1,
                                                    name := <<"double">>}},
                                  args=[{'Symbol', #{line := 1,
                                                     name := <<"x">>}}]}},
                   parse(alpaca_scanner:scan("(double x)"))),
     ?_assertMatch({ok, #alpaca_apply{
                           expr={'Symbol', #{line := 1,
                                             name := <<"tuple_func">>}},
                           args=[#alpaca_tuple{
                                    arity=2,
                                    values=[{'Symbol', #{line := 1,
                                                         name := <<"x">>}},
                                            {'Int', #{line := 1, value := 1}}]},
                                 {'Symbol', #{line := 1, name := <<"y">>}}]}},
                   parse(alpaca_scanner:scan("tuple_func (x, 1) y")))
    ].

module_with_let_test() ->
    Code =
        "module test_mod\n\n"
        "export add/2\n\n"
        "let add x y =\n"
        "  let adder a b = a + b in\n"
        "  adder x y",
    ?assertMatch({ok,
       [#alpaca_module{
           name='test_mod',
           function_exports=[{<<"add">>,2}],
           functions=
               [#alpaca_binding{
                   name={'Symbol', #{line := 5, name := <<"add">>}},
                   bound_expr=
                       #alpaca_fun{
                          versions=
                              [#alpaca_fun_version{
                                  args=[{'Symbol', #{line := 5,
                                                     name := <<"svar_0">>}},
                                        {'Symbol', #{line := 5,
                                                     name := <<"svar_1">>}}],
                                  body=#alpaca_binding{
                                          name={'Symbol', #{line := 6,
                                                            name := <<"svar_2">>}},
                                          bound_expr=
                                              #alpaca_fun{
                                                 versions=
                                                     [#alpaca_fun_version{
                                                         args=[{'Symbol',
                                                                #{line := 6,
                                                                  name := <<"svar_3">>}},
                                                               {'Symbol',
                                                                #{line := 6,
                                                                  name := <<"svar_4">>}}],
                                                         body=#alpaca_apply{
                                                                 type=undefined,
                                                                 expr={bif, '+', 6, erlang, '+'},
                                                                 args=[{'Symbol',
                                                                        #{line := 6,
                                                                          name := <<"svar_3">>}},
                                                                       {'Symbol',
                                                                        #{line := 6,
                                                                          name := <<"svar_4">>}}]}}]},
                                          body=#alpaca_apply{
                                                  expr={'Symbol',
                                                        #{line := 7,
                                                          name := <<"svar_2">>}},
                                                  args=[{'Symbol',
                                                         #{line := 7,
                                                           name := <<"svar_0">>}},
                                                        {'Symbol',
                                                         #{line := 7,
                                                           name := <<"svar_1">>}}]}}}]}}]}]},
                 test_make_modules([Code])).

match_test_() ->
    [?_assertMatch(
        {ok, #alpaca_match{
                match_expr={'Symbol', #{line := 1, name := <<"x">>}},
                clauses=[#alpaca_clause{
                            pattern={'Int', #{line := 2, value := 0}},
                            result={'Symbol', #{line := 2,
                                                name := <<"zero">>}}},
                         #alpaca_clause{
                            pattern={'_', 3},
                            result={'Symbol', #{line := 3,
                                                name := <<"non_zero">>}}}]}},
        parse(alpaca_scanner:scan(
                "match x with\n"
                " 0 -> zero\n"
                "| _ -> non_zero\n"))),
     ?_assertMatch(
        {ok, #alpaca_match{match_expr=#alpaca_apply{
                                         expr={'Symbol', #{line := 1,
                                                           name := <<"add">>}},
                                         args=[{'Symbol',
                                                #{line := 1,
                                                  name := <<"x">>}},
                                               {'Symbol',
                                                #{line := 1,
                                                  name := <<"y">>}}]},
                           clauses=[#alpaca_clause{
                                       pattern={'Int', #{line := 2, value := 0}},
                                       result={atom, 2, "zero"}},
                                    #alpaca_clause{
                                       pattern={'Int', #{line := 3, value := 1}},
                                       result={atom, 3, "one"}},
                                    #alpaca_clause{
                                       pattern={'_', 4},
                                       result={atom, 4, "more_than_one"}}
                                   ]}},
        parse(alpaca_scanner:scan(
                "match add x y with\n"
                " 0 -> :zero\n"
                "| 1 -> :one\n"
                "| _ -> :more_than_one\n"))),
     ?_assertMatch(
        {ok, #alpaca_match{
                match_expr={'Symbol', #{line := 1, name := <<"x">>}},
                clauses=[#alpaca_clause{
                            pattern=#alpaca_tuple{
                                       arity=2,
                                       values=[{'_', 2},
                                               {'Symbol',
                                                #{line := 2,
                                                  name := <<"x">>}}]},
                            result={atom, 2, "anything_first"}},
                         #alpaca_clause{
                            pattern=#alpaca_tuple{
                                       arity=2,
                                       values=[{'Int', #{line := 3, value := 1}},
                                               {'Symbol', #{line := 3,
                                                            name := <<"x">>}}]},
                            result={atom, 3, "one_first"}}]}},
        parse(alpaca_scanner:scan(
                "match x with\n"
                "  (_, x) -> :anything_first\n"
                "| (1, x) -> :one_first\n"))),
     ?_assertMatch(
        {ok, #alpaca_match{
                match_expr=#alpaca_tuple{
                              arity=2,
                              values=[{'Symbol', #{line := 1, name := <<"x">>}},
                                      {'Symbol', #{line := 1, name := <<"y">>}}]},
                clauses=[#alpaca_clause{
                            pattern=#alpaca_tuple{
                                       arity=2,
                                       values=[#alpaca_tuple{
                                                  arity=2,
                                                  values=[{'_', 2},
                                                          {'Int',
                                                           #{line := 2,
                                                             value := 1}}]},
                                               {'Symbol', #{line := 2,
                                                            name := <<"a">>}}]},
                            result={atom, 2, "nested_tuple"}}]}},
        parse(alpaca_scanner:scan(
                "match (x, y) with\n"
                " ((_, 1), a) -> :nested_tuple")))
    ].

tuple_test_() ->
    %% first no unary tuples:
    [?_assertMatch({ok, {'Int', #{line := 1, value := 1}}},
                   parse(alpaca_scanner:scan("(1)"))),
     ?_assertMatch({ok, #alpaca_tuple{arity=2,
                                    values=[{'Int', #{line := 1, value := 1}},
                                            {'Int', #{line := 1, value := 2}}]}},
                   parse(alpaca_scanner:scan("(1, 2)"))),
     ?_assertMatch({ok, #alpaca_tuple{
                           arity=2,
                           values=[{'Symbol', #{line := 1, name := <<"x">>}},
                                   {'Int', #{line := 1, value := 1}}]}},
                   parse(alpaca_scanner:scan("(x, 1)"))),
     ?_assertMatch({ok,
                    #alpaca_tuple{
                       arity=2,
                       values=[#alpaca_tuple{
                                  arity=2,
                                  values=[{'Int',
                                           #{line := 1,
                                             value := 1}},
                                          {'Symbol',
                                           #{line := 1,
                                             name := <<"x">>}}]},
                               {'Int', #{line := 1, value := 12}}]}},
                   parse(alpaca_scanner:scan("((1, x), 12)")))
    ].

list_test_() ->
    [?_assertMatch({ok,
                    #alpaca_cons{head={'Int', #{line := 1, value := 1}},
                                 tail=#alpaca_cons{
                                         head={'Int', #{line := 1, value := 2}},
                                         tail=#alpaca_cons{
                                                 head={'Int', #{line := 1, value := 3}},
                                                 tail={nil, 0}}}}},
                   test_parse("[1, 2, 3]")),
     ?_assertMatch({ok, {nil, 1}}, parse(alpaca_scanner:scan("[]"))),
     ?_assertMatch({ok, #alpaca_cons{
                           head={'Int', #{line := 1, value := 1}},
                           tail={nil, 1}}},
                   parse(alpaca_scanner:scan("[1]"))),
     ?_assertMatch({ok, #alpaca_cons{
                           head={'Symbol', #{line := 1, name := <<"x">>}},
                           tail=#alpaca_cons{head={'Int', #{line := 1, value := 1}},
                                             tail={nil, 1}}}},
                   parse(alpaca_scanner:scan("x :: [1]"))),
     ?_assertMatch({ok, #alpaca_cons{head={'Int', #{line := 1, value := 1}},
                                     tail={'Symbol', #{line := 1,
                                                       name := <<"y">>}}}},
                   parse(alpaca_scanner:scan("1 :: y"))),
     ?_assertMatch(
        {ok, #alpaca_match{
                match_expr={'Symbol', #{line := 1, name := <<"x">>}},
                clauses=[#alpaca_clause{pattern={nil,2},
                                        result={nil,2}},
                         #alpaca_clause{
                            pattern=#alpaca_cons{
                                       head={'Symbol', #{line := 3,
                                                         name := <<"h">>}},
                                       tail={'Symbol', #{line := 3,
                                                         name := <<"t">>}}},
                            result={'Symbol', #{line := 3, name := <<"h">>}}}]}},
        parse(alpaca_scanner:scan(
                "match x with\n"
                "  [] -> []\n"
                "| h :: t -> h\n")))
    ].

binary_test_() ->
    [?_assertMatch({ok,
                    #alpaca_binary{
                       line=1,
                       segments=[#alpaca_bits{
                                    line=1,
                                    value={'Int', #{line := 1, value := 1}}}]}},
                   parse(alpaca_scanner:scan("<<1>>"))),
     ?_assertMatch(
        {ok, #alpaca_binary{
                line=1,
                segments=[#alpaca_bits{value={'Int', #{line := 1, value := 1}},
                                       size=8,
                                       unit=1},
                          #alpaca_bits{value={'Int', #{line := 1, value := 2}},
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
                segments=[#alpaca_bits{
                             value={'Symbol', #{line := 1, name := <<"a">>}}},
                          #alpaca_bits{
                             value={'Symbol', #{line := 1, name := <<"b">>}}}]}},
        parse(alpaca_scanner:scan("<<a: size=8 type=int, b: size=8 type=int>>"))),
     ?_assertMatch(
        {error, {1, alpaca_parser, unsized_binary_before_end}},
        parse(alpaca_scanner:scan("match <<1>> with <<a: type=binary, b: type=utf8>> -> (a, b)")))
    ].

string_test_() ->
    [ ?_assertMatch(
         {ok, {string, 1, "Hello world"}}, test_parse("\"Hello world\""))
    %% , ?_assertMatch({ok, {string, 1, "Nested \" quotes"}}),
    %% , test_parse("\"Nested " "\"" " quotes\"")
    ].

ffi_test_() ->
    [?_assertMatch({ok,
                    #alpaca_ffi{
                       module={atom, 1, "io"},
                       function_name={atom, 1, "format"},
                       args=#alpaca_cons{
                               head={string, 1, "One is ~s~n"},
                               tail=#alpaca_cons{
                                       head=#alpaca_cons{
                                               head={'Int', #{line := 1, value := 1}},
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
    ?assertMatch({ok,
       [#alpaca_module{
           name='test_mod',
           function_exports=[{<<"add">>, 2},{<<"sub">>, 2}],
           functions=
               [#alpaca_binding{
                   name={'Symbol', #{line := 5, name := <<"adder">>}},
                   bound_expr=
                       #alpaca_fun{
                          versions=
                              [#alpaca_fun_version{
                                  args=[{'Symbol',
                                         #{line := 5,
                                           name := <<"svar_0">>}},
                                        {'Symbol',
                                         #{line := 5,
                                           name := <<"svar_1">>}}],
                                  body=#alpaca_apply{type=undefined,
                                                     expr={bif, '+', 5, erlang, '+'},
                                                     args=[{'Symbol',
                                                            #{line := 5,
                                                              name := <<"svar_0">>}},
                                                           {'Symbol',
                                                            #{line := 5,
                                                              name := <<"svar_1">>}}]}}]}},
                #alpaca_binding{
                   name={'Symbol', #{line := 7, name := <<"add1">>}},
                   bound_expr=
                       #alpaca_fun{
                          versions=
                              [#alpaca_fun_version{
                                  args=[{'Symbol', #{line := 7,
                                                     name := <<"svar_2">>}}],
                                  body=#alpaca_apply{
                                          expr={'Symbol',
                                                #{line := 7,
                                                  name := <<"adder">>}},
                                          args=[{'Symbol',
                                                 #{line := 7,
                                                   name := <<"svar_2">>}},
                                                {'Int',
                                                 #{line := 7, value := 1}}]}}]}},
                #alpaca_binding{
                   name={'Symbol', #{line := 9, name := <<"add">>}},
                   bound_expr=
                       #alpaca_fun{
                          versions=
                              [#alpaca_fun_version{
                                  args=[{'Symbol', #{line := 9,
                                                     name := <<"svar_3">>}},
                                        {'Symbol', #{line := 9,
                                                     name := <<"svar_4">>}}],
                                  body=#alpaca_apply{expr={'Symbol',
                                                           #{line := 9,
                                                             name := <<"adder">>}},
                                                     args=[{'Symbol',
                                                            #{line := 9,
                                                              name := <<"svar_3">>}},
                                                           {'Symbol',
                                                            #{line := 9,
                                                              name := <<"svar_4">>}}]}}]}},
                #alpaca_binding{
                   name={'Symbol', #{line := 11, name := <<"sub">>}},
                   bound_expr=
                       #alpaca_fun{
                          versions=
                              [#alpaca_fun_version{
                                  args=[{'Symbol', #{line := 11,
                                                     name := <<"svar_5">>}},
                                        {'Symbol', #{line := 11,
                                                     name := <<"svar_6">>}}],
                                  body=#alpaca_apply{type=undefined,
                                                     expr={bif, '-', 11, erlang, '-'},
                                                     args=[{'Symbol',
                                                            #{line := 11,
                                                              name := <<"svar_5">>}},
                                                           {'Symbol',
                                                            #{line := 11,
                                                              name := <<"svar_6">>}}]}}]}}]}]},
       test_make_modules([Code])).

break_test() ->
    % We should tolerate whitespace between the two break tokens
    Code = "module test_mod\n\n
            let a = 5\n   \n"
           "let b = 6\n\n",
     ?assertMatch({ok,
       [#alpaca_module{
           name='test_mod',
           function_exports=[],
           functions=[#alpaca_binding{
                         name={'Symbol', #{line := 4, name := <<"a">>}},
                         bound_expr={'Int', #{line := 4, value := 5}}},
                      #alpaca_binding{
                         name={'Symbol', #{line := 6, name := <<"b">>}},
                         bound_expr={'Int', #{line := 6, value := 6}}}]}]},
       test_make_modules([Code])).


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

    [?_assertMatch(
        {_, _,
         #alpaca_binding{
            name={'Symbol', #{line := 1, name := <<"f">>}},
            bound_expr=#alpaca_fun{
                          versions=
                              [#alpaca_fun_version{
                                  args=[{'Symbol',
                                         #{line := 1,
                                           name := <<"svar_0">>,
                                           original := {'Some', <<"x">>}}}],
                                  body=#alpaca_binding{
                                          name={'Symbol',
                                                #{line := 1,
                                                  name := <<"svar_1">>,
                                                  original := {'Some', <<"y">>}}},
                                          bound_expr={'Int',
                                                      #{line := 1, value := 2}},
                                          body=#alpaca_apply{
                                                  expr={bif, '+', 1, 'erlang', '+'},
                                                  args=[{'Symbol',
                                                         #{line := 1,
                                                           name := <<"svar_0">>,
                                                           original := {'Some',
                                                                        <<"x">>}}},
                                                        {'Symbol',
                                                         #{line := 1,
                                                           name := <<"svar_1">>,
                                                           original := {'Some',
                                                                        <<"y">>}}}]}}}]}}},
        rename_bindings(#env{}, A)),
     ?_assertThrow({parse_error, undefined, 2, {duplicate_definition, <<"x">>}},
                   rename_bindings(#env{}, B)),
     ?_assertMatch(
        {_, _,
         #alpaca_binding{
            name={'Symbol', #{line := 1, name := <<"f">>}},
            bound_expr=
                #alpaca_fun{
                   versions=
                       [#alpaca_fun_version{
                           args=[{'Symbol',
                                  #{line := 1, name := <<"svar_0">>}}],
                           body=#alpaca_match{
                                   match_expr={'Symbol',
                                               #{line := 1,
                                                 name := <<"svar_0">>}},
                                   clauses=
                                       [#alpaca_clause{
                                           pattern=#alpaca_tuple{
                                                      values=
                                                          [{'Symbol',
                                                            #{line := 2,
                                                              name := <<"svar_1">>}},
                                                           {'Int',
                                                            #{line := 2,
                                                              value := 0}}]},
                                           result={'Symbol',
                                                   #{line := 2,
                                                     name := <<"svar_1">>}}},
                                        #alpaca_clause{
                                           pattern=#alpaca_tuple{
                                                      values=
                                                          [{'Symbol',
                                                            #{line := 3,
                                                              name := <<"svar_2">>}},
                                                           {'Symbol',
                                                            #{line := 3,
                                                              name := <<"svar_3">>}}]},
                                           result={'Symbol',
                                                   #{line := 3,
                                                     name := <<"svar_3">>}}}]}}]}}},
        rename_bindings(#env{}, C)),
     ?_assertThrow({parse_error, undefined, 2, {duplicate_definition, <<"x">>}},
                   rename_bindings(#env{}, D)),
     ?_assertMatch(
        {_, _,
         #alpaca_binding{
            bound_expr=
                #alpaca_fun{
                   versions=
                       [#alpaca_fun_version{
                           body=
                               #alpaca_match{
                                  match_expr={'Symbol', #{line := 1,
                                                          name := <<"svar_0">>}},
                                  clauses=
                                      [#alpaca_clause{
                                          pattern=
                                              #alpaca_cons{
                                                 head={'_', 2},
                                                 tail=#alpaca_cons{
                                                         head={'Symbol',
                                                               #{line := 2,
                                                                 name := <<"svar_1">>}},
                                                         tail=#alpaca_cons{
                                                                 head={'Int',
                                                                       #{line := 2,
                                                                         value := 0}},
                                                                 tail={nil, 0}}}},
                                          result={'Symbol', #{line := 2,
                                                              name := <<"svar_1">>}}},
                                       #alpaca_clause{
                                          pattern=#alpaca_cons{
                                                     head={'Symbol',
                                                           #{line := 3,
                                                             name := <<"svar_2">>}},
                                                     tail={'Symbol',
                                                           #{line := 3,
                                                             name := <<"svar_3">>}}},
                                          result={'Symbol',
                                                  #{line := 3,
                                                    name := <<"svar_2">>}}}]}}]}}},
        rename_bindings(#env{}, E)),
     ?_assertThrow({parse_error, undefined, 2, {duplicate_definition, <<"y">>}},
                   rename_bindings(#env{}, F))
    ].

type_expr_in_type_declaration_test() ->
    ?assertMatch({error, _}, test_parse("type a not_a_var = A not_a_var")).


ambiguous_type_expressions_test() ->
    ?assertMatch({ok, #alpaca_type{
                         name={type_name,1,<<"my_map">>},
                         vars=[],
                         members=[{t_map,
                                   #alpaca_type{
                                      name={type_name,1,<<"foo">>},
                                      vars=[],
                                      members=[]},
                                   t_atom}]}},
                 test_parse("type my_map = map foo atom")),
    ?assertMatch({error, _}, test_parse("type my_map = map foo bar atom")),
    ?assertMatch({error, _}, test_parse("type my_list = list foo atom")),
    ?assertMatch({error, _}, test_parse("type my_pid = pid foo atom")),
    ?assertMatch({ok, #alpaca_type{
                         name={type_name,1,<<"my_type">>},
                         vars=[],
                         members=[#alpaca_type{
                                     name={type_name,1,<<"foo">>},
                                     vars=[{_, #alpaca_type{
                                                  name={type_name, _, <<"bar">>}}},
                                           {_, #alpaca_type{
                                                  name={type_name, _, <<"baz">>}}}],
                                     members=[#alpaca_type{
                                                 name={type_name, 1, <<"bar">>},
                                                 vars=[],
                                                 members=[]},
                                              #alpaca_type{
                                                 name={type_name, 1, <<"baz">>},
                                                 vars=[],
                                                 members=[]}]}]}},
                 test_parse("type my_type = foo bar baz")),
    ?assertMatch({ok, #alpaca_type{
                         name={type_name, 1, <<"my_type">>},
                         vars=[],
                         members=[#alpaca_type{
                                     name={type_name, 1, <<"foo">>},
                                     vars=[{_,
                                            #alpaca_type{
                                               name={type_name, _, <<"bar">>},
                                               vars=[{_,
                                                      #alpaca_type{
                                                        name={_, _, <<"baz">>}}}]}}],
                                     members=
                                         [#alpaca_type{
                                             name={type_name, 1, <<"bar">>},
                                             vars=[_],
                                             members=
                                                 [#alpaca_type{
                                                     name={type_name, 1, <<"baz">>},
                                                     vars=[],
                                                     members=[]}]}]}]}},
                 test_parse("type my_type = foo (bar baz)")).



expand_exports_test_() ->
    [fun() ->
             Def = fun(Name, Arity) ->
                           #alpaca_binding{
                              name=alpaca_ast:symbol(0, list_to_binary(Name)),
                              bound_expr=#alpaca_fun{arity=Arity}}
                   end,

             Ms = [#alpaca_module{
                      function_exports=[<<"foo">>, {<<"bar">>, 1}],
                      functions=[Def("foo", 1), Def("foo", 2), Def("bar", 1)]}],
             [#alpaca_module{function_exports=FEs}] = expand_exports(Ms, []),
             ?assertEqual([{<<"foo">>, 1}, {<<"foo">>, 2}, {<<"bar">>, 1}], FEs)
     end
    , fun() ->
              Code =
                  "module test_export_all_funs\n\n"
                  "export foo, bar/1\n\n"
                  "let foo x = x\n\n"
                  "let foo x y = x + y\n\n"
                  "let bar x = x",

              {ok, [Mod]} = test_make_modules([Code]),
              [#alpaca_module{function_exports=FEs}] = expand_exports([Mod], []),
              ?assertEqual([{<<"foo">>, 1}, {<<"foo">>, 2}, {<<"bar">>, 1}],
                           FEs)
      end
    ].

expand_imports_test_() ->
    [fun() ->
             Code1 =
                 "module m1\n\n"
                 "export foo\n\n"
                 "let foo x = x\n\n"
                 "let foo x y = x + y",

             Code2 =
                 "module m2\n\n"
                 "import m1.foo",

             {ok, [Mod1, Mod2]} = test_make_modules([Code1, Code2]),
             WithExports = expand_exports([Mod1, Mod2]),

             [M1, M2] = expand_imports(WithExports),

             ?assertMatch(
                #alpaca_module{
                   function_exports=[_, _],
                   function_imports=[]},
                M1),
             ?assertMatch(
                #alpaca_module{
                   function_imports=[{<<"foo">>, {m1, 1}},
                                     {<<"foo">>, {m1, 2}}]},
                M2)
     end
    , fun() ->
              Code =
                  "module m\n\n"
                  "import n.foo",

              Mod = parse_module({?FILE, Code}),
              ?assertThrow({parse_error, ?FILE, 1, {no_module, n}},
                           expand_imports(expand_exports([Mod])))
      end
    ].

import_rewriting_test_() ->
    [fun() ->
             Code1 =
                 "module a\n\n"
                 "export add/2\n\n"
                 "let add x y = x + y",
             Code2 =
                 "module b\n\n"
                 "import a.add\n\n"
                 "let f () = add 2 3",
             ?assertMatch(
                {ok,
                 [#alpaca_module{name=a},
                  #alpaca_module{
                     name=b,
                     functions=
                         [#alpaca_binding{
                             bound_expr=#alpaca_fun{
                                           versions=
                                               [#alpaca_fun_version{
                                                   body=#alpaca_apply{
                                                           expr=#alpaca_far_ref{
                                                                   module=a,
                                                                   name= <<"add">>,
                                                                   arity=2}
                                                          }}]
                                          }}]}]},
                test_make_modules([Code1, Code2]))
     end
    , fun() ->
              Code1 =
                 "module a\n\n"
                  "export (|>)\n\n"
                  "let (|>) x y = y x",
              Code2 =
                  "module b\n\n"
                  "import a.(|>)\n\n"
                  "let add_ten x = x + 10\n\n"
                  "let f () = 2 |> add_ten",
              ?assertMatch(
                 {ok,
                  [#alpaca_module{name=a},
                   #alpaca_module{
                      name=b,
                      functions=
                          [_,
                           #alpaca_binding{
                              bound_expr=#alpaca_fun{
                                            versions=
                                                [#alpaca_fun_version{
                                                    body=#alpaca_apply{
                                                            expr=#alpaca_far_ref{
                                                                    module=a,
                                                                    name= <<"(|>)">>,
                                                                    arity=2}
                                                           }}]
                                           }}]}]},
                 test_make_modules([Code1, Code2]))
      end
    , fun() ->
              Code1 =
                  "module b\n\n"
                  "let foo () = let y = bar.baz in y",
              ?assertEqual({error, {parse_error, ?FILE, 3, {no_module, bar}}},
                           test_make_modules([Code1]))
    end
    , fun() ->
              Code1 = "module a",
              Code2 =
                  "module b\n\n"
                  "let foo () = let y = a.bar in y",
              ?assertEqual({error, {parse_error, ?FILE, 3,
                                    {function_not_exported, a, <<"bar">>}}},
                           test_make_modules([Code1, Code2]))
    end
    ].

invalid_map_type_parameters_test() ->
    Code1 = "module a\n\n"
            "type x = map",
    Code2 = "module a\n\n"
            "type x = map int",
    Code3 = "module a\n\n"
            "type x = map int int int",
    ?assertMatch({error,{parse_error, ?FILE, 3, {wrong_type_arity,t_map, 0}}},
                 test_make_modules([Code1])),
    ?assertMatch({error,{parse_error, ?FILE, 3, {wrong_type_arity, t_map, 1}}},
                 test_make_modules([Code2])),
    ?assertMatch({error,{parse_error, ?FILE, 3, {wrong_type_arity, t_map, 3}}},
                 test_make_modules([Code3])).

invalid_list_type_parameters_test() ->
    Code1 = "module a\n\n"
            "type x = list",
    Code2 = "module a\n\n"
            "type x = list int int",
    ?assertMatch({error,{parse_error, ?FILE, 3, {wrong_type_arity, t_list, 0}}},
                 test_make_modules([Code1])),
    ?assertMatch({error,{parse_error, ?FILE, 3, {wrong_type_arity, t_list, 2}}},
                 test_make_modules([Code2])).

invalid_pid_type_parameters_test() ->
    Code1 = "module a\n\n"
            "type x = pid",
    Code2 = "module a\n\n"
            "type x = pid int int",
    ?assertMatch({error,{parse_error, ?FILE, 3, {wrong_type_arity,t_pid, 0}}},
                 test_make_modules([Code1])),
    ?assertMatch({error,{parse_error, ?FILE, 3, {wrong_type_arity, t_pid, 2}}},
                 test_make_modules([Code2])).

invalid_base_type_parameters_test_() ->
    Types = [ {"atom", t_atom},
              {"binary", t_binary},
              {"bool", t_bool},
              {"chars", t_chars},
              {"float", t_float},
              {"int", t_int},
              {"string", t_string}
            ],
    lists:map(fun({Token, Typ}) ->
      Code = "module a\n\n"
             "type concrete = Constructor\n"
             "type x = " ++ Token ++ " concrete",
      ?_assertMatch({error,{parse_error, ?FILE, 4, {wrong_type_arity,Typ, 1}}},
                   test_make_modules([Code]))
    end, Types).

invalid_fun_parameter_test_() ->
    P = fun(Code) -> parse(alpaca_scanner:scan(Code)) end,

    [?_assertMatch({error, {1, _, {invalid_fun_parameter, _}}},
                   P("fn (fn x -> x + 1) -> 2"))
     , ?_assertMatch({error, {1, _, {invalid_fun_parameter, _}}},
                     P("let f (fn x -> x + 1) = 2"))
     , ?_assertMatch({error, {1, _, {invalid_fun_parameter, _}}},
                     P("let f = fn (fn x -> x + 1) -> 2"))
    ].

infer_modules_test_() ->
    Src = "module a_mod\n\n"
          "import_type f.far_type\n\n"
          "import r.[arity/5, other/4]"
          "import b.other_fun\n\n"
          "let arg_far_fun () = c.far_fun (d.my_fun 2)\n\n"
          "let other () = match g.far_fun 10 with\n"
          "  | _ -> h.far_fun 10\n\n"
          "let colls () = ( [(i.far_fun 1), #{1 => (l.far_fun 1)}]\n"
          "               , (j.far_fun 1), { key = k.far_fun 1})\n"
          "let adds_x rec = {x=(m.far_fun 1) | rec}\n"
          "let add_far m = #{k => (n.far_fun 1) | m}\n"
          "let main () = let x = e.far_fun 5 in c.far_fun 10\n"
          "let ffi () = beam :erl :mod [(p.far_fun 1)] with _ -> q.far_fun 1\n"
          "test \"this\" = o.far_fun 1",

    ?_assertMatch(
       {a_mod, [b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r]},
       list_dependencies(Src)).

valid_signature_test() ->
    Src = "module sigs;;"
           "val add : fn int int -> int;;"
           "let add x y = x + y\n",
    {ok, [#alpaca_module{functions=Funs}]} = test_make_modules([Src]),
    ?assertMatch([#alpaca_binding{
                     signature=#alpaca_type_signature{
                                  name = <<"add">>,
                                  type = {t_arrow, [t_int, t_int], t_int}}}], 
                 Funs).

multi_arity_signature_test() ->
    Src = "module sigs\n"
          "val add : fn int -> int\n"
          "let add x = x + 1\n\n"
          "val add : fn int int -> int\n"
          "let add x y = x + y\n",
    {ok, [#alpaca_module{functions=Funs}]} = test_make_modules([Src]),
    ?assertMatch(
       [#alpaca_binding{
           signature=#alpaca_type_signature{
                        name = <<"add">>,
                        type = {t_arrow, [t_int], t_int}}},
        #alpaca_binding{
           signature=#alpaca_type_signature{
                        name = <<"add">>,
                        type = {t_arrow, [t_int, t_int], t_int}}}
       ],
       Funs).

mismatched_signature_test() ->
    Src = "module sigs\n"
          "val bad : fn int int -> int\n"
          "let add x y = x + y\n",
    ?assertMatch(
      {error, {parse_error, ?FILE, 2, {signature_missing_def, <<"bad">>}}},
      test_make_modules([Src])).

duplicate_signature_test() ->
    Src = "module sigs\n"
          "val num : int\n"
          "val num : int\n"
          "let num = 42\n",
    ?assertMatch(
       {error, {parse_error, ?FILE, 3, {duplicate_signature, <<"num">>}}},
       test_make_modules([Src])).

test_make_modules(Sources) ->
    NamedSources = lists:map(fun(C) -> {?FILE, C} end, Sources),
    make_modules(NamedSources).

-endif.
 
