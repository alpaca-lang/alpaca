%%% -*- mode: erlang;erlang-indent-level: 4;indent-tabs-mode: nil -*-
%%% ex: ft=erlang ts=4 sw=4 et
-module(alpaca_ast_gen).
-export([parse/1, make_modules/1, term_line/1]).

%% Parse is used by other modules (particularly alpaca_typer) to make ASTs
%% from code that does not necessarily include a module:
-ignore_xref([parse/1]).

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
                        {invalid_endianess, term()} |
                        {invalid_bin_qualifier, string()} |
                        {invalid_bin_type, string()} |
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
%% A single function make_modules/1 provides one entry point that can be used
%% to cover all three steps for a list of code strings.

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
    StartMod = #alpaca_module{filename=FileName},
    parse_module(Tokens, StartMod).

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

name_and_arity(#alpaca_binding{name={symbol, _, N}, bound_expr=E}) ->
    case E of
        #alpaca_fun{arity=A} -> {N, A};
        _                    -> {N, 0}
    end.

expand_exports([], Memo) ->
    Memo;
expand_exports([M|Tail], Memo) ->
    F = fun({_, _}=FunWithArity) -> 
                FunWithArity;
           (Name) when is_list(Name) ->
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
    F = fun(#alpaca_binding{name={symbol, _, N}, bound_expr=Expr}, Acc) ->
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
              %% we use the first occurence's line as the function's primary
              %% location:
              case A of
                  0 ->
                      [OnlyV] = NewVs,
                      #alpaca_binding{name={symbol, L, N}, bound_expr=OnlyV};
                  _ ->
                      #alpaca_binding{name={symbol, L, N}, 
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
    #alpaca_module{name=_MN, functions=Funs}=Mod,
    BindingF = fun(#alpaca_binding{name={_, _, N}, bound_expr=#alpaca_fun{arity=A}}) ->
                       {N, A};
                  (#alpaca_binding{name={_, _, N}}) ->
                       {N, 0}
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
    {#env{next_var=NV2, rename_map=_M}, Funs2} = lists:foldl(F, {Env, []}, Funs),
    %% TODO:  other parts of the compiler might care about the rename
    %%        map but we do throw away some details deliberately
    %%        when rewriting patterns and different function versions.
    %%        Probably worth expanding the symbol AST node to track
    %%        an original name.
    {NV2, Mod#alpaca_module{functions=lists:reverse(Funs2)}}.

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
    #alpaca_binding{name={symbol, _, _}, bound_expr=Expr} = TopLevel,
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
                        %% throw away the rename map here so that the
                        %% same symbols can be reused by distinctly
                        %% different function definitions.
                        {Env3, Map, [FV2|Versions]}
                end,
            
            {Env, M2, Vs2} = lists:foldl(F, {Environment, maps:new(), []}, Vs),
            {Env, M2, TopLevel#alpaca_binding{bound_expr=Expr#alpaca_fun{versions=Vs2}}};
        _ ->
            {Env, _, E} =  rename_bindings(Environment, maps:new(), Expr),
            {Env, maps:new(), TopLevel#alpaca_binding{bound_expr=E}}
    end.

rebind_args(#env{current_module=Mod}=Env, Map, Args) ->
    F = fun({symbol, L, N}, {#env{next_var=NV}=E, AccMap, Syms}) ->
                case maps:get(N, AccMap, undefined) of
                    undefined ->
                        Synth = next_var(NV),
                        { E#env{next_var=NV+1}
                        , maps:put(N, Synth, AccMap)
                        , [{symbol, L, Synth}|Syms]
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
                #alpaca_binding{name={symbol, L, Name}}=Binding) ->
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
    case Expr of
        #alpaca_fun{versions=Vs}=Def ->
            {Env3, Map2, Vs2} = lists:foldl(F, {En2, M2, []}, Vs),
            {Env4, Map3, Body2} = rename_bindings(Env3, Map2, Body),
            NewDef = Binding#alpaca_binding{
                       name={symbol, L, NewName},
                       bound_expr=Def#alpaca_fun{
                                    versions=lists:reverse(Vs2)},
                       body=Body2},
            {Env4, Map3, NewDef};
        _ ->
            {Env3, Map2, Expr2} = rename_bindings(En2, M2, Expr),
            {Env4, Map3, Body2} = rename_bindings(Env3, Map2, Body),
            {Env4, Map3, Binding#alpaca_binding{
                           name={symbol, L, NewName},
                           bound_expr=Expr2,
                           body=Body2}}
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
                      NameAndArity = lists:map(fun name_and_arity/1, Fs),
                      [{{X, A}, local} || {X, A} <- NameAndArity]
              end,
    ImpFuns = fun () ->
                      Mod = Env#env.current_module,
                      #alpaca_module{function_imports=Imps} = Mod,
                      [{{X, A}, Mod1} || {X, {Mod1, A}} <- Imps]
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
    #alpaca_record_transform{additions=As, existing=E} = Update,
    FakeRec = #alpaca_record{members=As},
    {Env2, Map2, #alpaca_record{members=Renamed}} = rename_bindings(Env, Map, FakeRec),
    {Env3, Map3, E2} = rename_bindings(Env2, Map2, E),
    {Env3, Map3, #alpaca_record_transform{additions=Renamed, existing=E2}};

rename_bindings(Env, Map, {symbol, L, N}=S) ->
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
        Synthetic -> {Env, Map, {symbol, L, Synthetic}}
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

make_bindings(#env{current_module=Mod}=Env, M, {symbol, L, Name}) ->
    case maps:get(Name, M, undefined) of
        undefined ->
            #env{next_var=NV} = Env,
            Synth = next_var(NV),
            Env2 = Env#env{next_var=NV+1},
            {Env2, maps:put(Name, Synth, M), {symbol, L, Synth}};
        _ ->
            parse_error(Mod, L, {duplicate_definition, Name})
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
                                               name=#type_constructor{line=1, name="A"},
                                               arg=t_int}]}},
                   test_parse("type t = int | A int")),
     ?_assertMatch(
        {ok, #alpaca_type{
                name={type_name, 1, "my_list"},
                vars=[{type_var, 1, "x"}],
                members=[#alpaca_constructor{
                            name=#type_constructor{line=1, name="Nil"},
                            arg=none},
                         #alpaca_constructor{
                            name=#type_constructor{line=1, name="Cons"},
                            arg=#alpaca_type_tuple{
                                   members=[{type_var, 1, "x"},
                                            #alpaca_type{
                                               name={type_name, 1, "my_list"},
                                               vars=[{type_var, 1, "x"}]}]}
                           }]}},
        test_parse("type my_list 'x = Nil | Cons ('x, my_list 'x)")),
     ?_assertEqual({error, {parse_error, ?FILE, 5,
                            {duplicate_type, "t"}}},
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
                           name={type_name, 1, "either"},
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
            name={symbol, 1, "x"},
            bound_expr={int, 1, 5}}},
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
         #alpaca_binding{
            name={symbol, 1, "double"},
            bound_expr=#alpaca_fun{
                          versions=[#alpaca_fun_version{
                                       args=[{symbol, 1, "x"}],
                                       body=#alpaca_apply{
                                               type=undefined,
                                               expr={bif, '+', 1, erlang, '+'},
                                               args=[{symbol, 1, "x"},
                                                     {symbol, 1, "x"}]}}]}}},
        parse(alpaca_scanner:scan("let double x = x + x"))),
     ?_assertMatch(
        {ok, 
         #alpaca_binding{
            name={symbol, 1, "add"},
            bound_expr=#alpaca_fun{
                          versions=[#alpaca_fun_version{
                                       args=[{symbol, 1, "x"}, 
                                             {symbol, 1, "y"}],
                                       body=#alpaca_apply{
                                               type=undefined,
                                               expr={bif, '+', 1, erlang, '+'},
                                               args=[{symbol, 1, "x"},
                                                     {symbol, 1, "y"}]}}]}}},
        parse(alpaca_scanner:scan("let add x y = x + y"))),
        ?_assertMatch(
            {ok, 
             #alpaca_binding{
                name={symbol, 1, "(<*>)"},
                bound_expr=#alpaca_fun{
                              versions=[#alpaca_fun_version{
                                           args=[{symbol, 1, "x"}, 
                                                 {symbol, 1, "y"}],
                                           body=#alpaca_apply{
                                                   type=undefined,
                                                   expr={bif, '+', 1, erlang, '+'},
                                                   args=[{symbol, 1, "x"},
                                                         {symbol, 1, "y"}]}}]}}},
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
            name={symbol, 1, "double"},
            bound_expr=#alpaca_fun{
                          versions=[#alpaca_fun_version{
                                       args=[{symbol, 1, "x"}],
                                       body=#alpaca_apply{
                                               type=undefined,
                                               expr={bif, '+', 1, erlang, '+'},
                                               args=[{symbol, 1, "x"},
                                                     {symbol, 1, "x"}]}}]},
            body=#alpaca_apply{
                    expr={symbol, 1, "double"},
                    args=[{int, 1, 2}]}}},
        parse(alpaca_scanner:scan("let double x = x + x in double 2"))),
     ?_assertMatch({ok, #alpaca_binding{
                           name={symbol, 1, "x"},
                           bound_expr=#alpaca_apply{
                                         expr={symbol, 1, "double"},
                                         args=[{int, 1, 2}]},
                           body=#alpaca_apply{
                                   expr={symbol, 1, "double"},
                                   args=[{symbol, 1, "x"}]}}},
                   parse(alpaca_scanner:scan("let x = double 2 in double x"))),
     ?_assertMatch(
        {ok, 
         #alpaca_binding{
            name={symbol, 1, "doubler"},
            bound_expr=
                #alpaca_fun{
                   versions=
                       [#alpaca_fun_version{
                           args=[{symbol, 1, "x"}],
                           body=
                               #alpaca_binding{
                                  name={symbol, 2, "double"},
                                  bound_expr=
                                      #alpaca_fun{
                                         versions=
                                             [#alpaca_fun_version{
                                                 args=[{symbol, 2, "x"}],
                                                 body=#alpaca_apply{
                                                         type=undefined,
                                                         expr={bif, '+', 2, erlang, '+'},
                                                         args=[{symbol, 2, "x"},
                                                               {symbol, 2, "x"}]}}]},
                                  body=#alpaca_apply{
                                          expr={symbol, 3, "double"},
                                          args=[{int, 3, 2}]}}}]}}},
        parse(alpaca_scanner:scan(
                "let doubler x =\n"
                "  let double x = x + x in\n"
                "  double 2"))),
     ?_assertMatch(
        {ok, 
         #alpaca_binding{
            name={symbol,1,"my_fun"},
            bound_expr=
                #alpaca_fun{
                   versions=
                       [#alpaca_fun_version{
                           args=[{symbol,1,"x"},{symbol,1,"y"}],
                           body=#alpaca_binding{
                                   name={symbol,1,"xer"},
                                   bound_expr=
                                       #alpaca_fun{
                                          versions=[#alpaca_fun_version{
                                                       args=[{symbol,1,"a"}],
                                                       body=#alpaca_apply{
                                                               type=undefined,
                                                               expr={bif, '+', 1, erlang, '+'},
                                                               args=[{symbol,1,"a"},
                                                                     {symbol,1,"a"}]}}]},
                                   body=#alpaca_binding{
                                           name={symbol,1,"yer"},
                                           bound_expr=
                                               #alpaca_fun{
                                                  versions=[#alpaca_fun_version{
                                                               args=[{symbol,1,"b"}],
                                                               body=#alpaca_apply{
                                                                       type=undefined,
                                                                       expr={bif, '+', 1, erlang, '+'},
                                                                       args=[{symbol,1,"b"},
                                                                             {symbol,1,"b"}]}}]},
                                           body=#alpaca_apply{
                                                   type=undefined,
                                                   expr={bif, '+', 1, erlang, '+'},
                                                   args=[#alpaca_apply{
                                                            expr={symbol,1,"xer"},
                                                            args=[{symbol,1,"x"}]},
                                                         #alpaca_apply{
                                                            expr={symbol,1,"yer"},
                                                            args=[{symbol,1,"y"}]}]}}}}]}}},
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
    [?_assertMatch({ok, {module, 'test_mod', 1}},
                   parse(alpaca_scanner:scan("module test_mod"))),
     ?_assertMatch({ok, {module, 'myMod', 1}},
                   parse(alpaca_scanner:scan("module myMod"))),
     ?_assertThrow({parse_error, ?FILE, 2, {module_rename, mod1, mod2}},
                   parse_module({?FILE, "module mod1\nmodule mod2"}))
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
                parse_module({?FILE, Code1}))
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
    ?assertMatch({ok,
       [#alpaca_module{
           name='test_mod',
           function_exports=[{"add",2}],
           functions=
               [#alpaca_binding{
                   name={symbol,5,"add"},
                   bound_expr=
                       #alpaca_fun{
                          versions=
                              [#alpaca_fun_version{
                                  args=[{symbol,5,"svar_0"},{symbol,5,"svar_1"}],
                                  body=#alpaca_binding{
                                          name={symbol,6,"svar_2"},
                                          bound_expr=
                                              #alpaca_fun{
                                                 versions=[#alpaca_fun_version{
                                                              args=[{symbol,6,"svar_3"},
                                                                    {symbol,6,"svar_4"}],
                                                              body=#alpaca_apply{
                                                                      type=undefined,
                                                                      expr={bif, '+', 6, erlang, '+'},
                                                                      args=[{symbol,6,"svar_3"},
                                                                            {symbol,6,"svar_4"}]}}]},
                                          body=#alpaca_apply{
                                                  expr={symbol,7,"svar_2"},
                                                  args=[{symbol,7,"svar_0"},
                                                        {symbol,7,"svar_1"}]}}}]}}]}]},
                 test_make_modules([Code])).

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
    ?assertMatch({ok,
       [#alpaca_module{
           name='test_mod',
           function_exports=[{"add",2},{"sub",2}],
           functions=
               [#alpaca_binding{
                   name={symbol, 5, "adder"},
                   bound_expr=
                       #alpaca_fun{
                          versions=
                              [#alpaca_fun_version{
                                  args=[{symbol, 5, "svar_0"},
                                        {symbol,5 , "svar_1"}],
                                  body=#alpaca_apply{type=undefined,
                                                     expr={bif, '+', 5, erlang, '+'},
                                                     args=[{symbol, 5, "svar_0"},
                                                           {symbol,5,"svar_1"}]}}]}},
                #alpaca_binding{
                   name={symbol,7,"add1"},
                   bound_expr=
                       #alpaca_fun{
                          versions=
                              [#alpaca_fun_version{
                                  args=[{symbol,7,"svar_2"}],
                                  body=#alpaca_apply{expr={symbol,7,"adder"},
                                                     args=[{symbol,7,"svar_2"},
                                                           {int,7,1}]}}]}},
                #alpaca_binding{
                   name={symbol,9,"add"},
                   bound_expr=
                       #alpaca_fun{
                          versions=
                              [#alpaca_fun_version{
                                  args=[{symbol,9,"svar_3"},{symbol,9,"svar_4"}],
                                  body=#alpaca_apply{expr={symbol,9,"adder"},
                                                     args=[{symbol,9,"svar_3"},
                                                           {symbol,9,"svar_4"}]}}]}},
                #alpaca_binding{
                   name={symbol,11,"sub"},
                   bound_expr=
                       #alpaca_fun{
                          versions=
                              [#alpaca_fun_version{
                                  args=[{symbol,11,"svar_5"},{symbol,11,"svar_6"}],
                                  body=#alpaca_apply{type=undefined,
                                                     expr={bif, '-', 11, erlang, '-'},
                                                     args=[{symbol,11,"svar_5"},
                                                           {symbol,11,"svar_6"}]}}]}}]}]},
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
                         name={symbol, 4, "a"},
                         bound_expr={int, 4, 5}},
                      #alpaca_binding{
                         name={symbol, 6, "b"},
                         bound_expr={int, 6, 6}}]}]},
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
            name={symbol, 1, "f"},
            bound_expr=#alpaca_fun{
                          versions=[#alpaca_fun_version{
                                       args=[{symbol, 1, "svar_0"}],
                                       body=#alpaca_binding{
                                               name={symbol, 1, "svar_1"},
                                               bound_expr={int, 1, 2},
                                               body=#alpaca_apply{
                                                       expr={bif, '+', 1, 'erlang', '+'},
                                                       args=[{symbol, 1, "svar_0"},
                                                             {symbol, 1, "svar_1"}]}}}]}}},
                   rename_bindings(#env{}, A)),
     ?_assertThrow({parse_error, undefined, 2, {duplicate_definition, "x"}},
                   rename_bindings(#env{}, B)),
     ?_assertMatch(
        {_, _, 
         #alpaca_binding{
            name={symbol, 1, "f"},
            bound_expr=
                #alpaca_fun{
                   versions=[#alpaca_fun_version{
                                args=[{symbol, 1, "svar_0"}],
                                body=#alpaca_match{
                                       match_expr={symbol, 1, "svar_0"},
                                       clauses=
                                            [#alpaca_clause{
                                                pattern=#alpaca_tuple{
                                                           values=[{symbol, 2, "svar_1"},
                                                                   {int, 2, 0}]},
                                                result={symbol, 2, "svar_1"}},
                                             #alpaca_clause{
                                                pattern=#alpaca_tuple{
                                                           values=[{symbol, 3, "svar_2"},
                                                                   {symbol, 3, "svar_3"}]},
                                                result={symbol, 3, "svar_3"}}]}}]}}},
         rename_bindings(#env{}, C)),
     ?_assertThrow({parse_error, undefined, 2, {duplicate_definition, "x"}},
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
                                  match_expr={symbol, 1, "svar_0"},
                                  clauses=[#alpaca_clause{
                                              pattern=
                                                  #alpaca_cons{
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
                                              result={symbol, 3, "svar_2"}}]}}]}}},
        rename_bindings(#env{}, E)),
     ?_assertThrow({parse_error, undefined, 2, {duplicate_definition, "y"}},
                   rename_bindings(#env{}, F))
    ].

type_expr_in_type_declaration_test() ->
    ?assertMatch({error, _}, test_parse("type a not_a_var = A not_a_var")).


ambiguous_type_expressions_test() ->
    ?assertMatch({ok, #alpaca_type{
                         name={type_name,1,"my_map"},
                         vars=[],
                         members=[{t_map,
                                   #alpaca_type{
                                      name={type_name,1,"foo"},
                                      vars=[],
                                      members=[]},
                                   t_atom}]}},
                 test_parse("type my_map = map foo atom")),
    ?assertMatch({error, _}, test_parse("type my_map = map foo bar atom")),
    ?assertMatch({error, _}, test_parse("type my_list = list foo atom")),
    ?assertMatch({error, _}, test_parse("type my_pid = pid foo atom")),
    ?assertMatch({ok, #alpaca_type{
                         name={type_name,1,"my_type"},
                         vars=[],
                         members=[#alpaca_type{
                                     name={type_name,1,"foo"},
                                     vars=[{_, #alpaca_type{
                                                  name={type_name, _, "bar"}}},
                                           {_, #alpaca_type{
                                                  name={type_name, _, "baz"}}}],
                                     members=[#alpaca_type{
                                                 name={type_name,1,"bar"},
                                                 vars=[],
                                                 members=[]},
                                              #alpaca_type{
                                                 name={type_name,1,"baz"},
                                                 vars=[],
                                                 members=[]}]}]}},
                 test_parse("type my_type = foo bar baz")),
    ?assertMatch({ok, #alpaca_type{
                         name={type_name,1,"my_type"},
                         vars=[],
                         members=[#alpaca_type{
                                     name={type_name,1,"foo"},
                                     vars=[{_,
                                            #alpaca_type{
                                               name={type_name, _, "bar"},
                                               vars=[{_,
                                                      #alpaca_type{
                                                        name={_, _, "baz"}}}]}}],
                                     members=[#alpaca_type{
                                                 name={type_name,1,"bar"},
                                                 vars=[_],
                                                 members=[#alpaca_type{
                                                             name={type_name,1,"baz"},
                                                             vars=[],
                                                             members=[]}]}]}]}},
                 test_parse("type my_type = foo (bar baz)")).



expand_exports_test_() ->
    [fun() ->
             Def = fun(Name, Arity) ->
                           #alpaca_binding{
                              name={symbol, 0, Name},
                              bound_expr=#alpaca_fun{arity=Arity}}
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
                  "let foo x = x\n\n"
                  "let foo x y = x + y\n\n"
                  "let bar x = x",

              {ok, [Mod]} = test_make_modules([Code]),
              [#alpaca_module{function_exports=FEs}] = expand_exports([Mod], []),
              ?assertEqual([{"foo", 1}, {"foo", 2}, {"bar", 1}], FEs)
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
                   function_imports=[{"foo", {m1, 1}}, {"foo", {m1, 2}}]},
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
             ?assertMatch({ok, 
                [#alpaca_module{name=a},
                 #alpaca_module{
                    name=b,
                    functions=[#alpaca_binding{
                                  bound_expr=#alpaca_fun{
                                                versions=[#alpaca_fun_version{
                                                             body=#alpaca_apply{
                                                                     expr=#alpaca_far_ref{
                                                                             module=a,
                                                                             name="add",
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
                      functions=[_,
                                 #alpaca_binding{
                                    bound_expr=#alpaca_fun{
                                                  versions=[#alpaca_fun_version{
                                                               body=#alpaca_apply{
                                                                       expr=#alpaca_far_ref{
                                                                               module=a,
                                                                               name="(|>)",
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
                                    {function_not_exported, a, "bar"}}},
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

test_make_modules(Sources) ->
    NamedSources = lists:map(fun(C) -> {?FILE, C} end, Sources),
    make_modules(NamedSources).

-endif.
