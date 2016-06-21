-module(mlfe).

-export([compile/1]).

-include("mlfe_ast.hrl").

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

-record(compiled_module, {
          name :: atom(),
          filename :: string(),
          bytes :: binary()}).

-spec compile({text, list(binary())}
              |{files, list(string())}) -> {ok, list(#compiled_module{})} | 
                                         {error, term()}.
compile({text, Code}) ->
    {ok, _, _, Mods} = parse_modules([Code]),
     case type_modules(Mods) of
         {error, _}=Err -> Err;
         {ok, _, [TypedMod]} ->
             {ok, Forms} = mlfe_codegen:gen(TypedMod),
             compile:forms(Forms, [report, verbose, from_core])
     end;

compile({files, Filenames}) ->
    Code = lists:foldl(fun(FN, Acc) ->
                               {ok, Bin} = file:read_file(FN),
                               [binary_to_list(Bin)|Acc]
                       end, [], Filenames),
    {ok, _, Mods} = type_modules(parse_modules(Code)),
    Compiled = lists:foldl(fun(M, Acc) -> [compile_module(M)|Acc] end, [], Mods),
    Compiled.
    

compile_module(#mlfe_module{name=N}=Mod) ->
    {ok, Forms} = mlfe_codegen:gen(Mod),
    {ok, _, Bin} = compile:forms(Forms, [report, verbose, from_core]),
    #compiled_module{
       name=N,
       filename=atom_to_list(N) ++ ".beam",
       bytes=Bin}.

parse_modules(Mods) ->
    F = fun
            (_, {error, _}=Err) -> Err;
            (ModCode, {ok, NV, Map, Acc}) ->
                case mlfe_ast_gen:parse_module(NV, ModCode) of
                    {ok, NV2, Map2, Mod} ->
                        {ok, NV2, maps:merge(Map, Map2), [Mod|Acc]};
                    {error, _}=Err ->
                        Err
                end
        end,
    lists:foldl(F, {ok, 0, maps:new(), []}, Mods).

type_modules({ok, _, _, Mods}) ->
    type_modules(Mods);
type_modules({error, _}=Err) ->
    Err;
type_modules(Mods) ->
    E = mlfe_typer:new_env(Mods),

    F = fun
            (_, {error, _, _}=Err) -> Err;
            (M, {ok, Env, Acc}) ->
                case mlfe_typer:typ_module(M, Env) of
                    {ok, M2} -> {ok, mlfe_typer:replace_env_module(Env, M2), [M2|Acc]};
                    Err -> Err
                end
        end,
    lists:foldl(F, {ok, E, []}, Mods).

-ifdef(TEST).

basic_math_compile_test() ->
    Res = compile({files, ["test_files/basic_math.mlfe"]}),
    [#compiled_module{name=N, filename=FN, bytes=Bin}] = Res,
    ?assertEqual('basic_math', N),
    ?assertEqual("basic_math.beam", FN),
    {module, N} = code:load_binary(N, FN, Bin),
    ?assertEqual(3, N:add2(1)),
    ?assertEqual(5, N:add(2, 3)),
    true = code:delete(N).

basic_adt_compile_test() ->
    Res = compile({files, ["test_files/basic_adt.mlfe"]}),
    [#compiled_module{name=N, filename=FN, bytes=Bin}] = Res,
    {module, N} = code:load_binary(N, FN, Bin),
    ?assertEqual(0, N:len('Nil')),
    ?assertEqual(1, N:len({'Cons', {1, 'Nil'}})),
    ?assertEqual(2, N:len({'Cons', {1, {'Cons', {2, 'Nil'}}}})),
    true = code:delete(N).

basic_concat_compile_test() ->
    Res = compile({files, ["test_files/string_concat.mlfe"]}),
    [#compiled_module{name=N, filename=FN, bytes=Bin}] = Res,
    {module, N} = code:load_binary(N, FN, Bin),
    ?assertEqual("Hello, world", N:hello("world")),
    true = code:delete(N).

-endif.
