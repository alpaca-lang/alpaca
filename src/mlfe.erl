% Copyright 2016 Jeremy Pierre
%
% Licensed under the Apache License, Version 2.0 (the "License");
% you may not use this file except in compliance with the License.
% You may obtain a copy of the License at
%
%     http://www.apache.org/licenses/LICENSE-2.0
%
% Unless required by applicable law or agreed to in writing, software
% distributed under the License is distributed on an "AS IS" BASIS,
% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
% See the License for the specific language governing permissions and
% limitations under the License.
-module(mlfe).

-export([compile/1]).

% Can be safely ignored, it is meant to be called by external OTP-apps and part
% of the public API.
-ignore_xref([compile/1]).

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
    io:format("~nFORMS~n~w~n", [Forms]),
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

    F = fun(_, {error, _, _}=Err) -> Err;
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

compile_and_load(Files) ->
    Compiled = compile({files, Files}),
    LoadFolder = fun(#compiled_module{name=N, filename=FN, bytes=Bin}, Acc) ->
                         {module, N} = code:load_binary(N, FN, Bin),
                         io:format("Loaded ~w ~s~n", [N, FN]),
                         [N|Acc]
                 end,
    lists:foldl(LoadFolder, [], Compiled).

type_import_test() ->
    Files = ["test_files/basic_adt.mlfe", "test_files/type_import.mlfe"],
    ModuleNames = compile_and_load(Files),
    io:format("Compiled and loaded modules are ~w~n", [ModuleNames]),
    M = type_import,
    ?assertEqual(2, M:test_output(unit)),
    [code:delete(N) || N <- ModuleNames].

basic_pid_test() ->
    Files = ["test_files/basic_pid_test.mlfe"],
    [M] = compile_and_load(Files),
    Pid = M:start_pid_fun(0),
    Pid ! {'Fetch', self()},
    X = receive
            I -> I
        end,
    ?assertEqual(0, X),
    Pid ! {'Add', 5},
    Pid ! {'Fetch', self()},
    ShouldBe5 = receive
                    II -> II
                end,
    ?assertEqual(5, ShouldBe5),
    code:delete(M).

simple_example_module_test() ->
    [M] = compile_and_load(["test_files/simple_example.mlfe"]),
    code:delete(M).
-endif.
