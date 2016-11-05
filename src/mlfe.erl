%%% -*- mode: erlang;erlang-indent-level: 4;indent-tabs-mode: nil -*-
%%% ex: ft=erlang ts=4 sw=4 et
%%%
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
-module(mlfe).

-export([ compile/1
        , compile/2
        , file/1
        , file/2
        ]).

%% Can be safely ignored, it is meant to be called by external OTP-apps and part
%% of the public API.
-ignore_xref([ compile/1
             , compile/2
             , file/1
             , file/2
             ]).

-include("mlfe_ast.hrl").

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

-record(compiled_module, {
          name :: atom(),
          filename :: string(),
          bytes :: binary()}).

-type compile_res() :: {ok, list(#compiled_module{})} | {error, term()}.

-spec file(file:filename()) -> compile_res().
file(File) ->
    file(File, []).

-spec file(file:filename(), list()) -> compile_res().
file(File, Opts) ->
    compile({files, [File]}, Opts).

-spec compile({text, list(binary())}
              |{files, list(string())}) -> compile_res().
compile(What) ->
    compile(What, []).

compile({text, Code}, Opts) ->
    {ok, _, _, Mods} = parse_modules([Code]),
    case type_modules(Mods) of
        {error, _}=Err -> Err;
        {ok, [TypedMod]} ->
            {ok, Forms} = mlfe_codegen:gen(TypedMod, Opts),
            compile:forms(Forms, [report, verbose, from_core])
    end;

compile({files, Filenames}, Opts) ->
    Code = lists:foldl(
             fun(FN, Acc) ->
                     {ok, Device} = file:open(FN, [read, {encoding, utf8}]),
                     Res = read_file(Device, []),
                     ok = file:close(Device),
                     [Res|Acc]
             end, [], Filenames),
    {ok, Mods} = type_modules(parse_modules(Code)),
    Compiled = lists:foldl(
                 fun(M, Acc) ->
                         [compile_module(M, Opts)|Acc]
                 end, [], Mods),
    Compiled.


compile_module(#mlfe_module{name=N}=Mod, Opts) ->
    {ok, Forms} = mlfe_codegen:gen(Mod, Opts),
    {ok, _, Bin} = compile:forms(Forms, [report, verbose, from_core]),
    #compiled_module{
       name=N,
       filename=atom_to_list(N) ++ ".beam",
       bytes=Bin}.

read_file(_, [eof|Memo]) ->
    lists:flatten(lists:reverse(Memo));
read_file(Device, Memo) ->
    read_file(Device, [io:get_line(Device, '')|Memo]).

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
    mlfe_typer:type_modules(Mods).

-ifdef(TEST).

basic_file_test() ->
    Res = file("test_files/basic_compile_file.mlfe"),
    [#compiled_module{name=N, filename=FN, bytes=Bin}] = Res,
    ?assertEqual('basic_compile_file', N),
    ?assertEqual("basic_compile_file.beam", FN),
    ?assertMatch({module, N}, code:load_binary(N, FN, Bin)),
    ?assertEqual(1998, N:double(999)).

basic_math_compile_test() ->
    Res = file("test_files/basic_math.mlfe", []),
    [#compiled_module{name=N, filename=FN, bytes=Bin}] = Res,
    ?assertEqual('basic_math', N),
    ?assertEqual("basic_math.beam", FN),
    {module, N} = code:load_binary(N, FN, Bin),
    ?assertEqual(3, N:add2(1)),
    ?assertEqual(5, N:add(2, 3)),
    ?assertEqual(-1, N:dec(0)),
    ?assertEqual(-1, N:dec_alt(0)),
    ?assertEqual(4.0, N:neg_float(-4.0)),
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

compile_and_load(Files, Opts) ->
    Compiled = compile({files, Files}, Opts),
    LoadFolder = fun(#compiled_module{name=N, filename=FN, bytes=Bin}, Acc) ->
                         {module, N} = code:load_binary(N, FN, Bin),
                         io:format("Loaded ~w ~s~n", [N, FN]),
                         [N|Acc]
                 end,
    lists:foldl(LoadFolder, [], Compiled).

type_import_test() ->
    Files = ["test_files/basic_adt.mlfe", "test_files/type_import.mlfe"],
    ModuleNames = compile_and_load(Files, []),
    io:format("Compiled and loaded modules are ~w~n", [ModuleNames]),
    M = type_import,
    ?assertEqual(2, M:test_output(unit)),
    [code:delete(N) || N <- ModuleNames].

basic_pid_test() ->
    Files = ["test_files/basic_pid_test.mlfe"],
    [M] = compile_and_load(Files, []),
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

basic_map_test() ->
    Files =["test_files/basic_map_test.mlfe"],
    [M] = compile_and_load(Files, []),
    ?assertEqual({'Ok', 1}, M:get('one', M:test_map(unit))),
    ?assertEqual('NotFound', M:get('four', M:test_map(unit))),

    ?assertEqual({'Ok', <<"b">>}, M:get({'two', 2}, M:test_tuple_key_map(unit))),
    ?assertEqual('NotFound', M:get({'one', 2}, M:test_tuple_key_map(unit))),
    ?assertEqual(#{one => 1, two => 2}, M:add(one, 1, #{two => 2})),

    code:delete(M).

basic_binary_test() ->
    Files =["test_files/basic_binary.mlfe"],
    [M] = compile_and_load(Files, []),
    ?assertEqual(1, M:count_one_twos(<<1, 2>>)),
    ?assertEqual(2, M:count_one_twos(<<1, 2, 1, 2, 3, 1, 2>>)),
    ?assertEqual(0, M:count_one_twos(<<2, 1, 0>>)),

    ?assertEqual(1, M:first_three_bits(<<2#00100000>>)),
    ?assertEqual(3, M:first_three_bits(<<2#01100000>>)),

    ?assertEqual(<<"안녕"/utf8>>, M:utf8_bins(unit)),

    ?assertEqual(<<" world">>, M:drop_hello(<<"hello world">>)),

    code:delete(M).

basic_unit_tests_test() ->
    Files = ["test_files/basic_module_with_tests.mlfe"],
    [M] = compile_and_load(Files, [test]),
    %% Checking that the synthesized test functions are exported:
    ?assertEqual(passed, M:'add_2_and_2_test'()),
    try
        M:'subtract_2_from_4_test'()
    catch
        error:R ->
            ?assertEqual(R, "Not equal:  2 and 3")
    end.

simple_example_module_test() ->
    [M] = compile_and_load(["test_files/simple_example.mlfe"], []),
    code:delete(M).

comments_test() ->
    [M] = compile_and_load(["test_files/comments.mlfe"], []),
    ?assertMatch(4, M:double(2)).

higher_order_function_test() ->
    [M] = compile_and_load(["test_files/higher_order_functions.mlfe"], []),
    Dict0 = M:new({}),
    ?assertEqual('None', M:lookup(key, Dict0)),
    Dict1 = M:insert(key, value, Dict0),
    ?assertEqual({'Some', value}, M:lookup(key, Dict1)),
    ?assertEqual('None', M:lookup(anotherkey, Dict1)),
    code:delete(M).

simple_record_test() ->
    [M] = compile_and_load(["test_files/simple_records.mlfe"], []),
    ?assertEqual({<<"sample">>, <<"person">>}, M:sample_person({})),
    code:delete(M).

polymorphic_record_test() ->
    [M] = compile_and_load(["test_files/polymorphic_record_test.mlfe"], []),
    ?assertEqual(<<"bar">>, M:with_y({})),
    code:delete(M).

%% A pattern match that matches records and maps with the same key should
%% correctly distinguish between maps and records that are compiled as
%% maps.
record_vs_map_match_order_test() ->
    [M] = compile_and_load(["test_files/record_map_match_order.mlfe"], []),
    ?assertEqual(1, M:check_map({})),
    ?assertEqual(2, M:check_record({})),
    code:delete(M).
    
-endif.
