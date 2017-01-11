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
-module(alpaca).

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

-include("alpaca_ast.hrl").

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
    Mods = alpaca_ast_gen:make_modules([Code]),
    case type_modules(Mods) of
        {error, _}=Err -> Err;
        {ok, [TypedMod]} ->
            {ok, Forms} = alpaca_codegen:gen(TypedMod, Opts),
            compile:forms(Forms, [report, verbose, from_core])
    end;

compile({files, Filenames}, Opts) ->
    Code = load_files(Filenames),
    {ok, Mods} = type_modules(alpaca_ast_gen:make_modules(Code)),
    Compiled = lists:foldl(
                 fun(M, Acc) ->
                         [compile_module(M, Opts)|Acc]
                 end, [], Mods),
    Compiled.

load_files(Filenames) ->
    lists:foldl(
      fun(FN, Acc) ->
              {ok, Device} = file:open(FN, [read, {encoding, utf8}]),
              Res = read_file(Device, []),
              ok = file:close(Device),
              [Res|Acc]
      end, [], Filenames).

compile_module(#alpaca_module{name=N}=Mod, Opts) ->
    {ok, Forms} = alpaca_codegen:gen(Mod, Opts),
    {ok, _, Bin} = compile:forms(Forms, [report, verbose, from_core]),
    PrefixedName = list_to_atom("alpaca_" ++ atom_to_list(N)),
    #compiled_module{
       name=PrefixedName,
       filename=atom_to_list(PrefixedName) ++ ".beam",
       bytes=Bin}.

read_file(_, [eof|Memo]) ->
    lists:flatten(lists:reverse(Memo));
read_file(Device, Memo) ->
    read_file(Device, [io:get_line(Device, '')|Memo]).

type_modules(Mods) ->
    alpaca_typer:type_modules(Mods).

-ifdef(TEST).

basic_file_test() ->
    Res = file("test_files/basic_compile_file.alp"),
    [#compiled_module{name=N, filename=FN, bytes=Bin}] = Res,
    ?assertEqual('alpaca_basic_compile_file', N),
    ?assertEqual("alpaca_basic_compile_file.beam", FN),
    ?assertMatch({module, N}, code:load_binary(N, FN, Bin)),
    ?assertEqual(1998, N:double(999)).

basic_math_compile_test() ->
    Res = file("test_files/basic_math.alp", []),
    [#compiled_module{name=N, filename=FN, bytes=Bin}] = Res,
    ?assertEqual('alpaca_basic_math', N),
    ?assertEqual("alpaca_basic_math.beam", FN),
    {module, N} = code:load_binary(N, FN, Bin),
    ?assertEqual(3, N:add2(1)),
    ?assertEqual(5, N:add(2, 3)),
    ?assertEqual(-1, N:dec(0)),
    ?assertEqual(-1, N:dec_alt(0)),
    ?assertEqual(4.0, N:neg_float(-4.0)),
    true = code:delete(N).

basic_adt_compile_test() ->
    Res = compile({files, ["test_files/basic_adt.alp"]}),
    [#compiled_module{name=N, filename=FN, bytes=Bin}] = Res,
    {module, N} = code:load_binary(N, FN, Bin),
    ?assertEqual(0, N:len('Nil')),
    ?assertEqual(1, N:len({'Cons', {1, 'Nil'}})),
    ?assertEqual(2, N:len({'Cons', {1, {'Cons', {2, 'Nil'}}}})),
    true = code:delete(N).

basic_concat_compile_test() ->
    Res = compile({files, ["test_files/string_concat.alp"]}),
    [#compiled_module{name=N, filename=FN, bytes=Bin}] = Res,
    {module, N} = code:load_binary(N, FN, Bin),
    ?assertEqual("Hello, world", N:hello("world")),
    true = code:delete(N).

compile_and_load(Files, Opts) ->
    Compiled = compile({files, Files}, Opts),    
    LoadFolder = fun(#compiled_module{name=N, filename=FN, bytes=Bin}, Acc) ->
                         Prefixed = list_to_atom("alpaca_" ++ atom_to_list(N)),
                         {module, N_} = code:load_binary(N, FN, Bin),
                         io:format("Loaded ~w ~s~n", [N, FN]),
                         [N|Acc]
                 end,
    lists:reverse(lists:foldl(LoadFolder, [], Compiled)).

type_import_test() ->
    Files = ["test_files/basic_adt.alp", "test_files/type_import.alp"],
    ModuleNames = compile_and_load(Files, []),
    io:format("Compiled and loaded modules are ~w~n", [ModuleNames]),
    M = alpaca_type_import,
    ?assertEqual(2, M:test_output(unit)),
    [code:delete(N) || N <- ModuleNames].

type_imports_and_pattern_test() ->
    Files = ["test_files/basic_adt.alp", "test_files/list_opts.alp"],
    ModuleNames = compile_and_load(Files, []),
    io:format("Compiled and loaded modules are ~w~n", [ModuleNames]),
    LO = alpaca_list_opts,
    ADT = alpaca_basic_adt,
    ?assertEqual({'Some', 1}, LO:head_opt({'Cons', {1, {'Cons', {2, 'Nil'}}}})),
    ?assertEqual('None', LO:head_opt('Nil')),
    [code:delete(N) || N <- ModuleNames].

private_types_error_test() ->
    Files = ["test_files/unexported_adts.alp", "test_files/list_opts.alp"],
    Code = load_files(Files),
    ?assertEqual(
       {error, {unexported_type, list_opts, basic_adt, "my_list"}},
       type_modules(alpaca_ast_gen:make_modules(Code))).

basic_pid_test() ->
    Files = ["test_files/basic_pid_test.alp"],
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
    Files =["test_files/basic_map_test.alp"],
    [M] = compile_and_load(Files, []),
    ?assertEqual({'Ok', 1}, M:get('one', M:test_map(unit))),
    ?assertEqual('NotFound', M:get('four', M:test_map(unit))),

    ?assertEqual({'Ok', <<"b">>}, M:get({'two', 2}, M:test_tuple_key_map(unit))),
    ?assertEqual('NotFound', M:get({'one', 2}, M:test_tuple_key_map(unit))),
    ?assertEqual(#{one => 1, two => 2}, M:add(one, 1, #{two => 2})),

    code:delete(M).

basic_binary_test() ->
    Files =["test_files/basic_binary.alp"],
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
    Files = ["test_files/basic_module_with_tests.alp"],
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
    [M] = compile_and_load(["test_files/simple_example.alp"], []),
    code:delete(M).

comments_test() ->
    [M] = compile_and_load(["test_files/comments.alp"], []),
    ?assertMatch(4, M:double(2)).

top_level_value_test() ->
    [M] = compile_and_load(["test_files/values.alp"], []),
    ?assertMatch({42, <<"Vicugna pacos">>}, M:test_values({})),
    code:delete(M).

higher_order_function_test() ->
    [M] = compile_and_load(["test_files/higher_order_functions.alp"], []),
    Dict0 = M:new({}),
    ?assertEqual('None', M:lookup(key, Dict0)),
    Dict1 = M:insert(key, value, Dict0),
    ?assertEqual({'Some', value}, M:lookup(key, Dict1)),
    ?assertEqual('None', M:lookup(anotherkey, Dict1)),
    code:delete(M).

simple_record_test() ->
    [M] = compile_and_load(["test_files/simple_records.alp"], []),
    ?assertEqual({<<"sample">>, <<"person">>}, M:sample_person({})),
    code:delete(M).

polymorphic_record_test() ->
    [M] = compile_and_load(["test_files/polymorphic_record_test.alp"], []),
    ?assertEqual(<<"bar">>, M:with_y({})),
    ?assertEqual(<<"baz">>, M:with_y_and_throwaway_x({})),
    code:delete(M).

multiple_underscore_test() ->
    [M] = compile_and_load(["test_files/multiple_underscore_test.alp"], []),
    ?assertEqual(list, M:list_check({})),
    %% Compiler adds the __struct__ tag to distinguish between records
    %% and maps:
    Map = #{'__struct__' => 'map', x => 1, y => 2},
    ?assertEqual(<<"just two">>, M:map_check(Map)),
    ?assertEqual(<<"all three">>, M:map_check(Map#{z => 3})),
    ?assertEqual(<<"three">>, M:tuple_check({1, 2, 3})),
    code:delete(M).

circle_module_test() ->
    [M] = compile_and_load(["test_files/circles.alp"], []),
    ?assertEqual(12.56636, M:area(M:new(2))),
    code:delete(M).

records_with_x_module_test() ->
    [M] = compile_and_load(["test_files/records_with_x.alp"], []),
    ?assertEqual(2, M:get_x(M:make_xyz(2, 3, 4))),
    ?assertEqual(5, M:get_x(M:make_xy(5, 6))),
    code:delete(M).

%% A pattern match that matches records and maps with the same key should
%% correctly distinguish between maps and records that are compiled as
%% maps.
record_vs_map_match_order_test() ->
    [M] = compile_and_load(["test_files/record_map_match_order.alp"], []),
    ?assertEqual(1, M:check_map({})),
    ?assertEqual(2, M:check_record({})),
    code:delete(M).
    
raise_errors_test() ->
    [M] = compile_and_load(["test_files/error_tests.alp"], []),
    ?assertException(throw, <<"this should be a throw">>, M:raise_throw(unit)),
    ?assertException(exit, <<"exit here">>, M:raise_exit(unit)),
    ?assertException(error, <<"and an error">>, M:raise_error(unit)),

    ?assertException(throw, <<"oh no zero!">>, M:throw_or_int(0)),
    ?assertEqual(4, M:throw_or_int(2)),
    code:delete(M).

function_pattern_args_test() ->
    [M] = compile_and_load(["test_files/function_pattern_args.alp"], []),
    ?assertEqual(true, M:is_zero(0)),
    ?assertEqual(false, M:is_zero(5)),

    ?assertEqual(true, M:both_zero(0, 0)),
    ?assertEqual(false, M:both_zero(0, 1)),
    ?assertEqual(false, M:both_zero(1, 0)),
    ?assertEqual(false, M:both_zero(5, 4)),

    ?assertEqual(1, M:get_x(M:make_xy(1, 2))),

    ?assertEqual({'Some', 2}, M:get_opt_x(M:make_xy(2, 3))),
    ?assertEqual('None', M:get_opt_x(M:make_y(2))),
    
    ?assertEqual({'Some', 4}, M:doubler(2)),
    ?assertEqual({'Some', 4}, M:double_maybe_x(M:make_xy(2, 3))),
    ?assertEqual('None', M:double_maybe_x(M:make_y(2))),
    
    code:delete(M).

radius_test() ->
    [M1, M2] = compile_and_load(
            ["test_files/radius.alp", 
             "test_files/use_radius.alp"], 
            []),
    ?assertEqual(1, M1:test_radius(unit)),
    code:delete(M1),
    code:delete(M2).

allow_duplicate_definition_with_different_arity_test() ->
    [M] = compile_and_load(["test_files/same_name_diff_arity.alp"], []),
    ?assertEqual([0, 1, 2, 3], M:seq(3)),
    code:delete(M).

apply_to_expressions_test() ->
    [M] = compile_and_load(["test_files/apply_to_expression.alp"], []),
    ?assertEqual(4, M:foo(unit)),
    ?assertEqual(6, M:uses_fun(3)),
    code:delete(M).

batch_export_test() ->
    [M] = compile_and_load(["test_files/batch_export.alp"], []),
    ?assertEqual(1, M:foo(1)),
    ?assertEqual(5, M:foo(2, 3)),
    ?assertEqual(8, M:mult(2, 4)),
    code:delete(M).

%% There seems to be a compilation bug in the early formatter work I'm trying
%% using Alpaca to write its own code formatter.  Figured I might as well just
%% add the test here.
own_formatter_test() ->
    Files = ["src/alpaca_native_ast.alp", "src/alpaca_format.alp"],
    [M1, M2] = compile_and_load(Files, []),
    code:delete(M1),
    code:delete(M2).

export_import_test() ->
    Files = ["test_files/export_all_arities.alp", "test_files/import_test.alp"],
    [M1, M2] = compile_and_load(Files, []),
    ?assertEqual(12, M1:test_pipe({})),
    ?assertEqual(12, M1:test_pipe_far_call({})),
    ?assertEqual(5, M1:test_specified_arity({})),
    code:delete(M1),
    code:delete(M2).

-endif.
