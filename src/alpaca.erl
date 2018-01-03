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
        , compiler_info/0
        , hash_source/1
        , retrieve_hash/1
        , list_dependencies/1
        ]).

%% Can be safely ignored, it is meant to be called by external OTP-apps and part
%% of the public API.
-ignore_xref([ compile/1
             , compile/2
             , file/1
             , file/2
             , compiler_info/0
             , hash_source/1
             , retrieve_hash/1
             , list_dependencies/1
             ]).

-include("alpaca_ast.hrl").

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

-define(COMPILER_VERSION, "0.2.8").

-record(compiled_module, {
          name :: atom(),
          filename :: string(),
          bytes :: binary()}).

-type compile_res() :: {ok, list(#compiled_module{})} | {error, term()}.

-spec compiler_info() -> list({atom(), term()}).
compiler_info() ->
    [{version, ?COMPILER_VERSION}].

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
    compile_phase_1([{"<no file>", Code}], Opts);

compile({files, Filenames}, Opts) ->
    %% Files may be .beam files or .alp files
    compile_phase_1(load_files(Filenames), Opts).

compile_phase_1(Sources, Opts) ->
    {BeamFiles, AlpacaSrcs} =
        lists:partition(fun({FN, _}) ->
                            filename:extension(FN) == ".beam"
                        end, Sources),

    DefaultImports = proplists:get_value(default_imports, Opts, {[], []}),

    case alpaca_ast_gen:make_modules(AlpacaSrcs, BeamFiles, DefaultImports) of
        {error, _}=Err -> Err;
        {ok, Mods} ->
            compile_phase_2(Mods, Opts)
    end.

compile_phase_2(Mods, Opts) ->
    case type_modules(Mods) of
        {error, _}=Err -> Err;
        {ok, TypedMods} -> compile_phase_3(TypedMods, Opts)
    end.

compile_phase_3(Mods, Opts) ->
    %% Don't check precompiled modules - as the AST is stripped, they will not
    %% have function bodies and so will always fail these checks
    ToCheckMods = lists:filter(fun(#alpaca_module{precompiled=P}) -> not P end, Mods),
    ExhaustivenessWarnings = alpaca_exhaustiveness:check_exhaustiveness(ToCheckMods),
    maybe_print_exhaustivess_warnings(ExhaustivenessWarnings, Opts),
    compile_phase_4(Mods, Opts).

compile_phase_4(Mods, Opts) ->
    %% Filter out precompiled modules
    CompileMods = lists:filter(fun(#alpaca_module{precompiled=P}) -> not P end, Mods),
    {ok, lists:map(fun(M) -> compile_module(M, Opts) end, CompileMods)}.

%% For some given Alpaca source code (list), generates a hash specific
%% to this version of the Alpaca compiler. This is so it may be compared
%% against compiled versions of modules.
hash_source(Src) ->
    crypto:hash(md5, Src ++ ?COMPILER_VERSION).

%% From a compiled Alpaca beam file, extract the stored hash.
retrieve_hash(Filename) ->
    {ok,{_,[{attributes,A}]}} = beam_lib:chunks(Filename,[attributes]),
    proplists:get_value(alpaca_hash, A).

%% For some given Alpaca source code (binary or list), attempt to extract a
%% tuple of {Module, [Dependency]}. This is so that external tools can generate
%% a graph of the relationship between modules without having to compile.
list_dependencies(Src) ->
    alpaca_ast_gen:list_dependencies(Src).

maybe_print_exhaustivess_warnings(Warnings, Opts) ->
  case proplists:get_value(warn_exhaustiveness, Opts, true) of
    true  ->
      lists:foreach(fun alpaca_exhaustiveness:print_warning/1, Warnings);
    _ ->
      ok
  end.

load_files(Filenames) ->
    Loaded = lists:foldl(
      fun(FN, Acc) ->
          Res = case filename:extension(FN) of
                    ".alp" ->
                        {ok, Device} = file:open(FN, [read, {encoding, utf8}]),
                        R = read_file(Device, []),
                        ok = file:close(Device),
                        R;
                    ".beam" ->
                        {ok,{_,[{attributes,A}]}} = beam_lib:chunks(FN,[attributes]),
                        TypeInfo = proplists:get_value(alpaca_typeinfo, A),
                        TypeInfo#alpaca_module{precompiled=true}
                end,

              [{FN, Res}|Acc]
      end, [], Filenames),
    %% Ensure original order is preserved; This helps with incremental builds
    lists:reverse(Loaded).

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


pd(Module) ->
    code:purge(Module),
    code:delete(Module).

basic_file_test() ->
    {ok, Res} = file("test_files/basic_compile_file.alp"),
    [#compiled_module{name=N, filename=FN, bytes=Bin}] = Res,
    ?assertEqual('alpaca_basic_compile_file', N),
    ?assertEqual("alpaca_basic_compile_file.beam", FN),
    ?assertMatch({module, N}, code:load_binary(N, FN, Bin)),
    ?assertEqual(1998, N:double(999)).

basic_math_compile_test() ->
    {ok, Res} = file("test_files/basic_math.alp", []),
    [#compiled_module{name=N, filename=FN, bytes=Bin}] = Res,
    ?assertEqual('alpaca_basic_math', N),
    ?assertEqual("alpaca_basic_math.beam", FN),
    {module, N} = code:load_binary(N, FN, Bin),
    ?assertEqual(3, N:add2(1)),
    ?assertEqual(5, N:add(2, 3)),
    ?assertEqual(-1, N:dec(0)),
    ?assertEqual(-1, N:dec_alt(0)),
    ?assertEqual(4.0, N:neg_float(-4.0)),
    true = pd(N).

basic_adt_compile_test() ->
    {ok, Res} = compile({files, ["test_files/basic_adt.alp"]}),
    [#compiled_module{name=N, filename=FN, bytes=Bin}] = Res,
    {module, N} = code:load_binary(N, FN, Bin),
    ?assertEqual(0, N:len('Nil')),
    ?assertEqual(1, N:len({'Cons', {1, 'Nil'}})),
    ?assertEqual(2, N:len({'Cons', {1, {'Cons', {2, 'Nil'}}}})),
    true = pd(N).

basic_concat_compile_test() ->
    {ok, Res} = compile({files, ["test_files/string_concat.alp"]}),
    [#compiled_module{name=N, filename=FN, bytes=Bin}] = Res,
    {module, N} = code:load_binary(N, FN, Bin),
    ?assertEqual("Hello, world", N:hello("world")),
    true = pd(N).

compile_and_load(Files, Opts) ->
    {ok, Compiled} = compile({files, Files}, Opts),
    LoadFolder = fun(#compiled_module{name=N, filename=FN, bytes=Bin}, Acc) ->
                         {module, _N} = code:load_binary(N, FN, Bin),
                         io:format("Loaded ~w ~s~n", [N, FN]),
                         [N|Acc]
                 end,
    lists:reverse(lists:foldl(LoadFolder, [], Compiled)).

type_import_test() ->
    Files = ["test_files/basic_adt.alp", "test_files/type_import.alp"],
    ModuleNames = compile_and_load(Files, []),
    io:format("Compiled and loaded modules are ~w~n", [ModuleNames]),
    M = alpaca_type_import,
    ?assertEqual(2, M:test_output({})),
    [pd(N) || N <- ModuleNames].

type_imports_and_pattern_test() ->
    Files = ["test_files/basic_adt.alp", "test_files/list_opts.alp"],
    ModuleNames = compile_and_load(Files, []),
    io:format("Compiled and loaded modules are ~w~n", [ModuleNames]),
    LO = alpaca_list_opts,
    ?assertEqual({'Some', 1}, LO:head_opt({'Cons', {1, {'Cons', {2, 'Nil'}}}})),
    ?assertEqual('None', LO:head_opt('Nil')),
    [pd(N) || N <- ModuleNames].

private_types_error_test() ->
    Files = ["test_files/unexported_adts.alp", "test_files/list_opts.alp"],
    Code = load_files(Files),
    {ok, Mods} = alpaca_ast_gen:make_modules(Code),
    ?assertEqual(
       {error, {unexported_type, list_opts, basic_adt, <<"my_list">>}},
       type_modules(Mods)).

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
    pd(M).

basic_map_test() ->
    Files =["test_files/basic_map_test.alp"],
    [M] = compile_and_load(Files, []),
    ?assertEqual({'Ok', 1}, M:get('one', M:test_map({}))),
    ?assertEqual('NotFound', M:get('four', M:test_map({}))),

    ?assertEqual({'Ok', <<"b">>}, M:get({'two', 2}, M:test_tuple_key_map({}))),
    ?assertEqual('NotFound', M:get({'one', 2}, M:test_tuple_key_map({}))),
    ?assertEqual(#{one => 1, two => 2}, M:add(one, 1, #{two => 2})),

    pd(M).

basic_binary_test() ->
    Files =["test_files/basic_binary.alp"],
    [M] = compile_and_load(Files, []),
    ?assertEqual(1, M:count_one_twos(<<1, 2>>)),
    ?assertEqual(2, M:count_one_twos(<<1, 2, 1, 2, 3, 1, 2>>)),
    ?assertEqual(0, M:count_one_twos(<<2, 1, 0>>)),

    ?assertEqual(1, M:first_three_bits(<<2#00100000>>)),
    ?assertEqual(3, M:first_three_bits(<<2#01100000>>)),

    ?assertEqual(<<"안녕"/utf8>>, M:utf8_bins({})),

    ?assertEqual(<<" world">>, M:drop_hello(<<"hello world">>)),

    pd(M).

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
    pd(M).

comments_test() ->
    [M] = compile_and_load(["test_files/comments.alp"], []),
    ?assertMatch(4, M:double(2)).

top_level_value_test() ->
    [M] = compile_and_load(["test_files/values.alp"], []),
    ?assertMatch({42, <<"Vicugna pacos">>}, M:test_values({})),
    pd(M).

higher_order_function_test() ->
    [M] = compile_and_load(["test_files/higher_order_functions.alp"], []),
    Dict0 = M:new({}),
    ?assertEqual('None', M:lookup(key, Dict0)),
    Dict1 = M:insert(key, value, Dict0),
    ?assertEqual({'Some', value}, M:lookup(key, Dict1)),
    ?assertEqual('None', M:lookup(anotherkey, Dict1)),
    pd(M).

simple_record_test() ->
    [M] = compile_and_load(["test_files/simple_records.alp"], []),
    ?assertEqual({<<"sample">>, <<"person">>}, M:sample_person({})),
    pd(M).

polymorphic_record_test() ->
    [M] = compile_and_load(["test_files/polymorphic_record_test.alp"], []),
    ?assertEqual(<<"bar">>, M:with_y({})),
    ?assertEqual(<<"baz">>, M:with_y_and_throwaway_x({})),
    pd(M).

multiple_underscore_test() ->
    [M] = compile_and_load(["test_files/multiple_underscore_test.alp"], []),
    ?assertEqual(list, M:list_check({})),
    %% Compiler adds the __struct__ tag to distinguish between records
    %% and maps:
    Map = #{'__struct__' => 'map', x => 1, y => 2},
    ?assertEqual(<<"just two">>, M:map_check(Map)),
    ?assertEqual(<<"all three">>, M:map_check(Map#{z => 3})),
    ?assertEqual(<<"three">>, M:tuple_check({1, 2, 3})),
    pd(M).

circle_module_test() ->
    [M] = compile_and_load(["test_files/circles.alp"], []),
    ?assertEqual(12.56636, M:area(M:new(2))),
    pd(M).

records_with_x_module_test() ->
    [M] = compile_and_load(["test_files/records_with_x.alp"], []),
    ?assertEqual(2, M:get_x(M:make_xyz(2, 3, 4))),
    ?assertEqual(5, M:get_x(M:make_xy(5, 6))),
    pd(M).

%% A pattern match that matches records and maps with the same key should
%% correctly distinguish between maps and records that are compiled as
%% maps.
record_vs_map_match_order_test() ->
    [M] = compile_and_load(["test_files/record_map_match_order.alp"], []),
    ?assertEqual(1, M:check_map({})),
    ?assertEqual(2, M:check_record({})),
    pd(M).

raise_errors_test() ->
    [M] = compile_and_load(["test_files/error_tests.alp"], []),
    ?assertException(throw, <<"this should be a throw">>, M:raise_throw({})),
    ?assertException(exit, <<"exit here">>, M:raise_exit({})),
    ?assertException(error, <<"and an error">>, M:raise_error({})),

    ?assertException(throw, <<"oh no zero!">>, M:throw_or_int(0)),
    ?assertEqual(4, M:throw_or_int(2)),
    pd(M).

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

    pd(M).

radius_test() ->
    [M1, M2] = compile_and_load(
            ["test_files/radius.alp",
             "test_files/use_radius.alp"],
            []),
    ?assertEqual(1, M1:test_radius({})),
    pd(M1),
    pd(M2).

allow_duplicate_definition_with_different_arity_test() ->
    [M] = compile_and_load(["test_files/same_name_diff_arity.alp"], []),
    ?assertEqual([0, 1, 2, 3], M:seq(3)),
    pd(M).

apply_to_expressions_test() ->
    [M] = compile_and_load(["test_files/apply_to_expression.alp"], []),
    ?assertEqual(4, M:foo({})),
    ?assertEqual(6, M:uses_fun(3)),
    pd(M).

batch_export_test() ->
    [M] = compile_and_load(["test_files/batch_export.alp"], []),
    ?assertEqual(1, M:foo(1)),
    ?assertEqual(5, M:foo(2, 3)),
    ?assertEqual(8, M:mult(2, 4)),
    pd(M).

%% There seems to be a compilation bug in the early formatter work I'm trying
%% using Alpaca to write its own code formatter.  Figured I might as well just
%% add the test here.
own_formatter_test() ->
    Files = ["test_files/alpaca_native_ast.alp", "test_files/alpaca_format.alp"],
    [M1, M2] = compile_and_load(Files, []),
    pd(M1),
    pd(M2).

export_import_test() ->
    Files = ["test_files/export_all_arities.alp", "test_files/import_test.alp"],
    [M1, M2] = compile_and_load(Files, []),
    ?assertEqual(12, M1:test_pipe({})),
    ?assertEqual(12, M1:test_pipe_far_call({})),
    ?assertEqual(5, M1:test_specified_arity({})),
    pd(M1),
    pd(M2).

function_in_adt_test() ->
    [M] = compile_and_load(["test_files/dictionary.alp"], []),
    ?assertEqual(true, M:test_int_dict({})),
    pd(M).

curry_test() ->
    [M] = compile_and_load(["test_files/curry.alp"], []),
    ?assertEqual({16,26,[2]}, M:foo({})),
    LocalFun = M:local({}),
    ?assertEqual(100, LocalFun(90)),
    pd(M).

curry_import_export_test() ->
    Files = ["test_files/curry.alp", "test_files/curry_import.alp"],
    [M1, M2] = compile_and_load(Files, []),
    ?assertEqual([3], M1:run_filter({})),
    pd(M1),
    pd(M2).

throw_with_variables_test() ->
    Files = ["test_files/asserts.alp"],
    [M] = compile_and_load(Files, []),
    ?assertEqual(true, M:assert_equal(2, 2)),
    ?assertThrow({not_equal, 1, 2}, M:assert_equal(1, 2)),
    pd(M).

record_update_test() ->
    Files = ["test_files/update_record.alp",
             "test_files/use_update_record.alp"],
    [M1, M2] = compile_and_load(Files, []),

    ?assertEqual(#{'__struct__' => record, x => 5, b => 2}, M1:main({})),
    ?assertEqual(#{'__struct__' => record, x => 2}, M1:overwrite_x({})),
    ?assertEqual(#{'__struct__' => record,
                   a => 1,
                   b => 2,
                   c => 3}, M1:add_2_members({})),
    ?assertEqual(#{'__struct__' => record,
                   a => 1,
                   b => 2,
                   c => 3,
                   x => 1.0,
                   z => <<"this is z">>}, M1:add_3_members({})),
    pd(M1),
    pd(M2).

option_map_test() ->
    %% Including asserts now to check a bug found when experimenting for the
    %% beginning of alpaca_lib:
    Files = ["test_files/option_example.alp", "test_files/asserts.alp"],
    [_, M] = compile_and_load(Files, [test]),
    ?assertEqual({'Some', 1}, M:some(1)),
    ?assertEqual({'Some', 2}, M:map(fun(X) -> X + 1 end, M:some(1))),
    ?assertEqual('None', M:map(fun(X) -> X + 1 end, 'None')),
    pd(M).

lambdas_test() ->
    Files = ["test_files/lambda_examples.alp"],
    [M] = compile_and_load(Files, []),
    ?assertEqual([2, 3, 4], M:map_lambda({})),
    ?assertEqual(3, M:no_sugar_internal_binding({})),
    ?assertEqual(2, M:no_sugar_top_binding(1)),
    ?assertEqual({'T', [2, 3, 4]}, M:map_to_make_t([1, 2, 3])),
    ?assertEqual([2, 3, 4], M:nested_fun({})),
    ?assertEqual(4, M:use_lambda(3)),
    ?assertEqual([zero, not_zero, zero, not_zero],
                 M:use_literal_fun_with_patterns({})),
    ?assertEqual([int, not_int, int, not_int],
                 M:literal_fun_and_guards({})),
    ?assertEqual(4, M:fun_in_record({})),
    ?assertEqual(3, M:fun_in_record_in_record({})),
    pd(M).

%% Tests that we can use both leading `|` for every clause or treat it strictly
%% as "or" when defining clauses.
clause_style_test() ->
    Files = ["test_files/different_clause_styles.alp"],
    [M] = compile_and_load(Files, []),
    ?assertEqual(zero, M:leading_pipe(0)),
    ?assertEqual(not_zero, M:leading_pipe(42)),
    ?assertEqual(not_zero, M:or_pipe(1)),
    ?assertEqual(zero, M:or_pipe(0)),
    pd(M).

%% Check that we can use the receiver and rec types directly in an ADT.
receiver_type_test() ->
    Files = ["test_files/receiver_type.alp"],
    [M] = compile_and_load(Files, []),
    pd(M).

failing_test_test() ->
    Files = ["test_files/failing_test.alp"],
    [M] = compile_and_load(Files, [test]),
    ?assertMatch(error, M:test()),
    pd(M).

forward_symbol_reference_test() ->
    Files = ["test_files/forward_symbol_reference.alp"],
    [M] = compile_and_load(Files, [test]),
    ?assertMatch(15, M:hof_fail({})),
    ?assertMatch(15, M:val_fail({})),
    pd(M).

lambda_in_test_test() ->
    Files = ["test_files/lambda_in_test.alp"],
    [M] = compile_and_load(Files, [test]),
    ?assertMatch(2, M:lambda_test()),
    pd(M).

tests_in_imports_test() ->
    Files = ["test_files/asserts.alp", "test_files/tests_and_imports.alp"],
    [M1, M2] = compile_and_load(Files, [test]),
    ?assertMatch(true, M1:example_test()),
    pd(M1),
    pd(M2).

type_information_stored_test() ->
    Code =
        "module typeinfo\n\n"
        "export add\n\n"
        "let add x y = x + y\n",
    {ok, Compiled} = alpaca:compile({text, Code}),
    [#compiled_module{name=N, filename=FN, bytes=Bin}] = Compiled,
    {module, _N} = code:load_binary(N, FN, Bin),

    TypeInfo = proplists:get_value(alpaca_typeinfo, N:module_info(attributes)),

    [#alpaca_binding{bound_expr=F, type=T}] = TypeInfo#alpaca_module.functions,

    %% We should have type information but the bodies should be stripped
    ?assertMatch({t_arrow, [t_int, t_int], t_int}, T),
    ?assertMatch(#alpaca_fun{versions=[]}, F).

compiling_from_beam_test() ->
    %% Compile the initial beam file
    Files = ["test_files/asserts.alp"],
    {ok, [Compiled]} = alpaca:compile({files, Files}),
    {compiled_module, _ModuleName, FileName, BeamBinary} = Compiled,
    FP = filename:join("_build", FileName),
    file:write_file(FP, BeamBinary),
    Files2 = [FP, "test_files/tests_and_imports.alp"],
    %% Only one new module should be compiled
    [M] = compile_and_load(Files2, [test]),
    pd(M).

retrieve_hash_test() ->
    %% Compile and write out .beam file
    FN = "test_files/asserts.alp",
    Files = [FN],
    {ok, [Compiled]} = alpaca:compile({files, Files}),
    {compiled_module, _ModuleName, FileName, BeamBinary} = Compiled,
    FP = filename:join("_build", FileName),
    file:write_file(FP, BeamBinary),

    %% Read in source
    {ok, Device} = file:open(FN, [read, {encoding, utf8}]),
    R = read_file(Device, []),
    ok = file:close(Device),

    %% Retrieve hash from generated .beam file
    BeamHash = retrieve_hash(FP),

    %% If the source matches exactly what was compiled on the same version of
    %% Alpaca, the hashes should be the same
    ?assertEqual(hash_source(R), BeamHash),
    ?assertNotEqual(hash_source(R ++ "dirty"), BeamHash).

hash_annotation_test() ->
    F = "test_files/asserts.alp",
    {ok, Device} = file:open(F, [read, {encoding, utf8}]),
    R = read_file(Device, []),
    ok = file:close(Device),
    Version = proplists:get_value(version, alpaca:compiler_info()),
    Hash = crypto:hash(md5, R ++ Version),

    {ok, [Compiled]} = alpaca:compile({files, [F]}),
    {compiled_module, N, FN, Bin} = Compiled,
    {module, N} = code:load_binary(N, FN, Bin),
    ?assertEqual(Hash, proplists:get_value(alpaca_hash, N:module_info(attributes))),
    ?assertEqual(Hash, hash_source(R)),
    pd(N).

default_imports_test() ->
    Files = ["test_files/default.alp", "test_files/use_default.alp"],

    DefaultImports = {
        [{default, <<"identity">>}, {default, <<"always">>, 2}],
        [{default, <<"box">>}]},

    {ok, [Compiled, Default]} = alpaca:compile(
        {files, Files},
        [{default_imports, DefaultImports}]),

    {compiled_module, N, FN, Bin} = Compiled,
    {compiled_module, N2, FN2, Bin2} = Default,
    {module, N} = code:load_binary(N, FN, Bin),
    code:load_binary(N2, FN2, Bin2),

    ?assertEqual({'Box', 42}, N:main({})),
    pd(N).

built_in_adt_exhaustiveness_test() ->
    Files = ["test_files/exhaustiveness_cases.alp"],
    [M1] = compile_and_load(Files, [test]),
    ?assertMatch(
       #{'__struct__' := record,
         arity := 'None',
         line := 1,
         name := <<"make_export">>},
       M1:make_export(1, <<"make_export">>)),
    pd(M1).

type_signature_test() ->
    Files = ["test_files/basic_type_signature.alp"],
    [M] = compile_and_load(Files, [test]),
    ?assertMatch(4, M:add(1, 3)).

use_lambda_test() ->
    Files = ["test_files/use_lambda.alp"],
    [M] = compile_and_load(Files, [test]),
    ?assertMatch(15, M:useLambda(5)),
    ?assertMatch(13, M:useLambdaTuple(3)),
    MatchFun = M:matchLambda(true),
    Res = MatchFun(16),
    ?assertMatch(256, Res),
    FFIFun = M:ffiLambda("alpaca"),
    ?assertMatch(64, FFIFun(8)),
    pd(M).

list_item_expression_test() ->
    Files = ["test_files/list_items.alp"],
    [M] = compile_and_load(Files, [test]),
    ?assertMatch([4, 17], M:getList({})),

    Matrix = [[0, 0, 0, 0],
              [0, 1, 0, 0],
              [0, 0, 1, 0],
              [0, 0, 0, 1]],
    ?assertMatch(Matrix, M:getMatrix({})),
    pd(M).

destructuring_test() ->
    Files = ["test_files/destructuring.alp"],
    [M] = compile_and_load(Files, [test]),
    ?assertMatch(11, M:test_it({})),
    ?assertMatch(6, M:g({3, 3})),
    ?assertMatch(12, M:add_first_2_in_list([7, 5, 54, 32, not_an_int])),
    ?assertError(if_clause, M:fail_on_tuple_without_1({2, "twelve"})),
    ?assertMatch(<<"got 1!">>, M:fail_on_tuple_without_1({1, 1})),
    pd(M).

-endif.
