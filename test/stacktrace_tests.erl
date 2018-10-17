%%% -*- mode: erlang;erlang-indent-level: 4;indent-tabs-mode: nil -*-
%%% ex: ft=erlang ts=4 sw=4 et
%%% Copyright 2018 Jeremy Pierre
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

%% Some basic tests to check that source (line and file) annotations show up in
%% stack traces.  Far from exhaustive, just the beginning of making sure we can
%% get decent runtime feedback on failures.
-module(stacktrace_tests).
-include_lib("eunit/include/eunit.hrl").

simple_badarith_test() ->
    Mod =
	"module arith_err \n"
	"export main/1 \n"
	"let main () = 1 + :a",
    {error, error, badarith, Trace} =
	run_for_trace(
	  [{"arith_err.alp", alpaca_arith_err, Mod}],
	  fun() -> alpaca_arith_err:main({}) end),
    Expected = {alpaca_arith_err, main, 1, [{file, "arith_err.alp"}, {line, 3}]},
    ?assertMatch([Expected | _], Trace).

indirect_badarith_test() ->
    Mod =
	"module indirect_arith \n"
	"export foo/1 \n"
	"let bar x = x + 1 \n"
	"let foo () = bar :a",
    {error, error, badarith, Trace} =
	run_for_trace(
	  [{"indirect_arith.alp", alpaca_indirect_arith, Mod}],
	  fun() -> alpaca_indirect_arith:foo({}) end),
    Expected1 = {alpaca_indirect_arith, bar, 1, [{file, "indirect_arith.alp"}, {line, 3}]},
    ?assertMatch([Expected1 | _], Trace).

fun_pattern_test() ->
    Mod =
	"module fun_pattern \n"
	"export f/1 \n"
	"let f 0 = :zero \n"
	"let f 1 = :one \n",
    {error, error, if_clause, Trace} =
	run_for_trace(
	  [{"fun_pattern.alp", alpaca_fun_pattern, Mod}],
	  fun() -> alpaca_fun_pattern:f(2) end),
    %% After adding a catch-all match case we would expect these annotations:
    %%   [{file, "fun_pattern.alp"}, {line, 3}]
    Expected = {alpaca_fun_pattern, f, 1, []},
    ?assertMatch([Expected | _], Trace).

throw_test() ->
    Mod =
	"module t \n"
	"export f/1 \n"
	"let f () = throw :wat",
    {error, throw, wat, Trace} = run_for_trace(
				   [{"t.alp", alpaca_t, Mod}],
				   fun() -> alpaca_t:f({}) end),
    ?assertMatch([{alpaca_t, f, 1, [{file, "t.alp"}, {line, 3}]} | _], Trace).

multi_module_test() ->
    Mod1 =
	"module a \n"
	"export f/1 \n"
	"let f x = x + 1",
    Mod2 =
	"module b \n"
	"export g/1 \n"
	"let g x = a.f x",
    {error, error, badarith, Trace} = run_for_trace(
				   [{"a.alp", alpaca_a, Mod1}, {"b.alp", alpaca_b, Mod2}],
				   fun() -> alpaca_b:g(an_atom) end),
    %% Somewhat surprising, I thought I might get the full trace through module
    %% b as well.
    ?assertMatch([{alpaca_a, f, 1, [{file, "a.alp"}, {line, 3}]} | _], Trace).

undef_test() ->
    Mod1 =
	"module m \n"
	"export f/1 \n"
	"let f () = n.g 1",
    Mod2 =
	"module n \n"
	"export foo/1 \n"
	"let foo () = :foo",

    {error, error, undef, Trace} = run_for_trace(
				     [{"m.alp", alpaca_m, Mod1}, {"n.alp", alpaca_n, Mod2}],
				     fun() -> alpaca_m:f({}) end),
    %% Interesting that we don't seem to get call site details even though the
    %% call itself is annotated:
    ?assertMatch([{alpaca_n, g, [1], []} | _], Trace).

%% A wrapper that compiles the provided code for one or more modules and
%% executes the provided operation.  Captures any resulting stack trace so that
%% the caller can check correctness.
run_for_trace(ModulesWithFilenames, Expr) ->
    Compile = fun({FN, ModName, ModCode}) ->
		      {ok, Name, Bin} = parse_and_gen(ModCode, FN),
		      {module, Name} = code:load_binary(ModName, FN, Bin),
		      {Name, Bin}
	      end,
    Ms = lists:map(Compile, ModulesWithFilenames),
    Ret = try Expr() of
	      Res -> {ok, Res}
	  catch Type:Detail ->
		  Trace = erlang:get_stacktrace(),
		  {error, Type, Detail, Trace}
	  end,
    [pd(M) || {M, _} <- Ms],
    Ret.

%% Note that this skips the type checker!
parse_and_gen(Code, FN) ->
    {ok, [Mod]} = alpaca_ast_gen:make_modules([{FN, Code}]),
    {ok, Forms} = alpaca_codegen:gen(Mod, []),
    compile:forms(Forms, [report, verbose, from_core]).

%% Purge and delete the given module from the VM.
pd(Module) ->
    code:purge(Module),
    code:delete(Module).

