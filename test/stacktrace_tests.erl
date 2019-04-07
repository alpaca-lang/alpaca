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
-include("alpaca.hrl").

simple_badarith_test() ->
    Mod =
	"module arith_err \n"
	"export main/1 \n"
	"let main x = 1 + x",
    {error, error, badarith, Trace} =
	run_for_trace(
	  [{"arith_err.alp", Mod}],
	  fun() -> alpaca_arith_err:main(atom) end),
    Expected = {alpaca_arith_err, main, 1, [{file, "arith_err.alp"}, {line, 3}]},
    ?assertMatch([Expected | _], Trace).

indirect_badarith_test() ->
    Mod =
	"module indirect_arith \n"
	"export foo/1 \n"
	"let bar x = x + 1 \n"
	"let foo y = bar y",
    {error, error, badarith, Trace} =
	run_for_trace(
	  [{"indirect_arith.alp", Mod}],
	  fun() -> alpaca_indirect_arith:foo(atom_again) end),
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
	  [{"fun_pattern.alp", Mod}],
	  fun() -> alpaca_fun_pattern:f(2) end),
    %% Incorrect line number, see the following issue:
    %% https://github.com/alpaca-lang/alpaca/issues/263
    Expected = {alpaca_fun_pattern, f, 1, [{file, "fun_pattern.alp"}, {line, 4}]},
    ?assertMatch([Expected | _], Trace).

throw_test() ->
    Mod =
	"module t \n"
	"export f/1 \n"
	"let f () = throw :wat",
    {error, throw, wat, Trace} = run_for_trace(
				   [{"t.alp", Mod}],
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
				   [{"a.alp", Mod1}, {"b.alp", Mod2}],
				   fun() -> alpaca_b:g(an_atom) end),
    %% Somewhat surprising, I thought I might get the full trace through module
    %% b as well.
    ?assertMatch([{alpaca_a, f, 1, [{file, "a.alp"}, {line, 3}]} | _], Trace).

%% A wrapper that compiles the provided code for one or more modules and
%% executes the provided operation.  Captures any resulting stack trace so that
%% the caller can check correctness.
run_for_trace(ModulesWithFilenames, Expr) ->
    % Temporary, callers should change:
    ToCompile = [{FN, Code} || {FN, Code} <- ModulesWithFilenames],
    {ok, Compiled} = alpaca:compile({text_set, ToCompile}),
    Ms = lists:map(
           fun(#compiled_module{name=M, filename=F, bytes=B}) -> {M, F, B} end,
           Compiled
          ),
    [code:load_binary(M, F, B) || {M, F, B} <- Ms],

    Ret = try Expr() of
	      Res -> {ok, Res}
	  catch Type:Detail ->
		  Trace = erlang:get_stacktrace(),
		  {error, Type, Detail, Trace}
	  end,
    [pd(M) || {M, _, _} <- Ms],
    Ret.

%% Purge and delete the given module from the VM.
pd(Module) ->
    code:purge(Module),
    code:delete(Module).

