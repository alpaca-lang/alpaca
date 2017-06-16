%% -*- coding: utf-8 -*-
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

%% Formatting and translation of error messages.
-module(alpaca_error_format).

-export([fmt/2]).

-ignore_xref([ fmt/2 ]).

-compile({parse_transform, epo_gettext}).

%% number of lines to show before or after the errorrous line
-define(CTX_AREA, 2).
-define(RE_OPTS, [{return, binary}, unicode, ucp]).

%% This function expects all strings passed in to it as part of error messages
%% (e.g. function names) to be valid unicode strings.
-spec fmt({error, term()}, Locale::string()) -> binary().
fmt({error, {parse_error, F, Line, E}}, Locale) ->
    File = unicode:characters_to_binary(F, utf8),
    {Msg, HlFn} = case fmt_parse_error(E, Locale) of
                      {MsgC, HlFnC} ->
                          {MsgC, HlFnC};
                      MsgC ->
                          {MsgC, hl_fn("")}
                  end,
    MsgI = ident(Msg),
    SourceDir = filename:dirname(File),
    Module = filename:rootname(filename:basename(File)),
    FileLine = case File of
                   <<"<no file>">> ->
                       cf("~!_c~ts~!!:~!c~p~!!", [File, Line]);
                   _ ->
                       cf("~!__~ts/~!_c~ts~!!~!__.alp~!!:~!c~p~!!",
                          [SourceDir, Module, Line])
               end,
    case get_context(SourceDir, Module, Line, HlFn) of
        "" ->
            cf("~ts~n~ts~n", [FileLine, MsgI]);
        Ctx ->
            cf("~ts~n~ts~n~n~ts~n", [FileLine, MsgI, Ctx])
    end;

fmt({error, Err}, Locale) ->
    Msg = fmt_parse_error(Err, Locale),
    <<Msg/binary, "\n"/utf8>>.

ident(S) ->
    re:replace(S, "^", "  ", [multiline, global | ?RE_OPTS]).

fmt_parse_error({duplicate_definition, Id}, Locale) ->
    t(__(<<"duplicate_definition %(id)">>), Locale, [{id, red(Id)}]);
fmt_parse_error({duplicate_type, Id}, Locale) ->
    t(__(<<"duplicate_type_definition %(id)">>), Locale, [{id, red(Id)}]);
fmt_parse_error({function_not_exported, Mod, Name}, Locale) ->
    t(__(<<"function_not_exported %(mod) %(fun)">>), Locale,
      [{'fun', red(Name)}, {mod, bold(atom_to_binary(Mod, utf8))}]);
fmt_parse_error({invalid_bin_qualifier, Str}, Locale) ->
    t(__(<<"invalid_bin_qualifier %(qualifier)">>), Locale,
      [{qualifier, red(Str)}]);
fmt_parse_error({invalid_bin_type, Str}, Locale) ->
    t(__(<<"invalid_bin_type %(type)">>), Locale,
      [{type, red(Str)}]);
fmt_parse_error({invalid_endianness, Str}, Locale) ->
    t(__(<<"invalid_endianness %(endianness)">>), Locale,
      [{endianness, red(Str)}]);
fmt_parse_error({invalid_fun_parameter, _}, Locale) ->
    t(__(<<"invalid_fun_parameter">>), Locale);
fmt_parse_error({invalid_top_level_construct, _}, Locale) ->
    t(__(<<"invalid_top_level_construct">>), Locale);
fmt_parse_error({module_rename, Old, New}, Locale) ->
    t(__(<<"module_rename %(old) %(new).">>), Locale,
      [{old, green(atom_to_binary(Old, utf8))},
       {new, red(atom_to_binary(New, utf8))}]);
fmt_parse_error(no_module, Locale) ->
    t(__(<<"no_module">>), Locale);
fmt_parse_error({no_module, Mod}, Locale) when is_atom(Mod) ->
    fmt_parse_error({no_module, atom_to_binary(Mod, utf8)}, Locale);
fmt_parse_error({no_module, Mod}, Locale) ->
    t(__(<<"no_module %(mod)">>), Locale, [{mod, red(Mod)}]);
fmt_parse_error({syntax_error, ""}, Locale) ->
    t(__(<<"incomplete_expression">>), Locale);
fmt_parse_error({syntax_error, Token}, Locale) ->
    {t(__(<<"unexpected_token %(token)">>), Locale,
       [{token, red(Token)}]), hl_fn(Token)};
fmt_parse_error({wrong_type_arity, t_atom, _A}, Locale) ->
    simple_type_arity_error("atom", Locale);
fmt_parse_error({wrong_type_arity, t_binary, _A}, Locale) ->
    simple_type_arity_error("binary", Locale);
fmt_parse_error({wrong_type_arity, t_bool, _A}, Locale) ->
    simple_type_arity_error("bool", Locale);
fmt_parse_error({wrong_type_arity, t_float, _A}, Locale) ->
    simple_type_arity_error("float", Locale);
fmt_parse_error({wrong_type_arity, t_int, _A}, Locale) ->
    simple_type_arity_error("int", Locale);
fmt_parse_error({wrong_type_arity, t_list, A}, Locale) ->
    poly_type_arity_error("list", 1, A, Locale);
fmt_parse_error({wrong_type_arity, t_map, A}, Locale) ->
    poly_type_arity_error("map", 2, A, Locale);
fmt_parse_error({wrong_type_arity, t_pid, A}, Locale) ->
    poly_type_arity_error("pid", 1, A, Locale);
fmt_parse_error({wrong_type_arity, t_string, _A}, Locale) ->
    simple_type_arity_error("string", Locale);
fmt_parse_error(Unknown, Locale) ->
    E = fmt_unknown_error(Unknown, Locale),
    <<"(╯°□°）╯︵ ┻━┻ "/utf8, E/binary>>.

simple_type_arity_error(LiteralType, Locale) ->
    t(__(<<"type_parameter_given_to_primitive_builtin_type %(type)">>), Locale,
      [{type, red(LiteralType)}]).

poly_type_arity_error(LiteralType, ExpectedArity, ActualArity, Locale) ->
    t(__(<<"builtin_type_arity_error %(type) %(num_expected) %(num_supplied)">>),
      Locale,
      [{type, bold(LiteralType)},
       {num_expected, green(integer_to_binary(ExpectedArity))},
       {num_supplied, red(integer_to_binary(ActualArity))}]).

fmt_unknown_error(Err, Locale) ->
    t(__(<<"unknown_error %(raw_error_term)">>), Locale,
      [{raw_error_term, io_lib:format("~tp", [Err])}]).

t(MsgId, Locale) ->
    t(MsgId, Locale, []).

t(MsgId, Locale, Replacements) ->
    Translated = case epo_gettext:gettext(alpaca_compiled_po, MsgId, Locale) of
                     MsgId -> epo_gettext:gettext(alpaca_compiled_po, MsgId, "en_US");
                     Translation -> Translation
                 end,
    replace(Translated, Replacements).

replace(TranslatedStr, Replacements) ->
    lists:foldl(fun({FromAtom, To}, Str) ->
                        FromStr = "%\\(" ++ atom_to_list(FromAtom) ++ "\\)",
                        re:replace(Str, FromStr, To, [global | ?RE_OPTS])
                end, TranslatedStr, Replacements).


get_context(SourceDir, Module, Target, Fn) ->
    case file:open(io_lib:format("~ts/~ts.alp", [SourceDir, Module]),
                   [read, binary]) of
        {ok, Device} ->
            read_lines(Device, 1, Target, Fn, []);
        _E ->
            ""
    end.

read_lines(Device, Line, Target, Fn, Acc)
  when Line < Target - ?CTX_AREA ->
    case io:get_line(Device, "") of
        eof ->
            file:close(Device),
            lists:reverse(Acc);
        _Txt ->
            read_lines(Device, Line + 1, Target, Fn, Acc)
    end;
read_lines(Device, Line, Target, _Fn, Acc)
  when Line > Target + ?CTX_AREA ->
    file:close(Device),
    lists:reverse(Acc);

read_lines(Device, Line, Target, Fn, Acc) ->
    case io:get_line(Device, "") of
        eof ->
            file:close(Device),
            lists:reverse(Acc);
        Txt ->
            L1 = case Line of
                     Target ->
                         cf("  ~!r~4b~!!: ~ts", [Line, Fn(Txt)]);
                     _ ->
                         cf("  ~!c~4b~!!: ~ts", [Line, Txt])
                 end,
            read_lines(Device, Line + 1, Target, Fn, [L1 | Acc])
    end.

red(S) ->
    cf("~!r~ts", [S]).

green(S) ->
    cf("~!g~ts", [S]).

bold(S) ->
    cf("~!^~ts", [S]).

cf(Fmt, Args) ->
    unicode:characters_to_binary(cf:format(Fmt, Args), utf8).


%% Helper function to generate a 'highlighter' to display syntax errors
%% in line.
hl_fn("") ->
    fun(X) ->
            X
    end;
hl_fn(O) ->
    P = re:replace(O, "[.^$*+?()[{\\\|\s#]", "\\\\&", [global | ?RE_OPTS]),
    R = red(O),
    fun(L) ->
            re:replace(L, ["(.*)", P, "(.*?)$"], ["\\1", R, "\\2"], ?RE_OPTS)
    end.

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

test_fmt(Error) ->
    CF = application:get_env(cf, colour_term),
    application:set_env(cf, colour_term, false),
    R = fmt(Error, "en_US"),
    application:set_env(cf, colour_term, CF),
    R.

test_fmt_c(Error) ->
    CF = application:get_env(cf, colour_term),
    application:set_env(cf, colour_term, true),
    R = fmt(Error, "en_US"),
    application:set_env(cf, colour_term, CF),
    R.
fmt_unknown_parse_error_test() ->
    File = "/tmp/file.alp",
    Line = 10,
    ParseError = unknown,
    Error = {error, {parse_error, File, Line, ParseError}},
    Msg = test_fmt(Error),
    Expected = <<"/tmp/file.alp:10\n",
                 "  (╯°□°）╯︵ ┻━┻ "/utf8, "unknown\n"
                 "  Sorry, we do not have a proper message for this error yet.\n"
                 "  Please consider filing an issue at "
                 "https://www.github.com/alpaca-lang/alpaca/issues.\n">>,
    ?assertEqual(Expected, Msg).

fmt_unknown_error_test() ->
    application:set_env(cf, colour_term, false),
    Error = {error, unknown},
    Msg = test_fmt(Error),
    Expected = <<"(╯°□°）╯︵ ┻━┻ "/utf8, "unknown\n"
                 "Sorry, we do not have a proper message for this error yet.\n"
                 "Please consider filing an issue at "
                 "https://www.github.com/alpaca-lang/alpaca/issues.\n">>,
    ?assertEqual(Expected, Msg).

en_us_fallback_test() ->
    File = "/tmp/file.alp",
    Line = 10,
    ParseError = {syntax_error, "blah"},
    Error = {error, {parse_error, File, Line, ParseError}},
    Msg = test_fmt(Error),
    Expected = <<"/tmp/file.alp:10\n"
                 "  Syntax error before \"blah\".\n">>,
    ?assertEqual(Expected, Msg).

syntax_error_hl_test() ->
    File = "test/error.alp",
    Line = 11,
    ParseError = {syntax_error, "="},
    Error = {error, {parse_error, File, Line, ParseError}},
    Msg = test_fmt(Error),
    Expected = <<"test/error.alp:11\n"
                 "  Syntax error before \"=\".\n\n"
                 "     9: let format ast_node = format_ast 0 ast_node\n"
                 "    10: \n"
                 "    11: let max_len = = 80\n"
                 "    12: \n"
                 "    13: let format_ast depth Symbol {name=name} =\n\n">>,
    ?assertEqual(Expected, Msg).

syntax_error_hl_c_test() ->
    File = "test/error.alp",
    Line = 11,
    ParseError = {syntax_error, "="},
    Error = {error, {parse_error, File, Line, ParseError}},
    Msg = test_fmt_c(Error),
    Expected =
        <<"\e[4mtest/\e[0;36m\e[4merror\e[0m\e[4m.alp\e[0m:"
          "\e[0;36m11\e[0m\e[0m\n"
          "  Syntax error before \"\e[0;31m=\e[0m\".\n\n"
          "  \e[0;36m   9\e[0m: let format ast_node = format_ast 0 ast_node\n"
          "\e[0m  \e[0;36m  10\e[0m: \n"
          "\e[0m  \e[0;31m  11\e[0m: let max_len = \e[0;31m=\e[0m 80\n"
          "\e[0m  \e[0;36m  12\e[0m: \n"
          "\e[0m  \e[0;36m  13\e[0m: let format_ast depth Symbol "
          "{name=name} =\n\e[0m\n\e[0m">>,
    ?assertEqual(Expected, Msg).

en_us_syntax_color_test() ->
    File = "/tmp/file.alp",
    Line = 10,
    ParseError = {syntax_error, "blah"},
    Error = {error, {parse_error, File, Line, ParseError}},
    Msg = test_fmt_c(Error),
    Expected = <<"\e[4m/tmp/\e[0;36m\e[4mfile\e[0m\e[4m.alp\e[0m:"
                 "\e[0;36m10\e[0m\e[0m\n"
                 "  Syntax error before \"\e[0;31mblah\e[0m\".\n\e[0m">>,
    ?assertEqual(Expected, Msg).

function_not_exported_test() ->
    File = "/tmp/module.alp",
    Line = 10,
    ParseError = {function_not_exported, module, <<"fun">>},
    Error = {error, {parse_error, File, Line, ParseError}},
    Msg = test_fmt(Error),
    Expected = <<"/tmp/module.alp:10\n"
                 "  No function \"fun\" exported from module \"module\".\n">>,
    ?assertEqual(Expected, Msg).

function_not_exported_c_test() ->
    File = "/tmp/module.alp",
    Line = 10,
    ParseError = {function_not_exported, module, <<"fun">>},
    Error = {error, {parse_error, File, Line, ParseError}},
    Msg = test_fmt_c(Error),
    Expected = <<"\e[4m/tmp/\e[0;36m\e[4mmodule\e[0m\e[4m.alp\e[0m:"
                 "\e[0;36m10\e[0m\e[0m\n"
                 "  No function \"\e[0;31mfun\e[0m\" exported from module "
                 "\"\e[1mmodule\e[0m\".\n\e[0m">>,
    ?assertEqual(Expected, Msg).

buildin_type_arity_test() ->
    File = "/tmp/module.alp",
    Line = 10,
    ParseError = {wrong_type_arity, t_pid, 42},
    Error = {error, {parse_error, File, Line, ParseError}},
    Msg = test_fmt(Error),
    Expected = <<"/tmp/module.alp:10\n"
                 "  Wrong number of type parameters provided for builtin type ",
                 "\"pid\".\n"
                 "  Expected 1, but got 42.\n">>,
    ?assertEqual(Expected, Msg).

buildin_type_arity_c_test() ->
    File = "/tmp/module.alp",
    Line = 10,
    ParseError = {wrong_type_arity, t_pid, 42},
    Error = {error, {parse_error, File, Line, ParseError}},
    Msg = test_fmt_c(Error),
    Expected = <<"\e[4m/tmp/\e[0;36m\e[4mmodule\e[0m\e[4m.alp\e[0m:"
                 "\e[0;36m10\e[0m\e[0m\n"
                 "  Wrong number of type parameters provided for builtin type"
                 " \"\e[1mpid\e[0m\".\n"
                 "  Expected \e[0;32m1\e[0m, but got \e[0;31m42\e[0m.\n\e[0m">>,
    ?assertEqual(Expected, Msg).



real_error_test() ->
    Source = "let add a b = a + b",
    Error = {error, _}  = alpaca:compile({text, Source}),
    Msg = test_fmt(Error),
    Expected = <<"<no file>:1\n"
                 "  No module name defined.\n"
                 "  You may define it like this: \"module foo\".\n">>,
    ?assertEqual(Expected, Msg).

-endif.
