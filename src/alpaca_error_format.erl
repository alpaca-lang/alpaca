%% -*- coding: utf-8 -*-
%%% Licensed under the Apache License, Version 2.0 (the "License");
%%% you may not use this file except in compliance with the License.
%%% You may obtain a copy of the License at
%%%
%%%     http://www.apache.org/licenses/LICENSE-2.0
%%%
% Unless required by applicable law or agreed to in writing, software
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

%% This function expects all strings passed in to it as part of error messages
%% (e.g. function names) to be valid unicode strings.
-spec fmt({error, term()}, Locale::string()) -> binary().
fmt({error, {parse_error, F, Line, E}}, Locale) ->
    File = unicode:characters_to_binary(F, utf8),
    {Msg, H} = case fmt_parse_error(E, Locale) of
                   {MsgC, HC} ->
                       {MsgC, HC};
                   MsgC ->
                       {MsgC, ""}
               end,
    SourceDir = filename:dirname(File),
    Module = filename:rootname(filename:basename(File)),
    FileLine = case File of
                   <<"<no file>">> ->
                       cf:format("~!_c~s~!!:~!c~p~!!", [File, Line]);
                   _ ->
                       cf:format("~!__~s/~!_c~s.alp~!!:~!c~p~!!",
                                 [SourceDir, Module, Line])
               end,
    Err = case get_context(SourceDir, Module, Line, hl_fn(H)) of
              "" ->
                  cf:format("~s~n  ~s~n",
                            [FileLine, Msg]);
              Ctx ->
                  cf:format("~s~n  ~s~n~n"
                            "~s~n", [FileLine, Msg, Ctx])
          end,
    unicode:characters_to_binary(Err, utf8);
fmt({error, Err}, Locale) ->
    Msg = fmt_parse_error(Err, Locale),
    <<Msg/binary, "\n"/utf8>>.

fmt_parse_error({duplicate_definition, Id}, Locale) ->
    t(__(<<"duplicate_definition %(id)">>), Locale, [{id, Id}]);
fmt_parse_error({duplicate_type, Id}, Locale) ->
    t(__(<<"duplicate_type_definition %(id)">>), Locale, [{id, Id}]);
fmt_parse_error({function_not_exported, Mod, Name}, Locale) ->
    t(__(<<"function_not_exported %(mod) %(name)">>), Locale,
      [{'fun', Name}, {mod, atom_to_binary(Mod, utf8)}]);
fmt_parse_error({invalid_bin_qualifier, Str}, Locale) ->
    t(__(<<"invalid_bin_qualifier %(qualifier)">>), Locale, [{qualifier, Str}]);
fmt_parse_error({invalid_bin_type, Str}, Locale) ->
    t(__(<<"invalid_bin_type %(type)">>), Locale, [{type, Str}]);
fmt_parse_error({invalid_endianness, Str}, Locale) ->
    t(__(<<"invalid_endianness %(endianness)">>), Locale, [{endianness, Str}]);
fmt_parse_error({invalid_fun_parameter, _}, Locale) ->
    t(__(<<"invalid_fun_parameter">>), Locale);
fmt_parse_error({invalid_top_level_construct, _}, Locale) ->
    t(__(<<"invalid_top_level_construct">>), Locale);
fmt_parse_error({module_rename, Old, New}, Locale) ->
    t(__(<<"module_rename %(old) %(new).">>), Locale,
      [{old, atom_to_binary(Old, utf8)}, {new, atom_to_binary(New, utf8)}]);
fmt_parse_error(no_module, Locale) ->
    t(__(<<"no_module">>), Locale);
fmt_parse_error({no_module, Mod}, Locale) when is_atom(Mod) ->
    t(__(<<"no_module %(mod)">>), Locale, [{mod, atom_to_binary(Mod, utf8)}]);
fmt_parse_error({no_module, Mod}, Locale) ->
    t(__(<<"no_module %(mod)">>), Locale, [{mod, Mod}]);
fmt_parse_error({syntax_error, ""}, Locale) ->
    t(__(<<"incomplete_expression">>), Locale);
fmt_parse_error({syntax_error, Token}, Locale) ->
    t(__(<<"unexpected_token %(token)">>), Locale, [{token, Token}]);
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
    fmt_unknown_error(Unknown, Locale).

simple_type_arity_error(LiteralType, Locale) ->
    t(__(<<"type_parameter_given_to_primitive_builtin_type %(type)">>), Locale,
      [{type, LiteralType}]).

poly_type_arity_error(LiteralType, ExpectedArity, ActualArity, Locale) ->
    t(__(<<"builtin_type_arity_error %(num_expected) %(num_supplied)">>),
      Locale,
      [{type, LiteralType},
       {num_expected, integer_to_binary(ExpectedArity)},
       {num_supplied, integer_to_binary(ActualArity)}]).

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
    re:replace(Str, FromStr, To, [global, unicode, {return, binary}])
  end, TranslatedStr, Replacements).


get_context(SourceDir, Module, Target, Fn) ->
    case file:open(io_lib:format("~s/~s.alp", [SourceDir, Module]),
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
                         cf:format("~!r~4b~!!: ~s", [Line, Fn(Txt)]);
                      _ ->
                         cf:format("~!c~4b~!!: ~s", [Line, Txt])
                  end,
            read_lines(Device, Line + 1, Target, Fn, [L1 | Acc])
    end.



%% Helper function to generate a 'highlighter' to display syntax errors
%% in line.
hl_fn("") ->
    fun(X) ->
            X
    end;
hl_fn(O) ->
    P = re:replace(O, "[.^$*+?()[{\\\|\s#]", "\\\\&", [global]),
    R = list_to_binary(cf:format("~!r~s", [O])),
    fun(L) ->
            re:replace(L, ["(.*)", P, "(.*?)$"], ["\\1", R, "\\2"])
    end.

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

test_fmt(Error) ->
    CF = application:get_env(cf, colour_term),
    application:set_env(cf, colour_term, false),
    R = fmt(Error, "en_US"),
    application:set_env(cf, colour_term, CF),
    R.
fmt_unknown_parse_error_test() ->
  File = "/tmp/file.alp",
  Line = 10,
  ParseError = unknown,
  Error = {error, {parse_error, File, Line, ParseError}},
  Msg = test_fmt(Error),
  Expected = <<"/tmp/file.alp:10\n  unknown\n"
               "Sorry, we do not have a proper message for this error yet.\n"
               "Please consider filing an issue at "
               "https://www.github.com/alpaca-lang/alpaca/issues.\n">>,
  ?assertEqual(Expected, Msg).

fmt_unknown_error_test() ->
    application:set_env(cf, colour_term, false),
  Error = {error, unknown},
  Msg = test_fmt(Error),
  Expected = <<"unknown\n"
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
  Expected = <<"/tmp/file.alp:10\n  Syntax error before \"blah\".\n">>,
  ?assertEqual(Expected, Msg).

real_error_test() ->
  Source = "let add a b = a + b",
  Error = {error, _}  = alpaca:compile({text, Source}),
  Msg = test_fmt(Error),
  Expected = <<"<no file>:1\n  No module name defined.\n"
               "You may define it like this: \"module foo\".\n">>,
  ?assertEqual(Expected, Msg).

-endif.
