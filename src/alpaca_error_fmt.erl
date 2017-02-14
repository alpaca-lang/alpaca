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
-module(alpaca_error_fmt).

-export([fmt/2]).

-define(EN_US, "en-US").

fmt({error, {parse_error, F, L, E}}, Locale) ->
    [F, $:, integer_to_list(L), ": ", fmt_parse_error(E, Locale), $\n];
fmt({error, _}=Err, Locale) ->
    fmt_unknown_error(Err, Locale).

fmt_parse_error({duplicate_definition, Id}, ?EN_US) ->
    ["Duplicate definitation of \"", Id, "\""];
fmt_parse_error({duplicate_type, Id}, ?EN_US) ->
    ["Duplicate definitation of type \"", Id, "\"."];
fmt_parse_error({function_not_exported, Mod, Name}, ?EN_US) ->
    ["No function \"", Name, "\" exported from module \"",
     atom_to_list(Mod), "\"."];
fmt_parse_error({invalid_bin_qualifier, Str}, ?EN_US) ->
    ["Invalid binary qualifier \"", Str, "\".\n",
     "Valid qualifiers are \"end\", \"sign\", \"size\", \"type\" and \"unit\"."];
fmt_parse_error({invalid_bin_type, Str}, ?EN_US) ->
    ["Invalid binary part type \"", Str, "\".\n",
     "Valid types are \"binary\", \"float\", \"int\", and \"utf8\"."];
fmt_parse_error({invalid_endianess, Str}, ?EN_US) ->
    ["Invalid endianess \"", Str, "\". ",
     "Did you mean \"big\", \"little\", or \"native\"?"];
fmt_parse_error({invalid_fun_parameter, _}, ?EN_US) ->
    ["Invalid pattern for function argument."];
fmt_parse_error({invalid_top_level_construct, _}, ?EN_US) ->
    ["Invalid top level construct."];
fmt_parse_error({module_rename, Old, New}, ?EN_US) ->
    io_lib:format("Redefintion of module name from \"~p\" to \"~p\".",
                  [Old, New]);
fmt_parse_error(no_module, ?EN_US) ->
    ["No module name defined.\n",
     "You may define it like this: \"module foo\""];
fmt_parse_error({no_module, Mod}, ?EN_US) ->
    io_lib:format("Cannot find module \"~p\".", [Mod]);
fmt_parse_error({syntax_error, ""}, ?EN_US) ->
    ["Incomplete expression."];
fmt_parse_error({syntax_error, Token}, ?EN_US) ->
    ["Unexpected token ", Token, $.];
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
fmt_parse_error(Unknown, ?EN_US=Locale) ->
    fmt_unknown_error(Unknown, Locale);
fmt_parse_error(Unknown, Locale) ->
    [locale_fallback_msg(Locale), fmt_parse_error(Unknown, ?EN_US)].

simple_type_arity_error(LiteralType, ?EN_US) ->
    io_lib:format("Type parameter provided for builtin type ~p, "
                  "but none was expected.", [LiteralType]);
simple_type_arity_error(LiteralType, Locale) ->
    [locale_fallback_msg(Locale), simple_type_arity_error(LiteralType, ?EN_US)].

poly_type_arity_error(LiteralType, ExpectedArity, ActualArity, ?EN_US) ->
    io_lib:format("Wrong number of type parameters provided for "
                  "builtin type ~p.~nExpected ~p, but got ~p.",
                  [LiteralType, ExpectedArity, ActualArity]);
poly_type_arity_error(LiteralType, ExpectedArity, ActualArity, Locale) ->
    [locale_fallback_msg(Locale),
     poly_type_arity_error(LiteralType, ExpectedArity, ActualArity, ?EN_US)].

fmt_unknown_error(Err, ?EN_US) ->
    ["Sorry, we do not have a proper message for this error yet.",
     $\n, "Please consider filing an issue at ",
     "https://www.github.com/alpaca-lang/alpaca.",
     $\n, io_lib:format("~p", [Err]), $\n];
fmt_unknown_error(Err, Locale) ->
    [locale_fallback_msg(Locale), fmt_unknown_error(Err, ?EN_US)].

locale_fallback_msg(Locale) ->
    ["Error messages are not available in your locale (", Locale, ").",
     "Falling back to ", ?EN_US, $\., $\n].
