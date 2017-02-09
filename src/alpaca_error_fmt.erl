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

fmt_parse_error(Unknown, ?EN_US=Locale) ->
    fmt_unknown_error(Unknown, Locale);
fmt_parse_error(Unknown, Locale) ->
    [locale_fallback_msg(Locale), fmt_parse_error(Unknown, ?EN_US)].

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
