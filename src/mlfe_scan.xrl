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

Definitions.
D   = [0-9]
L   = [a-z]
U   = [A-Z]
SYM = {L}[a-zA-Z0-9_]*
ATOM = :[a-zA-Z0-9_\*]*
TYPE = {U}[a-zA-Z0-9_]*
WS  = [\s\n]
BRK = \n(\n)+
FLOAT_MATH = (\+\.)|(\-\.)|(\*\.)|(\/\.)
TYPE_CHECK = is_integer|is_float|is_atom|is_bool|is_list|is_string|is_chars|is_pid|is_binary

BASE_TYPE = atom|int|float|string|bool|binary
BASE_LIST = list
BASE_MAP = map
BASE_PID = pid

Rules.
%% Separators
,     : {token, {',', TokenLine}}.
/     : {token, {'/', TokenLine}}.

\(    : {token, {'(', TokenLine}}.
\)    : {token, {')', TokenLine}}.
\|    : {token, {'|', TokenLine}}.
\:\:  : {token, {cons_infix, TokenLine}}.
\:    : {token, {':', TokenLine}}.
\[    : {token, {'[', TokenLine}}.
\]    : {token, {']', TokenLine}}.
()    : {token, {unit, TokenLine}}.
#{    : {token, {map_open, TokenLine}}.
{     : {token, {open_brace, TokenLine}}.
}     : {token, {close_brace, TokenLine}}.
=>    : {token, {map_arrow, TokenLine}}.

%% Reserved words
let         : {token, {'let', TokenLine}}.
in          : {token, {in, TokenLine}}.
match       : {token, {match, TokenLine}}.
with        : {token, {with, TokenLine}}.
beam        : {token, {beam, TokenLine}}.
module      : {token, {module, TokenLine}}.
export      : {token, {export, TokenLine}}.
type        : {token, {type_declare, TokenLine}}.
export_type : {token, {export_type, TokenLine}}.
import_type : {token, {import_type, TokenLine}}.
spawn       : {token, {spawn, TokenLine}}.
send        : {token, {send, TokenLine}}.
receive     : {token, {'receive', TokenLine}}.
after       : {token, {'after', TokenLine}}.
test        : {token, {'test', TokenLine}}.
error|exit|throw : {token, {'raise_error', TokenLine, TokenChars}}.

true|false : {token, {boolean, TokenLine, list_to_atom(TokenChars)}}.

%% Base types are the fundamental types available on the Erlang VM.
{BASE_TYPE} : {token, {base_type, TokenLine, TokenChars}}.
{BASE_LIST} : {token, {base_list, TokenLine}}.
{BASE_MAP}  : {token, {base_map, TokenLine}}.
{BASE_PID}  : {token, {base_pid, TokenLine}}.

%% Type variables (nicked from OCaml):
'{SYM} : {token, {type_var, TokenLine, string:substr(TokenChars, 2)}}.

%% User-defined type constructors
{TYPE} : {token, {type_constructor, TokenLine, TokenChars}}.

%% Type assertions/checks for guards

{TYPE_CHECK} : {token, {type_check_tok, list_to_atom(TokenChars), TokenLine}}.

%% Integer
{D}+       : {token, {int, TokenLine, list_to_integer(TokenChars)}}.

%% Float
{D}+\.{D}+ : {token, {float, TokenLine, list_to_float(TokenChars)}}.

%% Binaries
<< : {token, {bin_open, TokenLine}}.
>> : {token, {bin_close, TokenLine}}.
unit : {token, {bin_unit, TokenLine}}.
size : {token, {bin_size, TokenLine}}.
end : {token, {bin_end, TokenLine}}.
sign : {token, {bin_sign, TokenLine}}.
big|little|native : {token, {bin_endian, TokenLine, TokenChars}}.
utf8 : {token, {bin_text_encoding, TokenChars}}.

%% Symbol
{SYM}  : {token, {symbol, TokenLine, TokenChars}}.

%% Atom
{ATOM} : {token, {atom, TokenLine, tl(TokenChars)}}.

%% Module-function reference
{SYM}\.{SYM} : {token, {module_fun, TokenLine, TokenChars}}.

%% String
"(\\"*|\\.|[^"\\])*" :
  S = string:substr(TokenChars, 2, TokenLen - 2),
  {token, {string, TokenLine, S}}.

%% Chars
c"(\\"*|\\.|[^"\\])*" :
  S = string:substr(TokenChars, 3, TokenLen - 3),
  {token, {chars, TokenLine, S}}.


%% Operators
=    : {token, {assign, TokenLine}}.

==   : {token, {eq, TokenLine}}.
!=   : {token, {neq, TokenLine}}.
>    : {token, {gt, TokenLine}}.
<    : {token, {lt, TokenLine}}.
>=   : {token, {gte, TokenLine}}.
=<   : {token, {lte, TokenLine}}.

- : {token, {minus, TokenLine}}.
\+ : {token, {plus, TokenLine}}.

[\*\/\%]   : {token, {int_math, TokenLine, TokenChars}}.
{FLOAT_MATH} : {token, {float_math, TokenLine, TokenChars}}.
->   : {token, {'->', TokenLine}}.
_    : {token, {'_', TokenLine}}.

%% Whitespace ignore
{WS} : skip_token.
{BRK} : {token, {break, TokenLine}}.

%% Comments
--[.]*\n :
  Text = string:sub_string(TokenChars, 3),
  {token, {comment_line, TokenLine, Text}}.
({-([^-]|(-+[^}]))*-})|(--.*) :
  validate_comment(TokenLine, string:substr(TokenChars, 3)).



Erlang code.

-dialyzer({nowarn_function, yyrev/2}).

-ignore_xref([format_error/1, string/2, token/2, token/3, tokens/2, tokens/3]).

validate_comment(TokenLine, TokenChars) ->
    case string:str(TokenChars, "{-") of
        0 -> {token, {comment_lines, TokenLine, TokenChars}};
        _ -> {error, {nested_comment, TokenChars}}
    end.
