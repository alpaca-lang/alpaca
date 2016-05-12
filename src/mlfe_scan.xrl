Definitions.
D   = [0-9]
L   = [a-z]
U   = [A-Z]
SYM = {L}[a-zA-Z0-9_]*
ATOM = :[a-zA-Z0-9_\*]*
TYPE = {U}[a-zA-Z0-9_]*
WS  = [\s\n]
BRK = \n\n
FLOAT_MATH = (\+\.)|(\-\.)|(\*\.)|(\/\.)
TYPE_CHECK = is_integer|is_float|is_atom|is_bool|is_list|is_chars

Rules.
%% Separators
,     : {token, {',', TokenLine}}.
/     : {token, {'/', TokenLine}}.

{     : {token, {'{', TokenLine}}.
}     : {token, {'}', TokenLine}}.
\(    : {token, {'(', TokenLine}}.
\)    : {token, {')', TokenLine}}.
\|    : {token, {'|', TokenLine}}.
\:\:    : {token, {':', TokenLine}}.
\[    : {token, {'[', TokenLine}}.
\]    : {token, {']', TokenLine}}.
()    : {token, {unit, TokenLine}}.

%% Reserved words
let         : {token, {'let', TokenLine}}.
in          : {token, {in, TokenLine}}.
match       : {token, {match, TokenLine}}.
with        : {token, {with, TokenLine}}.
call_erlang : {token, {call_erlang, TokenLine}}.
module      : {token, {module, TokenLine}}.
export      : {token, {export, TokenLine}}.
type        : {token, {type_decl, TokenLine}}.

%% Type assertions/checks for guards

{TYPE_CHECK} : {token, {type_check_tok, list_to_atom(TokenChars), TokenLine}}.

%% Integer
[+-]?{D}+       : {token, {int, TokenLine, list_to_integer(TokenChars)}}.

%% Float
[+-]?{D}+\.{D}+ : {token, {float, TokenLine, list_to_float(TokenChars)}}.

%% Symbol
{SYM}  : {token, {symbol, TokenLine, TokenChars}}.

%% Atom
{ATOM} : {token, {atom, TokenLine, tl(TokenChars)}}.

%% Type
{TYPE} : {token, {type_name, TokenLine, TokenChars}}.

%% Module-function reference
{SYM}\.{SYM} : {token, {module_fun, TokenLine, TokenChars}}.

%% Chars
\'([^\']|\\.|\')*\' :   
  S = string:substr(TokenChars, 2, TokenLen - 2),
  {token, {chars, TokenLine, S}}.

%% String
"([^"]|\\.|\")*" :
  S = string:substr(TokenChars, 2, TokenLen - 2),
  {token, {string, TokenLine, S}}.

%% Operators
=    : {token, {assign, TokenLine}}.

==   : {token, {eq, TokenLine}}.
!=   : {token, {neq, TokenLine}}.
>    : {token, {gt, TokenLine}}.
<    : {token, {lt, TokenLine}}.
>=   : {token, {gte, TokenLine}}.
=<   : {token, {lte, TokenLine}}.

[\+\-\*\/\%]   : {token, {int_math, TokenLine, TokenChars}}.
{FLOAT_MATH} : {token, {float_math, TokenLine, TokenChars}}.
->   : {token, {'->', TokenLine}}.
_    : {token, {'_', TokenLine}}.

%% Whitespace ignore
{WS} : skip_token.
{BRK} : {token, {break, TokenLine}}.

Erlang code.

