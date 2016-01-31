Definitions.
D   = [0-9]
L   = [a-z]
U   = [A-Z]
SYM = {L}[a-zA-Z0-9_]*
ATOM = \'{SYM}
TYPE = {U}[a-zA-Z0-9_]*
WS  = [\s\n]
BRK = \n\n

Rules.
%% Separators
,     : {token, {',', TokenLine}}.
/     : {token, {'/', TokenLine}}.

{     : {token, {'{', TokenLine}}.
}     : {token, {'}', TokenLine}}.
\(    : {token, {'(', TokenLine}}.
\)    : {token, {')', TokenLine}}.
\|    : {token, {'|', TokenLine}}.
\:    : {token, {':', TokenLine}}.
\[    : {token, {'[', TokenLine}}.
\]    : {token, {']', TokenLine}}.
()    : {token, {unit, TokenLine}}.

%% Reserved words
let    : {token, {'let', TokenLine}}.
in     : {token, {in, TokenLine}}.
match  : {token, {match, TokenLine}}.
with   : {token, {with, TokenLine}}.
module : {token, {module, TokenLine}}.
export : {token, {export, TokenLine}}.
type   : {token, {type_decl, TokenLine}}.

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

%% Operators
=    : {token, {assign, TokenLine}}.
==   : {token, {eq, TokenLine}}.
\+   : {token, {add, TokenLine}}.
-    : {token, {minus, TokenLine}}.
->   : {token, {'->', TokenLine}}.
_    : {token, {'_', TokenLine}}.

%% Whitespace ignore
{WS} : skip_token.
{BRK} : {token, {break, TokenLine}}.

Erlang code.

