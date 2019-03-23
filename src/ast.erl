-module(ast).

%% Exports are divided into three categories based on purpose:
%%   1. Functions that make AST nodes.
%%   2. Functions that retrieve values from AST node contents.
%%   3. Functions that manipulate or mutate (making a copy of) AST nodes.

%% Functions that construct AST node values:
-export([unit/1,
	 bool/2,
	 atom/2,
	 int/2,
	 float/2,
	 string/2,
	 symbol/2
	]).

%% Functions that retrieve parts of AST nodes:
-export([line/1,
	 symbol_name/1
	]).

%% Functions that mutate/manipulate AST node internals:
-export([symbol_rename/2]).

-include("alpaca_ast.hrl").

line(#a_unit{line=L}) ->
    L;
line(#a_bool{line=L}) ->
    L;
line(#a_atom{line=L}) ->
    L;
line(#a_int{line=L}) ->
    L;
line(#a_flt{line=L}) ->
    L;
line(#a_str{line=L}) ->
    L;
line(#a_sym{line=L}) ->
    L.

unit(Line) ->
    #a_unit{line=Line}.

bool(Line, Val) ->
    #a_bool{line=Line, val=Val}.

%% Multiple types accepted by `atom` simply for convenience.
atom(Line, Val) when is_list(Val) ->
    #a_atom{line=Line, val=list_to_atom(Val)};
atom(Line, Val) when is_binary(Val) ->
    #a_atom{line=Line, val=binary_to_atom(Val, utf8)};
atom(Line, Val) when is_atom(Val) ->
    #a_atom{line=Line, val=Val}.

int(Line, Val) ->
    #a_int{line=Line, val=Val}.

float(Line, Val) ->
    #a_flt{line=Line, val=Val}.

string(Line, Val) ->
    #a_str{line=Line, val=Val}.

symbol(Line, Name) ->
    #a_sym{line=Line, name=Name}.

symbol_name(#a_sym{name=N}) ->
    N.

%% Used for renaming symbols as part of Alpaca's final AST generation stage,
%% after parsing with `yecc`.  See alpaca_ast_gen:rename_bindings/2 for more
%% details.
symbol_rename(#a_sym{name=Orig}=S, NewName) ->
    S#a_sym{name=NewName, original=Orig}.
