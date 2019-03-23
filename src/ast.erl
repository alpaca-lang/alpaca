-module(ast).
-export([line/1]).
-export([int/2,
	 float/2,
	 symbol/2, symbol_name/1, symbol_rename/2
	]).

-include("alpaca_ast.hrl").

line(#a_int{line=L}) ->
    L;
line(#a_flt{line=L}) ->
    L;
line(#a_sym{line=L}) ->
    L.

int(Line, Val) ->
    #a_int{line=Line, val=Val}.

float(Line, Val) ->
    #a_flt{line=Line, val=Val}.

%% TODO:  string

symbol(Line, Name) ->
    #a_sym{line=Line, name=Name}.

symbol_name(#a_sym{name=N}) ->
    N.

symbol_rename(#a_sym{name=Orig}=S, NewName) ->
    S#a_sym{name=NewName, original=Orig}.
