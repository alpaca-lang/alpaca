-module(ast).
-export([line/1]).
-export([symbol/2, symbol_name/1, symbol_rename/2]).

-include("alpaca_ast.hrl").

line(#a_sym{line=L}) ->
    L.

symbol(Line, Name) ->
    #a_sym{line=Line, name=Name}.

symbol_name(#a_sym{name=N}) ->
    N.

symbol_rename(#a_sym{name=Orig}=S, NewName) ->
    S#a_sym{name=NewName, original=Orig}.
