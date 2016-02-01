Nonterminals 

op infix
const
cons nil
term terms nested_terms
tuple tuple_list
defn binding
apply
module_def module_part module_parts export_def export_list fun_and_arity
match_clause match_clauses match_with match_pattern
expr simple_expr.

Terminals 

module export 
boolean int float atom string '_' unit
symbol
assign add minus
'[' ']' ':'
match with '|' '->'
let in '(' ')' '/' ','.

Rootsymbol expr.

module_def -> module atom : {module, '$1'}.

module_part -> defn : '$1'.
module_part -> export_def : '$1'.

module_parts -> module_part : ['$1'].
module_parts -> module_part module_parts : ['$1'|'$2'].

op -> add : '$1'.
op -> minus : '$1'.

const -> boolean : '$1'.
const -> int : '$1'.
const -> float : '$1'.
const -> atom : '$1'.
const -> string : '$1'.
const -> '_' : '$1'.
const -> unit : '$1'.

cons -> '[' ']' : 
  {_, L} = '$1',
  {nil, L}.
cons -> '[' term ']' : 
  {_, L} = '$3',
  {cons, '$2', {nil, L}}.
cons -> term ':' cons : {cons, '$1', '$3'}.
cons -> term ':' term : {cons, '$1', '$3'}.

tuple_list -> simple_expr ',' simple_expr : ['$1', '$3'].
tuple_list -> simple_expr ',' tuple_list : ['$1' | '$3'].
tuple -> '(' tuple_list ')' : {tuple, '$2'}.

infix -> term op term : make_infix('$2', '$1', '$3').
%{infix, '$2', '$1', '$3'}.

term -> const : '$1'.
term -> tuple : '$1'.
term -> infix : '$1'.
term -> symbol : '$1'.
term -> '(' simple_expr ')' : '$2'.

terms -> term : ['$1'].
terms -> term terms : ['$1'|'$2'].

match_pattern -> term : '$1'.
match_pattern -> cons : '$1'.
match_clause -> '|' match_pattern '->' simple_expr : #mlfe_clause{pattern='$2', result='$4'}.
match_clauses -> match_clause : ['$1'].
match_clauses -> match_clause match_clauses : ['$1'|'$2'].

match_with  -> match simple_expr with match_clauses : #mlfe_match{match_expr='$2', clauses='$4'}.

defn -> terms assign simple_expr : make_define('$1', '$3').
binding -> let defn in simple_expr : make_binding('$2', '$4').

module_def -> module symbol : 
{symbol, _, Name} = '$2',
{module, Name}.

export_def -> export export_list : {export, '$2'}.

fun_and_arity -> symbol '/' int : 
{symbol, _, Name} = '$1',
{int, _, Arity} = '$3',
{Name, Arity}.
export_list -> fun_and_arity : ['$1'].
export_list -> fun_and_arity ',' export_list : ['$1' | '$3'].

%% TODO:  we should be able to apply the tail to the result of
%%        an expression that yields a function.  This check 
%%        must move to the eventual type checker.
simple_expr -> terms :
case '$1' of
    [T] ->
        T;
    [{symbol, _, _} = S | T] ->
        #mlfe_apply{name=S, args=T};
    [Term|Args] ->
        {error, {invalid_fun_application, Term, Args}}
end.

simple_expr -> binding : '$1'.
simple_expr -> match_with : '$1'.
simple_expr -> cons : '$1'.

expr -> simple_expr : '$1'.
expr -> module_def : '$1'.
expr -> export_def : '$1'.
expr -> defn : '$1'.

Erlang code.
-include("mlfe_ast.hrl").

make_infix(Op, A, B) ->
    #mlfe_infix{type=undefined,
                operator=Op,
                left=A,
                right=B}.

make_define([{symbol, _, N} = Name|A], Expr) ->
    io:format("~nDefining function ~w ~s~n", [Name, N]),
    
    case validate_args(A) of
        {ok, Args} ->
            #mlfe_fun_def{name=Name, args=Args, body=Expr};
        {error, _} = E ->
            E
    end;
make_define([BadName|Args], Expr) ->
    {error, {invalid_function_name, BadName, Args}}.

%% Unit is only valid for single argument functions as a way around
%% the problem of distinguishing between nullary functions and 
%% variable bindings in let forms:
validate_args([{unit, _}]=Args) ->
    {ok, Args};
validate_args(Args) ->
    validate_args(Args, []).

validate_args([], GoodArgs) ->
    {ok, lists:reverse(GoodArgs)};
validate_args([{symbol, _, _}=A|T], Memo) ->
    validate_args(T, [A|Memo]);
validate_args([NonSymbol|_], _) ->
    {error, {invalid_fun_parameter, NonSymbol}}.

%% Convert a nullary def into a variable binding:
make_binding(#mlfe_fun_def{name=N, args=[], body=B}, Expr) ->
    #var_binding{name=N, to_bind=B, expr=Expr};
make_binding(Def, Expr) ->
    #fun_binding{def=Def, expr=Expr}.
    
