Nonterminals 

op infix
const
cons nil literal_cons_items
term terms nested_terms
unit tuple tuple_list
defn binding
apply
module_def module_part module_parts export_def export_list fun_and_arity
match_clause match_clauses match_with match_pattern guard guards
ffi_call
expr simple_expr.

Terminals 

module export 
boolean int float atom string '_'
symbol module_fun
assign int_math float_math
'[' ']' ':'
match with '|' '->'
call_erlang
let in '(' ')' '/' ','

'eq'.

Rootsymbol expr.

module_def -> module atom : {module, '$1'}.

module_part -> defn : '$1'.
module_part -> export_def : '$1'.

module_parts -> module_part : ['$1'].
module_parts -> module_part module_parts : ['$1'|'$2'].

op -> int_math : '$1'.
op -> float_math : '$1'.

const -> boolean : '$1'.
const -> int : '$1'.
const -> float : '$1'.
const -> atom : '$1'.
const -> string : '$1'.
const -> '_' : '$1'.
const -> unit : '$1'.

literal_cons_items -> term : ['$1'].
literal_cons_items -> term ',' literal_cons_items: ['$1' | '$3'].

cons -> '[' ']' : 
  {_, L} = '$1',
  {nil, L}.
cons -> '[' term ']' : 
  {_, L} = '$3',
  #mlfe_cons{head='$2', tail={nil, L}}.
cons -> term ':' term : #mlfe_cons{head='$1', tail='$3'}.
cons -> '[' literal_cons_items ']':
  F = fun(X, Acc) -> #mlfe_cons{head=X, tail=Acc} end,
  lists:foldr(F, {nil, 0}, '$2').

unit -> '(' ')':
  {_, L} = '$1',
  {unit, L}.

tuple_list -> simple_expr ',' simple_expr : ['$1', '$3'].
tuple_list -> simple_expr ',' tuple_list : ['$1' | '$3'].
tuple -> '(' tuple_list ')' : 
  #mlfe_tuple{arity=length('$2'), values='$2'}.

infix -> term op term : make_infix('$2', '$1', '$3').

term -> const : '$1'.
term -> tuple : '$1'.
term -> infix : '$1'.
term -> symbol : '$1'.
term -> cons : '$1'.
term -> module_fun : '$1'.
term -> '(' simple_expr ')' : '$2'.

terms -> term : ['$1'].
terms -> term terms : ['$1'|'$2'].

guard -> term eq term : make_infix('$2', '$1', '$3').

guards -> guard : ['$1'].
guards -> guard ',' guards : ['$1'|'$3'].

match_pattern -> term : '$1'.
match_clause -> match_pattern '->' simple_expr :
  #mlfe_clause{pattern='$1', result='$3'}.
match_clause -> match_pattern ',' guards '->' simple_expr :
  #mlfe_clause{pattern='$1', guards='$3', result='$5'}.
match_clauses -> match_clause : ['$1'].
match_clauses -> match_clause '|' match_clauses : ['$1'|'$3'].

match_with  -> match simple_expr with match_clauses : #mlfe_match{match_expr='$2', clauses='$4'}.

defn -> terms assign simple_expr : make_define('$1', '$3').
binding -> let defn in simple_expr : make_binding('$2', '$4').

ffi_call -> call_erlang atom atom cons with match_clauses:
  #mlfe_ffi{module='$2',
            function_name='$3',
            args='$4',
            clauses='$6'}.

module_def -> module symbol : 
{symbol, _, Name} = '$2',
{module, list_to_atom(Name)}.

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
    [{module_fun, L, MF} | T] ->
        % this should be safe given the definition of a module-function
        % reference in mlfe_scan.xrl:
        [Mod, Fun] = string:tokens(MF, "."),
        Name = {list_to_atom(Mod), {symbol, L, Fun}, length(T)},
        #mlfe_apply{name=Name, args=T};
    [Term|Args] ->
        {error, {invalid_fun_application, Term, Args}}
end.

simple_expr -> binding : '$1'.
simple_expr -> match_with : '$1'.
simple_expr -> ffi_call : '$1'.
simple_expr -> guard : '$1'.

expr -> simple_expr : '$1'.
expr -> module_def : '$1'.
expr -> export_def : '$1'.
expr -> defn : '$1'.

Erlang code.
-include("mlfe_ast.hrl").

make_infix(Op, A, B) ->
    Name = case Op of
      {int_math, L, '%'} -> {bif, '%', L, erlang, 'rem'};
      {int_math, L, OpString} ->
                   OpAtom =  list_to_atom(OpString),
                   {bif, OpAtom, L, erlang, OpAtom};
      {float_math, L, OpString} ->
                   [OpChar|_] = OpString,
                   OpAtom = list_to_atom([OpChar]),
                   {bif, list_to_atom(OpString), L, erlang, OpAtom};
      {eq, L} ->
                   {bif, '==', L, erlang, '=='}
    end,
    #mlfe_apply{type=undefined,
                name=Name,
                args=[A, B]}.

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
    
