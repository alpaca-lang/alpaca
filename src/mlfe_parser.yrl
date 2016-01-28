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
boolean int float atom string '_'
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

infix -> term op term : {infix, '$2', '$1', '$3'}.

term -> const : '$1'.
term -> tuple : '$1'.
term -> infix : '$1'.
term -> symbol : '$1'.
term -> '(' simple_expr ')' : '$2'.

terms -> term : ['$1'].
terms -> term terms : ['$1'|'$2'].

match_pattern -> term : '$1'.
match_pattern -> cons : '$1'.
match_clause -> '|' match_pattern '->' simple_expr : {match_clause, '$2', '$4'}.
match_clauses -> match_clause : ['$1'].
match_clauses -> match_clause match_clauses : ['$1'|'$2'].

match_with  -> match simple_expr with match_clauses : {match, '$2', '$4'}.

defn -> terms assign simple_expr : {defn, '$1', '$3'}.
binding -> let defn in simple_expr : {bind_in, '$2', '$4'}.

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

simple_expr -> terms :
case '$1' of
    [T] ->
        T;
    [{symbol, _, _} = S | T] ->
        {apply, S, T}
end.
simple_expr -> binding : '$1'.
simple_expr -> match_with : '$1'.
simple_expr -> cons : '$1'.

expr -> simple_expr : '$1'.
expr -> module_def : '$1'.
expr -> export_def : '$1'.
expr -> defn : '$1'.
