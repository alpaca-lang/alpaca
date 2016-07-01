% Copyright 2016 Jeremy Pierre
%
% Licensed under the Apache License, Version 2.0 (the "License");
% you may not use this file except in compliance with the License.
% You may obtain a copy of the License at
%
%     http://www.apache.org/licenses/LICENSE-2.0
%
% Unless required by applicable law or agreed to in writing, software
% distributed under the License is distributed on an "AS IS" BASIS,
% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
% See the License for the specific language governing permissions and
% limitations under the License.

Nonterminals 

comment
op infix
const
type poly_type type_member type_members type_expr type_vars
type_tuple type_tuple_list 
type_apply
type_import

cons literal_cons_items
term terms
unit tuple tuple_list
defn binding
module_def export_def export_list fun_and_arity
match_clause match_clauses match_with match_pattern 

send_to
receive_block
spawn_pid

compare type_check guard guards
ffi_call
expr simple_expr.

Terminals 

comment_line comment_lines

module export 
type_declare type_constructor type_var base_type base_list base_pid
use
boolean int float atom string chars '_'
symbol module_fun
assign int_math float_math
'[' ']' ':'
match with '|' '->'

send
receive after
spawn

call_erlang

type_check_tok

let in '(' ')' '/' ','

eq neq gt lt gte lte.

Rootsymbol expr.

%% Comments are stripped in the AST assembly right now but I want them 
%% embedded soon.
comment -> comment_line :
  {comment_line, L, Chars} = '$1',
  #mlfe_comment{multi_line=false,
                line=L,
                text=Chars}.
comment -> comment_lines :
  {comment_lines, L, Chars} = '$1',
  #mlfe_comment{multi_line=true,
                line=L,
                text=Chars}.

type_import -> use module_fun:
  {module_fun, _, MF} = '$2',
  [Mod, Type] = string:tokens(MF, "."),
  #mlfe_type_import{module=list_to_atom(Mod), type=Type}.

module_def -> module atom : {module, '$1'}.

type_vars -> type_var : ['$1'].
type_vars -> type_var type_vars : ['$1'|'$2'].

poly_type -> symbol type_vars : 
  {symbol, L, N} = '$1',
  #mlfe_type{name={type_name, L, N}, vars='$2'}.
poly_type -> poly_type type_vars : 
  '$1'#mlfe_type{vars='$1'#mlfe_type.vars ++ ['$2']}.

type_expr -> type_var : '$1'.
type_expr -> poly_type : '$1'.
type_expr -> symbol : 
  {symbol, L, N} = '$1',
  #mlfe_type{name={type_name, L, N}, vars=[]}. % not polymorphic
type_expr -> type_tuple : '$1'.
type_expr -> '(' type_expr ')': '$2'.
type_expr -> base_type : 
  {base_type, _, T} = '$1',
  list_to_atom("t_" ++ T).
type_expr -> base_list type_expr: 
  {mlfe_list, '$2'}.
type_expr -> base_pid type_expr :
  {mlfe_pid, '$2'}.

type_tuple_list -> type_expr ',' type_expr: ['$1', '$3'].
type_tuple_list -> type_expr ',' type_tuple_list: ['$1' | '$3'].

type_tuple -> '(' type_tuple_list ')': #mlfe_type_tuple{members='$2'}.

%%% A type_member is one of three things:
%%% 
%%% - a type name (symbol) followed by one or more type variables
%%% - a type constructor followed by one or more type variables
%%% - a tuple built from any combination of the above with the same
%%%   kind of tuples nested.
%%% 
%%% Valid type examples:
%%%     type T = int | A
%%%     type U x = B | C x
%%%     type V x y = D x | E (x, (int, x))
%%% 
type_member -> type_constructor : #mlfe_constructor{name='$1', arg=none}.
type_member -> type_constructor type_expr : #mlfe_constructor{name='$1', arg='$2'}.
type_member -> type_expr : '$1'.

type_members -> type_member : ['$1'].
type_members -> type_member '|' type_members : ['$1'|'$3'].

type -> type_declare poly_type assign type_members :
  '$2'#mlfe_type{members='$4'}.
type -> type_declare symbol assign type_members :
  {symbol, L, N} = '$2',
  #mlfe_type{name={type_name, L, N}, vars=[], members='$4'}.

type_apply -> type_constructor term : #mlfe_type_apply{name='$1', arg='$2'}.
type_apply -> type_constructor : #mlfe_type_apply{name='$1'}.

op -> int_math : '$1'.
op -> float_math : '$1'.

const -> boolean : '$1'.
const -> int : '$1'.
const -> float : '$1'.
const -> atom : '$1'.
const -> chars : '$1'.
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
  #mlfe_cons{head='$2', tail={nil, L}, line=L}.
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
term -> type_apply : '$1'.

terms -> term : ['$1'].
terms -> term terms : ['$1'|'$2'].

type_check -> type_check_tok symbol : 
  {_, Check, L} = '$1',
  #mlfe_type_check{type=Check, line=L, expr='$2'}.

compare -> eq : '$1'.
compare -> neq : '$1'.
compare -> gt : '$1'.
compare -> lt : '$1'.
compare -> gte : '$1'.
compare -> lte : '$1'.

guard -> term compare term : make_infix('$2', '$1', '$3').
guard -> type_check : '$1'.

guards -> guard : ['$1'].
guards -> guard ',' guards : ['$1'|'$3'].

match_pattern -> term : '$1'.
match_clause -> match_pattern '->' simple_expr :
  #mlfe_clause{pattern='$1', result='$3', line=term_line('$1')}.
match_clause -> match_pattern ',' guards '->' simple_expr :
  #mlfe_clause{pattern='$1', guards='$3', result='$5', line=term_line('$1')}.
match_clauses -> match_clause : ['$1'].
match_clauses -> match_clause '|' match_clauses : ['$1'|'$3'].

match_with  -> match simple_expr with match_clauses : 
  {match, L} = '$1',
  #mlfe_match{match_expr='$2', clauses='$4', line=L}.

send_to-> send term term :
  {send, L} = '$1',
  #mlfe_send{line=L, message='$2', pid='$3'}.

receive_block -> receive with match_clauses :
  {_, Line} = '$1',
  #mlfe_receive{line=Line, clauses='$3'}.
receive_block -> receive_block after int simple_expr :
  {_, _, Timeout} = '$3',
  '$1'#mlfe_receive{timeout=Timeout, timeout_action='$4'}.

%% Only supporting spawning functions inside the current module
%% for now:
spawn_pid -> spawn symbol cons:
  {_, L} = '$1',
  Args = cons_to_list('$3'),
  #mlfe_spawn{line=L,
              module=undefined,
              function='$2',
              args=Args}.

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
simple_expr -> send_to : '$1'.
simple_expr -> receive_block : '$1'.
simple_expr -> ffi_call : '$1'.
simple_expr -> guard : '$1'.
simple_expr -> spawn_pid : '$1'.

expr -> comment : '$1'.
expr -> simple_expr : '$1'.
expr -> type : '$1'.
expr -> module_def : '$1'.
expr -> export_def : '$1'.
expr -> type_import : '$1'.
expr -> defn : '$1'.

Erlang code.
-include("mlfe_ast.hrl").

-ignore_xref([format_error/1, parse_and_scan/1]).

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
      {eq, L} ->   {bif, '=:=', L, erlang, '=:='};
      {gt, L} ->   {bif, '>', L, erlang, '>'};
      {lt, L} ->   {bif, '<', L, erlang, '<'};
      {gte, L} ->  {bif, '>=', L, erlang, '>='};
      {lte, L} ->  {bif, '=<', L, erlang, '=<'};
      {neq, L} ->  {bif, '/=', L, erlang, '/='}
    end,
    #mlfe_apply{type=undefined,
                name=Name,
                args=[A, B]}.

make_define([{symbol, _, _} = Name|A], Expr) ->
    case validate_args(A) of
        {ok, Args} ->
            #mlfe_fun_def{name=Name, args=Args, body=Expr};
        {error, _} = E ->
            E
    end;
make_define([BadName|Args], _Expr) ->
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
    
term_line(Term) ->
    case Term of
        {_, L} when is_integer(L) -> L;
        {_, L, _} when is_integer(L) -> L;
        #mlfe_cons{line=L} -> L;
        #mlfe_tuple{values=[H|_]} -> term_line(H);
        #mlfe_type_apply{name=N} -> term_line(N)
    end.

cons_to_list({nil, _}) ->
    [];
cons_to_list(#mlfe_cons{head=H, tail=T}) ->
    [H|cons_to_list(T)].
