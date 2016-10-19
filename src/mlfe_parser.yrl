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

Nonterminals

comment
op infix
const
type poly_type poly_type_decl type_vars type_member type_members type_expr
type_expressions type_tuple type_tuple_list
type_apply
type_import

test_case

cons literal_cons_items
binary bin_segments bin_segment bin_qualifier bin_qualifiers
map_literal map_add map_literal_pairs map_pair

%% For literal records:
record_member record_members record
%% For pre-defined record types:
record_type_member record_type_members record_type

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
type_declare type_constructor type_var base_type base_list base_map base_pid
test
':'
use
boolean int float atom string chars '_'
symbol module_fun
assign int_math float_math minus plus
'[' ']' cons_infix
bin_open bin_close bin_unit bin_size bin_end bin_endian bin_sign bin_text_encoding
open_brace close_brace
map_open map_arrow
match with '|' '->'

send
receive after
spawn

beam

type_check_tok

let in '(' ')' '/' ','

eq neq gt lt gte lte.

Rootsymbol expr.

Unary 500 minus.
Unary 500 plus.

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

type_expressions -> type_expr : ['$1'].
type_expressions -> type_expr type_expressions : ['$1'|'$2'].

poly_type -> symbol type_expressions :
  {symbol, L, N} = '$1',
  Members = '$2',
  Vars = [V || {type_var, _, _}=V <- Members],
  #mlfe_type{name={type_name, L, N}, members=Members, vars=Vars}.

record_type_member -> symbol ':' type_expr : 
  {symbol, L, N} = '$1',
  #t_record_member{name=list_to_atom(N), type='$3'}.

record_type_members -> record_type_member : ['$1'].
record_type_members -> record_type_member ',' record_type_members : ['$1' | '$3'].

record_type -> open_brace record_type_members close_brace : 
  #t_record{members='$2'}.

type_expr -> type_var : '$1'.
type_expr -> record_type : '$1'.
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
type_expr -> base_map type_expr type_expr : {mlfe_map, '$2', '$3'}.
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

type -> type_declare poly_type_decl assign type_members :
  '$2'#mlfe_type{members='$4'}.
type -> type_declare symbol assign type_members :
  {symbol, L, N} = '$2',
  #mlfe_type{name={type_name, L, N}, vars=[], members='$4'}.

poly_type_decl -> symbol type_vars :
  {symbol, L, N} = '$1',
  #mlfe_type{name={type_name, L, N}, vars='$2'}.
poly_type -> poly_type type_vars :
  '$1'#mlfe_type{vars='$1'#mlfe_type.vars ++ ['$2']}.

type_vars -> type_var : ['$1'].
type_vars -> type_var type_vars : ['$1'|'$2'].

type_apply -> type_constructor term : #mlfe_type_apply{name='$1', arg='$2'}.
type_apply -> type_constructor : #mlfe_type_apply{name='$1'}.

test_case -> test string assign simple_expr :
  #mlfe_test{line=term_line('$1'), name='$2', expression='$4'}.

op -> int_math : '$1'.
op -> float_math : '$1'.
op -> minus : '$1'.
op -> plus : '$1'.

const -> boolean : '$1'.
const -> minus int : {int, L, Val} = '$2', {int, L, 0-Val}.
const -> plus int : '$2'.
const -> int : '$1'.
const -> minus float : {float, L, Val} = '$2', {float, L, 0-Val}.
const -> float : '$1'.
const -> plus float : '$2'.
const -> atom : '$1'.
const -> chars : '$1'.
const -> string : '$1'.
const -> '_' : '$1'.
const -> unit : '$1'.

%% ----- Lists  ------------------------
literal_cons_items -> term : ['$1'].
literal_cons_items -> term ',' literal_cons_items: ['$1' | '$3'].

cons -> '[' ']' :
  {_, L} = '$1',
  {nil, L}.
cons -> '[' term ']' :
  {_, L} = '$3',
  #mlfe_cons{head='$2', tail={nil, L}, line=L}.
cons -> term cons_infix term : #mlfe_cons{head='$1', tail='$3'}.
cons -> '[' literal_cons_items ']':
  F = fun(X, Acc) -> #mlfe_cons{head=X, tail=Acc} end,
  lists:foldr(F, {nil, 0}, '$2').

%% -----  Binaries  --------------------
bin_qualifier -> type_declare assign base_type : '$3'.
bin_qualifier -> type_declare assign bin_text_encoding : '$3'.
bin_qualifier -> bin_unit assign int : {unit, '$3'}.
bin_qualifier -> bin_size assign int : {size, '$3'}.
bin_qualifier -> bin_end assign bin_endian : '$3'.
bin_qualifier -> bin_sign assign boolean :
  case '$3' of
      {boolean, L, true} -> {bin_sign, L, "signed"};
      {boolean, L, false} -> {bin_sign, L, "unsigned"}
  end.

bin_qualifiers -> bin_qualifier : ['$1'].
bin_qualifiers -> bin_qualifier bin_qualifiers : ['$1' | '$2'].

bin_segment -> float : #mlfe_bits{value='$1', type=float, line=term_line('$1')}.
bin_segment -> int : #mlfe_bits{value='$1', type=int, line=term_line('$1')}.
bin_segment -> symbol : #mlfe_bits{value='$1', line=term_line('$1')}.
bin_segment -> binary : #mlfe_bits{value='$1', line=term_line('$1'), type=binary}.
bin_segment -> string : #mlfe_bits{value='$1', line=term_line('$1'), type=utf8}.
%% TODO:  string bin_segment

bin_segment -> bin_segment ':' bin_qualifiers :
  lists:foldl(fun(Q, S) -> add_qualifier(S, Q) end, '$1', '$3').

bin_segments -> bin_segment : ['$1'].
bin_segments -> bin_segment ',' bin_segments : ['$1'|'$3'].

binary -> bin_open bin_close : #mlfe_binary{line=term_line('$1'), segments=[]}.
binary -> bin_open bin_segments bin_close :
  #mlfe_binary{line=term_line('$1'), segments='$2'}.

%% ----- Maps --------------------------
map_pair -> term map_arrow term :
  #mlfe_map_pair{line=term_line('$1'), key='$1', val='$3'}.
map_literal_pairs -> map_pair : ['$1'].
map_literal_pairs -> map_pair ',' map_literal_pairs : ['$1'|'$3'].

map_literal -> map_open close_brace :
  #mlfe_map{line=term_line('$1')}.
map_literal -> map_open map_literal_pairs close_brace :
  #mlfe_map{line=term_line('$1'), pairs='$2'}.

%% Adding a pair to a map, e.g. #{:a => "b" :: existing_map}
map_add -> map_open map_pair '|' term close_brace:
  #mlfe_map_add{line=term_line('$1'), to_add='$2', existing='$4'}.

record_member -> symbol assign simple_expr:
  {symbol, L, N} = '$1',
  #mlfe_record_member{line=L, name=list_to_atom(N), val='$3'}.

record_members -> record_member: ['$1'].
record_members -> record_member ',' record_members: ['$1' | '$3'].

record -> open_brace record_members close_brace:
  #mlfe_record{arity=length('$2'), members='$2'}.

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
term -> binary : '$1'.
term -> map_literal : '$1'.
term -> map_add : '$1'.
term -> record : '$1'.
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
spawn_pid -> spawn symbol terms:
  {_, L} = '$1',
  #mlfe_spawn{line=L,
              module=undefined,
              function='$2',
              args='$3'}.

defn -> terms assign simple_expr : make_define('$1', '$3').
binding -> let defn in simple_expr : make_binding('$2', '$4').

ffi_call -> beam atom atom cons with match_clauses:
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
expr -> test_case : '$1'.
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
      {minus, L} -> {bif, '-', L, erlang, '-'};
      {plus, L} -> {bif, '+', L, erlang, '+'};
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
        #mlfe_map_pair{line=L} -> L;
        #mlfe_map{line=L} -> L;
        #mlfe_tuple{values=[H|_]} -> term_line(H);
        #mlfe_type_apply{name=N} -> term_line(N)
    end.

add_qualifier(#mlfe_bits{}=B, {size, {int, _, I}}) ->
    B#mlfe_bits{size=I, default_sizes=false};
add_qualifier(#mlfe_bits{}=B, {unit, {int, _, I}}) ->
    B#mlfe_bits{unit=I, default_sizes=false};
add_qualifier(#mlfe_bits{}=B, {bin_endian, _, E}) ->
    B#mlfe_bits{endian=list_to_atom(E)};
add_qualifier(#mlfe_bits{}=B, {base_type, _, T})
  when T =:= "int"; T =:= "float"; T =:= "binary"; T =:= "utf8" ->
    B#mlfe_bits{type=list_to_atom(T)};
add_qualifier(#mlfe_bits{}=B, {bin_text_encoding, Enc}) ->
    B#mlfe_bits{type=list_to_atom(Enc)};
add_qualifier(#mlfe_bits{}=B, {bin_sign, _, S}) ->
    B#mlfe_bits{sign=list_to_atom(S)}.
