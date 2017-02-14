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
const module_fun
type poly_type poly_type_decl type_vars type_member type_members type_expr
sub_type_expr type_expressions type_tuple comma_separated_type_list type_list
module_qualified_type module_qualified_type_name
type_apply module_qualified_type_constructor
type_import type_export types_to_export

test_case

cons literal_cons_items
binary bin_segments bin_segment bin_qualifier bin_qualifiers
map_literal map_add map_literal_pairs map_pair

%% For literal records:
record_member record_members record record_transform
%% For pre-defined record types:
record_type_member record_type_members record_type

term terms
unit tuple tuple_list
defn definfix binding
module_def 

import_export_fun

export_def export_list fun_and_arity
import_def import_fun_items import_fun_item

fun_list_items fun_subset

match_clause match_clauses match_with match_pattern

send_to
receive_block
spawn_pid

error

compare type_check guard guards
ffi_call
expr simple_expr.

Terminals

comment_line comment_lines

module export import
import_type export_type

type_declare type_constructor type_var

test

boolean int float atom string chars '_'
symbol infixable '.'
assign int_math float_math minus plus
'[' ']' cons_infix ':'
bin_open bin_close
open_brace close_brace
map_open map_arrow
match with '|' '->'

raise_error

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
Left 200 infixable.


%% Comments are stripped in the AST assembly right now but I want them
%% embedded soon.
comment -> comment_line :
  {comment_line, L, Chars} = '$1',
  #alpaca_comment{multi_line=false,
                line=L,
                text=Chars}.
comment -> comment_lines :
  {comment_lines, L, Chars} = '$1',
  #alpaca_comment{multi_line=true,
                line=L,
                text=Chars}.

type_import -> import_type symbol '.' symbol:
  {symbol, _, Mod} = '$2',
  {symbol, _, Type} = '$4',
  #alpaca_type_import{module=list_to_atom(Mod), type=Type}.

types_to_export -> symbol : ['$1'].
types_to_export -> symbol ',' types_to_export : ['$1'|'$3'].

type_export -> export_type types_to_export :
  {_, L}  = '$1',
  Names = [N || {symbol, _, N} <- '$2'],
  #alpaca_type_export{line=L, names=Names}.

type_expressions -> sub_type_expr : ['$1'].
type_expressions -> sub_type_expr type_expressions : ['$1'|'$2'].

poly_type -> symbol type_expressions :
  {symbol, L, N} = '$1',
  Members = '$2',

  case {N, Members} of
      {"atom", Params}   -> type_arity_error(L, t_atom, Params);
      {"binary", Params} -> type_arity_error(L, t_binary, Params);
      {"bool", Params}   -> type_arity_error(L, t_bool, Params);
      {"chars", Params}  -> type_arity_error(L, t_chars, Params);
      {"float", Params}  -> type_arity_error(L, t_float, Params);
      {"int", Params}    -> type_arity_error(L, t_int, Params);
      {"list", [E]}      -> {t_list, E};
      {"list", Params}   -> type_arity_error(L, t_list, Params);
      {"map", [K, V]}    -> {t_map, K, V};
      {"map", Params}    -> type_arity_error(L, t_map, Params);
      {"pid", [T]}       -> {t_pid, T};
      {"pid", Params}    -> type_arity_error(L, t_pid, Params);
      {"string", Params} -> type_arity_error(L, t_string, Params);
      _ ->
          %% Any concrete type in the type_expressions gets a synthesized variable name:
          Vars = make_vars_for_concrete_types('$2', L),

          #alpaca_type{
             line = L,
             name = {type_name, L, N},
             members = Members,
             vars = Vars}
  end.

record_type_member -> symbol ':' type_expr : 
  {symbol, _L, N} = '$1',
  #t_record_member{name=list_to_atom(N), type='$3'}.

record_type_members -> record_type_member : ['$1'].
record_type_members -> record_type_member ',' record_type_members : ['$1' | '$3'].

record_type -> open_brace record_type_members close_brace : 
  #t_record{members='$2'}.

module_qualified_type_name -> symbol '.' symbol:
  {symbol, L, Mod} = '$1',
  {symbol, _, Name} = '$3',
  {module_qualified_type_name, L, Mod, Name}.

module_qualified_type -> module_qualified_type_name :
  {module_qualified_type_name, L, Mod, Name} = '$1',
  #alpaca_type{
     line = L,
     module = list_to_atom(Mod),
     name = {type_name, L, Name}}.

module_qualified_type -> module_qualified_type_name type_expressions:
  {module_qualified_type_name, L, Mod, Name} = '$1',
  %% Any concrete type in the type_expressions gets a synthesized variable name:
  Vars = make_vars_for_concrete_types('$2', L),

  #alpaca_type{
     line = L,
     module = list_to_atom(Mod),
     name = {type_name, L, Name},
     vars = Vars}.

type_expr -> poly_type : '$1'.
type_expr -> module_qualified_type : '$1'.
type_expr -> sub_type_expr : '$1'.

sub_type_expr -> type_var : '$1'.
sub_type_expr -> record_type : '$1'.
sub_type_expr -> symbol :
  {symbol, L, N} = '$1',
  case N of
      "atom" ->
          t_atom;
      "binary" ->
          t_binary;
      "bool" ->
          t_bool;
      "chars" ->
          t_chars;
      "float" ->
          t_float;
      "int" ->
          t_int;
      "list" ->
          return_error(L, {wrong_type_arity, t_list, 0});
      "map" ->
          return_error(L, {wrong_type_arity, t_map, 0});
      "pid" ->
          return_error(L, {wrong_type_arity, t_pid, 0});
      "string" ->
          t_string;
      _ ->
          #alpaca_type{name={type_name, L, N}, vars=[]} % not polymorphic
  end.

sub_type_expr -> type_tuple : '$1'.
sub_type_expr -> '(' type_expr ')': '$2'.
sub_type_expr -> '[' type_list ']' '->' type_expr :

    {t_arrow, '$2', '$5'}.
sub_type_expr -> unit : t_unit.

type_list -> comma_separated_type_list : '$1'.
type_list -> type_expr: ['$1'].

comma_separated_type_list -> type_expr ',' type_expr:
    ['$1', '$3'].
comma_separated_type_list -> type_expr ',' comma_separated_type_list:
    ['$1' | '$3'].

type_tuple -> '(' comma_separated_type_list ')':
    #alpaca_type_tuple{members='$2'}.

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
type_member -> type_constructor : 
  {type_constructor, L, N} = '$1',
  #alpaca_constructor{name=#type_constructor{line=L, name=N}, arg=none}.
type_member -> type_constructor type_expr :
  {type_constructor, L, N} = '$1',
  #alpaca_constructor{name=#type_constructor{line=L, name=N}, arg='$2'}.
type_member -> type_expr : '$1'.

type_members -> type_member : ['$1'].
type_members -> type_member '|' type_members : ['$1'|'$3'].

type -> type_declare poly_type_decl assign type_members :
  '$2'#alpaca_type{members='$4'}.
type -> type_declare symbol assign type_members :
  {symbol, L, N} = '$2',
  #alpaca_type{
     line=L,
     name={type_name, L, N},
     vars=[],
     members='$4'}.

poly_type_decl -> symbol type_vars :
  {symbol, L, N} = '$1',
  #alpaca_type{
     line=L,
     name={type_name, L, N},
     vars='$2'}.

type_vars -> type_var : ['$1'].
type_vars -> type_var type_vars : ['$1'|'$2'].

module_qualified_type_constructor -> symbol '.' type_constructor :
  {symbol, _, Mod} = '$1',
  {type_constructor, L, N} = '$3',
  #type_constructor{line=L, module=list_to_atom(Mod), name=N}.

type_apply -> module_qualified_type_constructor term :
  #alpaca_type_apply{name='$1', arg='$2'}.
type_apply -> module_qualified_type_constructor :
  #alpaca_type_apply{name='$1'}.

type_apply -> type_constructor term :
  {type_constructor, L, N} = '$1',
  #alpaca_type_apply{name=#type_constructor{line=L, name=N}, arg='$2'}.
type_apply -> type_constructor :
  {type_constructor, L, N} = '$1',
  #alpaca_type_apply{name=#type_constructor{line=L, name=N}}.

test_case -> test string assign simple_expr :
  #alpaca_test{line=term_line('$1'), name='$2', expression='$4'}.

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

module_fun -> symbol '.' symbol '/' int :
  {symbol, L, Mod} = '$1',
  {symbol, _, Fun} = '$3',
  {int, _, Arity} = '$5',
  #alpaca_far_ref{line=L, module=list_to_atom(Mod), name=Fun, arity=Arity}.
module_fun -> symbol '.' symbol :
  {symbol, L, Mod} = '$1',
  {symbol, _, Fun} = '$3',
  #alpaca_far_ref{line=L, module=list_to_atom(Mod), name=Fun}.

%% ----- Lists  ------------------------
literal_cons_items -> term : ['$1'].
literal_cons_items -> term ',' literal_cons_items: ['$1' | '$3'].

cons -> '[' ']' :
  {_, L} = '$1',
  {nil, L}.
cons -> '[' term ']' :
  {_, L} = '$3',
  #alpaca_cons{head='$2', tail={nil, L}, line=L}.
cons -> term cons_infix term : #alpaca_cons{head='$1', tail='$3'}.
cons -> '[' literal_cons_items ']':
  F = fun(X, Acc) -> #alpaca_cons{head=X, tail=Acc} end,
  lists:foldr(F, {nil, 0}, '$2').

%% -----  Binaries  --------------------
bin_qualifier -> type_declare assign symbol :
    {symbol, L, S} = '$3',
    case S of
        "binary" -> {bin_type, S};
        "float" -> {bin_type, S};
        "int" -> {bin_type, S};
        "utf8" -> {bin_type, S};
        _      -> return_error(L, {invalid_bin_type, S})
    end.
bin_qualifier -> symbol assign int :
    {symbol, L, S} = '$1',
    case S of
        "size" -> {size, '$3'};
        "unit" -> {unit, '$3'};
        _      -> return_error(L, {invalid_bin_qualifier, S})
    end.
bin_qualifier -> symbol assign boolean :
    {symbol, L, S} = '$1',
    case {S, '$3'} of
        {"sign", {boolean, L, true}}  -> {bin_sign, L, "signed"};
        {"sign", {boolean, L, false}} -> {bin_sign, L, "unsigned"};
        {_, _}                        ->
            return_error(L, {invalid_bin_qualifier, S})
    end.
bin_qualifier -> symbol assign symbol :
    {symbol, _, K} = '$1',
    {symbol, L, V} = '$3',
    case {K, V} of
        {"end", "big"}    -> {bin_endian, L, V};
        {"end", "little"} -> {bin_endian, L, V};
        {"end", "native"} -> {bin_endian, L, V};
        {"end", _}        -> return_error(L, {invalid_endianess, V});
        {_, _}            -> return_error(L, {invalid_bin_qualifier, K})
    end.

bin_qualifiers -> bin_qualifier : ['$1'].
bin_qualifiers -> bin_qualifier bin_qualifiers : ['$1' | '$2'].

bin_segment -> float : #alpaca_bits{value='$1', type=float, line=term_line('$1')}.
bin_segment -> int : #alpaca_bits{value='$1', type=int, line=term_line('$1')}.
bin_segment -> symbol : #alpaca_bits{value='$1', line=term_line('$1')}.
bin_segment -> binary : #alpaca_bits{value='$1', line=term_line('$1'), type=binary}.
bin_segment -> string : #alpaca_bits{value='$1', line=term_line('$1'), type=utf8}.
%% TODO:  string bin_segment

bin_segment -> bin_segment ':' bin_qualifiers :
  lists:foldl(fun(Q, S) -> add_qualifier(S, Q) end, '$1', '$3').

bin_segments -> bin_segment : ['$1'].
bin_segments -> bin_segment ',' bin_segments : ['$1'|'$3'].

binary -> bin_open bin_close : #alpaca_binary{line=term_line('$1'), segments=[]}.
binary -> bin_open bin_segments bin_close :
  #alpaca_binary{line=term_line('$1'), segments='$2'}.

%% ----- Maps --------------------------
map_pair -> term map_arrow term :
  #alpaca_map_pair{line=term_line('$1'), key='$1', val='$3'}.
map_literal_pairs -> map_pair : ['$1'].
map_literal_pairs -> map_pair ',' map_literal_pairs : ['$1'|'$3'].

map_literal -> map_open close_brace :
  #alpaca_map{line=term_line('$1')}.
map_literal -> map_open map_literal_pairs close_brace :
  #alpaca_map{line=term_line('$1'), pairs='$2'}.

%% Adding a pair to a map, e.g. #{:a => "b" :: existing_map}
map_add -> map_open map_pair '|' term close_brace:
  #alpaca_map_add{line=term_line('$1'), to_add='$2', existing='$4'}.

record_member -> symbol assign simple_expr:
  {symbol, L, N} = '$1',
  #alpaca_record_member{line=L, name=list_to_atom(N), val='$3'}.

record_members -> record_member: ['$1'].
record_members -> record_member ',' record_members: ['$1' | '$3'].

record -> open_brace record_members close_brace:
  {_, L} = '$1',
  #alpaca_record{line=L, arity=length('$2'), members='$2'}.

record_transform -> open_brace record_members '|' term close_brace:
  {_, L} = '$1',
  #alpaca_record_transform{line=L, additions='$2', existing='$4'}.

%% Need to permit "empty" records for pattern matches:
record -> open_brace close_brace:
  {_, L} = '$1',
  #alpaca_record{line=L, arity=0, members=[]}.

unit -> '(' ')':
  {_, L} = '$1',
  {unit, L}.

tuple_list -> simple_expr ',' simple_expr : ['$1', '$3'].
tuple_list -> simple_expr ',' tuple_list : ['$1' | '$3'].
tuple -> '(' tuple_list ')' :
  #alpaca_tuple{arity=length('$2'), values='$2'}.

infix -> term op term : make_infix('$2', '$1', '$3').

%% ----- Errors (including throw, exit) --------------
error -> raise_error term:
  {_, L, Kind} = '$1',
  {raise_error, L, list_to_atom(Kind), '$2'}.

term -> const : '$1'.
term -> tuple : '$1'.
term -> infix : '$1'.
term -> symbol : '$1'.
term -> cons : '$1'.
term -> binary : '$1'.
term -> map_literal : '$1'.
term -> map_add : '$1'.
term -> record : '$1'.
term -> record_transform : '$1'.
term -> module_fun : '$1'.
term -> '(' simple_expr ')' : '$2'.
term -> type_apply : '$1'.
term -> error : '$1'.

terms -> term : ['$1'].
terms -> term terms : ['$1'|'$2'].

type_check -> type_check_tok symbol :
  {_, Check, L} = '$1',
  #alpaca_type_check{type=Check, line=L, expr='$2'}.

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
  #alpaca_clause{pattern='$1', result='$3', line=term_line('$1')}.
match_clause -> match_pattern ',' guards '->' simple_expr :
  #alpaca_clause{pattern='$1', guards='$3', result='$5', line=term_line('$1')}.
match_clauses -> match_clause : ['$1'].
match_clauses -> match_clause '|' match_clauses : ['$1'|'$3'].

match_with  -> match simple_expr with match_clauses :
  {match, L} = '$1',
  #alpaca_match{match_expr='$2', clauses='$4', line=L}.

send_to-> send term term :
  {send, L} = '$1',
  #alpaca_send{line=L, message='$2', pid='$3'}.

receive_block -> receive with match_clauses :
  {_, Line} = '$1',
  #alpaca_receive{line=Line, clauses='$3'}.
receive_block -> receive_block after int simple_expr :
  {_, _, Timeout} = '$3',
  '$1'#alpaca_receive{timeout=Timeout, timeout_action='$4'}.

%% Only supporting spawning functions inside the current module
%% for now:
spawn_pid -> spawn symbol terms:
  {_, L} = '$1',
  #alpaca_spawn{line=L,
              module=undefined,
              function='$2',
              args='$3'}.

defn -> let terms assign simple_expr : make_define('$2', '$4', 'top').
definfix -> let '(' infixable ')' terms assign simple_expr : 
  {infixable, L, C} = '$3',
  make_define([{symbol, L, "(" ++ C ++ ")"}] ++ '$5', '$7', 'top').

binding -> let defn in simple_expr : make_binding('$2', '$4').

binding -> let terms assign simple_expr in simple_expr : 
    make_binding(make_define('$2', '$4', 'let'), '$6').


ffi_call -> beam atom atom cons with match_clauses:
  #alpaca_ffi{module='$2',
            function_name='$3',
            args='$4',
            clauses='$6'}.

module_def -> module symbol :
{symbol, L, Name} = '$2',
{module, list_to_atom(Name), L}.

export_def -> export export_list : {export, '$2'}.
%% Imported functions come out of the parser in the following tuple format:
%%   {FunctionName, {ModuleName, Arity}}
%% where names are strings (lists) and Arity is integer().
%% 
%% Name comes first because we will resolve missing local functions in the order
%% that they were imported.  We can import individual functions from another 
%% module with `import foo.bar` for all arities of `bar` or `import foo.bar/1`
%% for only `bar1`.  Subsets of functions from the same module can be imported
%% in a list, e.g. `import foo.[bar, baz/2]` to import all arities of `bar` and
%% in the case of `baz`, only it's version that takes two arguments.
import_def -> import import_fun_items : {import, lists:flatten('$2')}.

%% fun_list_items get turned into the correct tuple format above when they
%% become a fun_subset (see a bit further below).
fun_list_items -> import_export_fun :
  {symbol, _, F} = '$1',
  [F].
fun_list_items -> fun_and_arity : ['$1'].
fun_list_items -> import_export_fun ',' fun_list_items :
  {symbol, _, F} = '$1',
  [F | '$3'].
fun_list_items -> fun_and_arity ',' fun_list_items : ['$1' | '$3'].

%% Here we associate the module name with each of the functions being imported.
%% We do this so we can deal with a flat proplist later on when resolving 
%% functions that aren't defined in the module importing these functions.
fun_subset -> symbol '.' '[' fun_list_items ']' : 
  {symbol, _, Mod} = '$1',
  F = fun({Name, Arity}) -> {Name, {list_to_atom(Mod), Arity}};
         (Name)          -> {Name, list_to_atom(Mod)}
  end,
  lists:map(F, '$4').

%% Individually imported items now:

%% module.foo means import all arities for foo:
import_fun_item -> symbol '.' import_export_fun :
  {symbol, _, Mod} = '$1',
  {symbol, _, Fun} = '$3',
  {Fun, list_to_atom(Mod)}.
%% module.foo/1 means only import foo/1:
import_fun_item -> symbol '.' import_export_fun '/' int:
  {symbol, _, Mod} = '$1',
  {symbol, _, Fun} = '$3',
  {int, _, Arity} = '$5',  
  {Fun, {list_to_atom(Mod), Arity}}.
import_fun_item -> fun_subset : '$1'.

import_fun_items -> import_fun_item : ['$1'].
import_fun_items -> import_fun_item ',' import_fun_items : ['$1'|'$3'].

import_export_fun -> symbol : '$1'.
import_export_fun -> '(' infixable ')' :
  {infixable, L, C} = '$2',
  {symbol, L, "(" ++ C ++ ")"}.

fun_and_arity -> import_export_fun '/' int :
  {symbol, _, Name} = '$1',
  {int, _, Arity} = '$3',
  {Name, Arity}.
fun_and_arity -> symbol '/' int :
{symbol, _, Name} = '$1',
{int, _, Arity} = '$3',
{Name, Arity}.

export_list -> fun_and_arity : ['$1'].
export_list -> import_export_fun :
  {_, _, Name} = '$1',
  [Name].
export_list -> fun_and_arity ',' export_list : ['$1' | '$3'].
export_list -> symbol ',' export_list :
  {_, _, Name} = '$1',
  [Name | '$3'].

%% TODO:  we should be able to apply the tail to the result of
%%        an expression that yields a function.  This check
%%        must move to the eventual type checker.
simple_expr -> terms :
case '$1' of
    [T] ->
        T;
    [{symbol, L, _} = S | T] ->
        #alpaca_apply{line=L, expr=S, args=T};
    [#alpaca_far_ref{line=L, module=Mod, name=Fun} | T] ->
        Name = {Mod, {symbol, L, Fun}, length(T)},
        #alpaca_apply{line=L, expr=Name, args=T};
    [Term|Args] ->
        #alpaca_apply{line=term_line(Term), expr=Term, args=Args}
end.

simple_expr -> binding : '$1'.
simple_expr -> match_with : '$1'.
simple_expr -> send_to : '$1'.
simple_expr -> receive_block : '$1'.
simple_expr -> ffi_call : '$1'.
simple_expr -> guard : '$1'.
simple_expr -> spawn_pid : '$1'.
simple_expr -> simple_expr infixable simple_expr : make_infix('$2', '$1', '$3').

expr -> comment : '$1'.
expr -> simple_expr : '$1'.
expr -> type : '$1'.
expr -> test_case : '$1'.
expr -> defn : '$1'.
expr -> definfix : '$1'.

%% I'm not sure these should be actually classifed as "expressions", something
%% to revisit:
expr -> module_def : '$1'.
expr -> export_def : '$1'.
expr -> import_def : '$1'.
expr -> type_import : '$1'.
expr -> type_export : '$1'.


Erlang code.
-include("alpaca_ast.hrl").

-ignore_xref([format_error/1, parse_and_scan/1]).

make_infix(Op, A, B) ->
    Name = case Op of
      {infixable, L, C} -> {symbol, L, "(" ++ C ++ ")"};
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
    #alpaca_apply{type=undefined,
                  line=term_line(Name),
                  expr=Name,
                  args=[A, B]}.

make_define([{symbol, L, _} = Name|A], Expr, Level) ->
    case validate_args(L, A) of
        {ok, []} ->
            %% If this is a zero-arg function, at the toplevel, it's a value
            %% and therefore its body must be restricted to literals only
            case {Level, is_literal(Expr)} of
                {top, false} -> 
                    {error, non_literal_value, Name, Expr};
                _ -> 
                    #alpaca_fun_def{
                      name=Name,
                      arity=0,
                      versions=[#alpaca_fun_version{
                                   line=L,
                                   args=[],
                                   body=Expr}]}
            end;
        {ok, Args} ->
            #alpaca_fun_def{
               name=Name, 
               arity=length(Args), 
               versions=[#alpaca_fun_version{
                            line=L,
                            args=Args,
                            body=Expr}]}
%        {error, _} = E ->
%            E
    end;
make_define([BadName|Args], _Expr, _) ->
    {error, {invalid_function_name, BadName, Args}}.

%% Unit is only valid for single argument functions as a way around
%% the problem of distinguishing between nullary functions and
%% variable bindings in let forms:
validate_args(_L, [{unit, _}]=Args) ->
    {ok, Args};
validate_args(L, Args) ->
    validate_args(L, Args, []).

validate_args(_L, [], GoodArgs) ->
    {ok, lists:reverse(GoodArgs)};
validate_args(L, [#alpaca_match{}=E|_], _) ->
    return_error(L, {invalid_fun_parameter, E});
validate_args(L, [#alpaca_spawn{}=E|_], _) ->
    return_error(L, {invalid_fun_parameter, E});
validate_args(L, [A|T], Memo) ->
    validate_args(L, T, [A|Memo]).

%% Determine whether an expression is a literal
is_literal({int, _, _}) -> true;
is_literal({string, _, _}) -> true;
is_literal({float, _, _}) -> true;
is_literal({alpaca_record, _, _, _, Members}) ->
    MemberExprs = lists:map(
        fun({alpaca_record_member, _, _, _, M}) -> 
            M 
        end, Members),  
    all_literals(MemberExprs);
is_literal({nil, _}) -> true;
is_literal({alpaca_cons, _, _, Value, Sub}) ->
    case is_literal(Value) of
        false -> false;
        true -> is_literal(Sub)
    end;
is_literal({alpaca_binary, _, Members}) ->
    MemberExprs = lists:map(
        fun({alpaca_bits, _, _, M, _, _, _, _, _}) ->
            M
    end, Members),
    all_literals(MemberExprs);
is_literal({alpaca_type_apply, _, _, Expr}) ->
    is_literal(Expr);
is_literal({atom, _, _}) -> true;
is_literal({boolean, _, _}) -> true;
is_literal({chars, _, _}) -> true;
is_literal({alpaca_tuple, _, _, Members}) ->
    all_literals(Members);
is_literal({unit, _}) ->
    true;
is_literal(_) -> false.

all_literals([]) -> true;
all_literals([M|Rest]) ->
    case is_literal(M) of
        true -> all_literals(Rest);
        false -> false
    end.

%% Convert a nullary def into a variable binding:
make_binding(#alpaca_fun_def{name=N, versions=[#alpaca_fun_version{args=[], body=B}]}, Expr) ->
    #var_binding{name=N, to_bind=B, expr=Expr};
make_binding(Def, Expr) ->
    #fun_binding{def=Def, expr=Expr}.

term_line(Term) ->
    case Term of
        {_, L} when is_integer(L) -> L;
        {_, L, _} when is_integer(L) -> L;
        {bif, _, L, _, _} -> L;
        #alpaca_apply{line=L} -> L;
        #alpaca_cons{line=L} -> L;
        #alpaca_map_pair{line=L} -> L;
        #alpaca_map{line=L} -> L;
        #alpaca_record{members=[#alpaca_record_member{line=L}|_]} -> L;
        #alpaca_record_transform{line=L} -> L;
        #alpaca_tuple{values=[H|_]} -> term_line(H);
        #alpaca_type_apply{name=N} -> term_line(N);
        #type_constructor{line=L} -> L
    end.

add_qualifier(#alpaca_bits{}=B, {size, {int, _, I}}) ->
    B#alpaca_bits{size=I, default_sizes=false};
add_qualifier(#alpaca_bits{}=B, {unit, {int, _, I}}) ->
    B#alpaca_bits{unit=I, default_sizes=false};
add_qualifier(#alpaca_bits{}=B, {bin_endian, _, E}) ->
    B#alpaca_bits{endian=list_to_atom(E)};
add_qualifier(#alpaca_bits{}=B, {bin_type, Enc}) ->
    B#alpaca_bits{type=list_to_atom(Enc)};
add_qualifier(#alpaca_bits{}=B, {bin_sign, _, S}) ->
    B#alpaca_bits{sign=list_to_atom(S)}.

make_vars_for_concrete_types(Vars, Line) ->
    F = fun({type_var, _, _}=V, {Vs, VarNum}) ->
                {[V|Vs], VarNum};
           (Expr, {Vs, VarNum}) ->
                VN = ":SynthTypeVar_" ++ integer_to_list(VarNum),
                {[{{type_var, Line, VN}, Expr}|Vs], VarNum + 1}
        end,
    {Vs, _} = lists:foldl(F, {[], 0}, Vars),
    lists:reverse(Vs).

type_arity_error(L, Typ, Params) ->
    return_error(L, {wrong_type_arity, Typ, length(Params)}).

