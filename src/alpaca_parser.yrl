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
sub_type_expr type_expressions type_tuple comma_separated_type_list
module_qualified_type module_qualified_type_name
type_apply module_qualified_type_constructor
type_import type_export types_to_export type_signature

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
defn definfix binding all_infix
module_def

import_export_fun

export_def export_list fun_and_arity
import_def import_fun_items import_fun_item

literal_fun
literal_fun_clause literal_fun_clauses

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

type_declare type_constructor type_var val

test

boolean int float atom string chars '_'
symbol infixl infixr '.'
assign int_math float_math minus plus
'[' ']' cons_infix ':'
bin_open bin_close
open_brace close_brace
map_open map_arrow
match with '|' '->'  'and' 'or' 'xor'

raise_error

send
receive after receiver
spawn

beam

type_check_tok

let in '(' ')' '/' ','
fn

eq neq gt lt gte lte.

Rootsymbol expr.

Unary 500 minus.
Unary 500 plus.
Right 0 infixr.
Left 100 infixl.


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
  Mod = symbol_name('$2'),
  Type = symbol_name('$4'),
  #alpaca_type_import{module=binary_to_atom(Mod, utf8), type=Type}.

types_to_export -> symbol : [unwrap('$1')].
types_to_export -> symbol ',' types_to_export : [unwrap('$1')|'$3'].

type_export -> export_type types_to_export :
  {_, L}  = '$1',
  Names = [symbol_name(S) || S <- '$2'],
  #alpaca_type_export{line=L, names=Names}.

type_signature -> val symbol ':' sub_type_expr :
  {L, N} = symbol_line_name('$2'),
  #alpaca_type_signature{name=N, line=L, type='$4'}.

type_signature -> val symbol type_vars ':' sub_type_expr :
  {L, N} = symbol_line_name('$2'),
  TV = make_vars_for_concrete_types('$3', L),
  #alpaca_type_signature{name=N, line=L, type='$5', vars=TV}.

type_signature -> val '(' infixl ')' ':' sub_type_expr :
  {L, N} = symbol_line_name('$3'),
  #alpaca_type_signature{name=N, line=L, type='$6'}.

type_signature -> val '(' infixl ')' type_vars ':' sub_type_expr :
  {L, N} = symbol_line_name('$3'),
  TV = make_vars_for_concrete_types('$5', L),
  #alpaca_type_signature{name=N, line=L, type='$7', vars=TV}.

type_signature -> val '(' infixr ')' ':' sub_type_expr :
  {L, N} = symbol_line_name('$3'),
  #alpaca_type_signature{name=N, line=L, type='$6'}.

type_signature -> val '(' infixr ')' type_vars ':' sub_type_expr :
  {L, N} = symbol_line_name('$3'),
  TV = make_vars_for_concrete_types('$5', L),
  #alpaca_type_signature{name=N, line=L, type='$7', vars=TV}.

type_expressions -> sub_type_expr : ['$1'].
type_expressions -> sub_type_expr type_expressions : ['$1'|'$2'].

poly_type -> symbol type_expressions :
  {L, N} = symbol_line_name('$1'),

  Members = '$2',

  case {N, Members} of
      {<<"atom">>, Params}           -> type_arity_error(L, t_atom, Params);
      {<<"binary">>, Params}         -> type_arity_error(L, t_binary, Params);
      {<<"bool">>, Params}           -> type_arity_error(L, t_bool, Params);
      {<<"chars">>, Params}          -> type_arity_error(L, t_chars, Params);
      {<<"float">>, Params}          -> type_arity_error(L, t_float, Params);
      {<<"int">>, Params}            -> type_arity_error(L, t_int, Params);
      {<<"list">>, [E]}              -> {t_list, E};
      {<<"list">>, Params}           -> type_arity_error(L, t_list, Params);
      {<<"map">>, [K, V]}            -> {t_map, K, V};
      {<<"map">>, Params}            -> type_arity_error(L, t_map, Params);
      {<<"pid">>, [T]}               -> {t_pid, T};
      {<<"pid">>, Params}            -> type_arity_error(L, t_pid, Params);
      {<<"string">>, Params}         -> type_arity_error(L, t_string, Params);
      {<<"rec">>, Params}            -> type_arity_error(L, t_rec, Params);
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
  N = symbol_name('$1'),
  #t_record_member{name=binary_to_atom(N, utf8), type='$3'}.

record_type_members -> record_type_member : ['$1'].
record_type_members -> record_type_member ',' record_type_members : ['$1' | '$3'].

record_type -> open_brace record_type_members close_brace :
  #t_record{members='$2'}.

module_qualified_type_name -> symbol '.' symbol:
  {L, Mod} = symbol_line_name('$1'),
  Name = symbol_name('$3'),
  {module_qualified_type_name, L, Mod, Name}.

module_qualified_type -> module_qualified_type_name :
  {module_qualified_type_name, L, Mod, Name} = '$1',
  #alpaca_type{
     line = L,
     module = binary_to_atom(Mod, utf8),
     name = {type_name, L, Name}}.

module_qualified_type -> module_qualified_type_name type_expressions:
  {module_qualified_type_name, L, Mod, Name} = '$1',
  %% Any concrete type in the type_expressions gets a synthesized variable name:
  Vars = make_vars_for_concrete_types('$2', L),

  #alpaca_type{
     line = L,
     module = binary_to_atom(Mod, utf8),
     name = {type_name, L, Name},
     vars = Vars}.

type_expr -> poly_type : '$1'.
type_expr -> module_qualified_type : '$1'.
type_expr -> sub_type_expr : '$1'.

sub_type_expr -> type_var : '$1'.
sub_type_expr -> record_type : '$1'.
sub_type_expr -> symbol :
  {L, N} = symbol_line_name('$1'),

  case N of
      <<"atom">> ->
          t_atom;
      <<"binary">> ->
          t_binary;
      <<"bool">> ->
          t_bool;
      <<"chars">> ->
          t_chars;
      <<"float">> ->
          t_float;
      <<"int">> ->
          t_int;
      <<"list">> ->
          return_error(L, {wrong_type_arity, t_list, 0});
      <<"map">> ->
          return_error(L, {wrong_type_arity, t_map, 0});
      <<"pid">> ->
          return_error(L, {wrong_type_arity, t_pid, 0});
      <<"string">> ->
          t_string;
      <<"rec">> ->
          t_rec;
      _ ->
          #alpaca_type{name={type_name, L, N}, vars=[]} % not polymorphic
  end.

sub_type_expr -> type_tuple : '$1'.
sub_type_expr -> '(' type_expr ')': '$2'.
sub_type_expr -> fn type_expressions '->' type_expr :

    {t_arrow, '$2', '$4'}.

sub_type_expr -> receiver type_expressions :
    {receiver, L} = '$1',
    case '$2' of
        [MArg, MRet] -> {t_receiver, MArg, MRet};
        Params       -> type_arity_error(L, t_receiver, Params)
    end.

sub_type_expr -> unit : t_unit.

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
  {L, N} = symbol_line_name('$2'),
  %% Breaking this out to reduce repetition:
  MakeType = fun() ->
		    #alpaca_type{
		       line=L,
		       name={type_name, L, N},
		       vars=[],
		       members='$4'}
	    end,
  case '$4' of
      [#alpaca_constructor{}] -> MakeType();
      [M] -> #alpaca_type_alias{line=L, name={type_name, L, N}, target=M};
      _   -> MakeType()
  end.

poly_type_decl -> symbol type_vars :
  {L, N} = symbol_line_name('$1'),
  #alpaca_type{
     line=L,
     name={type_name, L, N},
     vars='$2'}.

type_vars -> type_var : ['$1'].
type_vars -> type_var type_vars : ['$1'|'$2'].

module_qualified_type_constructor -> symbol '.' type_constructor :
  Mod = symbol_name('$1'),
  {type_constructor, L, N} = '$3',
  #type_constructor{line=L, module=binary_to_atom(Mod, utf8), name=N}.

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
  #alpaca_test{line=term_line('$1'), name=unwrap('$2'), expression='$4'}.

op -> int_math : '$1'.
op -> float_math : '$1'.
op -> minus : '$1'.
op -> plus : '$1'.
op -> '/' : '$1'.

const -> boolean : unwrap('$1').

const -> minus int :
  #a_int{line=L, val=Val} = unwrap('$2'),
  ast:int(L, 0-Val).
const -> plus int :
  '$2'.
const -> int :
  '$1'.

const -> minus float :
  #a_flt{line=L, val=Val} = unwrap('$2'),
  ast:float(L, 0-Val).
const -> float :
  '$1'.
const -> plus float :
  '$2'.

const -> atom : unwrap('$1').
const -> chars : '$1'.
const -> string : unwrap('$1').
const -> '_' : '$1'.
const -> unit : unwrap('$1').

module_fun -> symbol '.' symbol '/' int :
  {L, Mod} = symbol_line_name('$1'),
  Fun = symbol_name('$3'),
  #a_int{val=Arity} = unwrap('$5'),
  #alpaca_far_ref{
     line=L,
     module=binary_to_atom(Mod, utf8),
     name=Fun,
     arity=Arity}.
module_fun -> symbol '.' symbol :
  {L, Mod} = symbol_line_name('$1'),
  Fun = symbol_name('$3'),
  #alpaca_far_ref{line=L, module=binary_to_atom(Mod, utf8), name=Fun}.

%% ----- Lists  ------------------------
literal_cons_items -> simple_expr : ['$1'].
literal_cons_items -> simple_expr ',' literal_cons_items: ['$1' | '$3'].

cons -> '[' ']' :
  {_, L} = '$1',
  {nil, L}.
cons -> '[' simple_expr ']' :
  {_, L} = '$3',
  #alpaca_cons{head='$2', tail={nil, L}, line=L}.
cons -> term cons_infix term :
  L = term_line('$1'),
  #alpaca_cons{head='$1', tail='$3', line=L}.
cons -> '[' literal_cons_items ']':
  F = fun(X, Acc) -> #alpaca_cons{head=X, tail=Acc, line=term_line(X)} end,
  {_, L} = '$3',
  lists:foldr(F, {nil, L}, '$2').

%% -----  Binaries  --------------------
bin_qualifier -> type_declare assign symbol :
    {L, S} = symbol_line_name('$3'),
    case S of
        <<"binary">> -> {bin_type, S};
        <<"float">> -> {bin_type, S};
        <<"int">> -> {bin_type, S};
        <<"utf8">> -> {bin_type, S};
        _      -> return_error(L, {invalid_bin_type, S})
    end.
bin_qualifier -> symbol assign int :
    {L, S} = symbol_line_name('$1'),
    case S of
        <<"size">> -> {size, unwrap('$3')};
        <<"unit">> -> {unit, unwrap('$3')};
        _          -> return_error(L, {invalid_bin_qualifier, S})
    end.
bin_qualifier -> symbol assign boolean :
    {L, S} = symbol_line_name('$1'),
    case {S, unwrap('$3')} of
        {<<"sign">>, #a_bool{line=L, val=true}}  -> {bin_sign, L, <<"signed">>};
        {<<"sign">>, #a_bool{line=L, val=false}} -> {bin_sign, L, <<"unsigned">>};
        {_, _}                        ->
            return_error(L, {invalid_bin_qualifier, S})
    end.
bin_qualifier -> symbol assign symbol :
    K = symbol_name('$1'),
    {L, V} = symbol_line_name('$3'),
    case {K, V} of
        {<<"end">>, <<"big">>}    -> {bin_endian, L, V};
        {<<"end">>, <<"little">>} -> {bin_endian, L, V};
        {<<"end">>, <<"native">>} -> {bin_endian, L, V};
        {<<"end">>, _}            -> return_error(L, {invalid_endianness, V});
        {_, _}                    -> return_error(L, {invalid_bin_qualifier, V})
    end.

bin_qualifiers -> bin_qualifier : ['$1'].
bin_qualifiers -> bin_qualifier bin_qualifiers : ['$1' | '$2'].

%% TODO:  this is not tested!  AST gen is a reasonable place to do so.
bin_segment -> float :
  #alpaca_bits{value=unwrap('$1'), type=float, line=term_line('$1')}.
bin_segment -> int :
  #alpaca_bits{value=unwrap('$1'), type=int, line=term_line(unwrap('$1'))}.
bin_segment -> symbol :
  #alpaca_bits{value=unwrap('$1'), line=line(unwrap('$1'))}.
bin_segment -> binary : #alpaca_bits{value='$1', line=term_line('$1'), type=binary}.
bin_segment -> string :
  Actual = unwrap('$1'),
  #alpaca_bits{value=Actual, line=term_line(Actual), type=utf8}.
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
  {L, N} = symbol_line_name('$1'),
  #alpaca_record_member{line=L, name=binary_to_atom(N, utf8), val='$3'}.

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
  ast:unit(L).

tuple_list -> simple_expr ',' simple_expr : ['$1', '$3'].
tuple_list -> simple_expr ',' tuple_list : ['$1' | '$3'].
tuple -> '(' tuple_list ')' :
  {_, L} = '$1',
  #alpaca_tuple{line=L, arity=length('$2'), values='$2'}.

infix -> term 'xor' term :
  L1 = term_line('$1'),
  FalseC1 = #alpaca_clause{ pattern=#alpaca_tuple{ line=L1
						 , arity=2
						 , values=[ ast:bool(L1, false)
							  , ast:bool(L1, false)
							  ]
						 },
			    result=ast:bool(L1, false)
			  , line=L1
			  },
  FalseC2 = #alpaca_clause{pattern=#alpaca_tuple{ line=L1
						, arity=2
						, values=[ ast:bool(L1, true)
							 , ast:bool(L1, true)
							 ]
						}
			  , result=ast:bool(L1, false)
			  , line=L1
			  },
  TrueC1 = #alpaca_clause{ pattern=#alpaca_tuple{ line=L1
						, arity=2
						, values=[ ast:bool(L1, true)
							 , ast:bool(L1, false)
							 ]
						}
			 , result=ast:bool(L1, true)
			 , line=L1
			 },
  TrueC2 = #alpaca_clause{ pattern=#alpaca_tuple{ line=L1
						, arity=2
						, values=[ ast:bool(L1, false)
							 , ast:bool(L1, true)
							 ]
						}
			 , result=ast:bool(L1, true)
			 , line=L1
			 },
  #alpaca_match{
     match_expr=#alpaca_tuple{arity=2, values=['$1', '$3']},
     clauses=[TrueC1, TrueC2, FalseC1, FalseC2],
     line=L1
    }.

infix -> term 'and' term :
         L1 = term_line('$1'),
         L2 = term_line('$3'),
         FalseC = #alpaca_clause{ pattern=ast:bool(L1, false)
				, result=ast:bool(L1, false)
				, line=L1
				},
         TrueC = #alpaca_clause{ pattern=ast:bool(L2, true)
			       , result='$3'
			       , line=L2},
         #alpaca_match{
            match_expr='$1',
            clauses=[TrueC, FalseC],
            line=L1
           }.

infix -> term 'or' term :
         L1 = term_line('$1'),
         L2 = term_line('$3'),
         TrueC = #alpaca_clause{ pattern=ast:bool(L1, true)
			       , result=ast:bool(L1, true)
			       , line=L1
			       },
         FalseC = #alpaca_clause{ pattern=ast:bool(L2, false)
				, result='$3'
				, line=L2
				},
         #alpaca_match{
            match_expr='$1',
            clauses=[TrueC, FalseC],
            line=L1
           }.

infix -> term op term : make_infix('$2', '$1', '$3').

literal_fun -> fn terms '->' simple_expr:
  {_, L} = '$1',
  {ok, Args} = validate_args(L, '$2'),
  #alpaca_fun{line=L,
              arity=length('$2'),
              versions=[#alpaca_fun_version{
			   line=L,
                           args=Args,
                           body='$4'}]}.

literal_fun_clause -> '|' match_clause:
  '$2'.
literal_fun_clauses -> literal_fun_clause: ['$1'].
literal_fun_clauses -> literal_fun_clause literal_fun_clauses: ['$1'|'$2'].

literal_fun -> fn literal_fun_clauses:
  {_, L} = '$1',
  F = fun(#alpaca_clause{pattern=P, guards=Gs, result=R, line=CL}) ->
              #alpaca_fun_version{line=CL,
                                  args=[P],
                                  guards=Gs,
                                  body=R}
      end,
  #alpaca_fun{line=L,
              arity=1,
              versions=lists:map(F, '$2')}.

%% ----- Errors (including throw, exit) --------------
error -> raise_error term:
  {_, L, Kind} = '$1',
  {raise_error, L, list_to_atom(Kind), '$2'}.

term -> literal_fun : '$1'.
term -> const : unwrap('$1').
term -> tuple : '$1'.
term -> infix : '$1'.
term -> symbol : unwrap('$1').
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
  #alpaca_type_check{type=Check, line=L, expr=unwrap('$2')}.

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

match_pattern -> term : validate_match_pattern('$1').
match_clause -> match_pattern '->' simple_expr :
  #alpaca_clause{pattern='$1', result='$3', line=term_line('$1')}.
match_clause -> match_pattern ',' guards '->' simple_expr :
  #alpaca_clause{pattern='$1', guards='$3', result='$5', line=term_line('$1')}.

match_clauses -> match_clause : ['$1'].
match_clauses -> '|' match_clause : ['$2'].
match_clauses -> match_clause '|' match_clauses : ['$1'|'$3'].
match_clauses -> '|' match_clause '|' match_clauses : ['$2'|'$4'].

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
  #a_int{val=Timeout} = unwrap('$3'),
  '$1'#alpaca_receive{timeout=Timeout, timeout_action='$4'}.

%% Only supporting spawning functions inside the current module
%% for now:
spawn_pid -> spawn symbol terms:
  {_, L} = '$1',
  #alpaca_spawn{line=L,
              module=undefined,
              function=unwrap('$2'),
              args='$3'}.

defn -> let terms assign simple_expr : make_define('$2', '$4', 'top').

definfix -> let '(' infixl ')' terms assign simple_expr :
  {infixl, L, C} = '$3',
  %% This conversion may seem excessive but note that the purpose of the Alpaca
  %% native AST is to let Alpaca code work with the AST.  This means that symbol
  %% names do need to be legitimate Alpaca strings in UTF-8, not Erlang strings.
  InfixName = infix_name(C),
  make_define([ast:symbol(L, InfixName) | '$5'], '$7', 'top').

definfix -> let '(' infixr ')' terms assign simple_expr :
  {infixr, L, C} = '$3',
  InfixName = infix_name(C),
  make_define([ast:symbol(L, InfixName) | '$5'], '$7', 'top').

binding -> let defn in simple_expr : make_binding('$2', '$4').

binding -> let terms assign simple_expr in simple_expr :
    make_binding(make_define('$2', '$4', 'let'), '$6').

ffi_call -> beam atom atom cons with match_clauses:
  {_, L} = '$1',
  #alpaca_ffi{module=unwrap('$2'),
	      function_name=unwrap('$3'),
	      args='$4',
	      clauses='$6',
	      line=L}.

module_def -> module symbol :
{L, Name} = symbol_line_name('$2'),
{module, binary_to_atom(Name, utf8), L}.

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
  F = symbol_name('$1'),
  [F].
fun_list_items -> fun_and_arity : ['$1'].
fun_list_items -> import_export_fun ',' fun_list_items :
  F = symbol_name('$1'),
  [F | '$3'].
fun_list_items -> fun_and_arity ',' fun_list_items : ['$1' | '$3'].

%% Here we associate the module name with each of the functions being imported.
%% We do this so we can deal with a flat proplist later on when resolving
%% functions that aren't defined in the module importing these functions.
fun_subset -> symbol '.' '[' fun_list_items ']' :
  Mod = binary_to_atom(symbol_name('$1'), utf8),
  F = fun({Name, Arity}) -> {Name, {Mod, Arity}};
         (Name)          -> {Name, Mod}
  end,
  lists:map(F, '$4').

%% Individually imported items now:

%% module.foo means import all arities for foo:
import_fun_item -> symbol '.' import_export_fun :
  Mod = symbol_name('$1'),
  Fun = symbol_name('$3'),
  {Fun, binary_to_atom(Mod, utf8)}.
%% module.foo/1 means only import foo/1:
import_fun_item -> symbol '.' import_export_fun '/' int:
  Mod = symbol_name('$1'),
  Fun = symbol_name('$3'),
  #a_int{val=Arity} = unwrap('$5'),
  {Fun, {binary_to_atom(Mod, utf8), Arity}}.
import_fun_item -> fun_subset : '$1'.

import_fun_items -> import_fun_item : ['$1'].
import_fun_items -> import_fun_item ',' import_fun_items : ['$1'|'$3'].

import_export_fun -> symbol : unwrap('$1').

all_infix -> infixl : '$1'.
all_infix -> infixr : '$1'.

import_export_fun -> '(' all_infix ')' :
  {_, L, C} = '$2',
  ast:symbol(L, infix_name(C)).

fun_and_arity -> import_export_fun '/' int :
  Name = symbol_name('$1'),
  #a_int{val=Arity} = unwrap('$3'),
  {Name, Arity}.
fun_and_arity -> symbol '/' int :
  Name = symbol_name('$1'),
  %% Destructuring the tuple from leex, we don't need or want the `int` tag:
  {_, #a_int{val=Arity}} = '$3',
  {Name, Arity}.

export_list -> fun_and_arity : ['$1'].
export_list -> import_export_fun :
  Name = symbol_name('$1'),
  [Name].
export_list -> fun_and_arity ',' export_list : ['$1' | '$3'].
export_list -> symbol ',' export_list :
  Name = symbol_name('$1'),
  [Name | '$3'].

%% TODO:  we should be able to apply the tail to the result of
%%        an expression that yields a function.  This check
%%        must move to the eventual type checker.
simple_expr -> terms :
case '$1' of
    [T] ->
        T;
    [{symbol, S} | T] ->
        #alpaca_apply{line=line(S), expr=S, args=T};
    [#alpaca_far_ref{line=L, module=Mod, name=Fun} | T] ->
        FunName = unicode:characters_to_binary(Fun, utf8),
        Name = {Mod, ast:symbol(L, FunName), length(T)},
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
simple_expr -> simple_expr infixl simple_expr : make_infix('$2', '$1', '$3').
simple_expr -> simple_expr infixr simple_expr : make_infix('$2', '$1', '$3').


expr -> comment : '$1'.
expr -> simple_expr : '$1'.
expr -> type : '$1'.
expr -> test_case : '$1'.
expr -> defn : '$1'.
expr -> definfix : '$1'.
expr -> type_signature : '$1'.

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
      {infixl, L, C} ->
                   ast:symbol(L, infix_name(C));
      {infixr, L, C} ->
                   ast:symbol(L, infix_name(C));

      {int_math, L, "%"} -> {bif, '%', L, erlang, 'rem'};

      {minus, L} -> {bif, '-', L, erlang, '-'};
      {plus, L} -> {bif, '+', L, erlang, '+'};
      {int_math, L, OpString} ->
                   OpAtom =  list_to_atom(OpString),
                   {bif, OpAtom, L, erlang, OpAtom};
      {float_math, L, OpString} ->
                   [OpChar|_] = OpString,
                   OpAtom = list_to_atom([OpChar]),
                   {bif, list_to_atom(OpString), L, erlang, OpAtom};
      {'/', L} ->  {bif, '/', L, erlang, 'div'};
      {eq, L} ->   {bif, '=:=', L, erlang, '=:='};
      {gt, L} ->   {bif, '>', L, erlang, '>'};
      {lt, L} ->   {bif, '<', L, erlang, '<'};
      {gte, L} ->  {bif, '>=', L, erlang, '>='};
      {lte, L} ->  {bif, '=<', L, erlang, '=<'};
      {neq, L} ->  {bif, '!=', L, erlang, '/='}
    end,
    #alpaca_apply{type=undefined,
                  line=term_line(Name),
                  expr=Name,
                  args=[A, B]}.

make_define([#a_sym{}=Name|A], Expr, Level) ->
    L = line(Name),
    case validate_args(L, A) of
        {ok, []} ->
            %% If this is a zero-arg function, at the toplevel, it's a value
            %% and therefore its body must be restricted to literals only
            case {Level, is_literal(Expr)} of
                {top, false} ->
                    {error, non_literal_value, Name, Expr};
                _ ->
                    #alpaca_binding{
                       name=Name,
                       line=L,
                       bound_expr=Expr}
            end;
        {ok, Args} ->
            #alpaca_binding{
               line=L,
               name=Name,
               bound_expr=#alpaca_fun{
                             line=L,
                             arity=length(Args),
                             versions=[#alpaca_fun_version{
                                          line=L,
                                          args=Args,
                                          body=Expr}]}}
    end;
make_define([SingleTerm], Expr, _Lvl) ->
    #alpaca_match{
       line=term_line(SingleTerm),
       match_expr=Expr,
       clauses=[#alpaca_clause{pattern=SingleTerm}]};
make_define([BadName|Args], _Expr, _) ->
    {error, {invalid_function_name, BadName, Args}}.

%% Unit is only valid for single argument functions as a way around
%% the problem of distinguishing between nullary functions and
%% variable bindings in let forms:
validate_args(_L, [#a_unit{}]=Args) ->
    {ok, Args};
validate_args(L, Args) ->
    validate_args(L, Args, []).

validate_args(_L, [], GoodArgs) ->
    {ok, lists:reverse(GoodArgs)};
validate_args(L, [#alpaca_fun{}=F|_], _) ->
    return_error(L, {invalid_fun_parameter, F});
validate_args(L, [#alpaca_match{}=E|_], _) ->
    return_error(L, {invalid_fun_parameter, E});
validate_args(L, [#alpaca_spawn{}=E|_], _) ->
    return_error(L, {invalid_fun_parameter, E});
validate_args(L, [A|T], Memo) ->
    validate_args(L, T, [A|Memo]).

%% Determine whether an expression is a literal
is_literal(#a_unit{}) -> true;
is_literal(#a_atom{}) -> true;
is_literal(#a_int{}) -> true;
is_literal(#a_str{}) -> true;
is_literal(#a_flt{}) -> true;
is_literal(#alpaca_fun{}) -> true;
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
is_literal(#a_bool{}) -> true;
is_literal({chars, _, _}) -> true;
is_literal(#alpaca_tuple{values=Members}) ->
    all_literals(Members);
is_literal(_) -> false.

all_literals([]) -> true;
all_literals([M|Rest]) ->
    case is_literal(M) of
        true -> all_literals(Rest);
        false -> false
    end.

make_binding(Def, Expr) ->
    case Def of
	#alpaca_binding{} ->
	    Def#alpaca_binding{body=Expr};
	#alpaca_match{clauses=[C]} ->
	    Def#alpaca_match{clauses=[C#alpaca_clause{result=Expr}]}
    end.

term_line(Term) ->
    alpaca_ast_gen:term_line(Term).

bin_to_atom(B) when is_binary(B) ->
    binary_to_atom(B, utf8).

add_qualifier(#alpaca_bits{}=B, {size, #a_int{val=I}}) ->
    B#alpaca_bits{size=I, default_sizes=false};
add_qualifier(#alpaca_bits{}=B, {unit, #a_int{val=I}}) ->
    B#alpaca_bits{unit=I, default_sizes=false};
add_qualifier(#alpaca_bits{}=B, {bin_endian, _, E}) ->
    B#alpaca_bits{endian=bin_to_atom(E)};
add_qualifier(#alpaca_bits{}=B, {bin_type, Enc}) ->
    B#alpaca_bits{type=bin_to_atom(Enc)};
add_qualifier(#alpaca_bits{}=B, {bin_sign, _, S}) ->
    B#alpaca_bits{sign=bin_to_atom(S)}.

make_vars_for_concrete_types(Vars, Line) ->
    F = fun({type_var, _, _}=V, {Vs, VarNum}) ->
                {[V|Vs], VarNum};
           (Expr, {Vs, VarNum}) ->
                VN = {synthetic, ":SynthTypeVar_" ++ integer_to_list(VarNum)},
                {[{{type_var, Line, VN}, Expr}|Vs], VarNum + 1}
        end,
    {Vs, _} = lists:foldl(F, {[], 0}, Vars),
    lists:reverse(Vs).

type_arity_error(L, Typ, Params) ->
    return_error(L, {wrong_type_arity, Typ, length(Params)}).

symbol_name({symbol, S}) ->
    ast:symbol_name(S);
symbol_name(S) ->
    ast:symbol_name(S).

symbol_line_name({symbol, S}) ->
    {ast:line(S), ast:symbol_name(S)};
symbol_line_name({infixl, L, N}) ->
    {L, infix_name(N)};
symbol_line_name({infixr, L, N}) ->
    {L, infix_name(N)}.

line({symbol, S}) ->
    ast:line(S);
line(X) ->
    ast:line(X).

infix_name(C) ->
  BinC = unicode:characters_to_binary(C, utf8),
  <<"("/utf8, BinC/binary, ")"/utf8>>.

%% Some patterns may be illegal, such as unsized binaries before the final segment
validate_match_pattern(#alpaca_binary{segments=Segments}=Ptn) ->
    case validate_bin_segments(Segments) of
        ok -> Ptn;
        E -> E
    end;
validate_match_pattern(Ptn) -> Ptn.

validate_bin_segments([_Ptn]) -> ok;
validate_bin_segments([Ptn | Rem]) ->
    case Ptn of
        #alpaca_bits{default_sizes=true, type=T, value=#a_sym{}=S}
        when T == binary; T == utf8 ->
            return_error(line(S), unsized_binary_before_end);
        _ -> validate_bin_segments(Rem)
    end.


%% Yecc requires tuples to start with a token name it can recognize so we can't
%% actually product and use Alpaca AST nodes straight from Leex.
unwrap({unit, U}) ->
    U;
unwrap({boolean, B}) ->
    B;
unwrap({atom, A}) ->
    A;
unwrap({int, I}) ->
    I;
unwrap({float, F}) ->
    F;
unwrap({string, S}) ->
    S;
unwrap({symbol, S}) ->
    S;
unwrap(X) ->
    X.


