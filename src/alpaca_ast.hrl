%%% -*- mode: erlang;erlang-indent-level: 4;indent-tabs-mode: nil -*-
%%% ex: ft=erlang ts=4 sw=4 et
%%%
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

%%% ## Type-Tracking Data Types
%%%
%%% These are all of the specs the typer uses to track Alpaca types.

-type typ_name() :: atom().

-type qvar()   :: {qvar, typ_name()}.
-type tvar()   :: {unbound, typ_name(), integer()}
                | {link, typ()}.
%% list of parameter types, return type:
-type t_arrow() :: {t_arrow, list(typ()), typ()}.

-record(adt, {name=undefined :: undefined|string(),
              module=undefined :: atom(),
              vars=[] :: list({string(), typ()}),
              members=[] :: list(typ())}).
-type t_adt() :: #adt{}.

-type t_adt_constructor() :: {t_adt_cons, string()}.

%% Processes that are spawned with functions that are not receivers are not
%% allowed to be sent messages.
-type t_pid() :: {t_pid, typ()}.

-type t_receiver() :: {t_receiver, typ(), typ()}.

-type t_list() :: {t_list, typ()}.

-type t_map() :: {t_map, typ(), typ()}.

-type t_tuple() :: {t_tuple, list(typ())}.

%% pattern, optional guard, result.  Currently I'm doing nothing with
%% present guards.
%% TODO:  the guards don't need to be part of the type here.  Their
%%        only role in typing is to constrain the pattern's typing.
-type t_clause() :: {t_clause, typ(), t_arrow()|undefined, typ()}.

%%% `t_rec` is a special type that denotes an infinitely recursive function.
%%% Since all functions here are considered recursive, the return type for
%%% any function must begin as `t_rec`.  `t_rec` unifies with anything else by
%%% becoming that other thing and as such should be in its own reference cell.
-type t_const() :: t_rec
                 | t_int
                 | t_float
                 | t_atom
                 | t_bool
                 | t_string
                 | t_chars
                 | t_unit.

-type typ() :: undefined
             | qvar()
             | tvar()
             | t_arrow()
             | t_adt()
             | t_adt_constructor()
             | t_const()
             | t_binary
             | t_list()
             | t_map()
             | t_record()
             | t_tuple()
             | t_clause()
             | t_pid()
             | t_receiver()
             | alpaca_typer:cell().  % a reference cell for a type.

%%% ## ALPACA AST Nodes

-record(alpaca_comment, {
          multi_line=false :: boolean(),
          line=0 :: integer(),
          text="" :: string()}).
-type alpaca_comment() :: #alpaca_comment{}.


-type alpaca_symbol() :: {symbol, integer(), string()}.
%% Reference to a symbol in a different module.  Arity can be 'none'
%% if the user wishes to default to the first exported version of the
%% reference.
-record(alpaca_far_ref, {
          line=0 :: integer(),
          module=undefined :: atom(),
          name="" :: string(),
          arity=none :: none | integer()}).
-type alpaca_far_ref() :: #alpaca_far_ref{}.

-type alpaca_unit() :: {unit, integer()}.
-type alpaca_int() :: {'Int', #{line := integer(), val := integer()}}.
-type alpaca_float() :: {float, integer(), float()}.
-type alpaca_number() :: alpaca_int()|alpaca_float().
-type alpaca_bool() :: {bool, integer(), boolean()}.
-type alpaca_atom() :: {atom, integer(), atom()}.

-type alpaca_error() :: {raise_error,
                       integer(),
                       throw|error|exit,
                       alpaca_value_expression()}.

%%% The variable _, meaning "don't care":
-type alpaca_any() :: {any, integer()}.

-type alpaca_string() :: {string, integer(), string()}.

-type alpaca_const() :: alpaca_unit()
                    | alpaca_any()
                    | alpaca_number()
                    | alpaca_bool()
                    | alpaca_atom()
                    | alpaca_string()
                      .

%%% ### Binaries

-record(alpaca_binary, {line=0 :: integer(),
                      segments=[] :: list(alpaca_bits())}).
-type alpaca_binary() :: #alpaca_binary{}.

-type alpaca_bits_type() :: int | float | binary | utf8.

-record(alpaca_bits, {line=0 :: integer(),
                    %% Used to signal whether or not the bitstring is simply
                    %% using default size and unit values.  If it is *not*
                    %% and the `type` is `binary` *and* the bitstring is the
                    %% last segment in a binary, it's size must be set to
                    %% `'all'` with unit 8 to capture all remaining bits.
                    %% This is in keeping with how Erlang compiles to Core
                    %% Erlang.
                    default_sizes=true :: boolean(),
                    value={symbol, 0, ""} :: alpaca_symbol()|alpaca_number()|alpaca_string(),
                    size=8 :: non_neg_integer()|all,
                    unit=1 :: non_neg_integer(),
                    type=int :: alpaca_bits_type(),
                    sign=unsigned :: signed | unsigned,
                    endian=big :: big | little | native}).
-type alpaca_bits() :: #alpaca_bits{}.

%%% ### AST Nodes For Types
%%%
%%% AST nodes that describe the basic included types and constructs for
%%% defining and instantiating ADTs (type constructors).

-type alpaca_base_type() :: t_atom
                        | t_int
                        | t_float
                        | t_string
                        | t_pid
                        | t_bool
                        | t_chars
                        | t_unit.

-type alpaca_type_name() :: {type_name, integer(), string()}.
-type alpaca_type_var()  :: {type_var, integer(), string()}.

-record(alpaca_type_tuple, {
          members=[] :: list(alpaca_base_type()
                             | alpaca_type_var()
                             | alpaca_poly_type())
         }).
-type alpaca_type_tuple() :: #alpaca_type_tuple{}.

-type alpaca_list_type() :: {t_list, alpaca_base_type()|alpaca_poly_type()}.

-type alpaca_map_type() :: {t_map,
                          alpaca_base_type()|alpaca_poly_type(),
                          alpaca_base_type()|alpaca_poly_type()}.

-type alpaca_pid_type() :: {t_list, alpaca_base_type()|alpaca_poly_type()}.

-type alpaca_poly_type() :: alpaca_type()
                        | alpaca_type_tuple()
                        | alpaca_list_type()
                        | alpaca_map_type()
                        | alpaca_pid_type().

%%% ### Record Type Tracking
%%%
%%% These will do double-duty for both defining record types for ADTs
%%% as well as to type records as they occur.
-record(t_record_member, {
          name=undefined :: atom(),
          type=undefined :: typ()}).
-type t_record_member() :: #t_record_member{}.

-record(t_record, {
          is_pattern=false :: boolean(),
          members=[] :: list(t_record_member()),
          row_var=undefined :: typ()}).

-type t_record() :: #t_record{}.

%%% ADT Type Tracking

-record(type_constructor, {
          line=0 :: integer(),
          module=undefined :: atom(),
          name="" :: string()
         }).
-type alpaca_constructor_name() :: #type_constructor{}.

-record(alpaca_constructor, {
          type=undefined :: typ() | alpaca_type(),
          name=#type_constructor{} :: alpaca_constructor_name(),
          arg=none :: none
                    | alpaca_base_type()
                    | alpaca_type_var()
                    | alpaca_type()
                    | alpaca_type_tuple()
         }).
-type alpaca_constructor() :: #alpaca_constructor{}.

-type alpaca_types() :: alpaca_type()
                    | alpaca_type_tuple()
                    | alpaca_base_type()
                    | alpaca_list_type()
                    | alpaca_map_type()
                    | alpaca_pid_type().

-record(alpaca_type, {
          line=0 :: integer(),
          module=undefined :: atom(),
          name={type_name, -1, ""} :: alpaca_type_name(),
          vars=[]                  :: list(alpaca_type_var()
                                           | {alpaca_type_var(), typ()}),
          members=[]               :: list(alpaca_constructor()
                                           | alpaca_type_var()
                                           | alpaca_types())
         }).
-type alpaca_type() :: #alpaca_type{}.

-record(alpaca_type_apply, {
          type=undefined :: typ(),
          name=#type_constructor{} :: alpaca_constructor_name(),
          arg=none :: none | alpaca_expression()}).
-type alpaca_type_apply() :: #alpaca_type_apply{}.

%%% ### Lists

-record(alpaca_cons, {type=undefined :: typ(),
                    line=0 :: integer(),
                    head=undefined :: undefined|alpaca_expression(),
                    tail={nil, 0} :: alpaca_expression()
                   }).

-type alpaca_cons() :: #alpaca_cons{}.
-type alpaca_nil() :: {nil, integer()}.
-type alpaca_list() :: alpaca_cons() | alpaca_nil().

%%% ### Maps
%%%
%%% For both map literals and map patterns

-record(alpaca_map_pair, {type=undefined :: typ(),
                        line=0 :: integer(),
                        is_pattern=false :: boolean(),
                        key=undefined :: alpaca_value_expression(),
                        val=undefined :: alpaca_value_expression()}).
-type alpaca_map_pair() :: #alpaca_map_pair{}.

%% The `structure` field tracks what we're actually using the map for.
%% The code generation stage will add a member to the compiled map that
%% indicates what the purpose of the map is so that pattern matches can
%% be correct, e.g. we don't want the order of maps and records to matter
%% in a pattern match because then compilation details are a concern for
%% a user.
-record(alpaca_map, {type=undefined :: typ(),
                   line=0 :: integer(),
                   is_pattern=false :: boolean(),
                   structure=map :: map | record,
                   pairs=[] :: list(alpaca_map_pair())}).
-type alpaca_map() :: #alpaca_map{}.

-record(alpaca_map_add, {type=undefined :: typ(),
                       line=0 :: integer(),
                       to_add=#alpaca_map_pair{} :: alpaca_map_pair(),
                       existing=#alpaca_map{} :: alpaca_value_expression()}).
-type alpaca_map_add() :: #alpaca_map_add{}.

%%% ### Tuples

-record(alpaca_tuple, {type=undefined :: typ(),
                     arity=0 :: integer(),
                     values=[] :: list(alpaca_expression())
                    }).
-type alpaca_tuple() :: #alpaca_tuple{}.

%%% ### Record AST Nodes

-record(alpaca_record_member, {
          line=-1 :: integer(),
          name=undefined :: atom(),
          type=undefined :: typ(),
          val={symbol, -1, ""} :: alpaca_value_expression()}).
-type alpaca_record_member() :: #alpaca_record_member{}.

-record(alpaca_record, {arity=0 :: integer(),
                      line=0 :: integer(),
                      is_pattern=false :: boolean(),
                      members=[] :: list(alpaca_record_member())}).
-type alpaca_record() :: #alpaca_record{}.

-record(alpaca_record_transform, {
          line=-1 :: integer(),
          additions=[] :: list(alpaca_record_member()),
          existing :: alpaca_value_expression()}).
-type alpaca_record_transform() :: #alpaca_record_transform{}.

%%% Pattern Matching

-type type_check() :: is_integer
                    | is_float
                    | is_atom
                    | is_bool
                    | is_list
                    | is_string
                    | is_chars
                    | is_binary.

%% TODO:  revisit this in alpaca_typer.erl as well as scanning and parsing:
-record(alpaca_type_check, {type=undefined :: undefined|type_check(),
                          line=0 :: integer(),
                          expr=undefined :: undefined|alpaca_symbol()}).
-type alpaca_type_check() :: #alpaca_type_check{}.

-record(alpaca_clause, {type=undefined :: typ(),
                      line=0 :: integer(),
                      pattern={symbol, 0, "_"} :: alpaca_expression(),
                      guards=[] :: list(alpaca_expression()),
                      result={symbol, 0, "_"} :: alpaca_expression()
                     }).
-type alpaca_clause() :: #alpaca_clause{}.

-record(alpaca_match, {type=undefined :: typ(),
                     line=0 :: integer(),
                     match_expr={symbol, 0, "_"} :: alpaca_expression(),
                     clauses=[#alpaca_clause{}] :: nonempty_list(alpaca_clause())
                    }).
-type alpaca_match() :: #alpaca_match{}.

%%% ### Erlang FFI
%%%
%%% A call to an Erlang function via the Foreign Function Interface.
%%% Only the result of these calls is typed.
-record(alpaca_ffi, {type=undefined :: typ(),
                   module={atom, 0, ""} :: alpaca_atom(),
                   function_name=undefined :: undefined|alpaca_atom(),
                   args={nil, 0}  :: alpaca_list(),
                   clauses=[] :: list(alpaca_clause())
                  }).
-type alpaca_ffi() :: #alpaca_ffi{}.

%%% ### Processes

-record(alpaca_spawn, {type=undefined :: typ(),
                     line=0 :: integer(),
                     module=undefined :: atom(),
                     from_module=undefined :: atom(),
                     function={symbol, 0, ""} :: alpaca_symbol(),
                     args=[] :: list(alpaca_expression())}).
-type alpaca_spawn() :: #alpaca_spawn{}.

-record(alpaca_send, {type=undefined :: typ(),
                    line=0 :: integer(),
                    message=undefined :: undefined|alpaca_value_expression(),
                    pid=undefined :: undefined|alpaca_expression()}).
-type alpaca_send() :: #alpaca_send{}.

-record(alpaca_receive, {type=undefined :: typ(),
                       line=0 :: integer(),
                       clauses=[#alpaca_clause{}] :: nonempty_list(alpaca_clause()),
                       timeout=infinity :: infinity | integer(),
                       timeout_action=undefined :: undefined
                                                 | alpaca_value_expression()}).
-type alpaca_receive() :: #alpaca_receive{}.

%%% ### Module Building Blocks

-record(alpaca_test, {type=undefined :: typ(),
                      line=0 :: integer(),
                      name={string, 0, ""} :: alpaca_string(),
                      expression={unit, 0} :: alpaca_expression()}).
-type alpaca_test() :: #alpaca_test{}.

%%% Expressions that result in values:
-type alpaca_value_expression() :: alpaca_const()
                               | alpaca_symbol()
                               | alpaca_far_ref()
                               | alpaca_list()
                               | alpaca_binary()
                               | alpaca_map()
                               | alpaca_map_add()
                               | alpaca_record()
                               | alpaca_record_transform()
                               | alpaca_tuple()
                               | alpaca_apply()
                               | alpaca_type_apply()
                               | alpaca_match()
                               | alpaca_receive()
                               | alpaca_clause()
                               | alpaca_fun()
                               | alpaca_spawn()
                               | alpaca_send()
                               | alpaca_ffi().

-type alpaca_expression() :: alpaca_comment()
                         | alpaca_value_expression()
                         | alpaca_binding()
                         | alpaca_type_check()
                         | alpaca_binding()
                         | alpaca_type_import()
                         | alpaca_type_export()
                         | alpaca_error().

%% When calling BIFs like erlang:'+' it seems core erlang doesn't want
%% the arity specified as part of the function name.  alpaca_bif_name()
%% is a way to indicate what the ALPACA function name is and the corresponding
%% actual Erlang BIF.  Making the distinction between the ALPACA and Erlang
%% name to support something like '+' for integers and '+.' for floats.
-type alpaca_bif_name() ::
        { bif
        , AlpacaFun::atom()
        , Line::integer()
        , Module::atom()
        , ErlangFun::atom()
        }.

%%% A function application can occur in one of 4 ways:
%%%
%%% - an Erlang BIF
%%% - intra-module, a function defined in the module it's being called
%%%   within or one in scope from a let binding
%%% - inter-module (a "call" in core erlang), calling a function defined
%%%   in a different module
%%% - a function bound to a variable
%%%
%%% The distinction is particularly important between the first and third
%%% since core erlang wants the arity specified in the first case but _not_
%%% in the third.

-record(alpaca_apply, {type=undefined :: typ(),
                       line=0 :: integer(),
                       expr=undefined :: undefined
                                       | {alpaca_symbol(), integer()}
                                       | {atom(), alpaca_symbol(), integer()}
                                       | alpaca_symbol()
                                       | alpaca_bif_name()
                                       | alpaca_expression(),
                     args=[] :: list(alpaca_expression())
                    }).
-type alpaca_apply() :: #alpaca_apply{}.

-record(alpaca_fun_version, {
          line=0 :: integer(),
          args=[] :: list(alpaca_value_expression()),
          guards=[] :: list(alpaca_expression()),
          body=undefined :: undefined|alpaca_expression()
         }).

%% The name field in an #alpaca_fun{} is there for the typer's convenience.
%% When typing an #alpaca_binding{}, the typer inserts the bound name into the
%% function to enable "let rec" behaviour.  We could relax this later to allow
%% for non-recursive let behaviour but I can't think of a good reason to go for
%% that at the immediate moment.
-record(alpaca_fun, {
          line=0 :: integer(),
          type=undefined :: typ(),
          arity=0 :: integer(),
          name=undefined :: undefined | string(),
          versions=[] :: list(#alpaca_fun_version{})
         }).
-type alpaca_fun() :: #alpaca_fun{}.

-record(alpaca_type_signature, {
          line=0 :: integer(),
          name=undefined :: undefined | alpaca_symbol(),
          type=undefined :: typ(),
          vars=undefined :: list(alpaca_type_var())
         }).

-type alpaca_type_signature() :: #alpaca_type_signature{}.

%% `body` remains `undefined` for top-level expressions and otherwise for
%% things like function and variable bindings within a top-level function.
-record(alpaca_binding, {
          line=0 :: integer(),
          name=undefined :: undefined | alpaca_symbol(),
          type=undefined :: typ(),
          bound_expr=undefined :: undefined | alpaca_expression(),
          body=undefined :: undefined | alpaca_expression(),
          signature=undefined :: alpaca_type_signature()
         }).

-type alpaca_binding() :: #alpaca_binding{}.

-record(alpaca_type_import, {module=undefined :: atom(),
                           type=undefined :: string()}).
-type alpaca_type_import() :: #alpaca_type_import{}.

-record(alpaca_type_export, {line=0 :: integer(),
                            names=[] :: list(string())}).
-type alpaca_type_export() :: #alpaca_type_export{}.

%% rename_map is a map from generated function and variable names to their
%% original names.
-record(alpaca_module, {
          name=no_module :: atom(),
          filename=undefined :: string() | undefined,
          rename_map=maps:new() :: map(),
          function_exports=[] :: list({string(), integer()}|string()),
          function_imports=[] :: list({string(), {atom(), integer()}|string()}),
          types=[] :: list(alpaca_type()),
          type_imports=[] :: list(alpaca_type_import()),
          type_exports=[] :: list(string()),
          functions=[] :: list(alpaca_binding()),
          tests=[] :: list(alpaca_test()),
          precompiled=false :: boolean(),
          hash=undefined :: binary() | undefined,
          typed=false :: boolean()
         }).
-type alpaca_module() :: #alpaca_module{}.
