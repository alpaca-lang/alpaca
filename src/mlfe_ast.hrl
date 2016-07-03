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

%%% ## Type-Tracking Data Types 
%%% 
%%% These are all of the specs the typer uses to track MLFE types.

-type typ_name() :: atom().

-type qvar()   :: {qvar, typ_name()}.
-type tvar()   :: {unbound, typ_name(), integer()}
                | {link, typ()}.
%% list of parameter types, return type:
-type t_arrow() :: {t_arrow, list(typ()), typ()}.

-record(adt, {name=undefined :: undefined|string(),
              vars=[] :: list({string(), typ()}),
              members=[] :: list(typ())}).
-type t_adt() :: #adt{}.

-type t_adt_constructor() :: {t_adt_con, string()}.

%% Processes that are spawned with functions that are not receivers are not
%% allowed to be sent messages.
-type t_pid() :: {t_pid, typ()}.

-type t_cons() :: {t_cons, typ(), t_list()}.
-type t_nil() :: t_nil.
-type t_list() :: t_cons() | t_nil().

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
                 | t_unit.

-type typ() :: undefined
             | qvar()
             | tvar()
             | t_arrow()
             | t_adt()
             | t_adt_constructor()
             | t_const()
             | t_list()
             | t_tuple()
             | t_clause()
             | typer:t_cell().  % a reference cell for a type.

%%% ## MLFE AST Nodes

-record(mlfe_comment, {
          multi_line=false :: boolean(),
          line=0 :: integer(),
          text="" :: string()}).
-type mlfe_comment() :: #mlfe_comment{}.


-type mlfe_symbol() :: {symbol, integer(), string()}.

-type mlfe_unit() :: {unit, integer()}.
-type mlfe_int() :: {int, integer(), integer()}.
-type mlfe_float() :: {float, integer(), float()}.
-type mlfe_number() :: mlfe_int()|mlfe_float().
-type mlfe_bool() :: {bool, integer(), boolean()}.
-type mlfe_atom() :: {atom, integer(), atom()}.

%%% The variable _, meaning "don't care":
-type mlfe_any() :: {any, integer()}.

-type mlfe_string() :: {string, integer(), binary()}.

-type mlfe_const() :: mlfe_unit()
                    | mlfe_any()
                    | mlfe_number()
                    | mlfe_bool()
                    | mlfe_atom()
                    | mlfe_string()
                      .

%%% ### AST Nodes For Types
%%% 
%%% AST nodes that describe the basic included types and constructs for
%%% defining and instantiating ADTs (type constructors).

-type mlfe_base_type() :: t_atom
                        | t_int
                        | t_float
                        | t_string
                        | t_pid
                        | t_bool.

-type mlfe_type_name() :: {type_name, integer(), string()}.
-type mlfe_type_var()  :: {type_var, integer(), string()}.

-record(mlfe_type_tuple, {
                         members=[] :: list(mlfe_type_var() | mlfe_type())
                        }).
-type mlfe_type_tuple() :: #mlfe_type_tuple{}.

%% Explicit built-in list type for use in ADT definitions.
-type mlfe_list_type() :: {mlfe_list, 
                           mlfe_type()
                           | mlfe_type_tuple()
                           | mlfe_type_var()
                           | mlfe_base_type()}.

-type mlfe_constructor_name() :: {type_constructor, integer(), string()}.
-record(mlfe_constructor, {type=undefined :: typ(),
                           name={type_constructor, 0, ""} :: mlfe_constructor_name(),
                           arg=none :: none
                                     | mlfe_base_type()
                                     | mlfe_type_var() 
                                     | mlfe_type() 
                                     | mlfe_type_tuple()
                          }).
-type mlfe_constructor() :: #mlfe_constructor{}.

-record(mlfe_type, {
          module=undefined :: atom(),
          name={type_name, -1, ""} :: mlfe_type_name(),
          vars=[]                  :: list(mlfe_type_var()),
          members=[]               :: list(mlfe_constructor()
                                           | mlfe_type()
                                           | mlfe_type_tuple()
                                           | mlfe_base_type()
                                           | mlfe_list_type())
         }).
-type mlfe_type() :: #mlfe_type{}.

-record(mlfe_type_apply, {type=undefined :: typ(),
                          name={type_constructor, 0, ""} :: mlfe_constructor_name(),
                          arg=none :: none | mlfe_expression()}).
-type mlfe_type_apply() :: #mlfe_type_apply{}.

%%% ### Lists

-record(mlfe_cons, {type=undefined :: typ(),
                    line=0 :: integer(),
                    head=undefined :: undefined|mlfe_expression(),
                    tail={nil, 0} :: mlfe_expression()
                   }).

-type mlfe_cons() :: #mlfe_cons{}.
-type mlfe_nil() :: {nil, integer()}.
-type mlfe_list() :: mlfe_cons() | mlfe_nil().

%%% ### Tuples

-record(mlfe_tuple, {type=undefined :: typ(),
                     arity=0 :: integer(),
                     values=[] :: list(mlfe_expression())
                    }).
-type mlfe_tuple() :: #mlfe_tuple{}.

%%% Pattern Matching

-type type_check() :: is_integer
                    | is_float
                    | is_atom
                    | is_bool
                    | is_list
                    | is_string.

%% TODO:  revisit this in mlfe_typer.erl as well as scanning and parsing:
-record(mlfe_type_check, {type=undefined :: undefined|type_check(),
                          line=0 :: integer(),
                          expr=undefined :: undefined|mlfe_symbol()}).
-type mlfe_type_check() :: #mlfe_type_check{}.

-record(mlfe_clause, {type=undefined :: typ(),
                      line=0 :: integer(),
                      pattern={symbol, 0, "_"} :: mlfe_expression(),
                      guards=[] :: list(mlfe_expression()),
                      result={symbol, 0, "_"} :: mlfe_expression()
                     }).
-type mlfe_clause() :: #mlfe_clause{}.

-record(mlfe_match, {type=undefined :: typ(),
                     line=0 :: integer(),
                     match_expr={symbol, 0, "_"} :: mlfe_expression(),
                     clauses=[#mlfe_clause{}] :: nonempty_list(mlfe_clause())
                    }).
-type mlfe_match() :: #mlfe_match{}.

%%% ### Erlang FFI
%%% 
%%% A call to an Erlang function via the Foreign Function Interface.
%%% Only the result of these calls is typed.
-record(mlfe_ffi, {type=undefined :: typ(),
                   module={atom, 0, ""} :: mlfe_atom(),
                   function_name=undefined :: undefined|mlfe_atom(),
                   args={nil, 0}  :: mlfe_list(),
                   clauses=[] :: list(mlfe_clause())
                  }).
-type mlfe_ffi() :: #mlfe_ffi{}.

%%% ### Processes

-record(mlfe_spawn, {type=undefined :: typ(),
                     line=0 :: integer(),
                     module=undefined :: atom(),
                     from_module=undefined :: atom(),
                     function={symbol, 0, ""} :: mlfe_symbol(),
                     args=[] :: list(mlfe_expression())}).
-type mlfe_spawn() :: #mlfe_spawn{}.

-record(mlfe_send, {type=undefined :: typ(),
                    line=0 :: integer(),
                    message=undefined :: undefined|mlfe_value_expression(),
                    pid=undefined :: undefined|mlfe_expression()}).
-type mlfe_send() :: #mlfe_send{}.

-record(mlfe_receive, {type=undefined :: typ(),
                       line=0 :: integer(),
                       clauses=[#mlfe_clause{}] :: nonempty_list(mlfe_clause()),
                       timeout=infinity :: infinity | integer(),
                       timeout_action=undefined :: undefined
                                                 | mlfe_value_expression()}).
-type mlfe_receive() :: #mlfe_receive{}.

%%% ### Module Building Blocks

%%% Expressions that result in values:
-type mlfe_value_expression() :: mlfe_const()
                               | mlfe_symbol()
                               | mlfe_list()
                               | mlfe_tuple()
                               | mlfe_apply()
                               | mlfe_type_apply()
                               | mlfe_match()
                               | mlfe_receive()
                               | mlfe_clause()
                               | mlfe_spawn()
                               | mlfe_send()
                               | mlfe_ffi().

-type mlfe_expression() :: mlfe_comment()
                         | mlfe_value_expression()
                         | mlfe_binding()
                         | mlfe_type_check()
                         | mlfe_binding()
                         | mlfe_fun_def()
                         | mlfe_type_import()
                           .

-record(fun_binding, {def :: mlfe_fun_def(),
                      expr :: mlfe_expression()
                     }).
                      
-record(var_binding, {type=undefined :: typ(),
                      name=undefined :: undefined|mlfe_symbol(),
                      to_bind=undefined :: undefined|mlfe_expression(),
                      expr=undefined :: undefined|mlfe_expression()
                     }).

-type fun_binding() :: #fun_binding{}.
-type var_binding() :: #var_binding{}.
-type mlfe_binding() :: fun_binding()|var_binding().

%% When calling BIFs like erlang:'+' it seems core erlang doesn't want
%% the arity specified as part of the function name.  mlfe_bif_name()
%% is a way to indicate what the MLFE function name is and the corresponding
%% actual Erlang BIF.  Making the distinction between the MLFE and Erlang
%% name to support something like '+' for integers and '+.' for floats.
-type mlfe_bif_name() :: 
        {bif, MlfeFun::atom(), Line::integer(), Module::atom(), ErlangFun::atom()}.

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

-record(mlfe_apply, {type=undefined :: typ(),
                     name=undefined :: undefined
                                     | {mlfe_symbol(), integer()}
                                     | {atom(), mlfe_symbol(), integer()}
                                     | mlfe_symbol()
                                     | mlfe_bif_name(),
                     args=[] :: list(mlfe_expression())
                     }).
-type mlfe_apply() :: #mlfe_apply{}.

-record (mlfe_fun_def, {
           type=undefined :: typ(),
           name=undefined :: undefined|mlfe_symbol(),
           args=[] :: list(mlfe_symbol() | mlfe_unit()),
           body=undefined :: undefined|mlfe_expression()
          }).

-type mlfe_fun_def() :: #mlfe_fun_def{}.

-record(mlfe_type_import, {module=undefined :: atom(),
                          type=undefined :: string()}).
-type mlfe_type_import() :: #mlfe_type_import{}.

-record(mlfe_module, {
          name=no_module :: atom(),
          function_exports=[] :: list({string(), integer()}),
          types=[] :: list(mlfe_type()),
          type_imports=[] :: list(mlfe_type_import()),
          type_exports=[] :: list(string()),
          functions=[] :: list(mlfe_fun_def())
         }).
-type mlfe_module() :: #mlfe_module{}.
