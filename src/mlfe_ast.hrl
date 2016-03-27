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

-record(mlfe_infix, {type :: atom(),
                     operator :: {atom(), integer()},
                     left :: mlfe_expression(),
                     right :: mlfe_expression()
                    }).
-type mlfe_infix() :: #mlfe_infix{}.

-record(mlfe_cons, {type=undefined :: atom(),
                    head :: mlfe_expression(),
                    tail :: mlfe_cons()
                          | mlfe_nil()
                   }).

-type mlfe_cons() :: #mlfe_cons{}.
-type mlfe_nil() :: {nil, integer()}.
-type mlfe_list() :: mlfe_cons() | mlfe_nil().

-record(mlfe_tuple, {type=undefined :: atom(),
                     arity :: integer(),
                     values :: list(mlfe_expression)
                    }).
-type mlfe_tuple() :: #mlfe_tuple{}.

-record(struct_member, {type :: atom(),
                        name :: atom()
                       }).
-type struct_member() :: #struct_member{}.

-type mlfe_struct_def() :: list(struct_member()).

-record(mlfe_clause, {type :: atom(),
                      pattern :: mlfe_expression(),
                      result :: mlfe_expression()
                     }).
-type mlfe_clause() :: #mlfe_clause{}.

-record(mlfe_match, {type :: atom(),
                     match_expr :: mlfe_expression(),
                     clauses :: list(mlfe_clause())
                    }).
-type mlfe_match() :: #mlfe_match{}.

-type mlfe_expression() :: mlfe_const()
                         | mlfe_infix()
                         | mlfe_apply()
                         | mlfe_list()
                         | mlfe_tuple()
                         | mlfe_match()
                         | mlfe_binding()
                           .

-record(fun_binding, {def :: mlfe_fun_def(),
                      expr :: mlfe_expression()
                     }).
                      
-record(var_binding, {type=undefined :: atom(),
                      name :: mlfe_symbol(),
                      to_bind :: mlfe_expression(),
                      expr :: mlfe_expression()
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

-record(mlfe_apply, {type=undefined :: undefined | typer:typ(),
                     name :: {mlfe_symbol(), integer()}
                           | {atom(), mlfe_symbol(), integer()}
                           | mlfe_symbol()
                           | mlfe_bif_name(),
                     args :: list(mlfe_expression())
                     }).
-type mlfe_apply() :: #mlfe_apply{}.

-record (mlfe_fun_def, {
           type=undefined :: typer:typ()|undefined,
           name :: mlfe_symbol(),
           args :: list(mlfe_symbol())
                 | mlfe_unit(),
           body :: mlfe_expression()
          }).

-type mlfe_fun_def() :: #mlfe_fun_def{}.

-record(mlfe_module, {
          name=no_module :: atom(),
          function_exports=[] :: list({atom(), integer()}),
          functions=[] :: list(mlfe_fun_def())
         }).
-type mlfe_module() :: #mlfe_module{}.
