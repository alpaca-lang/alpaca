%% This is based on the unsound type checker in 
%% http://okmij.org/ftp/ML/generalization.html with some influence
%% from https://github.com/tomprimozic/type-systems/blob/master/algorithm_w
%% where the arrow type is concerned.  The implementation here is not complete
%% as it's unsound as stated in Oleg's post above.  See notes in the typ_of/2
%% tests at the end.

-module(unsound_typer).

-include("mlfe_ast.hrl").

-export([new_env/0, typ_of/2]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

-type typ_name() :: atom().

-type qvar()   :: {qvar, typ_name()}.
-type tvar()   :: {unbound, typ_name()}
                | {link, typ()}.
%% list of parameter types, return type:
-type t_arrow() :: {t_arrow, list(typ()), typ()}.

-type t_const() :: t_int.

-type typ() :: qvar()
             | tvar()
             | t_arrow()
             | t_const().

%% Check to see if the first type is referenced anywhere in the chain
%% of the second.  If the second type isn't a link, there's no circular
%% reference.
-spec occurs(typ(), typ()) -> ok | {error, atom()}.
occurs({unbound, _} = T1, {link, T1}) ->
    {error, cyclic_type_var};
occurs({unbound, _} = T1, {link, Next}) ->
    occurs(T1, Next);
occurs(_, _) ->
    ok.

-spec unify(typ(), typ()) -> {typ(), typ()} | {error, atom()}.
unify(T, T) ->
    T;
unify({unbound, _} = T1, T2) ->
    case occurs(T1, T2) of
        ok -> 
            {{link, T2}, T2};
        E ->
            E
    end;
unify(T1, {unbound, _} = T2) ->
    case occurs(T1, T2) of
        ok -> 
            {T1, {link, T1}};
        E ->
            E
    end;
unify({t_arrow, A1, A2}, {t_arrow, B1, B2}) ->
    case unify(A1, B1) of
        {error, _} = E ->
            E;
        {ResA1, ResB1} ->
            case unify(A2, B2) of
                {error, _} = E ->
                    E;
                {ResA2, ResB2} ->
                    {{t_arrow, ResA1, ResA2}, {t_arrow, ResB1, ResB2}}
            end
    end;
unify(_, _) ->
    {error, cannot_unify}.

%% The list is {var name, var type}
-type env() :: {integer(), list({atom(), atom()})}.

-spec new_env() -> env().
new_env() ->
    {0, []}.

-spec inst(VarName :: atom(), Env :: env()) -> {typ(), env()} | {error, atom()}.
inst(VarName, {C, L}) ->
    case proplists:get_value(VarName, L, {error, bad_variable_name, VarName}) of
        {error, _, _} = E ->
            E;
        {_, TypName} ->
            NewL = [V || {Name, _} = V <- L, Name =/= VarName],
            T = {unbound, TypName},
            {T, {C, [{VarName, T}|NewL]}};
        {t_arrow, _, _} = T ->
            NewL = [V || {Name, _} = V <- L, Name =/= VarName],
            {T, {C, [{VarName, T}|NewL]}}
    end.

-spec new_var(Env :: env()) -> {tvar(), env()}.
new_var({C, L}) ->
    N = list_to_atom("t" ++ integer_to_list(C)),
    TVar = {unbound, N},
    {TVar, {C+1, L}}.

-spec gen(typ()) -> typ().
gen({unbound, N}) ->
    {qvar, N};
gen({link, T}) ->
    gen(T);
gen({t_arrow, PTs, T2}) ->
    {t_arrow, [gen(T) || T <- PTs], gen(T2)};
gen(T) ->
    T.

%% Simple function that takes the place of a foldl over a list of
%% arguments to an apply.
typ_list([], Env, Memo) ->
    {Env, Memo};
typ_list([H|T], Env, Memo) ->
    {Typ, Env2} = typ_of(Env, H),
    typ_list(T, Env2, [Typ|Memo]).

-spec typ_of(Env::env(), Exp::mlfe_expression()) -> {typ(), env()} | {error, atom()}.
typ_of(Env, {int, _, _}) ->
    {t_int, Env};
typ_of(Env, {symbol, _, N}) ->
    inst(N, Env);

typ_of(Env, #mlfe_apply{name={symbol, _, Name}=N, args=As}) ->
    {TypF, Env2} = typ_of(Env, N),
    {Env3, ArgTypes} = typ_list(As, Env2, []),
    {TypRes, Env4} = new_var(Env3),

    %% ArgTypes is in reverse order to As from typ_list/3:
    Arrow = {t_arrow, lists:reverse(ArgTypes), TypRes},
    case unify(TypF, Arrow) of
        {error, _} = E ->
            E;
        {_T1, T2} ->
            {C, L} = Env4,
            {TypRes, {C, [{Name, T2}|[TT || {NN, _} = TT <- L, NN =/= N]]}}
    end;

%% This can't handle recursive functions since the function name
%% is not bound in the environment:
typ_of(Env, #mlfe_fun_def{args=Args, body=Body}) ->
    {_, NewEnv} = args_to_types(Args, Env, []),
    {T, NewEnv2} = typ_of(NewEnv, Body),

    %% Some types may have been unified in NewEnv2 so we need
    %% to replace their occurences in ArgTypes.  This is getting
    %% around the lack of reference cells.
    {ArgTypesPass2, NewEnv2} = args_to_types(Args, NewEnv2, []),

    JustTypes = [Typ || {_, Typ} <- ArgTypesPass2],
    {{t_arrow, JustTypes, T}, NewEnv2};

%% A let binding inside a function:
typ_of(Env, #fun_binding{
               def=#mlfe_fun_def{name={symbol, _, N}}=E, 
               expr=E2}) ->
    {TypE, {C, Bindings}} = typ_of(Env, E),
    typ_of({C, [{N, gen(TypE)}|Bindings]}, E2);

%% A var binding inside a function:
typ_of(Env, #var_binding{name={symbol, _, N}, to_bind=E1, expr=E2}) ->
    {TypE, {C, Bindings}} = typ_of(Env, E1),
    typ_of({C, [{N, gen(TypE)}|Bindings]}, E2).
    
%% Find or make a type for each arg from a function's
%% argument list.
args_to_types([], Env, Memo) ->
    {lists:reverse(Memo), Env};
args_to_types([{unit, _}|T], Env, Memo) ->
    %% have to give t_unit a name for filtering later:
    args_to_types(T, Env, [{unit, t_unit}|Memo]);
args_to_types([{symbol, _, N}|T], {_, Vs} = Env, Memo) ->
    case proplists:get_value(N, Vs) of
        undefined ->
            {Typ, {C, L}} = new_var(Env),
            args_to_types(T, {C, [{N, Typ}|L]}, [{N, Typ}|Memo]);
        Typ ->
            args_to_types(T, Env, [{N, Typ}|Memo])
    end.


-ifdef(TEST).

occurs_test_() ->
    [?_assertEqual(ok, occurs({unbound, t1}, {unbound, t2})),
     ?_assertEqual(ok, occurs({unbound, t1}, {qvar, t2})),
     ?_assertEqual({error, cyclic_type_var}, 
                   occurs({unbound, t1}, {link, {unbound, t1}})),
     ?_assertEqual({error, cyclic_type_var},
                   occurs({unbound, t3}, {link, {link, {unbound, t3}}}))
    ].

unify_test_() ->
    [?_assertEqual({{link, {qvar, t2}}, {qvar, t2}}, 
                   unify({unbound, t1}, {qvar, t2})),
     ?_assertEqual({{link, {unbound, t2}}, {unbound, t2}},
                   unify({unbound, t1}, {unbound, t2})),
     ?_assertEqual({{t_arrow, {link, {unbound, t3}}, {link, {unbound, t4}}},
                    {t_arrow, {unbound, t3},{unbound, t4}}},
                   unify(
                     {t_arrow, {unbound, t1}, {unbound, t2}},
                     {t_arrow, {unbound, t3}, {unbound, t4}}))
    ].

from_code(C) ->
    {ok, E} = parser:parse(scanner:scan(C)),
    E.

%% There are a number of expected "unbound" variables here.  I think this
%% is due to the deallocation problem as described in the first post
%% referenced at the top.
typ_of_test_() ->
    [?_assertMatch({{t_arrow, [t_unit], t_int}, _}, 
                   typ_of(new_env(), from_code("x () = 0")))
    , ?_assertMatch({{t_arrow, 
                       [{unbound, t0}], 
                       {t_arrow, [{qvar, t1}], {qvar, t1}}}, 
                      _},
                    typ_of(new_env(), from_code("f x = let y z = z in y")))
    , ?_assertMatch({{t_arrow,[{unbound,t0}],{unbound,t0}}, _}, 
                     typ_of(new_env(), from_code("f x = let y = x in y")))
    , ?_assertMatch({{t_arrow, 
                      [{t_arrow, [{unbound, t1}], {unbound, t2}}],
                      {t_arrow, [{qvar, t1}],{qvar, t2}}}, _},
                    typ_of(new_env(), from_code("f x = let y z = x z in y")))
    , ?_assertMatch({{t_arrow, 
                      [{t_arrow, [{unbound, t1}], {unbound, t2}},
                       {unbound, t1}], 
                      {unbound, t2}}, _},
                    typ_of(new_env(), from_code("f x y = x y")))
    ].

-endif.
