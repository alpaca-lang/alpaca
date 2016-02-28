%% This is based on the sound and eager type checker in 
%% http://okmij.org/ftp/ML/generalization.html with some influence
%% from https://github.com/tomprimozic/type-systems/blob/master/algorithm_w
%% where the arrow type and instantiation are concerned.
%% 
%% The environment gets passed around a lot because it contains both
%% the counter for type variable name generation as well as the proplist
%% of {var name, type}.
%% 
%% It's behaving as I expect so far but I need to write a lot more tests and
%% get a better intuition as to what's really going on.  Need to spend some
%% quality time with TAPL.

-module(sound_eager_typer).

-include("mlfe_ast.hrl").

-export([new_env/0, typ_of/3]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

-type typ_name() :: atom().

-type qvar()   :: {qvar, typ_name()}.
-type tvar()   :: {unbound, typ_name(), integer()}
                | {link, typ()}.
%% list of parameter types, return type:
-type t_arrow() :: {t_arrow, list(typ()), typ()}.

-type t_const() :: t_int.

-type typ() :: qvar()
             | tvar()
             | t_arrow()
             | t_const().

occurs(Label, _Level, {unbound, Label, _}) ->
    {error_circular, Label};
occurs(Label, Level, {link, Ty}) ->
    occurs(Label, Level, Ty);
occurs(_Label, Level, {unbound, N, Lvl}) ->
    {unbound, N, min(Level, Lvl)};
occurs(Label, Level, {t_arrow, Params, RetTyp}) ->
    {t_arrow, 
     lists:map(fun(T) -> occurs(Label, Level, T) end, Params),
     occurs(Label, Level, RetTyp)};
occurs(_, _, T) ->
    T.

-spec unify(typ(), typ()) -> {typ(), typ()} | {error, atom()}.
unify(T1, T2) ->
    case {T1, T2} of
        {T, T} -> T;
        {{unbound, N, _}, {unbound, N, _}}  -> {error, cannot_unify};
        {{unbound, N, Lvl}, Ty} ->
            T = occurs(N, Lvl, Ty),
            {{link, T}, Ty};
        {Ty, {unbound, N, Lvl}} ->
            T = occurs(N, Lvl, Ty),
            {Ty, {link, T}};
        {{t_arrow, A1, A2}, {t_arrow, B1, B2}} ->
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
        {_T1, _T2} ->
            io:format("Failed to unify ~w and ~w~n", [_T1, _T2]),
            {error, cannot_unify}
    end.

%% The list is {var name, var type}
-type env() :: {integer(), list({atom(), atom()})}.

-spec new_env() -> env().
new_env() ->
    {0, []}.

update_env(Name, Typ, {C, L}) ->
    {C, [{Name, Typ}|[{N, T} || {N, T} <- L, N =/= Name]]}.

-spec inst(
        VarName :: atom(), 
        Lvl :: integer(), 
        Env :: env()) -> {typ(), env()} | {error, atom()}.

inst(VarName, Lvl, {_, L} = Env) ->
    case proplists:get_value(VarName, L, {error, bad_variable_name, VarName}) of
        {error, _, _} = E ->
            E;
        T ->
            inst(T, Lvl, Env, maps:new())
    end.

%% This is modeled after instantiate/2 github.com/tomprimozic's example
%% located in the URL given at the top of this file.  The purpose of
%% CachedMap is to reuse the same instantiated unbound type variable for
%% every occurrence of the _same_ quantified type variable in a list
%% of function parameters.
%% 
%% The return is the instantiated type, the updated environment and the 
%% updated cache map.
-spec inst(typ(), integer(), env(), CachedMap::map()) -> {typ(), env(), map()} | {error, atom()}.
inst({link, Typ}, Lvl, Env, CachedMap) ->
    inst(Typ, Lvl, Env, CachedMap);
inst({unbound, _, _}=Typ, _, Env, M) ->
    {Typ, Env, M};
inst({qvar, Name}, Lvl, Env, CachedMap) ->
    case maps:get(Name, CachedMap, undefined) of
        undefined ->
            {NewVar, NewEnv} = new_var(Lvl, Env),
            {NewVar, NewEnv, maps:put(Name, NewVar, CachedMap)};
        Typ ->
            Typ
    end;
inst({t_arrow, Params, ResTyp}, Lvl, Env, CachedMap) ->
    Folder = fun(Next, {L, E, Map, Memo}) ->
                     {T, Env2, M} = inst(Next, L, E, Map),
                     {Lvl, Env2, M, [T|Memo]}
             end,
    {_, NewEnv, M, PTs} = lists:foldr(Folder, {Lvl, Env, CachedMap, []}, Params),
    {RT, NewEnv2, M2} = inst(ResTyp, Lvl, NewEnv, M),
    {{t_arrow, PTs, RT}, NewEnv2, M2}.

-spec new_var(Lvl :: integer(), Env :: env()) -> {tvar(), env()}.
new_var(Lvl, {C, L}) ->
    N = list_to_atom("t" ++ integer_to_list(C)),
    TVar = {unbound, N, Lvl},
    {TVar, {C+1, L}}.

-spec gen(integer(), typ()) -> typ().
gen(Lvl, {unbound, N, L}) when L > Lvl ->
    {qvar, N};
gen(Lvl, {link, T}) ->
    gen(Lvl, T);
gen(Lvl, {t_arrow, PTs, T2}) ->
    {t_arrow, [gen(Lvl, T) || T <- PTs], gen(Lvl, T2)};
gen(_, T) ->
    T.

%% Simple function that takes the place of a foldl over a list of
%% arguments to an apply.
typ_list([], _Lvl, Env, Memo) ->
    {Env, Memo};
typ_list([H|T], Lvl, Env, Memo) ->
    {Typ, Env2} = typ_of(Env, Lvl, H),
    typ_list(T, Lvl, Env2, [Typ|Memo]).

-spec typ_of(
        Env::env(),
        Lvl::integer(),
        Exp::mlfe_expression()) -> {typ(), env()} | {error, atom()}.

typ_of(Env, _Lvl, {int, _, _}) ->
    {t_int, Env};
typ_of(Env, Lvl, {symbol, _, N}) ->
    {T, E2, _} = inst(N, Lvl, Env),
    {T, E2};

typ_of(Env, Lvl, #mlfe_apply{name={symbol, _, Name}=N, args=As}) ->
    {TypF, Env2} = typ_of(Env, Lvl, N),
    {Env3, ArgTypes} = typ_list(As, Lvl, Env2, []),
    {TypRes, Env4} = new_var(Lvl, Env3),

    %% ArgTypes is in reverse order to As from typ_list/3:
    Arrow = {t_arrow, lists:reverse(ArgTypes), TypRes},
    case unify(TypF, Arrow) of
        {error, _} = E ->
            E;
        {_T1, T2} ->
            {C, L} = Env4,
            {TypRes, update_env(Name, T2, Env4)}
    end;

%% This can't handle recursive functions since the function name
%% is not bound in the environment:
typ_of(Env, Lvl, #mlfe_fun_def{args=Args, body=Body}) ->
    {_, NewEnv} = args_to_types(Args, Lvl, Env, []),
    {T, NewEnv2} = typ_of(NewEnv, Lvl, Body),

    %% Some types may have been unified in NewEnv2 so we need
    %% to replace their occurences in ArgTypes.  This is getting
    %% around the lack of reference cells.
    {ArgTypesPass2, NewEnv2} = args_to_types(Args, Lvl, NewEnv2, []),

    JustTypes = [Typ || {_, Typ} <- ArgTypesPass2],
    {{t_arrow, JustTypes, T}, NewEnv2};

%% A let binding inside a function:
typ_of(Env, Lvl, #fun_binding{
               def=#mlfe_fun_def{name={symbol, _, N}}=E, 
               expr=E2}) ->
    {TypE, Env2} = typ_of(Env, Lvl, E),
    typ_of(update_env(N, gen(Lvl, TypE), Env2), Lvl+1, E2);

%% A var binding inside a function:
typ_of(Env, Lvl, #var_binding{name={symbol, _, N}, to_bind=E1, expr=E2}) ->
    {TypE, Env2} = typ_of(Env, Lvl, E1),
    typ_of(update_env(N, gen(Lvl, TypE), Env2), Lvl+1, E2).
    
%% Find or make a type for each arg from a function's
%% argument list.
args_to_types([], _Lvl, Env, Memo) ->
    {lists:reverse(Memo), Env};
args_to_types([{unit, _}|T], Lvl, Env, Memo) ->
    %% have to give t_unit a name for filtering later:
    args_to_types(T, Lvl, Env, [{unit, t_unit}|Memo]);
args_to_types([{symbol, _, N}|T], Lvl, {_, Vs} = Env, Memo) ->
    case proplists:get_value(N, Vs) of
        undefined ->
            {Typ, {C, L}} = new_var(Lvl, Env),
            args_to_types(T, Lvl, {C, [{N, Typ}|L]}, [{N, Typ}|Memo]);
        Typ ->
            args_to_types(T, Lvl, Env, [{N, Typ}|Memo])
    end.

-ifdef(TEST).

occurs_test_() ->
    [?_assertEqual({unbound, t2, 0}, 
                   occurs(t1, 0, {unbound, t2, 0})),
     ?_assertEqual({qvar, t2, 3},
                   occurs(t1, 0, {qvar, t2, 3})),
     ?_assertEqual({error_circular, t1}, 
                   occurs(t1, 0, {link, {unbound, t1, 0}})),
     ?_assertEqual({error_circular, t3},
                   occurs(t3, 0, {link, {link, {unbound, t3, 0}}}))
    , ?_assertEqual({unbound, t2, 0},
                    occurs(t1, 0, {unbound, t2, 2}))
    ].

unify_test_() ->
    [?_assertEqual({{link, {qvar, t2}}, {qvar, t2}}, 
                   unify({unbound, t1, 0}, {qvar, t2})),
     ?_assertEqual({{link, {unbound, t2, 0}}, {unbound, t2, 0}},
                   unify({unbound, t1, 0}, {unbound, t2, 0})),
     ?_assertMatch({{t_arrow, {link, {unbound, t3, _}}, {link, {unbound, t4, _}}},
                    {t_arrow, {unbound, t3, _},{unbound, t4, _}}},
                   unify(
                     {t_arrow, {unbound, t1, 0}, {unbound, t2, 0}},
                     {t_arrow, {unbound, t3, 0}, {unbound, t4, 0}}))
    ].

from_code(C) ->
    {ok, E} = parser:parse(scanner:scan(C)),
    E.

%% Check the type of an expression from the "top-level"
%% of 0 with a new environment.
top_typ_of(Code) ->
    {ok, E} = parser:parse(scanner:scan(Code)),
    typ_of(new_env(), 0, E).

%% There are a number of expected "unbound" variables here.  I think this
%% is due to the deallocation problem as described in the first post
%% referenced at the top.
typ_of_test_() ->
    [?_assertMatch({{t_arrow, [t_unit], t_int}, _}, 
                   top_typ_of("x () = 0"))
    , ?_assertMatch({{t_arrow, 
                       [{unbound, t0, 0}], 
                       {t_arrow, [{unbound, t1, 0}], {unbound, t1, 0}}}, 
                      _},
                    top_typ_of("f x = let y z = z in y"))
    , ?_assertMatch({{t_arrow,[{unbound, t0, L}],{unbound, t0, L}}, _}, 
                     top_typ_of("f x = let y = x in y"))
    , ?_assertMatch({{t_arrow, 
                      [{t_arrow, [{unbound, t1, L1}], {unbound, t2, L2}}],
                      {t_arrow, [{unbound, t1, L1}], {unbound, t2, L2}}}, _},
                    top_typ_of("f x = let y z = x z in y"))
    , ?_assertMatch({{t_arrow, 
                      [{t_arrow, [{unbound, t1, _}], {unbound, t2, _}},
                       {unbound, t1, _}], 
                      {unbound, t2, _}}, _},
                    top_typ_of("f x y = x y"))
    , ?_assertMatch({{t_arrow, [{unbound, t0, _}],
                      {t_arrow, [{unbound, t1, _}], {unbound, t0, _}}}, _},
                    top_typ_of("f x = let y z = x in y"))
    , ?_assertMatch({{t_arrow,
                      [{t_arrow, 
                        [{unbound, t1, _}, {unbound, t2, _}],
                        {unbound, t3, _}},
                       {unbound, t1, _}],
                      {t_arrow, [{unbound, t2, _}], {unbound, t3, _}}}, _},
                    top_typ_of("f x y = let a b = x y b in a")) 
    ].

-endif.
