%% This is based off of sound_eager_typer and is an attempt to modify
%% it for use as a type checker for my current AST-in-progress.

-module(typer).

-include("mlfe_ast.hrl").
-include("builtin_types.hrl").

-export([cell/1, new_env/0, typ_of/2, typ_of/3]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

-type typ_name() :: atom().

-type qvar()   :: {qvar, typ_name()}.
-type tvar()   :: {unbound, typ_name(), integer()}
                | {link, typ()}.
%% list of parameter types, return type:
-type t_arrow() :: {t_arrow, list(typ()), typ()}.

-type t_list() :: {t_list, typ()}.

-type t_const() :: t_int
                 | t_float
                 | t_atom
                 | t_bool
                 | t_string.

-type typ() :: qvar()
             | tvar()
             | t_arrow()
             | t_const()
             | t_list().

%% Reference cells make unification WAY easier:
-type t_cell() :: pid().

cell(TypVal) ->
    receive
        {get, Pid} -> 
            Pid ! TypVal,
            cell(TypVal);
        {set, NewVal} -> cell(NewVal)
    end.

-spec new_cell(typ()) -> pid().
new_cell(Typ) ->
    spawn(?MODULE, cell, [Typ]).

-spec get_cell(t_cell()) -> typ().
get_cell(Cell) ->
    Cell ! {get, self()},
    receive
        Val -> Val
    end.

set_cell(Cell, Val) ->
    Cell ! {set, Val}.

occurs(Label, Level, P) when is_pid(P) ->
    occurs(Label, Level, get_cell(P));
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

unwrap_cell(C) when is_pid(C) ->
    get_cell(C);
unwrap_cell(Typ) ->
    Typ.

-spec unify(typ(), typ()) -> ok | {error, atom()}.
unify(T1, T2) ->
    case {unwrap_cell(T1), unwrap_cell(T2)} of
        {T, T} -> ok;
        %% only one instance of a type variable is permitted:
        {{unbound, N, _}, {unbound, N, _}}  -> {error, {cannot_unify, T1, T2}};
        {{link, Ty}, _} ->
            unify(Ty, T2);
        {_, {link, Ty}} ->
            unify(T1, Ty);
        %% Definitely room for cleanup in the next two cases:
        {{unbound, N, Lvl}, Ty} ->
            case occurs(N, Lvl, Ty) of
                {unbound, _, _} = T -> 
                    set_cell(T2, T),
                    set_cell(T1, {link, T2});
                {error, _} = E ->
                    E;
                _Other ->
                    set_cell(T1, {link, T2})
            end,
            ok;
        {Ty, {unbound, N, Lvl}} ->
            case occurs(N, Lvl, Ty) of
                {unbound, _, _} = T -> 
                    set_cell(T1, T),            % level adjustment
                    set_cell(T2, {link, T1});
                {error, _} = E ->
                    E;
                _Other ->
                    set_cell(T2, {link, T1})
            end,
            set_cell(T2, {link, T1}),
            ok;
        {{t_arrow, A1, A2}, {t_arrow, B1, B2}} ->
            case unify_list(A1, B1) of
                {error, _} = E ->
                    E;
                {ResA1, ResB1} ->
                    case unify(A2, B2) of
                        {error, _} = E ->
                            E;
                        ok ->
                            ok
                    end
            end;
        {_T1, _T2} ->
            {error, {cannot_unify, T1, T2}}
    end.

%% Unify two parameter lists, e.g. from a function arrow.
unify_list(As, Bs) ->
    unify_list(As, Bs, {[], []}).
unify_list([], [], {MemoA, MemoB}) ->
    {lists:reverse(MemoA), lists:reverse(MemoB)};
unify_list([], _, _) ->
    {error, mismatched_arity};
unify_list(_, [], _) ->
    {error, mismatched_arity};
unify_list([A|TA], [B|TB], {MA, MB}) ->
    case unify(A, B) of
        {error, _} = E -> E;
        _ -> unify_list(TA, TB, {[A|MA], [B|MB]})
    end.

%% The list is {var name, var type}
-type env() :: {integer(), list({atom(), atom()})}.

-spec new_env() -> env().
new_env() ->
    {0, [Typ||Typ <- ?all_bifs]}.

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
    {{t_arrow, PTs, RT}, NewEnv2, M2};

%% Everything else is assumed to be a constant:
inst(Typ, _Lvl, Env, Map) ->
    {Typ, Env, Map}.

-spec new_var(Lvl :: integer(), Env :: env()) -> {t_cell(), env()}.
new_var(Lvl, {C, L}) ->
    N = list_to_atom("t" ++ integer_to_list(C)),
    TVar = new_cell({unbound, N, Lvl}),
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

unwrap(P) when is_pid(P) ->
    unwrap(get_cell(P));
unwrap({link, Ty}) ->
    unwrap(Ty);
unwrap({t_arrow, A, B}) ->
    {t_arrow, [unwrap(X)||X <- A], unwrap(B)};
unwrap(X) ->
    X.

%% Top-level typ_of unwraps the reference cells used in unification.
-spec typ_of(Env::env(), Exp::mlfe_expression()) -> {typ(), env()} | {error, term()}.
typ_of(Env, Exp) ->
    case typ_of(Env, 0, Exp) of
        {error, _} = E -> E;
        {Typ, NewEnv} -> {unwrap(Typ), NewEnv}
    end.

-spec typ_of(
        Env::env(),
        Lvl::integer(),
        Exp::mlfe_expression()) -> {typ(), env()} | {error, term()}.

typ_of(Env, _Lvl, {int, _, _}) ->
    {t_int, Env};
typ_of(Env, Lvl, {symbol, _, N}) ->
    {T, E2, _} = inst(N, Lvl, Env),
    {T, E2};
%% BIFs are loaded in the environment as atoms:
typ_of(Env, Lvl, {bif, MlfeName, _, _, _}) ->
    {T, E2, _} = inst(MlfeName, Lvl, Env),
    {T, E2};    

typ_of(Env, Lvl, #mlfe_apply{name={bif, MlfeName, _, _, _}=N, args=Args}) ->
    {TypF, Env2} = typ_of(Env, Lvl, N),
    typ_of(Env2, Lvl, {unwrapped_apply, MlfeName, Args, TypF});
typ_of(Env, Lvl, #mlfe_apply{name={symbol, _, Name}=N, args=Args}) ->
    {TypF, Env2} = typ_of(Env, Lvl, N),
    typ_of(Env2, Lvl, {unwrapped_apply, Name, Args, TypF});
typ_of(Env, Lvl, {unwrapped_apply, Name, Args, TypF}) ->
    {Env3, ArgTypes} = typ_list(Args, Lvl, Env, []),
    {TypRes, Env4} = new_var(Lvl, Env3),

    %% ArgTypes is in reverse order to As from typ_list/3:
    Arrow = new_cell({t_arrow, lists:reverse(ArgTypes), TypRes}),
    case unify(TypF, Arrow) of
        {error, _} = E ->
            E;
        ok ->
            {TypRes, Env4}
    end;

%% This can't handle recursive functions since the function name
%% is not bound in the environment:
typ_of(Env, Lvl, #mlfe_fun_def{args=Args, body=Body}) ->
    {_, NewEnv} = args_to_types(Args, Lvl, Env, []),
    {T, NewEnv2} = typ_of(NewEnv, Lvl, Body),

    dump_env(NewEnv2),

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

dump_env({C, L}) ->
    io:format("Next var number is ~w~n", [C]),
    [io:format("Env:  ~w~n", [X])||X <- L].

-ifdef(TEST).

from_code(C) ->
    {ok, E} = parser:parse(scanner:scan(C)),
    E.

%% Check the type of an expression from the "top-level"
%% of 0 with a new environment.
top_typ_of(Code) ->
    {ok, E} = parser:parse(scanner:scan(Code)),
    typ_of(new_env(), E).

%% There are a number of expected "unbound" variables here.  I think this
%% is due to the deallocation problem as described in the first post
%% referenced at the top.
typ_of_test_() ->
    [?_assertMatch({{t_arrow, [t_int], t_int}, _}, 
                   top_typ_of("double x = x + x"))
    , ?_assertMatch({{t_arrow, [{t_arrow, [A], B}, A], B}, _},
                   top_typ_of("apply f x = f x"))
    , ?_assertMatch({{t_arrow, [t_int], t_int}, _},
                    top_typ_of("doubler x = let double y = y + y in double x"))
    ].

-endif.
