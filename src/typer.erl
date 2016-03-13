%%% #typer.erl
%%% 
%%% This is based off of sound_eager_typer and is an attempt to modify
%%% it for use as a type checker for my current AST-in-progress.

-module(typer).

-include("mlfe_ast.hrl").
-include("builtin_types.hrl").

-export([cell/1, new_env/0, typ_of/2, typ_of/3]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

%%% ## Type-Tracking Data Types 
%%% 
%%% These are all of the specs the typer uses to track MLFE types.

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

%%% ##Data Structures
%%% 
%%% Reference cells make unification much simpler (linking is a mutation)
%%% but we also need a simple way to make complete copies of cells so that
%%% each expression being typed can refer to its own copies of items from
%%% the environment and not _globally_ unify another function's types with
%%% its own, preventing others from doing the same (see Types And Programming
%%% Languages (Pierce), chapter 22).

%%% A t_cell is just a reference cell for a type.
-type t_cell() :: pid().

%%% A cell can be sent the message `'stop'` to let the reference cell halt
%%% and be deallocated.
cell(TypVal) ->
    receive
        {get, Pid} -> 
            Pid ! TypVal,
            cell(TypVal);
        {set, NewVal} -> cell(NewVal);
        stop ->
            ok
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
    case Val of
        _ when is_pid(Val) ->
            io:format("!!WARN!! setting ~w to ~w~n", [Cell, Val]);
        _ -> ok
    end,
    Cell ! {set, Val}.

%%% Map of unbound type variable atom name to cell.
-spec copy_cell(t_cell(), map()) -> {t_cell(), map()}.
copy_cell(Cell, RefMap) ->
    case get_cell(Cell) of 
        {link, C} when is_pid(C) ->
            {NC, NewMap} = copy_cell(C, RefMap),
            {new_cell({link, NC}), NewMap};
        {t_arrow, Args, Ret} ->
            Folder = fun(A, {L, RM}) ->
                             {V, NM} = copy_cell(A, RM),
                             {[V|L], NM}
                     end,
            {NewArgs, Map2} = lists:foldl(Folder, {[], RefMap}, Args),
            {NewRet, Map3} = copy_cell(Ret, Map2),
            {new_cell({t_arrow, lists:reverse(NewArgs), NewRet}), Map3};
%        P when is_pid(P) ->
%            {NC, NewMap} = copy_cell(P, RefMap),
%            {new_cell(NC), NewMap};
        {unbound, Name, _Lvl} = V ->
            io:format("Copy is looking for ~w~n", [Name]),
            case maps:get(Name, RefMap, undefined) of
                undefined ->
                    NC = new_cell(V),
                    {NC, maps:put(Name, NC, RefMap)};
                Existing ->
                    io:format("Copy found ~w for ~w~n", [Existing, Name]),
                    {Existing, RefMap}
            end;
        V ->
            io:format("COPY:  hit V~n", []),
            {new_cell(V), RefMap}
    end.
%    new_cell(get_cell(Cell)).

%%% Environments track two things:
%%% 
%%% 1. A counter for naming new type variables
%%% 2. A proplist of {expression name, expression type} for the types
%%%    of values and functions so far inferred/checked.

%% The list is {var name, var type}
-type env() :: {integer(), list({atom(), atom()})}.

-spec new_env() -> env().
new_env() ->
    {0, [Typ||Typ <- ?all_bifs]}.

update_env(Name, Typ, {C, L}) ->
    {C, [{Name, Typ}|[{N, T} || {N, T} <- L, N =/= Name]]}.

update_var_counter(VarNum, {_, Bindings}) ->
    {VarNum, Bindings}.


%%% Make a copy of the named entity from the current environment, replacing
%%% reference cells with copies of them.  Multiple references of the same
%%% type variable must end up referencing a new _single_ copy of the type
%%% variable's cell.
copy_from_env(Name, {_C, L}) ->
    copy_from_env_2(proplists:get_value(Name, L), maps:new()).

copy_type_list(TL, RefMap) ->
    Folder = fun(A, {L, RM}) ->
                     {V, NM} = copy_type(A, RM),
                     {[V|L], NM}
             end,
    {NewList, Map2} = lists:foldl(Folder, {[], RefMap}, TL),
    {lists:reverse(NewList), Map2}.

copy_from_env_2({t_arrow, A, B}, RefMap) ->
    {NewArgs, Map2} = copy_type_list(A, RefMap),
    {NewRet, _Map3} = copy_type(B, Map2),
    {t_arrow, NewArgs, NewRet};
copy_from_env_2({t_list, A}, RefMap) ->
    {NewList, _} = copy_type_list(A, RefMap),
    {t_list, NewList};
%% TODO:  individual cell copy.
copy_from_env_2(T, _) ->
    io:format("COPY:  bottom env ~w~n", [T]),
    T.

copy_type(P, RefMap) when is_pid(P) ->
    copy_cell(P, RefMap);
copy_type(T, M) ->
    {T, M}.

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
            io:format("UNIFY:  unbound and ty~n", []),
            case occurs(N, Lvl, Ty) of
                {unbound, _, _} = T ->
                    io:format("Setting ~w to ~w~n", [N, Ty]),
                    set_cell(T2, T),
                    set_cell(T1, {link, T2});
                {error, _} = E ->
                    E;
                _Other ->
                    io:format("Unifying ~w ~w to ~w~n", [T1, get_cell(T1), Ty]),
                    set_cell(T1, {link, T2})
            end,
            ok;
        {Ty, {unbound, N, Lvl}} ->
            io:format("UNIFY:  ty and unbound~n", []),
            case occurs(N, Lvl, Ty) of
                {unbound, _, _} = T -> 
                    set_cell(T1, T),            % level adjustment
                    set_cell(T2, {link, T1});
                {error, _} = E ->
                    E;
                _Other ->
                    io:format("Unifying ~w ~w to ~w~n", [T2, get_cell(T2), Ty]),
                    set_cell(T2, {link, T1})
            end,
            set_cell(T2, {link, T1}),
            ok;
        {{t_arrow, A1, A2}, {t_arrow, B1, B2}} ->
            case unify_list(A1, B1) of
                {error, _} = E ->
                    E;
                {_ResA1, _ResB1} ->
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
typ_list([], _Lvl, {NextVar, _}, Memo) ->
    {NextVar, lists:reverse(Memo)};
typ_list([H|T], Lvl, Env, Memo) ->
    {Typ, NextVar} = typ_of(Env, Lvl, H),
    typ_list(T, Lvl, update_var_counter(NextVar, Env), [Typ|Memo]).

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

%% In the past I returned the environment entirely but this contained mutations
%% beyond just the counter for new type variable names.  The integer in the
%% successful return tuple is just the next type variable number so that
%% the environments further up have no possibility of being poluted with 
%% definitions below.
-spec typ_of(
        Env::env(),
        Lvl::integer(),
        Exp::mlfe_expression()) -> {typ(), integer()} | {error, term()}.

typ_of({VarNum, _}, _Lvl, {int, _, _}) ->
    {t_int, VarNum};
typ_of({VarNum, _}, _Lvl, {float, _, _}) ->
    {t_float, VarNum};
typ_of(Env, Lvl, {symbol, _, N}) ->
    {T, {VarNum, _}, _} = inst(N, Lvl, Env),
    {T, VarNum};
%% BIFs are loaded in the environment as atoms:
typ_of(Env, Lvl, {bif, MlfeName, _, _, _}) ->
    {T, {VarNum, _}, _} = inst(MlfeName, Lvl, Env),
    {T, VarNum};    

typ_of(Env, Lvl, #mlfe_apply{name=N, args=Args}) ->
    Name = case N of
               {bif, X, _, _, _} -> X;
               {symbol, _, X} -> X
           end,
    {TypF, NextVar} = typ_of(Env, Lvl, N),
    dump_env(Env),
    io:format("~nTypF is ~s from name ~s~n", [dump_term(TypF), Name]),
    io:format("Args are ~w~n", [Args]),
    CopiedTypF = copy_from_env_2(TypF, maps:new()),
    io:format("After copy is ~s from name ~s~n", [dump_term(CopiedTypF), Name]),

    {NextVar2, ArgTypes} = typ_list(Args, Lvl, update_var_counter(NextVar, Env), []),
    {TypRes, Env2} = new_var(Lvl, update_var_counter(NextVar2, Env)),

    Arrow = new_cell({t_arrow, ArgTypes, TypRes}),
    io:format("Arrow is ~s~n", [dump_term(Arrow)]),
    case unify(CopiedTypF, Arrow) of
        {error, _} = E ->
            io:format("Error when unifying, ~w~n", [E]),
            E;
        ok ->
            {VarNum, _} = Env2,
            {TypRes, VarNum}
    end;

%% This can't handle recursive functions since the function name
%% is not bound in the environment:
typ_of(Env, Lvl, #mlfe_fun_def{args=Args, body=Body}) ->
    %% I'm leaving the environment mutation here because the body
    %% needs the bindings:
    {ArgTypes, Env2} = args_to_types(Args, Lvl, Env, []),
    {T, NextVar} = typ_of(Env2, Lvl, Body),
    Env3 = update_var_counter(NextVar, Env2),

    io:format("===  FUN DEF:  ==============~n", []),
    dump_env(Env3),

    %% Some types may have been unified in NewEnv2 so we need
    %% to replace their occurences in ArgTypes.  This is getting
    %% around the lack of reference cells.
    %{ArgTypesPass2, NewEnv2} = args_to_types(Args, Lvl, NewEnv2, []),

    JustTypes = [Typ || {_, Typ} <- ArgTypes],
    {{t_arrow, JustTypes, T}, NextVar};

%% A let binding inside a function:
typ_of(Env, Lvl, #fun_binding{
               def=#mlfe_fun_def{name={symbol, _, N}}=E, 
               expr=E2}) ->
    io:format("=== FUN BIND:  ~s ========~n", [N]),
    {TypE, NextVar} = typ_of(Env, Lvl, E),
    Env2 = update_var_counter(NextVar, Env),
    typ_of(update_env(N, gen(Lvl, TypE), Env2), Lvl+1, E2);

%% A var binding inside a function:
typ_of(Env, Lvl, #var_binding{name={symbol, _, N}, to_bind=E1, expr=E2}) ->
    io:format("=== VAR BIND:  ~s ========~n", [N]),
    {TypE, NextVar} = typ_of(Env, Lvl, E1),
    Env2 = update_var_counter(NextVar, Env),
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
    [io:format("Env:  ~s ~s~n", [N, dump_term(T)])||{N, T} <- L].

dump_term({t_arrow, Args, Ret}) ->
    io_lib:format("~s -> ~s", [[dump_term(A) || A <- Args], dump_term(Ret)]);
dump_term(P) when is_pid(P) ->
    io_lib:format("{cell ~w ~s}", [P, dump_term(get_cell(P))]);
dump_term({link, P}) when is_pid(P) ->
    io_lib:format("{link ~w ~s}", [P, dump_term(P)]);
dump_term(T) ->
    io_lib:format("~w", [T]).


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

simple_polymorphic_let_test() ->
    Code =
        "double_app int ="
        "let two_times f x = f (f x) in "
        "let int_double i = i + i in "
        "two_times int_double int",
    ?assertMatch({{t_arrow, [t_int], t_int}, _}, top_typ_of(Code)).

polymorphic_let_test() ->
    Code = 
        "double_application int float = "
        "let two_times f x = f (f x) in "
        "let int_double a = a + a in "
        "let float_double b = b +. b in "
        "let doubled_2 = two_times int_double int in "
        "two_times float_double float",
    ?assertMatch({{t_arrow, [t_int, t_float], t_float}, _},
                 top_typ_of(Code)).

-endif.
