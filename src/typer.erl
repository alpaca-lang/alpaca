%%% #typer.erl
%%% 
%%% This is based off of the sound and eager type inferencer in 
%%% http://okmij.org/ftp/ML/generalization.html with some influence
%%% from https://github.com/tomprimozic/type-systems/blob/master/algorithm_w
%%% where the arrow type and instantiation are concerned.

-module(typer).

-include("mlfe_ast.hrl").
-include("builtin_types.hrl").

-export([cell/1, new_env/0, typ_of/2, typ_of/3]).
-export_type([env/0, typ/0]).

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
                 | t_string.

-type typ() :: qvar()
             | tvar()
             | t_arrow()
             | t_const()
             | t_list()
             | t_tuple()
             | t_clause().

%%% ##Data Structures
%%% 
%%% ###Reference Cells
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
    Cell ! {set, Val}.

%%% The `map` is a map of `unbound type variable name` to a `t_cell()`.
%%% It's used to ensure that each reference or link to a single type
%%% variable actually points to a single canonical reference cell for that
%%% variable.  Failing to do so causes problems with unification since
%%% unifying one variable with another type should impact all occurrences
%%% of that variable.
-spec copy_cell(t_cell(), map()) -> {t_cell(), map()}.
copy_cell(Cell, RefMap) ->
    case get_cell(Cell) of 
        {link, C} when is_pid(C) ->
            {NC, NewMap} = copy_cell(C, RefMap),
            {new_cell({link, NC}), NewMap};
        {t_arrow, Args, Ret} ->
            %% there's some commonality below with copy_type_list/2
            %% that can probably be exploited in future:
            Folder = fun(A, {L, RM}) ->
                             {V, NM} = copy_cell(A, RM),
                             {[V|L], NM}
                     end,
            {NewArgs, Map2} = lists:foldl(Folder, {[], RefMap}, Args),
            {NewRet, Map3} = copy_cell(Ret, Map2),
            {new_cell({t_arrow, lists:reverse(NewArgs), NewRet}), Map3};
        {unbound, Name, _Lvl} = V ->
            case maps:get(Name, RefMap, undefined) of
                undefined ->
                    NC = new_cell(V),
                    {NC, maps:put(Name, NC, RefMap)};
                Existing ->
                    {Existing, RefMap}
            end;
        V ->
            {new_cell(V), RefMap}
    end.

%%% ###Environments
%%% 
%%% Environments track three things:
%%% 
%%% 1. A counter for naming new type variables
%%% 2. A proplist of {expression name, expression type} for the types
%%%    of values and functions so far inferred/checked.
%%% 3. The set of modules included in type checking.
%%% 
%%% I'm including the modules in the typing environment so that when a call
%%% crosses a module boundary into a module not yet checked, we can add the
%%% bindings the other function expects.  An example:
%%% 
%%% Function `A.f` (f in module A) calls function `B.g` (g in module B).  `B.g`
%%% calls an unexported function `B.h`.  If the module B has not been checked
%%% before we check `A.f`, we have to check `B.g` in order to determine `A.f`'s
%%% type.  In order to check `B.g`, `B.h` must be in the enviroment to also be
%%% checked.  
%%% 
%%% Currently missing:  cycle detection and termination.

-record(env, {
          next_var=0          :: integer(),
          entered_modules=[]  :: list(atom()),
          current_module=none :: none | mlfe_module(),
          bindings=[]         :: list({term(), typer:typ()|t_cell()}),
          modules=[]          :: list(mlfe_module())
}).

-type env() :: #env{}.

-spec new_env() -> env().
new_env() ->
    #env{bindings=[celled_binding(Typ)||Typ <- ?all_bifs]}.

celled_binding({Name, {t_arrow, Args, Ret}}) ->
    {Name, {t_arrow, [new_cell(A) || A <- Args], new_cell(Ret)}}.

update_binding(Name, Typ, #env{bindings=Bs} = Env) ->
    Env#env{bindings=[{Name, Typ}|[{N, T} || {N, T} <- Bs, N =/= Name]]}.

update_counter(VarNum, Env) ->
    Env#env{next_var=VarNum}.
 
%%% Make a copy of the named entity from the current environment, replacing
%%% reference cells with copies of them.  Multiple references of the same
%%% type variable must end up referencing a new _single_ copy of the type
%%% variable's cell.
%copy_from_env(Name, {_C, L}) ->
%    deep_copy_type(proplists:get_value(Name, L), maps:new()).

%% Used by deep_copy_type for a set of function arguments or 
%% list elements.
copy_type_list(TL, RefMap) ->
    Folder = fun(A, {L, RM}) ->
                     {V, NM} = copy_type(A, RM),
                     {[V|L], NM}
             end,
    {NewList, Map2} = lists:foldl(Folder, {[], RefMap}, TL),
    {lists:reverse(NewList), Map2}.

%%% As referenced in several places, this is, after a fashion, following 
%%% Pierce's advice in chapter 22 of Types and Programming Languages.
%%% We make a deep copy of the chain of reference cells so that we can
%%% unify a polymorphic function with some other types from a function
%%% application without _permanently_ unifying the types for everyone else
%%% and thus possibly blocking a legitimate use of said polymorphic function
%%% in another location.
deep_copy_type({t_arrow, A, B}, RefMap) ->
    {NewArgs, Map2} = copy_type_list(A, RefMap),
    {NewRet, _Map3} = copy_type(B, Map2),
    {t_arrow, NewArgs, NewRet};
deep_copy_type({t_list, A}, RefMap) ->
    {NewList, _} = copy_type_list(A, RefMap),
    {t_list, NewList};
%% TODO:  individual cell copy.
deep_copy_type(T, _) ->
    T.

copy_type(P, RefMap) when is_pid(P) ->
    copy_cell(P, RefMap);
copy_type(T, M) ->
    {T, M}.

%%% ### Typer
%%% 
%%% 


%%% Type check all functions in the module, returning a new module with
%%% the function types set.
%-spec type_module(Mod::mlfe_module()) -> mlfe_module().
%type_module(Mod) ->
    

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
        {T, T} ->
            ok;
        %% only one instance of a type variable is permitted:
        {{unbound, N, _}, {unbound, N, _}}  -> {error, {cannot_unify, T1, T2}};
        {{link, Ty}, _} ->
            unify(Ty, T2);
        {_, {link, Ty}} ->
            unify(T1, Ty);
        {t_rec, _} ->
            set_cell(T1, {link, T2}),
            ok;
        {_, t_rec} ->
            set_cell(T2, {link, T1}),
            ok;
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
                {_ResA1, _ResB1} ->
                    case unify(A2, B2) of
                        {error, _} = E ->
                            E;
                        ok ->
                            ok
                    end
            end;
        {{t_tuple, A}, {t_tuple, B}} ->
            case unify_list(A, B) of
                {error, _} = Err -> Err;
                _ -> ok
            end;
        {{t_list, _}, t_nil} ->
            set_cell(T2, {link, T1}),
            ok;
        {t_nil, {t_list, _}} ->
            set_cell(T1, {link, T2}),
            ok;
        {{t_list, A}, {t_list, B}} ->
            unify(A, B);
        {{t_list, A}, B} ->
            unify(A, B);
        {A, {t_list, B}} ->
            unify(A, B);
        {_T1, _T2} ->
            io:format("UNIFY FAIL:  ~s AND ~s~n", [dump_term(X)||X<-[_T1, _T2]]),
            {error, {cannot_unify, _T1, _T2}}
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
        Env :: env()) -> {typ(), env()} | {error, term()}.

inst(VarName, Lvl, #env{bindings=Bs} = Env) ->
    Default = {error, {bad_variable_name, VarName}},
    case proplists:get_value(VarName, Bs, Default) of
        {error, _} = E ->
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
-spec inst(typ(), integer(), env(), CachedMap::map()) -> {typ(), env(), map()} | {error, term()}.
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
new_var(Lvl, #env{next_var=VN} = Env) ->
    N = list_to_atom("t" ++ integer_to_list(VN)),
    TVar = new_cell({unbound, N, Lvl}),
    {TVar, Env#env{next_var=VN+1}}.

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
typ_list([], _Lvl, #env{next_var=NextVar}, Memo) ->
    {lists:reverse(Memo), NextVar};
typ_list([H|T], Lvl, Env, Memo) ->
    {Typ, NextVar} = typ_of(Env, Lvl, H),
    typ_list(T, Lvl, update_counter(NextVar, Env), [Typ|Memo]).

unwrap(P) when is_pid(P) ->
    unwrap(get_cell(P));
unwrap({link, Ty}) ->
    unwrap(Ty);
unwrap({t_arrow, A, B}) ->
    {t_arrow, [unwrap(X)||X <- A], unwrap(B)};
unwrap({t_clause, A, G, B}) ->
    {t_clause, unwrap(A), unwrap(G), unwrap(B)};
unwrap({t_tuple, Vs}) ->
    {t_tuple, [unwrap(V)||V <- Vs]};
unwrap({t_list, T}) ->
    {t_list, unwrap(T)};
unwrap(X) ->
    X.

-spec typ_module(M::mlfe_module(), Env::env()) -> mlfe_module().
typ_module(#mlfe_module{functions=Fs, name=Name}=M, Env) ->
    Env2 = Env#env{current_module=M, entered_modules=[Name]},
    case typ_module_funs(Fs, Env2, []) of
        {error, _} = E -> E;
        [_|_] = Funs   -> M#mlfe_module{functions=Funs}
    end.

typ_module_funs([], _Env, Memo) ->
    lists:reverse(Memo);
typ_module_funs([#mlfe_fun_def{name={symbol, _, Name}=N}=F|Rem], Env, Memo) ->
    case typ_of(Env, F) of
        {error, _} = E -> 
            E;
        {Typ, Env2} ->
            Env3 = update_binding(Name, Typ, Env2),
            typ_module_funs(Rem, Env3, [F#mlfe_fun_def{type=Typ}|Memo])
    end.

%% Top-level typ_of unwraps the reference cells used in unification.
-spec typ_of(Env::env(), Exp::mlfe_expression()) -> {typ(), env()} | {error, term()}.
typ_of(Env, Exp) ->
    case typ_of(Env, 0, Exp) of
        {error, _} = E -> E;
        {Typ, NewVar} -> {unwrap(Typ), update_counter(NewVar, Env)}
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

typ_of(#env{next_var=VarNum}, _Lvl, {int, _, _}) ->
    {t_int, VarNum};
typ_of(#env{next_var=VarNum}, _Lvl, {float, _, _}) ->
    {t_float, VarNum};
typ_of(#env{next_var=VarNum}, _Lvl, {atom, _, _}) ->
    {t_atom, VarNum};
typ_of(Env, Lvl, {symbol, _, N}) ->
    case inst(N, Lvl, Env) of
        {error, _} = E -> E;
        {T, #env{next_var=VarNum}, _} -> {T, VarNum}
    end;

typ_of(Env, Lvl, {'_', _}) ->
    {T, #env{next_var=VarNum}, _} = inst('_', Lvl, Env),
    {T, VarNum};
typ_of(Env, Lvl, #mlfe_tuple{values=Vs}) ->
    {VTyps, NextVar} = typ_list(Vs, Lvl, Env, []),
    {{t_tuple, VTyps}, NextVar};
typ_of(#env{next_var=_VarNum}=Env, Lvl, {nil, _Line}) ->
    %% 20160403 a nil type isn't making much sense to
    %% me at the moment, it's just another list to be
    %% unified:
%    {new_cell(t_nil), VarNum};
    {TL, #env{next_var=NV}} = new_var(Lvl, Env),
    {new_cell({t_list, TL}), NV};
typ_of(Env, Lvl, #mlfe_cons{head=H, tail=T}) ->
    {HTyp, NV1} = typ_of(Env, Lvl, H),
    {TTyp, NV2} = case T of
                      {nil, _} -> {{t_list, HTyp}, NV1};
                      #mlfe_cons{}=Cons ->
                          typ_of(update_counter(NV1, Env), Lvl, Cons);
                      {symbol, _, _} = S -> 
                          {STyp, Next} = typ_of(
                                           update_counter(NV1, Env), 
                                           Lvl, 
                                           S),
                          {TL, #env{next_var=Next2}} = new_var(
                                               Lvl, 
                                               update_counter(Next, Env)),
                          case unify({t_list, TL}, STyp) of
                              {error, _} = E -> E;
                              ok -> {STyp, Next2}
                          end;
                      #mlfe_apply{}=Apply ->
                          {TApp, Next} = typ_of(update_counter(NV1, Env), Lvl, Apply),
                          case unify({t_list, HTyp}, TApp) of
                              {error, _} = E -> E;
                              ok -> {TApp, Next}
                          end;
                      NonList ->
                          {error, {cons_to_non_list, NonList}}
                  end,
    ListType = case TTyp of
                   P when is_pid(P) ->
                       case get_cell(TTyp) of
                           {link, {t_list, LT}} -> LT;
                           {t_list, LT} -> LT
                       end;
                   {t_list, LT} ->
                       LT
               end,
    case unify(HTyp, ListType) of
        {error, _} = Err ->
            Err;
        ok ->
            {TTyp, NV2}
    end;

%% BIFs are loaded in the environment as atoms:
typ_of(Env, Lvl, {bif, MlfeName, _, _, _}) ->
    case inst(MlfeName, Lvl, Env) of
        {error, _} = E ->
            E;
        {T, #env{next_var=VarNum}, _} ->
            {T, VarNum}
    end;

typ_of(Env, Lvl, #mlfe_apply{name={Mod, {symbol, _, X}, Arity}, args=Args}) ->
    case [M || M <- Env#env.entered_modules, M == Mod] of
        [] ->
            %% Naively assume a single call to the same function for now.
            % does the module exist and does it export the function?
            case extract_fun(Env, Mod, X, Arity) of
                {error, _} = E -> E;
                {ok, Module, Fun} -> 
                    Env2 = Env#env{current_module=Module, 
                                   entered_modules=[Mod | Env#env.entered_modules]},
                    case typ_of(Env2, Lvl, Fun) of
                        {error, _} = E -> E;
                        {TypF, NextVar} ->
                            typ_apply(update_counter(NextVar, Env), 
                                      Lvl, TypF, NextVar, Args)
                    end
            end;
        _  -> 
            [CurrMod|_] = Env#env.entered_modules,
            {error, {bidirectional_module_ref, Mod, CurrMod}}
    end;

typ_of(Env, Lvl, #mlfe_apply{name=N, args=Args}) ->
    %% When a symbol isn't bound to a function in the environment,
    %% attempt to find it in the module.  Here we're assuming that
    %% the user has referred to a function that is defined later than
    %% the one being typed.
    ForwardFun = fun() ->
                         Mod = Env#env.current_module,
                         {symbol, _, FN} = N,
                         case get_fun(Mod, FN, length(Args)) of
                             {ok, _, Fun} ->
                                 {TypF, NextVar} = typ_of(Env, Lvl, Fun),
                                 typ_apply(Env, Lvl, TypF, NextVar, Args);
                             {error, _} = E -> E
                         end
                 end,                                       

    case typ_of(Env, Lvl, N) of
        {error, {bad_variable_name, _}} -> ForwardFun();
        {error, _} = E -> E;
        {TypF, NextVar} -> typ_apply(Env, Lvl, TypF, NextVar, Args)
    end;

%% Unify the patterns with each other and resulting expressions with each
%% other, then unifying the general pattern type with the match expression's
%% type.
typ_of(Env, Lvl, #mlfe_match{match_expr=E, clauses=Cs}) ->
    {ETyp, NextVar1} = typ_of(Env, Lvl, E),
    ClauseFolder = fun(C, {Clauses, EnvAcc}) ->
                           {TypC, NV} = typ_of(EnvAcc, Lvl, C),
                           {[TypC|Clauses], update_counter(NV, EnvAcc)}
                   end,
    {TypedCs, #env{next_var=NextVar2}} = lists:foldl(
                                           ClauseFolder, 
                                           {[], update_counter(NextVar1, Env)}, Cs),
    UnifyFolder = fun({t_clause, PA, _, RA}, Acc) ->
                          case Acc of
                              {t_clause, PB, _, RB} = TypC ->
                                  case unify(PA, PB) of
                                      ok -> case unify(RA, RB) of
                                                ok -> TypC;
                                                {error, _} = Err -> Err
                                            end;
                                      {error, _} = Err -> Err
                                  end;
                              {error, _} = Err ->
                                  Err
                          end
                  end,
    [FC|TCs] = lists:reverse(TypedCs),

    case lists:foldl(UnifyFolder, FC, TCs) of
        {error, _} = Err ->
            Err;
        _ ->
            %% unify the expression with the unified pattern:
            {t_clause, PTyp, _, RTyp} = FC,
            case unify(ETyp, PTyp) of
                {error, _} = Err ->
                    Err;
                %% only need to return the result type of the unified clause types:
                ok -> 
                    {RTyp, NextVar2} 
            end
    end;

typ_of(Env, Lvl, #mlfe_clause{pattern=P, guards=Gs, result=R}) ->
    {PTyp, NewEnv, _} = add_bindings(P, Env, Lvl, 0),
    F = fun
            (_, {error, _}=Err) -> Err;
            (G, {Typs, AccEnv}) -> 
                case typ_of(AccEnv, Lvl, G) of
                    {error, _}=Err -> Err;
                    {GTyp, NV} -> {[GTyp|Typs], update_counter(NV, AccEnv)}
                end
        end,
    {GTyps, Env2} = lists:foldl(F, {[], NewEnv}, Gs),
    UnifyFolder = fun
                      (_, {error, _}=Err) -> Err;
                      (N, Acc) ->
                          case unify(N, Acc) of
                              {error, _}=Err -> Err;
                              ok -> Acc
                          end
                  end,

    case lists:foldl(UnifyFolder, new_cell(t_bool), GTyps) of
        {error, _}=Err -> Err;
        _ ->
            case typ_of(Env2, Lvl, R) of
                {error, _} = E   -> E;
                {RTyp, NextVar2} -> {{t_clause, PTyp, none, RTyp}, NextVar2}
            end
        end;

%%% Pattern match guards that both check the type of an argument and cause
%%% it's type to be fixed.
typ_of(Env, Lvl, #mlfe_type_check{type=T, expr=E}) ->
    case T of
        is_integer -> 
            {ETyp, NV} = typ_of(Env, Lvl, E),
            case unify(new_cell(t_int), ETyp) of
                {error, _}=Err -> Err;
                ok -> {t_bool, NV}
            end
    end;

%%% Calls to Erlang code are only have their return value typed.
typ_of(#env{next_var=NV}=Env, Lvl, #mlfe_ffi{clauses=Cs}) ->
    ClauseFolder = fun(C, {Typs, EnvAcc}) ->
                           {{t_clause, _, _, T}, X} = typ_of(EnvAcc, Lvl, C),
                           {[T|Typs], update_counter(X, EnvAcc)}
                   end,
    {TypedCs, #env{next_var=NV2}} = lists:foldl(
                                           ClauseFolder, 
                                           {[], update_counter(NV, Env)}, Cs),
    UnifyFolder = fun(A, Acc) ->
                             case unify(A, Acc) of
                                 ok -> Acc;
                                 {error, _} = Err -> Err
                             end
                     end,
    [FC|TCs] = lists:reverse(TypedCs),

    case lists:foldl(UnifyFolder, FC, TCs) of
        {error, _} = Err ->
            Err;
        _ ->
            {FC, NV2}
    end;
    

%% This can't handle recursive functions since the function name
%% is not bound in the environment:
typ_of(Env, Lvl, #mlfe_fun_def{name={symbol, _, N}, args=Args, body=Body}) ->
    %% I'm leaving the environment mutation here because the body
    %% needs the bindings:
    {ArgTypes, Env2} = args_to_types(Args, Lvl, Env, []),
    JustTypes = [Typ || {_, Typ} <- ArgTypes],
    RecursiveType = {t_arrow, JustTypes, new_cell(t_rec)},
    EnvWithLetRec = update_binding(N, RecursiveType, Env2),

    case typ_of(EnvWithLetRec, Lvl, Body) of 
        {error, _} = Err ->
            Err;
        {T, NextVar} ->
            Env3 = update_counter(NextVar, Env2),
            
            io:format("===  FUN DEF:  ==============~n", []),
            dump_env(Env3),
            JustTypes = [Typ || {_, Typ} <- ArgTypes],
            {{t_arrow, JustTypes, T}, NextVar}
    end;

%% A let binding inside a function:
typ_of(Env, Lvl, #fun_binding{
               def=#mlfe_fun_def{name={symbol, _, N}}=E, 
               expr=E2}) ->
    io:format("=== FUN BIND:  ~s ========~n", [N]),
    {TypE, NextVar} = typ_of(Env, Lvl, E),
    Env2 = update_counter(NextVar, Env),
    typ_of(update_binding(N, gen(Lvl, TypE), Env2), Lvl+1, E2);

%% A var binding inside a function:
typ_of(Env, Lvl, #var_binding{name={symbol, _, N}, to_bind=E1, expr=E2}) ->
    io:format("=== VAR BIND:  ~s ========~n", [N]),
    dump_env(Env),
    {TypE, NextVar} = typ_of(Env, Lvl, E1),
    Env2 = update_counter(NextVar, Env),
    typ_of(update_binding(N, gen(Lvl, TypE), Env2), Lvl+1, E2).

typ_apply(Env, Lvl, TypF, NextVar, Args) ->
    %typ_of(Env, Lvl, N),
    %% we make a deep copy of the function we're unifying 
    %% eso that the types we apply to the function don't 
    %% force every other application to unify with them 
    %% where the other callers may be expecting a 
    %% polymorphic function.  See Pierce's TAPL, chapter 22.
    CopiedTypF = deep_copy_type(TypF, maps:new()),
    
    {ArgTypes, NextVar2} = 
        typ_list(Args, Lvl, update_counter(NextVar, Env), []),

    TypRes = new_cell(t_rec),
    Env2 = update_counter(NextVar2, Env),
    
    Arrow = new_cell({t_arrow, ArgTypes, TypRes}),
    case unify(CopiedTypF, Arrow) of
        {error, _} = E ->
            E;
        ok ->
            #env{next_var=VarNum} = Env2,
            {TypRes, VarNum}
    end.

-spec extract_fun(
        Env::env(), 
        ModuleName::atom(), 
        FunName::string(), 
        Arity::integer()) -> {ok, mlfe_module(), mlfe_fun_def()} |
                             {error, {no_module, atom()}} |
                             {error, {not_exported, string(), integer()}} .
extract_fun(Env, ModuleName, FunName, Arity) ->
    case [M || M <- Env#env.modules, M#mlfe_module.name =:= ModuleName] of
        [] -> {error, {no_module, ModuleName}};
        [Module] ->
            Exports = Module#mlfe_module.function_exports,
            case [F || {FN, A} = F <- Exports, FN =:= FunName, A =:= Arity] of
                [_] -> get_fun(Module, FunName, Arity);
                []  -> {error, {not_exported, FunName, Arity}}
            end
    end.

-spec get_fun(
        Module::mlfe_module(), 
        FunName::string(), 
        Arity::integer()) -> {ok, mlfe_fun_def()} |
                             {error, {not_found, atom(), string, integer()}}.
get_fun(Module, FunName, Arity) ->
    case filter_to_fun(Module#mlfe_module.functions, FunName, Arity) of
        not_found    -> {error, {not_found, Module, FunName, Arity}};
        {ok, Fun} -> {ok, Module, Fun}
    end.

filter_to_fun([], _, _) ->
    not_found;
filter_to_fun(
  [#mlfe_fun_def{name={symbol, _, N}, args=Args}=Fun|_], FN, A) when length(Args) =:= A, N =:= FN ->
    {ok, Fun};
filter_to_fun([_|Rem], FN, Arity) ->
    filter_to_fun(Rem, FN, Arity).
    
%% Find or make a type for each arg from a function's
%% argument list.
args_to_types([], _Lvl, Env, Memo) ->
    {lists:reverse(Memo), Env};
args_to_types([{unit, _}|T], Lvl, Env, Memo) ->
    %% have to give t_unit a name for filtering later:
    args_to_types(T, Lvl, Env, [{unit, t_unit}|Memo]);
args_to_types([{symbol, _, N}|T], Lvl, #env{bindings=Bs} = Env, Memo) ->
    case proplists:get_value(N, Bs) of
        undefined ->
            {Typ, Env2} = new_var(Lvl, Env),
            args_to_types(T, Lvl, update_binding(N, Typ, Env2), [{N, Typ}|Memo]);
        Typ ->
            args_to_types(T, Lvl, Env, [{N, Typ}|Memo])
    end.

%%% For clauses we need to add bindings to the environment for any symbols
%%% (variables) that occur in the pattern.  "NameNum" is used to give 
%%% "wildcard" variable names (the '_' throwaway label) sequential and thus
%%% differing _actual_ variable names.  This is necessary so that two different
%%% occurrences of '_' with different types don't collide in `unify/2` and
%%% thus cause typing to fail when it really should succeed.
%%% 
%%% In addition to the type determined for the thing we're adding bindings from,
%%% the return type includes the modified environment with those new bindings
%%% we've added along with the updated "NameNum" value so that we can recurse
%%% through a data structure with `add_bindings/4`.
-spec add_bindings(
        mlfe_expression(), 
        env(), 
        Lvl::integer(),
        NameNum::integer()) -> {typ(), env(), integer()}.
add_bindings({symbol, _, Name}, Env, Lvl, NameNum) ->
    {Typ, Env2} = new_var(Lvl, Env),
    {Typ, update_binding(Name, Typ, Env2), NameNum};

%%% A single occurrence of the wildcard doesn't matter here as the renaming
%%% only occurs in structures where multiple instances can show up, e.g.
%%% in tuples and lists.

add_bindings({'_', _}, Env, Lvl, NameNum) ->
    {Typ, Env2} = new_var(Lvl, Env),
    {Typ, update_binding('_', Typ, Env2), NameNum};

%%% Tuples are a slightly more involved case since we want a type for the
%%% whole tuple as well as any explicit variables to be available in the
%%% result side of the clause.
add_bindings(#mlfe_tuple{values=_}=Tup1, Env, Lvl, NameNum) ->
    {#mlfe_tuple{values=Vs}=Tup2, NN2} = rename_wildcards(Tup1, NameNum),
    {Env2, NN3} = lists:foldl(
                    fun (V, {EnvAcc, NN}) -> 
                            {_Typ, NewEnv, NewNN} = add_bindings(V, EnvAcc, Lvl, NN),
                            {NewEnv, NewNN}
                    end, 
                    {Env, NN2}, 
                    Vs),
    {Typ, NextVar} = typ_of(Env2, Lvl, Tup2),
    
    {Typ, update_counter(NextVar, Env2), NN3};

add_bindings(#mlfe_cons{}=Cons, Env, Lvl, NameNum) ->
    {#mlfe_cons{head=H, tail=T}=RenCons, NN2} = rename_wildcards(Cons, NameNum),
    {_, Env2, NN3} = add_bindings(H, Env, Lvl, NN2),
    {_, Env3, NN4} = add_bindings(T, Env2, Lvl, NN3),
    {Typ, NextVar} = typ_of(Env3, Lvl, RenCons),
    {Typ, update_counter(NextVar, Env3), NN4};

add_bindings(Exp, Env, Lvl, NameNum) ->
    {Typ, NextVar} = typ_of(Env, Lvl, Exp),
    {Typ, update_counter(NextVar, Env), NameNum}.

%%% Tuples may have multiple instances of the '_' wildcard/"don't care"
%%% symbol.  Each instance needs a unique name for unification purposes
%%% so the individual occurrences of '_' get renamed with numbers in order,
%%% e.g. (1, _, _) would become (1, _0, _1).
rename_wildcards(#mlfe_tuple{values=Vs}=Tup, NameNum) ->
    {Renamed, NN} = rename_wildcards(Vs, NameNum),
    {Tup#mlfe_tuple{values=Renamed}, NN};
rename_wildcards(#mlfe_cons{head=H, tail=T}, NameNum) ->
    {RenH, N1} = rename_wildcards(H, NameNum),
    {RenT, N2} = rename_wildcards(T, N1),
    {#mlfe_cons{head=RenH, tail=RenT}, N2};
    
rename_wildcards(Vs, NameNum) when is_list(Vs) ->
    Folder = fun(V, {Acc, N}) ->
                     {NewOther, NewN} = rename_wildcards(V, N),
                     {[NewOther|Acc], NewN}
             end,
    {Renamed, NN} = lists:foldl(Folder, {[], NameNum}, Vs),
    {lists:reverse(Renamed), NN};
rename_wildcards({'_', L}, N) ->
    {{symbol, L, integer_to_list(N)++"_"}, N+1};
rename_wildcards(O, N) ->
    {O, N}.

dump_env(#env{next_var=V, bindings=Bs}) ->
    io:format("Next var number is ~w~n", [V]),
    [io:format("Env:  ~s ~s~n", [N, dump_term(T)])||{N, T} <- Bs].

dump_term({t_arrow, Args, Ret}) ->
    io_lib:format("~s -> ~s", [[dump_term(A) || A <- Args], dump_term(Ret)]);
dump_term({t_clause, P, G, R}) ->
    io_lib:format(" | ~s ~s -> ~s", [dump_term(X)||X<-[P, G, R]]);
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

clause_test_() ->
    [?_assertMatch({{t_clause, t_int, none, t_atom}, _},
                   typ_of(
                     new_env(),
                     #mlfe_clause{pattern={int, 1, 1}, 
                                  result={atom, 1, true}})),
     ?_assertMatch({{t_clause, {unbound, t0, 0}, none, t_atom}, _},
                   typ_of(
                     new_env(),
                     #mlfe_clause{pattern={symbol, 1, "x"},
                                  result={atom, 1, true}})),
     ?_assertMatch({{t_clause, t_int, none, t_int}, _},
                   typ_of(
                     new_env(),
                     #mlfe_clause{pattern={symbol, 1, "x"},
                                  result=#mlfe_apply{
                                            name={bif, '+', 1, erlang, '+'},
                                            args=[{symbol, 1, "x"},
                                                  {int, 1, 2}]}}))
    ].

match_test_() ->
    [?_assertMatch({{t_arrow, [t_int], t_int}, _},
                   top_typ_of("f x = match x with\n  i -> i + 2")),
     ?_assertMatch({error, {cannot_unify, _, _}},
                   top_typ_of(
                     "f x = match x with\n"
                     "  i -> i + 1\n"
                     "| :atom -> 2")),
     ?_assertMatch({{t_arrow, [t_int], t_atom}, _},
                   top_typ_of(
                     "f x = match x + 1 with\n"
                     "  1 -> :x_was_zero\n"
                     "| 2 -> :x_was_one\n"
                     "| _ -> :x_was_more_than_one"))
    ].

tuple_test_() ->
    [?_assertMatch({{t_arrow, 
                    [{t_tuple, [t_int, t_float]}], 
                    {t_tuple, [t_float, t_int]}}, _},
                   top_typ_of(
                     "f tuple = match tuple with\n"
                     " (i, f) -> (f +. 1.0, i + 1)")),
     ?_assertMatch({{t_arrow, [t_int], {t_tuple, [t_int, t_atom]}}, _},
                   top_typ_of("f i = (i + 2, :plus_two)")),
     ?_assertMatch({error, _},
                   top_typ_of(
                     "f x = match x with\n"
                     "  i -> i + 1\n"
                     "| (_, y) -> y + 1\n")),
     ?_assertMatch({{t_arrow, [{t_tuple, 
                                [{unbound, A, _}, 
                                 {unbound, B, _},
                                 {t_tuple, 
                                  [t_int, t_int]}]}],
                     {t_tuple, [t_int, t_int]}}, _},
                   top_typ_of(
                     "f x = match x with\n"
                     " (_, _, (1, x)) -> (x + 2, 1)\n"
                     "|(_, _, (_, x)) -> (x + 2, 50)\n"))
    ].

list_test_() ->
    [?_assertMatch({{t_list, t_float}, _},
                   top_typ_of("1.0 :: []")),
     ?_assertMatch({{t_list, t_int}, _},
                   top_typ_of("1 :: 2 :: []")),
     ?_assertMatch({error, _}, top_typ_of("1 :: 2.0 :: []")),
     ?_assertMatch({{t_arrow, 
                     [{unbound, A, _}, {t_list, {unbound, A, _}}],
                     {t_list, {unbound, A, _}}}, _},
                   top_typ_of("f x y = x :: y")),
     ?_assertMatch({{t_arrow, [{t_list, t_int}], t_int}, _},
                   top_typ_of(
                     "f list = match list with\n"
                     " h :: t -> h + 1")),
     %% Ensure that a '_' in a list nested in a tuple is renamed properly
     %% so that one does NOT get unified with the other when they're 
     %% potentially different types:
     ?_assertMatch({{t_arrow,
                    [{t_tuple, [{t_list, t_int}, {unbound, _, _}, t_float]}],
                    {t_tuple, [t_int, t_float]}}, _},
                   top_typ_of(
                     "f list_in_tuple =\n"
                     "  match list_in_tuple with\n"
                     "   (h :: 1 :: _ :: t, _, f) -> (h, f +. 3.0)")),
     ?_assertMatch({error, {cannot_unify, t_int, t_float}},
                   top_typ_of(
                     "f should_fail x =\n"
                     "let l = 1 :: 2 :: 3 :: [] in\n"
                     "match l with\n"
                     " a :: b :: _ -> a +. b"))
    ].

module_typing_test() ->
    Code =
        "module typing_test\n\n"
        "export add/2\n\n"
        "add x y = x + y\n\n"
        "head l = match l with\n"
        "  h :: t -> h",
    {ok, _, _, M} = parser:parse_module(0, Code),
    ?assertMatch(#mlfe_module{
                             functions=[
                                       #mlfe_fun_def{
                                          name={symbol, 5, "add"},
                                          type={t_arrow, 
                                                [t_int, t_int],
                                                t_int}},
                                        #mlfe_fun_def{
                                           name={symbol, 7, "head"},
                                           type={t_arrow,
                                                 [{t_list, {unbound, A, _}}],
                                                 {unbound, A, _}}}
                                       ]},
                 typ_module(M, new_env())).

module_with_forward_reference_test() ->
    Code =
        "module forward_ref\n\n"
        "export add/2\n\n"
        "add x y = adder x y\n\n"
        "adder x y = x + y",
    {ok, _, _, M} = parser:parse_module(0, Code),
    Env = new_env(),
    ?assertMatch(#mlfe_module{
                    functions=[
                               #mlfe_fun_def{
                                  name={symbol, 5, "add"},
                                  type={t_arrow, [t_int, t_int], t_int}},
                               #mlfe_fun_def{
                                  name={symbol, 7, "adder"},
                                  type={t_arrow, [t_int, t_int], t_int}}]},
                 typ_module(M, Env#env{current_module=M, modules=[M]})).

simple_inter_module_test() ->
    Mod1 =
        "module inter_module_one\n\n"
        "add x y = inter_module_two.adder x y",
    Mod2 =
        "module inter_module_two\n\n"
        "export adder/2\n\n"
        "adder x y = x + y",
    {ok, NV, _, M1} = parser:parse_module(0, Mod1),
    {ok, _, _, M2} = parser:parse_module(NV, Mod2),
    E = new_env(),
    Env = E#env{modules=[M1, M2]},
    ?assertMatch(#mlfe_module{
                    function_exports=[],
                    functions=[
                               #mlfe_fun_def{
                                  name={symbol, 3, "add"},
                                  type={t_arrow, [t_int, t_int], t_int}}]},
                  typ_module(M1, Env)).

bidirectional_module_fail_test() ->
    Mod1 =
        "module inter_module_one\n\n"
        "export add/2\n\n"
        "add x y = inter_module_two.adder x y",
    Mod2 =
        "module inter_module_two\n\n"
        "export adder/2, failing_fun/1\n\n"
        "adder x y = x + y\n\n"
        "failing_fun x = inter_module_one.add x x",
    {ok, NV, _, M1} = parser:parse_module(0, Mod1),
    {ok, _, _, M2} = parser:parse_module(NV, Mod2),
    E = new_env(),
    Env = E#env{modules=[M1, M2]},
    ?assertMatch({error, {bidirectional_module_ref, 
                          inter_module_two, 
                          inter_module_one}},
                 typ_module(M2, Env)).

        
recursive_fun_test_() ->
    [?_assertMatch({{t_arrow, [t_int], t_rec}, _},
                   top_typ_of(
                     "f x =\n"
                     "let y = x + 1 in\n"
                     "f y")),
     ?_assertMatch({{t_arrow, [t_int], t_atom}, _},
                   top_typ_of(
                     "f x = match x with\n"
                     "  0 -> :zero\n"
                     "| x -> f (x - 1)")),
     ?_assertMatch({error, {cannot_unify, t_int, t_atom}},
                   top_typ_of(
                     "f x = match x with\n"
                     "  0 -> :zero\n"
                     "| 1 -> 1\n"
                     "| y -> y - 1\n")),
     ?_assertMatch({{t_arrow, [{t_list, {unbound, A, _}}, 
                              {t_arrow, [{unbound, A, _}], {unbound, B, _}}],
                    {t_list, {unbound, B, _}}}, _} when A =/= B,
                   top_typ_of(
                     "map list f = match list with\n"
                     "  [] -> []\n"
                     "| h :: t -> (f h) :: (map t f)"))
    ].

infinite_mutual_recursion_test() ->
    Code =
        "module mutual_rec_test\n\n"
        "a x = b x\n\n"
        "b x = let y = x + 1 in a y",
    {ok, _, _, M} = parser:parse_module(0, Code),
    E = new_env(),
    ?assertMatch(#mlfe_module{
                    name=mutual_rec_test,
                    functions=[
                               #mlfe_fun_def{
                                  name={symbol, 3, "a"},
                                  type={t_arrow, [t_int], t_rec}},
                               #mlfe_fun_def{
                                  name={symbol, 5, "b"},
                                  type={t_arrow, [t_int], t_rec}}]},
                 typ_module(M, E)).

terminating_mutual_recursion_test() ->
    Code =
        "module terminating_mutual_rec_test\n\n"
        "a x = let y = x + 1 in b y\n\n"
        "b x = match x with\n"
        "  10 -> :ten\n"
        "| y -> a y",
    {ok, _, _, M} = parser:parse_module(0, Code),
    E = new_env(),
    ?assertMatch(#mlfe_module{
                    name=terminating_mutual_rec_test,
                    functions=[
                               #mlfe_fun_def{
                                  name={symbol, 3, "a"},
                                  type={t_arrow, [t_int], t_atom}},
                               #mlfe_fun_def{
                                  name={symbol, 5, "b"},
                                  type={t_arrow, [t_int], t_atom}}]},
                 typ_module(M, E)).

ffi_test_() ->
    [?_assertMatch({t_int, _},
                   top_typ_of(
                     "call_erlang :io :format [\"One is ~w~n\", [1]] with\n"
                     " _ -> 1")),
     ?_assertMatch({error, {cannot_unify, t_atom, t_int}},
                   top_typ_of(
                     "call_erlang :a :b [1] with\n"
                     "  (:ok, x) -> 1\n"
                     "| (:error, x) -> :error")),
     ?_assertMatch({{t_arrow, [{unbound, _, _}], t_atom}, _},
                   top_typ_of(
                     "f x = call_erlang :a :b [x] with\n"
                     "  1 -> :one\n"
                     "| _ -> :not_one"))
     
    ].

equality_test_() ->
    [?_assertMatch({t_bool, _}, top_typ_of("1 == 2")),
     ?_assertMatch({{t_arrow, [t_int], t_bool}, _}, 
                   top_typ_of("f x = 1 == x")),
     ?_assertMatch({error, {cannot_unify, _, _}}, top_typ_of("1.0 == 1")),
     ?_assertMatch({{t_arrow, [t_int], t_atom}, _}, 
                   top_typ_of(
                     "f x = match x with\n"
                     " a, a == 0 -> :zero\n"
                     "|b -> :not_zero")),
     ?_assertMatch({error, {cannot_unify, t_float, t_int}},
                   top_typ_of(
                     "f x = match x with\n"
                     "  a -> a + 1\n"
                     "| a, a == 1.0 -> 1"))
                     
    ].

type_guard_test_() ->
    [
     %% In a normal match without union types the is_integer guard should
     %% coerce all of the patterns to t_int:
     ?_assertMatch({{t_arrow, [t_int], t_int}, _},
                   top_typ_of(
                     "f x = match x with\n"
                     "   i, is_integer i -> i\n"
                     " | _ -> 0")),
     %% Calls to Erlang should use a type checking guard to coerce the
     %% type in the pattern for use in the resulting expression:
     ?_assertMatch({t_int, _},
                   top_typ_of(
                     "call_erlang :a :b [5] with\n"
                     "   :one -> 1\n"
                     " | i, i == 2.0 -> 2\n"
                     " | i, is_integer i -> i\n")),
     %% Two results with different types as determined by their guards
     %% should result in a type error:
     ?_assertMatch({error, {cannot_unify, t_int, t_float}},
                   top_typ_of(
                     "call_erlang :a :b [2] with\n"
                     "   i, i == 1.0 -> i\n"
                     " | i, is_integer i -> i")),
     %% Guards should work with items from inside tuples:
     ?_assertMatch({{t_arrow, [{t_tuple, [t_atom, {unbound, _, _}]}], t_atom}, _},
                   top_typ_of(
                     "f x = match x with\n"
                     "   (msg, _), msg == :error -> :error\n"
                     " | (msg, _) -> :ok"))

    ].

    
-endif.
