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

%%% #mlfe_typer.erl
%%% 
%%% This is based off of the sound and eager type inferencer in 
%%% http://okmij.org/ftp/ML/generalization.html with some influence
%%% from https://github.com/tomprimozic/type-systems/blob/master/algorithm_w
%%% where the arrow type and instantiation are concerned.
%%% 
%%% I still often use proplists in this module, mostly because dialyzer doesn't
%%% yet type maps correctly (Erlang 18.1).

-module(mlfe_typer).

-dialyzer({nowarn_function, dump_env/1}).
-dialyzer({nowarn_function, dump_term/1}).

-include("mlfe_ast.hrl").
-include("builtin_types.hrl").

-export([cell/1, new_env/1, replace_env_module/2,
         typ_module/2]).
-export_type([env/0, typ/0, t_cell/0]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.


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
get_cell(Cell) when is_pid(Cell) ->
    Cell ! {get, self()},
    receive
        Val -> Val
    end.


set_cell(Cell, Val) ->
    Cell ! {set, Val},
    ok.

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
%%% Environments track the following:
%%% 
%%% 1. A counter for naming new type variables
%%% 2. The modules entered so far while checking the types of functions called
%%%    in other modules that have not yet been typed.  This is used in a crude
%%%    form of detecting mutual recursion between/across modules.
%%% 3. The current module being checked.
%%% 4. The types available to the current module, eventually including
%%%    imported types.  This is used to find union types.
%%% 5. A proplist from type constructor name to the constructor AST node.
%%% 6. A proplist from type name to its instantiated ADT record.
%%% 7. A proplist of {expression name, expression type} for the types
%%%    of values and functions so far inferred/checked.
%%% 8. The set of modules included in type checking.
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

-record(env, {
          next_var=0           :: integer(),
          entered_modules=[]   :: list(atom()),
          current_module=none  :: none | mlfe_module(),
          current_types=[]     :: list(mlfe_type()),
          type_constructors=[] :: list({string(), mlfe_constructor()}),
          type_bindings=[]     :: list({string(), t_adt()}),
          bindings=[]          :: list({term(), typ()|t_cell()}),
          modules=[]           :: list(mlfe_module())
}).

-type env() :: #env{}.

new_env(Mods) ->
    #env{bindings=[celled_binding(Typ)||Typ <- ?all_bifs],
         modules=Mods}.

%%% We need to build a proplist of type constructor name to the actual type 
%%% constructor's AST node and associated type.
-spec constructors(list(mlfe_type())) -> list({string(), mlfe_constructor()}).
constructors(Types) ->
    MemberFolder = fun(#mlfe_constructor{name={type_constructor, _, N}}=C, {Type, Acc}) ->
                           WithType = C#mlfe_constructor{type=Type},
                           {Type, [{N, WithType}|Acc]};
                      (_, Acc) ->
                           Acc
                   end,
    TypesFolder = fun(#mlfe_type{members=Ms}=Typ, Acc) ->
                          {_, Cs} = lists:foldl(MemberFolder, {Typ, []}, Ms),
                          [Cs|Acc]
                  end,
    lists:flatten(lists:foldl(TypesFolder, [], Types)).

%% Given a presumed newly-typed module, replace its untyped occurence within
%% the supplied environment.  If the module does *not* exist in the environment,
%% it will be added.
replace_env_module(#env{modules=Ms}=E, #mlfe_module{name=N}=M) ->
    E#env{modules = [M | [X || #mlfe_module{name=XN}=X <- Ms, XN /= N]]}.

celled_binding({Name, {t_arrow, Args, Ret}}) ->
    {Name, {t_arrow, [new_cell(A) || A <- Args], new_cell(Ret)}}.

update_binding(Name, Typ, #env{bindings=Bs} = Env) ->
    Env#env{bindings=[{Name, Typ}|[{N, T} || {N, T} <- Bs, N =/= Name]]}.

update_counter(VarNum, Env) ->
    Env#env{next_var=VarNum}. 

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

%%% Deep copying is used only for function application so we extract the
%%% arrow for typing here:
deep_copy_type({t_receiver, _, {t_arrow, _, _}=Arrow}, RefMap) ->
    deep_copy_type(Arrow, RefMap);
deep_copy_type({t_receiver, A, B}, RefMap) ->
    {t_receiver, deep_copy_type(A, RefMap), deep_copy_type(B, RefMap)};

deep_copy_type(T, _) ->
    T.

copy_type(P, RefMap) when is_pid(P) ->
    copy_cell(P, RefMap);
copy_type(T, M) ->
    {new_cell(T), M}.

%%% ## Type Inferencer

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
occurs(_L, _Lvl, T) ->
    T.

unwrap_cell(C) when is_pid(C) ->
    unwrap_cell(get_cell(C));
unwrap_cell(Typ) ->
    Typ.

%% Get the name of the current module out of the environment.  Useful for
%% error generation.
module_name(#env{current_module=#mlfe_module{name=N}}) ->
    N;
module_name(_) ->
    undefined.

-type unification_error() :: {error, {cannot_unify, atom(), integer(), typ(), typ()}}.
%% I make unification error tuples everywhere, just standardizing their
%% construction here:
-spec unify_error(Env::env(), Line::integer(), typ(), typ()) -> unification_error().
unify_error(Env, Line, Typ1, Typ2) ->
    io:format("Failed on ~w ~w~n", [unwrap(Typ1), unwrap(Typ2)]),
    {error, {cannot_unify, module_name(Env), Line, Typ1, Typ2}}.

%%% Unify now requires the environment not in order to make changes to it but
%%% so that it can look up potential type unions when faced with unification
%%% errors.  
-spec unify(typ(), typ(), env(), integer()) -> ok | {error, term()}.
unify(T1, T2, Env, Line) ->
    case {unwrap_cell(T1), unwrap_cell(T2)} of
        {T, T} ->
            ok;
        %% only one instance of a type variable is permitted:
        {{unbound, N, _}, {unbound, N, _}}  -> unify_error(Env, Line, T1, T2);
        {{link, Ty}, _} ->
            unify(Ty, T2, Env, Line);
        {_, {link, Ty}} ->
            unify(T1, Ty, Env, Line);
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
        %%% This section creeps me right out at the moment.  This is where some
        %%% other operator that moves the receiver to the outside should be.
        %%% Smells like a functor or monad to me.
        {{t_arrow, _, A2}, {t_arrow, _, B2}} ->
            ArrowArgCells = fun(C) when is_pid(C) ->
                                    {t_arrow, Xs, _}=get_cell(C),
                                    Xs;
                               ({t_arrow, Xs, _}) -> Xs
                            end,
            case unify_list(ArrowArgCells(T1), ArrowArgCells(T2), Env, Line) of
                {error, _} = E  -> E;
                _ ->
                    %% Unwrap cells and links down to the first non-cell level.
                    %% Super gross.
                    F = fun(C) when is_pid(C) ->
                                case get_cell(C) of
                                    {t_receiver, _, _}=R -> 
                                        R;
                                    {link, CC} when is_pid(CC) -> case get_cell(CC) of
                                                     {t_receiver, _, _}=R2 -> R2;
                                                      _ -> none
                                                  end;
                                    {link, {t_receiver, _, _}=R2} -> R2;
                                    _ -> none
                                end;
                           ({link, CC}) when is_pid(CC) -> 
                                case get_cell(CC) of
                                    {t_receiver, _, _}=R2 -> R2;
                                    _ -> none
                                end;
                           ({t_receiver, _, _}=X) -> X;
                           (_) -> none
                        end,
                    AArgs = case T1 of
                                _ when is_pid(T1) ->
                                    {t_arrow, Xs, _}=get_cell(T1),
                                    Xs;
                                _ ->
                                    {t_arrow, Xs, _}=T1,
                                    Xs
                            end,

                    StripCell = fun(C) when is_pid(C) -> get_cell(C);
                                   ({link, C}) when is_pid(C) -> get_cell(C);
                                   ({link, X}) -> X;
                                   (X) -> X
                                end,
                    NoCellArgs = lists:map(StripCell, lists:map(StripCell, AArgs)),
                    RR = [Receiver||{t_receiver, _, _}=Receiver 
                                        <- lists:map(F, NoCellArgs)],
                    %% Any argument to a function application that is a receiver
                    %% makes the entire expression a receiver.
                    case RR of
                        [] -> 
                            unify(A2, B2, Env, Line);
                        %% The received types for each receiver must unify in
                        %% order for the process to be typed correctly.
                        [{t_receiver, H, _}|Tail] ->
                            Unify = fun(_, {error, _}=Err) -> Err;
                                       ({t_receiver, T, _}, Acc) -> 
                                            case unify(T, Acc, Env, Line) of
                                                {error, _}=Err -> Err;
                                                ok -> T
                                            end;
                                       (_Other, Acc) ->
                                            Acc
                                    end,
                            case lists:foldl(Unify, H, Tail) of
                                {error, _}=Err -> Err;
                                _ ->
                                    case unify(A2, B2, Env, Line) of
                                        {error, _}=Err -> Err;
                                        ok ->
                                            %% Re-wrapping with fresh cells because
                                            %% I was running into cycles.  This
                                            %% entire block of arrow unification
                                            %% needs to be rewritten.
                                            Receiver = {t_receiver, 
                                                        new_cell(unwrap(H)),
                                                        new_cell(unwrap(A2))},
                                            set_cell(A2, Receiver),
                                            set_cell(B2, {link, A2}),
                                            ok
                                    end
                            end
                    end
            end;
        {{t_tuple, A}, {t_tuple, B}} when length(A) =:= length(B) ->
            case unify_list(A, B, Env, Line) of
                {error, _} = Err -> Err;
                _                -> ok
            end;
        {{t_list, _}, t_nil} ->
            set_cell(T2, {link, T1}),
            ok;
        {t_nil, {t_list, _}} ->
            set_cell(T1, {link, T2}),
            ok;
        {{t_list, A}, {t_list, B}} ->
            unify(A, B, Env, Line);
        {{t_list, A}, B} ->
            unify(A, B, Env, Line);
        {A, {t_list, B}} ->
            unify(A, B, Env, Line);
        {#adt{}=A, B} -> unify_adt(T1, T2, A, B, Env, Line);
        {A, #adt{}=B} -> unify_adt(T2, T1, B, A, Env, Line);

        {{t_pid, _}, {t_pid, _}} ->
            {t_pid, AC} = get_cell(T1),
            {t_pid, BC} = get_cell(T2),
            case unify(AC, BC, Env, Line) of
                {error, _}=Err -> Err;
                ok ->
                    set_cell(T1, new_cell({t_pid, AC})),
                    set_cell(T2, {link, T1}),
                    ok
            end;    
        
        %%% Receivers unify with each other or in the case of a receiver and
        %%% something else, the receiver unifies its result type with the other
        %%% expression and both become receivers.
        {{t_receiver, _, _}, {t_receiver, _, _}} ->
            RecvRes = fun(C) when is_pid(C) ->
                              {t_receiver, _, X} = get_cell(C),
                              X;
                          ({t_receiver, _, X}) -> 
                              X
                       end,
            RecvR = fun(C) when is_pid(C) ->
                            {t_receiver, X, _} = get_cell(C),
                            X;
                       ({t_receiver, X, _}) -> 
                            X
                       end,
            case unify(RecvR(T1), RecvR(T2), Env, Line) of
                {error, _}=Err -> Err;
                ok -> case unify(RecvRes(T1), RecvRes(T2), Env, Line) of
                          {error, _}=Err -> Err;
                          ok -> 
                              set_cell(T2, {link, T1}),
                              ok
                      end
            end;
        {{t_receiver, Recv, ResA}, {t_arrow, Args, ResB}} ->
            case unify(ResA, ResB, Env, Line) of
                {error, _}=Err -> Err;
                ok ->
                    NewTyp = {t_receiver, Recv, {t_arrow, Args, ResA}},
                    set_cell(T1, NewTyp),
                    set_cell(T2, {link, T1}),
                    ok
            end;
        {{t_arrow, _, _}, {t_receiver, _, _}} ->
            unify(T2, T1, Env, Line);
        {{t_receiver, _Recv, ResA}, B} ->
            case unify(ResA, new_cell(B), Env, Line) of
                {error, _}=Err -> Err;
                ok ->
                    set_cell(T2, {link, T1}),
                    ok
                end;
        {_A, {t_receiver, _Recv, _ResB}} ->
            unify(T2, T1, Env, Line);
        {_T1, _T2} ->
            case find_covering_type(_T1, _T2, Env, Line) of
                {error, _}=Err -> 
                    io:format("UNIFY FAIL:  ~w AND ~w~n", [unwrap(T1), unwrap(T2)]),
                    io:format("LINE ~w~n", [Line]),
                    Err;
                {ok, _EnvOut, Union} ->
                    io:format("UNIFIED ~w AND ~w on ~w~n", 
                              [unwrap(_T1), unwrap(_T2), unwrap(Union)]),
                    set_cell(T1, Union),
                    set_cell(T2, Union),
                    %% TODO:  output environment.
                    ok
            end
    end.

%%% Here we're checking for membership of one party in another or for an
%%% exact match.
-spec unify_adt(t_cell(), t_cell(), t_adt(), typ(), env(), Line::integer()) -> 
                       ok | 
                       {error, {cannot_unify, typ(), typ()}}.
unify_adt(C1, C2, #adt{name=N, vars=AVars}=A, #adt{name=N, vars=BVars}, Env, L) ->
    %% Don't unify the keys _and_ vars:
    case unify_list([V||{_, V} <- AVars], [V||{_, V} <- BVars], Env, L) of
        {error, _}=Err -> Err;
        _ -> 
            set_cell(C1, A),
            set_cell(C2, {link, C1}),
            ok
    end;
unify_adt(C1, C2, #adt{vars=Vs, members=Ms}=A, AtomTyp, Env, L) when is_atom(AtomTyp) ->
    case [M||M <- Ms, unwrap(M) =:= AtomTyp] of
        [_] -> 
            set_cell(C1, A),
            set_cell(C2, {link, C1}),
            ok;
        []  -> 
            VFolder = fun(_, ok) -> ok;
                         ({_, V}, _) -> unify(AtomTyp, V, Env, L)
                      end,
            lists:foldl(VFolder, unify_error(Env, L, A, AtomTyp), Vs)
    end;

%% If an ADTs members are empty, it's a reference to an ADT that should
%% be instantiated in the environment.  Replace it with the instantiated
%% version before proceeding.  Having separate cases for A and B is
%% bothering me.
unify_adt(C1, C2, #adt{name=NA, members=[]}, B, Env, L) ->
    case proplists:get_value(NA, Env#env.type_bindings) of
        undefined -> {error, {no_type_for_name, NA}};
        ADT       -> unify_adt(C1, C2, ADT, B, Env, L)
    end;

unify_adt(_C1, _C2, 
          #adt{name=NA, vars=VarsA, members=MA}=A, 
          #adt{name=NB, vars=VarsB, members=MB}=B, Env, L) ->
    MemberFilter = fun(N) -> fun(#adt{name=AN}) when N =:= AN -> true;
                                (_) -> false
                             end
                   end,
    case lists:filter(MemberFilter(NB), MA) of 
        [#adt{vars=ToCheck}] ->
            UnifyFun = fun(_, {error, _}=Err)    -> Err;
                          ({{_, X}, {_, Y}}, ok) -> unify(L, X, Y, Env)
                       end,
            lists:foldl(UnifyFun, ok, lists:zip(VarsB, ToCheck));
        _ ->
            case lists:filter(MemberFilter(NA), MB) of 
                [#adt{vars=ToCheck}] ->
                    UnifyFun = fun(_, {error, _}=Err)    -> Err;
                                  ({{_, X}, {_, Y}}, ok) -> unify(L, X, Y, Env)
                               end,
                    lists:foldl(UnifyFun, ok, lists:zip(VarsA, ToCheck));
                _ -> unify_error(Env, L, A, B)
            end
    end;

unify_adt(C1, C2, #adt{members=Ms}=A, {t_tuple, _}=ToCheck, Env, L) ->
    %% Try to find an ADT member that will unify with the passed in tuple:
    F = fun(_, ok) -> ok;
           (T, Res) -> 
                case unify(ToCheck, T, Env, L) of
                    ok -> 
                        set_cell(C2, {link, C1}),
                        ok;
                    _ -> 
                        Res
                end
        end,
    Seed = unify_error(Env, L, A, ToCheck),
    lists:foldl(F, Seed, Ms);

unify_adt(_, _, A, B, Env, L) ->
    unify_error(Env, L, A, B).

%%% Given two different types, find a type in the set of currently available
%%% types that can unify them or fail.
-spec find_covering_type(
        T1::typ(), 
        T2::typ(), 
        env(),
        integer()) -> {ok, typ(), env()} | 
                      {error, 
                       {cannot_unify, atom(), integer(), typ(), typ()} |
                       {bad_variable, integer(), mlfe_type_var()}}.
find_covering_type(T1, T2, #env{current_types=Ts}=EnvIn, L) ->
    io:format("Covering for ~w ~w ~w ~w~n", [T1, unwrap(T1), T2, unwrap(T2)]),
    %% Convert all the available types to actual ADT types with
    %% which to attempt unions:
    TypeFolder = fun(_ ,{error, _}=Err) ->
                         Err;
                    (Typ, {ADTs, E}) ->
                         case inst_type(Typ, E) of
                             {error, _}=Err    -> Err;
                             {ok, E2, ADT, Ms} -> {[{ADT, Ms}|ADTs], E2}
                         end
                 end,

    %%% We remove all of the types from the environment because we don't want
    %%% to reinstantiate them again on unification failure when it's trying 
    %%% to unify the two types with the instantiated member types.
    %%% 
    %%% For example, if `T1` is `t_int` and the first member of a type we're
    %%% checking for valid union is anything _other_ that `t_int`, the call
    %%% to `unify` in `try_types` will cause `unify` to call this method
    %%% (`find_covering_type`) again, leading to instantiating all of the
    %%% types all over again and eventually leading to a spawn limit error.
    %%% By simply removing the types from the environment before proceeding,
    %%% we avoid this cycle.
    case lists:foldl(TypeFolder, {[], EnvIn#env{current_types=[]}}, Ts) of
        {error, _}=Err -> Err;
        {ADTs, EnvOut} ->
            ReturnEnv = EnvOut#env{current_types=EnvIn#env.current_types},
            %% each type, filter to types that are T1 or T2, if the list
            %% contains both, it's a match.
            F = fun(_, {ok, _}=Res) ->
                        Res;
                   ({ADT, Ms}, Acc) ->
                        case try_types(T1, T2, Ms, EnvOut, L, {none, none}) of
                            {ok, ok} -> {ok, ReturnEnv, ADT};
                            _ -> Acc
                        end
                end,
            Default = unify_error(EnvIn, L, T1, T2),
            lists:foldl(F, Default, lists:reverse(ADTs))
    end.

%%% try_types/5 attempts to unify the two given types with each ADT available
%%% to the module until one is found that covers both types or we run out of
%%% available types, yielding `'no_match'`.
try_types(_, _, _, _, _, {ok, ok}=Memo) ->
    Memo;
try_types(T1, T2, [Candidate|Tail], Env, L, {none, none}) ->
    case unify(T1, Candidate, Env, L) of
        ok -> try_types(T1, T2, Tail, Env, L, {ok, none});
        _ -> case unify(T2, Candidate, Env, L) of
                 ok -> try_types(T1, T2, Tail, Env, L, {none, ok});
                 _ -> try_types(T1, T2, Tail, Env, L, {none, none})
             end
    end;
try_types(T1, T2, [Candidate|Tail], Env, L, {none, M2}=Memo) ->
    case unify(T1, Candidate, Env, L) of
        ok -> try_types(T1, T2, Tail, Env, L, {ok, M2});
        _  -> try_types(T1, T2, Tail, Env, L, Memo)
    end;
try_types(T1, T2, [Candidate|Tail], Env, L, {M1, none}=Memo) ->
    case unify(T2, Candidate, Env, L) of
        ok -> try_types(T1, T2, Tail, Env, L, {M1, ok});
        _  -> try_types(T1, T2, Tail, Env, L, Memo)
    end;
try_types(_, _, [], _, _, _) ->
    no_match.


%%% To search for a potential union, a type's variables all need to be
%%% instantiated and its members that are other types need to use the
%%% same variables wherever referenced.  The successful returned elements
%%% (not including `'ok'`) include:
%%% 
%%% - the instantiated type as an `#adt{}` record, with real type variable
%%%   cells.
%%% - a list of all members that are _types_, so type variables, tuples, and
%%%   other types but _not_ ADT constructors.  
%%% 
%%% Any members that are polymorphic types (AKA "generics") must reference 
%%% only the containing type's variables or an error will result.
%%% 
%%% In the `VarFolder` function you'll see that I always use a level of `0`
%%% for type variables.  My thinking here is that since types are only 
%%% defined at the top level, their variables are always created at the 
%%% highest level.  I might be wrong here and need to include the typing
%%% level as passed to inst/3 as well.
-spec inst_type(mlfe_type(), EnvIn::env()) -> 
                       {ok, env(), typ(), list(typ())} | 
                       {error, {bad_variable, integer(), mlfe_type_var()}}.
inst_type(Typ, EnvIn) ->
    #mlfe_type{name={type_name, _, N}, vars=Vs, members=Ms} = Typ,
    VarFolder = fun({type_var, _, VN}, {Vars, E}) ->
                        {TVar, E2} = new_var(0, E),
                        {[{VN, TVar}|Vars], E2}
                end,    
    {Vars, Env} = lists:foldl(VarFolder, {[], EnvIn}, Vs),
    ParentADT = #adt{name=N, vars=lists:reverse(Vars)},
    inst_type_members(ParentADT, Ms, Env, []).

inst_type_members(ParentADT, [], Env, FinishedMembers) ->
    {ok, 
     Env, 
     new_cell(ParentADT#adt{members=FinishedMembers}), 
     lists:reverse(FinishedMembers)};
%% single atom types are passed unchanged (built-in types):
inst_type_members(ParentADT, [H|T], Env, Memo) when is_atom(H) ->
    inst_type_members(ParentADT, T, Env, [new_cell(H)|Memo]);
inst_type_members(ADT, [{mlfe_list, TExp}|Rem], Env, Memo) ->
    case inst_type_members(ADT, [TExp], Env, []) of
        {error, _}=Err -> Err;
        {ok, Env2, _, [InstMem]} ->
            inst_type_members(ADT, Rem, Env2, [new_cell({t_list, InstMem})|Memo])
    end;
inst_type_members(ADT, [{mlfe_pid, TExp}|Rem], Env, Memo) ->
    case inst_type_members(ADT, [TExp], Env, []) of
        {error, _}=Err -> Err;
        {ok, Env2, _, [InstMem]} ->
            inst_type_members(ADT, Rem, Env2, [new_cell({t_pid, InstMem})|Memo])
    end;

inst_type_members(#adt{vars=Vs}=ADT, [{type_var, L, N}|T], Env, Memo) ->
    Default = {error, {bad_variable, L, N}},
    case proplists:get_value(N, Vs, Default) of
        {error, _}=Err -> Err;
        Typ -> inst_type_members(ADT, T, Env, [Typ|Memo])
    end;
inst_type_members(ADT, [#mlfe_type_tuple{members=Ms}|T], Env, Memo) ->
    case inst_type_members(ADT, Ms, Env, []) of
        {error, _}=Err ->
            Err;
        {ok, Env2, _, InstMembers} ->
            inst_type_members(ADT, T, Env2, [new_cell({t_tuple, InstMembers})|Memo])
    end;

inst_type_members(ADT,
                  [#mlfe_type{name={type_name, _, N}, vars=Vs, members=[]}|T],
                  Env,
                  Memo) ->
    case inst_type_members(ADT, Vs, Env, []) of
        {error, _}=Err -> Err;
        {ok, Env2, _, Members} -> 
            Names = [VN || {type_var, _, VN} <- Vs],
            NewMember = #adt{name=N, vars=lists:zip(Names, Members)},
            inst_type_members(ADT, T, Env2, [NewMember|Memo])
    end;
inst_type_members(ADT, [#mlfe_constructor{name={_, _, N}}|T], Env, Memo) ->
    inst_type_members(ADT, T, Env, [{t_adt_cons, N}|Memo]);
%% Everything else gets discared.  Type constructors are not types in their 
%% own right and thus not eligible for unification so we just discard them here:
inst_type_members(ADT, [_|T], Env, Memo) ->
    inst_type_members(ADT, T, Env, Memo).    

%%% When the typer encounters the application of a type constructor, we can
%%% treat it somewhat like a typ arrow vs a normal function arrow (see
%%% `typ_apply/5`).  The difference is that the arity is always `1` and the 
%%% result type may contain numerous type variables rather than the single 
%%% type variable in a normal arrow.  Example:
%%% 
%%%     type t 'x 'y = A 'x | B 'y
%%% 
%%%     f z = A (z + 1)
%%% 
%%% We need a way to unify the constructor application with a type constructor
%%% arrow that will yield something matching the following:
%%% 
%%%     #adt{name="t", vars=[t_int, {unbound, _, _}]
%%%
%%% To do this, `inst_type_arrow` builds a type arrow that uses the same type
%%% variable cells in the argument as in the return type, which is of course
%%% an instantiated instance of the ADT.  If the "type arrow" unifies with
%%% the argument in the actual constructor application, the return of the type 
%%% arrow will have the correct variables instantiated.
-spec inst_type_arrow(Env::env(), Name::mlfe_constructor_name()) ->
                             {ok, env(), {typ_arrow, typ(), t_adt()}} |
                             {error, {bad_constructor, integer(), string()}}.
inst_type_arrow(EnvIn, {type_constructor, Line, Name}) ->
    %% 20160603:  I have an awful lot of case ... of all over this
    %% codebase, trying a lineup of functions specific to this 
    %% task here instead.  Sort of want Scala's `Try`.
    ADT_f = fun({error, _}=Err) -> Err;
               (#mlfe_constructor{type=#mlfe_type{}=T}=C) -> {C, inst_type(T, EnvIn)}
            end,
    Cons_f = fun({_, {error, _}=Err}) ->Err;
                ({C, {ok, Env, ADT, _}}) -> 
                     #adt{vars=Vs} = get_cell(ADT),
                     #mlfe_constructor{arg=Arg} = C,
                     Arrow = {type_arrow, inst_constructor_arg(Arg, Vs), ADT},
                     {Env, Arrow}
             end,
    Default = {error, {bad_constructor, Line, Name}},
    C = proplists:get_value(Name, EnvIn#env.type_constructors, Default),
    Cons_f(ADT_f(C)).

inst_constructor_arg(none, _) ->
    t_unit;
inst_constructor_arg(AtomType, _) when is_atom(AtomType) ->
    AtomType;
inst_constructor_arg({type_var, _, N}, Vs) ->
    proplists:get_value(N, Vs);
inst_constructor_arg(#mlfe_type_tuple{members=Ms}, Vs) ->
    new_cell({t_tuple, [inst_constructor_arg(M, Vs) || M <- Ms]});
inst_constructor_arg(#mlfe_type{name={type_name, _, N}, vars=Vars}, Vs) ->
    ADT_vars = [{VN, proplists:get_value(VN, Vs)} || {type_var, _, VN} <- Vars],
    new_cell(#adt{name=N, vars=ADT_vars});
inst_constructor_arg(Arg, _) ->
    {error, {bad_constructor_arg, Arg}}.

%% Unify two parameter lists, e.g. from a function arrow.
unify_list(As, Bs, Env, L) ->
    unify_list(As, Bs, {[], []}, Env, L).

arity_error(Env, L) ->
    {error, {module_name(Env), L}}.

unify_list([], [], {MemoA, MemoB}, _, _) ->
    {lists:reverse(MemoA), lists:reverse(MemoB)};
unify_list([], _, _, Env, L) ->
    arity_error(Env, L);
unify_list(_, [], _, Env, L) ->
    arity_error(Env, L);
unify_list([A|TA], [B|TB], {MA, MB}, Env, L) ->
    case unify(A, B, Env, L) of
        {error, _} = E -> E;
        ok -> unify_list(TA, TB, {[A|MA], [B|MB]}, Env, L)
    end.


-spec inst(
        VarName :: atom()|string(), 
        Lvl :: integer(), 
        Env :: env()) -> {typ(), env(), map()} | {error, term()}.

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
    case typ_of(Env, Lvl, H) of
        {error, _}=Err -> Err;
        {Typ, NextVar} ->
            typ_list(T, Lvl, update_counter(NextVar, Env), [Typ|Memo])
    end.

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
unwrap(#adt{vars=Vs, members=Ms}=ADT) ->
    ADT#adt{vars=[{Name, unwrap(V)} || {Name, V} <- Vs],
            members=[unwrap(M) || M <- Ms]};
unwrap({t_receiver, A, B}) ->
    {t_receiver, unwrap(A), unwrap(B)};
unwrap({t_pid, A}) ->
    {t_pid, unwrap(A)};
unwrap(X) ->
    X.

missing_type_error(SourceModule, Module, Type) ->
    {error, {no_such_type, SourceModule, Module, Type}}.

retrieve_type(SourceModule, Module, Type, []) ->
    missing_type_error(SourceModule, Module, Type);
retrieve_type(SM, M, T, [#mlfe_module{name=M, types=Ts}|Rem]) ->
    case [TT || #mlfe_type{name={type_name, _, TN}}=TT <- Ts, TN =:= T] of
        [Type] -> {ok, Type};
        [] -> retrieve_type(SM, M, T, Rem)
    end;
retrieve_type(SM, M, T, [_|Rem]) ->
    retrieve_type(SM, M, T, Rem).

-spec typ_module(M::mlfe_module(), Env::env()) -> {ok, mlfe_module()} |
                                                  {error, term()}.
typ_module(#mlfe_module{functions=Fs, 
                        name=Name, 
                        types=Ts,
                        type_imports=Imports}=M, 
           #env{modules=Modules}=Env) ->

    %% Fold function to yield all the imported types or report a missing one.
    ImportFolder = fun(_, {error, _}=Err) -> Err;
                      (_, [{error, _}=Err|_]) -> Err;
                      (#mlfe_type_import{module=MN, type=T}, Acc) -> 
                           [retrieve_type(Name, MN, T, Modules)|Acc]
                   end,

    %% Fold function to instantiate all in-scope ADTs.
    TypFolder = fun(_, {error, _}=Err) -> 
                        Err;
                   (T, {Typs, E}) -> 
                        case inst_type(T, E) of
                            {ok, E2, ADT, _} -> {[unwrap(ADT)|Typs], E2};
                            {error, _}=Err   -> Err
                        end
                end,
    case lists:foldl(ImportFolder, [], Imports) of
        {error, _}=Err -> Err;
        Imported ->
            AllTypes = Ts ++ [T || {ok, T} <- Imported],
            case lists:foldl(TypFolder, {[], Env}, AllTypes) of
                {error, _}=Err ->
                    Err;
                {ADTs, Env2} ->
                    TypBindings = [{N, A}||#adt{name=N}=A <- ADTs],
                    Env3 = Env2#env{
                             type_bindings=TypBindings,
                             current_module=M,
                             current_types=AllTypes,
                             type_constructors=constructors(AllTypes),
                             entered_modules=[Name]},
                    case typ_module_funs(Fs, Env3, []) of
                        {error, _} = E -> E;
                        [_|_] = Funs   -> {ok, M#mlfe_module{functions=Funs}}
                    end
            end
    end.

typ_module_funs([], _Env, Memo) ->
    lists:reverse(Memo);
typ_module_funs([#mlfe_fun_def{name={symbol, _, Name}}=F|Rem], Env, Memo) ->
    case typ_of(Env, 0, F) of
        {error, _} = E -> 
            E;
        {Typ, NV} ->
            Env2 = update_counter(NV, Env),
            Env3 = update_binding(Name, Typ, Env2),
            typ_module_funs(Rem, Env3, [F#mlfe_fun_def{type=unwrap(Typ)}|Memo])
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

%% Base types now need to be in reference cells because when they are part
%% of unions they may need to be reset.
typ_of(#env{next_var=VarNum}, _Lvl, {int, _, _}) ->
    {new_cell(t_int), VarNum};
typ_of(#env{next_var=VarNum}, _Lvl, {float, _, _}) ->
    {new_cell(t_float), VarNum};
typ_of(#env{next_var=VarNum}, _Lvl, {atom, _, _}) ->
    {new_cell(t_atom), VarNum};
typ_of(#env{next_var=VN}, _Lvl, {string, _, _}) ->
    {new_cell(t_string), VN};
typ_of(Env, Lvl, {symbol, _, N}) ->
    case inst(N, Lvl, Env) of
        {error, _} = E -> E;
        {T, #env{next_var=VarNum}, _} -> {T, VarNum}
    end;
typ_of(#env{next_var=VN}, _Lvl, {unit, _}) ->
    {new_cell(t_unit), VN};

typ_of(Env, Lvl, {'_', _}) ->
    {T, #env{next_var=VarNum}, _} = inst('_', Lvl, Env),
    {T, VarNum};
typ_of(Env, Lvl, #mlfe_tuple{values=Vs}) ->
    {VTyps, NextVar} = typ_list(Vs, Lvl, Env, []),
    {new_cell({t_tuple, VTyps}), NextVar};
typ_of(#env{next_var=_VarNum}=Env, Lvl, {nil, _Line}) ->
    {TL, #env{next_var=NV}} = new_var(Lvl, Env),
    {new_cell({t_list, TL}), NV};
typ_of(Env, Lvl, #mlfe_cons{line=Line, head=H, tail=T}) ->
    {HTyp, NV1} = typ_of(Env, Lvl, H),
    {TTyp, NV2} = case T of
                      {nil, _} -> {{t_list, HTyp}, NV1};
                      #mlfe_cons{}=Cons ->
                          typ_of(update_counter(NV1, Env), Lvl, Cons);
                      {symbol, L, _} = S -> 
                          {STyp, Next} = 
                              typ_of(update_counter(NV1, Env), Lvl, S),
                          {TL, #env{next_var=Next2}} = 
                              new_var(Lvl, update_counter(Next, Env)),
                          case unify({t_list, TL}, STyp, Env, L) of
                              {error, _} = E -> E;
                              ok -> {STyp, Next2}
                          end;
                      #mlfe_apply{}=Apply ->
                          {TApp, Next} = typ_of(update_counter(NV1, Env), Lvl, Apply),
                          case unify({t_list, HTyp}, TApp, Env, apply_line(Apply)) of
                              {error, _} = E -> E;
                              ok -> {TApp, Next}
                          end;
                      NonList ->
                          {error, {cons_to_non_list, NonList}}
                  end,

    %% TODO:  there's no error check here:
    ListType = case TTyp of
                   P when is_pid(P) ->
                       case get_cell(TTyp) of
                           {link, {t_list, LT}} -> LT;
                           {t_list, LT} -> LT
                       end;
                   {t_list, LT} ->
                       LT
               end,
    case unify(HTyp, ListType, Env, Line) of
        {error, _} = Err ->
            Err;
        ok ->
            {TTyp, NV2}
    end;

typ_of(Env, _Lvl, #mlfe_type_apply{name=N, arg=none}) ->
    case inst_type_arrow(Env, N) of
        {error, _}=Err -> Err;
        {Env2, {type_arrow, _CTyp, RTyp}} ->
            {RTyp, Env2#env.next_var}
    end;
typ_of(Env, Lvl, #mlfe_type_apply{name=N, arg=A}) ->
    case inst_type_arrow(Env, N) of
        {error, _}=Err -> Err;
        {Env2, {type_arrow, CTyp, RTyp}} ->
            case typ_of(Env2, Lvl, A) of
                {error, _}=Err -> Err;
                {ATyp, NVNum} ->
                    {type_constructor, L, _} = N,
                    case unify(ATyp, CTyp, update_counter(NVNum, Env2), L) of
                        ok             -> {RTyp, NVNum};
                        {error, _}=Err -> Err
                    end
            end
    end;

%% BIFs are loaded in the environment as atoms:
typ_of(Env, Lvl, {bif, MlfeName, _, _, _}) ->
    case inst(MlfeName, Lvl, Env) of
        {error, _} = E ->
            E;
        {T, #env{next_var=VarNum}, _} ->
            {T, VarNum}
    end;

typ_of(Env, Lvl, #mlfe_apply{name={Mod, {symbol, L, X}, Arity}, args=Args}) ->
    Satisfy = fun() ->
                      %% Naively assume a single call to the same function for now.
                      %% does the module exist and does it export the function?
                      case extract_fun(Env, Mod, X, Arity) of
                          {error, _} = E -> E;
                          {ok, Module, Fun} -> 
                              Env2 = Env#env{current_module=Module, 
                                             entered_modules=[Mod | Env#env.entered_modules]},
                              case typ_of(Env2, Lvl, Fun) of
                                  {error, _} = E -> E;
                                  {TypF, NextVar} ->
                                      typ_apply(update_counter(NextVar, Env), 
                                                Lvl, TypF, NextVar, Args, L)
                              end
                      end
              end,
    Error = fun() ->
                    [CurrMod|_] = Env#env.entered_modules,
                    {error, {bidirectional_module_ref, Mod, CurrMod}}
            end,

    case [M || M <- Env#env.entered_modules, M == Mod] of
        [] -> Satisfy();
        [Mod] -> case Env#env.current_module of
                     #mlfe_module{name=Mod} -> Satisfy();
                     _ -> Error()
                 end;
        _  -> Error()
    end;

typ_of(Env, Lvl, #mlfe_apply{name=N, args=Args}) ->
    %% When a symbol isn't bound to a function in the environment,
    %% attempt to find it in the module.  Here we're assuming that
    %% the user has referred to a function that is defined later than
    %% the one being typed.
    {L, FN} = case N of
                  {symbol, Line, FunName} -> {Line, FunName};
                  {bif, FunName, Line, _, _} -> {Line, FunName}
              end,

    ForwardFun = fun() ->
                         Mod = Env#env.current_module,
                         case get_fun(Mod, FN, length(Args)) of
                             {ok, _, Fun} ->
                                 case typ_of(Env, Lvl, Fun) of
                                     {error, _}=Err -> Err;
                                     {TypF, NextVar} ->
                                         typ_apply(Env, Lvl, TypF, NextVar, Args, L)
                                 end;
                             {error, _} = E -> E
                         end
                 end,                                       

    case typ_of(Env, Lvl, N) of
        {error, {bad_variable_name, _}} -> ForwardFun();
        {error, _} = E -> E;
        {TypF, NextVar} -> 
            typ_apply(Env, Lvl, TypF, NextVar, Args, L)
    end;

%% Unify the patterns with each other and resulting expressions with each
%% other, then unifying the general pattern type with the match expression's
%% type.
typ_of(Env, Lvl, #mlfe_match{match_expr=E, clauses=Cs, line=Line}) ->
    {ETyp, NextVar1} = typ_of(Env, Lvl, E),
    Env2 = update_counter(NextVar1, Env),

    case unify_clauses(Env2, Lvl, Cs) of
        {error, _} = Err -> Err;
        {ok, {t_clause, PTyp, _, RTyp}, #env{next_var=NextVar2}}  ->
            %% unify the expression with the unified pattern:
            case unify(ETyp, PTyp, Env, Line) of
                {error, _} = Err -> Err;
                %% only need to return the result type of the unified clause types:
                ok -> {RTyp, NextVar2} 
            end
    end;

typ_of(Env, Lvl, #mlfe_clause{pattern=P, guards=Gs, result=R, line=L}) ->
    {PTyp, _, NewEnv, _} = add_bindings(P, Env, Lvl, 0),
    F = fun(_, {error, _}=Err) -> Err;
           (G, {Typs, AccEnv}) -> 
                case typ_of(AccEnv, Lvl, G) of
                    {error, _}=Err -> Err;
                    {GTyp, NV} -> {[GTyp|Typs], update_counter(NV, AccEnv)}
                end
        end,
    {GTyps, Env2} = lists:foldl(F, {[], NewEnv}, Gs),
    UnifyFolder = fun(_, {error, _}=Err) -> Err;
                     (N, Acc) ->
                          case unify(N, Acc, Env, L) of
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
typ_of(Env, Lvl, #mlfe_type_check{type=T, expr=E, line=L}) ->
    Typ = proplists:get_value(T, ?all_type_checks),
    case typ_of(Env, Lvl, E) of
        {error, _}=Err -> Err;
        {ETyp, NV} ->
            case unify(new_cell(Typ), ETyp, Env, L) of
                {error, _}=Err -> Err;
                ok -> {t_bool, NV}
            end
    end;

typ_of(Env, Lvl, #mlfe_send{line=L, message=M, pid=P}) ->
    case typ_of(Env, Lvl, P) of
        {error, _}=Err -> Err;
        {T, NV} ->
            {Var, Env2} = new_var(Lvl, Env),
            PidT = new_cell(Var),
            PC = new_cell({t_pid, PidT}),
            case unify(T, PC, Env2, Lvl) of
                {error, _}=Err -> Err;
                ok ->
                    case typ_of(Env2, Lvl, M) of
                        {error, _}=Err -> Err;
                        {MT, NV2} ->
                            Env3 = update_counter(NV2, Env2),
                            case unify(PidT, MT, Env3, L) of
                                {error, _}=Err -> Err;
                                ok -> {t_unit, NV}
                            end
                    end
            end
    end;
typ_of(Env, Lvl, #mlfe_receive{}=Recv) ->
    type_receive(Env, Lvl, Recv);

%%% Calls to Erlang code only have their return value typed.
typ_of(#env{next_var=NV}=Env, Lvl, #mlfe_ffi{clauses=Cs, module={_, L, _}}) ->
    ClauseFolder = fun(C, {Typs, EnvAcc}) ->
                           {{t_clause, _, _, T}, X} = typ_of(EnvAcc, Lvl, C),
                           {[T|Typs], update_counter(X, EnvAcc)}
                   end,
    {TypedCs, #env{next_var=NV2}} = lists:foldl(
                                           ClauseFolder, 
                                           {[], update_counter(NV, Env)}, Cs),
    UnifyFolder = fun(A, Acc) ->
                             case unify(A, Acc, Env, L) of
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

%% Spawning of functions in the current module:
typ_of(Env, Lvl, #mlfe_spawn{line=L, module=undefined, function=F, args=Args}) ->
    
    %% make a function application and type it:
    Apply = #mlfe_apply{name=F, args=Args},
    #mlfe_module{functions=MFs} = Env#env.current_module,
    {_, _, FN} = F,
    FunTyp = case [Fun||#mlfe_fun_def{name={_, _, FF}}=Fun <- MFs, FF =:= FN] of
                 [#mlfe_fun_def{type=undefined}=Fun] ->
                     typ_of(Env, Lvl, Fun);
                 [#mlfe_fun_def{type=T}] ->
                     {T, Env#env.next_var};
                 [] ->
                     {error, {no_function, module_name(Env), L, FN}}
             end,

    case FunTyp of
        {error, _}=Err -> Err;
        {SpawnFunTyp, NV} ->
            Env2 = update_counter(NV, Env),
            case typ_of(Env2, Lvl, Apply) of
                {error, _}=Err -> Err;
                {_, NV2} ->
                    %% use the type of the application to type a pid
                    case SpawnFunTyp of
                        {t_receiver, Recv, _} ->
                            {new_cell({t_pid, Recv}), NV2};
                        _ ->
                            {new_cell({t_pid, new_cell(undefined)}), NV2}
                    end
            end
    end;

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
            JustTypes = [Typ || {_, Typ} <- ArgTypes],
            case unwrap(T) of
                {t_receiver, Recv, Res} ->
                    TRec = {t_receiver, new_cell(Recv), new_cell(Res)},
                    {t_receiver, Recv2, Res2}=collapse_receivers(TRec, Env, Lvl),
                    X = {{t_receiver, Recv2,
                      {t_arrow, JustTypes, Res2}}, NextVar},
                    X;
                _ ->
                    {{t_arrow, JustTypes, T}, NextVar}
            end
    end;

%% A function binding inside a function:
typ_of(Env, Lvl, #fun_binding{
               def=#mlfe_fun_def{name={symbol, _, N}}=E, 
               expr=E2}) ->
    {TypE, NextVar} = typ_of(Env, Lvl, E),
    Env2 = update_counter(NextVar, Env),
    typ_of(update_binding(N, gen(Lvl, TypE), Env2), Lvl+1, E2);

%% A var binding inside a function:
typ_of(Env, Lvl, #var_binding{name={symbol, _, N}, to_bind=E1, expr=E2}) ->
    case typ_of(Env, Lvl, E1) of
        {error, _}=Err ->
            Err;
        {TypE, NextVar} ->
            Gen = gen(Lvl, TypE),
            Env2 = update_counter(NextVar, Env),
            typ_of(update_binding(N, Gen, Env2), Lvl+1, E2)
    end.

%%% This was pulled out of typing match expressions since the exact same clause
%%% type unification has to occur in match and receive expressions.
unify_clauses(Env, Lvl, Cs) ->
     ClauseFolder = fun(_, {error, _}=Err) -> Err;
                       (C, {Clauses, EnvAcc}) ->
                            case typ_of(EnvAcc, Lvl, C) of
                                {error, _}=Err -> Err;
                                {TypC, NV} -> 
                                    #mlfe_clause{line=Line} = C,
                                    {[{Line, TypC}|Clauses], update_counter(NV, EnvAcc)}
                            end
                    end,
    case lists:foldl(ClauseFolder, {[], Env}, Cs) of
        {error, _}=Err -> Err;
        {TypedCs, #env{next_var=NextVar2}} ->
            UnifyFolder = fun(_, {error, _}=Err) -> Err;
                             ({Line, {t_clause, PA, _, RA}}, Acc) ->
                                  case Acc of
                                      {t_clause, PB, _, RB} = TypC ->
                                          case unify(PA, PB, Env, Line) of
                                              ok -> 
                                                  case unify(RA, RB, Env, Line) of
                                                      ok -> TypC;
                                                      {error, _} = Err -> Err
                                                  end;
                                              {error, _} = Err -> Err
                                          end;
                                      {error, _} = Err -> Err
                                  end
                          end,
    
            [{_, FC}|TCs] = lists:reverse(TypedCs),
            case lists:foldl(UnifyFolder, FC, TCs) of
                {error, _}=Err ->Err;
                _ -> {ok, FC, update_counter(NextVar2, Env)}
            end
    end.

collapse_error({error, _}=Err, _) ->
    Err;
collapse_error(Res, F) ->
    F(Res).

collapse_receivers(C, Env, Line) when is_pid(C) ->
    collapse_error(
      collapse_receivers(get_cell(C), Env, Line), 
      fun(R) -> set_cell(C, R), C end);
collapse_receivers({link, C}, Env, Line) when is_pid(C) ->
    collapse_error(
      collapse_receivers(C, Env, Line),
      fun(Res) -> {link, Res} end);
collapse_receivers({t_receiver, Typ, C}=Recv, Env, Line) when is_pid(C) ->
    case get_cell(C) of
        {t_receiver, _, _}=Nested -> 
            case collapse_receivers(Nested, Env, Line) of
                {error, _}=Err -> Err;
                {t_receiver, _, Res}=Collapsed ->
                    case unify({t_receiver, Typ, Res},
                               new_cell(Collapsed),
                               Env, Line) of
                        ok -> {t_receiver, Typ, Res};
                        {error, _} = Err -> Err
                    end
            end;
        {link, CC} when is_pid(CC) ->
            collapse_receivers({t_receiver, Typ, CC}, Env, Line);
        _Other ->
            Recv
    end;
collapse_receivers({t_receiver, T, E}, Env, Line) ->
    collapse_receivers({t_receiver, T, new_cell(E)}, Env, Line);
collapse_receivers(E, _, _) ->
    E.

type_receive(Env, Lvl, #mlfe_receive{clauses=Cs, line=Line, timeout_action=TA}) ->
    case unify_clauses(Env, Lvl, Cs) of
        {error, _}=Err -> Err;
        {ok, {t_clause, PTyp, _, RTyp}, Env2} ->
            Collapsed = collapse_receivers(RTyp, Env, Line),
            case unwrap(Collapsed) of
                {t_receiver, _, B} ->
                    RC = new_cell(Collapsed),
                    case unify(RC, new_cell(B), Env, Line) of
                        %% TODO:  return this error
                        {error, _}=Er -> erlang:error(Er);
                        ok -> RC
                    end;
                _ -> Collapsed
            end,
            
            case TA of
                undefined -> 
                    {new_cell({t_receiver, PTyp, RTyp}), Env2#env.next_var};
                E -> case typ_of(Env2, Lvl, E) of
                         {error, _}=Err -> Err;
                         {Typ, NV} ->
                             Env3 = update_counter(NV, Env2),
                             CollapsedC = new_cell(Collapsed),
                             case unify(Typ, CollapsedC, Env3, Line) of
                                 {error, _}=Err -> Err;
                                 ok -> {new_cell({t_receiver, PTyp, CollapsedC}), NV}
                             end
                     end
            end
    end.

%% Get the line number that should be reported by an application AST node.
apply_line(#mlfe_apply{name={symbol, L, _}}) ->
    L;
apply_line(#mlfe_apply{name={_, {symbol, L, _}, _}}) ->
    L;
apply_line(#mlfe_apply{name={bif, _, L, _, _}}) ->
    L.

typ_apply(Env, Lvl, TypF, NextVar, Args, Line) ->
    Result = 
        case TypF of
            _ when is_pid(TypF) ->
                case get_cell(TypF) of
                    {t_receiver, Recv, App} -> 
                        case typ_apply_no_recv(Env, Lvl, App, NextVar, Args, Line) of
                            {error, _}=Err -> Err;
                            {Typ, NV} -> 
                                NewRec = {t_receiver, Recv, Typ},
                                set_cell(TypF, NewRec),
                                {TypF, NV}
                        end;
                    _ ->
                        typ_apply_no_recv(Env, Lvl, TypF, NextVar, Args, Line)
                end;
            {t_receiver, Recv, App} ->
                case typ_apply_no_recv(Env, Lvl, App, NextVar, Args, Line) of
                    {error, _}=Err -> Err;
                    {Typ, NV} -> 
                        case get_cell(Typ) of
                            {t_receiver, Recv2, RetTyp} ->
                                case unify(Recv, Recv2, Env, Line) of
                                    {error, _}=Err -> Err;
                                    ok ->
                                        NewRec = {t_receiver, Recv, RetTyp},
                                        {NewRec, NV}
                                end;
                            _ ->
                                NewRec = {t_receiver, Recv, Typ},
                                {NewRec, NV}
                        end
                end;
            _ ->
                typ_apply_no_recv(Env, Lvl, TypF, NextVar, Args, Line)
        end,
    Result.
         
typ_apply_no_recv(Env, Lvl, TypF, NextVar, Args, Line) ->
    %% we make a deep copy of the function we're unifying 
    %% so that the types we apply to the function don't 
    %% force every other application to unify with them 
    %% where the other callers may be expecting a 
    %% polymorphic function.  See Pierce's TAPL, chapter 22.
    CopiedTypF = deep_copy_type(TypF, maps:new()),
    
    case typ_list(Args, Lvl, update_counter(NextVar, Env), []) of
        {error, _}=Err -> Err;
        {ArgTypes, NextVar2} ->
            TypRes = new_cell(t_rec),
            Env2 = update_counter(NextVar2, Env),

            Arrow = new_cell({t_arrow, ArgTypes, TypRes}),
            case unify(CopiedTypF, Arrow, Env2, Line) of
                {error, _} = E ->
                    E;
                ok ->
                    #env{next_var=VarNum} = Env2,
                    {TypRes, VarNum}
            end
    end.

-spec extract_fun(
        Env::env(), 
        ModuleName::atom(), 
        FunName::string(), 
        Arity::integer()) -> {ok, mlfe_module(), mlfe_fun_def()} |
                             {error, 
                              {no_module, atom()} |
                              {not_exported, string(), integer()} |
                              {not_found, atom(), string, integer()}} .
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
        Arity::integer()) -> {ok, mlfe_module(), mlfe_fun_def()} |
                             {error, {not_found, atom(), string, integer()}}.
get_fun(Module, FunName, Arity) ->
    case filter_to_fun(Module#mlfe_module.functions, FunName, Arity) of
        not_found    -> {error, {not_found, Module, FunName, Arity}};
        {ok, Fun} -> {ok, Module, Fun}
    end.

filter_to_fun([], _, _) ->
    not_found;
filter_to_fun([#mlfe_fun_def{name={symbol, _, N}, args=Args}=Fun|_], FN, A) when length(Args) =:= A, N =:= FN ->
    {ok, Fun};
filter_to_fun([_|Rem], FN, Arity) ->
    filter_to_fun(Rem, FN, Arity).
    
%% Find or make a type for each arg from a function's
%% argument list.
args_to_types([], _Lvl, Env, Memo) ->
    {lists:reverse(Memo), Env};
args_to_types([{unit, _}|T], Lvl, Env, Memo) ->
    %% have to give t_unit a name for filtering later:
    args_to_types(T, Lvl, Env, [{unit, new_cell(t_unit)}|Memo]);
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
%%% occurrences of '_' with different types don't collide in `unify/4` and
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
        NameNum::integer()) -> {typ(), mlfe_expression(), env(), integer()}.
add_bindings({symbol, _, Name}=S, Env, Lvl, NameNum) ->
    {Typ, Env2} = new_var(Lvl, Env),
    {Typ, S, update_binding(Name, Typ, Env2), NameNum};

%%% A single occurrence of the wildcard doesn't matter here as the renaming
%%% only occurs in structures where multiple instances can show up, e.g.
%%% in tuples and lists.

add_bindings({'_', _}=X, Env, Lvl, NameNum) ->
    {Typ, Env2} = new_var(Lvl, Env),
    {Typ, X, update_binding('_', Typ, Env2), NameNum};

%%% Tuples are a slightly more involved case since we want a type for the
%%% whole tuple as well as any explicit variables to be available in the
%%% result side of the clause.
add_bindings(#mlfe_tuple{values=_}=Tup1, Env, Lvl, NameNum) ->
    {#mlfe_tuple{values=Vs}=Tup2, NN2} = rename_wildcards(Tup1, NameNum),
    {Env2, NN3} = lists:foldl(
                    fun (V, {EnvAcc, NN}) -> 
                            {_, _, NewEnv, NewNN} = add_bindings(V, EnvAcc, Lvl, NN),
                            {NewEnv, NewNN}
                    end, 
                    {Env, NN2}, 
                    Vs),
    {Typ, NextVar} = typ_of(Env2, Lvl, Tup2),
    
    {Typ, Tup2, update_counter(NextVar, Env2), NN3};

add_bindings(#mlfe_cons{}=Cons, Env, Lvl, NameNum) ->
    {#mlfe_cons{head=H, tail=T}=RenCons, NN2} = rename_wildcards(Cons, NameNum),
    {_, _, Env2, NN3} = add_bindings(H, Env, Lvl, NN2),
    {_, _, Env3, NN4} = add_bindings(T, Env2, Lvl, NN3),
    {Typ, NextVar} = typ_of(Env3, Lvl, RenCons),
    {Typ, RenCons, update_counter(NextVar, Env3), NN4};

add_bindings(#mlfe_type_apply{arg=none}=T, Env, Lvl, NameNum) ->
    {Typ, NextVar} = typ_of(Env, Lvl, T),
    {Typ, T, update_counter(NextVar, Env), NameNum};
add_bindings(#mlfe_type_apply{arg=Arg}=T, Env, Lvl, NameNum) ->
    {RenamedArg, NN} = rename_wildcards(Arg, NameNum),
    {_, _, Env2, NextNameNum} = add_bindings(RenamedArg, Env, Lvl, NN),
    TA = T#mlfe_type_apply{arg=RenamedArg},
    case typ_of(Env2, Lvl, TA) of
        {error, _} = Err -> Err;
        {Typ, NextVar} -> {Typ, TA, update_counter(NextVar, Env2), NextNameNum}
    end;

add_bindings(Exp, Env, Lvl, NameNum) ->
    {Typ, NextVar} = typ_of(Env, Lvl, Exp),
    {Typ, Exp, update_counter(NextVar, Env), NameNum}.

%%% Tuples may have multiple instances of the '_' wildcard/"don't care"
%%% symbol.  Each instance needs a unique name for unification purposes
%%% so the individual occurrences of '_' get renamed with numbers in order,
%%% e.g. (1, _, _) would become (1, _0, _1).
rename_wildcards(#mlfe_tuple{values=Vs}=Tup, NameNum) ->
    {Renamed, NN} = rename_wildcards(Vs, NameNum),
    {Tup#mlfe_tuple{values=Renamed}, NN};
rename_wildcards(#mlfe_type_apply{arg=none}=TA, NN) ->
    {TA, NN};
rename_wildcards(#mlfe_type_apply{arg=Arg}=TA, NN) ->
    {Arg2, NN2} = rename_wildcards(Arg, NN),
    {TA#mlfe_type_apply{arg=Arg2}, NN2};
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
    [io:format("Env:  ~s ~s~n    ~w~n", [N, dump_term(T), unwrap(T)])||{N, T} <- Bs].

dump_term({t_arrow, Args, Ret}) ->
    io_lib:format("~s -> ~s", [[dump_term(A) || A <- Args], dump_term(Ret)]);
dump_term({t_clause, P, G, R}) ->
    io_lib:format(" | ~s ~s -> ~s", [dump_term(X)||X<-[P, G, R]]);
dump_term({t_tuple, Ms}) ->
    io_lib:format("(~s) ", [[dump_term(unwrap(M)) ++ " " || M <- Ms]]);
dump_term(P) when is_pid(P) ->
    io_lib:format("{cell ~w ~s}", [P, dump_term(get_cell(P))]);
dump_term({link, P}) when is_pid(P) ->
    io_lib:format("{link ~w ~s}", [P, dump_term(P)]);
dump_term(T) ->
    io_lib:format("~w", [T]).


%%% Tests

-ifdef(TEST).

new_env() ->
    #env{bindings=[celled_binding(Typ)||Typ <- ?all_bifs]}.

%% Top-level typ_of unwraps the reference cells used in unification.
%% This is only preserved for tests at the moment.
-spec typ_of(Env::env(), Exp::mlfe_expression()) -> {typ(), env()} | {error, term()}.
typ_of(Env, Exp) ->
    case typ_of(Env, 0, Exp) of
        {error, _} = E -> E;
        {Typ, NewVar} -> {unwrap(Typ), update_counter(NewVar, Env)}
    end.

from_code(C) ->
    {ok, E} = mlfe_ast_gen:parse(scanner:scan(C)),
    E.

%% Check the type of an expression from the "top-level"
%% of 0 with a new environment.
top_typ_of(Code) ->
    {ok, E} = mlfe_ast_gen:parse(scanner:scan(Code)),
    typ_of(new_env(), E).

%% Check the type of the expression in code from the "top-level" with a
%% new environment that contains the provided ADTs.
top_typ_with_types(Code, ADTs) ->
    {ok, E} = mlfe_ast_gen:parse(scanner:scan(Code)),
    Env = new_env(),
    typ_of(Env#env{current_types=ADTs,
                   type_constructors=constructors(ADTs)}, 
           E).

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
        "double_app my_int ="
        "let two_times f x = f (f x) in "
        "let int_double i = i + i in "
        "two_times int_double my_int",
    ?assertMatch({{t_arrow, [t_int], t_int}, _}, top_typ_of(Code)).

polymorphic_let_test() ->
    Code = 
        "double_application my_int my_float = "
        "let two_times f x = f (f x) in "
        "let int_double a = a + a in "
        "let float_double b = b +. b in "
        "let doubled_2 = two_times int_double my_int in "
        "two_times float_double my_float",
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
     ?_assertMatch({error, {cannot_unify, _, _, _, _}},
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

%% Testing that type errors are reported for the appropriate line when
%% clauses are unified by match or receive.
pattern_match_error_line_test_() ->
    [?_assertMatch({error, {cannot_unify, _, 3, t_float, t_int}},
                   top_typ_of(
                     "f x = match x with\n"
                     "    i, is_integer i -> :int\n"
                     "  | f, is_float f -> :float")),
     ?_assertMatch({error, {cannot_unify, _, 4, t_float, t_int}},
                   top_typ_of(
                     "f () = receive with\n"
                     "    0 -> :zero\n"
                     "  | 1 -> :one\n"
                     "  | 2.0 -> :two\n"
                     "  | 3 -> :three\n")),
     ?_assertMatch({error, {cannot_unify, _, 3, t_string, t_atom}},
                   top_typ_of(
                     "f x = match x with\n"
                     "    0 -> :zero\n"
                     "  | i -> \"not zero\""))
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
                                [{unbound, _A, _}, 
                                 {unbound, _B, _},
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
                     "f l = match l with\n"
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
     ?_assertMatch({error, {cannot_unify, undefined, 3, t_int, t_float}},
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
    {ok, _, _, M} = mlfe_ast_gen:parse_module(0, Code),
    ?assertMatch({ok, #mlfe_module{
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
                                   ]}},
                 typ_module(M, new_env())).

module_with_forward_reference_test() ->
    Code =
        "module forward_ref\n\n"
        "export add/2\n\n"
        "add x y = adder x y\n\n"
        "adder x y = x + y",
    {ok, _, _, M} = mlfe_ast_gen:parse_module(0, Code),
    Env = new_env(),
    ?assertMatch({ok, #mlfe_module{
                         functions=[
                                    #mlfe_fun_def{
                                       name={symbol, 5, "add"},
                                       type={t_arrow, [t_int, t_int], t_int}},
                                    #mlfe_fun_def{
                                       name={symbol, 7, "adder"},
                                       type={t_arrow, [t_int, t_int], t_int}}]}},
                 typ_module(M, Env#env{current_module=M, modules=[M]})).

simple_inter_module_test() ->
    Mod1 =
        "module inter_module_one\n\n"
        "add x y = inter_module_two.adder x y",
    Mod2 =
        "module inter_module_two\n\n"
        "export adder/2\n\n"
        "adder x y = x + y",
    {ok, NV, _, M1} = mlfe_ast_gen:parse_module(0, Mod1),
    {ok, _, _, M2} = mlfe_ast_gen:parse_module(NV, Mod2),
    E = new_env(),
    Env = E#env{modules=[M1, M2]},
    ?assertMatch({ok, #mlfe_module{
                         function_exports=[],
                         functions=[
                                    #mlfe_fun_def{
                                       name={symbol, 3, "add"},
                                       type={t_arrow, [t_int, t_int], t_int}}]}},
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
    {ok, NV, _, M1} = mlfe_ast_gen:parse_module(0, Mod1),
    {ok, _, _, M2} = mlfe_ast_gen:parse_module(NV, Mod2),
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
     ?_assertMatch({error, {cannot_unify, undefined, 3, t_int, t_atom}},
                   top_typ_of(
                     "f x = match x with\n"
                     "  0 -> :zero\n"
                     "| 1 -> 1\n"
                     "| y -> y - 1\n")),
     ?_assertMatch({{t_arrow, [{t_list, {unbound, A, _}}, 
                              {t_arrow, [{unbound, A, _}], {unbound, B, _}}],
                    {t_list, {unbound, B, _}}}, _} when A =/= B,
                   top_typ_of(
                     "map l f = match l with\n"
                     "  [] -> []\n"
                     "| h :: t -> (f h) :: (map t f)"))
    ].

infinite_mutual_recursion_test() ->
    Code =
        "module mutual_rec_test\n\n"
        "a x = b x\n\n"
        "b x = let y = x + 1 in a y",
    {ok, _, _, M} = mlfe_ast_gen:parse_module(0, Code),
    E = new_env(),
    ?assertMatch({ok, #mlfe_module{
                         name=mutual_rec_test,
                         functions=[
                                    #mlfe_fun_def{
                                       name={symbol, 3, "a"},
                                       type={t_arrow, [t_int], t_rec}},
                                    #mlfe_fun_def{
                                       name={symbol, 5, "b"},
                                       type={t_arrow, [t_int], t_rec}}]}},
                 typ_module(M, E)).

terminating_mutual_recursion_test() ->
    Code =
        "module terminating_mutual_rec_test\n\n"
        "a x = let y = x + 1 in b y\n\n"
        "b x = match x with\n"
        "  10 -> :ten\n"
        "| y -> a y",
    {ok, _, _, M} = mlfe_ast_gen:parse_module(0, Code),
    E = new_env(),
    ?assertMatch({ok, #mlfe_module{
                         name=terminating_mutual_rec_test,
                         functions=[
                                    #mlfe_fun_def{
                                       name={symbol, 3, "a"},
                                       type={t_arrow, [t_int], t_atom}},
                                    #mlfe_fun_def{
                                       name={symbol, 5, "b"},
                                       type={t_arrow, [t_int], t_atom}}]}},
                 typ_module(M, E)).

ffi_test_() ->
    [?_assertMatch({t_int, _},
                   top_typ_of(
                     "call_erlang :io :format [\"One is ~w~n\", [1]] with\n"
                     " _ -> 1")),
     ?_assertMatch({error, {cannot_unify, undefined, 1, t_atom, t_int}},
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
     ?_assertMatch({error, {cannot_unify, _, _, _, _}}, top_typ_of("1.0 == 1")),
     ?_assertMatch({{t_arrow, [t_int], t_atom}, _}, 
                   top_typ_of(
                     "f x = match x with\n"
                     " a, a == 0 -> :zero\n"
                     "|b -> :not_zero")),
     ?_assertMatch({error, {cannot_unify, _, _, t_float, t_int}},
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
     ?_assertMatch({error, {cannot_unify, _, _, t_int, t_float}},
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

%%% ### ADT Tests
%%% 
%%% 
%%% Tests for ADTs that are simply unions of existing types:
union_adt_test_() ->
    [?_assertMatch({error, {cannot_unify, _, 1, t_int, t_atom}},
                   top_typ_with_types(
                     "f x = match x with "
                     "  0 -> :zero"
                     "| i, is_integer i -> i",
                     [])),
     %% Adding a type that unions integers and atoms should make the
     %% previously failing code pass.
     ?_assertMatch({{t_arrow, 
                         [t_int], 
                         #adt{name="t", vars=[]}}, 
                    _},
                   top_typ_with_types(
                     "f x = match x with "
                     "  0 -> :zero"
                     "| i, is_integer i -> i",
                     [#mlfe_type{name={type_name, 1, "t"},
                                 vars=[],
                                 members=[t_int, t_atom]}]))
    ].

type_tuple_test_() ->
    %% This first test passes but the second does not due to a spawn limit.  
    %% I believe an infinite loop is occuring when unification fails between 
    %% t_int and t_tuple in try_types which causes unify to reinstantiate the
    %% types and the cycle continues.  Both orderings of members need to work.
    [?_assertMatch({{t_arrow, 
                    [#adt{name="t", vars=[{"x", {unbound, t1, 0}}]}],
                    t_atom},
                   _},
                   top_typ_with_types(
                     "f x = match x with "
                     "   0 -> :zero"
                     "| (i, 0) -> :adt",
                     [#mlfe_type{name={type_name, 1, "t"},
                                 vars=[{type_var, 1, "x"}],
                                 members=[#mlfe_type_tuple{
                                             members=[{type_var, 1, "x"},
                                                      t_int]},
                                          t_int]}])),
     ?_assertMatch({{t_arrow, 
                    [#adt{name="t", vars=[{"x", {unbound, t1, 0}}]}],
                    t_atom},
                   _},
                   top_typ_with_types(
                     "f x = match x with "
                     "   0 -> :zero"
                     "| (i, 0) -> :adt",
                     [#mlfe_type{name={type_name, 1, "t"},
                                 vars=[{type_var, 1, "x"}],
                                 members=[t_int,
                                          #mlfe_type_tuple{
                                             members=[{type_var, 1, "x"},
                                                      t_int]}]}])),
     %% A recursive type with a bad variable:
     ?_assertMatch({error, {bad_variable, 1, "y"}},
                   top_typ_with_types(
                     "f x = match x with "
                     " 0 -> :zero"
                     "| (i, 0) -> :adt"
                     "| (0, (i, 0)) -> :nested",
                     [#mlfe_type{name={type_name, 1, "t"},
                                 vars=[{type_var, 1, "x"}],
                                 members=[t_int,
                                          #mlfe_type_tuple{
                                             members=[{type_var, 1, "x"},
                                                      t_int]},
                                         #mlfe_type_tuple{
                                            members=[t_int,
                                                     #mlfe_type{
                                                        name={type_name, 1, "t"},
                                                        vars=[{type_var, 1, "y"}]}
                                                    ]}]}]))
    ].

same_polymorphic_adt_union_test_() ->
    [?_assertMatch({{t_arrow,
                     [#adt{name="t", vars=[{"x", t_float}]},
                      #adt{name="t", vars=[{"x", t_int}]}],
                     {t_tuple, [t_atom, t_atom]}},
                    _},
                   top_typ_with_types(
                     "f x y ="
                     "  let a = match x with"
                     "  (0.0, 0) -> :zero "
                     "| (0.0, 0, :atom) -> :zero_atom in "
                     "  let b = match y with"
                     "  (1, 1) -> :int_one"
                     "| (1, 1, :atom) -> :one_atom in "
                     "(a, b)",
                     [#mlfe_type{name={type_name, 1, "t"},
                                 vars=[{type_var, 1, "x"}],
                                 members=[#mlfe_type_tuple{
                                             members=[{type_var, 1, "x"},
                                                      t_int]},
                                          #mlfe_type_tuple{
                                             members=[{type_var, 1, "x"},
                                                      t_int,
                                                      t_atom]}]}]))
    ].

type_constructor_test_() ->
    [?_assertMatch({{t_arrow, 
                     [#adt{name="t", vars=[{"x", {unbound, _, _}}]}], 
                     t_atom}, 
                    _},
                   top_typ_with_types(
                     "f x = match x with "
                     "i, is_integer i -> :is_int"
                     "| A i -> :is_a",
                     [#mlfe_type{name={type_name, 1, "t"},
                                 vars=[{type_var, 1, "x"}],
                                 members=[t_int,
                                          #mlfe_constructor{
                                             name={type_constructor, 1, "A"},
                                             arg={type_var, 1, "x"}}]}])),
     ?_assertMatch({{t_arrow, 
                     [t_int],
                     #adt{name="even_odd", vars=[]}},
                    _},
                   top_typ_with_types(
                     "f x = match x % 2 with "
                     "  0 -> Even x"
                     "| 1 -> Odd x",
                     [#mlfe_type{name={type_name, 1, "even_odd"},
                                 vars=[],
                                 members=[#mlfe_constructor{
                                             name={type_constructor, 1, "Even"},
                                             arg=t_int},
                                          #mlfe_constructor{
                                             name={type_constructor, 1, "Odd"},
                                             arg=t_int}]}])),
     ?_assertMatch({{t_arrow, 
                     [#adt{name="json_subset", vars=[]}], 
                     t_atom}, 
                    _},
                   top_typ_with_types(
                     "f x = match x with "
                     "  i, is_integer i -> :int"
                     "| f, is_float f   -> :float"
                     "| (k, v)          -> :keyed_value",
                     [#mlfe_type{
                         name={type_name, 1, "json_subset"},
                         vars=[],
                         members=[t_int,
                                  t_float,
                                  #mlfe_type_tuple{
                                     members=[t_string, 
                                              #mlfe_type{
                                                 name={type_name, 1, "json_subset"}}]}
                                 ]}])),
     ?_assertMatch({{t_arrow,
                     [{unbound, V, _}],
                     #adt{name="my_list", vars=[{"x", {unbound, V, _}}]}},
                    _},
                   top_typ_with_types(
                     "f x = Cons (x, Cons (x, Nil))",
                     [#mlfe_type{
                         name={type_name, 1, "my_list"},
                         vars=[{type_var, 1, "x"}],
                         members=[#mlfe_constructor{
                                     name={type_constructor, 1, "Cons"},
                                     arg=#mlfe_type_tuple{
                                            members=[{type_var, 1, "x"},
                                                     #mlfe_type{
                                                        name={type_name, 1, "my_list"},
                                                        vars=[{type_var, 1, "x"}]}]}},
                                  #mlfe_constructor{
                                     name={type_constructor, 1, "Nil"},
                                     arg=none}]}])),
     ?_assertMatch({error, {cannot_unify, _, _, t_float, t_int}},
                   top_typ_with_types(
                     "f x = Cons (1, Cons (2.0, Nil))",
                     [#mlfe_type{
                         name={type_name, 1, "my_list"},
                         vars=[{type_var, 1, "x"}],
                         members=[#mlfe_constructor{
                                     name={type_constructor, 1, "Cons"},
                                     arg=#mlfe_type_tuple{
                                            members=[{type_var, 1, "x"},
                                                     #mlfe_type{
                                                        name={type_name, 1, "my_list"},
                                                        vars=[{type_var, 1, "x"}]}]}},
                                  #mlfe_constructor{
                                     name={type_constructor, 1, "Nil"},
                                     arg=none}]}]))
    ].

%%% Type constructors that use underscores in pattern matches to discard actual
%%% values should work, depends on correct recursive renaming.
rename_constructor_wildcard_test() ->
    Code =
        "module module_with_wildcard_constructor_tuples\n\n"
        "type t = int | float | Pair (string, t)\n\n"
        "a x = match x with\n"
        "i, is_integer i -> :int\n"
        "| f, is_float f -> :float\n"
        "| Pair (_, _) -> :tuple\n"
        "| Pair (_, Pair (_, _)) -> :nested_t"
        "| Pair (_, Pair (_, Pair(_, _))) -> :double_nested_t",
    {ok, _, _, M} = mlfe_ast_gen:parse_module(0, Code),
    Env = new_env(),
    Res = typ_module(M, Env),
    ?assertMatch({ok, #mlfe_module{
                         functions=[#mlfe_fun_def{
                                       name={symbol, 5, "a"},
                                       type={t_arrow,
                                             [#adt{
                                                 name="t",
                                                 vars=[],
                                                 members=[{t_adt_cons, "Pair"},
                                                          t_float, 
                                                          t_int]}],
                                             t_atom}}]}}, 
                 Res).    

json_union_type_test() ->
    Code =
        "module json_union_type_test\n\n"
        "type json = int | float | string | bool "
        "          | list json "
        "          | list (string, json)\n\n"
        "json_to_atom j = match j with "
        "    i, is_integer i -> :int"
        "  | f, is_float f -> :float"
        "  | (_, _) :: _ -> :json_object"
        "  | _ :: _ -> :json_array",
    {ok, _, _, M} = mlfe_ast_gen:parse_module(0, Code),
    Env = new_env(),
    Res = typ_module(M, Env),
    ?assertMatch({ok, 
                  #mlfe_module{
                     types=[#mlfe_type{
                               module='json_union_type_test',
                               name={type_name, 3, "json"}}],
                     functions=[#mlfe_fun_def{
                                   name={symbol, _, "json_to_atom"},
                                   type={t_arrow,
                                         [#adt{name="json",
                                               members=[{t_list,
                                                         {t_tuple,
                                                          [t_string,
                                                           #adt{name="json"}]}},
                                                         {t_list,
                                                          #adt{name="json"}},
                                                          t_bool,
                                                          t_string,
                                                          t_float,
                                                          t_int]}],
                                               t_atom}}]}},
                 Res).

module_with_types_test() ->
    Code =
        "module module_with_types\n\n"
        "type t = int | float | (string, t)\n\n"
        "a x = match x with\n"
        "i, is_integer i -> :int\n"
        "| f, is_float f -> :float\n"
        "| (_, _) -> :tuple"
        "| (_, (_, _)) -> :nested",
    {ok, _, _, M} = mlfe_ast_gen:parse_module(0, Code),
    Env = new_env(),
    Res = typ_module(M, Env),
    ?assertMatch({ok, #mlfe_module{
                         functions=[#mlfe_fun_def{
                                       name={symbol, 5, "a"},
                                       type={t_arrow,
                                             [#adt{
                                                 name="t",
                                                 vars=[],
                                                 members=[{t_tuple,
                                                           [t_string,
                                                            #adt{name="t",
                                                                 vars=[],
                                                                 members=[]}]},
                                                          t_float,
                                                          t_int
                                                          ]}],
                                             t_atom}}]}}, 
                 Res).

module_matching_lists_test() ->
    Code =
        "module module_matching_lists\n\n"
        "type my_list 'x = Nil | Cons ('x, my_list 'x)\n\n"
        "a x = match x with "
        "Nil -> :nil"
        "| Cons (i, Nil), is_integer i -> :one_item"
        "| Cons (i, x) -> :more_than_one",
    {ok, _, _, M} = mlfe_ast_gen:parse_module(0, Code),
    Env = new_env(),
    Res = typ_module(M, Env),
    ?assertMatch({ok, #mlfe_module{
                        functions=[#mlfe_fun_def{
                                     name={symbol, 5, "a"},
                                     type={t_arrow,
                                           [#adt{
                                               name="my_list",
                                               vars=[{"x", t_int}]}],
                                           t_atom}}]}}, 
                 Res).

%%% When ADTs are instantiated their variables and references to those 
%%% variables are put in reference cells.  Two functions that use the
%%% ADT with different types should not permanently union the ADTs 
%%% variables, one preventing the other from using the ADT.
type_var_protection_test() ->
    Code =
        "module module_matching_lists\n\n"
        "type my_list 'x = Nil | Cons ('x, my_list 'x)\n\n"
        "a x = match x with "
        "Nil -> :nil"
        "| Cons (i, Nil), is_integer i -> :one_integer"
        "| Cons (i, x) -> :more_than_one_integer\n\n"
        "b x = match x with "
        "Nil -> :nil"
        "| Cons (f, Nil), is_float f -> :one_float"
        "| Cons (f, x) -> :more_than_one_float\n\n"
        "c () = (Cons (1.0, Nil), Cons(1, Nil))",
    {ok, _, _, M} = mlfe_ast_gen:parse_module(0, Code),
    Env = new_env(),
    Res = typ_module(M, Env),
    ?assertMatch({ok, #mlfe_module{
                        functions=[#mlfe_fun_def{
                                     name={symbol, 5, "a"},
                                     type={t_arrow,
                                           [#adt{
                                               name="my_list",
                                               vars=[{"x", t_int}]}],
                                           t_atom}},
                                   #mlfe_fun_def{
                                      name={symbol, 7, "b"},
                                      type={t_arrow,
                                            [#adt{
                                                name="my_list",
                                                vars=[{"x", t_float}]}],
                                            t_atom}},
                                   #mlfe_fun_def{
                                      name={symbol, 9, "c"},
                                      type={t_arrow,
                                            [t_unit],
                                            {t_tuple, 
                                             [#adt{
                                                 name="my_list",
                                                 vars=[{"x", t_float}]},
                                              #adt{
                                                 name="my_list",
                                                 vars=[{"x", t_int}]}]}}}]}}, 
                 Res).

type_var_protection_fail_unify_test() ->
    Code =
        "module module_matching_lists\n\n"
        "type my_list 'x = Nil | Cons ('x, my_list 'x)\n\n"
        "c () = "
        "let x = Cons (1.0, Nil) in "
        "Cons (1, x)",
    Env = new_env(),
    {ok, _, _, M} = mlfe_ast_gen:parse_module(0, Code),
    Res = typ_module(M, Env),
    ?assertMatch({error, {cannot_unify, module_matching_lists, 5, t_float, t_int}}, Res).
    
%%% ### Process Interaction Typing Tests
%%% 
%%% Things like receive, send, and spawn.

module_typ_and_parse(Code) ->
    Env = new_env(),
    {ok, _, _, M} = mlfe_ast_gen:parse_module(0, Code),
    Env#env{modules=[M]},
    typ_module(M, Env).

receive_test_() ->
    [?_assertMatch({{t_receiver, t_int, t_int}, _},
                   top_typ_of(
                     "receive with "
                     "  i -> i + 1")),
     ?_assertMatch({error, {cannot_unify, _, _, t_float, t_int}},
                   top_typ_of(
                     "receive with "
                     "  i -> i + 1 "
                     "| f -> f +. 1")),
     fun() ->
             Code = 
                 "module receive_adt\n\n"
                 "type my_union = float | int\n\n"
                 "a () = receive with "
                 "  i, is_integer i -> :received_int"
                 "| f, is_float f -> :received_float",
             ?assertMatch(
                {ok, #mlfe_module{
                        functions=[#mlfe_fun_def{
                                      name={symbol, 5, "a"},
                                      type={t_receiver,
                                            #adt{name="my_union"},
                                            {t_arrow,
                                             [t_unit],
                                             t_atom}}
                                     }]}},
                module_typ_and_parse(Code))
     end,
     fun() ->
             Code = 
                 "module union_receives\n\n"
                 "f x = receive with "
                 "    0 -> :ok"
                 "  | i -> g (i + x)\n\n"
                 "g x = receive with "
                 "  i -> f (i - x)",
             ?assertMatch(
                {ok, #mlfe_module{
                       functions=[#mlfe_fun_def{
                                     name={symbol, 3, "f"},
                                     type={t_receiver,
                                           t_int,
                                           {t_arrow,
                                            [t_int],
                                            t_atom}}},
                                  #mlfe_fun_def{
                                     name={symbol, 5, "g"},
                                     type={t_receiver,
                                           t_int,
                                           {t_arrow,
                                            [t_int],
                                            t_atom}}}
                                 ]}},
                module_typ_and_parse(Code))
     end,
     fun() ->
             Code =
                 "module union_for_two_receivers\n\n"
                 "type t = A | B\n\n"
                 "a () = receive with "
                 "A -> b ()\n\n"
                 "b () = receive with "
                 "B -> a () after 5 a()",
             ?assertMatch(
                {ok, #mlfe_module{
                        functions=[#mlfe_fun_def{
                                     name={symbol, 5, "a"},
                                     type={t_receiver,
                                           #adt{name="t"},
                                           {t_arrow,
                                            [t_unit],
                                            t_rec}}},
                                   #mlfe_fun_def{
                                      name={symbol, 7, "b"},
                                      type={t_receiver,
                                            #adt{name="t"},
                                            {t_arrow,
                                             [t_unit],
                                             t_rec}}}
                                  ]}},
                module_typ_and_parse(Code))
     end,
     fun() ->
             Code = 
                 "module receive_in_let\n\n"
                 "f x = "
                 "  let y = receive with "
                 "    i -> i "
                 "  in let z = receive with "
                 "    i -> i "
                 "  in x + y + z",
             ?assertMatch(
                {ok, #mlfe_module{
                        functions=[#mlfe_fun_def{
                                      type={t_receiver,
                                            t_int,
                                            {t_arrow,
                                             [t_int],
                                             t_int}}}
                                  ]}},
                module_typ_and_parse(Code))
     end,
     fun() ->
             Code = 
                 "module receive_in_let\n\n"
                 "f x = "
                 "  let y = receive with "
                 "    i -> i "
                 "  in let z = receive with "
                 "    flt, is_float flt -> flt "
                 "  in x + y + z",
             ?assertMatch({error, {cannot_unify, _, _, t_float, t_int}},
                          module_typ_and_parse(Code))
     end

    ].

spawn_test_() ->
    [fun() ->
             Code = 
                 "module spawn_module\n\n"
                 "export f/1, start_f/1\n\n"
                 "f x = receive with "
                 " i -> f (x + i)\n\n"
                 "start_f init = spawn f [init]",
             ?assertMatch({ok, #mlfe_module{
                                 functions=[#mlfe_fun_def{
                                               name={symbol, 5, "f"},
                                               type={t_receiver, 
                                                     t_int,
                                                     {t_arrow,
                                                      [t_int],
                                                      t_rec}}},
                                            #mlfe_fun_def{
                                               name={symbol, 7, "start_f"},
                                               type={t_arrow,
                                                     [t_int],
                                                     {t_pid, t_int}
                                              }}]}},
                          module_typ_and_parse(Code))
     end
     , fun() ->
               Code =
                   "module spawn_composed_receiver\n\n"
                   "recv () = receive with "
                   "  i, is_integer i -> i\n\n"
                   "not_recv () = (recv ()) + 2",
               ?assertMatch({ok, #mlfe_module{
                                   functions=[#mlfe_fun_def{
                                                name={symbol, 3, "recv"},
                                                type={t_receiver,
                                                      t_int,
                                                      {t_arrow,
                                                       [t_unit],
                                                       t_int}}},
                                              #mlfe_fun_def{
                                                name={symbol, 5, "not_recv"},
                                                type={t_receiver,
                                                      t_int,
                                                      {t_arrow,
                                                       [t_unit],
                                                       t_int}}}]}},
                            module_typ_and_parse(Code))
     end
    , fun() ->
              Code =
                  "module spawn_composed_pid\n\n"
                  "type t = A int | B int\n\n"
                  "a x = let y = receive with "
                  "    B xx -> b (x + xx)\n"
                  "  | A xx -> xx + x in "
                  "  a (x + y)\n\n"
                  "b x = receive with "
                  "    A xx -> a (x + xx)\n"
                  "  | B xx -> b (xx + x)\n\n"
                  "start_a init = spawn a [init]",
              ?assertMatch({ok, #mlfe_module{
                                   functions=[#mlfe_fun_def{
                                                 name={symbol, _, "a"},
                                                 type={t_receiver,
                                                       #adt{name="t"},
                                                       {t_arrow,
                                                        [t_int],
                                                        t_rec}}},
                                              #mlfe_fun_def{
                                                 name={symbol, _, "b"},
                                                type={t_receiver,
                                                      #adt{name="t"},
                                                      {t_arrow,
                                                       [t_int],
                                                       t_rec}}},
                                              #mlfe_fun_def{
                                                 name={symbol, _, "start_a"},
                                                 type={t_arrow,
                                                       [t_int],
                                                       {t_pid, #adt{name="t"}}}}]}},
                           module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module unify_failure_for_spawn\n\n"
                  "type t = A int\n\n"
                  "type u = B int\n\n"
                  "a x = let y = receive with "
                  "    B xx -> b (x + xx)\n"
                  "  | A xx -> xx + x in "
                  "  a (x + y)\n\n"
                  "b x = receive with "
                  "    A xx -> a (x + xx)\n"
                  "  | B xx -> b (xx + x)\n\n"
                  "start_a init = spawn a [init]",
              ?assertMatch(
                 {error, {cannot_unify, _, _, #adt{name="u"}, #adt{name="t"}}},
                 module_typ_and_parse(Code))
      end
     , fun() ->
               Code =
                   "module non_receiver_pid\n\n"
                   "export f/1, start_f/1\n\n"
                   "f x = f (x + 1)\n\n"
                   "start_f () = spawn f [0]",
               ?assertMatch(
                  {ok, #mlfe_module{
                          functions=[#mlfe_fun_def{
                                        name={symbol, _, "f"},
                                        type={t_arrow, [t_int], t_rec}},
                                     #mlfe_fun_def{}]}},
                  module_typ_and_parse(Code))
       end
    ].

send_message_test_() ->
    [fun() ->
             Code =
                 "module send_example_1\n\n"
                 "f x = receive with "
                 "  i -> f (i + x)\n\n"
                 "spawn_and_message_f = "
                 "  let p = spawn f [0] in "
                 "  send 1 p",
             ?assertMatch(
                {ok, #mlfe_module{}},
                module_typ_and_parse(Code))
     end
    , fun() ->
              Code =
                  "module send_to_bad_pid\n\n"
                  "f x = receive with "
                  "  i -> f (i + x)\n\n"
                  "spawn_and_message_f = "
                  "  let p = spawn f [0] in "
                  "  send 1.0 p",
              ?assertMatch(
                 {error, {cannot_unify, _, _, t_int, t_float}},
                 module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module send_to_non_pid\n\n"
                  "f x = send 1 2",
              ?assertMatch(
                 {error, {cannot_unify, send_to_non_pid, _, t_int, {t_pid, _}}},
                 module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module send_to_non_receiver\n\n"
                  "f x = f (x+1)\n\n"
                  "start_f x = "
                  "  let p = spawn f [x] in "
                  "  send 1 p",
              ?assertMatch(
                 {error, {cannot_unify, _, _, undefined, t_int}},
                 module_typ_and_parse(Code))
      end
    ]. 
-endif.
