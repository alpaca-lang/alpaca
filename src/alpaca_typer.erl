%% -*- mode: erlang;erlang-indent-level: 4;indent-tabs-mode: nil -*-
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

%%% #alpaca_typer.erl
%%%
%%% This is based off of the sound and eager type inferencer in
%%% http://okmij.org/ftp/ML/generalization.html with some influence
%%% from https://github.com/tomprimozic/type-systems/blob/master/algorithm_w
%%% where the arrow type and instantiation are concerned.
%%%
%%% I still often use proplists in this module, mostly because dialyzer doesn't
%%% yet type maps correctly (Erlang 18.1).

-module(alpaca_typer).

-include("alpaca_ast.hrl").
-include("builtin_types.hrl").

%%% API
-export([type_modules/1]).

-export_type([cell/0]).

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

-type cell() :: {cell, {cell_name, integer()}}.

-define(CELL_TABLE, alpaca_typer_cells).
-define(CELL_COUNTER, alpaca_cell_counter).

-spec new_cell(typ()) -> cell().
new_cell({cell, _}=C) ->
    throw({error, cell_in_cell, C});
new_cell(Typ) ->
    [{?CELL_COUNTER, CellCounter}] = try
                         ets:lookup(?CELL_TABLE, ?CELL_COUNTER)
                     catch
                         error:badarg ->
                             ets:new(?CELL_TABLE, [set, named_table, public]),
                             Initial = {?CELL_COUNTER, 0},
                             ets:insert(?CELL_TABLE, Initial),
                             [Initial]
                     end,

    %% TODO:  does tuple construction time have a negative impact in larger
    %%        code bases?
    N = {cell_name, CellCounter},
    ets:insert(?CELL_TABLE, {?CELL_COUNTER, CellCounter + 1}),
    true = ets:insert_new(?CELL_TABLE, {N, Typ}),
    {cell, N}.

-spec get_cell(cell()|typ()) -> typ().
get_cell({cell, CellName}) ->
    case ets:lookup(?CELL_TABLE, CellName) of
        [{CellName, {cell, CellName}}] ->
            throw({recursive_cell, CellName});
        [{CellName, {cell, _}=NextCell}] ->
            get_cell(NextCell);
        [{CellName, Val}] ->
            Val
    end;
get_cell(NotACell) ->
    NotACell.

set_cell(?CELL_COUNTER, _) ->
    erlang:error(badarg);
set_cell({cell, CellName}, {cell, TriedToCell}) ->
    T = {error, cell_in_cell, CellName, TriedToCell},
    throw(T);
set_cell({cell, CellName}, {link, {cell, CellName}}) ->
    throw({error, recursive_link, CellName});
set_cell({cell, CellName}, Val) ->
    true = ets:insert(?CELL_TABLE, {CellName, Val}),
    ok.

%%% The `map` is a map of `unbound type variable name` to a `t_cell()`.
%%% It's used to ensure that each reference or link to a single type
%%% variable actually points to a single canonical reference cell for that
%%% variable.  Failing to do so causes problems with unification since
%%% unifying one variable with another type should impact all occurrences
%%% of that variable.
-spec copy_cell(cell(), map()) -> {cell(), map()}.
copy_cell(Cell, RefMap) ->
    case get_cell(Cell) of
        {link, {cell, _}=C} ->
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
        {t_tuple, Members} ->
            F = fun(M, {RM, Memo}) ->
                        {M2, RM2} = copy_cell(M, RM),
                        {RM2, [M2|Memo]}
                end,
            {RefMap2, Members2} = lists:foldl(F, {RefMap, []}, Members),
            {new_cell({t_tuple, lists:reverse(Members2)}), RefMap2};
        {t_list, C} ->
            {C2, Map2} = copy_cell(C, RefMap),
            {new_cell({t_list, C2}), Map2};
        {t_map, K, V} ->
            {K2, Map2} = copy_cell(K, RefMap),
            {V2, Map3} = copy_cell(V, Map2),
            {new_cell({t_map, K2, V2}), Map3};
        #t_record{members=Members, row_var=RV} ->
            F = fun(#t_record_member{type=T}=M, {Ms, Map}) ->
                        {T2, Map2} = copy_cell(T, Map),
                        {[M#t_record_member{type=T2}|Ms], Map2}
                end,
            {RevMembers, Map2} = lists:foldl(F, {[], RefMap}, Members),
            {RV2, Map3} = copy_cell(RV, Map2),
            {new_cell(#t_record{members=lists:reverse(RevMembers), row_var=RV2}), Map3};
        #adt{vars=TypeVars, members=Members}=ADT ->
            %% copy the type variables:
            Folder = fun({TN, C}, {L, RM}) ->
                             {C2, NM} = copy_cell(C, RM),
                             {[{TN, C2}|L], NM}
                     end,
            {NewTypeVars, Map2} = lists:foldl(Folder, {[], RefMap}, TypeVars),

            %% and then copy the members:
            F2 = fun(M, {L, RM}) ->
                         {M2, NM} = copy_cell(M, RM),
                         {[M2|L], NM}
                 end,

            {NewMembers, Map3} = lists:foldl(F2, {[], Map2}, Members),

            {new_cell(ADT#adt{vars=lists:reverse(NewTypeVars),
                              members=lists:reverse(NewMembers)}), Map3};
        {t_adt_cons, _}=Constructor ->
            {Constructor, RefMap};
        {t_receiver, MsgT, BodyT} ->
            {MsgT2, Map2} = copy_cell(MsgT, RefMap),
            {BodyT2, Map3} = copy_cell(BodyT, Map2),
            {new_cell({t_receiver, MsgT2, BodyT2}), Map3};
        {cell, _}=Cell ->
            copy_cell(Cell, RefMap);
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
          current_module=none  :: none | alpaca_module(),
          current_types=[]     :: list(alpaca_type()),
          type_constructors=[] :: list({string(), alpaca_constructor()}),
          type_bindings=[]     :: list({string(), t_adt()}),
          bindings=[]          :: list({term(), typ()|cell()}),
          modules=[]           :: list(alpaca_module())
         }).

-type env() :: #env{}.

new_env(Mods) ->
    #env{bindings=[celled_binding(Typ)||Typ <- ?all_bifs],
         modules=Mods}.

%%% We need to build a proplist of type constructor name to the actual type
%%% constructor's AST node and associated type.
-spec constructors(list(alpaca_type())) -> list({string(), alpaca_constructor()}).
constructors(Types) ->
    MemberFolder =
        fun(#alpaca_constructor{name=#type_constructor{name=N}}=C, {Type, Acc}) ->
                WithType = C#alpaca_constructor{type=Type},
                {Type, [{N, WithType}|Acc]};
           (_, Acc) ->
                Acc
        end,
    TypesFolder = fun(#alpaca_type{members=Ms}=Typ, Acc) ->
                          {_, Cs} = lists:foldl(MemberFolder, {Typ, []}, Ms),
                          [Cs|Acc]
                  end,
    lists:flatten(lists:foldl(TypesFolder, [], Types)).

%% Given a presumed newly-typed module, replace its untyped occurence within
%% the supplied environment.  If the module does *not* exist in the environment,
%% it will be added.
replace_env_module(#env{modules=Ms}=E, #alpaca_module{name=N}=M) ->
    E#env{modules = [M | [X || #alpaca_module{name=XN}=X <- Ms, XN /= N]]}.

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
    {NewRet, Map3} = copy_type(B, Map2),
    {{t_arrow, NewArgs, NewRet}, Map3};
deep_copy_type({t_tuple, Members}, RefMap) ->
    {Members2, Map2} = copy_type_list(Members, RefMap),
    {{t_tuple, Members2}, Map2};
deep_copy_type({t_list, A}, RefMap) ->
    {NewList, Map} = copy_type_list(A, RefMap),
    {{t_list, NewList}, Map};
deep_copy_type({t_map, K, V}, RefMap) ->
    {NewK, Map2} = copy_type(K, RefMap),
    {NewV, Map3} = copy_type(V, Map2),
    {{t_map, NewK, NewV}, Map3};

deep_copy_type({t_receiver, A, B}, RefMap) ->
    %% Here we're copying the body of the receiver first and then the
    %% receiver type itself, explicitly with a method that pulls existing
    %% reference cells for named type variables from the map returned by
    %% the body's deep copy operation.  This ensures that when the same
    %% type variable occurs in body the body and receive types we use the
    %% same reference cell.
    {B2, M2} = deep_copy_type(B, RefMap),
    {A2, M3} = copy_type(A, M2),
    {{t_receiver, A2, B2}, M3};

deep_copy_type(#t_record{members=Ms, row_var=V}=R, RefMap) ->
    {Ms2, RefMap2} = lists:foldl(fun(M, {Memo, Map}) ->
                                         {M2, Map2} = deep_copy_type(M, Map),
                                         {[M2|Memo], Map2}
                                 end,
                                 {[], RefMap}, Ms),
    {V2, RefMap3} = deep_copy_type(V, RefMap2),
    {R#t_record{members=lists:reverse(Ms2), row_var=V2}, RefMap3};
deep_copy_type(#t_record_member{type=T}=M, RefMap) ->
    {T2, RefMap2} = deep_copy_type(T, RefMap),
    {M#t_record_member{type=T2}, RefMap2};

deep_copy_type(T, M) ->
    {T, M}.

copy_type({cell, _}=Cell, RefMap) ->
    copy_cell(Cell, RefMap);
copy_type({t_arrow, _, _}=A, M) ->
    deep_copy_type(A, M);
copy_type({unbound, _, _}=U, M) ->
    copy_type(new_cell(U), M);
copy_type(T, M) ->
    {new_cell(T), M}.

%%% ## Type Inferencer

occurs(Label, Level, {cell, _}=Cell) ->
    occurs(Label, Level, get_cell(Cell));
occurs(Label, _Level, {unbound, Label, _}) ->
    {error, {circular, Label}};
occurs(Label, Level, {link, Ty}) ->
    occurs(Label, Level, Ty);
occurs(_Label, Level, {unbound, N, Lvl}) ->
    {unbound, N, min(Level, Lvl)};
occurs(Label, Level, {t_arrow, Params, RetTyp}) ->
    {t_arrow,
     lists:map(fun(T) -> occurs(Label, Level, T) end, Params),
     occurs(Label, Level, RetTyp)};
occurs(Label, Level, #t_record{members=Ms, row_var=RV}) ->
    F = fun(_, [{error, {circular, _}}=Err|_]) -> Err;
           (X, Acc) -> [occurs(Label, Level, X)|Acc]
        end,
    lists:foldl(F, [], [RV|Ms]);
occurs(Label, Level, #t_record_member{type=T}) ->
    occurs(Label, Level, T);
occurs(_L, _Lvl, T) ->
    T.

unwrap_cell({cell, _}=Cell) ->
    unwrap_cell(get_cell(Cell));
unwrap_cell(Typ) ->
    Typ.

%% Get the name of the current module out of the environment.  Useful for
%% error generation.
module_name(#env{current_module=#alpaca_module{name=N}}) ->
    N;
module_name(_) ->
    undefined.

-type unification_error() ::
        {error, {cannot_unify, atom(), integer(), typ(), typ()}}.
%% I make unification error tuples everywhere, just standardizing their
%% construction here:
-spec unify_error(Env::env(), Line::integer(), typ(), typ()) ->
                         unification_error().
unify_error(Env, Line, Typ1, Typ2) ->
    {error, {cannot_unify, module_name(Env), Line, unwrap(Typ1), unwrap(Typ2)}}.

%%% Unify now requires the environment not in order to make changes to it but
%%% so that it can look up potential type unions when faced with unification
%%% errors.
%%%
%%% For the purposes of record unification, T1 is considered to be the lower
%%% bound for unification.  Example:
%%%
%%% a: {x: int, y: int}  -- a row variable `A` is implied.
%%% f: {x: int|F} -> (int, {x: int|F})
%%%
%%% Calling f(a) given the above poses no problem.  The two `x` members unify
%%% and the `F` in f's type unifies with `y: int|A`.  But:
%%%
%%% b: {x: int}  - a row variable `B` is implied.
%%% f: {x: int, y: int|F} -> (int, {x: int, y: int|F})
%%%
%%% Here `f` is more specific than `b` and _requires_ a `y: int` member.  Its
%%% type must serve as a lower bound for unification, we don't want `f(b)` to
%%% succeed if the implied row variable `B` does not contain a `y: int`.
%%%
%%% Some of the packing into and unpacking from row variables is likely to get
%%% a little hairy in the first implementation here.
unify(T1, T2, Env, Line) ->
    unify(T1, T2, Env, Line, false).

%% `StrictRecords` should be set to `true` whenever unifying the results from
%% multiple branches, e.g. the results of several match clauses or different
%% function versions.  It will cause unify_records/5 to require that all records
%% have precisely the same fields so that a single expression or function will
%% result in the correct type.  Previously this expression:
%%
%%   match sym with
%%     | :a -> {a=true, b=false}
%%     | :b -> {b=false}
%%
%% would result in the type `{a: bool, b: bool}` which is only true for one of
%% the branches!  With `StrictRecords` this doesn't happen any more.
-spec unify(typ(), typ(), env(), integer()) -> ok | {error, term()}.
unify(T1, T2, Env, Line, StrictRecords) ->
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
                    throw(E);
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
            ArrowArgCells = fun({cell, _}=C) ->
                                    {t_arrow, Xs, _}=get_cell(C),
                                    Xs;
                               ({t_arrow, Xs, _}) -> Xs
                            end,
            case unify_list(ArrowArgCells(T1), ArrowArgCells(T2), Env, Line) of
                {error, _} = E  -> E;
                _ ->
                    %% Unwrap cells and links down to the first non-cell level.
                    %% Super gross.
                    F = fun({cell, _}=C) ->
                                case get_cell(C) of
                                    {t_receiver, _, _}=R ->
                                        R;
                                    {link, {cell, _}=CC} ->
                                        case get_cell(CC) of
                                            {t_receiver, _, _}=R2 -> R2;
                                            _ -> none
                                        end;
                                    {link, {t_receiver, _, _}=R2} -> R2;
                                    _ -> none
                                end;
                           ({link, {cell, _}=CC}) ->
                                case get_cell(CC) of
                                    {t_receiver, _, _}=R2 -> R2;
                                    _ -> none
                                end;
                           ({t_receiver, _, _}=X) -> X;
                           (_) -> none
                        end,
                    AArgs = case T1 of
                                {cell, _} ->
                                    {t_arrow, Xs, _}=get_cell(T1),
                                    Xs;
                                _ ->
                                    {t_arrow, Xs, _}=T1,
                                    Xs
                            end,

                    StripCell = fun({cell, _}=C)         -> get_cell(C);
                                   ({link, {cell, _}=C}) -> get_cell(C);
                                   %% TODO:  un-celled link?  Seems bad.  Verify and fix.
                                   ({link, X})           -> X;
                                   (X) -> X
                                end,
                    NoCellArgs = lists:map(StripCell, lists:map(StripCell, AArgs)),
                    RR = [Receiver||{t_receiver, _, _}=Receiver
                                        <- lists:map(F, NoCellArgs)],
                    %% Any argument to a function application that is a receiver
                    %% makes the entire expression a receiver.
                    case RR of
                        [] ->
                            unify(A2, B2, Env, Line, true);
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
                                    case unify(A2, B2, Env, Line, true) of
                                        {error, _}=Err -> Err;
                                        ok ->
                                            %% Re-wrapping with fresh cells
                                            %% because I was running into
                                            %% cycles. This entire block of
                                            %% arrow unification needs to be
                                            %% rewritten.
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
        {{t_map, A1, B1}, {t_map, A2, B2}} ->
            case unify(A1, A2, Env, Line) of
                {error, _}=Err -> Err;
                ok ->
                    case unify(B1, B2, Env, Line) of
                        {error, _}=Err -> Err;
                        ok -> ok
                    end
            end;

        {#t_record{}=LowerBound, #t_record{}=Target} ->
            unify_records(LowerBound, Target, Env, Line, StrictRecords);

        {#adt{}=A, B} -> unify_adt(T1, T2, A, B, Env, Line);
        {A, #adt{}=B} -> unify_adt(T2, T1, B, A, Env, Line);

        {{t_pid, _}, {t_pid, _}} ->
            {t_pid, AC} = get_cell(T1),
            {t_pid, BC} = get_cell(T2),
            case unify(AC, BC, Env, Line) of
                {error, _}=Err -> Err;
                ok ->
                    set_cell(T1, {t_pid, AC}),
                    set_cell(T2, {link, T1}),
                    ok
            end;

%%% Receivers unify with each other or in the case of a receiver and
%%% something else, the receiver unifies its result type with the other
%%% expression and both become receivers.
        {{t_receiver, _, _}, {t_receiver, _, _}} ->
            RecvRes = fun({cell, _}=C) ->
                              {t_receiver, _, X} = get_cell(C),
                              X;
                         ({t_receiver, _, X}) ->
                              X
                      end,
            RecvR = fun({cell, _}=C) ->
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
            %% Use strict record unification for return value typing:
            case unify(ResA, ResB, Env, Line, true) of
                {error, _}=Err -> Err;
                ok ->
                    NewTyp = {t_receiver, Recv, {t_arrow, Args, ResA}},
                    set_cell(new_cell(T1), NewTyp),
                    set_cell(new_cell(T2), {link, T1}),
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
                    Err;
                {ok, _EnvOut, Union} ->
%                    set_cell(T1, Union),
                    set_cell(T2, {link, Union}),
                    ok
            end
    end.

%%% Here we're checking for membership of one party in another or for an
%%% exact match.  ADTs with the same name are checked as the same only if
%%% they also come from the same module.
-spec unify_adt(cell(), cell(), t_adt(), typ(), env(), Line::integer()) ->
                       ok |
                       {error, {cannot_unify, typ(), typ()}}.
unify_adt(C1,
          C2,
          #adt{name=N, vars=AVars, module=M}=A,
          #adt{name=N, vars=BVars, module=M},
          Env, L) ->
    %% Don't unify the keys _and_ vars:
    case unify_list([V||{_, V} <- AVars], [V||{_, V} <- BVars], Env, L) of
        {error, _}=Err -> Err;
        _ ->
            set_cell(C1, A),
            set_cell(C2, {link, C1}),
            ok
    end;
unify_adt(C1, C2, #adt{vars=Vs, members=Ms}=A, AtomTyp, Env, L)
  when is_atom(AtomTyp) ->
    case [M||M <- Ms, unwrap(M) =:= AtomTyp] of
        [_] ->
            set_cell(C1, A),
            set_cell(C2, {link, C1}),
            ok;
        []  ->
            VFolder = fun(_, ok) -> ok;
                         ({_, V}, Res) ->
                            case lists:member(V, Ms) of
                              true -> unify(AtomTyp, V, Env, L);
                              false -> Res
                            end
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

    %% as a result of instantiating types some members might be in reference
    %% cells.  We unpack them before searching for the right encompassing
    %% type so we don't miss anything:
    UnpackMembers = fun(Ms) -> [get_cell(M) || M <- Ms] end,

    case lists:filter(MemberFilter(NB), UnpackMembers(MA)) of
        [#adt{vars=ToCheck}] ->
            UnifyFun = fun(_, {error, _}=Err)    -> Err;
                          ({{_, X}, {_, Y}}, ok) -> unify(X, Y, Env, L)
                       end,
            lists:foldl(UnifyFun, ok, lists:zip(VarsB, ToCheck));
        _ ->
            case lists:filter(MemberFilter(NA), UnpackMembers(MB)) of
                [#adt{vars=ToCheck}] ->
                    UnifyFun = fun(_, {error, _}=Err)    -> Err;
                                  ({{_, X}, {_, Y}}, ok) -> unify(X, Y, Env, L)
                               end,
                    lists:foldl(UnifyFun, ok, lists:zip(VarsA, ToCheck));
                _ ->
                    unify_error(Env, L, A, B)
            end
    end;

unify_adt(C1, C2, #adt{}=A, {t_tuple, _}=ToCheck, Env, L) ->
    unify_adt_and_poly(C1, C2, A, ToCheck, Env, L);
unify_adt(C1, C2, #adt{}=A, {t_list, _LType}=ToCheck, Env, L) ->
    unify_adt_and_poly(C1, C2, A, ToCheck, Env, L);
unify_adt(C1, C2, #adt{}=A, {t_map, _, _}=ToCheck, Env, L) ->
    unify_adt_and_poly(C1, C2, A, ToCheck, Env, L);
unify_adt(C1, C2, #adt{}=A, #t_record{}=ToCheck, Env, L) ->
    unify_adt_and_poly(C1, C2, A, ToCheck, Env, L);
unify_adt(C1, C2, #adt{}=A, {t_arrow, _, _}=ToCheck, Env, L) ->
    unify_adt_and_poly(C1, C2, A, ToCheck, Env, L);
unify_adt(C1, C2, #adt{}=A, #alpaca_type{}=T, Env, L) ->
    {ok, Env2, B, _} = inst_type(T, Env),
    unify_adt(C1, C2, A, get_cell(B), Env2, L);
unify_adt(_, _, A, B, Env, L) ->
    io:format("*** The failed ADT unification candidates were:~n~p ~p~n~p ~p~n", [A, unwrap(A), B, unwrap(B)]),
    unify_error(Env, L, A, B).

unify_adt_and_poly(C1, C2, #adt{members=Ms}=A, {cell, _}=ToCheck, Env, L) ->
    %% Try to find an ADT member that will unify with the passed in
    %% polymorphic type:
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
%% ToCheck needs to be in a reference cell for unification and we're not
%% worried about losing the cell at this level since C1 and C2 are what
%% will actually be manipulated.
unify_adt_and_poly(C1, C2, #adt{members=_Ms}=A, ToCheck, Env, L) ->
    unify_adt_and_poly(C1, C2, A, new_cell(ToCheck), Env, L).

%%% Given two different types, find a type in the set of currently available
%%% types that can unify them or fail.
-spec find_covering_type(
        T1::typ(),
        T2::typ(),
        env(),
        integer()) -> {ok, typ(), env()} |
                      {error,
                       {cannot_unify, atom(), integer(), typ(), typ()} |
                       {bad_variable, integer(), alpaca_type_var()}}.
find_covering_type(T1, T2, #env{current_types=Ts}=EnvIn, L) ->
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

    %% We remove all of the types from the environment because we don't want
    %% to reinstantiate them again on unification failure when it's trying
    %% to unify the two types with the instantiated member types.
    %%
    %% For example, if `T1` is `t_int` and the first member of a type we're
    %% checking for valid union is anything _other_ that `t_int`, the call
    %% to `unify` in `try_types` will cause `unify` to call this method
    %% (`find_covering_type`) again, leading to instantiating all of the
    %% types all over again and eventually leading to a spawn limit error.
    %% By simply removing the types from the environment before proceeding,
    %% we avoid this cycle.
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

%% See unify/5 for an explanation of `StrictRecords`.  TLDR; it's used to force
%% an expression with multiple branches to require all returned record types to
%% have the exact same fields.
unify_records(
  #t_record{members=[], row_var=Lower},
  #t_record{members=[], row_var=Target},
  Env,
  Line,
  StrictRecords
) ->
    unify(Lower, Target, Env, Line, StrictRecords);
unify_records(LowerBound, Target, Env, Line, StrictRecords) ->
    %% Unify each member of the lower bound with the others.  We track whether
    %% or not the type is for a pattern because if we _are_ unifying for
    %% patterns then we don't need to check for missing members.
    #t_record{
       is_pattern=P1,
       members=LowerM,
       row_var=LowerRow} = flatten_record(LowerBound),
    #t_record{
       is_pattern=P2,
       members=TargetM,
       row_var=TargetRow} = flatten_record(Target),

    case TargetM of
        [] ->
            %% We use a record with no members to force the row variable of a
            %% record update to be a record.
            unify_records(LowerBound, Target#t_record{members=LowerM}, Env, Line, StrictRecords);
        _ ->
            %% we operate on the target's members so that if the unification
            %% with the lower bound's members succeeds, we have a list of exactly
            %% what needs to unify with the lower's row variable.
            KeyedTarget = lists:map(
                            fun(#t_record_member{name=X}=TRM) -> {X, TRM} end,
                            TargetM),
            RemainingTarget = unify_record_members(
                                P1 or P2,
                                LowerM,
                                KeyedTarget,
                                Env,
                                Line,
                                StrictRecords),

            %% unify the row variables
            case RemainingTarget of
                [] ->
                    unify(LowerRow, TargetRow, Env, Line, StrictRecords);
                _ ->
                    case {LowerRow, TargetRow} of
                        {A, A} ->
                            NewTarget = #t_record{members=RemainingTarget},
                            unify(LowerRow, new_cell(NewTarget), Env, Line, StrictRecords);
                        _ ->
                            NewTarget = #t_record{
                                           members=RemainingTarget,
                                           row_var=TargetRow},
                            unify(LowerRow, new_cell(NewTarget), Env, Line, StrictRecords)
                    end
            end
    end.

unify_record_members(_IsPattern, [], [TargetRem|_], Env, Line, true) ->
    {N, #t_record_member{}} = TargetRem,
    erlang:error({missing_record_field, module_name(Env), Line, N});
unify_record_members(_IsPattern, [], TargetRem, _Env, _Line, _) ->
    lists:map(fun({cell, _}=X) -> X;
                 ({_, X}) -> X
              end, TargetRem);
unify_record_members(IsPattern, [LowerBound|Rem], TargetRem, Env, Line, StrictRecords) ->
    #t_record_member{name=N, type=T} = LowerBound,
    case proplists:get_value(N, TargetRem) of
        undefined when IsPattern =:= false ->
            erlang:error({missing_record_field, module_name(Env), Line, N});
        undefined ->
            unify_record_members(IsPattern, Rem, TargetRem, Env, Line, StrictRecords);
        #t_record_member{type=T2} ->
            case unify(T, T2, Env, Line, StrictRecords) of
                {error, Err} ->
                    erlang:error(Err);
                ok ->
                    NewTargetRem = proplists:delete(N, TargetRem),
                    unify_record_members(IsPattern, Rem, NewTargetRem, Env, Line, StrictRecords)
            end
    end.

%% Record types are basically linked lists where the `row_var` portion
%% could be either an unbound type variable or another record type.  We
%% need to unpack these row variables to unify records predictably and
%% also upon completion of typing.  Problems could occur when unifying the
%% following:
%%
%% #t_record{members={x, t_int}, row_var=#t_record{members={y, t_int}}, ...}
%% #t_record{members={y, t_int}, row_var=#t_record{members={x, t_int}}, ...}
%%
%% Because the members that need unifying (coming from either record to the
%% other) are effectively hidden in their respective row variables,
%% unify_record_members won't see them directly.
flatten_record(#t_record{members=Ms, row_var=#t_record{}=Inner}) ->
    #t_record{members=InnerMs, row_var=InnerRow} = Inner,

    %% Now de-dupe fields, preferring newer ones:
    Deduped = lists:foldl(
                fun(#t_record_member{name=N, type=T}, Map) -> maps:put(N, T, Map) end,
                maps:new(),
                lists:reverse(Ms ++ InnerMs)),

    RecMems = [#t_record_member{name=N, type=T} || {N, T} <- maps:to_list(Deduped)],
    Rec = #t_record{members=RecMems, row_var=InnerRow},
    flatten_record(Rec);
flatten_record(#t_record{row_var={cell, _}=Cell}=R) ->
    case get_cell(Cell) of
        #t_record{}=Inner -> flatten_record(R#t_record{row_var=Inner});
        {link, L}=_Link   -> flatten_record(R#t_record{row_var=L});
        {unbound, _, _}   -> R;
        Other                 -> erlang:error({bad_row_var, Other, R})
    end;
flatten_record(#t_record{}=R) ->
    R.

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
-spec inst_type(alpaca_type(), EnvIn::env()) ->
                       {ok, env(), typ(), list(typ())} |
                       {error, {bad_variable, integer(), alpaca_type_var()}}.
inst_type(Typ, EnvIn) ->
    #alpaca_type{name={type_name, _, N}, module=Mod, vars=Vs, members=Ms} = Typ,
    {Vars, Env} = inst_type_vars(Vs, [], EnvIn),
    F = fun(#alpaca_type{name={_, _, NN}, module=M}, undefined) when NN =:= N ->
                M;
           (_, M) ->
                M
        end,
    Mod2 = lists:foldl(F, Mod, Env#env.current_types),
    ParentADT = #adt{name=N, module=Mod2, vars=lists:reverse(Vars)},
    inst_type_members(ParentADT, Ms, Env, []).

inst_type_vars([], DoneVars, Env) ->
    {DoneVars, Env};
inst_type_vars([{type_var, _, VN}|Rem], DoneVars, Env) ->
    {TVar, E2} = new_var(0, Env),
    inst_type_vars(Rem, [{VN, TVar}|DoneVars], E2);
inst_type_vars([{{type_var, _, VN}, #alpaca_type{}=T}|Rem], DoneVars, Env) ->
    {ok, Env2, ADT, _} = inst_type(T, Env),
    inst_type_vars(Rem, [{VN, new_cell(ADT)}|DoneVars], Env2);
inst_type_vars([{{type_var, _, VN}, Expr}|Rem], DoneVars, E) ->
    %% copy_cell/1 should put every nested member properly
    %% into its own reference cell:
    {E2, Cell} = case get_cell(Expr) of
                     #alpaca_type{}=AT ->
                         {ok, Env2, Typ, _} = inst_type(AT, E),
                         {Env2, Typ};
                     _ ->
                         {Celled, _} = copy_cell(Expr, maps:new()),
                         {E, Celled}
                 end,
    inst_type_vars(Rem, [{VN, Cell}|DoneVars], E2).

inst_type_members(ParentADT, [], Env, FinishedMembers) ->
    {ok,
     Env,
     new_cell(ParentADT#adt{members=FinishedMembers}),
     lists:reverse(FinishedMembers)};
%% single atom types are passed unchanged (built-in types):
inst_type_members(ParentADT, [H|T], Env, Memo) when is_atom(H) ->
    inst_type_members(ParentADT, T, Env, [new_cell(H)|Memo]);
inst_type_members(ADT, [{t_list, TExp}|Rem], Env, Memo) ->
    case inst_type_members(ADT, [TExp], Env, []) of
        {error, _}=Err -> Err;
        {ok, Env2, _, [InstMem]} ->
            inst_type_members(ADT, Rem, Env2,
                              [new_cell({t_list, InstMem})|Memo])
    end;
inst_type_members(ADT, [{t_map, KExp, VExp}|Rem], Env, Memo) ->
    case inst_type_members(ADT, [KExp], Env, []) of
        {error, _}=Err -> Err;
        {ok, Env2, _, [InstK]} ->
            case inst_type_members(ADT, [VExp], Env2, []) of
                {error, _}=Err -> Err;
                {ok, Env3, _, [InstV]} ->
                    NewT = new_cell({t_map, InstK, InstV}),
                    inst_type_members(ADT, Rem, Env3, [NewT|Memo])
            end
    end;

inst_type_members(ADT, [#t_record{}=R|Rem], Env, Memo) ->
    #t_record{members=Ms, row_var=RV} = R,
    {RVC, Env2} = case RV of
                      undefined ->
                          {V, E} = new_var(0, Env),
                          {V, E};
                      {unbound, _, _}=V ->
                          {new_cell(V), Env};
                      _ ->
                          {RV, Env}
                  end,
    F = fun(#t_record_member{type=T}=M, {NewMems, _E}) ->
                case inst_type_members(ADT, [T], Env, []) of
                    {error, _}=Err ->
                        erlang:error(Err);
                    {ok, E2, _, [InstT]} ->
                        {[M#t_record_member{type=InstT}|NewMems], E2}
                end
        end,
    {NewMems, Env3} = lists:foldl(F, {[], Env2}, Ms),
    NewT = new_cell(#t_record{members=lists:reverse(NewMems), row_var=RVC}),
    inst_type_members(ADT, Rem, Env3, [NewT|Memo]);

inst_type_members(ADT, [{t_receiver, MExp, BExp}|Rem], Env, Memo) ->
    case inst_type_members(ADT, [MExp], Env, []) of
        {error, _}=Err -> Err;
        {ok, Env2, _, [InstM]} ->
            case inst_type_members(ADT, [BExp], Env2, []) of
                {error, _}=Err -> Err;
                {ok, Env3, _, [InstB]} ->
                    NewT = new_cell({t_receiver, InstM, InstB}),
                    inst_type_members(ADT, Rem, Env3, [NewT|Memo])
            end
    end;
inst_type_members(ADT, [{t_pid, TExp}|Rem], Env, Memo) ->
    case inst_type_members(ADT, [TExp], Env, []) of
        {error, _}=Err ->
            Err;
        {ok, Env2, _, [InstMem]} ->
            inst_type_members(ADT, Rem, Env2,
                              [new_cell({t_pid, InstMem})|Memo])
    end;

inst_type_members(#adt{vars=Vs}=ADT, [{type_var, L, N}|T], Env, Memo) ->
    Default = {error, {bad_variable, L, N}},
    case proplists:get_value(N, Vs, Default) of
        {error, _}=Err -> Err;
        Typ -> inst_type_members(ADT, T, Env, [Typ|Memo])
    end;

inst_type_members(ADT, [{t_arrow, Args, Ret}|T], Env, Memo) ->
    case inst_type_members(ADT, Args, Env, []) of
        {error, _}=Err ->
            Err;
        {ok, Env2, _, InstArgs} ->
            {ok, Env3, _, [InstRet]} = inst_type_members(ADT, [Ret], Env2, []),
            Arrow = new_cell({t_arrow, InstArgs, InstRet}),
            inst_type_members(ADT, T, Env3, [Arrow|Memo])
    end;

inst_type_members(ADT, [#alpaca_type_tuple{members=Ms}|T], Env, Memo) ->
    case inst_type_members(ADT, Ms, Env, []) of
        {error, _}=Err ->
            Err;
        {ok, Env2, _, InstMembers} ->
            inst_type_members(ADT, T, Env2,
                              [new_cell({t_tuple, InstMembers})|Memo])
    end;

inst_type_members(ADT,
                  [#alpaca_type{name={type_name, _, N}, vars=Vs, module=Mod}|T],
                  Env,
                  Memo) ->
    case inst_type_members(ADT, Vs, Env, []) of
        {error, _}=Err -> Err;
        {ok, Env2, _, Members} ->
            Names = [VN || {type_var, _, VN} <- Vs],
            NewMember = #adt{name=N, module=Mod, vars=lists:zip(Names, Members)},
            inst_type_members(ADT, T, Env2, [new_cell(NewMember)|Memo])
    end;
inst_type_members(ADT, [#alpaca_constructor{}=C|T], Env, Memo) ->
    #alpaca_constructor{name=#type_constructor{name=N}, arg=A}=C,
    %% We try to instantiate the constructor's argument just to make sure it's
    %% fully valid, e.g. that it doesn't reference any type variables that don't
    %% exist in the parent ADT's definition.
    {ok, _, _, _} = inst_type_members(ADT, [A], Env, []),
    inst_type_members(ADT, T, Env, [{t_adt_cons, N}|Memo]);

%% Everything else gets discared.  Type constructors are not types in their
%% own right and thus not eligible for unification so we just discard them here:
inst_type_members(ADT, [_H|T], Env, Memo) ->
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
-spec inst_type_arrow(Env::env(), Name::alpaca_constructor_name()) ->
                             {ok, env(), {typ_arrow, typ(), t_adt()}} |
                             {error, {bad_constructor, integer(), string()}} |
                             {error, {unknown_type, string()}} |
                             {error, {bad_constructor_arg,term()}}.
inst_type_arrow(EnvIn, #type_constructor{}=TC) ->
    %% 20160603:  I have an awful lot of case ... of all over this
    %% codebase, trying a lineup of functions specific to this
    %% task here instead.  Sort of want Scala's `Try`.
    ADT_f = fun({error, _}=Err) ->
                    Err;
               (#alpaca_constructor{type=#alpaca_type{}=T}=C) ->
                    {C, inst_type(T, EnvIn)}
            end,
    Cons_f = fun({error, _}=Err) ->Err;
                ({C, {ok, Env, ADT, _}}) ->
                     #adt{vars=Vs} = get_cell(ADT),
                     #alpaca_constructor{arg=Arg} = C,
                     %% We need to include types from other modules even if
                     %% they're not exported so that types we *have* imported
                     %% that depend on those we've not can still be instantiated
                     %% correctly:
                     ExtractTypes = fun(#alpaca_module{types=Ts}) -> Ts end,
                     OtherTs = lists:flatten(lists:map(ExtractTypes, Env#env.modules)),
                     Types = EnvIn#env.current_types ++ OtherTs,
                     {Env2, InstArg} = inst_constructor_arg(Arg, Vs, Types, Env),
                     Arrow = {type_arrow, InstArg, ADT},
                     {Env2, Arrow}
             end,

    %% If the constructor was not qualified with a module name it's pretty
    %% to fetch but if it was, then we need to first make sure it's in
    %% the specified module *and* that its enclosing type is exported.
    %%
    %% Here's the easy local get:
    GetTC = fun(#type_constructor{line=Line, name=Name, module=undefined}) ->
                    Default = {error, {bad_constructor, Line, Name}},
                    %% constructors defined in this module or imported by it:
                    Available = EnvIn#env.type_constructors,
                    proplists:get_value(Name, Available, Default);

               %% and the part where we go to a different module:
               (#type_constructor{line=Line, name=Name, module=Mod}) ->
                    Mods = EnvIn#env.modules,
                    M = [AM || #alpaca_module{name=N}=AM <- Mods, Mod =:= N],
                    case M of
                        [] ->
                            #alpaca_module{name=MN} = EnvIn#env.current_module,
                            throw({error, {bad_module, MN, Line, Mod}});
                        [Target] ->
                            %% in the beginning of typing, constructors/1 links
                            %% the actual type to the constructor contained
                            %% within it to make it easy for inst_type to
                            %% instantiate the type itself.  Here we grab each
                            %% constructor whose name matches the one we're
                            %% looking for and insert the ADT itself in a
                            %% similar manner.
                            Types = Target#alpaca_module.types,
                            Exports = Target#alpaca_module.type_exports,

                            F = fun(#alpaca_type{members=Ms, name={_, _, TypeN}}=AT) ->
                                        Cs = [AC#alpaca_constructor{type=AT} ||
                                                 #alpaca_constructor{
                                                    name=#type_constructor{name=TCN}
                                                   }=AC <- Ms, TCN =:= Name],

                                        %% Now we make sure the type that the
                                        %% constructor belongs to is actually
                                        %% exported:
                                        case [E || E <- Exports, E =:= TypeN] of
                                            []  -> [];
                                            [_] -> Cs
                                        end
                                end,
                            case lists:flatten(lists:map(F, Types)) of
                                [RealC] ->
                                    RealC;
                                [] ->
                                    throw({error, {bad_constructor, Line, Name}})
                            end
                    end
            end,
    try Cons_f(ADT_f(GetTC(TC)))
    catch
        throw:{error, _}=Error -> Error
    end.

inst_constructor_arg(none, _, _, Env) ->
    {Env, t_unit};
inst_constructor_arg(AtomType, _, _, Env) when is_atom(AtomType) ->
    {Env, AtomType};
inst_constructor_arg({type_var, _, N}, Vs, _, Env) ->
    case proplists:get_value(N, Vs) of
        undefined -> throw({error, {unknown_type_var, N}});
        V -> {Env, V}
    end;
inst_constructor_arg(#t_record{members=Ms}=R, Vs, Types, Env) ->
    F = fun(#t_record_member{type=T}=M) ->
                case inst_constructor_arg(T, Vs, Types, Env) of
                    {error, _}=E -> erlang:error(E);
                    {_, T2}      -> M#t_record_member{type=T2}
                end
        end,
    {Var, Env2} = new_var(0, Env),
    {Env2, new_cell(R#t_record{members=lists:map(F, Ms), row_var=Var})};
inst_constructor_arg(#alpaca_constructor{name=#type_constructor{name=N}},
                     _Vs, _Types, Env) ->
    {Env, {t_adt_cons, N}};
inst_constructor_arg(#alpaca_type_tuple{members=Ms}, Vs, Types, Env) ->
    F = fun(M, {E, Memo}) ->
                {E2, M2} = inst_constructor_arg(M, Vs, Types, E),
                {E2, [M2|Memo]}
        end,
    {Env2, Ms2} = lists:foldl(F, {Env, []}, Ms),
    {Env2, new_cell({t_tuple, lists:reverse(Ms2)})};
inst_constructor_arg({t_list, ElementType}, Vs, Types, Env) ->
    {Env2, ListElem} = inst_constructor_arg(ElementType, Vs, Types, Env),
    {Env2, new_cell({t_list, ListElem})};
inst_constructor_arg({t_map, KeyType, ValType}, Vs, Types, Env) ->
    {Env2, KElem} = inst_constructor_arg(KeyType, Vs, Types, Env),
    {Env3, VElem} = inst_constructor_arg(ValType, Vs, Types, Env2),
    {Env3, new_cell({t_map, KElem, VElem})};
inst_constructor_arg({t_receiver, MsgT, BodyT}, Vs, Types, Env) ->
    {Env2, MElem} = inst_constructor_arg(MsgT, Vs, Types, Env),
    {Env3, BElem} = inst_constructor_arg(BodyT, Vs, Types, Env2),
    {Env3, new_cell({t_receiver, MElem, BElem})};
inst_constructor_arg({t_pid, MsgType}, Vs, Types, Env) ->
    {Env2, PidElem} = inst_constructor_arg(MsgType, Vs, Types, Env),
    {Env2, new_cell({t_pid, PidElem})};
inst_constructor_arg(#alpaca_type{name={type_name, _, N}, vars=Vars, members=M1},
                     Vs, Types, Env) ->
    #alpaca_type{vars = V2, members=M2, module=Mod} = find_type(N, Types),

    %% when a polymorphic ADT occurs in another type's definition it might
    %% have concrete types assigned rather than variables and thus we want
    %% to find the original/biggest list of vars for the type.  E.g.
    %%
    %% type option 'a = Some 'a | None
    %% type either_int 'a = Left 'a | Right option int
    %%
    VarsToUse = case length(V2) > length(Vars) of
                    true -> V2;
                    false -> Vars
                end,

    F = fun({type_var, _, VN}) ->
                {VN, proplists:get_value(VN, Vs)};
           ({{type_var, _, _}=VN, CT}=_ConcreteType) ->
                %% the "concrete" type might actually be an as-yet
                %% uninstantiated type which will lead to unification
                %% failures later.  Instead of assuming it's one of our base
                %% types we instantiate it like anything else.  Here I haven't
                %% worried about the returned environment as I think we're
                %% safely covered by using the already known variables and
                %% existing environment:
                {_, InstCT} = inst_constructor_arg(CT, VarsToUse, Types, Env),
                {VN, InstCT}
        end,
    ADT_Vars = lists:map(F, VarsToUse),
    Vs2 = replace_vars(M1, V2, Vs),
    {Env2, Members} = lists:foldl(
                        fun(M, {E, Memo}) ->
                                {E2, MM} = inst_constructor_arg(M, Vs2, Types, E),
                                {E2, [MM|Memo]}
                        end,
                        {Env, []},
                        M2),

    ADT = #adt{
             name=N,
             vars=ADT_Vars,
             members=lists:reverse(Members),
             module=Mod},
    {Env2, new_cell(ADT)};

inst_constructor_arg({t_arrow, ArgTypes, RetType}, Vs, Types, Env) ->
    F = fun(A, {E, Memo}) ->
                {E2, A2} = inst_constructor_arg(A, Vs, Types, E),
                {E2, [A2|Memo]}
        end,
    {Env2, InstantiatedArgs} = lists:foldl(F, {Env, []}, ArgTypes),
    {Env3, InstantiatedRet} = inst_constructor_arg(RetType, Vs, Types, Env2),
    {Env3, new_cell({t_arrow, lists:reverse(InstantiatedArgs), InstantiatedRet})};

inst_constructor_arg(Arg, _, _, _) ->
    throw({error, {bad_constructor_arg, Arg}}).

find_type(Name, []) -> throw({error, {unknown_type, Name}});
find_type(Name, [#alpaca_type{name={type_name, _, Name}}=T|_]) -> T;
find_type(Name, [_|Types]) -> find_type(Name, Types).

replace_vars([], _, _) -> [];
replace_vars([{type_var, _, N}|Ms], [{type_var, _, V}|Vs], PropagatedVs) ->
    [{V,proplists:get_value(N, PropagatedVs)}|replace_vars(Ms, Vs, PropagatedVs)];
replace_vars([M|Ms], [{type_var, _, V}|Vs], PropagatedVs) ->
    [{V,M}|replace_vars(Ms, Vs, PropagatedVs)].

%% Unify two parameter lists, e.g. from a function arrow.
unify_list(As, Bs, Env, L) ->
    unify_list(As, Bs, {[], []}, Env, L).

arity_error(Env, L) ->
    erlang:error({arity_error, module_name(Env), L}).

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


-spec inst_binding(
        VarName :: atom()|string(),
        Line :: integer(),
        Lvl :: integer(),
        Env :: env()) -> {typ(), env(), map()} | {error, term()}.
inst_binding(VarName, Line, Lvl, #env{bindings=Bs} = Env) ->
    Default = {error, {bad_variable_name, module_name(Env), Line, VarName}},
    case proplists:get_value(VarName, Bs, Default) of
        {error, _} = E ->
            case lookup_binding(VarName, Env, E) of
                {ok, T} -> inst(T, Lvl, Env, maps:new());
                Err     -> Err
            end;
        T ->
            inst(T, Lvl, Env, maps:new())
    end.

%% If inst_binding/4 can't find a binding in the environment for the name it was
%% given to look up, it uses this function to see if the name is a top-level
%% binding later in the module:
lookup_binding(VarName, Env, Default) ->
    case Env of
        #env{current_module=#alpaca_module{functions=Funs}} ->
            MatchingFuns = [B || #alpaca_binding{
                                    name={'Symbol', #{name := N}}}=B <- Funs,
                                 N =:= VarName
                           ],
            case MatchingFuns of
                [] ->
                    Default;
                %% There's no way to tell which arity version of a function is
                %% intended from a symbol alone so we're defaulting to the
                %% first one bound to the name we're looking for:
                [F|_] ->
                    case typ_of(Env, 0, F) of
                        {error, _}=E                       -> E;
                        {Typ, _}   -> {ok, Typ}
                    end
            end;
        _ ->
            Default
    end.

%% This is modeled after instantiate/2 github.com/tomprimozic's example
%% located in the URL given at the top of this file.  The purpose of
%% CachedMap is to reuse the same instantiated unbound type variable for
%% every occurrence of the _same_ quantified type variable in a list
%% of function parameters.
%%
%% The return is the instantiated type, the updated environment and the
%% updated cache map.
-spec inst(typ(), integer(), env(), CachedMap::map()) ->
                  {typ(), env(), map()} | {error, term()}.
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
    Arrow = {t_arrow, PTs, RT},
    {Arrow, NewEnv2, M2};
inst({t_receiver, Recv, Body}=_R, Lvl, Env, CachedMap) ->
    {Body2, Env2, Map2} = inst(Body, Lvl, Env, CachedMap),
    {Recv2, Env3, Map3} = inst(Recv, Lvl, Env2, Map2),
    NewR = {t_receiver, Recv2, Body2},
    {NewR, Env3, Map3};

%% Everything else is assumed to be a constant:
inst(Typ, _Lvl, Env, Map) ->
    {Typ, Env, Map}.

-spec new_var(Lvl :: integer(), Env :: env()) -> {cell(), env()}.
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
gen(Lvl, {t_receiver, A, B}) ->
    {t_receiver, gen(Lvl, A), gen(Lvl, B)};
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

unwrap({cell, _}=Cell) ->
    unwrap(get_cell(Cell));
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
unwrap({t_map, K, V}) ->
    {t_map, unwrap(K), unwrap(V)};
unwrap(#t_record{}=R) ->
    #t_record{members=Ms, row_var=RV} = flatten_record(R),
    #t_record{members=lists:map(fun unwrap/1, Ms), row_var=unwrap(RV)};
unwrap(#t_record_member{type=T}=RM) ->
    RM#t_record_member{type=unwrap(T)};
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
    {no_such_type, SourceModule, Module, Type}.

private_type_error(SourceModule, Module, Type) ->
    {unexported_type, SourceModule, Module, Type}.

retrieve_type(SourceModule, Module, Type, []) ->
    throw(missing_type_error(SourceModule, Module, Type));
retrieve_type(SM, M, T, [#alpaca_module{name=M, types=Ts, type_exports=ETs}|Rem]) ->
    case [TT || #alpaca_type{name={type_name, _, TN}}=TT <- Ts, TN =:= T] of
        [#alpaca_type{name={_, _, TN}}=Type] ->
            %% now make sure the type is exported:
            case [X || X <- ETs, X =:= TN] of
                [_] -> {ok, Type};
                _   -> throw(private_type_error(SM, M, T))
            end;
        [] -> retrieve_type(SM, M, T, Rem)
    end;
retrieve_type(SM, M, T, [_|Rem]) ->
    retrieve_type(SM, M, T, Rem).

-spec type_modules([alpaca_module()]) -> {ok, [alpaca_module()]} |
                                       {error, term()}.
type_modules(Mods) ->
    {Pid, Monitor} = erlang:spawn_monitor(fun() ->
        try type_modules(Mods, new_env(Mods), []) of
            Res -> exit(Res)
        catch
            %% We want the underlying error that resulted in the bad match,
            %% not the `badmatch` itself:
            error:{badmatch, {error, _}=Err} ->
                exit(Err);
            E:T ->
                io:format("alpaca_typer:type_modules/2 crashed with ~p:~p~n"
                          "Stacktrace:~n~p~n", [E, T, erlang:get_stacktrace()]),
                exit({error, T})
        end
    end),
    receive
        {'DOWN', Monitor, process, Pid, Result} -> Result
    end.

type_modules([], _, Acc)       -> {ok, Acc};
type_modules([M|Ms], Env, Acc) ->
    case type_module(M, Env) of
        {ok, M2}       ->
            type_modules(Ms, replace_env_module(Env, M2), [M2|Acc]);
        {error, _}=Err ->
            Err
    end.

-spec type_module(M::alpaca_module(), Env::env()) -> {ok, alpaca_module()} |
                                                   {error, term()}.
type_module(#alpaca_module{precompiled=true}=M, _Env) -> 
    {ok, M};
type_module(#alpaca_module{functions=Fs,
                        name=Name,
                        types=Ts,
                        type_imports=Imports,
                        tests=Tests}=M,
           #env{modules=Modules}=Env) ->
    [] = validate_types(M, Modules),

    %% Fold function to yield all the imported types or report a missing one.
    ImportFolder = fun(_, {error, _}=Err) -> Err;
                      (_, [{error, _}=Err|_]) -> Err;
                      (#alpaca_type_import{module=MN, type=T}, Acc) ->
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
                             entered_modules=[Name|Env2#env.entered_modules]},


                    %% We need to get the environment back from typ_module_funs
                    %% so that the top-level function bindings are available to
                    %% tests:
                    case typ_module_funs(Fs, Env3, []) of
                        {error, _}=Err ->
                            Err;
                        {Env4, FunRes} ->
                            case type_module_tests(Tests, Env4, ok, FunRes) of
                                {error, _} = Err        ->
                                    Err;
                                Funs when is_list(Funs) ->
                                    {ok, M#alpaca_module{functions=Funs, typed=true}}
                            end
                    end
            end
    end.

typ_module_funs([], Env, Memo) ->
    {Env, lists:reverse(Memo)};
typ_module_funs([#alpaca_binding{name={'Symbol', _}=N}=F|Rem], Env, Memo) ->
    Name = alpaca_ast:symbol_name(N),
    case typ_of(Env, 0, F) of
        {error, _} = E ->
            E;
        {Typ, NV} ->
            Env2 = update_counter(NV, Env),
            Env3 = update_binding(Name, Typ, Env2),
            typ_module_funs(Rem, Env3, [F#alpaca_binding{type=unwrap(Typ)}|Memo])
    end.

type_module_tests(_, _Env, {error, _}=Err, _) ->
    Err;
type_module_tests(_, _Env, _, {error, _}=Err) ->
    Err;
type_module_tests([], _, _, Funs) ->
    Funs;
type_module_tests([#alpaca_test{expression=E}|Rem], Env, _, Funs) ->
    type_module_tests(Rem, Env, typ_of(Env, 0, E), Funs).

%% Here we make a quick pass over each type defined in a module to ensure
%% types that are members of a type are defined in this module or imported.
validate_types(#alpaca_module{name=Mod, types=Types, type_imports=Imports}, Mods) ->
    TypeNames =
        [N || #alpaca_type{name={_, _, N}} <- Types] ++
        [N || #alpaca_type_import{type=N} <- Imports],
    validate_types(Mod, TypeNames, Mods, Types).

validate_types(_ModName, _TypeNames, _Modules, []) ->
    [];
validate_types(
  ModName,
  TypeNames,
  Modules,
  [#alpaca_type{module=MN}=H|T]) when MN =:= undefined; MN =:= ModName ->
    #alpaca_type{name={_, L, N}, vars=Vs, members=Ms}=H,
    case [TN || TN <- TypeNames, TN =:= N] of
        [] ->
            throw({unknown_type, ModName, L, N});
        _ ->
            validate_types(ModName, TypeNames, Modules, Ms),
            validate_types(ModName, TypeNames, Modules, Vs),
            validate_types(ModName, TypeNames, Modules, T)
    end;
validate_types(MN, Ts, Mods, [#alpaca_type{}=T|Rem]) ->
    #alpaca_type{name={_, L, N}, module=TargetMod, vars=Vs} = T,
    case [M || #alpaca_module{name=X}=M <- Mods, X =:= TargetMod] of
        [] -> 
            throw({bad_module, MN, L, TargetMod});
        [#alpaca_module{types=Xs}] ->
            case [X || #alpaca_type{name={_, _, Y}}=X <- Xs, Y =:= N] of
                [] -> 
                    throw({unknown_type, MN, L, N});
                [_] ->
                    [] = validate_types(MN, Ts, Mods, Vs),
                    validate_types(MN, Ts, Mods, Rem)
            end
    end;
 validate_types(MN, TNs, Mods, [{{type_var, _, _}, Typ}|T]) ->
     validate_types(MN, TNs, Mods, [Typ]),
     validate_types(MN, TNs, Mods, T);
 validate_types(MN, TNs, Mods, [#alpaca_constructor{arg=A}|T]) ->
    validate_types(MN, TNs, Mods, [A]),
    validate_types(MN, TNs, Mods, T);
 validate_types(ModName, TypeNames, Mods, [#alpaca_type_tuple{members=Ms}|T]) ->
    validate_types(ModName, TypeNames, Mods, Ms),
    validate_types(ModName, TypeNames, Mods, T);
validate_types(MN, Ts, Mods, [#t_record{members=Ms}|T]) ->
    MemberTypes = [Type || #t_record_member{type=Type} <- Ms],
    validate_types(MN, Ts, Mods, MemberTypes ++ T);
validate_types(M, TNs, Mods, [{t_list, LT}|T]) ->
    [] = validate_types(M, TNs, Mods, [LT|T]),
    validate_types(M, TNs, Mods, T);
validate_types(M, TNs, Mods, [{t_map, KT, VT}|T]) ->
    [] = validate_types(M, TNs, Mods, [KT, VT] ++ T),
    validate_types(M, TNs, Mods, T);
validate_types(M, Ts, Mods, [_H|T]) ->
    validate_types(M, Ts, Mods, T).



%% In the past I returned the environment entirely but this contained mutations
%% beyond just the counter for new type variable names.  The integer in the
%% successful return tuple is just the next type variable number so that
%% the environments further up have no possibility of being poluted with
%% definitions below.
-spec typ_of(
        Env::env(),
        Lvl::integer(),
        Exp::alpaca_expression()) -> {typ(), integer()} | {error, term()}.

%% Base types now need to be in reference cells because when they are part
%% of unions they may need to be reset.
typ_of(#env{next_var=VarNum}, _Lvl, {'Int', _}) ->
    {new_cell(t_int), VarNum};
typ_of(#env{next_var=VarNum}, _Lvl, {'Float', _}) ->
    {new_cell(t_float), VarNum};
typ_of(#env{next_var=VarNum}, _Lvl, {boolean, _, _}) ->
    {new_cell(t_bool), VarNum};
typ_of(#env{next_var=VarNum}, _Lvl, {atom, _, _}) ->
    {new_cell(t_atom), VarNum};
typ_of(#env{next_var=VN}, _Lvl, {string, _, _}) ->
    {new_cell(t_string), VN};
typ_of(#env{next_var=VN}, _Lvl, {chars, _, _}) ->
    {new_cell(t_chars), VN};
typ_of(Env, Lvl, {'Symbol', _}=S) ->
    N = alpaca_ast:symbol_name(S),
    L = alpaca_ast:line(S),
    case inst_binding(N, L, Lvl, Env) of
        {error, _} = E -> E;
        {T, #env{next_var=VarNum}, _} -> {T, VarNum}
    end;
typ_of(Env, _Lvl, #alpaca_far_ref{module=Mod, name=N, line=_L, arity=A}) ->
    EnteredModules = [Mod | Env#env.entered_modules],
    {ok, Module, _} = extract_module_bindings(Env, Mod, N),

    Funs = case Module#alpaca_module.typed of
        true ->
            Module#alpaca_module.functions;
        false ->
            %% Type the called function in its own module:
            Env2 = Env#env{current_module=Module,
                          entered_modules=EnteredModules},
            {ok, #alpaca_module{functions=F}} = type_module(Module, Env2),
            F
    end,

    [Typ] = [Typ || #alpaca_binding{
                       name={'Symbol', #{name := X}},
                       type=Typ,
                       bound_expr=#alpaca_fun{arity=Arity}} <- Funs,
                    N =:= X,
                    A =:= Arity],

    Err = fun() ->
                  [CurrMod|_] = Env#env.entered_modules,
                  throw({error, {bidirectional_module_ref, Mod, CurrMod}})
          end,

    case [M || M <- Env#env.entered_modules, M == Mod] of
        []    -> Typ;
        [Mod] -> case Env#env.current_module of
                     #alpaca_module{name=Mod} -> Typ;
                     _ -> Err()
                 end;
        _     -> Err()
    end,

    #env{next_var=NV}=Env,
    %% deep copy to cell the various types, needed
    %% because typing a module unwraps all the
    %% reference cells before returning the module:
    {DT, _} = deep_copy_type(Typ, maps:new()),
    {DT, NV};

typ_of(#env{next_var=VN}, _Lvl, {unit, _}) ->
    {new_cell(t_unit), VN};

%% Errors only type as new variables for the moment to simplify
%% unification with other terms.  I'm considering typing them as
%% a kind of effect that wraps enclosing expressions, similar to
%% how receivers are handled.
typ_of(Env, Lvl, {raise_error, _, _, Expr}) ->
    case typ_of(Env, Lvl, Expr) of
        {error, _}=Err ->
            Err;
        {_, NV} ->
            {T, #env{next_var=NV2}} = new_var(Lvl, update_counter(NV, Env)),
            {T, NV2}
    end;

typ_of(Env, Lvl, {'_', L}) ->
    {T, #env{next_var=VarNum}, _} = inst_binding('_', L, Lvl, Env),
    {T, VarNum};
typ_of(Env, Lvl, #alpaca_tuple{values=Vs}) ->
    case typ_list(Vs, Lvl, Env, []) of
        {error, _} = E -> E;
        {VTyps, NextVar} -> {new_cell({t_tuple, VTyps}), NextVar}
    end;
typ_of(#env{next_var=_VarNum}=Env, Lvl, {nil, _Line}) ->
    {TL, #env{next_var=NV}} = new_var(Lvl, Env),
    {new_cell({t_list, TL}), NV};
typ_of(Env, Lvl, #alpaca_cons{line=Line, head=H, tail=T}) ->
    {HTyp, NV1} = typ_of(Env, Lvl, H),
    {TTyp, NV2} =
        case T of
            {nil, _} -> {new_cell({t_list, HTyp}), NV1};
            #alpaca_cons{}=Cons ->
                typ_of(update_counter(NV1, Env), Lvl, Cons);
            {'Symbol', _} = S ->
                L = alpaca_ast:line(S),
                {STyp, Next} =
                    typ_of(update_counter(NV1, Env), Lvl, S),
                {TL, #env{next_var=Next2}} =
                    new_var(Lvl, update_counter(Next, Env)),
                NC = new_cell({t_list, TL}),
                case unify(NC, STyp, Env, L) of
                    {error, _} = E -> E;
                    ok ->
                        {STyp, Next2}
                end;
            #alpaca_apply{}=Apply ->
                {TApp, Next} = typ_of(update_counter(NV1, Env), Lvl, Apply),
                case unify(
                       new_cell({t_list, HTyp}), TApp, Env, apply_line(Apply))
                of
                    {error, _} = E -> E;
                    ok -> {TApp, Next}
                end;
            NonList ->
                {error, {cons_to_non_list, NonList}}
        end,

    %% TODO:  there's no error check here:
    ListType = case TTyp of
                   {cell, _} ->
                       %% TODO:  this is kind of a gross tree but previously
                       %% there were cases above that would instantiate list
                       %% types that were not celled, leading to some badarg
                       %% exceptions when unifying with ADTs:
                       case get_cell(TTyp) of
                           {link, {t_list, LT}} -> LT;
                           {link, {cell, _}=C} ->
                               case get_cell(C) of
                                   {t_list, LT} -> LT
                               end;
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

typ_of(Env, Lvl, #alpaca_binary{segments=Segs}) ->
    case type_bin_segments(Env, Lvl, Segs) of
        {error, _}=Err -> Err;
        {ok, NV} -> {new_cell(t_binary), NV}
    end;

typ_of(Env, Lvl, #alpaca_map{}=M) ->
    type_map(Env, Lvl, M);
typ_of(Env, Lvl, #alpaca_map_add{line=L, to_add=A, existing=B}) ->
    #alpaca_map_pair{key=KE, val=VE} = A,
    TypA = typ_list([KE, VE], Lvl, Env, []),
    TypB = typ_of(Env, Lvl, B),

    map_typ_of(
      Env, TypA,
      fun(Env2, [KT, VT]) ->
              AMap = new_cell({t_map, KT, VT}),
              map_typ_of(
                Env2, TypB,
                fun(Env3, MTyp) ->
                        map_err(unify(AMap, MTyp, Env3, L),
                                fun(_) -> {MTyp, Env3#env.next_var} end)
                end)
      end);

%% Record typing:
typ_of(Env, Lvl, #alpaca_record{is_pattern=IsPattern, members=Members}) ->
    F = fun(#alpaca_record_member{name=N, val=V}, {ARMembers, E}) ->
                case typ_of(E, Lvl, V) of
                    {error, _}=Err ->
                        erlang:error(Err);
                    {VTyp, NextVar} ->
                        MTyp = #t_record_member{name=N, type=VTyp},
                        {[MTyp|ARMembers], update_counter(NextVar, E)}
                end
        end,
    {Members2, Env2} = lists:foldl(F, {[], Env}, Members),
    {RowVar, Env3} = new_var(Lvl, Env2),
    Res = new_cell(#t_record{
                      is_pattern=IsPattern,
                      members=lists:reverse(Members2),
                      row_var=RowVar}),
    {Res, Env3#env.next_var};

typ_of(Env, Lvl, #alpaca_record_transform{additions=Adds, existing=Exists, line=L}) ->
    {ExistsType, NV} = case typ_of(Env, Lvl, Exists) of
                           {error, _}=Err -> throw(Err);
                           OK -> OK
                       end,
    {EmptyRecType, NV2} = typ_of(update_counter(NV, Env), Lvl, #alpaca_record{line=L}),

    Env2 = update_counter(NV2, Env),
    ok = unify(EmptyRecType, ExistsType, Env2, Lvl),
    #t_record{row_var=RV} = get_cell(EmptyRecType),
    AddsRec = #alpaca_record{members=Adds, line=L},
    {AddsRecCell, NV3} = typ_of(Env2, Lvl, AddsRec),

    #t_record{members=AddMs} = get_cell(AddsRecCell),
    Flattened = flatten_record(#t_record{members=AddMs, row_var=RV}),
    #t_record{members=FlatMems, row_var=FlatVar} = Flattened,

    %% Now de-dupe fields, preferring newer ones:
    Deduped = lists:foldl(
                fun(#t_record_member{name=N, type=T}, Map) -> maps:put(N, T, Map) end,
                maps:new(),
                lists:reverse(FlatMems)),

    RecMems = [#t_record_member{name=N, type=T} || {N, T} <- maps:to_list(Deduped)],
    Rec = #t_record{members=RecMems, row_var=FlatVar},
    {new_cell(Rec), NV3};

typ_of(Env, _Lvl, #alpaca_type_apply{name=N, arg=none}) ->
    case inst_type_arrow(Env, N) of
        {error, _}=Err -> Err;
        {Env2, {type_arrow, _CTyp, RTyp}} ->
            {RTyp, Env2#env.next_var}
    end;
typ_of(Env, Lvl, #alpaca_type_apply{name=N, arg=A}) ->
    %% Some things come back from typing without being properly contained in a
    %% reference cell, specifically those bound to symbols.  This can be a
    %% problem when typing this kind of application because we jump straight
    %% to unify/4 which requires both arguments to be in cells while other parts
    %% of the typer balk at things being immediately celled.  An overhaul of the
    %% inferencer is in order pretty soon I think.
    EnsureCelled = fun({cell, _}=X) -> X;
                      (X)           -> new_cell(X)
                   end,

    case inst_type_arrow(Env, N) of
        {error, _}=Err -> Err;
        {Env2, {type_arrow, CTyp, RTyp}} ->
            case typ_of(Env2, Lvl, A) of
                {error, _}=Err -> Err;
                {ATyp, NVNum} ->
                    #type_constructor{line=L} = N,
                    case unify(CTyp,
                               EnsureCelled(ATyp),
                               update_counter(NVNum, Env2), L)
                    of
                        ok             -> {RTyp, NVNum};
                        {error, _}=Err -> Err
                    end
            end
    end;

%% BIFs are loaded in the environment as atoms:
typ_of(Env, Lvl, {bif, AlpacaName, L, _, _}) ->
    case inst_binding(AlpacaName, L, Lvl, Env) of
        {error, _} = E ->
            E;
        {T, #env{next_var=VarNum}, _} ->
            {T, VarNum}
    end;

typ_of(Env, Lvl, #alpaca_apply{expr={Mod, {'Symbol', _}=Sym, Arity}, args=Args}) ->
    X = alpaca_ast:symbol_name(Sym),
    L = alpaca_ast:line(Sym),
    Satisfy =
        fun() ->
                %% Naively assume a single call to the same function for now.
                %% does the module exist and does it export the function?
                case extract_fun(Env, Mod, X, Arity) of
                    {error, _} = E -> E;
                    {ok, Module, _Fun} ->
                        EnteredModules = [Mod | Env#env.entered_modules],
                        FarMod = case Module#alpaca_module.typed of
                            true ->
                                {ok, Module};
                            false ->
                                %% Type the called function in its own module:
                                Env2 = Env#env{current_module=Module,
                                               entered_modules=EnteredModules},
                                type_module(Module, Env2)
                        end,


                        %% Type the called function in its own module:
                        case FarMod of
                            {ok, #alpaca_module{functions=Funs}} ->
                                [T] = [Typ ||
                                          #alpaca_binding{
                                             name={'Symbol', #{name := N}},
                                             type=Typ,
                                             bound_expr=#alpaca_fun{
                                                           arity=A}} <- Funs,
                                          N =:= X,
                                          A =:= Arity],
                                #env{next_var=NextVar}=Env,
                                %% deep copy to cell the various types, needed
                                %% because typing a module unwraps all the
                                %% reference cells before returning the module:
                                {DT, _} = deep_copy_type(T, maps:new()),
                                typ_apply(Env, Lvl, DT, NextVar, Args, L);
                            {error, _}=Err ->
                                Err
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
                     #alpaca_module{name=Mod} -> Satisfy();
                     _ -> Error()
                 end;
        _  -> Error()
    end;

typ_of(Env, Lvl, #alpaca_apply{line=L, expr=Expr, args=Args}) ->
    %% When we hit arity failures, it may be because the user
    %% is intending a curried application. This function attempts
    %% to find a potential function that can be unambigiously
    %% curried, and then types against that by manipulating the
    %% argument list and return type
    LocalCurryFun =
        fun() ->
            %% If we got an arrow type, if we couldn't find it in the
            %% top level, and it still didn't unify, it might be
            %% a local binding we can still curry.
            case typ_of(Env, Lvl, Expr) of
                {error, {bad_variable_name, _, _, _}} = E -> E;
                {error, _} = E -> E;
                {{t_arrow, TArgs, TRet}, NextVar} ->
                    case length(Args) >= length(TArgs) of
                        true ->
                            {'Symbol', #{name := N, line := _Ln}} = Expr,
                            Mod = Env#env.current_module#alpaca_module.name,
                            {error, {not_found, Mod, N, length(Args)}};
                        false ->
                            {CurryArgs, RemArgs} = lists:split(length(Args), TArgs),
                            CurriedTypF = {t_arrow, CurryArgs, {t_arrow, RemArgs, TRet}},
                            typ_apply(Env, Lvl, CurriedTypF, NextVar, Args, L)
                    end
            end
        end,
    CurryFun =
        fun(_OriginalErr) ->
            %% Attempt to find a curryable version
            {Mod, FN, Env2} = case Expr of
                {'Symbol', _}=Sym ->
                    FunName = alpaca_ast:symbol_name(Sym),
                    {Env#env.current_module, FunName, Env};

                {bif, FunName, _, _, _} ->
                    {Env#env.current_module, FunName, Env};

                {alpaca_far_ref, _, ModName, FunName, _} ->
                    EnteredModules = [Env#env.current_module | Env#env.entered_modules],
                    {ok, Module, _} = extract_module_bindings(Env, ModName, FunName),
                    E = Env#env{current_module=Module,
                                entered_modules=EnteredModules},
                    {Module, FunName, E}
            end,
            CurryFuns = get_curryable_funs(Mod, FN, length(Args)+1),
            case CurryFuns of
                [] -> LocalCurryFun();
                [Item] -> case typ_of(Env2, Lvl, Item) of
                                {{t_arrow, TArgs, TRet}, NextVar} ->
                                    {CurryArgs, RemArgs} = lists:split(length(Args), TArgs),
                                    CurriedTypF = {t_arrow, CurryArgs, {t_arrow, RemArgs, TRet}},
                                    typ_apply(Env2, Lvl, CurriedTypF, NextVar, Args, L)
                          end;
                Items -> {error, {ambiguous_curry, Expr, Items, L}}
            end
    end,
    %% If the expression we're applying arguments to is a named function
    %% (e.g. a symbol or bif), attempt to find it in the module.
    %% This ForwardFun function is used specifically to find functions defined
    %% later than the application we're trying to type.
    ForwardFun =
        fun() ->
                FN = case Expr of
                         {'Symbol', _}=Sym       -> alpaca_ast:symbol_name(Sym);
                         {bif, FunName, _, _, _} -> FunName
                     end,
                Mod = Env#env.current_module,
                case get_fun(Mod, FN, length(Args)) of
                    {ok, _, Fun} ->
                        case typ_of(Env, Lvl, Fun) of
                            {error, _}=Err -> Err;
                            {TypF, NextVar} ->
                                %% We should have a t_arrow taking some args with a return value
                                %% What we need is a t_arrow that takes some of those args and returns
                                %% another t_arrow taking the remainder and returning the final arg
                                try
                                    typ_apply(Env, Lvl, TypF, NextVar, Args, L)
                                catch
                                    throw:{arity_error, _, _} = Err -> CurryFun(Err)
                                end
                        end;
                    {error, _} = E -> CurryFun(E)
                end
        end,

    case typ_of(Env, Lvl, Expr) of
        {error, {bad_variable_name, _, _, _}} -> ForwardFun();
        {error, _} = E -> E;
        {TypF, NextVar} ->
            %% If the function in the environment is the wrong arity we want to
            %% try to locate a matching one in the module.
            %% This does not allow for different arity functions in a sequence
            %% of let bindings which could be a weakness.
            %%
            try
                typ_apply(Env, Lvl, TypF, NextVar, Args, L)
            catch
                error:{arity_error, _, _} ->
                    case Expr of
                        #alpaca_far_ref{} -> CurryFun({error, uncurryable_far_ref});
                        _ -> ForwardFun()
                    end
            end
    end;

%% Unify the patterns with each other and resulting expressions with each
%% other, then unifying the general pattern type with the match expression's
%% type.
typ_of(Env, Lvl, #alpaca_match{match_expr=E, clauses=Cs, line=Line}) ->
    {ETyp, NextVar1} = typ_of(Env, Lvl, E),
    Env2 = update_counter(NextVar1, Env),

    case unify_clauses(Env2, Lvl, Cs) of
        {error, _} = Err -> Err;
        {ok, {t_clause, PTyp, _, RTyp}, #env{next_var=NextVar2}}  ->
            %% unify the expression with the unified pattern:
            case unify(PTyp, ETyp, Env, Line) of
                {error, _} = Err -> Err;
                %% only need to return the result type of the unified
                %% clause types:
                ok -> {RTyp, NextVar2}
            end
    end;

typ_of(Env, Lvl, #alpaca_clause{pattern=P, guards=Gs, result=R, line=L}) ->
    case add_bindings(P, Env, Lvl, 0) of
        {error, _}=Err -> Err;
        {PTyp, _, NewEnv, _} ->
            F = fun(_, {error, _}=Err) -> Err;
                   (G, {Typs, AccEnv}) ->
                        case typ_of(AccEnv, Lvl, G) of
                            {error, _}=Err ->
                                Err;
                            {GTyp, NV} ->
                                {[GTyp|Typs], update_counter(NV, AccEnv)}
                        end
                end,
            case lists:foldl(F, {[], NewEnv}, Gs) of
                {error, _}=Err -> Err;
                {GTyps, Env2} ->
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
                                {RTyp, NextVar2} ->
                                    {{t_clause, PTyp, none, RTyp}, NextVar2}
                            end
                    end
            end
    end;

%%% Pattern match guards that both check the type of an argument and cause
%%% it's type to be fixed.
typ_of(Env, Lvl, #alpaca_type_check{type=T, expr=E, line=L}) ->
    Typ = proplists:get_value(T, ?all_type_checks),
    case typ_of(Env, Lvl, E) of
        {error, _}=Err -> Err;
        {ETyp, NV} ->
            %% polymorphic built-in types like PIDs need to be instantiated
            %% with appropriate type variables before getting unified.
            {Env2, ToUnify} = case Typ of
                                  t_pid ->
                                      {PidT, E2} = new_var(Lvl, Env),
                                      {E2, new_cell({t_pid, PidT})};
                                  _ ->
                                      {Env, new_cell(Typ)}
                              end,
            case unify(ToUnify, ETyp, Env2, L) of
                {error, _}=Err -> Err;
                ok -> {t_bool, NV}
            end
    end;

typ_of(Env, Lvl, #alpaca_send{line=L, message=M, pid=P}) ->
    case typ_of(Env, Lvl, P) of
        {error, _}=Err -> Err;
        {T, NV} ->
            {PidT, Env2} = new_var(Lvl, Env),
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
typ_of(Env, Lvl, #alpaca_receive{}=Recv) ->
    type_receive(Env, Lvl, Recv);

%%% Calls to Erlang code only have their return value typed.
%%% However, we also check that the arguments refer to in-scope names.
typ_of(Env, Lvl, #alpaca_ffi{args=Args}=FFI) ->
    case typ_ffi_args(Env, Lvl, Args) of
        ok -> typ_ffi_clauses(Env, Lvl, FFI);
        {error, _}=Err -> Err
    end;

%% Spawning of functions in the current module:
typ_of(Env, Lvl, #alpaca_spawn{line=L, module=undefined, function=F, args=Args}) ->
    %% make a function application and type it:
    Apply = #alpaca_apply{line=L, expr=F, args=Args},

    case typ_of(Env, Lvl, F) of
        {error, _}=Err -> Err;
        {SpawnFunTyp, NV} ->
            Env2 = update_counter(NV, Env),
            case typ_of(Env2, Lvl, Apply) of
                {error, _}=Err -> Err;
                {_AT, NV2} ->
                    %% use the type of the application to type a pid but prefer
                    %% the one determined by typing the application.
                    case SpawnFunTyp of
                        {t_receiver, Recv, _} ->
                            case _AT of
                                {t_receiver, Recv2, _} ->
                                    {new_cell({t_pid, Recv2}), NV2};
                                _ ->
                                    {new_cell({t_pid, Recv}), NV2}
                                end;
                        _ ->
                            {new_cell({t_pid, new_cell(undefined)}), NV2}
                    end
            end
    end;

typ_of(EnvIn, Lvl, #alpaca_fun{line=L, name=N, versions=Vs}) ->
    F = fun(_, {error, _}=Err) ->
                Err;
           (#alpaca_fun_version{args=Args, body=Body}, {Types, Env}) ->
                BindingF = fun(Arg, {Typs, E, VN}) ->
                                   {AT, _, NE, VN2} = add_bindings(Arg, E, Lvl, VN),
                                   {[AT|Typs], NE, VN2}
                           end,

                {RevTyps, Env2, _} = lists:foldl(BindingF, {[], Env, 0}, Args),
                JustTypes = lists:reverse(RevTyps),
                RecursiveType = {t_arrow, JustTypes, new_cell(t_rec)},
                EnvWithLetRec = update_binding(N, RecursiveType, Env2),

                case typ_of(EnvWithLetRec, Lvl, Body) of
                    {error, _} = Err ->
                        Err;
                    {T, NextVar} ->
                        case unwrap(T) of
                            {t_receiver, Recv, Res} ->
                                TRec = {t_receiver, new_cell(Recv), new_cell(Res)},
                                {t_receiver, Recv2, Res2} =
                                    collapse_receivers(TRec, Env2, Lvl),
                                X = {t_receiver, Recv2,
                                      {t_arrow, JustTypes, Res2}},
                                {[X|Types], update_counter(NextVar, Env2)};
                            _ ->
                                %% Nullary funs are really values - for type
                                %% checking we're only interested in their
                                %% return value
                                case JustTypes of
                                    [] -> {[T|Types], update_counter(NextVar, Env2)};
                                    _  -> {[{t_arrow, JustTypes, T}|Types],
                                          update_counter(NextVar, Env2)}
                                end
                        end
                end
        end,
    case lists:foldl(F, {[], EnvIn}, Vs) of
        {error, _}=Err ->
            Err;
        {RevVersions, Env2} ->
            [H|TypedVersions] = lists:reverse(RevVersions),
            Unified = lists:foldl(
                        fun(_, {error, _}=Err) ->
                                Err;
                           (T1, T2) ->
                                case unify(T1, T2, Env2, L) of
                                    {error, _}=Err -> Err;
                                    ok -> T1
                                end
                        end,
                        H,
                        TypedVersions),
            case Unified of
                {error, _}=Err -> Err;
                Typ -> {Typ, Env2#env.next_var}
            end
    end;

%% A function binding inside a function:
typ_of(Env, Lvl, #alpaca_binding{
                    name={'Symbol', _}=Sym,
                    bound_expr=#alpaca_fun{}=E,
                    signature=Sig,
                    body=E2}) ->
    N = alpaca_ast:symbol_name(Sym),
    {TypE, NextVar} = typ_of(Env, Lvl, E#alpaca_fun{name=N}),
    Env2 = update_counter(NextVar, Env),
    case E2 of
        undefined ->
            %% If we have a type signature and we can unify it with the given
            %% binding we have typed, replace our inferred type with the sig
            case Sig of
                #alpaca_type_signature{type=TS, line=Line, vars=Vs} -> 
                    %% Type signatures may need to fully instantiated
                    Types = Env#env.current_types,

                    VarFolder = fun({type_var, _, VN}, {Vars, E_}) ->
                                        {TVar, E3} = new_var(0, E_),
                                        {[{VN, TVar}|Vars], E3};
                                   ({{type_var, _, VN}, Expr}, {Vars, E_}) ->
                                        %% copy_cell/1 should put every nested member properly
                                        %% into its own reference cell:
                                        {Celled, _} = copy_cell(Expr, maps:new()),
                                        {[{VN, Celled}|Vars], E_}
                                end,
                    {Vars2, Env3} = case Vs of
                        undefined -> {[], Env2};
                        _ -> lists:foldl(VarFolder, {[], Env2}, Vs)
                    end,

                    try inst_constructor_arg(TS, Vars2, Types, Env3) of
                        {_, ArgCons} -> 
                            case unify(TypE, ArgCons, Env3, Line) of
                                ok -> {unwrap_cell(ArgCons), NextVar};
                                Err -> Err
                            end
                        catch
                            throw:{error, {unknown_type_var, BadVar}} ->
                            {error, {unknown_type_var, module_name(Env), Line, BadVar}}
                    end; 
                _ -> {TypE, NextVar}
             end;
        _ ->
            typ_of(update_binding(N, gen(Lvl, TypE), Env2), Lvl+1, E2)
    end;

%% A var binding inside a function:
typ_of(Env, Lvl, #alpaca_binding{name={'Symbol', _}=Sym, bound_expr=E1, body=E2}) ->
    N = alpaca_ast:symbol_name(Sym),
    case typ_of(Env, Lvl, E1) of
        {error, _}=Err ->
            Err;
        {TypE, NextVar} ->
            case E2 of
                undefined ->
                    {TypE, NextVar};
                _ ->
                    Gen = gen(Lvl, TypE),
                    Env2 = update_counter(NextVar, Env),
                    typ_of(update_binding(N, Gen, Env2), Lvl+1, E2)
            end
    end.

typ_ffi_args(_Env, _Lvl, {nil, _}) -> ok;
typ_ffi_args(Env, Lvl, #alpaca_cons{head=H, tail=T}) ->
    case typ_of(Env, Lvl, H) of
        {error, _}=Err -> Err;
        _Ok -> typ_ffi_args(Env, Lvl, T)
    end.

typ_ffi_clauses(#env{next_var=NV}=Env, Lvl,
                #alpaca_ffi{clauses=Cs, module={_, L, _}}) ->
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
    end.

type_bin_segments(#env{next_var=NV}, _Lvl, []) ->
    {ok, NV};
type_bin_segments(
  Env,
  Level,
  [#alpaca_bits{value=V, type=T, line=L}|Rem])
  when T == int; T == float; T == binary; T == utf8; T == latin1 ->
    VTyp = typ_of(Env, Level, V),
    map_typ_of(Env, VTyp,
               fun(Env2, BitsTyp) ->
                       U = unify(BitsTyp, bin_type_to_type(T), Env2, L),
                       map_err(U, fun(_) -> type_bin_segments(Env2, Level, Rem) end)
               end).

bin_type_to_type(int) -> new_cell(t_int);
bin_type_to_type(float) -> new_cell(t_float);
bin_type_to_type(utf8) -> new_cell(t_string);
bin_type_to_type(binary) -> new_cell(t_binary).

%% 2016-07-24 trying this "map" function out instead of littering
%% code with yet more case statements to check errors from typ_of.
map_typ_of(Env, Res, NextStep) ->
    map_err(Res, fun({Typ, NV}) ->
                         Env2 = update_counter(NV, Env),
                         NextStep(Env2, Typ)
                 end).

map_err({error, _}=Err, _NextStep) -> Err;
map_err(Ok, NextStep) -> NextStep(Ok).

type_map(Env, Lvl, #alpaca_map{pairs=[]}) ->
    {KeyVar, Env2} = new_var(Lvl, Env),
    {ValVar, #env{next_var=NV}} = new_var(Lvl, Env2),
    {new_cell({t_map, KeyVar, ValVar}), NV};
type_map(Env, Lvl, #alpaca_map{pairs=Pairs}) ->
    {MapType, NV} = type_map(Env, Lvl, #alpaca_map{}),
    Env2 = update_counter(NV, Env),
    case unify_map_pairs(Env2, Lvl, Pairs, MapType) of
        {error, _}=Err -> Err;
        {Type, #env{next_var=NV2}} -> {Type, NV2}
    end.
unify_map_pairs(Env, _, [], {cell, _}=C) ->
    {C, Env};
unify_map_pairs(Env, _, [], T) ->
    {new_cell(T), Env};
unify_map_pairs(Env, Lvl, [#alpaca_map_pair{line=L, key=KE, val=VE}|Rem], T) ->
    {t_map, K, V} = unwrap_cell(T),
    case typ_list([KE, VE], Lvl, Env, []) of
        {error, _}=Err -> Err;
        {[KT, VT], NV} ->
            Env2 = update_counter(NV, Env),
            case unify(K, KT, Env2, L) of
                ok -> case unify(V, VT, Env2, L) of
                          ok -> unify_map_pairs(Env2, Lvl, Rem, T);
                          {error, _}=Err -> Err
                      end;
                {error, _}=Err -> Err
            end
    end.

%%% This was pulled out of typing match expressions since the exact same clause
%%% type unification has to occur in match and receive expressions.
unify_clauses(Env, Lvl, Cs) ->
    ClauseFolder =
        fun(_, {error, _}=Err) -> Err;
           (C, {Clauses, EnvAcc}) ->
                case typ_of(EnvAcc, Lvl, C) of
                    {error, _}=Err -> Err;
                    {TypC, NV} ->
                        #alpaca_clause{line=Line} = C,
                        {[{Line, TypC}|Clauses], update_counter(NV, EnvAcc)}
                end
        end,
    case lists:foldl(ClauseFolder, {[], Env}, Cs) of
        {error, _}=Err -> Err;
        {TypedCs, #env{next_var=NextVar2}} ->
            UnifyFolder =
                fun(_, {error, _}=Err) -> Err;
                   ({Line, {t_clause, PA, _, RA}}, Acc) ->
                        case Acc of
                            {t_clause, PB, _, RB} = TypC ->
                                case unify(PA, PB, Env, Line) of
                                    ok ->
                                        %% All record result types must have the
                                        %% exact same fields, hence `true`:
                                        case unify(RA, RB, Env, Line, true) of
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

collapse_receivers({cell, _}=C, Env, Line) ->
    collapse_error(
      collapse_receivers(get_cell(C), Env, Line),
      fun(R) -> set_cell(C, R), C end);
collapse_receivers({link, {cell, _}=C}, Env, Line) ->
    collapse_error(
      collapse_receivers(C, Env, Line),
      fun(Res) -> {link, Res} end);
collapse_receivers({t_receiver, Typ, {cell, _}=C}=Recv, Env, Line) ->
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
        {link, {cell, _}=CC} ->
            collapse_receivers({t_receiver, Typ, CC}, Env, Line);
        _Other ->
            Recv
    end;
collapse_receivers({t_receiver, T, E}, Env, Line) ->
    collapse_receivers({t_receiver, T, new_cell(E)}, Env, Line);
collapse_receivers(E, _, _) ->
    E.

type_receive(Env, Lvl, #alpaca_receive{clauses=Cs, line=Line, timeout_action=TA}) ->
    EnsureCelled = fun({cell, _}=C) -> C;
                      (NC) -> new_cell(NC)
                   end,
    case unify_clauses(Env, Lvl, Cs) of
        {error, _}=Err -> Err;
        {ok, {t_clause, PTyp, _, RTyp}, Env2} ->
            Collapsed = collapse_receivers(RTyp, Env, Line),
            case unwrap(Collapsed) of
                {t_receiver, _, B} ->
                    RC = EnsureCelled(Collapsed),
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
                         {error, _}=Err ->
                             Err;
                         {Typ, NV} ->
                             Env3 = update_counter(NV, Env2),
                             CollapsedC = EnsureCelled(Collapsed),
                             case unify(Typ, CollapsedC, Env3, Line) of
                                 {error, _}=Err ->
                                     Err;
                                 ok ->
                                     {new_cell({t_receiver, PTyp, CollapsedC}),
                                      NV}
                             end
                     end
            end
    end.

%% Get the line number that should be reported by an application AST node.
apply_line(#alpaca_apply{line=L}) ->
    L.

typ_apply(Env, Lvl, TypF, NextVar, Args, Line) ->
    Result =
        case TypF of
            {cell, _} ->
                case get_cell(TypF) of
                    {t_receiver, Recv, _App} ->
                        {App, _} = deep_copy_type(_App, maps:new()),
                        case typ_apply_no_recv(Env, Lvl, App,
                                               NextVar, Args, Line) of
                            {error, _}=Err -> Err;
                            {Typ, NV} ->
                                NewRec = {t_receiver, Recv, Typ},
                                set_cell(TypF, NewRec),
                                {TypF, NV}
                        end;
                    _ ->
                        typ_apply_no_recv(Env, Lvl, TypF, NextVar, Args, Line)
                end;
            {t_receiver, Recv, _App} ->
                %% Ensure that the receive type and body use the same reference
                %% cells for the same type variables:
                {{t_receiver, R2, A2}, _} = deep_copy_type(TypF, maps:new()),
                case typ_apply_no_recv(Env, Lvl, A2, NextVar, Args, Line) of
                    {error, _}=Err -> Err;
                    {Typ, NV} ->
                        case get_cell(Typ) of
                            {t_receiver, _, RetTyp} ->
                                case unify(R2, Recv, Env, Line) of
                                    {error, _}=Err -> Err;
                                    ok ->
                                        NewRec = {t_receiver, R2, RetTyp},
                                        {NewRec, NV}
                                end;
                            _ ->
                                NewRec = {t_receiver, R2, Typ},
                                {NewRec, NV}
                        end
                end;
            _ ->
                {TypF2, _} = deep_copy_type(TypF, maps:new()),
                typ_apply_no_recv(Env, Lvl, TypF2, NextVar, Args, Line)
        end,
    Result.

typ_apply_no_recv(Env, Lvl, TypF, NextVar, Args, Line) ->
    %% we make a deep copy of the function we're unifying
    %% so that the types we apply to the function don't
    %% force every other application to unify with them
    %% where the other callers may be expecting a
    %% polymorphic function.  See Pierce's TAPL, chapter 22.

    %{CopiedTypF, _} = deep_copy_type(TypF, maps:new()),
    %% placeholder:
    CopiedTypF = TypF,

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
        Arity::integer()) -> {ok, alpaca_module(), alpaca_binding()} |
                             {error,
                              {no_module, atom()} |
                              {not_exported, string(), integer()} |
                              {not_found, atom(), string, integer()}} .
extract_fun(Env, ModuleName, FunName, Arity) ->
    case [M || M <- Env#env.modules, M#alpaca_module.name =:= ModuleName] of
        [] ->
            {error, {no_module, ModuleName}};
        [Module] ->
            Exports = Module#alpaca_module.function_exports,
            case [F || {FN, A} = F <- Exports, FN =:= FunName, A =:= Arity] of
                [_] -> get_fun(Module, FunName, Arity);
                []  -> {error, {not_exported, FunName, Arity}}
            end
    end.

%% Arity-neutral version of extract_fun so that we can get all top-level
%% bindings for a name from a given module.
extract_module_bindings(Env, ModuleName, BindingName) ->
    case [M || M <- Env#env.modules, M#alpaca_module.name =:= ModuleName] of
        [] ->
            {error, {no_module, ModuleName}};
        [Module] ->
            Exports = Module#alpaca_module.function_exports,
            case [F || {N, _A} = F <- Exports, N =:= BindingName] of
                []  ->
                    throw({error, {not_exported, ModuleName, BindingName}});
                Funs ->
                    F = fun({_, A}) ->
                                {ok, _, Fun} = get_fun(Module, BindingName, A),
                                Fun
                        end,
                    {ok, Module, lists:map(F, Funs)}
            end
    end.


-spec get_fun(
        Module::alpaca_module(),
        FunName::string(),
        Arity::integer()) -> {ok, alpaca_module(), alpaca_binding()} |
                             {error, {not_found, atom(), string, integer()}}.
get_fun(Module, FunName, Arity) ->
    case filter_to_fun(Module#alpaca_module.functions, FunName, Arity) of
        not_found    -> {error, {not_found, Module, FunName, Arity}};
        {ok, Fun} -> {ok, Module, Fun}
    end.

get_curryable_funs(Module, FN, MinArity) ->
    filter_to_curryable_funs(Module#alpaca_module.functions, FN, MinArity).

filter_to_fun([], _, _) ->
    not_found;
filter_to_fun([#alpaca_binding{name={'Symbol', #{name := N}}, bound_expr=#alpaca_fun{arity=Arity}}=Fun|_], FN, A)
  when Arity =:= A, N =:= FN ->
    {ok, Fun};
filter_to_fun([#alpaca_binding{name={'Symbol', #{name :=  N}}}=Fun|_], FN, 0) when N =:= FN ->
    {ok, Fun};
filter_to_fun([_F|Rem], FN, Arity) ->
    filter_to_fun(Rem, FN, Arity).

filter_to_curryable_funs(Funs, FN, MinArity) ->
    Pred = fun(#alpaca_binding{name={'Symbol', _}=Sym, bound_expr=#alpaca_fun{arity=Arity}}) ->
               N = alpaca_ast:symbol_name(Sym),
               case {Arity >= MinArity, N =:= FN} of
                    {true, true} -> true;
                    _ -> false
               end;
              (_) -> false
           end,
    lists:filter(Pred, Funs).

%%% for clauses we need to add bindings to the environment for any symbols
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
        alpaca_expression(),
        env(),
        Lvl::integer(),
        NameNum::integer()) -> {typ(), alpaca_expression(), env(), integer()} |
                               {error, term()}.
add_bindings({'Symbol', _}=S, Env, Lvl, NameNum) ->
    Name = alpaca_ast:symbol_name(S),
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
add_bindings(#alpaca_tuple{values=_}=Tup1, Env, Lvl, NameNum) ->
    {#alpaca_tuple{values=Vs}=Tup2, NN2} = rename_wildcards(Tup1, NameNum),
    {Env2, NN3} = lists:foldl(
                    fun (V, {EnvAcc, NN}) ->
                            {_, _, NewEnv, NewNN} = add_bindings(V, EnvAcc,
                                                                 Lvl, NN),
                            {NewEnv, NewNN}
                    end,
                    {Env, NN2},
                    Vs),
    case typ_of(Env2, Lvl, Tup2) of
        {error, _}=Err -> Err;
        {Typ, NextVar} -> {Typ, Tup2, update_counter(NextVar, Env2), NN3}
    end;

add_bindings(#alpaca_cons{}=Cons, Env, Lvl, NameNum) ->
    {#alpaca_cons{head=H, tail=T}=RenCons, NN2} = rename_wildcards(Cons, NameNum),
    {_, _, Env2, NN3} = add_bindings(H, Env, Lvl, NN2),
    {_, _, Env3, NN4} = add_bindings(T, Env2, Lvl, NN3),
    case typ_of(Env3, Lvl, RenCons) of
        {error, _}=Err -> Err;
        {Typ, NextVar} -> {Typ, RenCons, update_counter(NextVar, Env3), NN4}
    end;

add_bindings(#alpaca_binary{}=Bin, Env, Lvl, NameNum) ->
    {Bin2, NN2} = rename_wildcards(Bin, NameNum),
    F = fun(_, {error, _}=Err) -> Err;
           (#alpaca_bits{value=V}, {E, N}) ->
                case add_bindings(V, E, Lvl, N) of
                    {_, _, E2, N2} -> {E2, N2};
                    {error, _}=Err -> Err
                end
        end,
    case lists:foldl(F, {Env, NN2}, Bin2#alpaca_binary.segments) of
        {error, _}=Err -> Err;
        {Env2, NN3} ->
            T = typ_of(Env2, Lvl, Bin2),
            map_typ_of(Env2, T, fun(Env3, Typ) -> {Typ, Bin2, Env3, NN3} end)
    end;

add_bindings(#alpaca_map{}=M, Env, Lvl, NN) ->
    {M2, _NN2} = rename_wildcards(M, NN),
    Folder = fun(_, {error, _}=Err) -> Err;
                (#alpaca_map_pair{key=K, val=V}, {E, N}) ->
                     case add_bindings(K, E, Lvl, N) of
                         {error, _}=Err -> Err;
                         {_, _, E2, N2} ->
                             case add_bindings(V, E2, Lvl, N2) of
                                 {error, _}=Err -> Err;
                                 {_, _, E3, N3} -> {E3, N3}
                             end
                     end
             end,
    case lists:foldl(Folder, {Env, NN}, M2#alpaca_map.pairs) of
        {error, _}=Err -> Err;
        {Env2, NN3} ->
            case typ_of(Env2, Lvl, M2) of
                {error, _}=Err -> Err;
                {Typ, NV} -> {Typ, M2, update_counter(NV, Env2), NN3}
            end
    end;

add_bindings(#alpaca_record{}=R, Env, Lvl, NameNum) ->
    {R2, _NameNum2} = rename_wildcards(R, NameNum),
    F = fun(#alpaca_record_member{val=V}=_M, {E, N}) ->
                case add_bindings(V, E, Lvl, N) of
                    {error, _}=Err  -> erlang:error(Err);
                    {_, _, E2, N2} -> {E2, N2}
                end
        end,
    case lists:foldl(F, {Env, NameNum}, R2#alpaca_record.members) of
        {Env2, NameNum3} ->
            case typ_of(Env2, Lvl, R2) of
                {error, _}=Err -> erlang:error(Err);
                {Typ, NV} -> {Typ, R2, update_counter(NV, Env2), NameNum3}
            end
    end;

add_bindings(#alpaca_type_apply{arg=none}=T, Env, Lvl, NameNum) ->
    case typ_of(Env, Lvl, T) of
        {error, _}=Err -> Err;
        {Typ, NextVar} -> {Typ, T, update_counter(NextVar, Env), NameNum}
    end;
add_bindings(#alpaca_type_apply{arg=Arg}=T, Env, Lvl, NameNum) ->
    {RenamedArg, NN} = rename_wildcards(Arg, NameNum),
    {_, _, Env2, NextNameNum} = add_bindings(RenamedArg, Env, Lvl, NN),
    TA = T#alpaca_type_apply{arg=RenamedArg},
    case typ_of(Env2, Lvl, TA) of
        {error, _} = Err -> Err;
        {Typ, NextVar} -> {Typ, TA, update_counter(NextVar, Env2), NextNameNum}
    end;

add_bindings(Exp, Env, Lvl, NameNum) ->
    case typ_of(Env, Lvl, Exp) of
        {error, _}=Err -> Err;
        {Typ, NextVar} -> {Typ, Exp, update_counter(NextVar, Env), NameNum}
    end.

%%% Tuples may have multiple instances of the '_' wildcard/"don't care"
%%% symbol.  Each instance needs a unique name for unification purposes
%%% so the individual occurrences of '_' get renamed with numbers in order,
%%% e.g. (1, _, _) would become (1, _0, _1).
rename_wildcards(#alpaca_tuple{values=Vs}=Tup, NameNum) ->
    {Renamed, NN} = rename_wildcards(Vs, NameNum),
    {Tup#alpaca_tuple{values=Renamed}, NN};
rename_wildcards(#alpaca_type_apply{arg=none}=TA, NN) ->
    {TA, NN};
rename_wildcards(#alpaca_type_apply{arg=Arg}=TA, NN) ->
    {Arg2, NN2} = rename_wildcards(Arg, NN),
    {TA#alpaca_type_apply{arg=Arg2}, NN2};
rename_wildcards(#alpaca_cons{head=H, tail=T}, NameNum) ->
    {RenH, N1} = rename_wildcards(H, NameNum),
    {RenT, N2} = rename_wildcards(T, N1),
    {#alpaca_cons{head=RenH, tail=RenT}, N2};
rename_wildcards(#alpaca_binary{segments=Segs}=B, NameNum) ->
    F = fun(S, {Memo, NN}) ->
                {S2, NN2} = rename_wildcards(S, NN),
                {[S2|Memo], NN2}
        end,
    {Segs2, NN2} = lists:foldl(F, {[], NameNum}, Segs),
    {B#alpaca_binary{segments=lists:reverse(Segs2)}, NN2};
rename_wildcards(#alpaca_bits{value=V}=Bits, NameNum) ->
    {V2, NN} = rename_wildcards(V, NameNum),
    {Bits#alpaca_bits{value=V2}, NN};
rename_wildcards(#alpaca_map{pairs=Pairs}=M, NameNum) ->
    Folder = fun(P, {Ps, NN}) ->
                     {P2, NN2} = rename_wildcards(P, NN),
                     {[P2|Ps], NN2}
             end,
    {Pairs2, NN} = lists:foldl(Folder, {[], NameNum}, Pairs),
    {M#alpaca_map{pairs=lists:reverse(Pairs2)}, NN};
rename_wildcards(#alpaca_map_pair{key=K, val=V}=P, NameNum) ->
    {K2, N1} = rename_wildcards(K, NameNum),
    {V2, N2} = rename_wildcards(V, N1),
    {P#alpaca_map_pair{key=K2, val=V2}, N2};

rename_wildcards(#alpaca_record{members=Ms}=R, NameNum) ->
    {Ms2, NameNum2} = rename_wildcards(Ms, NameNum),
    {R#alpaca_record{members=Ms2}, NameNum2};
rename_wildcards(#alpaca_record_member{val=V}=RM, NameNum) ->
    {V2, NameNum2} = rename_wildcards(V, NameNum),
    {RM#alpaca_record_member{val=V2}, NameNum2};

rename_wildcards(Vs, NameNum) when is_list(Vs) ->
    Folder = fun(V, {Acc, N}) ->
                     {NewOther, NewN} = rename_wildcards(V, N),
                     {[NewOther|Acc], NewN}
             end,
    {Renamed, NN} = lists:foldl(Folder, {[], NameNum}, Vs),
    {lists:reverse(Renamed), NN};
rename_wildcards({'_', L}, N) ->
    Name = unicode:characters_to_binary(integer_to_list(N)++"_", utf8),
    Sym = alpaca_ast:symbol(L, Name),
    {Sym, N+1};
rename_wildcards(O, N) ->
    {O, N}.

%%% Tests

-ifdef(TEST).

new_env() ->
    #env{bindings=[celled_binding(Typ)||Typ <- ?all_bifs]}.

%% Top-level typ_of unwraps the reference cells used in unification.
%% This is only preserved for tests at the moment.
-spec typ_of(Env::env(), Exp::alpaca_expression())
            -> {typ(), env()} | {error, term()}.
typ_of(Env, Exp) ->
    case typ_of(Env, 0, Exp) of
        {error, _} = E -> E;
        {Typ, NewVar} -> {unwrap(Typ), update_counter(NewVar, Env)}
    end.

%% Check the type of an expression from the "top-level"
%% of 0 with a new environment.
top_typ_of(Code) ->
    Tokens = alpaca_scanner:scan(Code),
    {ok, E} = alpaca_ast_gen:parse(Tokens),
    typ_of(new_env(), E).

%% Check the type of the expression in code from the "top-level" with a
%% new environment that contains the provided ADTs.
top_typ_with_types(Code, ADTs) ->
    {ok, E} = alpaca_ast_gen:parse(alpaca_scanner:scan(Code)),
    Env = new_env(),
    typ_of(Env#env{current_types=ADTs,
                   type_constructors=constructors(ADTs)},
           E).

%% There are a number of expected "unbound" variables here.  I think this
%% is due to the deallocation problem as described in the first post
%% referenced at the top.
typ_of_test_() ->
    [?_assertMatch({{t_arrow, [t_int], t_int}, _},
                   top_typ_of("let double x = x + x"))
    , ?_assertMatch({{t_arrow, [{t_arrow, [A], B}, A], B}, _},
                    top_typ_of("let apply f x = f x"))
    , ?_assertMatch({{t_arrow, [t_int], t_int}, _},
                    top_typ_of("let doubler x = let double y = y + y in double x"))
    ].

infix_arrow_types_test_() ->
    [?_assertMatch({{t_arrow, [t_int], t_int}, _},
                   top_typ_of("let (<*>) x = x + x"))
    , ?_assertMatch({{t_arrow, [A, {t_arrow, [A], B}], B}, _},
                    top_typ_of("let (|>) x f = f x"))
    ].

simple_polymorphic_let_test() ->
    Code =
        "let double_app my_int ="
        "let two_times f x = f (f x) in "
        "let int_double i = i + i in "
        "two_times int_double my_int",
    ?assertMatch({{t_arrow, [t_int], t_int}, _}, top_typ_of(Code)).

polymorphic_let_test() ->
    Code =
        "let double_application my_int my_float = "
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
                     #alpaca_clause{pattern=alpaca_ast:int(1, 1),
                                    result={atom, 1, true}})),
     ?_assertMatch({{t_clause, {unbound, t0, 0}, none, t_atom}, _},
                   typ_of(
                     new_env(),
                     #alpaca_clause{
                        pattern=alpaca_ast:symbol(1, <<"x">>),
                        result={atom, 1, true}})),
     ?_assertMatch({{t_clause, t_int, none, t_int}, _},
                   typ_of(
                     new_env(),
                     #alpaca_clause{
                        pattern=alpaca_ast:symbol(1, <<"x">>),
                        result=#alpaca_apply{
                                  expr={bif, '+', 1, erlang, '+'},
                                  args=[alpaca_ast:symbol(1, <<"x">>),
                                        alpaca_ast:int(1, 2)]}}))
    ].

match_test_() ->
    [?_assertMatch({{t_arrow, [t_int], t_int}, _},
                   top_typ_of("let f x = match x with\n  i -> i + 2")),
     ?_assertMatch({error, {cannot_unify, _, _, _, _}},
                   top_typ_of(
                     "let f x = match x with\n"
                     "  i -> i + 1\n"
                     "| :atom -> 2")),
     ?_assertMatch({{t_arrow, [t_int], t_atom}, _},
                   top_typ_of(
                     "let f x = match x + 1 with\n"
                     "  1 -> :x_was_zero\n"
                     "| 2 -> :x_was_one\n"
                     "| _ -> :x_was_more_than_one"))
    ].

%% Testing that type errors are reported for the appropriate line when
%% clauses are unified by match or receive.
pattern_match_error_line_test_() ->
    [?_assertMatch({error, {cannot_unify, _, 3, t_float, t_int}},
                   top_typ_of(
                     "let f x = match x with\n"
                     "    i, is_integer i -> :int\n"
                     "  | f, is_float f -> :float")),
     ?_assertMatch({error, {cannot_unify, _, 4, t_float, t_int}},
                   top_typ_of(
                     "let f () = receive with\n"
                     "    0 -> :zero\n"
                     "  | 1 -> :one\n"
                     "  | 2.0 -> :two\n"
                     "  | 3 -> :three\n")),
     ?_assertMatch({error, {cannot_unify, _, 3, t_string, t_atom}},
                   top_typ_of(
                     "let f x = match x with\n"
                     "    0 -> :zero\n"
                     "  | i -> \"not zero\""))
    ].

tuple_test_() ->
    [?_assertMatch({{t_arrow,
                     [{t_tuple, [t_int, t_float]}],
                     {t_tuple, [t_float, t_int]}}, _},
                   top_typ_of(
                     "let f tuple = match tuple with\n"
                     " (i, f) -> (f +. 1.0, i + 1)")),
     ?_assertMatch({{t_arrow, [t_int], {t_tuple, [t_int, t_atom]}}, _},
                   top_typ_of("let f i = (i + 2, :plus_two)")),
     ?_assertMatch({error, _},
                   top_typ_of(
                     "let f x = match x with\n"
                     "  i -> i + 1\n"
                     "| (_, y) -> y + 1\n")),
     ?_assertMatch({{t_arrow, [{t_tuple,
                                [{unbound, _A, _},
                                 {unbound, _B, _},
                                 {t_tuple,
                                  [t_int, t_int]}]}],
                     {t_tuple, [t_int, t_int]}}, _},
                   top_typ_of(
                     "let f x = match x with\n"
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
                   top_typ_of("let f x y = x :: y")),
     ?_assertMatch({{t_arrow, [{t_list, t_int}], t_int}, _},
                   top_typ_of(
                     "let f l = match l with\n"
                     " h :: t -> h + 1")),
     %% Ensure that a '_' in a list nested in a tuple is renamed properly
     %% so that one does NOT get unified with the other when they're
     %% potentially different types:
     ?_assertMatch({{t_arrow,
                     [{t_tuple, [{t_list, t_int}, {unbound, _, _}, t_float]}],
                     {t_tuple, [t_int, t_float]}}, _},
                   top_typ_of(
                     "let f list_in_tuple =\n"
                     "  match list_in_tuple with\n"
                     "   (h :: 1 :: _ :: t, _, f) -> (h, f +. 3.0)")),
     ?_assertMatch({error, {cannot_unify, undefined, 3, t_float, t_int}},
                   top_typ_of(
                     "let f should_fail x =\n"
                     "let l = 1 :: 2 :: 3 :: [] in\n"
                     "match l with\n"
                     " a :: b :: _ -> a +. b"))
    ].

binary_test_() ->
    [?_assertMatch({t_binary, _},
                   top_typ_of("<<1>>")),
     ?_assertMatch({{t_arrow, [t_binary], t_binary}, _},
                   top_typ_of(
                     "let f x = match x with "
                     "<<1: size=8, 2: size=8, rest: type=binary>> -> rest")),
     ?_assertMatch({error, {cannot_unify, _, 1, t_float, t_int}},
                   top_typ_of("let f () = let x = 1.0 in <<x: type=int>>")),
     ?_assertMatch({{t_arrow, [t_binary], t_string}, _},
                   top_typ_of(
                     "let drop_hello bin = "
                     "  match bin with"
                     "    <<\"hello\": type=utf8, rest: type=utf8>> -> rest"))
    ].

map_test_() ->
    [?_assertMatch({{t_map, t_atom, t_int}, _},
                   top_typ_of("#{:one => 1}")),
     ?_assertMatch({{t_map, t_atom, t_int}, _},
                   top_typ_of("#{:one => 1, :two => 2}")),
     ?_assertMatch({error, {cannot_unify, _, 2, t_atom, t_string}},
                   top_typ_of(
                     "#{:one => 1,\n"
                     "  \"two\" => 2}")),
     ?_assertMatch({{t_arrow, [{t_map, t_atom, t_int}], t_string}, _},
                   top_typ_of(
                     "let f x = match x with\n"
                     "    #{:one => i}, is_integer i -> \"has one\"\n"
                     "  | _ -> \"doesn't have one\"")),
     ?_assertMatch({{t_map, t_atom, t_int}, _},
                   top_typ_of("#{:a => 1 | #{:b => 2}}")),
     ?_assertMatch({error, {cannot_unify, undefined, 1, t_atom, t_string}},
                   top_typ_of("#{:a => 1 | #{\"b\" => 2}}"))
    ].

module_typing_test() ->
    Code =
        "module typing_test\n\n"
        "export add/2\n\n"
        "let add x y = x + y\n\n"
        "let head l = match l with\n"
        "  h :: t -> h",
    [M] = make_modules([Code]),
    ?assertMatch({ok, #alpaca_module{
                         functions=[
                                    #alpaca_binding{
                                       name={'Symbol',
                                             #{line := 5, name := <<"add">>}},
                                       type={t_arrow,
                                             [t_int, t_int],
                                             t_int}},
                                    #alpaca_binding{
                                       name={'Symbol',
                                             #{line := 7, name := <<"head">>}},
                                       type={t_arrow,
                                             [{t_list, {unbound, A, _}}],
                                             {unbound, A, _}}}
                                   ]}},
                 type_module(M, new_env())).

module_with_forward_reference_test() ->
    Code =
        "module forward_ref\n\n"
        "export add/2\n\n"
        "let add x y = adder x y\n\n"
        "let adder x y = x + y",

    [M] = make_modules([Code]),
    Env = new_env(),
    ?assertMatch(
       {ok, #alpaca_module{
               functions=[
                          #alpaca_binding{
                             name={'Symbol', #{line := 5, name := <<"add">>}},
                             type={t_arrow, [t_int, t_int], t_int}},
                          #alpaca_binding{
                             name={'Symbol', #{line := 7, name := <<"adder">>}},
                             type={t_arrow, [t_int, t_int], t_int}}]}},
       type_module(M, Env#env{current_module=M, modules=[M]})).

simple_inter_module_test() ->
    Mod1 =
        "module inter_module_one\n\n"
        "let add x y = inter_module_two.adder x y",
    Mod2 =
        "module inter_module_two\n\n"
        "export adder/2\n\n"
        "let adder x y = x + y",

    [M1, M2] = make_modules([Mod1, Mod2]),

    E = new_env(),
    Env = E#env{modules=[M1, M2]},

    ?assertMatch(
       {ok, #alpaca_module{
               function_exports=[],
               functions=[
                          #alpaca_binding{
                             name={'Symbol', #{line := 3, name := <<"add">>}},
                             type={t_arrow, [t_int, t_int], t_int}}]}},
       type_module(M1, Env)).

bidirectional_module_fail_test() ->
    Mod1 =
        "module inter_module_one\n\n"
        "export add/2\n\n"
        "let add x y = inter_module_two.adder x y",
    Mod2 =
        "module inter_module_two\n\n"
        "export adder/2, failing_fun/1\n\n"
        "let adder x y = x + y\n\n"
        "let failing_fun x = inter_module_one.add x x",

    [M1, M2] = make_modules([Mod1, Mod2]),
    E = new_env(),
    Env = E#env{modules=[M1, M2]},
    ?assertMatch({error, {bidirectional_module_ref,
                          inter_module_two,
                          inter_module_one}},
                 type_module(M2, Env)).


recursive_fun_test_() ->
    [?_assertMatch({{t_arrow, [t_int], t_rec}, _},
                   top_typ_of(
                     "let f x =\n"
                     "let y = x + 1 in\n"
                     "f y")),
     ?_assertMatch({{t_arrow, [t_int], t_atom}, _},
                   top_typ_of(
                     "let f x = match x with\n"
                     "  0 -> :zero\n"
                     "| x -> f (x - 1)")),
     ?_assertMatch({error, {cannot_unify, undefined, 3, t_int, t_atom}},
                   top_typ_of(
                     "let f x = match x with\n"
                     "  0 -> :zero\n"
                     "| 1 -> 1\n"
                     "| y -> y - 1\n")),
     ?_assertMatch(
        {{t_arrow, [{t_list, {unbound, A, _}},
                    {t_arrow, [{unbound, A, _}], {unbound, B, _}}],
          {t_list, {unbound, B, _}}}, _}
        when A =/= B,
             top_typ_of(
               "let my_map l f = match l with\n"
               "  [] -> []\n"
               "| h :: t -> (f h) :: (my_map t f)"))
    ].

infinite_mutual_recursion_test() ->
    Code =
        "module mutual_rec_test\n\n"
        "let a x = b x\n\n"
        "let b x = let y = x + 1 in a y",

    [M] = make_modules([Code]),
    E = new_env(),
    ?assertMatch({ok, #alpaca_module{
                         name=mutual_rec_test,
                         functions=[
                                    #alpaca_binding{
                                       name={'Symbol',
                                             #{line := 3, name := <<"a">>}},
                                       type={t_arrow, [t_int], t_rec}},
                                    #alpaca_binding{
                                       name={'Symbol',
                                             #{line := 5, name := <<"b">>}},
                                       type={t_arrow, [t_int], t_rec}}]}},
                 type_module(M, E)).

terminating_mutual_recursion_test() ->
    Code =
        "module terminating_mutual_rec_test\n\n"
        "let a x = let y = x + 1 in b y\n\n"
        "let b x = match x with\n"
        "  10 -> :ten\n"
        "| y -> a y",
    [M] = make_modules([Code]),
    E = new_env(),
    ?assertMatch({ok, #alpaca_module{
                         name=terminating_mutual_rec_test,
                         functions=[
                                    #alpaca_binding{
                                       name={'Symbol',
                                             #{line := 3, name := <<"a">>}},
                                       type={t_arrow, [t_int], t_atom}},
                                    #alpaca_binding{
                                       name={'Symbol',
                                             #{line := 5, name := <<"b">>}},
                                       type={t_arrow, [t_int], t_atom}}]}},
                 type_module(M, E)).

ffi_test_() ->
    [?_assertMatch({t_int, _},
                   top_typ_of(
                     "beam :io :format [\"One is ~w~n\", [1]] with\n"
                     " _ -> 1")),
     ?_assertMatch({error, {cannot_unify, undefined, 1, t_atom, t_int}},
                   top_typ_of(
                     "beam :a :b [1] with\n"
                     "  (:ok, x) -> 1\n"
                     "| (:error, x) -> :error")),
     ?_assertMatch({{t_arrow, [{unbound, _, _}], t_atom}, _},
                   top_typ_of(
                     "let f x = beam :a :b [x] with\n"
                     "  1 -> :one\n"
                     "| _ -> :not_one")),
     ?_assertMatch({error,{bad_variable_name, undefined, 1, <<"x">>}},
                   top_typ_of(
                     "let f () = beam :a :b [x] with\n"
                     "  1 -> :one\n"
                     "| _ -> :not_one"))
    ].

equality_test_() ->
    [?_assertMatch({t_bool, _}, top_typ_of("1 == 2")),
     ?_assertMatch({{t_arrow, [t_int], t_bool}, _},
                   top_typ_of("let f x = 1 == x")),
     ?_assertMatch({error, {cannot_unify, _, _, _, _}}, top_typ_of("1.0 == 1")),
     ?_assertMatch({{t_arrow, [t_int], t_atom}, _},
                   top_typ_of(
                     "let f x = match x with\n"
                     " a, a == 0 -> :zero\n"
                     "|b -> :not_zero")),
     ?_assertMatch({error, {cannot_unify, _, _, t_float, t_int}},
                   top_typ_of(
                     "let f x = match x with\n"
                     "  a -> a + 1\n"
                     "| a, a == 1.0 -> 1"))
    ].

type_guard_test_() ->
    [
     %% In a normal match without union types the is_integer guard should
     %% coerce all of the patterns to t_int:
     ?_assertMatch({{t_arrow, [t_int], t_int}, _},
                   top_typ_of(
                     "let f x = match x with\n"
                     "   i, is_integer i -> i\n"
                     " | _ -> 0")),
     %% Calls to Erlang should use a type checking guard to coerce the
     %% type in the pattern for use in the resulting expression:
     ?_assertMatch({t_int, _},
                   top_typ_of(
                     "beam :a :b [5] with\n"
                     "   :one -> 1\n"
                     " | i, i == 2.0 -> 2\n"
                     " | i, is_integer i -> i\n")),
     %% Two results with different types as determined by their guards
     %% should result in a type error:
     ?_assertMatch({error, {cannot_unify, _, _, t_int, t_float}},
                   top_typ_of(
                     "beam :a :b [2] with\n"
                     "   i, i == 1.0 -> i\n"
                     " | i, is_integer i -> i")),
     %% Guards should work with items from inside tuples:
     ?_assertMatch(
        {{t_arrow, [{t_tuple, [t_atom, {unbound, _, _}]}], t_atom}, _},
        top_typ_of(
          "let f x = match x with\n"
          "   (msg, _), msg == :error -> :error\n"
          " | (msg, _) -> :ok"))
    , ?_assertMatch(
         {{t_pid, _}, _},
         top_typ_of("beam :erlang :self [] with p, is_pid p -> p"))
    ].

%%% ### ADT Tests
%%%
%%%
%%% Tests for ADTs that are simply unions of existing types:
union_adt_test_() ->
    [?_assertMatch({error, {cannot_unify, _, 1, t_int, t_atom}},
                   top_typ_with_types(
                     "let f x = match x with "
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
                     "let f x = match x with "
                     "  0 -> :zero"
                     "| i, is_integer i -> i",
                     [#alpaca_type{name={type_name, 1, "t"},
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
                     "let f x = match x with "
                     "   0 -> :zero"
                     "| (i, 0) -> :adt",
                     [#alpaca_type{name={type_name, 1, "t"},
                                 vars=[{type_var, 1, "x"}],
                                 members=[#alpaca_type_tuple{
                                             members=[{type_var, 1, "x"},
                                                      t_int]},
                                          t_int]}])),
     ?_assertMatch({{t_arrow,
                     [#adt{name="t", vars=[{"x", {unbound, t1, 0}}]}],
                     t_atom},
                    _},
                   top_typ_with_types(
                     "let f x = match x with "
                     "   0 -> :zero"
                     "| (i, 0) -> :adt",
                     [#alpaca_type{name={type_name, 1, "t"},
                                 vars=[{type_var, 1, "x"}],
                                 members=[t_int,
                                          #alpaca_type_tuple{
                                             members=[{type_var, 1, "x"},
                                                      t_int]}]}])),
     %% A recursive type with a bad variable:
     ?_assertMatch(
        {error, {bad_variable, 1, "y"}},
        top_typ_with_types(
          "let f x = match x with "
          " 0 -> :zero"
          "| (i, 0) -> :adt"
          "| (0, (i, 0)) -> :nested",
          [#alpaca_type{name={type_name, 1, "t"},
                      vars=[{type_var, 1, "x"}],
                      members=[t_int,
                               #alpaca_type_tuple{
                                  members=[{type_var, 1, "x"},
                                           t_int]},
                               #alpaca_type_tuple{
                                  members=[t_int,
                                           #alpaca_type{
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
                     "let f x y ="
                     "  let a = match x with"
                     "  (0.0, 0) -> :zero "
                     "| (0.0, 0, :atom) -> :zero_atom in "
                     "  let b = match y with"
                     "  (1, 1) -> :int_one"
                     "| (1, 1, :atom) -> :one_atom in "
                     "(a, b)",
                     [#alpaca_type{name={type_name, 1, "t"},
                                 vars=[{type_var, 1, "x"}],
                                 members=[#alpaca_type_tuple{
                                             members=[{type_var, 1, "x"},
                                                      t_int]},
                                          #alpaca_type_tuple{
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
                     "let f x = match x with "
                     "i, is_integer i -> :is_int"
                     "| A i -> :is_a",
                     [#alpaca_type{name={type_name, 1, "t"},
                                 vars=[{type_var, 1, "x"}],
                                 members=[t_int,
                                          #alpaca_constructor{
                                             name=#type_constructor{line=1, name="A"},
                                             arg={type_var, 1, "x"}}]}])),
     ?_assertMatch(
        {{t_arrow,
          [t_int],
          #adt{name="even_odd", vars=[]}},
         _},
        top_typ_with_types(
          "let f x = match x % 2 with "
          "  0 -> Even x"
          "| 1 -> Odd x",
          [#alpaca_type{name={type_name, 1, "even_odd"},
                      vars=[],
                      members=[#alpaca_constructor{
                                  name=#type_constructor{line=1, name="Even"},
                                  arg=t_int},
                               #alpaca_constructor{
                                  name=#type_constructor{line=1, name="Odd"},
                                  arg=t_int}]}])),
     ?_assertMatch(
        {{t_arrow,
          [#adt{name="json_subset", vars=[]}],
          t_atom},
         _},
        top_typ_with_types(
          "let f x = match x with "
          "  i, is_integer i -> :int"
          "| f, is_float f   -> :float"
          "| (k, v)          -> :keyed_value",
          [#alpaca_type{
              name={type_name, 1, "json_subset"},
              vars=[],
              members=[t_int,
                       t_float,
                       #alpaca_type_tuple{
                          members=[t_string,
                                   #alpaca_type{
                                      name={type_name, 1, "json_subset"}}]}
                      ]}])),
     ?_assertMatch(
        {{t_arrow,
          [{unbound, V, _}],
          #adt{name="my_list", vars=[{"x", {unbound, V, _}}]}},
         _},
        top_typ_with_types(
          "let f x = Cons (x, Cons (x, Nil))",
          [#alpaca_type{
              name={type_name, 1, "my_list"},
              vars=[{type_var, 1, "x"}],
              members=[#alpaca_constructor{
                          name=#type_constructor{line=1, name="Cons"},
                          arg=#alpaca_type_tuple{
                                 members=[{type_var, 1, "x"},
                                          #alpaca_type{
                                             name={type_name, 1, "my_list"},
                                             vars=[{type_var, 1, "x"}]}]}},
                       #alpaca_constructor{
                          name=#type_constructor{line=1, name="Nil"},
                          arg=none}]}])),
     ?_assertMatch(
        {error, {cannot_unify, _, _, t_int, t_float}},
        top_typ_with_types(
          "let f x = Cons (1, Cons (2.0, Nil))",
          [#alpaca_type{
              name={type_name, 1, "my_list"},
              vars=[{type_var, 1, "x"}],
              members=[#alpaca_constructor{
                          name=#type_constructor{line=1, name="Cons"},
                          arg=#alpaca_type_tuple{
                                 members=[{type_var, 1, "x"},
                                          #alpaca_type{
                                             name={type_name, 1, "my_list"},
                                             vars=[{type_var, 1, "x"}]}]}},
                       #alpaca_constructor{
                          name=#type_constructor{line=1, name="Nil"},
                          arg=none}]}])),
     ?_assertMatch(
        {{t_arrow,
          [{unbound, _, _}],
          #adt{name="t", vars=[]}},
         _},
        top_typ_with_types(
          "let f x = Constructor [1]",
          [#alpaca_type{
              name={type_name, 1, "t"},
              vars=[],
              members=[#alpaca_constructor{
                          name=#type_constructor{line=1, name="Constructor"},
                          arg={t_list, t_int}}]}])),
     ?_assertMatch(
        {{t_arrow,
          [{unbound, _, _}],
          #adt{name="t", vars=[]}},
         _},
        top_typ_with_types(
          "let f x = Constructor #{1 => \"one\"}",
          [#alpaca_type{
              name={type_name, 1, "t"},
              vars=[],
              members=[#alpaca_constructor{
                          name=#type_constructor{line=1, name="Constructor"},
                          arg={t_map, t_int, t_string}}]}])),
     ?_assertMatch(
        {{t_arrow,
          [{unbound, _, _}],
          #adt{name="t", vars=[]}},
         _},
        top_typ_with_types(
          "let f x = Constructor 1",
          [#alpaca_type{
              name={type_name, 1, "t"},
              vars=[],
              members=[#alpaca_constructor{
                          name=#type_constructor{line=1, name="Constructor"},
                          arg=#alpaca_type{name={type_name, 1, "union"}}}]},
           #alpaca_type{
              name={type_name, 1, "union"},
              vars=[],
              members=[t_int, t_float]}]))
    ].

type_constructor_with_pid_arg_test() ->
    Code = "module constructor\n\n"
           "type t = Constructor pid int\n\n"
           "let a x = receive with i -> x + i\n\n"
           "let make () = Constructor (spawn a 2)",
     ?assertMatch({ok, _}, module_typ_and_parse(Code)).

type_constructor_with_arrow_arg_test() ->
    Base = "module constructor\n\n"
           "type t = Constructor (fn int int -> bool)\n\n",
    Valid = Base ++
            "let p x y = x > y\n\n"
            "let make () = Constructor p",
     ?assertMatch({ok, _}, module_typ_and_parse(Valid)),

    Invalid = Base ++
              "let p x y = x + y\n\n"
              "let make () = Constructor p",
     ?assertMatch({error,{cannot_unify, constructor, _, t_bool, t_int}},
                  module_typ_and_parse(Invalid)).

type_constructor_with_aliased_arrow_arg_test() ->
    Base = "module constructor\n\n"
           "type binop 'a = fn 'a 'a -> 'a\n"
           "type intbinop = binop int\n"
           "type wrapper = W intbinop\n\n",
    Valid = Base ++ "let f (W b) = b 1 1\n\n",
    ?assertMatch({ok, _}, module_typ_and_parse(Valid)),
    Invalid = Base ++ "let f (W b) = b 1 :atom\n\n",
    ?assertMatch({error, {cannot_unify,constructor,7,
                         #adt{name = <<"intbinop">>,
                              vars=[],
                              members=[#adt{name = <<"binop">>,
                                            vars=[{_, t_int}],
                                            members=[{t_arrow,[t_int,t_int],t_int}]}]},
                          {t_arrow,[t_int,t_atom],t_rec}}},
                  module_typ_and_parse(Invalid)).

type_constructor_multi_level_type_alias_arg_test() ->
    Code =
        "module constructor\n\n"
        "type twotuplelist 'a 'b = list ('a, 'b)\n\n"
        "type proplist 'v = twotuplelist atom 'v\n\n"
        "type checklist = proplist bool\n\n"
        "type constructor = Constructor checklist\n\n",
    Valid = Code ++ "let make () = Constructor [(:test_passed, true)]",
    BadKey = Code ++ "let make () = Constructor [(1, true)]",
    BadVal = Code ++ "let make () = Constructor [(:test_passed, 1)]",
    BadArg = Code ++ "let make () = Constructor 1",
    ?assertMatch({ok, #alpaca_module{}}, module_typ_and_parse(Valid)),
    ?assertMatch({error, {cannot_unify, _, _, _, _}},
                 module_typ_and_parse(BadKey)),
    ?assertMatch({error, {cannot_unify, _, _, _, _}},
                 module_typ_and_parse(BadVal)),
    ?assertMatch({error, {cannot_unify, _, _, _, _}},
                 module_typ_and_parse(BadArg)).

type_var_replacement_test_() ->
    [fun() ->
             Code =
                 "module nested\n\n"
                 "type option 'a = Some 'a | None\n\n"
                 "type either 'a = Left 'a | Right option int\n\n"
                 "let foo x =\n"
                 "  match x with\n"
                 "    Right Some a -> a\n\n"
                 "let tester () = foo Right Some 1",
             ?assertMatch(
                {ok, #alpaca_module{
                        functions=[#alpaca_binding{},
                                   #alpaca_binding{
                                      type={t_arrow, [t_unit], t_int}}]}},
                module_typ_and_parse(Code))
     end
    ,fun() ->
             Code =
                 "module nested\n\n"
                 "type option 'a = Some 'a | None\n\n"
                 "type either 'a = Left 'a | Right option 'a\n\n"
                 "let foo x =\n"
                 "  match x with\n"
                 "    Right Some a -> a\n\n"
                 "let tester () = foo Right Some 1",
             ?assertMatch(
                {ok, #alpaca_module{
                        functions=[#alpaca_binding{},
                                   #alpaca_binding{
                                      type={t_arrow, [t_unit], t_int}}]}},
                module_typ_and_parse(Code))
     end
    ].

%%% Type constructors that use underscores in pattern matches to discard actual
%%% values should work, depends on correct recursive renaming.
rename_constructor_wildcard_test() ->
    Code =
        "module module_with_wildcard_constructor_tuples\n\n"
        "type t = int | float | Pair (string, t)\n\n"
        "let a x = match x with\n"
        "i, is_integer i -> :int\n"
        "| f, is_float f -> :float\n"
        "| Pair (_, _) -> :tuple\n"
        "| Pair (_, Pair (_, _)) -> :nested_t"
        "| Pair (_, Pair (_, Pair(_, _))) -> :double_nested_t",
    [M] = make_modules([Code]),
    Env = new_env(),
    Res = type_module(M, Env),
    ?assertMatch(
       {ok, #alpaca_module{
               functions=[#alpaca_binding{
                             name={'Symbol', #{line := 5, name := <<"a">>}},
                             type={t_arrow,
                                   [#adt{
                                       name = <<"t">>,
                                       vars=[],
                                       members=[{t_adt_cons, "Pair"},
                                                t_float,
                                                t_int]}],
                                   t_atom}}]}},
       Res).

module_with_map_in_adt_test() ->
    Code =
        "module module_with_map_in_adt_test\n\n"
        "type t 'v = list 'v | map atom 'v\n\n"
        "let a x = match x with\n"
        "    h :: t -> h"
        "  | #{:key => v} -> v",
    [M] = make_modules([Code]),
    ?assertMatch({ok, _}, type_modules([M])).

module_with_adt_map_error_test() ->
    Code =
        "module module_with_map_in_adt_test\n\n"
        "type t 'v = list 'v | map atom 'v\n\n"
        "let a x = match x with\n"
        "    h :: t, is_string h -> h"
        "  | #{:key => v}, is_chars v -> v",
    [M] = make_modules([Code]),
    Res = type_modules([M]),
    ?assertMatch(
       {error, {cannot_unify, _, _, {t_map, _, _}, {t_list, _}}}, Res).

json_union_type_test() ->
    Code =
        "module json_union_type_test\n\n"
        "type json = int | float | string | bool "
        "          | list json "
        "          | list (string, json)\n\n"
        "let json_to_atom j = match j with "
        "    i, is_integer i -> :int"
        "  | f, is_float f -> :float"
        "  | (_, _) :: _ -> :json_object"
        "  | _ :: _ -> :json_array",
    [M] = make_modules([Code]),
    Env = new_env(),
    Res = type_module(M, Env),
    ?assertMatch(
       {ok,
        #alpaca_module{
           types=[#alpaca_type{
                     module='json_union_type_test',
                     name={type_name, 3, <<"json">>}}],
           functions=[#alpaca_binding{
                         name={'Symbol', #{name := <<"json_to_atom">>}},
                         type={t_arrow,
                               [#adt{name = <<"json">>,
                                     members=[{t_list,
                                               {t_tuple,
                                                [t_string,
                                                 #adt{name = <<"json">>}]}},
                                              {t_list,
                                               #adt{name = <<"json">>}},
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
        "let a x = match x with\n"
        "i, is_integer i -> :int\n"
        "| f, is_float f -> :float\n"
        "| (_, _) -> :tuple"
        "| (_, (_, _)) -> :nested",
    [M] = make_modules([Code]),
    Env = new_env(),
    Res = type_module(M, Env),
    ?assertMatch(
       {ok, #alpaca_module{
               functions=[#alpaca_binding{
                             name={'Symbol', #{line := 5, name := <<"a">>}},
                             type={t_arrow,
                                   [#adt{
                                       name = <<"t">>,
                                       vars=[],
                                       members=[{t_tuple,
                                                 [t_string,
                                                  #adt{name = <<"t">>,
                                                       vars=[],
                                                       members=[]}]},
                                                t_float,
                                                t_int
                                               ]}],
                                   t_atom}}]}},
       Res).

recursive_polymorphic_adt_test() ->
    Code = polymorphic_tree_code() ++
        "\n\nlet succeed () = height (Node (Leaf, 1, (Node (Leaf, 1, Leaf))))",

    [M] = make_modules([Code]),
    Res = type_modules([M]),
    ?assertMatch({ok, _}, Res).

recursive_polymorphic_adt_fails_to_unify_with_base_type_test() ->
    Code = polymorphic_tree_code() ++
        "\n\nlet fail () = height 1",

    [M] = make_modules([Code]),
    Res = type_modules([M]),
    ?assertMatch({error,
                  {cannot_unify,tree,15,
                   #adt{name = <<"tree">>,
                        vars=[{"a",_}],
                        members=[{t_adt_cons,"Node"},{t_adt_cons,"Leaf"}]},
                   t_int}},
                 Res).

polymorphic_tree_code() ->
    "module tree\n\n"
    "type tree 'a = Leaf | Node (tree 'a, 'a, tree 'a)\n\n"
    "let height t =\n"
    "  match t with\n"
    "    Leaf -> 0\n"
    "  | Node (l, _, r) -> 1 + (max (height l) (height r))\n\n"
    "let max a b =\n"
    "  match (a > b) with\n"
    "    true -> a\n"
    "  | false -> b".

builtin_types_as_type_variables_test() ->
    Code =
        "module optlist\n\n"
        "type proplist 'k 'v = list ('k, 'v)\n\n"
        "type optlist 'v = proplist atom 'v",
    [M] = make_modules([Code]),
    Res = type_modules([M]),
    ?assertMatch({ok, _}, Res).

module_matching_lists_test() ->
    Code =
        "module module_matching_lists\n\n"
        "type my_list 'x = Nil | Cons ('x, my_list 'x)\n\n"
        "let a x = match x with "
        "  Nil -> :nil"
        "  | Cons (i, Nil), is_integer i -> :one_item"
        "  | Cons (i, xx) -> :more_than_one",

    [M] = make_modules([Code]),
    Env = new_env(),
    Res = type_module(M, Env),
    ?assertMatch({ok, #alpaca_module{
                         functions=[#alpaca_binding{
                                       name={'Symbol',
                                             #{line := 5, name := <<"a">>}},
                                       type={t_arrow,
                                             [#adt{
                                                 name = <<"my_list">>,
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
        "let a x = match x with "
        "  Nil -> :nil"
        "  | Cons (i, Nil), is_integer i -> :one_integer"
        "  | Cons (i, xx) -> :more_than_one_integer\n\n"

        "let b x = match x with "
        "  Nil -> :nil"
        "  | Cons (f, Nil), is_float f -> :one_float"
        "  | Cons (f, xx) -> :more_than_one_float\n\n"

        "let c () = (Cons (1.0, Nil), Cons(1, Nil))",

    [M] = make_modules([Code]),
    Env = new_env(),
    Res = type_module(M, Env),
    ?assertMatch(
       {ok, #alpaca_module{
               functions=[#alpaca_binding{
                             name={'Symbol', #{line := 5, name := <<"a">>}},
                             type={t_arrow,
                                   [#adt{
                                       name = <<"my_list">>,
                                       vars=[{"x", t_int}]}],
                                   t_atom}},
                          #alpaca_binding{
                             name={'Symbol', #{line := 7, name := <<"b">>}},
                             type={t_arrow,
                                   [#adt{
                                       name = <<"my_list">>,
                                       vars=[{"x", t_float}]}],
                                   t_atom}},
                          #alpaca_binding{
                             name={'Symbol', #{line := 9, name := <<"c">>}},
                             type={t_arrow,
                                   [t_unit],
                                   {t_tuple,
                                    [#adt{
                                        name = <<"my_list">>,
                                        vars=[{"x", t_float}]},
                                     #adt{
                                        name = <<"my_list">>,
                                        vars=[{"x", t_int}]}]}}}]}},
       Res).

type_var_protection_fail_unify_test() ->
    Code =
        "module module_matching_lists\n\n"
        "type my_list 'x = Nil | Cons ('x, my_list 'x)\n\n"
        "let c () = "
        "  let x = Cons (1.0, Nil) in "
        "  Cons (1, x)",

    [M] = make_modules([Code]),

    Res = type_modules([M]),
    ?assertMatch(
       {error, {cannot_unify, module_matching_lists, 5, t_int, t_float}}, Res).

type_error_in_test_test() ->
    Code =
        "module type_error_in_test\n\n"
        "let add x y = x + y\n\n"
        "test \"add floats\" = add 1.0 2.0",
    Res = module_typ_and_parse(Code),
    ?assertEqual(
       {error, {cannot_unify, type_error_in_test, 5, t_int, t_float}}, Res).

%% At the moment we don't care what the type of the test expression is,
%% only that it type checks.
typed_tests_test() ->
    Code =
        "module type_error_in_test\n\n"
        "let add x y = x + y\n\n"
        "test \"add floats\" = add 1 2",
    Res = module_typ_and_parse(Code),
    ?assertMatch({ok, #alpaca_module{
                         tests=[#alpaca_test{name={string, 5, "add floats"}}]}},
                 Res).

polymorphic_list_as_return_value_test_() ->
    [fun() ->
             Code =
                 "module list_tests\n\n"
                 "let is_empty l =\n"
                 "    match l with\n"
                 "        []   -> true\n"
                 "    | _ :: _ -> false\n\n"
                 "let a () = is_empty []\n\n"
                 "let b () = is_empty [:ok]\n\n"
                 "let c () = is_empty [1]",
             Res = module_typ_and_parse(Code),
             ?assertMatch({ok, _}, Res)
     end
    ,fun() ->
             Code =
                 "module poly_list_head\n\n"
                 "let head l =\n"
                 "  match l with\n"
                 "    a :: _ -> a\n\n"
                 "let foo () = head [1, 2]",
             ?assertMatch(
                {ok, #alpaca_module{
                        functions=[#alpaca_binding{},
                                   #alpaca_binding{
                                      type={t_arrow, [t_unit], t_int}}]}},
                module_typ_and_parse(Code))
     end
    ].

polymorphic_adt_as_return_value_test() ->
    Code =
        "module option\n\n"
        "type option 't = Some 't | None\n\n"
        "let is_none opt =\n"
        "    match opt with\n"
        "        None   -> true\n"
        "    |   Some _ -> false\n\n"
        "let a () = is_none None\n\n"
        "let b () = is_none (Some :a)\n\n"
        "let c () = is_none (Some 1)",
    Res = module_typ_and_parse(Code),
    ?assertMatch({ok, _}, Res).

polymorphic_map_as_return_value_test_() ->
    [fun() ->
             Code =
                 "module empty_map\n\n"
                 "let is_empty m =\n"
                 "    match m with\n"
                 "        #{} -> true\n"
                 "        | _ -> false\n\n"
                 "let a () = is_empty #{}\n\n"
                 "let b () = is_empty #{:a => 1}\n\n"
                 "let c () = is_empty #{1 => :a}\n\n",
             Res = module_typ_and_parse(Code),
             ?assertMatch({ok, _}, Res)
     end
     , fun() ->
               Code =
                   "module poly_map\n\n"
                   "let get_a m =\n"
                   "  match m with\n"
                   "    #{:a => a} -> a\n\n"
                   "let foo () = get_a #{:a => 1}",
               ?assertMatch(
                  {ok, #alpaca_module{
                          functions=[#alpaca_binding{
                                       type={t_arrow,
                                             [{t_map, t_atom, {unbound, A, _}}],
                                             {unbound, A, _}}},
                                    #alpaca_binding{
                                       type={t_arrow, [t_unit], t_int}
                                      }]
                         }},
                  module_typ_and_parse(Code))
       end
    ].

polymorphic_tuple_as_return_value_test() ->
    Code =
        "module poly_tuple\n\n"
        "let second t =\n"
        "  match t with\n"
        "    (_, x)  -> x\n\n"
        "let a () = second (1, 2) \n\n"
        "let b () = second (:a, :b)",
    Res = module_typ_and_parse(Code),
    ?assertMatch({ok, _}, Res).

polymorphic_process_as_return_value_test() ->
    Code =
        "module poly_process\n\n"
        "let behaviour state state_f =\n"
        "  receive with\n"
        "    x -> behaviour (state_f state x) state_f \n\n"
        "let a () = let f x y = x + y in spawn behaviour 1 f\n\n"
        "let b () = \n"
        "  let f x y = x +. y in\n"
        "  let p = spawn behaviour 1.0 f in\n"
        "  let u = send :a p in\n"
        "  p",
    Res = module_typ_and_parse(Code),
    ?assertMatch({error, {cannot_unify, poly_process, 12, t_float, t_atom}}, Res).

polymorphic_spawn_test() ->
    FunCode =
        "let behaviour state state_f =\n"
        "  receive with\n"
        "    x -> behaviour (state_f state x) state_f",
    BaseEnv = new_env(),
    {ok, FunExp} = alpaca_ast_gen:parse(alpaca_scanner:scan(FunCode)),
    {FunType, _} = typ_of(BaseEnv, FunExp),
    ?assertMatch({t_receiver,
                  {unbound,t2,0},
                  {t_arrow,
                   [{unbound,t0,0},
                    {t_arrow,
                     [{unbound,t0,0},{unbound,t2,0}],
                     {unbound,t0,0}}],
                   t_rec}},
                 FunType),
    NewBindings = [{<<"behaviour">>, FunType}|BaseEnv#env.bindings],
    NewModule = #alpaca_module{functions=[FunExp#alpaca_binding{type=FunType}]},
    EnvWithFun = BaseEnv#env{bindings=NewBindings, current_module=NewModule},
    SpawnCode = "let f x y = x +. y in spawn behaviour 1.0 f",
    {ok, SpawnExp} = alpaca_ast_gen:parse(alpaca_scanner:scan(SpawnCode)),
    {SpawnType, _} = typ_of(EnvWithFun,  SpawnExp),

    ?assertMatch({t_pid, t_float}, SpawnType).


%%% ### Process Interaction Typing Tests
%%%
%%% Things like receive, send, and spawn.

module_typ_and_parse(Code) ->
    [M] = make_modules([Code]),
    case type_modules([M]) of
        {ok, [M2]} -> {ok, M2};
        Err        -> Err
    end.

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
                 "let a () = receive with "
                 "  i, is_integer i -> :received_int"
                 "| f, is_float f -> :received_float",
             ?assertMatch(
                {ok, #alpaca_module{
                        functions=[#alpaca_binding{
                                      name={'Symbol',
                                            #{line := 5,
                                              name := <<"a">>}},
                                      type={t_receiver,
                                            #adt{name = <<"my_union">>},
                                            {t_arrow,
                                             [t_unit],
                                             t_atom}}
                                     }]}},
                module_typ_and_parse(Code))
     end,
     fun() ->
             Code =
                 "module union_receives\n\n"
                 "let f x = receive with "
                 "    0 -> :ok"
                 "  | i -> g (i + x)\n\n"
                 "let g x = receive with "
                 "  i -> f (i - x)",
             ?assertMatch(
                {ok, #alpaca_module{
                        functions=[#alpaca_binding{
                                      name={'Symbol',
                                            #{line := 3,
                                              name := <<"f">>}},
                                      type={t_receiver,
                                            t_int,
                                            {t_arrow,
                                             [t_int],
                                             t_atom}}},
                                   #alpaca_binding{
                                      name={'Symbol',
                                            #{line := 5,
                                              name := <<"g">>}},
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
                 "let a () = receive with "
                 "    A -> b ()\n\n"
                 "let b () = receive with "
                 "    B -> a () after 5 a()",
             ?assertMatch(
                {ok, #alpaca_module{
                        functions=[#alpaca_binding{
                                      name={'Symbol',
                                            #{line := 5,
                                              name := <<"a">>}},
                                      type={t_receiver,
                                            #adt{name = <<"t">>},
                                            {t_arrow,
                                             [t_unit],
                                             t_rec}}},
                                   #alpaca_binding{
                                      name={'Symbol',
                                            #{line := 7,
                                              name := <<"b">>}},
                                      type={t_receiver,
                                            #adt{name = <<"t">>},
                                            {t_arrow,
                                             [t_unit],
                                             t_rec}}}
                                  ]}},
                module_typ_and_parse(Code))
     end,
     fun() ->
             Code =
                 "module receive_in_let\n\n"
                 "let f x = "
                 "  let y = receive with "
                 "    i -> i "
                 "  in let z = receive with "
                 "    i -> i "
                 "  in x + y + z",
             ?assertMatch(
                {ok, #alpaca_module{
                        functions=[#alpaca_binding{
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
                 "let f x = "
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
                 "let f x = receive with "
                 " i -> f (x + i)\n\n"
                 "let start_f init = spawn f init",
             ?assertMatch({ok, #alpaca_module{
                                  functions=[#alpaca_binding{
                                                name={'Symbol',
                                                      #{line := 5,
                                                        name := <<"f">>}},
                                                type={t_receiver,
                                                      t_int,
                                                      {t_arrow,
                                                       [t_int],
                                                       t_rec}}},
                                             #alpaca_binding{
                                                name={'Symbol',
                                                      #{line := 7,
                                                        name := <<"start_f">>}},
                                                type={t_arrow,
                                                      [t_int],
                                                      {t_pid, t_int}
                                                     }}]}},
                          module_typ_and_parse(Code))
     end
    , fun() ->
              Code =
                  "module spawn_composed_receiver\n\n"
                  "let recv () = receive with "
                  "  i, is_integer i -> i\n\n"
                  "let not_recv () = (recv ()) + 2",
              ?assertMatch(
                 {ok, #alpaca_module{
                         functions=[#alpaca_binding{
                                       name={'Symbol',
                                             #{line := 3,
                                               name := <<"recv">>}},
                                       type={t_receiver,
                                             t_int,
                                             {t_arrow,
                                              [t_unit],
                                              t_int}}},
                                    #alpaca_binding{
                                       name={'Symbol',
                                             #{line := 5,
                                               name := <<"not_recv">>}},
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
                  "let a x = let y = receive with "
                  "    B xx -> b (x + xx)\n"
                  "  | A xx -> xx + x in "
                  "  a (x + y)\n\n"
                  "let b x = receive with "
                  "    A xx -> a (x + xx)\n"
                  "  | B xx -> b (xx + x)\n\n"
                  "let start_a init = spawn a init",
              ?assertMatch(
                 {ok, #alpaca_module{
                         functions=[#alpaca_binding{
                                       name={'Symbol', #{name := <<"a">>}},
                                       type={t_receiver,
                                             #adt{name = <<"t">>},
                                             {t_arrow,
                                              [t_int],
                                              t_rec}}},
                                    #alpaca_binding{
                                       name={'Symbol', #{name := <<"b">>}},
                                       type={t_receiver,
                                             #adt{name = <<"t">>},
                                             {t_arrow,
                                              [t_int],
                                              t_rec}}},
                                    #alpaca_binding{
                                       name={'Symbol', #{name := <<"start_a">>}},
                                       type={t_arrow,
                                             [t_int],
                                             {t_pid, #adt{name = <<"t">>}}}}]}},
                 module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module unify_failure_for_spawn\n\n"
                  "type t = A int\n\n"
                  "type u = B int\n\n"
                  "let a x = let y = receive with "
                  "    B xx -> b (x + xx)\n"
                  "  | A xx -> xx + x in "
                  "  a (x + y)\n\n"
                  "let b x = receive with "
                  "    A xx -> a (x + xx)\n"
                  "  | B xx -> b (xx + x)\n\n"
                  "let start_a init = spawn a [init]",
              ?assertMatch(
                 {error, {cannot_unify, _, _,
                          #adt{name = <<"u">>},
                          #adt{name = <<"t">>}}},
                 module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module non_receiver_pid\n\n"
                  "export f/1, start_f/1\n\n"
                  "let f x = f (x + 1)\n\n"
                  "let start_f () = spawn f 0",
              ?assertMatch(
                 {ok, #alpaca_module{
                         functions=[#alpaca_binding{
                                       name={'Symbol', #{name := <<"f">>}},
                                       type={t_arrow, [t_int], t_rec}},
                                    #alpaca_binding{}]}},
                 module_typ_and_parse(Code))
      end
    ].

send_message_test_() ->
    [fun() ->
             Code =
                 "module send_example_1\n\n"
                 "let f x = receive with "
                 "  i -> f (i + x)\n\n"
                 "let spawn_and_message_f () = "
                 "  let p = spawn f 0 in "
                 "  send 1 p",
             ?assertMatch(
                {ok, #alpaca_module{}},
                module_typ_and_parse(Code))
     end
    , fun() ->
              Code =
                  "module send_to_bad_pid\n\n"
                  "let f x = receive with "
                  "  i -> f (i + x)\n\n"
                  "let spawn_and_message_f () = "
                  "  let p = spawn f 0 in "
                  "  send 1.0 p",
              ?assertMatch(
                 {error, {cannot_unify, _, _, t_int, t_float}},
                 module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module send_to_non_pid\n\n"
                  "let f x = send 1 2",
              ?assertMatch(
                 {error, {cannot_unify, send_to_non_pid, _, t_int, {t_pid, _}}},
                 module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module send_to_non_receiver\n\n"
                  "let f x = f (x+1)\n\n"
                  "let start_f x = "
                  "  let p = spawn f x in "
                  "  send 1 p",
              ?assertMatch(
                 {error, {cannot_unify, _, _, undefined, t_int}},
                 module_typ_and_parse(Code))
      end
    ].

%% Tests for records

record_inference_test_() ->
    [?_assertMatch({#t_record{
                      members=[#t_record_member{name=x, type=t_int},
                               #t_record_member{name=y, type=t_float}],
                      row_var={unbound, _, _}}, _},
                   top_typ_of("{x=1, y=2.0}")),
     fun() ->
             Code =
                 "let f r = match r with\n"
                 "  {x = x1} -> x1 + 1",
             ?assertMatch({{t_arrow,
                            [#t_record{
                                 members=[#t_record_member{
                                             name=x,
                                             type=t_int}],
                                 row_var={unbound, _, _}}],
                            t_int}, _},
                          top_typ_of(Code))
     end,
     fun() ->
             Code =
                 "module record_inference_test_unify\n\n"
                 "let f r = match r with\n"
                 "  {x = x1} -> (x1 * 2, r)\n\n"
                 "let g () = f {x=1, y=2}",
             ?assertMatch({ok,
                           #alpaca_module{
                              functions=[#alpaca_binding{
                                            name={'Symbol', #{name := <<"f">>}},
                                            type={t_arrow,
                                                  [#t_record{
                                                      members=[#t_record_member{
                                                                  name=x,
                                                                  type=t_int}],
                                                      row_var={unbound, A, _}}],
                                                  {t_tuple,
                                                   [t_int,
                                                    #t_record{
                                                       members=[#t_record_member{
                                                                   name=x,
                                                                   type=t_int}],
                                                       row_var={unbound, A, _}}]}}},
                                         #alpaca_binding{
                                            name={'Symbol', #{name := <<"g">>}},
                                            type={t_arrow,
                                                  [t_unit],
                                                  {t_tuple,
                                                   [t_int,
                                                    #t_record{
                                                       members=[#t_record_member{
                                                                   name=x,
                                                                   type=t_int},
                                                                #t_record_member{
                                                                   name=y,
                                                                   type=t_int}],
                                                       row_var={unbound, _B, _}}]}}
                                           }]
                             }},
                          module_typ_and_parse(Code))
     end,
     ?_assertException(error, {missing_record_field, undefined, 1, y},
                   top_typ_of("let f () = "
                              "  let g r = match r with "
                              "    {x=x1, y=y1} -> x1 + y1 in "
                              "  g {x=1}")),
     fun() ->
             Code =
                 "module record_inference_record_adt_test\n\n"
                 "type my_adt 'a = Adt | {x: int, a: 'a}\n\n"
                 "let f r = match r with \n"
                 "    {x=x1, a=a1} -> x1 + a1\n"
                 "  | Adt -> 0",
             ?assertMatch(
                {ok,
                 #alpaca_module{
                    functions=[#alpaca_binding{
                                  type={t_arrow,
                                        [#adt{
                                            name = <<"my_adt">>,
                                            vars=[{"a", t_int}],
                                            members=[#t_record{
                                                        members=[#t_record_member{
                                                                    name=x,
                                                                    type=t_int},
                                                                 #t_record_member{
                                                                    name=a,
                                                                    type=t_int}],
                                                        row_var={unbound, _, _}},
                                                    {t_adt_cons, "Adt"}]
                                                       }],
                                            t_int}}]}},
                    module_typ_and_parse(Code))
     end,
     fun() ->
             %% The following uses a constructor argument only to force
             %% typing to the ADT.
             Code =
                 "module nested_record_adt_test\n\n"
                 "type nested = Nested {fname: string, "
                 "                      lname: string, "
                 "                      address: {street: string,"
                 "                                city: string}}\n\n"
                 "let fname r = match r with\n"
                 "  Nested {address={street=s}}, is_string s ->  s",
             ?assertMatch({ok,
                           #alpaca_module{
                              functions=[#alpaca_binding{
                                            type={t_arrow,
                                                  [#adt{name = <<"nested">>}],
                                                  t_string}}]}},
                          module_typ_and_parse(Code))
     end
    ].

%% In the sample test file record_map_match_order.alp the ordering of maps
%% and records in the definition of a type impacts the unification and thus
%% inference of a function's return type.  This test is to check for multiple
%% orderings and regressions.
%%
%% The root error appears to have been arising because in unify_adt_and_poly
%% one of the target type members was unwrapped from its reference cell.  Since
%% the unification was actually impacting the top level cells, we could re-cell
%% the type and not worry about throwing that away later.
adt_ordering_test_() ->
    [fun() ->
             Code =
                 "module simple_adt_order_1\n\n"
                 "type t 'a = Some 'a | None\n\n"
                 "let f x = match x with\n"
                 "    None -> :none\n"
                 "  | Some a -> :an_a",
             ?assertMatch({ok,
                           #alpaca_module{
                              functions=[#alpaca_binding{
                                            type={t_arrow,
                                                  [#adt{
                                                    vars=[{"a", {unbound, _A, _}}],
                                                      members=[{t_adt_cons, "None"},
                                                               {t_adt_cons, "Some"}]}],
                                                 t_atom}}]}},
                          module_typ_and_parse(Code))
     end
    ,fun() ->
             Code =
                 "module simple_adt_order_2\n\n"
                 "type t 'a = None | Some 'a\n\n"
                 "let f x = match x with\n"
                 "    None -> :none\n"
                 "  | Some a -> :an_a",
             ?assertMatch({ok,
                           #alpaca_module{
                              functions=[#alpaca_binding{
                                            type={t_arrow,
                                                  [#adt{
                                                      vars=[{"a", {unbound, _A, _}}],
                                                      members=[{t_adt_cons, "Some"},
                                                               {t_adt_cons, "None"}]}],
                                                 t_atom}}]}},
                          module_typ_and_parse(Code))
     end
     ,fun() ->
              Code =
                  "module list_and_map_order_1\n\n"
                  "type t 'a = list 'a | map atom 'a\n\n"
                  "let f x = match x with\n"
                  "    a :: _ -> a\n"
                  "  | #{:a => a} -> a\n\n"
                  "let g () = f #{:a => 1, :b => 2}\n\n"
                  "let h () = f [1, 2]",
              ?assertMatch(
                 {ok,
                  #alpaca_module{
                     functions=[#alpaca_binding{
                                   type={t_arrow,
                                         [#adt{
                                             vars=[{"a", {unbound, A, _}}],
                                             members=[{t_map, t_atom, {unbound, A, _}},
                                                      {t_list, {unbound, A, _}}]
                                            }],
                                         {unbound, A, _}}},
                                #alpaca_binding{type={t_arrow, [t_unit], t_int}},
                                #alpaca_binding{type={t_arrow, [t_unit], t_int}}]}},
                 module_typ_and_parse(Code))
      end
    ,fun() ->
              Code =
                 "module list_and_map_order_2\n\n"
                 "type t 'a = map atom 'a | list 'a \n\n"
                 "let f x = match x with\n"
                 "    #{:a => a} -> a\n"
                 "  | a :: _ -> a\n\n"
                 "let g () = f #{:a => 1, :b => 2}\n\n"
                 "let h () = f [1, 2]",
              ?assertMatch(
                 {ok,
                  #alpaca_module{
                     functions=[#alpaca_binding{
                                   type={t_arrow,
                                         [#adt{
                                             vars=[{"a", {unbound, A, _}}],
                                             members=[{t_list, {unbound, A, _}},
                                                      {t_map, t_atom, {unbound, A, _}}]
                                            }],
                                         {unbound, A, _}}},
                                #alpaca_binding{type={t_arrow, [t_unit], t_int}},
                                #alpaca_binding{type={t_arrow, [t_unit], t_int}}]}},

                           module_typ_and_parse(Code))
     end
    ,fun() ->
             Code =
                 "module record_and_map_order_1\n\n"
                 "type record_map_union 'a = map atom int | {x: int}\n\n"
                 "let get_x rec_or_map =\n"
                 "  match rec_or_map with\n"
                 "      #{:x => xx} -> xx\n"
                 "    | {x = xx}    -> xx\n\n"
                 "let check_map () = get_x #{:x => 1}\n\n"
                 "let check_record () = get_x {x=2}",
             ?assertMatch(
                {ok, #alpaca_module{
                        functions=[#alpaca_binding{
                                      type={t_arrow,
                                            [#adt{}],
                                            t_int}},
                                   #alpaca_binding{type={t_arrow, [t_unit], t_int}},
                                   #alpaca_binding{type={t_arrow, [t_unit], t_int}}]}},
                module_typ_and_parse(Code))
     end
    ,fun() ->
             Code =
                 "module record_and_map_order_2\n\n"
                 "type record_map_union 'a = {x: 'a} | map atom 'a\n\n"
                 "let get_x rec_or_map =\n"
                 "  match rec_or_map with\n"
                 "      #{:x => xx} -> xx\n"
                 "    | {x = xx}    -> xx\n\n"
                 "let check_map () = get_x #{:x => 1}\n\n"
                 "let check_record () = get_x {x=:b}",
             ?assertMatch(
                {ok, #alpaca_module{
                        functions=[#alpaca_binding{
                                      type={t_arrow,
                                            [#adt{vars=[{"a", {unbound, A, _}}]}],
                                            {unbound, A, _}}},
                                   #alpaca_binding{type={t_arrow, [t_unit], t_int}},
                                   #alpaca_binding{type={t_arrow, [t_unit], t_atom}}]}},
                          module_typ_and_parse(Code))
     end
    ].

unify_with_error_test_() ->
    [fun() ->
             Code =
                 "module unify_with_error_test\n\n"
                 "let throw_on_zero x = match x with "
                 "    0 -> throw :zero"
                 "  | _ -> x * 2",
             ?assertMatch(
                {ok, #alpaca_module{
                        functions=[#alpaca_binding{
                                      type={t_arrow, [t_int], t_int}}]}},
                module_typ_and_parse(Code))
     end
     , fun() ->
               Code =
                   "module unify_with_error_test\n\n"
                   "let should_not_unify x = match x with "
                   "    0 -> throw :zero"
                   "  | 1 -> :one "
                   "  | _ -> x * 2",
               ?assertMatch(
                  {error, {cannot_unify, _, _, t_int, t_atom}},
                  module_typ_and_parse(Code))
       end
    , fun() ->
              Code =
                  "module m\n"
                  "let f () = throw (x, :a)",
              ?assertMatch({error, {bad_variable_name, m, 2, <<"x">>}},
                           module_typ_and_parse(Code))
      end
    ].

function_argument_pattern_test_() ->
    [fun() ->
             Code =
                 "module fun_pattern\n\n"
                 "export f/1\n\n"
                 "let f 0 = :zero\n\n"
                 "let f x = :not_zero",
             ?assertMatch(
                {ok, #alpaca_module{
                        functions=[#alpaca_binding{
                                      bound_expr=#alpaca_fun{versions=[_, _]},
                                      type={t_arrow, [t_int], t_atom}}]}},
                module_typ_and_parse(Code))
     end
     , fun() ->
               Code =
                   "module fun_pattern_with_adt\n\n"
                   "type option 'a = None | Some 'a\n\n"
               %% parens needed so the parser doesn't assume the _
               %% belongs to the type constructor:
                   "let my_map (None) _ = None\n\n"
                   "let my_map Some a f = Some (f a)",
               ?assertMatch(
                  {ok, #alpaca_module{
                          functions=[#alpaca_binding{
                                        bound_expr=#alpaca_fun{versions=[_, _]},
                                        type={t_arrow,
                                              [#adt{vars=[{_, {unbound, A, _}}]},
                                               {t_arrow,
                                                [{unbound, A, _}],
                                                {unbound, B, _}}],
                                              #adt{vars=[{_, {unbound, B, _}}]}}}]}},
                  module_typ_and_parse(Code))
       end
    , fun() ->
              Code =
                  "module fun_pattern_with_adt\n\n"
                  "type option 'a = None | Some 'a\n\n"
                  "let my_map _ None = None\n\n"
                  "let my_map f Some a = Some (f a)",
              ?assertMatch(
                 {ok, #alpaca_module{
                         functions=[#alpaca_binding{
                                       bound_expr=#alpaca_fun{versions=[_, _]},
                                       type={t_arrow,
                                             [{t_arrow,
                                               [{unbound, A, _}],
                                               {unbound, B, _}},
                                              #adt{vars=[{_, {unbound, A, _}}]}],
                                             #adt{vars=[{_, {unbound, B, _}}]}}}]}},
                 module_typ_and_parse(Code))
      end
    ].

constrain_polymorphic_adt_funs_test_() ->
    [
     %% Make sure my_map/2 with an explicit integer argument fails to type:
     fun() ->
              Code =
                  "module fun_pattern_with_adt\n\n"
                  "type option 'a = None | Some 'a\n\n"
                  "let my_map _ None = None\n\n"
                  "let my_map f Some a = Some (f a)\n\n"
                  "let doubler x = x * x\n\n"
                  "let foo () = my_map doubler 2",

              ?assertMatch(
                 {error, {cannot_unify, _, _, #adt{}, t_int}},
                 module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module fun_pattern_with_adt\n\n"
                  "type option 'a = None | Some 'a\n\n"
                  "let my_map _ None = None\n\n"
                  "let my_map f Some a = Some (f a)\n\n"
                  "let doubler x = x * x\n\n"
                  "let get_x {x=x} = x\n\n"
                  "let foo () = "
                  "  let rec = {x=1, y=2} in "
                  "  my_map doubler (get_x rec)",
              ?assertMatch(
                 {error, {cannot_unify, _, _, #adt{}, t_int}},
                 module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module fun_pattern_with_adt\n\n"
                  "type option 'a = None | Some 'a\n\n"
                  "let my_map _ None = None\n\n"
                  "let my_map f Some a = Some (f a)\n\n"
                  "let doubler x = x * x\n\n"
                  "let get_x rec = match rec with {x=x} -> x\n\n"
                  "let foo () = "
                  "  let rec = {x=1, y=2} in "
                  "  my_map doubler (get_x rec)",
              ?assertMatch(
                 {error, {cannot_unify, _, _, #adt{}, t_int}},
                 module_typ_and_parse(Code))
      end
    , fun() ->
              %% If my_map depends on an option, when `third` always returns
              %% a bare integer we should get a type error.  `third` here is
              %% obviously not very useful, I'm just trying to isolate the
              %% typing issue to records.
              Code =
                  "module fun_pattern_with_adt\n\n"
                  "type option 'a = None | Some 'a\n\n"
                  "type tuple_or_triple 'a 'b 'c = ('a, 'b) | ('a, 'b, 'c)\n\n"
                  "let my_map _ None = None\n\n"
                  "let my_map f Some a = Some (f a)\n\n"
                  "let third (_, _) = 0\n\n"
                  "let third (_, _, t) = t\n\n"
                  "let doubler x = x * x\n\n"
                  "let foo () = "
                  "  let tup = (1, 2) in "
                  "  my_map doubler (third tup)",
              ?assertMatch(
                 {error, {cannot_unify, _, _, #adt{}, t_int}},
                 module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module fun_pattern_with_adt\n\n"
                  "type option 'a = None | Some 'a\n\n"
                  "let my_map _ None = None\n\n"
                  "let my_map f Some a = Some (f a)\n\n"
                  "let doubler x = x * x\n\n"
                  "let get_x {x=x} = Some x\n\n"
                  "let get_x _ = None\n\n"
                  "let foo () = "
                  "  let rec = {x=1, y=2} in "
                  "  my_map doubler (get_x rec)",
              ?assertMatch(
                 {ok,
                 #alpaca_module{
                    functions=[#alpaca_binding{
                                  type={t_arrow,
                                        [{t_arrow, [{unbound, A, _}], {unbound, B, _}},
                                         #adt{vars=[{_, {unbound, A, _}}]}],
                                        #adt{vars=[{_, {unbound, B, _}}]}}},
                               #alpaca_binding{
                                  type={t_arrow, [t_int], t_int}},
                               #alpaca_binding{
                                  type={t_arrow,
                                        [#t_record{
                                            members=[#t_record_member{
                                                        name=x,
                                                        type={unbound, C, _}}]}],
                                        #adt{vars=[{_, {unbound, C, _}}]}}},
                               #alpaca_binding{
                                  type={t_arrow,
                                        [t_unit],
                                        #adt{vars=[{"a", t_int}]}}}]
                   }},
                 module_typ_and_parse(Code))
      end
    ].

different_arity_test_() ->
    [fun() ->
             Code =
                 "module arity_test\n\n"
                 "let add x = x + x\n\n"
                 "let add x y = x + y",
             ?assertMatch({ok, #alpaca_module{}}, module_typ_and_parse(Code))
     end
    , fun() ->
              Code =
                  "module arity_test\n\n"
                  "export add/2\n\n"
                  "let add x = x + x\n"
                  "let add x y = x + y",
              ?assertMatch({ok, #alpaca_module{}}, module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module arity_test\n\n"
                  "export add/1\n\n"
                  "let add x = x + x\n"
                  "let f x y = add x y",
              ?assertMatch(
                 {error, {not_found, _, <<"add">>, 2}},
                 module_typ_and_parse(Code))
      end].

types_in_types_test_() ->
    AstCode =
        "module types_in_types\n\n"
        "export format/1\n\n"
        "export_type symbol,expr,ast\n\n"
        "type symbol = Symbol string\n\n"
        "type expr = symbol | Apply (expr, expr) "
        "| Match {e: expr, clauses: list {pattern: expr, result: expr}}\n\n"
        "type ast = expr | Fun {name: symbol, arity: int, body: expr}\n\n",
    [fun() ->
             %% Without importing `symbol` we should be fine if we're not
             %% referencing its constructor directly:
             FormatterCode =
                 "module formatter\n\n"
                 "import_type types_in_types.expr\n\n"
                 "import_type types_in_types.ast\n\n"
                 "let format ast_node = format 0 ast_node\n\n"
                 "let format d Match {e=e, clauses=cs} = :match",

             [M1, M2] = make_modules([AstCode, FormatterCode]),
             ?assertMatch(
                {ok, [#alpaca_module{}, #alpaca_module{}]},
                type_modules([M1, M2]))
     end
    , fun() ->
              %% Importing `symbol` and not using it should be fine:
              FormatterCode =
                  "module formatter\n\n"
                  "import_type types_in_types.symbol\n\n"
                  "import_type types_in_types.expr\n\n"
                  "import_type types_in_types.ast\n\n"
                  "let format ast_node = format 0 ast_node\n\n"
                  "let format d Match {e=e, clauses=cs} = :match",

              [M1, M2] = make_modules([AstCode, FormatterCode]),
              ?assertMatch(
                 {ok, [#alpaca_module{}, #alpaca_module{}]},
                 type_modules([M1, M2]))
      end
    , fun() ->
              %% NOT importing `symbol` and then trying to use its type
              %% constructor should yield an error:
              FormatterCode =
                  "module formatter\n\n"
                  "import_type types_in_types.expr\n\n"
                  "import_type types_in_types.ast\n\n"
                  "let format ast_node = format 0 ast_node\n\n"
                  "let format d Match {e=e, clauses=cs} = :match\n\n"
                  "let format d Symbol _ = :symbol\n\n"
                  "let foo () = format 0 Match {e=Symbol \"x\", clauses=[]}",

              [M1, M2] = make_modules([AstCode, FormatterCode]),
              ?assertMatch(
                 {error, {bad_constructor, _, "Symbol"}},
                 type_modules([M1, M2]))
      end
    , fun() ->
              Ast =
                  "module types_in_types\n\n"
                  "export format/1\n\n"
                  "export_type symbol,expr,ast\n\n"
                  "type symbol = Symbol {name: string}\n\n"
                  "type expr = symbol | Apply (expr, expr) "
                  "| Match {e: expr, clauses: list {pattern: expr, result: expr}}\n\n"
                  "type ast = expr | Fun {name: symbol, arity: int, body: expr}\n\n",

              %% Importing `symbol` should let us use the constructor:
              FormatterCode =
                  "module formatter\n"
                  "import_type types_in_types.symbol\n"
                  "import_type types_in_types.expr\n"
                  "import_type types_in_types.ast\n\n"
                  "let format ast_node = format 0 ast_node\n\n"
                  "let format d Match {e=e, clauses=cs} = :match\n\n"
                  "let format d Symbol _ = :symbol\n\n"
                  "let foo () = format 0 Match {e=Symbol {name=\"x\"}, clauses=[]}",

              [M1, M2] = make_modules([Ast, FormatterCode]),
              ?assertMatch(
                 {ok, [#alpaca_module{}, #alpaca_module{}]},
                 type_modules([M1, M2]))
      end
    ].

expression_typing_test_() ->
    [%% `1` is not a function from an int to something else:
     ?_assertMatch(
        {error, {cannot_unify, _, _, t_int, {t_arrow, [t_int], _}}},
        top_typ_of("1 2")),
     ?_assertMatch({{t_arrow, [t_unit], t_int}, _},
                   top_typ_of(
                     "let g () = "
                     "let f x = x + x in "
                     "let g () = f in "
                     "(g ()) 2"
                    ))

    ].

module_qualified_types_test_() ->
    [fun() ->
             Code1 = "module m type a = int",
             Code2 = "module n type b = m.a",
             [M1, M2] = make_modules([Code1, Code2]),
             ?assertMatch(
                {ok, [#alpaca_module{}, #alpaca_module{}]},
                type_modules([M1, M2]))
     end
     , fun() ->
               Code1 = "module m export_type a type a 'a = A 'a",
               Code2 = 
                   "module n "
                   "type b 'x = m.a 'x "
                   "let f m.A a = a + 1",
               [M1, M2] = make_modules([Code1, Code2]),
               ?assertMatch(
                  {ok,
                   [#alpaca_module{
                       functions=[#alpaca_binding{
                                    type={t_arrow,
                                          [#adt{
                                              name = <<"a">>,
                                              vars=[{_, t_int}]}],
                                          _}}]},
                    #alpaca_module{}]},
                  type_modules([M1, M2]))
       end
    , fun() ->
              Code1 = "module m export_type a type a 'a = A 'a",
              Code2 =
                  "module n "
                  "type a 'a = A 'a "
                  "let f A x = x + 1 "
                  "let other_a x = m.A x "
                  "let should_fail () = f (other_a 1)",
              [M1, M2] = make_modules([Code1, Code2]),
              ?assertMatch({error,
                            {cannot_unify, _, _,
                             #adt{name = <<"a">>, module=n},
                             #adt{name = <<"a">>, module=m}}},
                           type_modules([M1, M2]))
      end
     , fun() ->
               Code =
                   "module m "
                   "let f n.A x = x + 1",
               [M] = make_modules([Code]),
               ?assertMatch({error, {bad_module, m, 1, n}}, type_modules([M]))
       end
    ].

no_process_leak_test() ->
    Code =
        "module no_leaks\n"
        "let add a b = a + b",

    [M] = make_modules([Code]),
    ProcessesBefore = length(erlang:processes()),
    ?assertMatch({ok, _}, type_modules([M])),
    ProcessesAfter = wait_for_processes_to_die(ProcessesBefore, 10),
    ?assertEqual(ProcessesBefore, ProcessesAfter).

wait_for_processes_to_die(_ExpectedNumProcesses, 0)            ->
    length(erlang:processes());
wait_for_processes_to_die(ExpectedNumProcesses, AttemptsLeft) ->
    case length(erlang:processes()) of
        ExpectedNumProcesses -> ExpectedNumProcesses;
        _WrongNumProcesses   ->
            timer:sleep(10),
            wait_for_processes_to_die(ExpectedNumProcesses, AttemptsLeft-1)
    end.

curry_applications_test_() ->
    [fun() ->
        Code =
            "module curry\n"
            "let add a b = a + b\n\n"
            "let main x = add x\n",

        ?assertMatch(
            {ok, #alpaca_module{
                    functions=[#alpaca_binding{
                        type={t_arrow,
                            [t_int, t_int], t_int}

                        },
                        #alpaca_binding{
                        type={t_arrow,
                            [t_int], {t_arrow, [t_int], t_int}}
                        }
                    ]
                }
            },
        module_typ_and_parse(Code))
    end,
    fun() ->
        Code =
            "module curry\n"
            "let main x = add x\n"
            "let add a b = a + b\n\n",

        ?assertMatch(
            {ok, #alpaca_module{
                    functions=[
                        #alpaca_binding{
                            type={t_arrow,
                                    [t_int], {t_arrow, [t_int], t_int}}
                        },
                        #alpaca_binding{
                            type={t_arrow,
                                    [t_int, t_int], t_int}
                        }
                    ]
                }
            },
        module_typ_and_parse(Code))
    end,
    fun() ->
        Code =
            "module curry\n"
            "let main x = add x\n"
            "let add a b = a + b\n\n"
            "let add a b c = a + b + c\n\n",

        ?assertMatch(
            {error, {ambiguous_curry, _, _, _}},
            module_typ_and_parse(Code))
    end
    ].

local_curry_test() ->
    Code =
    "module local_curry\n"
    "let main () = \n"
    "  let f x y = x * y in\n"
    "  f 10",
    ?assertMatch(
        {ok, #alpaca_module{
                functions=[
                    #alpaca_binding{
                        type={t_arrow,
                                [t_unit], {t_arrow, [t_int], t_int}}
                    }
                ]
            }
        },
        module_typ_and_parse(Code)).

%% For issue #113, we want to be able to define a polymorphic type and use it
%% as a member in another type but with a concrete type rather than variables,
%% e.g.
%%
%% type option 'a = Some 'a | None
%% type int_option = option 'a
%%
concrete_type_parameters_test_() ->
    [fun() ->
             Code =
                 "module concrete_option\n"
                 "type opt 'a = Some 'a | None\n"
                 "type uses_opt = Uses opt int\n"
                 "let f () = Uses Some 1",
             ?assertMatch({ok, #alpaca_module{}},
                          module_typ_and_parse(Code))
     end,
     fun() ->
             Code =
                 "module should_not_unify "
                 "type opt 'a = Some 'a | None "
                 "type uses_opt = Uses opt int "
                 "let f () = Uses Some 1.0",
             ?assertMatch({error, {cannot_unify, _, _, t_int, t_float}},
                          module_typ_and_parse(Code))
     end,
     fun() ->
             Option =
                 "module option "
                 "export_type option "
                 "type option 'a = Some 'a | None",

             UsesOption =
                 "module uses_option "
                 "type int_opt = IntOpt option.option int "
                 "let make_opt x = IntOpt option.Some x",

             ImportsOption =
                 "module imports_option "
                 "import_type option.option "
                 "type int_opt = IntOpt option int "
                 "let make_opt x = IntOpt Some x",

             Mods1 = make_modules([Option, UsesOption]),
             Mods2 = make_modules([Option, ImportsOption]),

             ?assertMatch({ok,
                           [#alpaca_module{
                               name=uses_option,
                               types=[#alpaca_type{
                                         members=[#alpaca_constructor{
                                                     arg=#alpaca_type{
                                                            name={_, _, <<"option">>},
                                                            module=option,
                                                            vars=[{_, t_int}]
                                                           }}]}],
                               functions=[#alpaca_binding{
                                             type={t_arrow,
                                                   [t_int],
                                                   #adt{
                                                      name= <<"int_opt">>,
                                                      module=uses_option
                                                     }}
                                            }]
                              },
                            #alpaca_module{}]},
                          type_modules(Mods1)),
             ?assertMatch({ok,
                           [#alpaca_module{
                               name=imports_option,
                               types=[#alpaca_type{
                                         members=[#alpaca_constructor{
                                                     arg=#alpaca_type{
                                                            name={_, _, <<"option">>},
                                                            vars=[{_, t_int}]
                                                           }}]}],
                               functions=[#alpaca_binding{
                                             type={t_arrow,
                                                   [t_int],
                                                   #adt{
                                                      name= <<"int_opt">>,
                                                      module=imports_option
                                                     }}
                                            }]
                              },
                            #alpaca_module{}]},
                          type_modules(Mods2))
     end,
     %% From @danabr's example on PR #116
     fun() ->
             Code =
                 "module int_opt \n"
                 "type opt 'a = Some 'a | None \n"
                 "type int_opt = opt int \n"
                 "type indirect = Indirect int_opt \n"
                 "let deconstruct (Indirect opt) = \n"
                 "match opt with \n"
                 "(Some 1) -> :blah \n",

             ?assertMatch({ok,
                           #alpaca_module{
                              functions=[#alpaca_binding{
                                            type={t_arrow,
                                                  [#adt{name= <<"indirect">>}],
                                                  t_atom}
                                           }]
                             }},
                          module_typ_and_parse(Code))
     end
    ].

ensure_private_types_cant_import_test_() ->
    [fun() ->
             PrivateOptions =
                 "module private_option \n"
                 "type opt 'a = Some 'a | None \n",

             ImportOption =
                 "module import_option \n"
                 "import_type private_option.opt",

             UsesOption =
                 "module uses_option \n"
                 "type nested_int_opt = Nested private_option.opt int \n"
                 "let nest x = Nested x",

             Mods1 = make_modules([PrivateOptions, ImportOption]),
             Mods2 = make_modules([PrivateOptions, UsesOption]),
             ?assertMatch({error, {unexported_type, _, _, <<"opt">>}},
                          type_modules(Mods1)),
             ?assertMatch({ok, [_, _]}, type_modules(Mods2))
     end
     %% Make sure exporting a type containing a private type doesn't leak the
     %% private type's constructors:
    , fun() ->
              Exported =
                  "module exported \n"
                  "export_type b \n"
                  "type a 'a = A 'a \n"
                  "type b = B a int",
              UsesB =
                  "module uses_b \n"
                  "import_type exported.b \n"
                  "let use_a x = A x",

              Mods = make_modules([Exported, UsesB]),
              ?assertMatch({error, {bad_constructor, _, "A"}},
                           type_modules(Mods))
      end

     %% Make sure we can't access constructors in private types:
     , fun() ->
               PrivateType =
                   "module private_type \n"
                   "type a = A int \n",
               UsesA =
                   "module uses_a \n"
                   "let f x = private_type.A x",

               Mods = make_modules([PrivateType, UsesA]),
               ?assertMatch({error, {bad_constructor, _, "A"}},
                            type_modules(Mods))
       end
    ].

%% From issue #91, a type's members must all exist, both concrete types and
%% type variables.
error_on_missing_types_test_() ->
    [fun() ->
             Code =
                 "module m \n"
                 "type t = b",
             ?assertMatch({error, {unknown_type, m, 2, <<"b">>}},
                          module_typ_and_parse(Code))
     end
     , fun() ->
               Code =
                   "module m \n"
                   "type t 'a = A 'a \n"
                   "type u = t b",
               ?assertMatch({error, {unknown_type, m, 3, <<"b">>}},
                            module_typ_and_parse(Code))
       end
    , fun() ->
              Code =
                  "module m \n"
                  "type t = T b",
              ?assertMatch({error, {unknown_type, m, 2, <<"b">>}},
                            module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module m \n"
                  "type t = (int, b)",
              ?assertMatch({error, {unknown_type, m, 2, <<"b">>}},
                            module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module m \n"
                  "type t = {x: b}",
              ?assertMatch({error, {unknown_type, m, 2, <<"b">>}},
                            module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module m \n"
                  "type t = T int | list b",
              ?assertMatch({error, {unknown_type, m, 2, <<"b">>}},
                            module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module m \n"
                  "type t = map atom c",
              ?assertMatch({error, {unknown_type, m, 2, <<"c">>}},
                            module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module m \n"
                  "type t = T 'a",
              ?assertMatch({error, {bad_variable, 2, "a"}},
                            module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module m \n"
                  "type t = T (int, float, 'c)",
              ?assertMatch({error, {bad_variable, 2, "c"}},
                            module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module m \n"
                  "type t 'a = map atom (t 'a)",
              ?assertMatch({ok, #alpaca_module{}},
                            module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module m \n"
                  "type t 'a = n.u",
              ?assertMatch({error, {bad_module, m, 2, n}},
                            module_typ_and_parse(Code))
      end
    , fun() ->
              M1 = "module m",
              M2 = "module n \n type t = m.a",
              Mods = make_modules([M1, M2]),
              ?assertMatch({error, {unknown_type, n, 2, <<"a">>}},
                            type_modules(Mods))
      end
    ].

record_transform_test_() ->
    [?_assertMatch({#t_record{members=[#t_record_member{
                                          name=a,
                                          type=t_int},
                                       #t_record_member{
                                          name=x,
                                          type=t_int},
                                       #t_record_member{
                                          name=y,
                                          type=t_int}], row_var={unbound, _, _}}, _},
                   top_typ_of("let z = {a=3} in {x=1, y=2 | z}")),
     ?_assertMatch({#t_record{members=[#t_record_member{
                                          name=x,
                                          type=t_string},
                                       #t_record_member{
                                          name=y,
                                          type=t_int}], row_var={unbound, _, _}}, _},
                   top_typ_of("{x=\"hello\" | {y=2}}")),
     ?_assertMatch({#t_record{members=[#t_record_member{
                                          name=x,
                                          type=t_float}]}, _},
                   top_typ_of("{x=1.0 | {x=1}}")),
     fun() ->
             Code =
                 "module update_a_record \n"
                 "let add_y y_value r = \n"
                 "  match r with \n"
                 "    {x=1}\n -> {y=y_value\n | r}",
             ?assertMatch({ok, #alpaca_module{}},
                          module_typ_and_parse(Code))
     end
    , fun() ->
              Code =
                  "module update_record_no_match \n"
                  "let add_y y_value r = \n"
                  "  {y=y_value | r} \n"
                  "let f () = add_y 5 {x=2.2}",
              ?assertMatch({ok,
                            #alpaca_module{
                               functions=[_,
                                          #alpaca_binding{
                                             type={t_arrow,
                                                   [t_unit],
                                                   #t_record{
                                                      members=[#t_record_member{
                                                                  name=x,
                                                                  type=t_float},
                                                               #t_record_member{
                                                                  name=y,
                                                                  type=t_int}]}}}]}},
                           module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module m \n"
                  "let opaque_add rx = \n"
                  "  match rx with \n"
                  "    {x=_} -> {a=2, b=\"three\" | rx} \n"
                  "let f () = opaque_add {x=1, b=3}",
              ?assertMatch(
                 {ok,
                  #alpaca_module{
                    functions=[_,
                               #alpaca_binding{
                                 type={t_arrow,
                                       [t_unit],
                                       #t_record{
                                          members=[#t_record_member{},
                                                   #t_record_member{},
                                                   #t_record_member{}]
                                         }}}]}},
                 module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module m \n"
                  "let x_int rec = {x=1 | rec} \n"
                  "let x_float rec = {x=1.0, y=\"b\" | rec} \n"
                  "let x_string rec = {x=\"one!\" | rec} \n"
                  "let main () = x_string (x_float (x_int {z=5}))",
              ?assertMatch(
                 {ok,
                  #alpaca_module{
                     functions=[_, _, _,
                                #alpaca_binding{
                                   type={t_arrow,
                                         [t_unit],
                                         #t_record{
                                            members=[#t_record_member{
                                                        name=x,
                                                        type=t_string
                                                       },
                                                     #t_record_member{
                                                        name=y,
                                                        type=t_string
                                                       },
                                                     #t_record_member{
                                                        name=z,
                                                        type=t_int
                                                       }]}}}]}},
                           module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module m \n"
                  "type t = T {x: int, y: float} \n"
                  "let main () = T {x=1}",
              ?assertMatch(
                 {error, {missing_record_field, m, 3,  y}},
                 module_typ_and_parse(Code))
      end
    ].

records_and_type_constructors_test_() ->
    [fun() ->
             Code =
                 "module m \n"
                 "type t 'a = T {x: int, y: 'a} \n"
                 "let main () = T {x=1, y=\"hello\"}",
             ?assertMatch(
                {ok, #alpaca_module{
                        functions=[#alpaca_binding{
                                      type={t_arrow,
                                            [_],
                                            #adt{vars=[{"a", t_string}]}}}
                                  ]}},
                module_typ_and_parse(Code))
     end
     %% This test illustrates something I'm not sure we want at the moment.
     %% Because an instance of a type constructor is used to instantiate a
     %% type arrow rather than carry type information itself, using a
     %% constructor with a record loses the row variable information as seen
     %% in extract_rec/1's type.
    , fun() ->
              Code =
                  "module m \n"
                  "type t = T {x: int} \n"
                  "let main () = T {x=1, y=\"hello\"} \n"
                  "let extract_rec () = match (main ()) with \n"
                  "  T rec -> rec",
              ?assertMatch(
                 {ok, #alpaca_module{
                         functions=[_,
                                    #alpaca_binding{
                                      type={t_arrow,
                                            [_],
                                            #t_record{
                                               members=[#t_record_member{
                                                          name=x,
                                                          type=t_int}]
                                              }}}
                                   ]}},
                 module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module m \n"
                  "type t = T {x: int} \n"
                  "let main () = T {x=1.0}",
              ?assertMatch(
                 {error, {cannot_unify, _, _, t_int, t_float}},
                 module_typ_and_parse(Code))
      end
    ].

literal_fun_test_() ->
    [?_assertMatch({{t_arrow, [t_int], t_int}, _},
                   top_typ_of("fn x -> x + 1"))
    , ?_assertMatch({{t_arrow, [t_int], t_int}, _},
                    top_typ_of("let f = fn x -> x + 1"))
    , fun () ->
              Code =
                  "module m "
                  "let map f [] = [] "
                  "let map f (h :: t) = (f h) :: (map f t) "
                  "let nested_fun () ="
                  "  map (fn x -> (fn y -> y + 1) x) [1, 2, 3]",
              ?assertMatch(
                 {ok, #alpaca_module{
                         functions=[_,
                                    #alpaca_binding{
                                       type={t_arrow, [t_unit], {t_list, t_int}}}]}},
                 module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module m \n"
                  "let f () = \n"
                  "  let g = fn x -> x + 1 in \n"
                  "  g 2",
              ?assertMatch(
                 {ok, #alpaca_module{
                         functions=[#alpaca_binding{
                                       type={t_arrow, [t_unit], t_int}}]}},
                 module_typ_and_parse(Code))
      end
    ].

bad_signature_unify_fail_test() ->
    Code =
      "module sig \n"
      "val double : fn string -> string\n"
      "let double x = x * x",
    ?assertMatch({error,{cannot_unify,sig,2,t_int,t_string}},
                 module_typ_and_parse(Code)).

poly_specialization_unify_fail_test() ->
    Code =
      "module sig \n"
      "-- Without the sig this types as `fn 'a -> 'a`\n"
      "val intsOnly : fn int -> int\n"
      "let intsOnly x = x\n"
      "-- Without the type signature, the below would succeed\n"
      "let tryWithString () = intsOnly \"hello world\"",
    ?assertMatch({error,{cannot_unify,sig,6,t_int,t_string}},
                 module_typ_and_parse(Code)). 

beam_with_signatures_test() ->
    Code =
      "module sig \n"
      "-- signatures with 'beam' FFI allows us to guard against bad input\n"
      "val atomToBinary : fn atom -> binary\n"
      "let atomToBinary b = beam :erlang :atom_to_binary [b, :utf8] with\n"
      "  | res, is_binary res -> res\n"
      "let main () = \n",

    Good = "atomToBinary :hello",
    Fail = "atomToBinary 42",
    
    ?assertMatch({error,{cannot_unify,sig,7,t_atom,t_int}},
                 module_typ_and_parse(Code ++ Fail)),

    ?assertMatch({ok, _},
                 module_typ_and_parse(Code ++ Good)).

missing_type_var_in_signature_test() ->
    Code =
      "module sig \n"
      "--type bob = Hello 'a\n"
      "val missingTypeVar : fn 'a -> ('a, 'a)\n"
      "let missingTypeVar x = (x, x)\n"
      "let main () = missingTypeVar 10",
    ?assertMatch({error,{unknown_type_var,sig,3,"a"}},
                 module_typ_and_parse(Code)).  

nested_adt_test() ->
    Code =
        "module nested_adt\n"
        "type opt 'a = None | Some 'a\n"
        "type w = W opt (opt int)\n"
        "let make_w () = W (Some (Some 1))\n",
    ?assertMatch(
       {ok, #alpaca_module{
               types=[#alpaca_type{
                         name={type_name, _, <<"w">>},
                         vars=[],
                         members=[#alpaca_constructor{
                                     arg=#alpaca_type{
                                            name={type_name, _, <<"opt">>},
                                            vars=[{{type_var, _, _},
                                                  #alpaca_type{
                                                     name={type_name, _, <<"opt">>},
                                                     vars=[{{type_var, _, _}, t_int}]
                                                    }}]
                                           }}]},
                      #alpaca_type{name={type_name, _, <<"opt">>}}],
               functions=[#alpaca_binding{
                            type={t_arrow, [t_unit], #adt{name = <<"w">>}}}]}},
       module_typ_and_parse(Code)).

direct_lambda_application_test_() ->
    Prelude =
        "module lambdas\n"
        "val apply 'a 'b : fn (fn 'a -> 'b) 'a -> 'b\n"
        "let apply f x = f x\n",

    [fun() ->
             Code = Prelude ++
                 "let useLambda x =\n"
                 "  apply (fn y -> x + y) 10",
             ?assertMatch({ok, _}, module_typ_and_parse(Code))
     end,
     fun() ->
             Code = Prelude ++
                 "let useLambda x =\n"
                 "  apply (fn (_, y) -> x + y) (:ignored, 10)",
             ?assertMatch({ok, _}, module_typ_and_parse(Code))
     end,
     fun() ->
             Code = Prelude ++
                 "let boundLambda x =\n"
                 "  let lambda = (fn y -> x + y) in\n"
                 "  apply lambda 10",
             ?assertMatch({ok, #alpaca_module{}}, module_typ_and_parse(Code))
     end,
     fun() ->
             Code = Prelude ++
                 "let useLet x =\n"
                 "  apply (let f y = x + y in f) 10",
             ?assertMatch({ok, #alpaca_module{}}, module_typ_and_parse(Code))
     end
    ].
    
destructuring_test_() ->
    [fun() ->
             Code = "module m let f() = let (x, _) = (1, 2) in x + 1",
             ?assertMatch({ok, #alpaca_module{
                                  functions=[#alpaca_binding{
                                                type={t_arrow, [t_unit], t_int}}]}},
                          module_typ_and_parse(Code))
     end
    , fun() ->
              Code = "module m let f t = let (x, y) = t in x + y",
              ?assertMatch(
                 {ok, #alpaca_module{
                         functions=[#alpaca_binding{
                                       type={t_arrow, [{t_tuple, [t_int, t_int]}],
                                             t_int}}]}},
                 module_typ_and_parse(Code))
      end
     , fun() ->
               Code =
                   "module m \n"
                   "let f r = let {x=x, y=y} = r in x + y \n"
                   "let g t = let (x, y) = t in f {x=x, y=y} \n"
                   "let test_it () = g (5, 6)",
               ?assertMatch(
                  {ok, #alpaca_module{
                         functions=[#alpaca_binding{
                                       type={t_arrow, 
                                             [#t_record{members=[#t_record_member{type=t_int},
                                                                 #t_record_member{type=t_int}
                                                                ]}], t_int}},
                                    #alpaca_binding{
                                       type={t_arrow, [{t_tuple, [t_int, t_int]}], t_int}},
                                    #alpaca_binding{
                                       type={t_arrow, [t_unit], t_int}}]}},
                  module_typ_and_parse(Code))
       end
    ].

%% TODO/FIXME:  we have some bad line number reporting in here, lots of zeroes.
record_unification_test_() ->
    %% Initial cases taken from https://github.com/alpaca-lang/alpaca/issues/198
    %% and then expanded on.
    [fun() ->
             Code =
                 "module m \n"
                 "type s = {a: bool, b: int} \n"
                 "let foo :a s = {a=true, b=0 | s} \n"
                 "let foo :b s = {b=1| s} \n",

             ?assertMatch({error, {missing_record_field, m, 0, a}},
                          module_typ_and_parse(Code))
     end
    , fun() ->
	      Code =
		  "module mod\n"
		  "let foo :a = {a=true, b=0}\n"
		  "let foo :b = {b=0}\n",
	      ?assertMatch({error, {missing_record_field, mod, 0, a}},
			   module_typ_and_parse(Code))
      end
    , fun() ->
	      Code =
		  "module mod\n"
		  "let foo :b = {b=0}\n"
		  "let foo :a = {a=true, b=0}\n",
	      ?assertMatch({error, {missing_record_field, mod, 0, a}},
			   module_typ_and_parse(Code))
      end
    , fun() ->
	      Code =
		  "module m \n"
		  "type s = {a: bool, b: int} \n"
		  "let foo sym = "
		  "  match sym with \n"
		  "  | :b -> {b=1} \n"
		  "  | :a -> {a=true, b=0} ",

	      %% TODO/FIXME:  this should report line 4!
	      ?assertMatch({error, {missing_record_field, m, 5, a}},
			   module_typ_and_parse(Code))
      end
    , fun() ->
	      Code =
		  "module m \n"
		  "type s = {a: bool, b: int} \n"
		  "val foo: fn atom -> {a: bool, b: int}\n"
		  "let foo sym = "
		  "  match sym with "
		  "  | :a -> {a=true, b=0} "
		  "  | :b -> {b=1}",

	      ?assertMatch({error, {missing_record_field, m, 4, a}},
			   module_typ_and_parse(Code))
      end
    , fun() ->
	      Code =
		  "module m \n"
		  "type s = {a: bool, b: int} \n"
		  "let foo sym rec = "
		  "  match sym with "
		  "  | :a -> {a=true, b=0 | rec } "
		  "  | :b -> {b=1 | rec}",
	      ?assertMatch({error, {missing_record_field, m, 3, a}},
			   module_typ_and_parse(Code))
      end
    , fun() ->
              Code =
                  "module m \n"
                  "type s = A {a: bool, b: int} \n"
                  "let foo :a A s = A {a=true | s} \n"
                  "let foo :b A s = A {b=1 | s}",

              ?assertMatch({ok, #alpaca_module{
                                  functions=[#alpaca_binding{
                                               type={t_arrow,
                                                    [t_atom, #adt{name = <<"s">>}],
                                                    #adt{name = <<"s">>}}}]}},
                           module_typ_and_parse(Code))
      end
].

make_modules(Sources) ->
  NamedSources = lists:map(fun(C) -> {?FILE, C} end, Sources),
  {ok, Mods} = alpaca_ast_gen:make_modules(NamedSources),
  Mods.

-endif.
