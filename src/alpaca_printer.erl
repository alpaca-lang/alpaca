%%% -*- mode: erlang;erlang-indent-level: 4;indent-tabs-mode: nil -*-
%%% ex: ft=erlang ts=4 sw=4 et
%%%
%%% Copyright 2017 Jeremy Pierre
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
%
%%% This module pretty prints Alpaca types from their AST representation.
%%% This is useful for error messages, pretty printing module documentation,
%%% shells and debugging. User defined types are also supported.

-module(alpaca_printer).

-export([format_type/1]).

-include("alpaca_ast.hrl").

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

-ignore_xref([format_type/1]).

%% If a type has multiple parts, we may need to add parens so it is
%% unambigious for types like t_arrow, t_list etc.,
infer_parens(<<"(", _Rest>> = TypeRep) -> TypeRep;
infer_parens(<<"{", _Rest>> = TypeRep) -> TypeRep;
infer_parens(TypeRepr) ->
    case binary:split(TypeRepr, <<" ">>) of
        [_] -> TypeRepr;
        [_, _] -> <<"(", TypeRepr/binary, ")">>
    end.

%% Simple primitive types
format_t(t_int)    -> <<"int">>;
format_t(t_float)  -> <<"float">>;
format_t(t_string) -> <<"string">>;
format_t(t_binary) -> <<"binary">>;
format_t(t_atom)   -> <<"atom">>;
format_t(t_unit)   -> <<"()">>;
format_t(t_bool)   -> <<"boolean">>;
format_t(t_chars)  -> <<"chars">>;
format_t(t_rec)    -> <<"rec">>;

%% Complex types
format_t({t_tuple, TupleTypes}) ->
    FormattedTypes = lists:map(fun(T) -> format_t(T) end, TupleTypes),
    TupleList = list_to_binary(lists:join(<<", ">>, FormattedTypes)),
    <<"(", TupleList/binary, ")">>;

format_t({t_list, ListType}) ->
    SubTypeRepr = infer_parens(format_t(ListType)),
    <<"list ", SubTypeRepr/binary>>;

format_t(#t_record{members=Members}) ->
    SubTypeReprs = lists:map(fun(T) -> format_t(T) end, Members),
    MembersList = list_to_binary(lists:join(<<", ">>, SubTypeReprs)),
    <<"{", MembersList/binary, "}">>;

format_t(#t_record_member{name=Name, type=Type}) ->
    NameRepr = list_to_binary(atom_to_list(Name)),
    TypeRepr = format_t(Type),
    <<NameRepr/binary, " : ", TypeRepr/binary>>;

%% Function types
format_t({t_arrow, Args, RetType}) ->
    ArgReprs = lists:map(fun(T) -> infer_parens(format_t(T)) end, Args),
    ArgsList = list_to_binary(lists:join(<<" ">>, ArgReprs)),
    RetRepr = format_t(RetType),
    <<"fn ", ArgsList/binary, " -> ", RetRepr/binary>>;

format_t({unbound, N, _}) ->
    Num = atom_to_binary(N, utf8),
    <<"!!", Num/binary>>;

format_t(#adt{name=Name, vars=Vars}) ->
    case Vars of
        [] -> Name;
        _ -> ArgReprs = lists:map(fun({_, T}) -> 
                                          infer_parens(format_t(T))
                                  end,
                                  Vars),

             ArgsList = list_to_binary(lists:join(<<" ">>, ArgReprs)),

             <<Name/binary, " ", ArgsList/binary>>
     end;

format_t({t_map, Key, Val}) ->
    KeyRepr = infer_parens(format_t(Key)),
    ValRepr = infer_parens(format_t(Val)),
    <<"map ", KeyRepr/binary, " ", ValRepr/binary>>;

format_t({t_pid, Type}) ->
    TypeRepr = infer_parens(format_t(Type)),
    <<"pid ", TypeRepr/binary>>;

format_t({t_receiver, Initial, ReceiveFun}) ->
    InitialRepr = infer_parens(format_t(Initial)),
    ReceiveFunRepr = infer_parens(format_t(ReceiveFun)),
    <<"receiver ", InitialRepr/binary, " ", ReceiveFunRepr/binary>>;

%% Catch all
format_t(Unknown) -> io:format("unknown type ~p", [Unknown]).

format_type(Type) ->
    Repr = format_t(Type),
    %% Deal with any type vars
    case re:run(Repr, <<"!!t([0-9]+)">>, [global, {capture, first, binary}]) of
        {match, Matches} ->
            TypeVars = lists:usort(lists:map(fun([M]) -> M end, Matches)),
            apply_type_vars(Repr, TypeVars, 97);
        _ ->
            Repr
    end.

apply_type_vars(Str, [], _NextVar) ->
    Str;

apply_type_vars(Str, [TV | Rest], NextVar) ->
    NewStr = re:replace(Str, TV, <<"'", NextVar>>, [global, {return, binary}]),
    apply_type_vars(NewStr, Rest, NextVar+1).

-ifdef(TEST).

simple_builtin_types_test_() ->
    [?_assertMatch(<<"int">>,       format_type(t_int)),
     ?_assertMatch(<<"string">>,    format_type(t_string)),
     ?_assertMatch(<<"float">>,     format_type(t_float)),
     ?_assertMatch(<<"binary">>,    format_type(t_binary)),
     ?_assertMatch(<<"atom">>,      format_type(t_atom)),
     ?_assertMatch(<<"boolean">>,   format_type(t_bool)),
     ?_assertMatch(<<"chars">>,     format_type(t_chars)),
     ?_assertMatch(<<"rec">>,       format_type(t_rec)),
     ?_assertMatch(<<"()">>,        format_type(t_unit))
   ].

tuples_test_() ->
    [?_assertMatch(
        <<"(int, float)">>,
        format_type({t_tuple, [t_int, t_float]}))].

lists_test_() ->
    [?_assertMatch(
       <<"list string">>,
        format_type({t_list, t_string})),

     ?_assertMatch(
        <<"list (list int)">>,
        format_type({t_list, {t_list, t_int}}))].

record_test_() ->
    [?_assertMatch(
       <<"{name : string, age : int}">>,
       format_type(#t_record{members=[#t_record_member{name=name, type=t_string},
                                      #t_record_member{name=age, type=t_int}]}))
    ].

function_test_() ->
    [?_assertMatch(
       <<"fn int int -> int">>,
       format_type({t_arrow, [t_int, t_int], t_int})),
     ?_assertMatch(
       <<"fn int -> rec">>,
       format_type({t_arrow, [t_int], t_rec}))].

pid_test() ->
    ?assertMatch(<<"pid int">>, format_type({t_pid, t_int})).

from_module_test() ->
    Code = "module types\n"
           "val apply 'a 'b : fn (fn 'a -> 'b) 'a -> 'b\n"
           "let apply f x = f x\n"
           "type maybe 'a = Just 'a | Nothing\n"
           "let just something = Just something\n"
           "let make_map x = #{\"key\" => x * x}\n"
           "let make_receiver x = receive with y -> x * y\n"
           "let make_pid () = spawn make_receiver 10",
    {ok, Res} = alpaca:compile({text, Code}),
    [{compiled_module, N, FN, Bin}] = Res,
    {module, N} = code:load_binary(N, FN, Bin),
    Attrs = N:module_info(attributes),
    Types = proplists:get_value(alpaca_typeinfo, Attrs),

    #alpaca_module{functions=Funs} = Types,
    [#alpaca_binding{type=PidType},
     #alpaca_binding{type=ReceiverType},
     #alpaca_binding{type=MapType}, 
     #alpaca_binding{type=JustType}, 
     #alpaca_binding{type=ApplyType}] = Funs,

    ?assertMatch(<<"fn (fn 'a -> 'b) 'a -> 'b">>, format_type(ApplyType)),
    ?assertMatch(<<"fn 'a -> maybe 'a">>, format_type(JustType)),
    ?assertMatch(<<"fn int -> map string int">>, format_type(MapType)),
    ?assertMatch(<<"fn () -> pid int">>, format_type(PidType)),
    ?assertMatch(<<"receiver int (fn int -> int)">>, format_type(ReceiverType)),

    code:purge(N).

-endif.
