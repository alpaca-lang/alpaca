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

-export([format_type/1, format_binding/1, format_module/1, format_module/2]).

-include("alpaca_ast.hrl").

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

-ignore_xref([format_type/1, format_binding/1, format_module/1, format_module/2]).

%% If a type has multiple parts, we may need to add parens so it is
%% unambigious for types like t_arrow, t_list etc.,
infer_parens(<<"(", _Rest/binary>> = TypeRep) -> TypeRep;
infer_parens(<<"{", _Rest/binary>> = TypeRep) -> TypeRep;
infer_parens(TypeRepr) ->
    case binary:split(TypeRepr, <<" ">>) of
        [_] -> TypeRepr;
        [_, _] ->
            <<"(", TypeRepr/binary, ")">>
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
    SubTypeRepr = infer_parens(format_type_arg(ListType)),
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

format_binding(#alpaca_binding{type=Type, name={'Symbol', #{name := Name}}}) ->
    TypeSigRepr = format_type(Type),
    TypeVarsRepr = case re:run(TypeSigRepr, <<"'[a-z]">>,
                              [global, {capture, first, binary}]) of
        nomatch ->
            <<"">>;

        {match, Vars} ->
            TypeVars = lists:usort(lists:map(fun([M]) -> M end, Vars)),
            list_to_binary(lists:join(" ", TypeVars) ++ " ")
    end,
    <<"val ", Name/binary, " ", TypeVarsRepr/binary, ": ", TypeSigRepr/binary>>.

format_type_arg({type_var, _, TVName}) -> list_to_binary("'" ++ TVName);
format_type_arg(none) -> <<"">>;
format_type_arg({alpaca_type_tuple, Args}) ->
    ArgsFmt = lists:map(fun format_type_arg/1, Args),
    Joined = lists:join(", ", ArgsFmt),
    list_to_binary("(" ++ Joined ++ ")");
format_type_arg(#alpaca_type{vars=Vars, name={_, _, Name}}) ->
    TypeVars = case length(Vars) > 0 of
                   true ->
                       VarsFmt = lists:map(fun({type_var, _, TVName}) ->
                                                 "'" ++ TVName;
                                              ({{type_var, _, _}, T}) ->
                                                 format_type_arg(T)
                                           end,
                                           Vars),
                       list_to_binary(" " ++ lists:join(" ", VarsFmt));
                   false ->
                       <<"">>
               end,
    <<Name/binary, TypeVars/binary>>;


format_type_arg(Other) -> format_type(Other).

format_type_def(#alpaca_type{vars=Vars, name={_, _, Name}, members=Members}) ->
    TypeVars = case length(Vars) > 0 of
        true -> list_to_binary(
            lists:join(" ", lists:map(fun({type_var, _, TVName}) ->

                                                " '" ++ TVName
                                            end,
                                            Vars)));
        false -> <<"">>
    end,
    MemberRepr = list_to_binary(lists:join(" | ", lists:map(
        fun
            (#alpaca_constructor{name=#type_constructor{name=N}, arg=none}) ->
                list_to_binary(N);
            (#alpaca_constructor{name=#type_constructor{name=N}, arg=Arg}) ->
                list_to_binary(N ++ " " ++ infer_parens(format_type_arg(Arg)));
            ({type_var, _, _, T}) -> format_type(T);
            (Other) ->
                format_type_arg(Other)
        end,
        Members))),
    <<"type ", Name/binary, TypeVars/binary, " = ", MemberRepr/binary>>.

format_module(#alpaca_module{functions=Funs,
                             name=Name,
                             types=ModTypes,
                             type_exports=TypeExports,
                             function_exports=FunExports}, Opts) ->

    ModName = atom_to_binary(Name, utf8),
    %% Sort funs by line
    SortedFuns = lists:sort(
        fun(#alpaca_binding{name={'Symbol', #{line := L1}}},
            #alpaca_binding{name={'Symbol', #{line := L2}}}) ->
                L1 =< L2
        end,
        Funs),
    {PublicFuns, PrivateFuns} = lists:partition(
        fun(#alpaca_binding{name={'Symbol', #{name := FunName}}, type=T}) ->
            lists:any(fun(N) when is_binary(N) -> N == FunName;
                         ({N, Arity}) ->
                             case T of
                                {t_arrow, Args, _} ->
                                    (N == FunName) and (length(Args) == Arity);
                                _ -> N == FunName
                             end;
                         (_O) -> false
                      end,
                      FunExports)
        end,
        SortedFuns),

    {PublicTypes, PrivateTypes} = lists:partition(
        fun(#alpaca_type{name={_, _, TName}}) ->
                lists:member(TName, TypeExports)
        end,
        ModTypes),
    Bindings = lists:map(fun format_binding/1, PublicFuns),
    BindingsRepr = list_to_binary(lists:join("\n\n", Bindings)),

    Types = lists:reverse(lists:map(fun format_type_def/1, PublicTypes)),
    TypesRepr = list_to_binary(lists:join("\n\n", Types)),
    PublicTypeHeader = <<"-- Exported types\n",
                         "-----------------\n\n">>,
    PublicFunHeader = <<"-- Exported functions\n"
                        "---------------------\n\n">>,
    ModAndPublic = <<"module ", ModName/binary, "\n\n",
      PublicTypeHeader/binary,
      TypesRepr/binary,
      "\n\n",
      PublicFunHeader/binary,
      BindingsRepr/binary,
      "\n">>,

    case lists:member(internal, Opts) of
        false ->
            ModAndPublic;
        true  ->
            PrivateTypeHeader =
                <<"\n-- Internal types\n"
                  "-----------------\n\n">>,

            PrivateFunHeader =
                <<"-- Internal functions\n"
                  "---------------------\n\n">>,

            PrivateTypesMap =
                lists:reverse(lists:map(fun format_type_def/1, PrivateTypes)),
            PrivateTypesRepr =
                list_to_binary(lists:join("\n\n", PrivateTypesMap)),

            PrivateBindings = lists:map(fun format_binding/1, PrivateFuns),
            PrivateBindingsRepr = list_to_binary(lists:join("\n\n", PrivateBindings)),

            <<ModAndPublic/binary,
              PrivateTypeHeader/binary,
              PrivateTypesRepr/binary,
              "\n\n",
              PrivateFunHeader/binary,
              PrivateBindingsRepr/binary,
              "\n">>
    end;


format_module(Name, Opts) when is_atom(Name) ->
    Attrs = Name:module_info(attributes),
    Module = proplists:get_value(alpaca_typeinfo, Attrs),
    format_module(Module, Opts).

format_module(Module) ->
    format_module(Module, []).

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

simple_binding_test() ->
    [Binding] = get_bindings("module types;; let add x y = x + y"),
    ?assertMatch(<<"val add : fn int int -> int">>, format_binding(Binding)).

parameterized_binding_test() ->
    [Binding] = get_bindings("module types;; let identity a = a"),
    ?assertMatch(<<"val identity 'a : fn 'a -> 'a">>, format_binding(Binding)).

format_module_test() ->
    Code = "module my_lovely_lovely_mod\n"
           "export hello, add, pair, identity\n"
           "export_type maybe\n"
           "export_type alias\n"
           "export_type my_tuple\n"
           "export_type others\n"
           "type maybe 'a = Just 'a | Nothing\n"
           "type alias = int\n"
           "type my_tuple = (int, int)\n"
           "type others = (maybe int, alias)\n"
          " type compound = MyList (string, (list alias))\n"
           "type mixed = HaveTuple (maybe my_tuple)\n"
           "let hello = \"hello world\""
           "let add x y = x + y\n"
           "val pair : fn int -> my_tuple\n"
           "let pair x = (x, x)\n"
           "let identity x = x\n"
           "let private () = :private",
    {ok, Res} = alpaca:compile({text, Code}),
    [{compiled_module, N, FN, Bin}] = Res,
    {module, N} = code:load_binary(N, FN, Bin),
    ModAndExported =
        <<"module my_lovely_lovely_mod\n\n"
          "-- Exported types\n"
          "-----------------\n\n"
          "type maybe 'a = Just 'a | Nothing\n\n"
          "type alias = int\n\n"
          "type my_tuple = (int, int)\n\n"
          "type others = (maybe int, alias)\n\n"
          "-- Exported functions\n"
          "---------------------\n\n"
          "val hello : string\n\n"
          "val add : fn int int -> int\n\n"
          "val pair : fn int -> my_tuple\n\n"
          "val identity 'a : fn 'a -> 'a\n"
        >>,

    ?assertEqual(ModAndExported, format_module(N)),

    Internal =
        <<"\n-- Internal types\n"
          "-----------------\n\n"
          "type compound = MyList (string, list alias)\n\n"
          "type mixed = HaveTuple (maybe my_tuple)\n\n"
          "-- Internal functions\n"
          "---------------------\n\n"
          "val private : fn () -> atom\n"
        >>,

    ModExportedAndInternal =
        <<ModAndExported/binary, Internal/binary>>,

    ?assertEqual(ModExportedAndInternal, format_module(N, [internal])).

from_module_test() ->
    Code = "module types\n"
           "val apply 'a 'b : fn (fn 'a -> 'b) 'a -> 'b\n"
           "let apply f x = f x\n"
           "type maybe 'a = Just 'a | Nothing\n"
           "let just something = Just something\n"
           "let make_map x = #{\"key\" => x * x}\n"
           "let make_receiver x = receive with y -> x * y\n"
           "let make_pid () = spawn make_receiver 10",

    Funs = get_bindings(Code),

    [#alpaca_binding{type=PidType},
     #alpaca_binding{type=ReceiverType},
     #alpaca_binding{type=MapType},
     #alpaca_binding{type=JustType},
     #alpaca_binding{type=ApplyType}] = Funs,

    ?assertMatch(<<"fn (fn 'a -> 'b) 'a -> 'b">>, format_type(ApplyType)),
    ?assertMatch(<<"fn 'a -> maybe 'a">>, format_type(JustType)),
    ?assertMatch(<<"fn int -> map string int">>, format_type(MapType)),
    ?assertMatch(<<"fn () -> pid int">>, format_type(PidType)),
    ?assertMatch(<<"receiver int (fn int -> int)">>, format_type(ReceiverType)).

get_bindings(Code) ->
    {ok, Res} = alpaca:compile({text, Code}),
    [{compiled_module, N, FN, Bin}] = Res,
    {module, N} = code:load_binary(N, FN, Bin),
    Attrs = N:module_info(attributes),
    Types = proplists:get_value(alpaca_typeinfo, Attrs),
    code:purge(N),
    #alpaca_module{functions=Funs} = Types,
    Funs.

-endif.
