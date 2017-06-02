%% Performs exhaustiveness checking of pattern matches.
%%
%% Only deals with top level functions, as the typer currently does not
%% expose type information on the expression level.
-module(alpaca_exhaustiveness).

-export([check_exhaustiveness/1]).
-export([print_warning/1]).

-include("alpaca_ast.hrl").

-type pattern() :: {missing_pattern, term()}.
-type warning() :: {partial_function, warning_mfa(), [pattern()]}.
-type warning_mfa() :: {Mod::atom(), Fun::string(), Arity::non_neg_integer()}.

print_warning({partial_function, {M, F, A}, Patterns}) ->
    io:format("Warning: Partial function ~p.~s/~w. Missing patterns:~n",
              [M, F, A]),
    lists:foreach(fun(P) ->  print_pattern(P, F) end, Patterns).

print_pattern({missing_pattern, Args}, FName) ->
    Formatted = lists:map(fun format_pattern/1, Args),
    io:format("  let ~s ~s = ...~n", [FName, string:join(Formatted, " ")]).

format_pattern({t_adt_cons, C, none}) -> C;
format_pattern({t_adt_cons, C, Arg})  ->
    "(" ++ C ++ " " ++ format_pattern(Arg) ++ ")";
format_pattern({t_bool, Bool}) -> atom_to_list(Bool);
format_pattern({t_list, empty}) -> "[]";
format_pattern({t_list, P}) ->
    "(" ++ format_pattern(P) ++ " :: _)";
format_pattern(t_map) -> "#{}";
format_pattern({t_tuple, Elems}) ->
    Parts = lists:map(fun(E) -> format_pattern(E) end, Elems),
    "(" ++ string:join(Parts, ", ") ++ ")";
format_pattern(t_unit) -> "()";
format_pattern({t_record, Assignments}) ->
    Fields = lists:map(fun({K, V}) ->
             atom_to_list(K) ++ " = " ++ format_pattern(V) end,
           maps:to_list(Assignments)),
    "{ " ++ string:join(Fields, ", ") ++ " }";
format_pattern('_') -> "_".

-spec check_exhaustiveness([alpaca_module()]) -> [warning()].
check_exhaustiveness(Mods) ->
    lists:flatmap(fun(M) -> check_exhaustiveness(M, Mods) end, Mods).

check_exhaustiveness(#alpaca_module{functions=Funs}=M, AllMods) ->
    lists:flatmap(fun(F) -> check_exhaustiveness(M, F, AllMods) end, Funs).

check_exhaustiveness(Mod, #alpaca_binding{type=Type, bound_expr=Bound}=F, AllMods) ->
    case Bound of
        #alpaca_fun{} ->
            case Type of
                {t_arrow, FunArgTypes, _}                  ->
                    check_exhaustiveness(Mod, F, FunArgTypes, AllMods);
                {t_receiver, _, {t_arrow, FunArgTypes, _}} ->
                    check_exhaustiveness(Mod, F, FunArgTypes, AllMods);
                _                                         -> % Top level value
                    []
            end;
        _ ->
            []
    end.

check_exhaustiveness(Mod, #alpaca_binding{
                             name={'Symbol', _}=Sym,
                             bound_expr=#alpaca_fun{}=F},
                     FunArgTypes, AllMods) ->
    Name = alpaca_ast:symbol_name(Sym),
    #alpaca_fun{arity=Arity, versions=FunArgPatterns} = F,
    case missing_patterns(Mod, FunArgTypes, FunArgPatterns, AllMods) of
        []              ->
            [];
        MissingPatterns ->
            MFA = {Mod#alpaca_module.name, Name, Arity},
            [{partial_function, MFA, MissingPatterns}]
    end.

missing_patterns(Mod, FunArgTypes, FunArgPatterns, AllMods) ->
    CoveringPatterns = covering_patterns(FunArgTypes, Mod, AllMods),
    ProvidedPatterns = extract_patterns(FunArgPatterns),
    lists:flatmap(fun({t_tuple, FunArgs}=CovP) ->
        case lists:any(fun(P) -> covered(CovP, P) end, ProvidedPatterns) of
            true  -> [];
            false -> [{missing_pattern, FunArgs}]
        end
      end, CoveringPatterns).

covering_patterns(FunArgTypes, Mod, AllMods) ->
    covering_patterns({t_tuple, FunArgTypes}, Mod, AllMods, sets:new(), []).

covering_patterns(#adt{name=Name, vars=Vars}, Mod, AllMods, SeenADTs, _Vars) ->
    wildcard_if_seen(Name, Mod, AllMods, SeenADTs, Vars);
covering_patterns(#alpaca_type{members=[], name={type_name, _, Name},
                               vars=Vars}, Mod, AllMods, SeenADTs, _Vars) ->
    wildcard_if_seen(Name, Mod, AllMods, SeenADTs, Vars);
covering_patterns(#alpaca_type{members=Members}, Mod, AllMods, SeenADTs,
                  Vars) ->
    lists:flatmap(fun(C) ->
        covering_patterns(C, Mod, AllMods, SeenADTs, Vars)
    end, Members);
covering_patterns(#alpaca_type_tuple{members=Members}, Mod, AllMods, SeenADTs,
                  Vars) ->
    covering_patterns({t_tuple, Members}, Mod, AllMods, SeenADTs, Vars);
covering_patterns(#alpaca_constructor{name=#type_constructor{name=N}, arg=none},
                  _Mod, _AllMods, _SeenADTs, _Vars) ->
    [{t_adt_cons, N, none}];
covering_patterns(#alpaca_constructor{name=#type_constructor{name=N}, arg=Arg},
             Mod, AllMods, SeenADTs, Vars) ->
    ArgPatterns = covering_patterns(Arg, Mod, AllMods, SeenADTs, Vars),
    lists:map(fun(A) -> {t_adt_cons, N, A} end, ArgPatterns);
covering_patterns({t_arrow, _, _}, _Mod, _AllMods, _SeenADTs, _Vars) ->
    ['_'];
covering_patterns(t_atom, _Mod, _AllMods, _SeenADTs, _Vars) ->
    ['_'];
covering_patterns(t_binary, _Mod, _AllMods, _SeenADTs, _Vars) ->
    ['_'];
covering_patterns(t_bool, _Mod, _AllMods, _SeenADTs, _Vars) ->
    [{t_bool, true}, {t_bool, false}];
covering_patterns(t_chars, _Mod, _AllMods, _SeenADTs, _Vars) ->
    ['_'];
covering_patterns(t_float, _Mod, _AllMods, _SeenADTs, _Vars) ->
    ['_'];
covering_patterns(t_int, _Mod, _AllMods, _SeenADTs, _Vars) ->
    ['_'];
covering_patterns({t_list, Elem}, Mod, AllMods, SeenADTs, Vars) ->
    ElemPatterns = covering_patterns(Elem, Mod, AllMods, SeenADTs, Vars),
    Base = lists:map(fun(E) -> {t_list, E} end, ElemPatterns),
    [{t_list, empty}|Base];
%% We explicitly ignore maps.
%% Consider this example:
%%   let foo #{true => false,  false => true} = ...
%%
%% The most helpful patterns to report would be:
%%   let foo #{true => false, false => false} = ...
%%   let foo #{true => true, false => true } = ...
%%   let foo #{true => true, false => false } = ...
%%
%% However, to do this, we would need to know all the keys that are used
%% in the patterns, and we do not get that information from the type.
covering_patterns({t_map, _KeyT, _ValT}, _Mod, _AllMods, _SeenADTs, _Vars) ->
    [t_map];
covering_patterns(#t_record{members=Ms}, Mod, AllMods, SeenADTs, Vars) ->
    Assignments = record_field_assignments(Ms, Mod, AllMods, SeenADTs, Vars),
    lists:map(fun(A) -> {t_record, A} end, Assignments);
covering_patterns(t_string, _Mod, _AllMods, _SeenADTs, _Vars) ->
    ['_'];
covering_patterns({t_tuple, Ms}, Mod, AllMods, SeenADTs, Vars) ->
    lists:map(fun(A) -> {t_tuple, maps:values(A)} end,
              tuple_patterns(Ms, 1, Mod, AllMods, SeenADTs, Vars));
covering_patterns(t_unit, _Mod, _AllMods, _SeenADTs, _Vars) ->
    [t_unit];
covering_patterns({type_var, _, Var}, Mod, AllMods, SeenADTs, Vars) ->
    {Var, C} = lists:keyfind(Var, 1, Vars),
    covering_patterns(C, Mod, AllMods, SeenADTs, Vars);
covering_patterns({unbound, _, _}, _Mod, _AllMods, _SeenADTs, _Vars) ->
    ['_'].

wildcard_if_seen(Name, Mod, AllMods, SeenADTs0, Vars) ->
    case sets:is_element(Name, SeenADTs0) of
        true  ->
            ['_'];
        false ->
            {ok, T} = lookup_type(Name, Mod, AllMods),
            SeenADTs = sets:add_element(Name, SeenADTs0),
            %% User-defined ADTs may bind concrete types or new variable names
            %% to existing ADT variables, causing name lookup failures.  Here
            %% we replace any user-supplied or synthetic names with the original
            %% type definition's variable names so that lookup in
            %% covering_patterns/5 does not fail.
            Vars2 = case T of
                        #alpaca_type{vars=Vs} ->
                            F = fun({{type_var, _, _}, ActualV}) -> ActualV;
                                   ({{_, Bound}, {_, _, ActualV}}) -> {ActualV, Bound}
                                end,
                            lists:map(F, lists:zip(Vars, Vs));
                        _ ->
                            Vars
                    end,
            covering_patterns(T, Mod, AllMods, SeenADTs, Vars2)
    end.

lookup_type(Name, Mod, AllMods) ->
  case lookup_type(Mod#alpaca_module.types, Name) of
     {ok, _}=Res    ->
        Res;
     {not_found, _} ->
        lookup_type_from_imports(Name, Mod, AllMods)
  end.

lookup_type([], Name) ->
    {not_found, Name};
lookup_type([#alpaca_type{name={type_name, _, Name}}=T|_], Name) ->
    {ok, T};
lookup_type([_|Rest], Name) ->
    lookup_type(Rest, Name).

lookup_type_from_imports(Name, #alpaca_module{type_imports=Imports},
                         AllMods) ->
    case lists:keyfind(Name, #alpaca_type_import.type, Imports) of
        #alpaca_type_import{module=ModName} ->
            Mod = lists:keyfind(ModName, #alpaca_module.name, AllMods),
            lookup_type(Mod#alpaca_module.types, Name);
        false -> % abstract/hidden type in another module.
            {ok, {unbound, '_', 1}}
    end.

record_field_assignments([], _Mod, _AllMods, _SeenADTs, _Vars) ->
    [#{}];
record_field_assignments([#t_record_member{name=Key, type=T}|Rest], Mod,
                          AllMods, SeenADTs,
            Vars) ->
    RestAssignments = record_field_assignments(Rest, Mod, AllMods, SeenADTs,
                                               Vars),
    lists:flatmap(fun(C) ->
        lists:map(fun(A) -> maps:put(Key, C, A) end, RestAssignments)
    end, covering_patterns(T, Mod, AllMods, SeenADTs, Vars)).

tuple_patterns([], _Ix, _Mod, _AllMods, _SeenADTs, _Vars) ->
    [#{}];
tuple_patterns([T|Rest], Ix, Mod, AllMods, SeenADTs, Vars) ->
    RestPatterns = tuple_patterns(Rest, Ix+1, Mod, AllMods, SeenADTs, Vars),
    lists:flatmap(fun(C) ->
        lists:map(fun(A) -> maps:put(Ix, C, A) end, RestPatterns)
    end, covering_patterns(T, Mod, AllMods, SeenADTs, Vars)).

extract_patterns(FunArgPatterns) ->
    lists:map(fun(#alpaca_fun_version{args=Args}) ->
          #alpaca_tuple{values=Args}
        end, FunArgPatterns).

covered('_', Pattern) ->
    matches_wildcard(Pattern);
covered({t_adt_cons, Name, PArg}, Pattern) ->
    matches_constructor(Pattern, Name, PArg);
covered({t_bool, Boolean}, Pattern) ->
    matches_bool(Pattern, Boolean);
covered({t_list, empty}, Pattern) ->
    matches_empty_list(Pattern);
covered({t_list, Elem}, Pattern) ->
    matches_list(Pattern, Elem);
covered(t_map, _Pattern) ->
    true;
covered({t_record, Assignments}, Pattern) ->
    matches_record(Pattern, Assignments);
covered({t_tuple, Members}, Pattern) ->
    matches_tuple(Pattern, Members);
covered(t_unit, Pattern) ->
    matches_unit(Pattern).

matches_bool({boolean, _, Bool}, Bool) ->
    true;
matches_bool(Other, _Bool) ->
    matches_wildcard(Other).

matches_constructor(#alpaca_type_apply{name=#type_constructor{name=Name},
                                       arg=none}, Name, none) ->
    true;
matches_constructor(#alpaca_type_apply{name=#type_constructor{name=Name},
                                       arg=Arg}, Name, PArg) ->
    covered(PArg, Arg);
matches_constructor(P, _Name, _PArg) ->
    matches_wildcard(P).

matches_empty_list({nil, _}) ->
    true;
matches_empty_list(P) ->
    matches_wildcard(P).

matches_list(#alpaca_cons{head=H, tail=T}, E) ->
    covered(E, H) andalso matches_wildcard(T);
matches_list(P, _E) ->
    matches_wildcard(P).

matches_record(#alpaca_record{members=Ms}, Assignments) ->
    lists:all(fun(#alpaca_record_member{name=N, val=P}) ->
        covered(maps:get(N, Assignments), P)
    end, Ms);
matches_record(P, _Assignments) ->
    matches_wildcard(P).

matches_tuple(#alpaca_tuple{values=Patterns}, TElems) ->
    matches(Patterns, TElems);
matches_tuple(P, _TElems) ->
    matches_wildcard(P).

matches([], []) -> true;
matches([Pattern|Patterns], [CP|CPs]) ->
    covered(CP, Pattern) andalso matches(Patterns, CPs).

matches_unit({unit, _}) ->
    true;
matches_unit(P) ->
    matches_wildcard(P).

matches_wildcard({'_', _}) ->
    true;
matches_wildcard({'Symbol', _}) ->
    true;
matches_wildcard(_)              ->
    false.

-ifdef(TEST).

-include_lib("eunit/include/eunit.hrl").

atom_coverage_test() ->
    Code =
        "module coverage\n\n"
        "let complete_wildcard :ok = :ok\n"
        "let complete_wildcard _ = :ok\n\n"
        "let missing_wildcard :ok = :ok\n\n",
    ?assertMatch([
        {partial_function, {coverage, <<"missing_wildcard">>, 1},
         [{missing_pattern,['_']}]}
      ], run_checks([Code])).

arrow_coverage_test() ->
    Code =
        "module coverage\n\n"
        "let complete_wildcard f = (f 1) + 1\n\n",
    ?assertMatch([], run_checks([Code])).

binary_coverage_test() ->
    Code =
        "module coverage\n\n"
        "let complete_wildcard <<\"\">> = :ok\n"
        "let complete_wildcard _ = :ok\n\n"
        "let missing_wildcard <<\"\">> = :ok\n\n",
    ?assertMatch([
        {partial_function, {coverage, <<"missing_wildcard">>, 1},
         [{missing_pattern,['_']}]}
      ], run_checks([Code])).

boolean_coverage_test() ->
    Code =
        "module coverage\n\n"
        "let complete_boolean true = :ok\n"
        "let complete_boolean false = :ok\n\n"
        "let complete_wildcard false = :ok\n"
        "let complete_wildcard _ = :ok\n\n"
        "let missing_true false = :ok\n\n"
        "let missing_false false = :ok\n\n",
    ?assertMatch([
        {partial_function, {coverage, <<"missing_true">>, 1},
         [{missing_pattern,[{t_bool,true}]}]},
        {partial_function, {coverage, <<"missing_false">>, 1},
         [{missing_pattern,[{t_bool,true}]}]}
      ], run_checks([Code])).

erlang_string_coverage_test() ->
    Code =
        "module coverage\n\n"
        "let complete_wildcard c\"\" = :ok\n"
        "let complete_wildcard _ = :ok\n\n"
        "let missing_wildcard c\"\" = :ok\n\n",
    ?assertMatch([
        {partial_function, {coverage, <<"missing_wildcard">>, 1},
         [{missing_pattern,['_']}]}
      ], run_checks([Code])).

float_coverage_test() ->
    Code =
        "module coverage\n\n"
        "let complete_wildcard 1.0 = :ok\n"
        "let complete_wildcard _ = :ok\n\n"
        "let missing_wildcard 1.0 = :ok\n\n",
    ?assertMatch([
        {partial_function, {coverage, <<"missing_wildcard">>, 1},
         [{missing_pattern,['_']}]}
      ], run_checks([Code])).

int_coverage_test() ->
    Code =
        "module coverage\n\n"
        "let complete_wildcard 1 = :ok\n"
        "let complete_wildcard _ = :ok\n\n"
        "let missing_wildcard 1 = :ok\n\n",
    ?assertMatch([
        {partial_function, {coverage, <<"missing_wildcard">>, 1},
         [{missing_pattern,['_']}]}
      ], run_checks([Code])).

string_coverage_test() ->
    Code =
        "module coverage\n\n"
        "let complete_wildcard \"\" = :ok\n"
        "let complete_wildcard _ = :ok\n\n"
        "let missing_wildcard \"\" = :ok\n\n",
    ?assertMatch([
        {partial_function, {coverage, <<"missing_wildcard">>, 1},
         [{missing_pattern,['_']}]}
      ], run_checks([Code])).

unit_coverage_test() ->
    Code =
        "module coverage\n\n"
        "let complete_unit () = :ok\n\n",
    ?assertMatch([], run_checks([Code])).

tuple_coverage_test() ->
    Code =
        "module coverage\n\n"
        "let complete (true, true) = :ok\n"
        "let complete (true, false) = :ok\n"
        "let complete (false, true) = :ok\n"
        "let complete (false, false) = :ok\n"
        "let complete_wildcard (true, _) = :ok\n"
        "let complete_wildcard _ = :ok\n\n"
        "let missing (true, true) = :ok\n"
        "let missing (false, _) = :ok\n\n",
    ?assertMatch([
        {partial_function, {coverage, <<"missing">>, 1},
         [{missing_pattern,[{t_tuple,[{t_bool,true},{t_bool,false}]}]}]}
      ], run_checks([Code])).

list_coverage_test() ->
    Code =
        "module coverage\n\n"
        "let complete_wildcard [] = :ok\n"
        "let complete_wildcard _ :: _ = :ok\n\n"
        "let missing [true, false] = :ok\n\n",
    ?assertMatch([
        {partial_function, {coverage, <<"missing">>, 1},
         [{missing_pattern,[{t_list, empty}]},
          {missing_pattern,[{t_list, {t_bool, true}}]},
          {missing_pattern,[{t_list, {t_bool, false}}]}]}
      ], run_checks([Code])).

map_coverage_test() ->
    Code =
        "module coverage\n\n"
        "let missing #{true => false} = :ok\n\n",
    ?assertMatch([], run_checks([Code])).

record_coverage_test() ->
    Code =
        "module coverage\n\n"
        "let complete {x = ()} = :ok\n\n"
        "let complete_wildcard {x = false, y = true} = :ok\n"
        "let complete_wildcard _ = :ok\n\n"
        "let missing {x = false, y = false} = :ok\n"
        "let missing {x = true} = :ok\n\n",
    ?assertMatch([
        {partial_function, {coverage, <<"missing">>, 1},
         [{missing_pattern,
           [{t_record, #{x := {t_bool, false}, y := {t_bool, true}}}]}]}
      ], run_checks([Code])).

basic_adt_coverage_test() ->
    Code =
        "module coverage\n\n"
        "type color = Red | Green | Blue\n\n"
        "let complete Red = :ok\n"
        "let complete Green = :ok\n"
        "let complete Blue = :ok\n\n"
        "let complete_wildcard Red = :ok\n"
        "let complete_wildcard color = :ok\n\n"
        "let missing Red = :ok\n\n",
    ?assertMatch([
        {partial_function, {coverage, <<"missing">>, 1},
         [{missing_pattern,[{t_adt_cons,"Green",none}]},
          {missing_pattern,[{t_adt_cons,"Blue",none}]}]}
      ], run_checks([Code])).

parameterized_adt_coverage_test() ->
    Code =
        "module coverage\n\n"
        "type option 'a = None | Some 'a\n\n"
        "let complete None = :ok\n"
        "let complete (Some false) = :ok\n"
        "let complete (Some true) = :ok\n\n"
        "let complete_wildcard (Some false) = :ok\n"
        "let complete_wildcard _ = :ok\n\n"
        "let missing (Some false) = :ok\n\n",
    ?assertMatch([
        {partial_function, {coverage, <<"missing">>, 1},
         [{missing_pattern,[{t_adt_cons,"None",none}]},
          {missing_pattern,[{t_adt_cons,"Some",{t_bool, true}}]}]}
      ], run_checks([Code])).

recursive_adt_test() ->
    Code =
        "module coverage\n\n"
        "type tree = Leaf | Tree (tree, bool, tree)\n\n"
        "let complete Leaf = :ok\n"
        "let complete (Tree (_, true, _)) = :ok\n"
        "let complete (Tree (_, false, _)) = :ok\n\n"
        "let complete_wildcard Leaf = :ok\n"
        "let complete_wildcard _ = :ok\n\n"
        "let missing (Tree (Leaf, false, _)) = :ok\n\n",
    ?assertMatch([
        {partial_function, {coverage, <<"missing">>, 1},
         [{missing_pattern,[{t_adt_cons,"Leaf",none}]},
          {missing_pattern,[{t_adt_cons,"Tree",{t_tuple, ['_', {t_bool, true}, '_']}}]},
          {missing_pattern,[{t_adt_cons,"Tree",{t_tuple, ['_', {t_bool, false}, '_']}}]}
         ]}], run_checks([Code])).

multi_arg_test() ->
    Code =
        "module coverage\n\n"
        "let complete true true true = :ok\n"
        "let complete true true false = :ok\n"
        "let complete true false true = :ok\n"
        "let complete true false false = :ok\n"
        "let complete false true true = :ok\n"
        "let complete false true false = :ok\n"
        "let complete false false true = :ok\n"
        "let complete false false false = :ok\n"
        "let complete_wildcard true true true = :ok\n"
        "let complete_wildcard _ _ _ = :ok\n\n"
        "let missing false true false = :ok\n"
        "let missing true _ _ = :ok\n\n",
    ?assertMatch([
        {partial_function, {coverage, <<"missing">>, 3},
         [{missing_pattern, [{t_bool,false},{t_bool,true},{t_bool,true}]},
          {missing_pattern, [{t_bool,false},{t_bool,false},{t_bool,true}]},
          {missing_pattern, [{t_bool,false},{t_bool,false},{t_bool,false}]}
         ]}], run_checks([Code])).

imported_type_test() ->
    Mod1 =
        "module provider\n\n"
        "type color = Red | Green | Blue\n\n"
        "export_type color",
    Mod2 =
        "module consumer\n\n"
        "import_type provider.color\n\n"
        "let missing Red = :ok\n"
        "let missing Blue = :ok\n\n",
    ?assertMatch([
        {partial_function, {consumer, <<"missing">>, 1},
         [{missing_pattern, [{t_adt_cons, "Green", none}]}
         ]}], run_checks([Mod1, Mod2])).

foreign_type_test() ->
    Mod1 =
        "module provider\n\n"
        "export is_color_of_grass/1\n\n"
        "type color = Red | Green | Blue\n\n"
        "let is_color_of_grass Green = true\n"
        "let is_color_of_grass _ = false\n\n",
    Mod2 =
        "module consumer\n\n"
        "let complete color = provider.is_color_of_grass color\n\n",
    ?assertMatch([], run_checks([Mod1, Mod2])).

receiver_test() ->
    Code =
        "module coverage\n\n"
        "let missing true = receive with\n"
        "  i, is_integer i -> :ok\n\n",
    ?assertMatch([
        {partial_function, {coverage, <<"missing">>, 1},
         [{missing_pattern, [{t_bool, false}]}
         ]}], run_checks([Code])).

top_level_value_test() ->
    Code =
        "module coverage\n\n"
        "let one = 1\n\n",
    ?assertMatch([], run_checks([Code])).


run_checks(ModeCodeListings) ->
    NamedSources = lists:map(fun(C) -> {?FILE, C} end, ModeCodeListings),
    {ok, ParsedMods} = alpaca_ast_gen:make_modules(NamedSources),
    {ok, TypedMods} = alpaca_typer:type_modules(ParsedMods),
    Warnings = check_exhaustiveness(TypedMods),
    %% To test the formatter does not crash
    lists:foreach(fun print_warning/1, Warnings),
    Warnings.
-endif.
