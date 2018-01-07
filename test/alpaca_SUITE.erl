-module(alpaca_SUITE).

%%-compile(export_all).

-export([
         all/0,
         proper_compile/1,
         g_function/0,
         g_function_name/0,
         g_function_body/0,
         g_basic_value/0,
         g_boolean/0,
         g_number/0,
         g_float/0,
         g_atom/0,
         g_string/0,
         g_char_list/0,
         g_binary/0
        ]).

-include_lib("common_test/include/ct.hrl").
-include_lib("proper/include/proper.hrl").
-include_lib("eunit/include/eunit.hrl").

all() -> [proper_compile].

proper_compile(_Config) ->
    NumTests = list_to_integer(os:getenv("NUMTESTS", "1000")),
    ?assert(proper:quickcheck(prop_can_compile_module_def(), [{numtests, NumTests}])),
    ?assert(proper:quickcheck(prop_can_compile_type_decl(), [{numtests, NumTests},
                                                             {max_size, 10}
                                                            ])).

prop_can_compile_module_def() ->
    ?FORALL(ModuleDef, g_module_def(), can_compile(ModuleDef)).

g_module_def() ->
    ?LET(Module, g_module(), to_binary([Module], [])).

prop_can_compile_type_decl() ->
    ?FORALL(Code, g_module_with_type_declaration(), can_compile(Code)).

g_module_with_type_declaration() ->
    ?LET({Module,
          TypeDecl},
         {g_module(),
          g_type_declaration([])},
         ?LET(MoreTypeDecl, g_type_declaration([TypeDecl]),
              to_binary([Module, TypeDecl, MoreTypeDecl], []))).

can_compile(Code) ->
    ?WHENFAIL(ct:pal("failed to compile:~n~ts~n", [Code]),
              ?TIMEOUT(timer:seconds(5),
                       case alpaca:compile({text, Code}) of
                           {ok, _} -> true;
                           {error, _} -> false
                       end)).

%%% Module generators

%% @doc Generate module declaration.
g_module() ->
    ?LET(Mod, g_module_name(), {module, Mod}).

%% @doc Generate a module name.
%% Module names are turned into atoms. The module name is internally prefixed
%% with 'alpaca_'. Atom max length is 255.
%% @end
g_module_name() ->
    ?LET(N, integer(1, 248),
         ?LET(Module,
              ?SUCHTHAT(Name, g_sym(N), not lists:member(Name, keywords())),
              Module)).

%%% Type generators

g_type_declaration(KnownTypes) ->
    ?LET({Name, Params}, {g_type_name(KnownTypes), list(g_type_param())},
         ?LET(Type, ?SUCHTHAT(T, g_type_top_level_def(Name, Params, KnownTypes),
                              is_valid_type(T, KnownTypes)),
              {type, Name, Params, Type})).

is_valid_type(Type, KnownTypes) ->
    Constructors = lists:flatten(extract_constructors(Type) ++
                                 [extract_constructors(T) || T <- KnownTypes]),
    %% unique constructors
    is_unique(Constructors).

g_type_name(KnownTypes) ->
    ?LET(TypeName,
         ?SUCHTHAT(Name, g_sym(), is_valid_type_name(Name, KnownTypes)),
         TypeName).

is_valid_type_name(Name, KnownTypes) ->
    %% unique type name
    not lists:member(Name, [extract_type_name(T) || T <- KnownTypes])
    andalso
    %% name is not a keyword
    not lists:member(Name, keywords()).

g_type_param() ->
    ?LET(Param, g_sym(), list_to_binary([$', Param])).

g_type_top_level_def(Name, Params, KnownTypes) ->
    ?SIZED(Size, g_type_top_level_def(Name, Params, KnownTypes, Size)).
g_type_top_level_def(Name, Params, KnownTypes, 0) ->
    oneof([g_type_constructor_name(),
           g_type_def(Name, Params, KnownTypes),
           g_type_construct(g_type_def(Name, Params, KnownTypes))]);
g_type_top_level_def(Name, Params, KnownTypes, Size) ->
    oneof([g_type_top_level_def(Name, Params, KnownTypes, 0),
           ?LAZY(g_type_union(Name, Params, KnownTypes, Size))
          ]).

g_type_construct(Of) ->
    ?LET(Constructor, g_type_constructor_name(),
         {construct, Constructor, Of}).

g_type_constructor_name() ->
    ?LET(N, non_neg_integer(),
         ?LET({U, Rest},
              {g_u(), vector(N, oneof([g_d(), g_l(), g_u(), $_]))},
              {constructor, list_to_binary([U, Rest])})).

g_type_union(Name, Params, KnownTypes, 1) ->
    g_type_top_level_def(Name, Params, KnownTypes, 0);
g_type_union(Name, Params, KnownTypes, Size) ->
    ?LET(OfTypes, vector(Size, g_type_top_level_def(Name, Params, KnownTypes, 0)),
         {union, OfTypes}).

g_type_def(Name, Params, KnownTypes) ->
    ?SIZED(Size, g_type_def(Name, Params, KnownTypes, Size)).

g_type_def(Name, Params, KnownTypes, 0) ->
    oneof([g_base_type(),
           Name
          ]
          ++ [oneof(Params) || length(Params) > 0]
          ++ [oneof([extract_type_name(KnownType) || KnownType <- KnownTypes])
              || length(KnownTypes) > 0]
         );
g_type_def(Name, Params, KnownTypes, Size) ->
    oneof([g_type_def(Name, Params, KnownTypes, 0),
           ?LAZY(g_type_list(g_type_def(Name, Params, KnownTypes, Size div 2))),
           ?LAZY(g_type_map(g_type_def(Name, Params, KnownTypes, Size div 2),
                            g_type_def(Name, Params, KnownTypes, Size div 2))),
           ?LAZY(g_type_pid(g_type_def(Name, Params, KnownTypes, Size div 2))),
           ?LAZY(g_type_tuple(Name, Params, KnownTypes, Size div 2)),
           ?LAZY(g_type_record(Name, Params, KnownTypes, Size div 2))
          ]).

g_base_type() ->
    oneof(base_types()).

g_type_list(Of) ->
    {list, Of}.

g_type_map(KeyType, ValueType) ->
    {map, KeyType, ValueType}.

g_type_pid(Of) ->
    {pid, Of}.

g_type_tuple(Name, Params, KnownTypes, N) when N =< 1 ->
    g_type_def(Name, Params, KnownTypes, 0);
g_type_tuple(Name, Params, KnownTypes, Size) ->
    ?LET(OfTypes,
         vector(Size, g_type_def(Name, Params, KnownTypes, Size div 2)),
         {tuple, OfTypes}).

g_type_record(Name, Params, KnownTypes, N) when N =< 0 ->
    g_type_def(Name, Params, KnownTypes, 0);
g_type_record(Name, Params, KnownTypes, Size) ->
   ?LET({Keys, OfTypes},
        {?SUCHTHAT(Symbols, vector(Size, g_record_key()), is_unique(Symbols)),
         vector(Size, g_type_def(Name, Params, KnownTypes, Size div 2))},
        {record, Keys, OfTypes}).

g_record_key() ->
    ?LET(N,
	 integer(1, 255),
	 ?SUCHTHAT(Name, g_sym(N), not lists:member(Name, keywords()))).

to_binary([], Acc) ->
    g_sprinkle(lists:flatten(lists:reverse(Acc)));
to_binary([{module, Mod} | Rest], Acc) ->
    to_binary(Rest, [[<<"module">> , Mod, g_breaks()]| Acc]);
to_binary([{type, Name, Params, Type} | Rest], Acc) ->
    to_binary(Rest,
              [[<<"type">>, Name, Params, $=, to_binary(Type), g_breaks()] | Acc]).

to_binary({construct, Constructor, Of}) ->
    [to_binary(Constructor), to_binary(Of)];
to_binary({union, OfTypes}) ->
    lists:join($|, [to_binary(Type) || Type <- OfTypes]);
to_binary({list, Of}) ->
    [<<"list">>, $(, to_binary(Of), $)];
to_binary({map, KeyType, ValueType}) ->
    [<<"map">>, $(, to_binary(KeyType), $), $(, to_binary(ValueType), $)];
to_binary({pid, Of}) ->
    [<<"pid">>, $(, to_binary(Of), $)];
to_binary({tuple, OfTypes}) ->
    [$(, lists:join($,, [to_binary(Type) || Type <- OfTypes]), $)];
to_binary({record, Keys, OfTypes}) ->
    [${, lists:join($,, [[K, $:, to_binary(T)] || {K, T} <- lists:zip(Keys, OfTypes)]), $}];
to_binary({constructor, Constructor}) ->
    Constructor;
to_binary(Binary) when is_binary(Binary) ->
    Binary.

%%% Function generators

g_function() ->
    ?LET({Name, Body},
         {g_function_name(), g_function_body()},
         {function, Name, Body}).

g_function_name() ->
    ?LET(Fun, g_sym(), Fun).

g_function_body() ->
    g_basic_value().

%%% Value generators

%% Basic values

g_basic_value() ->
    oneof([g_boolean(), g_number(), g_atom(), g_string(), g_char_list(),
           g_binary()]).

g_boolean() ->
    oneof(["true", "false"]).

g_number() ->
    oneof([g_d(), g_float()]).

g_float() ->
    ?LET({D, R}, {g_d(), g_d()}, list_to_binary([D, ".", R])).

g_atom() ->
    ?LET(N, integer(1, 255),
         ?LET(Atom, vector(N, oneof([g_l(), g_u(), g_d(), $*, $_])),
              list_to_binary([$:, Atom]))).

g_string() ->
    ?LET(String, string(), list_to_binary([$", String, $"])).

g_char_list() ->
    ?LET(String, string(), list_to_binary([$c, $", String, $"])).

g_binary() ->
    binary().


%%% Comments generators

%% @doc Add comments to an iolist of tokens.
g_sprinkle_comments(Tokens) ->
    ?LET(CommentedTokens,
         [{oneof(["", g_comment()]), Token} || Token <- Tokens],
         [[C, T] || {C, T} <- CommentedTokens]).

%% @doc Generate either a line or a block comment.
g_comment() ->
    oneof([g_line_comment(), g_block_comment()]).

g_line_comment() ->
    ?LET(Comment, ?SUCHTHAT(Str, string(), not lists:member($\n, Str)),
         [<<"--">>, unicode:characters_to_binary(Comment), $\n]).

g_block_comment() ->
    ?LET(Comment,
         ?SUCHTHAT(Str, string(),
                   nomatch == re:run(unicode:characters_to_binary(Str), "({-|-})",
                                     [{capture, none}])),
         [<<"{-">>, unicode:characters_to_binary(Comment), <<"-}">>]).

%%% Whitespace generators

g_sprinkle_whitespace(Tokens) ->
    ?LET({Begin,
          Spaces,
          End,
          Newlines},
         {list(oneof([g_space(), g_tab()])),
          vector(length(Tokens) - 1, g_whitespace()),
          list(oneof([g_space(), g_tab()])),
          list(g_newline())},
         begin
             Line = lists:zipwith(fun(Token, Space) -> [Token, Space] end,
                                  Tokens, Spaces ++ [""]),
             [Begin, Line, End, Newlines]
         end).

%% @doc Generate at least one whitespace.
g_whitespace() ->
    non_empty(oneof([g_space(), g_tab(), $\f, $\v, $\n])).

g_tab() -> $\t.

g_space() -> " ".

g_newline() ->
    oneof([$\n, <<"\r\n">>]).

g_breaks() ->
    non_empty(oneof([g_break(), g_newline()])).

g_break() -> <<";;">>.

%%% Helpers.

%% @doc Generate lower case letter.
g_l() ->
    integer($a, $z).

%% @doc Generate upper case letter.
g_u() ->
    integer($A, $Z).

%% @doc Generate number.
g_d() ->
    integer($0, $9).

g_sym() ->
    ?LET(N, pos_integer(), g_sym(N)).

g_sym(N) ->
    ?LET({L, Rest},
         {g_l(), vector(N - 1, oneof([g_d(), g_l(), g_u(), $_]))},
         list_to_binary([L, Rest])).

%% @doc Generate whitespace and comments and add them into an iolist of tokens.
g_sprinkle(Tokens) ->
    ?LET(SpacedTokens, g_sprinkle_whitespace(Tokens),
         ?LET(CommentedTokens, g_sprinkle_comments(SpacedTokens),
              list_to_binary(CommentedTokens))).

%%% Extraction functions

extract_constructors({constructor, Constructor}) ->
    [Constructor];
extract_constructors({construct, Constructor, _}) ->
    extract_constructors(Constructor);
extract_constructors({union, OfTypes}) ->
    [extract_constructors(Type) || Type <- OfTypes];
extract_constructors({type, _, _, Type}) ->
    lists:flatten(extract_constructors(Type));
extract_constructors(_) ->
    [].

extract_type_name({type, Name, _, _}) -> Name.

keywords() ->
    [<<"let">>,
     <<"in">>,
     <<"fn">>,
     <<"match">>,
     <<"with">>,
     <<"beam">>,
     <<"module">>,
     <<"export">>,
     <<"type">>,
     <<"export_type">>,
     <<"import_type">>,
     <<"spawn">>,
     <<"send">>,
     <<"receive">>,
     <<"after">>,
     <<"test">>,
     <<"error">>,
     <<"exit">>,
     <<"throw">>,
     <<"true">>,
     <<"false">>,
     <<"fn">>,
     <<"and">>,
     <<"xor">>,
     <<"or">>
    ]
    ++ base_types().

base_types() ->
    [<<"atom">>,
     <<"int">>,
     <<"float">>,
     <<"string">>,
     <<"bool">>,
     <<"binary">>,
     <<"chars">>,
     <<"()">>
    ].

is_unique(List) ->
    List -- lists:usort(List) == [].
