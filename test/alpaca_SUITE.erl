-module(alpaca_SUITE).

-compile(export_all).

-include_lib("common_test/include/ct.hrl").
-include_lib("proper/include/proper.hrl").
-include_lib("eunit/include/eunit.hrl").

all() -> [proper_compile].

proper_compile(_Config) ->
    ?assert(proper:quickcheck(prop_can_compile_module_def(), [{numtests, 1000}])).

prop_can_compile_module_def() ->
    ?FORALL(Module, g_module(), can_compile(Module)).

can_compile(Code) ->
    case alpaca:compile({text, [Code]}) of
        {ok, _, _} -> true;
        {ok, _, _, _} -> true;
        {error, _} ->
            ct:fail("failed to compile:~n~p~n", [Code]),
            false
    end.

%%% Module generators

%% @doc Generate module declaration.
g_module() ->
    ?LET(Mod, g_module_name(),
         ?LET(Tokens, g_sprinkle_whitespace(["module", Mod, $\n]),
              ?LET(ModuleDef, g_sprinkle_comments(Tokens),
                   list_to_binary(ModuleDef)))).

%% @doc Generate a module name.
%% Module names are turned into atoms. The module name is internally prefixed
%% with 'alpaca_'. Atom max length is 255.
%% @end
g_module_name() ->
    ?LET(N, integer(1, 248), ?LET(Module, g_sym(N), Module)).


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
         ["--", unicode:characters_to_binary(Comment), $\n]).

g_block_comment() ->
    ?LET(Comment,
         ?SUCHTHAT(Str, string(),
                   nomatch == re:run(unicode:characters_to_binary(Str), "({-|-})",
                                     [{capture, none}])),
         ["{-", unicode:characters_to_binary(Comment), "-}"]).

%%% Type generators

g_type_declaration() ->
    ?LET(N, pos_integer(),
         ?LET({Name, Type}, {g_type_name(N), g_type()},
              ["type", Name, "=", Type, $\n])).

g_type_name(N) ->
    ?LET({U, Rest},
         {g_u(), vector(N - 1, oneof([g_d(), g_l(), g_u(), $_]))},
         list_to_binary([U, Rest])).

g_type() ->
    "".

%%% Function generators

g_function() ->
    ?LET({F, Body},
         {g_function_name(), g_function_body()},
         g_sprinkle_whitespace([F, "()", "=", Body, $\n])).

g_function_name() ->
    ?LET(N, pos_integer(), ?LET(Fun, g_sym(N), Fun)).

g_function_body() ->
    g_basic_value().


%% @doc Generate lower case letter.
g_l() ->
    integer($a, $z).

%% @doc Generate upper case letter.
g_u() ->
    integer($A, $Z).

%% @doc Generate number.
g_d() ->
    integer($0, $9).

g_sym(N) ->
    ?LET({L, Rest},
         {g_l(), vector(N - 1, oneof([g_d(), g_l(), g_u(), $_]))},
         list_to_binary([L, Rest])).


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
              list_to_binary([":", Atom]))).

g_string() ->
    ?LET(String, string(), list_to_binary(["\"", String, "\""])).

g_char_list() ->
    ?LET(String, string(), list_to_binary(["c", "\"", String, "\""])).

g_binary() ->
    binary().


%%% Whitespace generators

g_sprinkle_whitespace(Tokens) ->
    ?LET({Begin,
          Spaces,
          End,
          Breaks},
         {list(oneof([g_space(), g_tab()])),
          vector(length(Tokens) - 1, g_line_space()),
          list(oneof([g_space(), g_tab()])),
          g_breaks()},
         begin
             Line = lists:zipwith(fun(Token, Space) -> [Token, Space] end,
                                  Tokens, Spaces ++ [""]),
             [Begin, Line, End, Breaks]
         end).

%% @doc Generate at least one whitespace on the same line.
g_line_space() ->
    non_empty(oneof([g_space(), g_tab(), $\f, $\v])).

g_tab() -> "\t".

g_space() -> " ".

g_breaks() ->
    ?LET(N, pos_integer(), ?LET(Breaks, vector(N, g_newline()), Breaks)).

g_newline() ->
    oneof(["\n", "\r\n"]).
