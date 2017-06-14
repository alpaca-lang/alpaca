%%% -*- mode: erlang;erlang-indent-level: 4;indent-tabs-mode: nil -*-
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

-define(all_bifs, [
                   ?t_int_add, ?t_int_sub,
                   ?t_int_mul, ?t_int_div, ?t_int_rem,
                   ?t_float_add, ?t_float_sub,
                   ?t_float_mul, ?t_float_div,

                   ?t_equality, ?t_neq,
                   ?t_gt, ?t_lt, ?t_gte, ?t_lte
                  ]).

-define(t_int_math, {t_arrow, [t_int, t_int], t_int}).

-define(t_int_add, {'+', ?t_int_math}).
-define(t_int_sub, {'-', ?t_int_math}).
-define(t_int_mul, {'*', ?t_int_math}).
-define(t_int_div, {'/', ?t_int_math}).
-define(t_int_rem, {'%', ?t_int_math}).

-define(t_float_math, {t_arrow, [t_float, t_float], t_float}).

-define(t_float_add, {'+.', ?t_float_math}).
-define(t_float_sub, {'-.', ?t_float_math}).
-define(t_float_mul, {'*.', ?t_float_math}).
-define(t_float_div, {'/.', ?t_float_math}).

-define(compare, {t_arrow, [{unbound, eq_a, 1}, {unbound, eq_a, 1}], t_bool}).
-define(t_equality, {'=:=', ?compare}).
-define(t_neq, {'!=', ?compare}).
-define(t_gt, {'>', ?compare}).
-define(t_lt, {'<', ?compare}).
-define(t_gte, {'>=', ?compare}).
-define(t_lte, {'=<', ?compare}).

-define(all_type_checks, [{is_integer, t_int},
                          {is_float, t_float},
                          {is_atom, t_atom},
                          {is_bool, t_bool},
                          {is_list, t_list},
                          {is_pid, t_pid},
                          {is_string, t_string},
                          {is_chars, t_chars},
                          {is_binary, t_binary}]).
