-define(all_bifs, [?t_int_add, ?t_int_sub,
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
