-define(all_bifs, [?t_int_add, ?t_int_sub,
                   ?t_int_mul, ?t_int_div, ?t_int_rem,
                   ?t_float_add, ?t_float_sub,
                   ?t_float_mul, ?t_float_div,

                   ?t_equality
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

-define(t_equality, {'==',
                     {t_arrow, [{unbound, eq_a, 1}, {unbound, eq_a, 1}], t_bool}}).
