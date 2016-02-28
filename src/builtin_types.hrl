-define(all_bifs, [?t_int_add,
                   ?t_int_sub
                  ]).

%% type of the '+'/2 function for integers:
-define(t_int_add, {'+', {t_arrow, [t_int, t_int], t_int}}).

%% type of the '-'/2 function:
-define(t_int_sub, {'-', {t_arrow, [t_int, t_int], t_int}}).
