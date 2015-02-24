%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
% A representation for already-typechecked FlatZinc.
%
%-----------------------------------------------------------------------------%

:- module tfzn_ast.
:- interface.

%-----------------------------------------------------------------------------%

:- import_module tmzn_ast.
:- import_module types.

:- import_module bool.
:- import_module list.
:- import_module maybe.
:- import_module set.

%-----------------------------------------------------------------------------%
%
% The representation of typed FlatZinc.
%

:- type tfzn
    --->    tfzn(
                tfzn_pred_decls             :: list(tfzn_item_pred_decl),
                tfzn_par_decls              :: list(tfzn_item_par_decl),
                tfzn_var_decls              :: list(tfzn_item_var_decl),
                tfzn_constraints            :: list(tfzn_item_constraint),
                tfzn_solve                  :: tfzn_item_solve
            ).

%-----------------------------------------------------------------------------%
% Items.
%-----------------------------------------------------------------------------%

:- type tfzn_item_pred_decl
    --->    tfzn_item_pred_decl(
                tfzn_pred_decl_name             :: string,
                tfzn_pred_decl_args             :: list(tfzn_pred_decl_arg)
            ).

:- type tfzn_item_par_decl
    --->    tfzn_item_par_decl(
                tfzn_par_decl_type_value        :: tfzn_par_type_value
            ).

:- type tfzn_item_var_decl
    --->    tfzn_item_var_decl(
                tfzn_var_decl_type_value        :: tfzn_var_type_maybe_value,
                tfzn_var_decl_annotations       :: list(tfzn_var_ann)
            ).

:- type tfzn_item_constraint
    --->    tfzn_item_constraint(
                tfzn_constr                     :: tfzn_constraint,
                tfzn_constr_anns                :: set(tfzn_constr_ann)
            ).

:- type tfzn_item_solve
    --->    tfzn_item_solve(
                tfzn_solve_kind                 :: tfzn_solve_kind,
                tfzn_solve_anns                 :: set(tfzn_solve_ann)
            ).

:- type tfzn_pred_decl_arg
    --->    tfzn_pred_decl_arg(
                tfzn_pda_name                   :: string,
                tfzn_pda_type_inst              :: tfzn_type_inst
            ).

    % Normally, we want to minimize or maximize the value of a variable,
    % but there are models that apparently try to minimize the value of
    % a constant. Go figure.
:- type tfzn_solve_kind
    --->    tfzn_sk_satisfy
    ;       tfzn_sk_minimize_int(tfzn_int_term)
    ;       tfzn_sk_maximize_int(tfzn_int_term)
    ;       tfzn_sk_minimize_float(tfzn_float_term)
    ;       tfzn_sk_maximize_float(tfzn_float_term).

%-----------------------------------------------------------------------------%
% Type-insts.
%-----------------------------------------------------------------------------%

:- type tfzn_type_inst
    --->    tfzn_type_inst(
                tfzn_ti_type                    :: tfzn_type,
                tfzn_ti_inst                    :: var_inst
            ).

:- type tfzn_type
    --->    tt_bool
    ;       tt_bool_array(index_ranges)

    ;       tt_int(int_range)
    ;       tt_int_array(index_ranges, int_range)
    ;       tt_int_set(int_range)
    ;       tt_int_set_array(index_ranges, int_range)

    ;       tt_float(float_range)
    ;       tt_float_array(index_ranges, float_range)
    ;       tt_float_set(float_range)
%   ;       tt_float_set_array(index_ranges, float_range)

    ;       tt_string.

:- type tfzn_par_type_value
    --->    tpv_bool(tfzn_bool_var, bool)
    ;       tpv_bool_array(tfzn_bool_array_var, list(bool))

    ;       tpv_int(tfzn_int_var, int)
    ;       tpv_int_array(tfzn_int_array_var, list(int))
    ;       tpv_int_set(tfzn_int_set_var, set(int))
    ;       tpv_int_set_array(tfzn_int_set_array_var, list(set(int)))

    ;       tpv_float(tfzn_float_var, float)
    ;       tpv_float_array(tfzn_float_array_var, list(float)).
%   ;       tpv_float_set(tfzn_float_set_var, set(float))
%   ;       tpv_float_set_array(tfzn_float_set_array_var, list(set(float)))

%   ;       tpv_string(tfzn_string_var, string).

:- type tfzn_var_type_maybe_value
    --->    tftmv_bool(tfzn_bool_var,
                maybe(tmzn_bool_expr))
    ;       tftmv_bool_array(tfzn_bool_array_var, int,
                maybe(list(tmzn_bool_expr)))

    ;       tftmv_int(tfzn_int_var, int_range,
                maybe(tmzn_int_expr))
    ;       tftmv_int_array(tfzn_int_array_var, int_range, int,
                maybe(list(tmzn_int_expr)))
    ;       tftmv_int_set(tfzn_int_set_var, int_range,
                maybe(tmzn_int_set_expr))
    ;       tftmv_int_set_array(tfzn_int_set_array_var, int_range,
                int, maybe(list(tmzn_int_set_expr)))

    ;       tftmv_float(tfzn_float_var, float_range,
                maybe(tmzn_float_expr))
    ;       tftmv_float_array(tfzn_float_array_var, float_range, int,
                maybe(list(tmzn_float_expr))).

%   ;       tftmv_float_set(float_set_var, float_range,
%               maybe(tfzn_float_set_term))
%   ;       tftmv_float_set_array(float_set_array_var, float_range, int,
%               maybe(list(tfzn_float_set_term)))

%   ;       tftmv_string(string_var,
%               maybe(tfzn_string_term)).

%-----------------------------------------------------------------------------%
% Constraints.
%-----------------------------------------------------------------------------%

:- type tfzn_reification
    --->    not_reified
    ;       half_reified(tfzn_bool_term)
    ;       fully_reified(tfzn_bool_term).

:- type tfzn_half_reification
    --->    hr_not_reified
    ;       hr_half_reified(tfzn_bool_var).

:- type tfzn_array_bool_op
    --->    array_bool_and
    ;       array_bool_or.

:- type tfzn_bool_element_op
    --->    array_bool_element
    ;       array_var_bool_element.

:- type tfzn_int_element_op
    --->    array_int_element
    ;       array_var_int_element.

:- type tfzn_float_element_op
    --->    array_float_element
    ;       array_var_float_element.

:- type tfzn_int_set_element_op
    --->    array_int_set_element
    ;       array_var_int_set_element.

:- type tfzn_bool_to_int_op
    --->    bool_to_int.

:- type tfzn_int_to_float_op
    --->    int_to_float.

:- type tfzn_bool_arith_unop
    --->    bool_not.

:- type tfzn_bool_arith_binop
    --->    bool_and
    ;       bool_or
    ;       bool_xor.

:- type tfzn_int_arith_unop
    --->    int_abs
    ;       int_negate.

:- type tfzn_int_arith_binop
    --->    int_plus
    ;       int_minus
    ;       int_times
    ;       int_div
    ;       int_mod
    ;       int_min
    ;       int_max.

:- type tfzn_float_arith_unop
    --->    float_abs
    ;       float_negate
    ;       float_exp
    ;       float_sin
    ;       float_cos.

:- type tfzn_float_arith_binop
    --->    float_plus
    ;       float_minus
    ;       float_times
    ;       float_div
    ;       float_min
    ;       float_max.

:- type tfzn_bool_compare_op
    --->    bool_eq
    ;       bool_le.

:- type tfzn_set_compare_op
    --->    set_eq
    ;       set_ne
    ;       set_le.

:- type tfzn_int_compare_op
    --->    int_eq
    ;       int_ne
    ;       int_lt
    ;       int_le.

:- type tfzn_float_compare_op
    --->    float_eq
    ;       float_ne
    ;       float_lt
    ;       float_le.

:- type tfzn_int_linear_op
    --->    int_lin_eq
    ;       int_lin_ne
    ;       int_lin_le.

:- type tfzn_float_linear_op
    --->    float_lin_eq
    ;       float_lin_ne
    ;       float_lin_le.

:- type tfzn_set_in_op
    --->    set_in.

:- type tfzn_set_card_op
    --->    set_card.

:- type tfzn_set_subset_op
    --->    set_subset.

:- type tfzn_set_set_op
    --->    set_intersect
    ;       set_union
    ;       set_diff.

% :- type tfzn_int_all_diff_op
%     --->    g12fd_int_all_different
%     ;       g12lazy_int_all_different.
%
% :- type tfzn_cumulative_op
%     --->    g12fd_cumulative.
%
% :- type tfzn_global_card_open_op
%     --->    g12fd_global_cardinality_open.

:- type tfzn_constraint
    --->    tfzn_constr_array_bool(
                tfzn_array_bool_op              :: tfzn_array_bool_op,
                tfzn_array_bool_arg1            :: tfzn_bool_array_term,
                tfzn_array_bool_result          :: tfzn_bool_term
            )
    ;       tfzn_constr_array_bool_element(
                tfzn_bool_element_op            :: tfzn_bool_element_op,
                tfzn_bool_element_index         :: tfzn_int_term,
                tfzn_bool_element_array         :: tfzn_bool_array_term,
                tfzn_bool_element_value         :: tfzn_bool_term,
                tfzn_bool_element_reif          :: tfzn_half_reification
            )
    ;       tfzn_constr_array_int_element(
                tfzn_int_element_op             :: tfzn_int_element_op,
                tfzn_int_element_index          :: tfzn_int_term,
                tfzn_int_element_array          :: tfzn_int_array_term,
                tfzn_int_element_value          :: tfzn_int_term,
                tfzn_int_element_reif           :: tfzn_half_reification
            )
    ;       tfzn_constr_array_float_element(
                tfzn_float_element_op           :: tfzn_float_element_op,
                tfzn_float_element_index        :: tfzn_int_term,
                tfzn_float_element_array        :: tfzn_float_array_term,
                tfzn_float_element_value        :: tfzn_float_term,
                tfzn_float_element_reif         :: tfzn_half_reification
            )
    ;       tfzn_constr_array_int_set_element(
                tfzn_int_set_element_op         :: tfzn_int_set_element_op,
                tfzn_int_set_element_index      :: tfzn_int_term,
                tfzn_int_set_element_array      :: tfzn_int_set_array_term,
                tfzn_int_set_element_value      :: tfzn_int_set_term,
                tfzn_int_set_element_reif       :: tfzn_half_reification
            )
    ;       tfzn_constr_bool_to_int(
                tfzn_bool_to_int_op             :: tfzn_bool_to_int_op,
                tfzn_bool_to_int_arg1           :: tfzn_bool_term,
                tfzn_bool_to_int_result         :: tfzn_int_var
            )
    ;       tfzn_constr_int_to_float(
                tfzn_int_to_float_op            :: tfzn_int_to_float_op,
                tfzn_int_to_float_arg1          :: tfzn_int_term,
                tfzn_int_to_float_result        :: tfzn_float_var
            )
    ;       tfzn_constr_bool_arith_unop(
                tfzn_bool_arith_unop            :: tfzn_bool_arith_unop,
                tfzn_bool_arith_un_arg1         :: tfzn_bool_term,
                tfzn_bool_arith_un_result       :: tfzn_bool_term
            )
    ;       tfzn_constr_bool_arith_binop(
                tfzn_bool_arith_binop           :: tfzn_bool_arith_binop,
                tfzn_bool_arith_bin_arg1        :: tfzn_bool_term,
                tfzn_bool_arith_bin_arg2        :: tfzn_bool_term,
                tfzn_bool_arith_bin_result      :: tfzn_bool_term
            )
    ;       tfzn_constr_int_arith_unop(
                tfzn_int_arith_unop             :: tfzn_int_arith_unop,
                tfzn_int_arith_un_arg1          :: tfzn_int_term,
                tfzn_int_arith_un_result        :: tfzn_int_term
            )
    ;       tfzn_constr_int_arith_binop(
                tfzn_int_arith_binop            :: tfzn_int_arith_binop,
                tfzn_int_arith_bin_arg1         :: tfzn_int_term,
                tfzn_int_arith_bin_arg2         :: tfzn_int_term,
                tfzn_int_arith_bin_result       :: tfzn_int_term
            )
    ;       tfzn_constr_float_arith_unop(
                tfzn_float_arith_unop           :: tfzn_float_arith_unop,
                tfzn_float_arith_un_arg1        :: tfzn_float_term,
                tfzn_float_arith_un_result      :: tfzn_float_term
            )
    ;       tfzn_constr_float_arith_binop(
                tfzn_float_arith_binop          :: tfzn_float_arith_binop,
                tfzn_float_arith_bin_arg1       :: tfzn_float_term,
                tfzn_float_arith_bin_arg2       :: tfzn_float_term,
                tfzn_float_arith_bin_result     :: tfzn_float_term
                % tfzn_float_arith_bin_reif     :: tfzn_reification
            )
    ;       tfzn_constr_bool_compare(
                tfzn_bool_compare_op            :: tfzn_bool_compare_op,
                tfzn_bool_compare_arg1          :: tfzn_bool_term,
                tfzn_bool_compare_arg2          :: tfzn_bool_term,
                tfzn_bool_compare_reif          :: tfzn_reification
            )
    ;       tfzn_constr_int_compare(
                tfzn_int_compare_op             :: tfzn_int_compare_op,
                tfzn_int_compare_arg1           :: tfzn_int_term,
                tfzn_int_compare_arg2           :: tfzn_int_term,
                tfzn_int_compare_reif           :: tfzn_reification
            )
    ;       tfzn_constr_int_set_compare(
                tfzn_int_set_compare_op         :: tfzn_set_compare_op,
                tfzn_int_set_compare_arg1       :: tfzn_int_set_term,
                tfzn_int_set_compare_arg2       :: tfzn_int_set_term
                % XXX Should there be a tfzn_reification argument?
            )
    ;       tfzn_constr_float_compare(
                tfzn_reif_float_compare_op      :: tfzn_float_compare_op,
                tfzn_reif_float_compare_arg1    :: tfzn_float_term,
                tfzn_reif_float_compare_arg2    :: tfzn_float_term,
                tfzn_reif_float_compare_reify   :: tfzn_reification
            )
    ;       tfzn_constr_int_linear(
                tfzn_int_linear_op              :: tfzn_int_linear_op,
                % XXX Should the coeffs field be list(int)?
                tfzn_int_linear_coeffs          :: tfzn_int_array_term,
                tfzn_int_linear_xs              :: tfzn_int_array_term,
                tfzn_int_linear_value           :: tfzn_int_term,
                tfzn_int_linear_reif            :: tfzn_reification
            )
    ;       tfzn_constr_float_linear(
                tfzn_float_linear_op            :: tfzn_float_linear_op,
                % XXX Should the coeffs field be list(float)?
                tfzn_float_linear_coeffs        :: tfzn_float_array_term,
                tfzn_float_linear_xs            :: tfzn_float_array_term,
                tfzn_float_linear_value         :: tfzn_float_term,
                tfzn_float_linear_reif          :: tfzn_reification
            )
    ;       tfzn_constr_int_set_in(
                tfzn_int_set_in_op              :: tfzn_set_in_op,
                tfzn_int_set_in_element         :: tfzn_int_term,
                tfzn_int_set_in_set             :: tfzn_int_set_term,
                tfzn_int_set_in_reif            :: tfzn_reification
            )
    ;       tfzn_constr_int_set_card(
                tfzn_int_set_card_op            :: tfzn_set_card_op,
                tfzn_int_set_card_set           :: tfzn_int_set_term,
                tfzn_int_set_card_card          :: tfzn_int_term
            )
    ;       tfzn_constr_int_set_subset(
                tfzn_int_set_subset_op          :: tfzn_set_subset_op,
                tfzn_int_set_subset_arg1        :: tfzn_int_set_term,
                tfzn_int_set_subset_arg2        :: tfzn_int_set_term,
                tfzn_int_set_subset_reif        :: tfzn_reification
            )
    ;       tfzn_constr_int_set_set_op(
                tfzn_int_set_set_op             :: tfzn_set_set_op,
                tfzn_int_set_set_arg1           :: tfzn_int_set_term,
                tfzn_int_set_set_arg2           :: tfzn_int_set_term,
                tfzn_int_set_set_result         :: tfzn_int_set_term
            )
%   ;       tfzn_constr_int_all_different(
%               tfzn_g12fd_int_all_diff_op      :: tfzn_int_all_diff_op,
%               tfzn_g12fd_int_all_diff_arg1    :: tfzn_int_array_term
%           )
%   ;       tfzn_constr_cumulative(
%               tfzn_g12fd_cumulative_op        :: tfzn_cumulative_op,
%               tfzn_g12fd_cumulative_arg1      :: tfzn_int_array_term,
%               tfzn_g12fd_cumulative_arg2      :: tfzn_int_array_term,
%               tfzn_g12fd_cumulative_arg3      :: tfzn_int_array_term,
%               tfzn_g12fd_cumulative_arg4      :: tfzn_int_term
%           )
%   ;       tfzn_constr_global_card_open(
%               tfzn_g12fd_glo_card_open_op     :: tfzn_global_card_open_op,
%               tfzn_g12fd_glo_card_open_arg1   :: tfzn_int_array_var,
%               tfzn_g12fd_glo_card_open_arg2   :: tfzn_int_array_term,
%               tfzn_g12fd_glo_card_open_arg3   :: tfzn_int_array_term,
%               tfzn_g12fd_glo_card_open_arg4   :: tfzn_int_array_term
%           )
    ;       tfzn_constr_user(
                tfzn_user_pred_name             :: string,
                tfzn_user_arg_terms             :: list(tfzn_general_term)
            ).

%-----------------------------------------------------------------------------%
% Terms of unknown type.
%-----------------------------------------------------------------------------%

:- type tfzn_general_term
    --->    tfzn_gen_term_bool(tfzn_bool_term)
    ;       tfzn_gen_term_bool_array(tfzn_bool_array_term)
    ;       tfzn_gen_term_int(tfzn_int_term)
    ;       tfzn_gen_term_int_array(tfzn_int_array_term)
    ;       tfzn_gen_term_int_set(tfzn_int_set_term)
    ;       tfzn_gen_term_int_set_array(tfzn_int_set_array_term)
    ;       tfzn_gen_term_float(tfzn_float_term)
    ;       tfzn_gen_term_float_array(tfzn_float_array_term)
    ;       tfzn_gen_term_float_set(tfzn_float_set_term)
%   ;       tfzn_gen_term_float_set_array(tfzn_float_set_array_term)
    ;       tfzn_gen_term_string(tfzn_string_term).

:- type tfzn_ann_term
    --->    tfzn_ann_term_general(tfzn_general_term)
    ;       tfzn_ann_term_ann(string, list(tfzn_ann_term))
    ;       tfzn_ann_term_ann_array(list(tfzn_ann_term)).

%-----------------------------------------------------------------------------%
% Terms of known types.
%-----------------------------------------------------------------------------%

:- type tfzn_bool_term
    --->    tfzn_bool_term_const(
                tfzn_bt_c_value                 :: bool
            )
    ;       tfzn_bool_term_var(
                tfzn_bt_v_var                   :: tfzn_bool_var
            ).

:- type tfzn_bool_array_term
    --->    tfzn_bool_array_term_consts(
                tfzn_bat_cs_value               :: list(bool)
            )
    ;       tfzn_bool_array_term_vars(
                tfzn_bat_vs_vars                :: list(tfzn_bool_var)
            )
    ;       tfzn_bool_array_term_terms(
                tfzn_bat_ts_terms               :: list(tfzn_bool_term)
            )
    ;       tfzn_bool_array_term_var(
                tfzn_bat_v_var                  :: tfzn_bool_array_var
            ).

:- type tfzn_int_term
    --->    tfzn_int_term_const(
                tfzn_it_c_value                 :: int
            )
    ;       tfzn_int_term_var(
                tfzn_it_v_var                   :: tfzn_int_var
            ).

:- type tfzn_int_array_term
    --->    tfzn_int_array_term_consts(
                tfzn_iat_cs_value               :: list(int)
            )
    ;       tfzn_int_array_term_vars(
                tfzn_iat_vs_vars                :: list(tfzn_int_var)
            )
    ;       tfzn_int_array_term_terms(
                tfzn_iat_ts_terms               :: list(tfzn_int_term)
            )
    ;       tfzn_int_array_term_var(
                tfzn_iat_v_var                  :: tfzn_int_array_var
            ).

:- type tfzn_int_set_term
    --->    tfzn_int_set_term_const(
                tfzn_ist_c_value                :: set(int)
            )
    ;       tfzn_int_set_term_var(
                tfzn_ist_v_var                  :: tfzn_int_set_var
            ).

:- type tfzn_int_set_array_term
    --->    tfzn_int_set_array_term_consts(
                tfzn_isat_cs_value              :: list(set(int))
            )
    ;       tfzn_int_set_array_term_vars(
                tfzn_isat_vs_vars               :: list(tfzn_int_set_var)
            )
    ;       tfzn_int_set_array_term_terms(
                tfzn_isat_ts_terms              :: list(tfzn_int_set_term)
            )
    ;       tfzn_int_set_array_term_var(
                tfzn_isat_v_var                 :: tfzn_int_set_array_var
            ).

:- type tfzn_float_term
    --->    tfzn_float_term_const(
                tfzn_ft_c_value                 :: float
            )
    ;       tfzn_float_term_var(
                tfzn_ft_v_var                   :: tfzn_float_var
            ).

:- type tfzn_float_array_term
    --->    tfzn_float_array_term_consts(
                tfzn_fat_cs_value               :: list(float)
            )
    ;       tfzn_float_array_term_vars(
                tfzn_fat_vs_vars                :: list(tfzn_float_var)
            )
    ;       tfzn_float_array_term_terms(
                tfzn_fat_ts_terms               :: list(tfzn_float_term)
            )
    ;       tfzn_float_array_term_var(
                tfzn_fat_v_var                  :: tfzn_float_array_var
            ).

:- type tfzn_float_set_term
    --->    tfzn_float_set_term_const(
                tfzn_fst_c_value                :: set(float)
            )
    ;       tfzn_float_set_term_var(
                tfzn_fst_v_var                  :: tfzn_float_set_var
            ).

% Not yet needed.
% :- type tfzn_float_set_array_term
%     --->    tfzn_float_set_array_term_consts(
%                 tfzn_fsat_cs_value              :: list(float_set)
%             )
%     ;       tfzn_float_set_array_term_vars(
%                 tfzn_fsat_vs_vars               :: list(tfzn_float_set_var)
%             )
%     ;       tfzn_float_set_array_term_terms(
%                 tfzn_fsat_ts_terms              :: list(tfzn_float_set_term)
%             )
%     ;       tfzn_float_set_array_term_var(
%                 tfzn_fsat_v_var                 :: tfzn_float_set_array_var
%             ).

:- type tfzn_string_term
    --->    tfzn_string_term_const(
                tfzn_st_c_value                 :: string
            )
    ;       tfzn_string_term_var(
                tfzn_st_v_var                   :: tfzn_string_var
            ).

%-----------------------------------------------------------------------------%
% Variables.
%-----------------------------------------------------------------------------%

:- type tfzn_bool_var
    --->    tfzn_bool_var_named(string)
    ;       tfzn_bool_var_tmp(int)
    ;       tfzn_bool_var_array_slot(tfzn_bool_array_var, int).

:- type tfzn_bool_array_var
    --->    tfzn_bool_array_var_named(string)
    ;       tfzn_bool_array_var_tmp(int).

:- type tfzn_int_var
    --->    tfzn_int_var_named(string)
    ;       tfzn_int_var_tmp(int)
    ;       tfzn_int_var_array_slot(tfzn_int_array_var, int).

:- type tfzn_int_array_var
    --->    tfzn_int_array_var_named(string)
    ;       tfzn_int_array_var_tmp(int).

:- type tfzn_int_set_var
    --->    tfzn_int_set_var_named(string)
    ;       tfzn_int_set_var_tmp(int)
    ;       tfzn_int_set_var_array_slot(tfzn_int_set_array_var, int).

:- type tfzn_int_set_array_var
    --->    tfzn_int_set_array_var_named(string)
    ;       tfzn_int_set_array_var_tmp(int).

:- type tfzn_float_var
    --->    tfzn_float_var_named(string)
    ;       tfzn_float_var_tmp(int)
    ;       tfzn_float_var_array_slot(tfzn_float_array_var, int).

:- type tfzn_float_array_var
    --->    tfzn_float_array_var_named(string)
    ;       tfzn_float_array_var_tmp(int).

:- type tfzn_float_set_var
    --->    tfzn_float_set_var_named(string)
    ;       tfzn_float_set_var_tmp(int).
    % Not needed (yet).
    % ;       tfzn_float_set_var_array_slot(tfzn_float_set_array_var, int).

:- type tfzn_string_var
    --->    tfzn_string_var_named(string)
    ;       tfzn_string_var_tmp(int).

%-----------------------------------------------------------------------------%
% Annotations on variable declarations.
%-----------------------------------------------------------------------------%

:- type tfzn_var_ann
    --->    var_ann_is_defined_var
    ;       var_ann_is_defined_var_eqv(string)
            % XXX should be general var
    ;       var_ann_var_is_introduced
    ;       var_ann_output_var
    ;       var_ann_output_array(list(index_range))
    ;       var_ann_general(string, list(tfzn_ann_term)).

%-----------------------------------------------------------------------------%
% Annotations on constraints.
%-----------------------------------------------------------------------------%

:- type tfzn_constr_ann
    --->    constr_ann_defines_var(tfzn_defined_var)
    ;       constr_ann_domain_consistency
    ;       constr_ann_general(string, list(tfzn_general_term)).

:- type tfzn_defined_var
    --->    tfzn_def_bool_var(tfzn_bool_var)
    ;       tfzn_def_int_var(tfzn_int_var)
    ;       tfzn_def_int_set_var(tfzn_int_set_var)
    ;       tfzn_def_float_var(tfzn_float_var).

%-----------------------------------------------------------------------------%
% Annotations on solve goals.
%-----------------------------------------------------------------------------%

:- type tfzn_search_params
    --->    int_search(
                tfzn_int_array_term,
                tfzn_search_var_choice,
                tfzn_search_assignment,
                tfzn_search_strategy
            )
    ;       set_search(
                tfzn_int_set_array_term,
                tfzn_search_var_choice,
                tfzn_search_assignment,
                tfzn_search_strategy
            )
    ;       bool_search(
                tfzn_bool_array_term,
                tfzn_search_var_choice,
                tfzn_search_assignment,
                tfzn_search_strategy
            )
    ;       seq_search(
                list(tfzn_search_params)
            ).

:- type tfzn_search_var_choice
    --->    svc_input_order
    ;       svc_smallest
    ;       svc_largest
    ;       svc_occurrence
    ;       svc_first_fail
    ;       svc_anti_first_fail
    ;       svc_most_constrained
    ;       svc_max_regret.

:- type tfzn_search_assignment
    --->    sa_indomain
    ;       sa_indomain_min
    ;       sa_indomain_max
    ;       sa_indomain_median
    ;       sa_indomain_middle
    ;       sa_indomain_split
    ;       sa_indomain_reverse_split
    ;       sa_indomain_interval
    ;       sa_indomain_random.

:- type tfzn_search_strategy
    --->    ss_complete.

:- type tfzn_limit
    --->    time_limit(tfzn_int_term).

:- type tfzn_solve_ann
    --->    solve_ann_search(tfzn_search_params)
    ;       solve_ann_limit(tfzn_limit, tfzn_search_params).

%-----------------------------------------------------------------------------%
:- end_module tfzn_ast.
%-----------------------------------------------------------------------------%
