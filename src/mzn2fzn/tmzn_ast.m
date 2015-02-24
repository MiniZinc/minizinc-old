%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
% A representation for already-typechecked MiniZinc.
%
%-----------------------------------------------------------------------------%

:- module tmzn_ast.
:- interface.

%-----------------------------------------------------------------------------%

:- import_module mzn_ops.
:- import_module types.
:- import_module zinc_common.

:- import_module bool.
:- import_module list.
:- import_module maybe.
:- import_module set.

%-----------------------------------------------------------------------------%
% The representation of typed MiniZinc.
%-----------------------------------------------------------------------------%

:- type tmzn
    --->    tmzn(
%               tmzn_predfuncs              :: list(tmzn_predfunc_item),
                tmzn_var_decls              :: list(tmzn_var_decl_item),
                tmzn_assigns                :: list(tmzn_assign_item),

                tmzn_constraints            :: list(tmzn_constraint_item),

                tmzn_solve                  :: tmzn_solve_item,

                % The output specification, if present.
                tmzn_output                 :: maybe(tmzn_output_item)
            ).

%-----------------------------------------------------------------------------%
% Items.
%-----------------------------------------------------------------------------%

% :- type tmzn_predfunc_item
%     --->    tmzn_predfunc_item(
%                 % Functions have 'func_ret(ti_expr)' as their return type.
%                 % Predicates have 'pred_ret' (they're implicitly 'var bool').
%                 % Tests have 'test_ret' (they're implicitly 'par bool').
%                 tmzn_predfunc_item_ret          :: predfunc_ret,
%                 tmzn_predfunc_item_name         :: zinc_name,
% 
%                 % Each pred/func *symbol* can be overloaded and thus
%                 % represents 1..N distinct preds/funcs, each with their own
%                 % type-signature.  Each pred/func symbol also has 0..M
%                 % "procedures", each of which has a different
%                 % type-inst-signature.
%                 %
%                 % Eg. the '+' operation symbol has four type-sigs and eight
%                 % procedures (where i/f are int/float, pi/vi/pf/vf are par
%                 % int/var int/par float/var float):
%                 %
%                 % TSigs:  [(i,i)->i, (f,f)->f, (i)->i, (f)->f]
%                 % TISigs: [(pi,pi)->pi, (vi,vi)->vi, (pf,pf)->pf, (vf,vf)->vf)
%                 %          (pi)->pi, (vi)->vi, (pf)->pf, (vf)->vf)]
%                 %
%                 tmzn_predfunc_item_proc_number  :: int,
% 
%                 tmzn_predfunc_item_params       :: ti_exprs_and_ids,
%                 tmzn_predfunc_item_annotations  :: exprs,
%                 tmzn_predfunc_item_maybe_body   :: maybe(expr)
%             ).

:- type tmzn_var_decl_item
    --->    tmzn_item_var_decl(
                tmzn_var_decl_locn              :: src_pos,
                tmzn_var_decl_name              :: zinc_name,
                tmzn_var_decl_ints              :: var_inst,
                tmzn_var_decl_type_value        :: tmzn_var_type_maybe_value
                % tmzn_var_decl_annotations     :: list(var_decl_ann)   % XXX
            ).

:- type tmzn_assign_item
    --->    tmzn_assign_item(
                tmzn_assign_locn                :: src_pos,
                tmzn_assign_name                :: zinc_name,
                tmzn_assign_value               :: tmzn_general_expr
            ).

:- type tmzn_constraint_item
    --->    tmzn_constraint_item(
                tmzn_constr_locn                :: src_pos,
                tmzn_constr                     :: tmzn_constraint,
                tmzn_constr_anns                :: set(tmzn_constr_ann)
            ).

:- type tmzn_solve_item
    --->    tmzn_solve_item(
                tmzn_solve_locn                 :: src_pos,
                tmzn_solve_kind                 :: tmzn_solve_kind,
                tmzn_solve_anns                 :: set(tmzn_solve_ann)
            ).

:- type tmzn_output_item
    --->    tmzn_output_item(
                tmzn_output_locn                :: src_pos,
                tmzn_output_spec                :: tmzn_string_array_expr
            ).

:- type tmzn_solve_kind
    --->    tmzn_sk_satisfy
    ;       tmzn_sk_minimize_int(tmzn_int_expr)
    ;       tmzn_sk_maximize_int(tmzn_int_expr)
    ;       tmzn_sk_minimize_float(tmzn_float_expr)
    ;       tmzn_sk_maximize_float(tmzn_float_expr).

%-----------------------------------------------------------------------------%
% Components of predicate declarations.
%-----------------------------------------------------------------------------%

    % A proc_id uniquely identifies a procedure.
    %
:- type tmzn_proc_id
    --->    tmzn_proc_id(
                tmzn_proc_name      :: zinc_name,   % pred/func/operator name
                tmzn_proc_number    :: int          % procedure number
            ).

% :- type predfunc_ret
%     --->    pred_ret
%     ;       test_ret
%     ;       func_ret(ti_expr).

% :- type ti_exprs_and_ids == list(ti_expr_and_id).
% :- type ti_expr_and_id   == pair(ti_expr, id).

% :- type local_vars ==   list(local_var).
% :- type local_var
%     --->    local_var(ti_expr, id, exprs, maybe(expr)).

% :- type tmzn_type_inst
%     --->    tmzn_type_inst(
%                 tti_src_locn                    :: src_locn,
%                 tti_type                        :: tmzn_type,
%                 tti_inst                        :: var_inst
%             ).
% 
% :- type tmzn_type
%     --->    tt_bool
%     ;       tt_int
%     ;       tt_float
%     ;       tt_string
% 
%     ;       tt_bool_array
%     ;       tt_int_array
%     ;       tt_float_array
% 
%     ;       tt_int_set
%     ;       tt_float_set.

:- type tmzn_var_type_maybe_value
    --->    tmtmv_bool(maybe(tmzn_bool_expr))
    ;       tmtmv_bool_array(index_ranges, maybe(list(tmzn_bool_expr)))

    ;       tmtmv_int(int_range, maybe(tmzn_int_expr))
    ;       tmtmv_int_array(int_range, index_ranges,
                maybe(list(tmzn_int_expr)))
    ;       tmtmv_int_set(int_range, maybe(tmzn_int_set_expr))
    ;       tmtmv_int_set_array(int_range, index_ranges,
                maybe(list(tmzn_int_set_expr)))

    ;       tmtmv_float(float_range, maybe(tmzn_float_expr))
    ;       tmtmv_float_array(float_range, index_ranges,
                maybe(list(tmzn_float_expr))).

%-----------------------------------------------------------------------------%
% Constraints.
%-----------------------------------------------------------------------------%

:- type tmzn_constraint
    --->    tmzn_constr_bool_expr(
                tmzn_bool_expr                  :: tmzn_bool_expr
            ).

%-----------------------------------------------------------------------------%
% Expressions.
%-----------------------------------------------------------------------------%

% XXX consider src_pos's for everything below
% XXX consider type_insts for everything below for which it is not given

:- type tmzn_general_expr
    --->    tmzn_gen_expr_bool(tmzn_bool_expr)
    ;       tmzn_gen_expr_bool_array(tmzn_bool_array_expr)
    ;       tmzn_gen_expr_int(tmzn_int_expr)
    ;       tmzn_gen_expr_int_array(tmzn_int_array_expr)
    ;       tmzn_gen_expr_int_set(tmzn_int_set_expr)
    ;       tmzn_gen_expr_int_set_array(tmzn_int_set_array_expr)
    ;       tmzn_gen_expr_float(tmzn_float_expr)
    ;       tmzn_gen_expr_float_array(tmzn_float_array_expr)
    ;       tmzn_gen_expr_float_set(tmzn_float_set_expr)
%   ;       tmzn_gen_expr_float_set_array(tmzn_float_set_array_expr)
    ;       tmzn_gen_expr_string(tmzn_string_expr)
    ;       tmzn_gen_expr_string_array(tmzn_string_array_expr).

:- type tmzn_ann_expr
    --->    tmzn_ann_expr_general(tmzn_general_expr)
    ;       tmzn_ann_expr_ann(string, list(tmzn_ann_expr))
    ;       tmzn_ann_expr_ann_array(list(tmzn_ann_expr)).

%-----------------------------------------------------------------------------%
% Expressions of known types.
%-----------------------------------------------------------------------------%

% XXX consider annotations, on bools, on others
% XXX consider insts

:- type tmzn_bool_expr
    --->    tmzn_bool_expr_const(
                tmzn_be_c_sl                    :: src_pos,
                tmzn_be_c_value                 :: bool
            )
    ;       tmzn_bool_expr_var(
                tmzn_be_v_sl                    :: src_pos,
                tmzn_be_v_var                   :: tmzn_bool_var
            )
    ;       tmzn_bool_expr_b2b(
                tmzn_be_bsb_sl                  :: src_pos,
                tmzn_be_b2b_op                  :: bool_to_bool_op,
                tmzn_be_b2b_arg1                :: tmzn_bool_expr
            )
    ;       tmzn_bool_expr_bb2b(
                tmzn_be_bb2b_sl                 :: src_pos,
                tmzn_be_bb2b_op                 :: bool_bool_to_bool_op,
                tmzn_be_bb2b_arg1               :: tmzn_bool_expr,
                tmzn_be_bb2b_arg2               :: tmzn_bool_expr
            )
    ;       tmzn_bool_expr_ba2b(
                tmzn_be_ba2b_sl                 :: src_pos,
                tmzn_be_ba2b_op                 :: bool_array_to_bool_op,
                tmzn_be_ba2b_args               :: tmzn_bool_array_expr
            )
    ;       tmzn_bool_expr_ii2b(
                tmzn_be_ii2b_sl                 :: src_pos,
                tmzn_be_ii2b_op                 :: int_int_to_bool_op,
                tmzn_be_ii2b_arg1               :: tmzn_int_expr,
                tmzn_be_ii2b_arg2               :: tmzn_int_expr
            )
    ;       tmzn_bool_expr_iis2b(
                tmzn_be_iis2b_sl                :: src_pos,
                tmzn_be_iis2b_op                :: int_int_set_to_bool_op,
                tmzn_be_iis2b_arg1              :: tmzn_int_expr,
                tmzn_be_iis2b_arg2              :: tmzn_int_set_expr
            )
    ;       tmzn_bool_expr_isis2b(
                tmzn_be_isis2b_sl               :: src_pos,
                tmzn_be_isis2b_op               :: set_set_to_bool_op,
                tmzn_be_isis2b_arg1             :: tmzn_int_set_expr,
                tmzn_be_isis2b_arg2             :: tmzn_int_set_expr
            )
    ;       tmzn_bool_expr_ff2b(
                tmzn_be_ff2b_sl                 :: src_pos,
                tmzn_be_ff2b_op                 :: float_float_to_bool_op,
                tmzn_be_ff2b_arg1               :: tmzn_float_expr,
                tmzn_be_ff2b_arg2               :: tmzn_float_expr
            )
    ;       tmzn_bool_expr_ffs2b(
                tmzn_be_ffs2b_sl                :: src_pos,
                tmzn_be_ffs2b_op                :: float_float_set_to_bool_op,
                tmzn_be_ffs2b_arg1              :: tmzn_float_expr,
                tmzn_be_ffs2b_arg2              :: tmzn_float_set_expr
            )
    ;       tmzn_bool_expr_fsfs2b(              % XXX
                tmzn_be_fsfs2b_sl               :: src_pos,
                tmzn_be_fsfs2b_op               :: set_set_to_bool_op,
                tmzn_be_fsfs2b_arg1             :: tmzn_float_set_expr,
                tmzn_be_fsfs2b_arg2             :: tmzn_float_set_expr
            )
    ;       tmzn_bool_expr_ss2b(
                tmzn_be_ss2b_sl                 :: src_pos,
                tmzn_be_ss2b_op                 :: string_string_to_bool_op,
                tmzn_be_ss2b_arg1               :: tmzn_string_expr,
                tmzn_be_ss2b_arg2               :: tmzn_string_expr
            )
    ;       tmzn_bool_expr_ite(
                tmzn_be_ite_sl                  :: src_pos,
                tmzn_be_ite_cond                :: tmzn_bool_expr,
                tmzn_be_ite_then                :: tmzn_bool_expr,
                tmzn_be_ite_else                :: tmzn_bool_expr
            )
    ;       tmzn_bool_expr_is_fixed(
                tmzn_be_if_sl                   :: src_pos,
                tmzn_be_if_arg1                 :: tmzn_general_expr
            )
    ;       tmzn_bool_expr_general(
                tmzn_be_gen_sl                  :: src_pos,
                tmzn_be_gen_pred                :: string,
                tmzn_be_gen_args                :: list(tmzn_general_expr)
            ).

:- type tmzn_bool_array_expr
    --->    tmzn_bool_array_expr_consts(
                tmzn_bae_cs_sl                  :: src_pos,
                tmzn_bae_cs_index_ranges        :: list(index_range),
                tmzn_bae_cs_value               :: list(bool)
            )
    ;       tmzn_bool_array_expr_vars(
                tmzn_bae_vs_sl                  :: src_pos,
                tmzn_bae_vs_index_ranges        :: list(index_range),
                tmzn_bae_vs_vars                :: list(tmzn_bool_var)
            )
    ;       tmzn_bool_array_expr_exprs(
                tmzn_bae_es_sl                  :: src_pos,
                tmzn_bae_es_index_ranges        :: list(index_range),
                tmzn_bae_es_exprs               :: list(tmzn_bool_expr)
            )
    ;       tmzn_bool_array_expr_var(
                tmzn_bae_v_sl                   :: src_pos,
                tmzn_bae_v_var                  :: tmzn_bool_array_var
            )
    ;       tmzn_bool_array_expr_comprehension(
                tmzn_bae_comp_sl                :: src_pos,
                tmzn_bae_comp_head              :: tmzn_bool_expr,
                tmzn_bae_comp_generators        :: list(tmzn_generator),
                tmzn_bae_comp_maybe_cond        :: maybe(tmzn_bool_expr)
            ).

:- type tmzn_int_expr
    --->    tmzn_int_expr_const(
                tmzn_ie_c_sl                    :: src_pos,
                tmzn_ie_c_value                 :: int
            )
    ;       tmzn_int_expr_var(
                tmzn_ie_v_sl                    :: src_pos,
                tmzn_ie_v_var                   :: tmzn_int_var
            )
    ;       tmzn_int_expr_b2i(
                tmzn_ie_b2i_sl                  :: src_pos,
                tmzn_ie_b2i_op                  :: bool_to_int_op,
                tmzn_ie_b2i_arg1                :: tmzn_bool_expr
            )
    ;       tmzn_int_expr_i2i(
                tmzn_ie_i2i_sl                  :: src_pos,
                tmzn_ie_i2i_op                  :: int_to_int_op,
                tmzn_ie_i2i_arg1                :: tmzn_int_expr
            )
    ;       tmzn_int_expr_ii2i(
                tmzn_ie_ii2i_sl                 :: src_pos,
                tmzn_ie_ii2i_op                 :: int_int_to_int_op,
                tmzn_ie_ii2i_arg1               :: tmzn_int_expr,
                tmzn_ie_ii2i_arg2               :: tmzn_int_expr
            )
    ;       tmzn_int_expr_is2i(
                tmzn_ie_is2i_sl                 :: src_pos,
                tmzn_ie_is2i_op                 :: int_set_to_int_op,
                tmzn_ie_is2i_arg1               :: tmzn_int_set_expr
            )
    ;       tmzn_int_expr_ia2i(
                tmzn_ie_ia2i_sl                 :: src_pos,
                tmzn_ie_ia2i_op                 :: int_array_to_int_op,
                tmzn_ie_ia2i_arg1               :: tmzn_int_array_expr
            )
    ;       tmzn_int_expr_xs2i(
                tmzn_ie_xs2i_sl                 :: src_pos,
                tmzn_ie_xs2i_op                 :: set_to_int_op,
                tmzn_ie_xs2i_arg1               :: tmzn_int_set_expr    % XXX
            )
    ;       tmzn_int_expr_ite(
                tmzn_ie_ite_sl                  :: src_pos,
                tmzn_ie_ite_cond                :: tmzn_bool_expr,
                tmzn_ie_ite_then                :: tmzn_int_expr,
                tmzn_ie_ite_else                :: tmzn_int_expr
            ).

:- type tmzn_int_array_expr
    --->    tmzn_int_array_expr_consts(
                tmzn_iae_cs_sl                  :: src_pos,
                tmzn_iae_cs_index_ranges        :: list(index_range),
                tmzn_iae_cs_value               :: list(int)
            )
    ;       tmzn_int_array_expr_vars(
                tmzn_iae_vs_sl                  :: src_pos,
                tmzn_iae_vs_index_ranges        :: list(index_range),
                tmzn_iae_vs_vars                :: list(tmzn_int_var)
            )
    ;       tmzn_int_array_expr_exprs(
                tmzn_iae_es_sl                  :: src_pos,
                tmzn_iae_es_index_ranges        :: list(index_range),
                tmzn_iae_es_exprs               :: list(tmzn_int_expr)
            )
    ;       tmzn_int_array_expr_var(
                tmzn_iae_v_sl                   :: src_pos,
                tmzn_iae_v_var                  :: tmzn_int_array_var
            )
    ;       tmzn_int_array_expr_comprehension(
                tmzn_iae_comp_sl                :: src_pos,
                tmzn_iae_comp_head              :: tmzn_int_expr,
                tmzn_iae_comp_generators        :: list(tmzn_generator),
                tmzn_iae_comp_maybe_cond        :: maybe(tmzn_bool_expr)
            )
    ;       tmzn_int_array_expr_from_set(
                tmzn_iae_fs_sl                  :: src_pos,
                tmzn_iae_fs_set                 :: tmzn_int_set_expr
            ).

:- type tmzn_int_set_expr
    --->    tmzn_int_set_expr_const(
                tmzn_ise_c_sl                   :: src_pos,
                tmzn_ise_c_value                :: set(int)
            )
    ;       tmzn_int_set_expr_exprs(
                tmzn_ise_es_sl                  :: src_pos,
                tmzn_ise_es_exprs               :: set(tmzn_int_expr)
            )
    ;       tmzn_int_set_expr_var(
                tmzn_ise_v_sl                   :: src_pos,
                tmzn_ise_v_var                  :: tmzn_int_set_var
            )
    ;       tmzn_int_set_expr_i2is(
                tmzn_ise_i2is_sl                :: src_pos,
                tmzn_ise_i2is_op                :: int_to_int_set_op,
                tmzn_ise_i2is_arg1              :: tmzn_int_expr
            )
    ;       tmzn_int_set_expr_ii2is(
                tmzn_ise_ii2is_sl               :: src_pos,
                tmzn_ise_ii2is_op               :: int_int_to_int_set_op,
                tmzn_ise_ii2is_arg1             :: tmzn_int_expr,
                tmzn_ise_ii2is_arg2             :: tmzn_int_expr
            )
    ;       tmzn_int_set_expr_isis2is(
                tmzn_ise_isis2is_sl             :: src_pos,
                tmzn_ise_isis2is_op             :: set_set_to_set_op,
                tmzn_ise_isis2is_arg1           :: tmzn_int_set_expr,
                tmzn_ise_isis2is_arg2           :: tmzn_int_set_expr
            )
    ;       tmzn_int_set_expr_comprehension(
                tmzn_ise_comp_sl                :: src_pos,
                tmzn_ise_comp_head              :: tmzn_int_expr,
                tmzn_ise_comp_generators        :: list(tmzn_generator),
                tmzn_ise_comp_maybe_cond        :: maybe(tmzn_bool_expr)
            ).

:- type tmzn_int_set_array_expr
    --->    tmzn_int_set_array_expr_consts(
                tmzn_isae_cs_sl                 :: src_pos,
                tmzn_isae_cs_index_ranges       :: list(index_range),
                tmzn_isae_cs_value              :: list(set(int))
            )
    ;       tmzn_int_set_array_expr_vars(
                tmzn_isae_vs_sl                 :: src_pos,
                tmzn_isae_vs_index_ranges       :: list(index_range),
                tmzn_isae_vs_vars               :: list(tmzn_int_set_var)
            )
    ;       tmzn_int_set_array_expr_exprs(
                tmzn_isae_es_sl                 :: src_pos,
                tmzn_isae_es_index_ranges       :: list(index_range),
                tmzn_isae_es_exprs              :: list(tmzn_int_set_expr)
            )
    ;       tmzn_int_set_array_expr_var(
                tmzn_isae_v_sl                  :: src_pos,
                tmzn_isae_v_var                 :: tmzn_int_set_array_var
            )
    ;       tmzn_int_set_array_expr_comprehension(
                tmzn_isae_comp_sl               :: src_pos,
                tmzn_isae_comp_head             :: tmzn_int_set_expr,
                tmzn_isae_comp_generators       :: list(tmzn_generator),
                tmzn_isae_comp_maybe_cond       :: maybe(tmzn_bool_expr)
            ).

:- type tmzn_float_expr
    --->    tmzn_float_expr_const(
                tmzn_fe_c_sl                    :: src_pos,
                tmzn_fe_c_value                 :: float
            )
    ;       tmzn_float_expr_var(
                tmzn_fe_v_sl                    :: src_pos,
                tmzn_fe_v_var                   :: tmzn_float_var
            )
%   ;       tmzn_float_expr_int(
%               tmzn_fe_i_sl                    :: src_pos,
%               tmzn_fe_i_int                   :: tmzn_int_expr
%           )
    ;       tmzn_float_expr_i2f(
                tmzn_fe_i2f_sl                  :: src_pos,
                tmzn_fe_i2f_op                  :: int_to_float_op,
                tmzn_fe_i2f_arg1                :: tmzn_int_expr
            )
    ;       tmzn_float_expr_f2f(
                tmzn_fe_f2f_sl                  :: src_pos,
                tmzn_fe_f2f_op                  :: float_to_float_op,
                tmzn_fe_f2f_arg1                :: tmzn_float_expr
            )
    ;       tmzn_float_expr_ff2f(
                tmzn_fe_ff2f_sl                 :: src_pos,
                tmzn_fe_ff2f_op                 :: float_float_to_float_op,
                tmzn_fe_ff2f_arg1               :: tmzn_float_expr,
                tmzn_fe_ff2f_arg2               :: tmzn_float_expr
            )
    ;       tmzn_float_expr_ite(
                tmzn_fe_ite_sl                  :: src_pos,
                tmzn_fe_ite_cond                :: tmzn_bool_expr,
                tmzn_fe_ite_then                :: tmzn_float_expr,
                tmzn_fe_ite_else                :: tmzn_float_expr
            ).

:- type tmzn_float_array_expr
    --->    tmzn_float_array_expr_consts(
                tmzn_fae_cs_sl                  :: src_pos,
                tmzn_fae_cs_index_ranges        :: list(index_range),
                tmzn_fae_cs_value               :: list(float)
            )
    ;       tmzn_float_array_expr_vars(
                tmzn_fae_vs_sl                  :: src_pos,
                tmzn_fae_vs_index_ranges        :: list(index_range),
                tmzn_fae_vs_vars                :: list(tmzn_float_var)
            )
    ;       tmzn_float_array_expr_exprs(
                tmzn_fae_es_sl                  :: src_pos,
                tmzn_fae_es_index_ranges        :: list(index_range),
                tmzn_fae_es_exprs               :: list(tmzn_float_expr)
            )
    ;       tmzn_float_array_expr_var(
                tmzn_fae_v_sl                   :: src_pos,
                tmzn_fae_v_var                  :: tmzn_float_array_var
            )
    ;       tmzn_float_array_expr_comprehension(
                tmzn_fae_comp_sl                :: src_pos,
                tmzn_fae_comp_head              :: tmzn_float_expr,
                tmzn_fae_comp_generators        :: list(tmzn_generator),
                tmzn_fae_comp_maybe_cond        :: maybe(tmzn_bool_expr)
            ).

:- type tmzn_float_set_expr
    --->    tmzn_float_set_expr_const(
                tmzn_fse_c_sl                   :: src_pos,
                tmzn_fse_c_value                :: set(float)
            )
    ;       tmzn_float_set_expr_var(
                tmzn_fse_v_sl                   :: src_pos,
                tmzn_fse_v_var                  :: tmzn_float_set_var
            ).

% Not yet needed.
% :- type tmzn_float_set_array_expr
%     --->    tmzn_float_set_array_expr_consts(
%                 tmzn_fsae_cs_sl                 :: src_pos,
%                 tmzn_fsae_cs_value              :: list(float_set)
%             )
%     ;       tmzn_float_set_array_expr_vars(
%                 tmzn_fsae_vs_sl                 :: src_pos,
%                 tmzn_fsae_vs_vars               :: list(tmzn_float_set_var)
%             )
%     ;       tmzn_float_set_array_expr_exprs(
%                 tmzn_fsae_es_sl                 :: src_pos,
%                 tmzn_fsae_es_exprs              :: list(tmzn_float_set_expr)
%             )
%     ;       tmzn_float_set_array_expr_var(
%                 tmzn_fsae_v_sl                  :: src_pos,
%                 tmzn_fsae_v_var                 :: tmzn_float_set_array_var
%             ).

:- type tmzn_string_expr
    --->    tmzn_string_expr_const(
                tmzn_se_c_sl                    :: src_pos,
                tmzn_se_c_value                 :: string
            )
    ;       tmzn_string_expr_var(
                tmzn_se_v_sl                    :: src_pos,
                tmzn_se_v_var                   :: tmzn_string_var
            )
    ;       tmzn_string_expr_ss2s(
                tmzn_se_ss2s_sl                 :: src_pos,
                tmzn_se_ss2s_op                 :: string_string_to_string_op,
                tmzn_se_ss2s_arg1               :: tmzn_string_expr,
                tmzn_se_ss2s_arg2               :: tmzn_string_expr
            )
    ;       tmzn_string_expr_sa2s(
                tmzn_se_sa2s_sl                 :: src_pos,
                tmzn_se_sa2s_op                 :: string_array_to_string_op,
                tmzn_se_sa2s_arg1               :: tmzn_string_array_expr
            )
    ;       tmzn_string_expr_ssa2s(
                tmzn_se_ssa2s_sl          :: src_pos,
                tmzn_se_ssa2s_op          :: string_string_array_to_string_op,
                tmzn_se_ssa2s_arg1        :: tmzn_string_expr,
                tmzn_se_ssa2s_arg2        :: tmzn_string_array_expr
            )
    ;       tmzn_string_expr_x2s(
                tmzn_se_x2s_sl                  :: src_pos,
                tmzn_se_x2s_op                  :: general_to_string_op,
                tmzn_se_x2s_arg1                :: tmzn_general_expr
            )
    ;       tmzn_string_expr_ii2s(
                tmzn_se_ii2s_sl                 :: src_pos,
                tmzn_se_ii2s_op                 :: int_int_to_string_op,
                tmzn_se_ii2s_arg1               :: tmzn_int_expr,
                tmzn_se_ii2s_arg2               :: tmzn_int_expr
            )
    ;       tmzn_string_expr_iif2s(
                tmzn_se_iif2s_sl                :: src_pos,
                tmzn_se_iif2s_op                :: int_int_float_to_string_op,
                tmzn_se_iif2s_arg1              :: tmzn_int_expr,
                tmzn_se_iif2s_arg2              :: tmzn_int_expr,
                tmzn_se_iif2s_arg3              :: tmzn_float_expr
            )
    ;       tmzn_string_expr_ite(
                tmzn_se_ite_sl                  :: src_pos,
                tmzn_se_ite_cond                :: tmzn_bool_expr,
                tmzn_se_ite_then                :: tmzn_string_expr,
                tmzn_se_ite_else                :: tmzn_string_expr
            ).

:- type tmzn_string_array_expr
    --->    tmzn_string_array_expr_consts(
                tmzn_sae_cs_sl                  :: src_pos,
                tmzn_sae_cs_index_ranges        :: list(index_range),
                tmzn_sae_cs_value               :: list(string)
            )
    ;       tmzn_string_array_expr_exprs(
                tmzn_sae_es_sl                  :: src_pos,
                tmzn_sae_es_index_ranges        :: list(index_range),
                tmzn_sae_es_exprs               :: list(tmzn_string_expr)
            )
    ;       tmzn_string_array_expr_var(
                tmzn_sae_v_sl                   :: src_pos,
                tmzn_sae_v_var                  :: tmzn_string_array_var
            )
    ;       tmzn_string_array_expr_sasa2sa(
                tmzn_sae_sasa2sa_sl             :: src_pos,
                tmzn_sae_sasa2sa_op             :: array_array_to_array_op,
                tmzn_sae_sasa2sa_arg1           :: tmzn_string_array_expr,
                tmzn_sae_sasa2sa_arg2           :: tmzn_string_array_expr
            )
    ;       tmzn_string_array_expr_comprehension(
                tmzn_sae_comp_sl                :: src_pos,
                tmzn_sae_comp_head              :: tmzn_string_expr,
                tmzn_sae_comp_generators        :: list(tmzn_generator),
                tmzn_sae_comp_maybe_cond        :: maybe(tmzn_bool_expr)
            ).

%-----------------------------------------------------------------------------%

:- func get_src_pos_from_bool_expr(tmzn_bool_expr) = src_pos.
:- func get_src_pos_from_bool_array_expr(tmzn_bool_array_expr) = src_pos.
:- func get_src_pos_from_int_expr(tmzn_int_expr) = src_pos.
:- func get_src_pos_from_int_array_expr(tmzn_int_array_expr) = src_pos.
:- func get_src_pos_from_int_set_expr(tmzn_int_set_expr) = src_pos.
:- func get_src_pos_from_int_set_array_expr(tmzn_int_set_array_expr) = src_pos.
:- func get_src_pos_from_float_expr(tmzn_float_expr) = src_pos.
:- func get_src_pos_from_float_array_expr(tmzn_float_array_expr) = src_pos.
:- func get_src_pos_from_float_set_expr(tmzn_float_set_expr) = src_pos.
:- func get_src_pos_from_string_expr(tmzn_string_expr) = src_pos.
:- func get_src_pos_from_string_array_expr(tmzn_string_array_expr) = src_pos.

%-----------------------------------------------------------------------------%
% Variables.
%-----------------------------------------------------------------------------%

:- type tmzn_bool_var
    --->    tmzn_bool_var_named(string)
    ;       tmzn_bool_var_anon
    ;       tmzn_bool_var_array_slot(tmzn_bool_array_expr, indexes).

:- type tmzn_bool_array_var
    --->    tmzn_bool_array_var_named(string)
    ;       tmzn_bool_array_var_anon.

:- type tmzn_int_var
    --->    tmzn_int_var_named(string)
    ;       tmzn_int_var_anon
    ;       tmzn_int_var_array_slot(tmzn_int_array_expr, indexes).

:- type tmzn_int_array_var
    --->    tmzn_int_array_var_named(string)
    ;       tmzn_int_array_var_anon.

:- type tmzn_int_set_var
    --->    tmzn_int_set_var_named(string)
    ;       tmzn_int_set_var_anon
    ;       tmzn_int_set_var_array_slot(tmzn_int_set_array_expr, indexes).

:- type tmzn_int_set_array_var
    --->    tmzn_int_set_array_var_named(string)
    ;       tmzn_int_set_array_var_anon.

:- type tmzn_float_var
    --->    tmzn_float_var_named(string)
    ;       tmzn_float_var_anon
    ;       tmzn_float_var_array_slot(tmzn_float_array_expr, indexes).

:- type tmzn_float_array_var
    --->    tmzn_float_array_var_named(string)
    ;       tmzn_float_array_var_anon.

:- type tmzn_float_set_var
    --->    tmzn_float_set_var_named(string)
    ;       tmzn_float_set_var_anon.
    % Not needed (yet).
    % ;       tmzn_float_set_var_array_slot(tmzn_float_set_array_expr, indexes).

:- type tmzn_string_var
    --->    tmzn_string_var_named(string)
    ;       tmzn_string_var_anon
    ;       tmzn_string_var_array_slot(tmzn_string_array_expr, indexes).

:- type tmzn_string_array_var
    --->    tmzn_string_array_var_named(string).

:- type indexes == list(tmzn_int_expr).

%-----------------------------------------------------------------------------%
% Other expression components.
%-----------------------------------------------------------------------------%

:- type tmzn_generator
    --->    tmzn_generator(
                list(string),
                tmzn_general_expr
            ).

%-----------------------------------------------------------------------------%
% Annotations on variable declarations.
%-----------------------------------------------------------------------------%

:- type tmzn_var_ann
    --->    var_ann_is_defined_var
    ;       var_ann_is_defined_var_eqv(string)
            % XXX should be general var
    ;       var_ann_var_is_introduced
    ;       var_ann_output_var
    ;       var_ann_output_array(list(set(int)))
            % XXX should be list(int_range)
    ;       var_ann_general(string, list(tmzn_ann_expr)).

%-----------------------------------------------------------------------------%
% Annotations on constraints.
%-----------------------------------------------------------------------------%

:- type tmzn_constr_ann
    --->    constr_ann_defines_var(tmzn_defined_var)
    ;       constr_ann_domain_consistency
    ;       constr_ann_general(string, list(tmzn_general_expr)).

:- type tmzn_defined_var
    --->    tmzn_def_bool_var(tmzn_bool_var)
    ;       tmzn_def_int_var(tmzn_int_var)
    ;       tmzn_def_int_set_var(tmzn_int_set_var)
    ;       tmzn_def_float_var(tmzn_float_var).

%-----------------------------------------------------------------------------%
% Annotations on solve goals.
%-----------------------------------------------------------------------------%

:- type tmzn_search_params
    --->    int_search(
                tmzn_int_array_expr,
                tmzn_search_var_choice,
                tmzn_search_assignment,
                tmzn_search_strategy
            )
    ;       set_search(
                tmzn_int_set_array_expr,
                tmzn_search_var_choice,
                tmzn_search_assignment,
                tmzn_search_strategy
            )
    ;       bool_search(
                tmzn_bool_array_expr,
                tmzn_search_var_choice,
                tmzn_search_assignment,
                tmzn_search_strategy
            )
    ;       seq_search(
                list(tmzn_search_params)
            ).

:- type tmzn_search_var_choice
    --->    svc_input_order
    ;       svc_smallest
    ;       svc_largest
    ;       svc_occurrence
    ;       svc_first_fail
    ;       svc_anti_first_fail
    ;       svc_most_constrained
    ;       svc_max_regret.

:- type tmzn_search_assignment
    --->    sa_indomain
    ;       sa_indomain_min
    ;       sa_indomain_max
    ;       sa_indomain_median
    ;       sa_indomain_middle
    ;       sa_indomain_split
    ;       sa_indomain_reverse_split
    ;       sa_indomain_interval
    ;       sa_indomain_random.

:- type tmzn_search_strategy
    --->    ss_complete.

:- type tmzn_limit
    --->    time_limit(tmzn_int_expr).

:- type tmzn_solve_ann
    --->    solve_ann_search(tmzn_search_params)
    ;       solve_ann_limit(tmzn_limit, tmzn_search_params).

%-----------------------------------------------------------------------------%

:- type src_pos
    --->    src_pos(nest_pos, src_locn).

:- type nest_pos
    --->    outermost(
                % This shows that construct X is not inside any other
                % construct.

                % The nature of construct X.
                outer_pos
            )
    ;       nest(
                % This shows that construct X is inside construct Y.

                % The src_pos of construct Y.
                src_pos,

                % The step from construct Y to construct X.
                inner_step
            ).

:- type assign_kind
    --->    assign_explicit
    ;       assign_from_var_decl.

:- type constr_kind
    --->    constr_explicit
    ;       constr_from_assign
    ;       constr_from_var_decl.

:- type outer_pos
    --->    op_var_decl
    ;       op_assign(assign_kind)
    ;       op_constraint(constr_kind)
    ;       op_output
    ;       op_solve
    ;       op_predfunc
    ;       op_enum
    ;       op_type_inst_syn
    ;       op_annotation.

:- type inner_step
            % The top levels of declarations.
    --->    is_constr_expr
    ;       is_var_decl_init
    ;       is_init_index_type(int)
    ;       is_init_elt_type

            % Static data.
    ;       is_simple_array(int)
    ;       is_lit_set(int)

            % Operations.
    ;       is_unop_arg(string)
    ;       is_binop_arg(string, left_right)
    ;       is_array_id
    ;       is_index(int)
    ;       is_arg(string, int)
    ;       is_compre_cond
    ;       is_compre_head
    ;       is_compre_array(int)
    ;       is_cond
    ;       is_then
    ;       is_else.

:- type left_right
    --->    left
    ;       right.

%-----------------------------------------------------------------------------%

:- pred compare_var_decl_items(tmzn_var_decl_item::in, tmzn_var_decl_item::in,
    comparison_result::out) is det.

:- pred compare_assign_items(tmzn_assign_item::in, tmzn_assign_item::in,
    comparison_result::out) is det.

:- pred compare_constraint_items(
    tmzn_constraint_item::in, tmzn_constraint_item::in,
    comparison_result::out) is det.

%-----------------------------------------------------------------------------%

:- pred try_project_bool_expr_to_const(tmzn_bool_expr::in,
    bool::out) is semidet.
:- pred try_project_bool_expr_to_var(tmzn_bool_expr::in,
    tmzn_bool_var::out) is semidet.
:- pred try_project_int_expr_to_const(tmzn_int_expr::in,
    int::out) is semidet.
:- pred try_project_int_expr_to_var(tmzn_int_expr::in,
    tmzn_int_var::out) is semidet.
:- pred try_project_int_set_expr_to_const(tmzn_int_set_expr::in,
    set(int)::out) is semidet.
:- pred try_project_int_set_expr_to_var(tmzn_int_set_expr::in,
    tmzn_int_set_var::out) is semidet.
:- pred try_project_float_expr_to_const(tmzn_float_expr::in,
    float::out) is semidet.
:- pred try_project_float_expr_to_var(tmzn_float_expr::in,
    tmzn_float_var::out) is semidet.
:- pred try_project_string_expr_to_const(tmzn_string_expr::in,
    string::out) is semidet.

%-----------------------------------------------------------------------------%

:- implementation.

get_src_pos_from_bool_expr(BoolExpr) = SrcPos :-
    ( BoolExpr = tmzn_bool_expr_const(SrcPos, _)
    ; BoolExpr = tmzn_bool_expr_var(SrcPos, _)
    ; BoolExpr = tmzn_bool_expr_b2b(SrcPos, _, _)
    ; BoolExpr = tmzn_bool_expr_bb2b(SrcPos, _, _, _)
    ; BoolExpr = tmzn_bool_expr_ba2b(SrcPos, _, _)
    ; BoolExpr = tmzn_bool_expr_ii2b(SrcPos, _, _, _)
    ; BoolExpr = tmzn_bool_expr_iis2b(SrcPos, _, _, _)
    ; BoolExpr = tmzn_bool_expr_isis2b(SrcPos, _, _, _)
    ; BoolExpr = tmzn_bool_expr_ff2b(SrcPos, _, _, _)
    ; BoolExpr = tmzn_bool_expr_ffs2b(SrcPos, _, _, _)
    ; BoolExpr = tmzn_bool_expr_fsfs2b(SrcPos, _, _, _)
    ; BoolExpr = tmzn_bool_expr_ss2b(SrcPos, _, _, _)
    ; BoolExpr = tmzn_bool_expr_ite(SrcPos, _, _, _)
    ; BoolExpr = tmzn_bool_expr_is_fixed(SrcPos, _)
    ; BoolExpr = tmzn_bool_expr_general(SrcPos, _, _)
    ).

get_src_pos_from_bool_array_expr(BoolArrayExpr) = SrcPos :-
    ( BoolArrayExpr = tmzn_bool_array_expr_consts(SrcPos, _, _)
    ; BoolArrayExpr = tmzn_bool_array_expr_vars(SrcPos, _, _)
    ; BoolArrayExpr = tmzn_bool_array_expr_exprs(SrcPos, _, _)
    ; BoolArrayExpr = tmzn_bool_array_expr_var(SrcPos, _)
    ; BoolArrayExpr = tmzn_bool_array_expr_comprehension(SrcPos, _, _, _)
    ).

get_src_pos_from_int_expr(IntExpr) = SrcPos :-
    ( IntExpr = tmzn_int_expr_const(SrcPos, _)
    ; IntExpr = tmzn_int_expr_var(SrcPos, _)
    ; IntExpr = tmzn_int_expr_b2i(SrcPos, _, _)
    ; IntExpr = tmzn_int_expr_i2i(SrcPos, _, _)
    ; IntExpr = tmzn_int_expr_ii2i(SrcPos, _, _, _)
    ; IntExpr = tmzn_int_expr_is2i(SrcPos, _, _)
    ; IntExpr = tmzn_int_expr_ia2i(SrcPos, _, _)
    ; IntExpr = tmzn_int_expr_xs2i(SrcPos, _, _)
    ; IntExpr = tmzn_int_expr_ite(SrcPos, _, _, _)
    ).

get_src_pos_from_int_array_expr(IntArrayExpr) = SrcPos :-
    ( IntArrayExpr = tmzn_int_array_expr_consts(SrcPos, _, _)
    ; IntArrayExpr = tmzn_int_array_expr_vars(SrcPos, _, _)
    ; IntArrayExpr = tmzn_int_array_expr_exprs(SrcPos, _, _)
    ; IntArrayExpr = tmzn_int_array_expr_var(SrcPos, _)
    ; IntArrayExpr = tmzn_int_array_expr_comprehension(SrcPos, _, _, _)
    ; IntArrayExpr = tmzn_int_array_expr_from_set(SrcPos, __)
    ).

get_src_pos_from_int_set_expr(IntSetExpr) = SrcPos :-
    ( IntSetExpr = tmzn_int_set_expr_const(SrcPos, _)
    ; IntSetExpr = tmzn_int_set_expr_exprs(SrcPos, _)
    ; IntSetExpr = tmzn_int_set_expr_var(SrcPos, _)
    ; IntSetExpr = tmzn_int_set_expr_i2is(SrcPos, _, _)
    ; IntSetExpr = tmzn_int_set_expr_ii2is(SrcPos, _, _, _)
    ; IntSetExpr = tmzn_int_set_expr_isis2is(SrcPos, _, _, _)
    ; IntSetExpr = tmzn_int_set_expr_comprehension(SrcPos, _, _, _)
    ).

get_src_pos_from_int_set_array_expr(IntSetArrayExpr) = SrcPos :-
    ( IntSetArrayExpr = tmzn_int_set_array_expr_consts(SrcPos, _, _)
    ; IntSetArrayExpr = tmzn_int_set_array_expr_vars(SrcPos, _, _)
    ; IntSetArrayExpr = tmzn_int_set_array_expr_exprs(SrcPos, _, _)
    ; IntSetArrayExpr = tmzn_int_set_array_expr_var(SrcPos, _)
    ; IntSetArrayExpr = tmzn_int_set_array_expr_comprehension(SrcPos, _, _, _)
    ).

get_src_pos_from_float_expr(FloatExpr) = SrcPos :-
    ( FloatExpr = tmzn_float_expr_const(SrcPos, _)
    ; FloatExpr = tmzn_float_expr_var(SrcPos, _)
    ; FloatExpr = tmzn_float_expr_i2f(SrcPos, _, _)
    ; FloatExpr = tmzn_float_expr_f2f(SrcPos, _, _)
    ; FloatExpr = tmzn_float_expr_ff2f(SrcPos, _, _, _)
    ; FloatExpr = tmzn_float_expr_ite(SrcPos, _, _, _)
    ).

get_src_pos_from_float_array_expr(FloatArrayExpr) = SrcPos :-
    ( FloatArrayExpr = tmzn_float_array_expr_consts(SrcPos, _, _)
    ; FloatArrayExpr = tmzn_float_array_expr_vars(SrcPos, _, _)
    ; FloatArrayExpr = tmzn_float_array_expr_exprs(SrcPos, _, _)
    ; FloatArrayExpr = tmzn_float_array_expr_var(SrcPos, _)
    ; FloatArrayExpr = tmzn_float_array_expr_comprehension(SrcPos, _, _, _)
    ).

get_src_pos_from_float_set_expr(FloatSetExpr) = SrcPos :-
    ( FloatSetExpr = tmzn_float_set_expr_const(SrcPos, _)
    ; FloatSetExpr = tmzn_float_set_expr_var(SrcPos, _)
    ).

get_src_pos_from_string_expr(StringExpr) = SrcPos :-
    ( StringExpr = tmzn_string_expr_const(SrcPos, _)
    ; StringExpr = tmzn_string_expr_var(SrcPos, _)
    ; StringExpr = tmzn_string_expr_ss2s(SrcPos, _, _, _)
    ; StringExpr = tmzn_string_expr_sa2s(SrcPos, _, _)
    ; StringExpr = tmzn_string_expr_ssa2s(SrcPos, _, _, _)
    ; StringExpr = tmzn_string_expr_x2s(SrcPos, _, _)
    ; StringExpr = tmzn_string_expr_ii2s(SrcPos, _, _, _)
    ; StringExpr = tmzn_string_expr_iif2s(SrcPos, _, _, _, _)
    ; StringExpr = tmzn_string_expr_ite(SrcPos, _, _, _)
    ).

get_src_pos_from_string_array_expr(StringArrayExpr) = SrcPos :-
    ( StringArrayExpr = tmzn_string_array_expr_consts(SrcPos, _, _)
    ; StringArrayExpr = tmzn_string_array_expr_exprs(SrcPos, _, _)
    ; StringArrayExpr = tmzn_string_array_expr_var(SrcPos, _)
    ; StringArrayExpr = tmzn_string_array_expr_sasa2sa(SrcPos, _, _, _)
    ; StringArrayExpr = tmzn_string_array_expr_comprehension(SrcPos, _, _, _)
    ).

%-----------------------------------------------------------------------------%

compare_var_decl_items(ItemA, ItemB, Result) :-
    compare_src_pos(ItemA ^ tmzn_var_decl_locn, ItemB ^ tmzn_var_decl_locn,
        Result).

compare_assign_items(ItemA, ItemB, Result) :-
    compare_src_pos(ItemA ^ tmzn_assign_locn, ItemB ^ tmzn_assign_locn,
        Result).

compare_constraint_items(ItemA, ItemB, Result) :-
    compare_src_pos(ItemA ^ tmzn_constr_locn, ItemB ^ tmzn_constr_locn,
        Result).

:- pred compare_src_pos(src_pos::in, src_pos::in,
    comparison_result::out) is det.

compare_src_pos(SrcPosA, SrcPosB, Result) :-
    SrcPosA = src_pos(_, SrcLocnA),
    SrcPosB = src_pos(_, SrcLocnB),
    (
        SrcLocnA = builtin,
        SrcLocnB = builtin,
        Result = (=)
    ;
        SrcLocnA = builtin,
        SrcLocnB = src_locn(_, _),
        Result = (<)
    ;
        SrcLocnA = builtin,
        SrcLocnB = unknown,
        Result = (<)
    ;
        SrcLocnA = src_locn(_, _),
        SrcLocnB = builtin,
        Result = (>)
    ;
        SrcLocnA = src_locn(FileNameA, LineNumberA),
        SrcLocnB = src_locn(FileNameB, LineNumberB),
        compare(FileNameResult, FileNameA, FileNameB),
        (
            FileNameResult = (<),
            Result = FileNameResult
        ;
            FileNameResult = (=),
            compare(Result, LineNumberA, LineNumberB)
        ;
            FileNameResult = (>),
            Result = FileNameResult
        )
    ;
        SrcLocnA = src_locn(_, _),
        SrcLocnB = unknown,
        Result = (<)
    ;
        SrcLocnA = unknown,
        SrcLocnB = builtin,
        Result = (>)
    ;
        SrcLocnA = unknown,
        SrcLocnB = src_locn(_, _),
        Result = (>)
    ;
        SrcLocnA = unknown,
        SrcLocnB = unknown,
        Result = (=)
    ).

%-----------------------------------------------------------------------------%

try_project_bool_expr_to_const(BoolExpr, Bool) :-
    BoolExpr = tmzn_bool_expr_const(_, Bool).

try_project_bool_expr_to_var(BoolExpr, BoolVar) :-
    BoolExpr = tmzn_bool_expr_var(_, BoolVar).

%------------%

try_project_int_expr_to_const(IntExpr, Int) :-
    IntExpr = tmzn_int_expr_const(_, Int).

try_project_int_expr_to_var(IntExpr, IntVar) :-
    IntExpr = tmzn_int_expr_var(_, IntVar).

%------------%

try_project_int_set_expr_to_const(IntSetExpr, IntSet) :-
    IntSetExpr = tmzn_int_set_expr_const(_, IntSet).

try_project_int_set_expr_to_var(IntSetExpr, IntSetVar) :-
    IntSetExpr = tmzn_int_set_expr_var(_, IntSetVar).

%------------%

try_project_float_expr_to_const(FloatExpr, Float) :-
    FloatExpr = tmzn_float_expr_const(_, Float).

try_project_float_expr_to_var(FloatExpr, FloatVar) :-
    FloatExpr = tmzn_float_expr_var(_, FloatVar).

%------------%

try_project_string_expr_to_const(StrExpr, Str) :-
    StrExpr = tmzn_string_expr_const(_, Str).

%-----------------------------------------------------------------------------%
:- end_module tmzn_ast.
%-----------------------------------------------------------------------------%
