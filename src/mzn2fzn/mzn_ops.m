%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Authors:
% Ralph Becket
% Zoltan Somogyi
%
% Types and predicates for representing MiniZinc operations.
%
%-----------------------------------------------------------------------------%

:- module mzn_ops.
:- interface.

:- import_module bool.

%-----------------------------------------------------------------------------%

:- type bool_to_int_op
    --->    b2i_bool2int.

:- type bool_to_bool_op
    --->    b2b_not
    ;       b2b_lb
    ;       b2b_ub
    ;       b2b_fix.

:- type bool_bool_to_bool_op
    --->    bb2b_and
    ;       bb2b_or
    ;       bb2b_xor
    ;       bb2b_imp2r  % implies to right
    ;       bb2b_imp2l  % implies to left
    ;       bb2b_biimp
    ;       bb2b_min
    ;       bb2b_max
    ;       bb2b_eq     % =
    ;       bb2b_ee     % ==    XXX why is this needed?
    ;       bb2b_ne
    ;       bb2b_lt
    ;       bb2b_le
    ;       bb2b_gt
    ;       bb2b_ge.

:- type bool_array_to_bool_op
    --->    ba2b_exists
    ;       ba2b_forall
    ;       ba2b_iffall
    ;       ba2b_xorall.

:- pred is_bool_to_int_op(string, bool_to_int_op).
:- mode is_bool_to_int_op(in, out) is semidet.
:- mode is_bool_to_int_op(out, in) is det.

:- pred is_bool_to_bool_op(string, bool_to_bool_op).
:- mode is_bool_to_bool_op(in, out) is semidet.
:- mode is_bool_to_bool_op(out, in) is det.

:- pred is_bool_bool_to_bool_op(string, bool_bool_to_bool_op).
:- mode is_bool_bool_to_bool_op(in, out) is semidet.
:- mode is_bool_bool_to_bool_op(out, in) is det.

:- pred is_bool_array_to_bool_op(string, bool_array_to_bool_op).
:- mode is_bool_array_to_bool_op(in, out) is semidet.
:- mode is_bool_array_to_bool_op(out, in) is det.

%-----------------------------------------------------------------------------%

:- type int_to_float_op
    --->    i2f_int2float.

:- type int_to_int_op
    --->    i2i_add
    ;       i2i_sub
    ;       i2i_abs
    ;       i2i_lb
    ;       i2i_ub
    ;       i2i_dom_size
    ;       i2i_fix.

:- type int_to_int_set_op
    --->    i2is_dom.

:- type int_int_to_int_op
    --->    ii2i_add
    ;       ii2i_sub
    ;       ii2i_mul
    ;       ii2i_div
    ;       ii2i_mod
    ;       ii2i_pow
    ;       ii2i_min
    ;       ii2i_max.

:- type int_int_to_int_set_op
    --->    ii2is_range.

:- type int_int_to_bool_op
    --->    ii2b_eq     % =
    ;       ii2b_ee     % ==    XXX why is this needed?
    ;       ii2b_ne
    ;       ii2b_lt
    ;       ii2b_le
    ;       ii2b_gt
    ;       ii2b_ge.

:- type int_int_set_to_bool_op
    --->    iis2b_in.

:- pred is_int_to_float_op(string, int_to_float_op).
:- mode is_int_to_float_op(in, out) is semidet.
:- mode is_int_to_float_op(out, in) is det.

:- pred is_int_to_int_op(string, int_to_int_op).
:- mode is_int_to_int_op(in, out) is semidet.
:- mode is_int_to_int_op(out, in) is det.

:- pred is_int_to_int_set_op(string, int_to_int_set_op).
:- mode is_int_to_int_set_op(in, out) is semidet.
:- mode is_int_to_int_set_op(out, in) is det.

:- pred is_int_int_to_int_op(string, int_int_to_int_op).
:- mode is_int_int_to_int_op(in, out) is semidet.
:- mode is_int_int_to_int_op(out, in) is det.

:- pred is_int_int_to_int_set_op(string, int_int_to_int_set_op).
:- mode is_int_int_to_int_set_op(in, out) is semidet.
:- mode is_int_int_to_int_set_op(out, in) is det.

:- pred is_int_int_to_bool_op(string, int_int_to_bool_op).
:- mode is_int_int_to_bool_op(in, out) is semidet.
:- mode is_int_int_to_bool_op(out, in) is det.

:- pred is_int_int_set_to_bool_op(string, int_int_set_to_bool_op).
:- mode is_int_int_set_to_bool_op(in, out) is semidet.
:- mode is_int_int_set_to_bool_op(out, in) is det.

%-----------------------------------------------------------------------------%

:- type float_to_float_op
    --->    f2f_add
    ;       f2f_sub
    ;       f2f_lb
    ;       f2f_ub
    ;       f2f_abs
    ;       f2f_sqrt
    ;       f2f_exp
    ;       f2f_ln
    ;       f2f_log10
    ;       f2f_log2
    ;       f2f_sin
    ;       f2f_cos
    ;       f2f_tan
    ;       f2f_sinh
    ;       f2f_cosh
    ;       f2f_tanh
    ;       f2f_asin
    ;       f2f_acos
    ;       f2f_atan
    ;       f2f_fix.

:- type float_to_int_op
    --->    f2i_ceil
    ;       f2i_floor
    ;       f2i_round.

:- type float_to_float_set_op
    --->    f2fs_dom.

:- type float_float_to_float_op
    --->    ff2f_add
    ;       ff2f_sub
    ;       ff2f_mul
    ;       ff2f_div
    ;       ff2f_min
    ;       ff2f_max
    ;       ff2f_pow
    ;       ff2f_log.

:- type float_float_to_float_set_op
    --->    ff2fs_range.

:- type float_float_to_bool_op
    --->    ff2b_eq     % =
    ;       ff2b_ee     % ==    XXX why is this needed?
    ;       ff2b_ne
    ;       ff2b_lt
    ;       ff2b_le
    ;       ff2b_gt
    ;       ff2b_ge.

:- type float_float_set_to_bool_op
    --->    ffs2b_in.

:- pred is_float_to_float_op(string, float_to_float_op).
:- mode is_float_to_float_op(in, out) is semidet.
:- mode is_float_to_float_op(out, in) is det.

:- pred is_float_to_int_op(string, float_to_int_op).
:- mode is_float_to_int_op(in, out) is semidet.
:- mode is_float_to_int_op(out, in) is det.

:- pred is_float_to_float_set_op(string, float_to_float_set_op).
:- mode is_float_to_float_set_op(in, out) is semidet.
:- mode is_float_to_float_set_op(out, in) is det.

:- pred is_float_float_to_float_op(string, float_float_to_float_op).
:- mode is_float_float_to_float_op(in, out) is semidet.
:- mode is_float_float_to_float_op(out, in) is det.

:- pred is_float_float_to_float_set_op(string, float_float_to_float_set_op).
:- mode is_float_float_to_float_set_op(in, out) is semidet.
:- mode is_float_float_to_float_set_op(out, in) is det.

:- pred is_float_float_to_bool_op(string, float_float_to_bool_op).
:- mode is_float_float_to_bool_op(in, out) is semidet.
:- mode is_float_float_to_bool_op(out, in) is det.

:- pred is_float_float_set_to_bool_op(string, float_float_set_to_bool_op).
:- mode is_float_float_set_to_bool_op(in, out) is semidet.
:- mode is_float_float_set_to_bool_op(out, in) is det.

%-----------------------------------------------------------------------------%

:- type string_string_to_string_op
    --->    ss2s_append.

:- type string_string_to_bool_op
    --->    ss2b_eq     % =
    ;       ss2b_ee     % ==    XXX why is this needed?
    ;       ss2b_ne
    ;       ss2b_lt
    ;       ss2b_le
    ;       ss2b_gt
    ;       ss2b_ge.

:- type string_array_to_string_op
    --->    sa2s_concat.

:- type string_string_array_to_string_op
    --->    ssa2s_join.

:- type general_to_string_op
    --->    x2s_show.

:- type int_int_to_string_op
    --->    ii2s_show_int.

:- type int_int_float_to_string_op
    --->    iif2s_show_float.

:- pred is_string_string_to_string_op(string, string_string_to_string_op).
:- mode is_string_string_to_string_op(in, out) is semidet.
:- mode is_string_string_to_string_op(out, in) is det.

:- pred is_string_string_to_bool_op(string, string_string_to_bool_op).
:- mode is_string_string_to_bool_op(in, out) is semidet.
:- mode is_string_string_to_bool_op(out, in) is det.

:- pred is_string_array_to_string_op(string, string_array_to_string_op).
:- mode is_string_array_to_string_op(in, out) is semidet.
:- mode is_string_array_to_string_op(out, in) is det.

:- pred is_string_string_array_to_string_op(string,
    string_string_array_to_string_op).
:- mode is_string_string_array_to_string_op(in, out) is semidet.
:- mode is_string_string_array_to_string_op(out, in) is det.

:- pred is_general_to_string_op(string, general_to_string_op).
:- mode is_general_to_string_op(in, out) is semidet.
:- mode is_general_to_string_op(out, in) is det.

:- pred is_int_int_to_string_op(string, int_int_to_string_op).
:- mode is_int_int_to_string_op(in, out) is semidet.
:- mode is_int_int_to_string_op(out, in) is det.

:- pred is_int_int_float_to_string_op(string, int_int_float_to_string_op).
:- mode is_int_int_float_to_string_op(in, out) is semidet.
:- mode is_int_int_float_to_string_op(out, in) is det.

%-----------------------------------------------------------------------------%

:- type set_to_int_op
    --->    xs2i_card.

:- type int_set_to_int_op
    --->    is2i_min
    ;       is2i_max.

:- type int_array_to_int_op
    --->    ia2i_sum
    ;       ia2i_product
    ;       ia2i_length
    ;       ia2i_min
    ;       ia2i_max
    ;       ia2i_lb_array
    ;       ia2i_ub_array.

:- type int_set_to_int_set_op
    --->    is2is_ub.

:- type set_set_to_set_op
    --->    xsxs2xs_diff
    ;       xsxs2xs_intersect
    ;       xsxs2xs_union.

:- type set_set_to_bool_op
    --->    xsxs2b_eq
    ;       xsxs2b_ee
    ;       xsxs2b_ne
    ;       xsxs2b_lt
    ;       xsxs2b_le
    ;       xsxs2b_gt
    ;       xsxs2b_ge
    ;       xsxs2b_subset
    ;       xsxs2b_superset.

:- type set_to_array_op
    --->    xs2xa_set2array.

:- pred is_set_to_int_op(string, set_to_int_op).
:- mode is_set_to_int_op(in, out) is semidet.
:- mode is_set_to_int_op(out, in) is det.

:- pred is_int_set_to_int_op(string, int_set_to_int_op).
:- mode is_int_set_to_int_op(in, out) is semidet.
:- mode is_int_set_to_int_op(out, in) is det.

:- pred is_int_array_to_int_op(string, int_array_to_int_op).
:- mode is_int_array_to_int_op(in, out) is semidet.
:- mode is_int_array_to_int_op(out, in) is det.

:- pred is_int_set_to_int_set_op(string, int_set_to_int_set_op).
:- mode is_int_set_to_int_set_op(in, out) is semidet.
:- mode is_int_set_to_int_set_op(out, in) is det.

:- pred is_set_set_to_set_op(string, set_set_to_set_op).
:- mode is_set_set_to_set_op(in, out) is semidet.
:- mode is_set_set_to_set_op(out, in) is det.

:- pred is_set_set_to_bool_op(string, set_set_to_bool_op).
:- mode is_set_set_to_bool_op(in, out) is semidet.
:- mode is_set_set_to_bool_op(out, in) is det.

:- pred is_set_to_array_op(string, set_to_array_op).
:- mode is_set_to_array_op(in, out) is semidet.
:- mode is_set_to_array_op(out, in) is det.

%-----------------------------------------------------------------------------%

:- type array_array_to_array_op
    --->    xaxa2xa_append.

:- pred is_array_array_to_array_op(string, array_array_to_array_op).
:- mode is_array_array_to_array_op(in, out) is semidet.
:- mode is_array_array_to_array_op(out, in) is det.

%-----------------------------------------------------------------------------%

    % is_builtin_op(Name, Arity, IsLogicalOp, NeedToReifyArgs, Type)
    %
    % A table of built-in operators. Against each is an indication of whether
    % it is a logical operator (in which case annotations from the enclosing
    % scope are made visible when flattening the arguments) and, if so,
    % whether the arguments should be flattened in a reified form
    % (e.g., for disjunction).
    %
:- pred is_builtin_op(string::in, int::in, bool::out, bool::out,
    builtin_op_type::out) is semidet.

:- pred builtin_op_table(string, int, bool, bool, builtin_op_type).
:- mode builtin_op_table(in, in, out, out, out) is semidet.
:- mode builtin_op_table(out, out, out, out, in) is det.

:- type builtin_op_type
    --->    bo_dom
    ;       bo_lb
    ;       bo_ub
    ;       bo_dom_array
    ;       bo_lb_array
    ;       bo_ub_array
    ;       bo_dom_size
    ;       bo_exists
    ;       bo_forall
    ;       bo_iffall
    ;       bo_xorall
    ;       bo_not
    ;       bo_abort
    ;       bo_assert
    ;       bo_eq
    ;       bo_ne
    ;       bo_lt
    ;       bo_le
    ;       bo_gt
    ;       bo_ge
    ;       bo_bool2int
    ;       bo_int2float
    ;       bo_and
    ;       bo_or
    ;       bo_xor
    ;       bo_imp2l
    ;       bo_imp2r
    ;       bo_biimp
    ;       bo_negate
    ;       bo_abs
    ;       bo_add
    ;       bo_sub
    ;       bo_mul
    ;       bo_fdiv
    ;       bo_idiv
    ;       bo_mod
    ;       bo_min
    ;       bo_max
    ;       bo_array_min
    ;       bo_array_max
    ;       bo_array_sum
    ;       bo_array_product
    ;       bo_array_length
    ;       bo_ceil
    ;       bo_floor
    ;       bo_round
    ;       bo_exp
    ;       bo_ln
    ;       bo_log10
    ;       bo_log2
    ;       bo_log
    ;       bo_pow
    ;       bo_sqrt
    ;       bo_sin
    ;       bo_cos
    ;       bo_tan
    ;       bo_sinh
    ;       bo_cosh
    ;       bo_tanh
    ;       bo_asin
    ;       bo_acos
    ;       bo_atan
    ;       bo_card
    ;       bo_set2array
    ;       bo_range
    ;       bo_in
    ;       bo_subset
    ;       bo_superset
    ;       bo_diff
    ;       bo_intersect
    ;       bo_union
    ;       bo_array_intersect
    ;       bo_array_union
    ;       bo_append
    ;       bo_array1d
    ;       bo_array2d
    ;       bo_array3d
    ;       bo_array4d
    ;       bo_array5d
    ;       bo_array6d
    ;       bo_index_set
    ;       bo_index_set_1of2
    ;       bo_index_set_2of2
    ;       bo_index_set_1of3
    ;       bo_index_set_2of3
    ;       bo_index_set_3of3
    ;       bo_index_set_1of4
    ;       bo_index_set_2of4
    ;       bo_index_set_3of4
    ;       bo_index_set_4of4
    ;       bo_show
    ;       bo_show_int
    ;       bo_show_float
    ;       bo_concat
    ;       bo_join
    ;       bo_fix.

%-----------------------------------------------------------------------------%

:- implementation.

%-----------------------------------------------------------------------------%

is_bool_to_int_op("bool2int",       b2i_bool2int).

is_bool_to_bool_op("not",           b2b_not).
is_bool_to_bool_op("lb",            b2b_lb).
is_bool_to_bool_op("ub",            b2b_ub).
is_bool_to_bool_op("fix",           b2b_fix).

is_bool_bool_to_bool_op("/\\",      bb2b_and).
is_bool_bool_to_bool_op("\\/",      bb2b_or).
is_bool_bool_to_bool_op("xor",      bb2b_xor).
is_bool_bool_to_bool_op("->",       bb2b_imp2r).
is_bool_bool_to_bool_op("<-",       bb2b_imp2l).
is_bool_bool_to_bool_op("<->",      bb2b_biimp).
is_bool_bool_to_bool_op("min",      bb2b_min).
is_bool_bool_to_bool_op("max",      bb2b_max).
is_bool_bool_to_bool_op("=",        bb2b_eq).
is_bool_bool_to_bool_op("==",       bb2b_ee).
is_bool_bool_to_bool_op("!=",       bb2b_ne).
is_bool_bool_to_bool_op("<",        bb2b_lt).
is_bool_bool_to_bool_op("<=",       bb2b_le).
is_bool_bool_to_bool_op(">",        bb2b_gt).
is_bool_bool_to_bool_op(">=",       bb2b_ge).

is_bool_array_to_bool_op("exists",  ba2b_exists).
is_bool_array_to_bool_op("forall",  ba2b_forall).
is_bool_array_to_bool_op("iffall",  ba2b_iffall).
is_bool_array_to_bool_op("xorall",  ba2b_xorall).

%-----------------------------------------------------------------------------%

is_int_to_float_op("int2float", i2f_int2float).

is_int_to_int_op("+",               i2i_add).
is_int_to_int_op("-",               i2i_sub).
is_int_to_int_op("abs",             i2i_abs).
is_int_to_int_op("lb",              i2i_lb).
is_int_to_int_op("ub",              i2i_ub).
is_int_to_int_op("dom_size",        i2i_dom_size).
is_int_to_int_op("fix",             i2i_fix).

is_int_to_int_set_op("dom",         i2is_dom).

is_int_int_to_int_op("+",           ii2i_add).
is_int_int_to_int_op("-",           ii2i_sub).
is_int_int_to_int_op("*",           ii2i_mul).
is_int_int_to_int_op("div",         ii2i_div).
is_int_int_to_int_op("mod",         ii2i_mod).
is_int_int_to_int_op("pow",         ii2i_pow).
is_int_int_to_int_op("min",         ii2i_min).
is_int_int_to_int_op("max",         ii2i_max).

is_int_int_to_int_set_op("..",      ii2is_range).

is_int_int_to_bool_op("=",          ii2b_eq).
is_int_int_to_bool_op("==",         ii2b_ee).
is_int_int_to_bool_op("!=",         ii2b_ne).
is_int_int_to_bool_op("<",          ii2b_lt).
is_int_int_to_bool_op("<=",         ii2b_le).
is_int_int_to_bool_op(">",          ii2b_gt).
is_int_int_to_bool_op(">=",         ii2b_ge).

is_int_int_set_to_bool_op("in",     iis2b_in).

%-----------------------------------------------------------------------------%

is_float_to_float_op("+",           f2f_add).
is_float_to_float_op("-",           f2f_sub).
is_float_to_float_op("lb",          f2f_lb).
is_float_to_float_op("ub",          f2f_ub).
is_float_to_float_op("abs",         f2f_abs).
is_float_to_float_op("sqrt",        f2f_sqrt).
is_float_to_float_op("exp",         f2f_exp).
is_float_to_float_op("ln",          f2f_ln).
is_float_to_float_op("log10",       f2f_log10).
is_float_to_float_op("log2",        f2f_log2).
is_float_to_float_op("sin",         f2f_sin).
is_float_to_float_op("cos",         f2f_cos).
is_float_to_float_op("tan",         f2f_tan).
is_float_to_float_op("sinh",        f2f_sinh).
is_float_to_float_op("cosh",        f2f_cosh).
is_float_to_float_op("tanh",        f2f_tanh).
is_float_to_float_op("asin",        f2f_asin).
is_float_to_float_op("acos",        f2f_acos).
is_float_to_float_op("atan",        f2f_atan).
is_float_to_float_op("fix",         f2f_fix).

is_float_to_int_op("ceil",          f2i_ceil).
is_float_to_int_op("floor",         f2i_floor).
is_float_to_int_op("round",         f2i_round).

is_float_to_float_set_op("dom",     f2fs_dom).

is_float_float_to_float_op("+",     ff2f_add).
is_float_float_to_float_op("-",     ff2f_sub).
is_float_float_to_float_op("*",     ff2f_mul).
is_float_float_to_float_op("/",     ff2f_div).
is_float_float_to_float_op("min",   ff2f_min).
is_float_float_to_float_op("max",   ff2f_max).
is_float_float_to_float_op("pow",   ff2f_pow).
is_float_float_to_float_op("log",   ff2f_log).

is_float_float_to_float_set_op("..",      ff2fs_range).

is_float_float_to_bool_op("=",      ff2b_eq).
is_float_float_to_bool_op("==",     ff2b_ee).
is_float_float_to_bool_op("!=",     ff2b_ne).
is_float_float_to_bool_op("<",      ff2b_lt).
is_float_float_to_bool_op("<=",     ff2b_le).
is_float_float_to_bool_op(">",      ff2b_gt).
is_float_float_to_bool_op(">=",     ff2b_ge).

is_float_float_set_to_bool_op("in", ffs2b_in).

%-----------------------------------------------------------------------------%

is_string_string_to_string_op("++", ss2s_append).

is_string_string_to_bool_op("=",    ss2b_eq).
is_string_string_to_bool_op("==",   ss2b_ee).
is_string_string_to_bool_op("!=",   ss2b_ne).
is_string_string_to_bool_op("<",    ss2b_lt).
is_string_string_to_bool_op("<=",   ss2b_le).
is_string_string_to_bool_op(">",    ss2b_gt).
is_string_string_to_bool_op(">=",   ss2b_ge).

is_string_array_to_string_op("concat", sa2s_concat).

is_string_string_array_to_string_op("join", ssa2s_join).

is_general_to_string_op("show",     x2s_show).

is_int_int_to_string_op("show_int", ii2s_show_int).

is_int_int_float_to_string_op("show_float", iif2s_show_float).

%-----------------------------------------------------------------------------%

is_set_to_int_op("card",            xs2i_card).

is_int_set_to_int_op("min",         is2i_min).
is_int_set_to_int_op("max",         is2i_max).

is_int_array_to_int_op("sum",       ia2i_sum).
is_int_array_to_int_op("product",   ia2i_product).
is_int_array_to_int_op("length",    ia2i_length).
is_int_array_to_int_op("min",       ia2i_min).
is_int_array_to_int_op("max",       ia2i_max).
is_int_array_to_int_op("lb_array",  ia2i_lb_array).
is_int_array_to_int_op("ub_array",  ia2i_ub_array).

is_int_set_to_int_set_op("ub",      is2is_ub).

is_set_set_to_set_op("diff",        xsxs2xs_diff).
is_set_set_to_set_op("intersect",   xsxs2xs_intersect).
is_set_set_to_set_op("union",       xsxs2xs_union).

is_set_set_to_bool_op("=",          xsxs2b_eq).
is_set_set_to_bool_op("==",         xsxs2b_ee).
is_set_set_to_bool_op("!=",         xsxs2b_ne).
is_set_set_to_bool_op("<",          xsxs2b_lt).
is_set_set_to_bool_op("<=",         xsxs2b_le).
is_set_set_to_bool_op(">",          xsxs2b_gt).
is_set_set_to_bool_op(">=",         xsxs2b_ge).
is_set_set_to_bool_op("subset",     xsxs2b_subset).
is_set_set_to_bool_op("superset",   xsxs2b_superset).

is_set_to_array_op("set2array",     xs2xa_set2array).

is_array_array_to_array_op("++",    xaxa2xa_append).

%-----------------------------------------------------------------------------%

is_builtin_op(Name, Arity, IsLogicalOp, NeedToReifyArgs, Type) :-
    ( if
        builtin_op_table(Name, Arity, IsLogicalOpPrime, NeedToReifyArgsPrime,
            TypePrime)
    then
        IsLogicalOp = IsLogicalOpPrime,
        NeedToReifyArgs = NeedToReifyArgsPrime,
        Type = TypePrime
    else if
        Name = "==",
        builtin_op_table("=", Arity, IsLogicalOpPrime, NeedToReifyArgsPrime,
            TypePrime)
    then
        IsLogicalOp = IsLogicalOpPrime,
        NeedToReifyArgs = NeedToReifyArgsPrime,
        Type = TypePrime
    else
        fail
    ).

builtin_op_table("dom",             1, no, no, bo_dom).
builtin_op_table("lb",              1, no, no, bo_lb).
builtin_op_table("ub",              1, no, no, bo_ub).
builtin_op_table("dom_array",       1, no, no, bo_dom_array).
builtin_op_table("lb_array",        1, no, no, bo_lb_array).
builtin_op_table("ub_array",        1, no, no, bo_ub_array).
builtin_op_table("dom_size",        1, no, no, bo_dom_size).

builtin_op_table("exists",          1, yes, yes, bo_exists).
builtin_op_table("forall",          1, yes, no, bo_forall).
builtin_op_table("iffall",          1, yes, no, bo_iffall).
builtin_op_table("xorall",          1, yes, no, bo_xorall).
builtin_op_table("not",             1, yes, yes, bo_not).

builtin_op_table("abort",           1, no,  no,  bo_abort).
builtin_op_table("assert",          1, yes, yes, bo_assert).

builtin_op_table("=",               2, yes, yes, bo_eq).
builtin_op_table("!=",              2, yes, yes, bo_ne).
builtin_op_table("<",               2, yes, yes, bo_lt).
builtin_op_table("<=",              2, yes, yes, bo_le).
builtin_op_table(">",               2, yes, yes, bo_gt).
builtin_op_table(">=",              2, yes, yes, bo_ge).

builtin_op_table("bool2int",        1, yes, yes, bo_bool2int).
builtin_op_table("int2float",       1, no, no, bo_int2float).

builtin_op_table("/\\",             2, yes, no, bo_and).
builtin_op_table("\\/",             2, yes, yes, bo_or).
builtin_op_table("xor",             2, yes, yes, bo_xor).
builtin_op_table("->",              2, yes, yes, bo_imp2r).
builtin_op_table("<-",              2, yes, yes, bo_imp2l).
builtin_op_table("<->",             2, yes, yes, bo_biimp).

builtin_op_table("-",               1, no, no, bo_negate).
builtin_op_table("abs",             1, no, no, bo_abs).

builtin_op_table("+",               2, no, no, bo_add).
builtin_op_table("-",               2, no, no, bo_sub).
builtin_op_table("*",               2, no, no, bo_mul).
builtin_op_table("/",               2, no, no, bo_fdiv).
builtin_op_table("div",             2, no, no, bo_idiv).
builtin_op_table("mod",             2, no, no, bo_mod).
builtin_op_table("min",             2, no, no, bo_min).
builtin_op_table("max",             2, no, no, bo_max).

builtin_op_table("min",             1, no, no, bo_array_min).
builtin_op_table("max",             1, no, no, bo_array_max).
builtin_op_table("sum",             1, no, no, bo_array_sum).
builtin_op_table("product",         1, no, no, bo_array_product).
builtin_op_table("length",          1, no, no, bo_array_length).

builtin_op_table("ceil",            1, no, no, bo_ceil).
builtin_op_table("floor",           1, no, no, bo_floor).
builtin_op_table("round",           1, no, no, bo_round).

builtin_op_table("exp",             1, no, no, bo_exp).
builtin_op_table("ln",              1, no, no, bo_ln).
builtin_op_table("log10",           1, no, no, bo_log10).
builtin_op_table("log2",            1, no, no, bo_log2).
builtin_op_table("log",             2, no, no, bo_log).
builtin_op_table("pow",             2, no, no, bo_pow).
builtin_op_table("sqrt",            1, no, no, bo_sqrt).

builtin_op_table("sin",             1, no, no, bo_sin).
builtin_op_table("cos",             1, no, no, bo_cos).
builtin_op_table("tan",             1, no, no, bo_tan).
builtin_op_table("sinh",            1, no, no, bo_sinh).
builtin_op_table("cosh",            1, no, no, bo_cosh).
builtin_op_table("tanh",            1, no, no, bo_tanh).
builtin_op_table("asin",            1, no, no, bo_asin).
builtin_op_table("acos",            1, no, no, bo_acos).
builtin_op_table("atan",            1, no, no, bo_atan).

builtin_op_table("card",            1, no, no, bo_card).
builtin_op_table("set2array",       1, no, no, bo_set2array).
builtin_op_table("..",              2, no, no, bo_range).
builtin_op_table("in",              2, no, no, bo_in).
builtin_op_table("subset",          2, no, no, bo_subset).
builtin_op_table("superset",        2, no, no, bo_superset).
builtin_op_table("diff",            2, no, no, bo_diff).
builtin_op_table("intersect",       2, no, no, bo_intersect).
builtin_op_table("union",           2, no, no, bo_union).

builtin_op_table("array_intersect", 1, no, no, bo_array_intersect).
builtin_op_table("array_union",     1, no, no, bo_array_union).

builtin_op_table("++",              2, no, no, bo_append).
builtin_op_table("array1d",         2, no, no, bo_array1d).
builtin_op_table("array2d",         3, no, no, bo_array2d).
builtin_op_table("array3d",         4, no, no, bo_array3d).
builtin_op_table("array4d",         5, no, no, bo_array4d).
builtin_op_table("array5d",         6, no, no, bo_array5d).
builtin_op_table("array6d",         7, no, no, bo_array6d).
builtin_op_table("index_set",       1, no, no, bo_index_set).
builtin_op_table("index_set_1of2",  1, no, no, bo_index_set_1of2).
builtin_op_table("index_set_2of2",  1, no, no, bo_index_set_2of2).
builtin_op_table("index_set_1of3",  1, no, no, bo_index_set_1of3).
builtin_op_table("index_set_2of3",  1, no, no, bo_index_set_2of3).
builtin_op_table("index_set_3of3",  1, no, no, bo_index_set_3of3).
builtin_op_table("index_set_1of4",  1, no, no, bo_index_set_1of4).
builtin_op_table("index_set_2of4",  1, no, no, bo_index_set_2of4).
builtin_op_table("index_set_3of4",  1, no, no, bo_index_set_3of4).
builtin_op_table("index_set_4of4",  1, no, no, bo_index_set_4of4).

builtin_op_table("show",            1, no, no, bo_show).
builtin_op_table("show_int",        2, no, no, bo_show_int).
builtin_op_table("show_float",      3, no, no, bo_show_float).
builtin_op_table("fix",             1, no, no, bo_fix).
builtin_op_table("concat",          1, no, no, bo_concat).
builtin_op_table("join",            2, no, no, bo_join). 

%-----------------------------------------------------------------------------%
:- end_module mzn_ops.
%-----------------------------------------------------------------------------%
