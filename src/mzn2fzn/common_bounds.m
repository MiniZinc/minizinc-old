%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
% This module provides operations to compute bounds on nontrivial expressions.
% The trivial expressions are handled in bounds.m.
%
%-----------------------------------------------------------------------------%

:- module common_bounds.
:- interface.

:- import_module errors.
:- import_module types.

:- import_module bool.
:- import_module set.
:- import_module unit.

%-----------------------------------------------------------------------------%

    % Calculate the lower and upper bounds on a float_expr.
    %
:- pred get_float_expr_lb_ub(global_var_map::in,
    float_expr::in, float::out, float::out) is det.

    % Compute the lower and upper bounds on an int_expr.
    %
:- pred get_int_expr_lb_ub(error_context::in, global_var_map::in,
    int_expr::in, int::out, int::out) is det.

    % Compute the lower and upper bounds on an int_set_expr (if the set
    % is empty then the lower bound will be greater than the upper bound).
    %
:- pred get_int_set_expr_lb_ub(global_var_map::in,
    int_set_expr::in, int::out, int::out) is det.

    % Retrieve the set upper bound of an int set variable.
    % JJJ FIXME - Output needs to be an intset.
    %
:- pred get_int_set_expr_set_bound(global_var_map::in, int_set_expr::in,
    set(int)::out) is det.

:- func int_set_expr_bound_is_contiguous(global_var_map, int_set_expr) = bool.

%-----------------------------------------------------------------------------%

    % Calculate the lower and upper bounds on array expressions.

:- func float_array_bounds(error_context, global_var_map, float_array_expr)
    = float_range.

:- func int_array_bounds(error_context, global_var_map, int_array_expr)
    = int_range.

:- func int_set_array_bounds(error_context, global_var_map, int_set_array_expr)
    = int_range.

:- func float_set_array_bounds(error_context, global_var_map,
    float_set_array_expr) = float_range.

    % Functions to return dummy bounds on arrays on whose elements the notion
    % of bounds does not make sense. This is to allow these arrays to be
    % handled by the same higher order predicates as the arrays on whose
    % elements the notion of bounds DOES make sense.

:- func bool_array_bounds(error_context, global_var_map, bool_array_expr)
    = unit.

:- func string_array_bounds(error_context, global_var_map, string_array_expr)
    = unit.

:- func ann_array_bounds(error_context, global_var_map, ann_array_expr)
    = unit.

:- func bool_set_array_bounds(error_context, global_var_map,
    bool_set_array_expr) = unit.

%-----------------------------------------------------------------------------%

    % Turn a set into an index range. Check it isn't empty or discontiguous.
    %
:- func set_to_index_range(error_context, global_var_map, set(int))
    = index_range.

:- func int_set_to_index_range(error_context, global_var_map, int_set_expr)
    = index_range.

%-----------------------------------------------------------------------------%

:- implementation.

:- import_module bounds.
:- import_module global_vars.

:- import_module intset.

:- import_module array.
:- import_module float.
:- import_module int.
:- import_module list.

%-----------------------------------------------------------------------------%

get_float_expr_lb_ub(GlobalVarMap, A, LB, UB) :-
    (
        A = float_const(FA),
        LB = FA,
        UB = FA
    ;
        A = float_var(var_no_index(VarId)),
        get_float_lb_ub(GlobalVarMap, VarId, LB, UB)
    ;
        A = float_var(var_index(VarId, _)),
        get_float_lb_ub(GlobalVarMap, VarId, LB, UB)
    ;
        A = B + C,
        get_float_expr_lb_ub(GlobalVarMap, B, LBB, UBB),
        get_float_expr_lb_ub(GlobalVarMap, C, LBC, UBC),
        float_plus_bounds(LBB, UBB, LBC, UBC, LB, UB)
    ;
        A = K * B,
        get_float_expr_lb_ub(GlobalVarMap, B, LBB, UBB),
        float_times_bounds(K, K, LBB, UBB, LB, UB)
    ).

%-----------------------------------------------------------------------------%

get_int_expr_lb_ub(Context, GlobalVarMap, A, LB, UB) :-
    (
        A = int_const(IA),
        LB = IA,
        UB = IA
    ;
        A = int_var(var_no_index(VarId)),
        get_int_lb_ub(GlobalVarMap, VarId, LB, UB)
    ;
        A = int_var(var_index(VarId, _)),
        get_int_lb_ub(GlobalVarMap, VarId, LB, UB)
    ;
        A = B + C,
        get_int_expr_lb_ub(Context, GlobalVarMap, B, LBB, UBB),
        get_int_expr_lb_ub(Context, GlobalVarMap, C, LBC, UBC),
        int_plus_bounds(Context, LBB, UBB, LBC, UBC, LB, UB)
    ;
        A = K * B,
        get_int_expr_lb_ub(Context, GlobalVarMap, B, LBB, UBB),
        int_times_bounds(Context, K, K, LBB, UBB, LB, UB)
    ).

%-----------------------------------------------------------------------------%

get_int_set_expr_lb_ub(GlobalVarMap, IntSetExpr, LB, UB) :-
    (
        IntSetExpr = set_items(Set),
        ( if
            Xs = set.to_sorted_list(Set),
            Xs = [LB0 | _],
            list.last(Xs, UB0)
        then
            LB = LB0,
            UB = UB0
        else
            LB = 1,
            UB = 0
        )
    ;
        IntSetExpr = set_var(MZVar),
        ( MZVar = var_no_index(VarId)
        ; MZVar = var_index(VarId, _)
        ),
        get_int_lb_ub(GlobalVarMap, VarId, LB, UB)
    ).

get_int_set_expr_set_bound(GlobalVarMap, IntSetExpr, SetUB) :-
    (
        IntSetExpr = set_items(Set),
        SetUB = Set
    ;
        IntSetExpr = set_var(MZVar),
        VarId = mzn_var_id(MZVar),
        Range = get_int_set_bounds(GlobalVarMap, VarId),
        (
            Range = int_range_set(SetUB0),
            % JJJ - INTSET
            SetUB = set.from_sorted_list(intset.to_sorted_list(SetUB0))
        ;
            Range = int_range_lb_ub(LB, UB),
            ( if
                LB \= int_minus_infinity,
                UB \= int_plus_infinity
            then
                SetUB = set.from_sorted_list(LB..UB)
            else
                minizinc_internal_error([], $pred, "set var is unbounded.\n")
            )
        ;
            Range = int_range_unbounded,
            minizinc_internal_error([], $pred, "set var is unbounded.\n")
        )
    ).

int_set_expr_bound_is_contiguous(GlobalVarMap, IntSetExpr) = IsContiguous :-
    (
        IntSetExpr = set_items(Set),
        get_int_set_expr_lb_ub(GlobalVarMap, IntSetExpr, LB, UB),
        ( if set.count(Set) = 1 + UB - LB then
            IsContiguous = yes
        else
            IsContiguous = no
        )
    ;
        IntSetExpr = set_var(MZVar),
        VarId = mzn_var_id(MZVar),
        IsContiguous = var_int_set_bounds_is_contiguous(GlobalVarMap, VarId)
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

float_array_bounds(Context, GlobalVarMap, ArrayExpr) = Range :-
    (
        ArrayExpr = array_items(_, As),
        ( if array.size(As) = 0 then
            LB = 0.0,
            UB = 0.0
        else
            float_array_items_bounds(Context, GlobalVarMap, As,
                float_plus_infinity, LB, float_minus_infinity, UB)
        )
    ;
        ArrayExpr = array_var(_, VarId),
        get_float_lb_ub(GlobalVarMap, VarId, LB, UB)
    ),
    Range = float_range_lb_ub(LB, UB).

:- pred float_array_items_bounds(error_context::in, global_var_map::in,
    array(float_expr)::in, float::in, float::out, float::in, float::out)
    is det.

float_array_items_bounds(Context, GlobalVarMap, As, !LB, !UB) :-
    array.foldl2(update_float_lb_ub(Context, GlobalVarMap), As, !LB, !UB).

:- pred update_float_lb_ub(error_context::in, global_var_map::in,
    float_expr::in, float::in, float::out, float::in, float::out) is det.

update_float_lb_ub(_Context, GlobalVarMap, A, !LB, !UB) :-
    get_float_expr_lb_ub(GlobalVarMap, A, LBA, UBA),
    !:LB = float.min(LBA, !.LB),
    !:UB = float.max(UBA, !.UB).

%-----------------------------------------------------------------------------%

int_array_bounds(Context, GlobalVarMap, ArrayExpr) = Range :-
    (
        ArrayExpr = array_items(_, As),
        ( if array.size(As) = 0 then
            LB = 0,
            UB = 0
        else
            int_array_items_bounds(Context, GlobalVarMap, As,
                int_plus_infinity, LB, int_minus_infinity, UB)
        )
    ;
        ArrayExpr = array_var(_, VarId),
        get_int_lb_ub(GlobalVarMap, VarId, LB, UB)
    ),
    Range = int_range_lb_ub(LB, UB).

:- pred int_array_items_bounds(error_context::in, global_var_map::in,
    array(int_expr)::in, int::in, int::out, int::in, int::out) is det.

int_array_items_bounds(Context, GlobalVarMap, As, !LB, !UB) :-
    array.foldl2(update_int_lb_ub(Context, GlobalVarMap), As, !LB, !UB).

:- pred update_int_lb_ub(error_context::in, global_var_map::in,
    int_expr::in, int::in, int::out, int::in, int::out) is det.

update_int_lb_ub(Context, GlobalVarMap, A, !LB, !UB) :-
    get_int_expr_lb_ub(Context, GlobalVarMap, A, LBA, UBA),
    !:LB = int.min(LBA, !.LB),
    !:UB = int.max(UBA, !.UB).

%-----------------------------------------------------------------------------%

int_set_array_bounds(Context, GlobalVarMap, ArrayExpr) = Range :-
    (
        ArrayExpr = array_items(_, As),
        int_set_array_items_min_max(Context, GlobalVarMap, As,
            int_plus_infinity, LB, int_minus_infinity, UB),
        Range = int_range_lb_ub(LB, UB)
    ;
        ArrayExpr = array_var(_, VarId),
        Range = get_int_set_bounds(GlobalVarMap, VarId)
    ).

:- pred int_set_array_items_min_max(error_context::in, global_var_map::in,
    array(int_set_expr)::in, int::in, int::out, int::in, int::out) is det.

int_set_array_items_min_max(Context, GlobalVarMap, As, !Min, !Max) :-
    array.foldl2(update_int_set_min_max(Context, GlobalVarMap), As,
        !Min, !Max).

:- pred update_int_set_min_max(error_context::in, global_var_map::in,
    int_set_expr::in, int::in, int::out, int::in, int::out) is det.

update_int_set_min_max(_Context, GlobalVarMap, A, !Min, !Max) :-
    get_int_set_expr_lb_ub(GlobalVarMap, A, MinA, MaxA),
    !:Min = int.min(MinA, !.Min),
    !:Max = int.max(MaxA, !.Max).

%-----------------------------------------------------------------------------%

float_set_array_bounds(_, _, _) = float_range_unbounded.
    % Could we do better than this?

%-----------------------------------------------------------------------------%

bool_array_bounds(_, _, _) = unit.
string_array_bounds(_, _, _) = unit.
ann_array_bounds(_, _, _) = unit.
bool_set_array_bounds(_, _, _) = unit.

%-----------------------------------------------------------------------------%

set_to_index_range(Context, GlobalVarMap, Set) = IndexRange :-
    get_int_set_expr_lb_ub(GlobalVarMap, set_items(Set), LB, UB),
    ( if set.count(Set) = 1 + UB - LB then
        IndexRange = index_range(LB, UB)
    else if LB > UB then
        minizinc_user_error(Context, "Index range is empty.\n")
    else
        minizinc_user_error(Context, "Index ranges must be contiguous.\n")
    ).

int_set_to_index_range(Context, GlobalVarMap, IntSetExpr) = Range :-
    (
        IntSetExpr = set_var(_),
        minizinc_user_error(Context,
            "Array index range does not have a value.\n")
    ;
        IntSetExpr = set_items(Set),
        Range = set_to_index_range(Context, GlobalVarMap, Set)
    ).

%-----------------------------------------------------------------------------%
:- end_module common_bounds.
%-----------------------------------------------------------------------------%
