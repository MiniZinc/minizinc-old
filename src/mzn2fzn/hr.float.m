%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2001 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
%-----------------------------------------------------------------------------%

:- module hr.float.
:- interface.

:- import_module errors.
:- import_module hr.info.
:- import_module types.

    % Refine bounds on a float variable.
    % These do nothing in a reifying context.
    % These do nothing if the float_expr is not a float_var(var_no_index(_)).
    %
:- pred hr_refine_float_bounds(error_context::in, ilhs::in,
    float_range::in, float_expr::in, model::in, model::out) is det.

:- pred hr_refine_float_lb(error_context::in, ilhs::in,
    float::in, float_expr::in, model::in, model::out) is det.

:- pred hr_refine_float_ub(error_context::in, ilhs::in,
    float::in, float_expr::in, model::in, model::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module global_vars.

:- import_module float.

%-----------------------------------------------------------------------------%

hr_refine_float_bounds(Context, ILHS, RefineBounds, A, !Model) :-
    ( if
        A = float_var(var_no_index(VarId)),
        ILHS = ilhs_true
    then
        (
            RefineBounds = float_range_unbounded
        ;
            RefineBounds = float_range_lb_ub(RefineLB, RefineUB),
            GlobalVarMap0 = !.Model ^ model_globals,
            get_float_lb_ub(GlobalVarMap0, VarId, OldLB, OldUB),
            LB = float.max(RefineLB, OldLB),
            UB = float.min(RefineUB, OldUB),
            set_float_lb_ub(VarId, LB, UB, GlobalVarMap0, GlobalVarMap),
            !Model ^ model_globals := GlobalVarMap
        ;
            RefineBounds = float_range_set(_),
            minizinc_user_error(Context,
                "set membership is not supported for float variables.\n")
        )
    else
        true
    ).

%-----------------------------------------------------------------------------%

hr_refine_float_lb(_Context, ILHS, RefineLB, A, !Model) :-
    ( if
        A = float_var(var_no_index(VarId)),
        ILHS = ilhs_true
    then
        GlobalVarMap0 = !.Model ^ model_globals,
        OldLB = get_float_lb(GlobalVarMap0, VarId),
        LB = float.max(RefineLB, OldLB),
        set_float_lb(VarId, LB, GlobalVarMap0, GlobalVarMap),
        !Model ^ model_globals := GlobalVarMap
    else
        true
    ).

%-----------------------------------------------------------------------------%

hr_refine_float_ub(_Context, ILHS, RefineUB, A, !Model) :-
    ( if
        A = float_var(var_no_index(VarId)),
        ILHS = ilhs_true
    then
        GlobalVarMap0 = !.Model ^ model_globals,
        OldUB = get_float_ub(GlobalVarMap0, VarId),
        UB = float.min(RefineUB, OldUB),
        set_float_ub(VarId, UB, GlobalVarMap0, GlobalVarMap),
        !Model ^ model_globals := GlobalVarMap
    else
        true
    ).

%-----------------------------------------------------------------------------%
:- end_module hr.float.
%-----------------------------------------------------------------------------%
