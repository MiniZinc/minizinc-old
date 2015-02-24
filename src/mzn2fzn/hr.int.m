%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
%-----------------------------------------------------------------------------%

:- module hr.int.
:- interface.

:- import_module errors.
:- import_module global_vars.
:- import_module hr.info.
:- import_module mzn_ops.
:- import_module types.

:- import_module list.

%-----------------------------------------------------------------------------%
%
% These predicates assume their int_expr arguments have been simplified
% where possible.
%
% XXX The semidet predicates below should be det.
%

:- pred halfreify_int_to_int(error_context::in, mzn_anns::in, ilhs::in,
    int_to_int_op::in, int_expr::in,
    int_expr::out, mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is semidet.

:- pred halfreify_int_int_to_int(error_context::in, mzn_anns::in, ilhs::in,
    int_int_to_int_op::in, int_expr::in, int_expr::in,
    int_expr::out, mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is semidet.

:- pred halfreify_int_int_to_bool_or_inconsistent(error_context::in,
    string::in, mzn_anns::in, ilhs::in,
    int_int_to_bool_op::in, int_expr::in, int_expr::in,
    bool_const_or_var::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

:- pred halfreify_int_int_to_bool(error_context::in, mzn_anns::in, ilhs::in,
    int_int_to_bool_op::in, int_expr::in, int_expr::in,
    bool_const_or_var::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is semidet.

%-----------------------------------------------------------------------------%

    % Convert an int_expr into a "simple" (i.e., FlatZinc) form (namely either
    % a constant or a variable). This may require introducing a new temporary
    % variable if the int_expr is a linear sum.
    %
:- pred hr_simplify_int(error_context::in, mzn_anns::in, ilhs::in,
    int_expr::in, int_expr::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

%-----------------------------------------------------------------------------%

    % Refine bounds on an int variable.
    % These do nothing in a reifying context, or if the int_expr has a shape
    % other than int_var(var_no_index(VarId)).
    %
:- pred hr_refine_int_bounds(error_context::in, ilhs::in,
    int_range::in, int_expr::in, list(mzn_constraint_to_add)::out,
    model::in, model::out) is det.
:- pred hr_do_refine_int_bounds(error_context::in,
    int_range::in, var_id::in, list(mzn_constraint_to_add)::out,
    model::in, model::out) is det.

:- pred hr_refine_int_lb(ilhs::in, int::in, int_expr::in,
    model::in, model::out) is det.
:- pred hr_do_refine_int_lb(int::in, var_id::in, model::in, model::out) is det.

:- pred hr_refine_int_ub(ilhs::in, int::in, int_expr::in,
    model::in, model::out) is det.
:- pred hr_do_refine_int_ub(int::in, var_id::in, model::in, model::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module bounds.
:- import_module common_array.
:- import_module common_bounds.
:- import_module common_expr.
:- import_module global_vars.

:- import_module intset.

:- import_module bool.
:- import_module int.
:- import_module maybe.
:- import_module set.
:- import_module unit.

%-----------------------------------------------------------------------------%

halfreify_int_to_int(Context, Anns, ILHS, Op, A, Z, AllConstraints, KnownFalse,
        !Info, !Model) :-
    ( if
        A = int_const(IntA)
    then
        halfreify_par_int_to_int(Op, IntA, IntZ),
        Z = int_const(IntZ),
        mzn_constraint_set_empty(AllConstraints),
        KnownFalse = not_known_to_be_false
    else
        halfreify_var_int_to_int(Context, Anns, ILHS, Op, A, Z,
            AllConstraints, KnownFalse, !Info, !Model)
    ).

:- pred halfreify_par_int_to_int(int_to_int_op::in, int::in, int::out) is det.

halfreify_par_int_to_int(i2i_add,      IntA, IntA).
halfreify_par_int_to_int(i2i_sub,      IntA, -IntA).
halfreify_par_int_to_int(i2i_abs,      IntA, int.abs(IntA)).
halfreify_par_int_to_int(i2i_lb,       IntA, IntA).
halfreify_par_int_to_int(i2i_ub,       IntA, IntA).
halfreify_par_int_to_int(i2i_dom_size, _,    1).
halfreify_par_int_to_int(i2i_fix,      IntA, IntA).

:- pred halfreify_var_int_to_int(error_context::in, mzn_anns::in, ilhs::in,
    int_to_int_op::in, int_expr::in,
    int_expr::out, mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is semidet.

halfreify_var_int_to_int(Context, Anns, ILHS, Op, A, Z,
        AllConstraints, KnownFalse, !Info, !Model) :-
    % XXX OutsideAnns is ASSUMED to be no_anns
    OutsideAnns = no_anns,
    (
        Op = i2i_add,
        Z = A,
        mzn_constraint_set_empty(AllConstraints),
        KnownFalse = not_known_to_be_false
    ;
        Op = i2i_sub,
        Z = -1 * A,
        mzn_constraint_set_empty(AllConstraints),
        KnownFalse = not_known_to_be_false
    ;
        Op = i2i_abs,
        get_int_expr_lb_ub(Context, !.Model ^ model_globals, A, LBA, UBA),
        ( if LBA < 0, 0 < UBA then
            LB = 0,
            ( if ( LBA = int_minus_infinity ; UBA = int_plus_infinity ) then
                UB = int_plus_infinity
            else
                UB = max(-LBA, UBA)
            ),
            Bounds = int_range_lb_ub(LB, UB),
            hr_simplify_int(Context, OutsideAnns, ILHS, A, SimpleA,
                SimplifyConstraints, !Info, !Model),
            hr_add_tmp_int_var(Context, OutsideAnns, ILHS, Bounds,
                "int_abs", [int_to_mzn_expr(SimpleA)], Anns, _VarIdZ, Z,
                ResultConstraints, !Info, !Model),
            mzn_constraint_set_union(SimplifyConstraints, ResultConstraints,
                AllConstraints),
            KnownFalse = not_known_to_be_false
        else if UBA =< 0 then
            halfreify_var_int_to_int(Context, Anns, ILHS, i2i_sub, A, Z,
                AllConstraints, KnownFalse, !Info, !Model)
        else
            Z = A,
            mzn_constraint_set_empty(AllConstraints),
            KnownFalse = not_known_to_be_false
        )
    ;
        Op = i2i_lb,
        get_int_expr_lb_ub(Context, !.Model ^ model_globals, A, LBA, _UBA),
        ( if LBA = int_minus_infinity then
            minizinc_user_error(Context, "Cannot infer lower bound.\n")
        else
            Z = int_const(LBA),
            mzn_constraint_set_empty(AllConstraints),
            KnownFalse = not_known_to_be_false
        )
    ;
        Op = i2i_ub,
        get_int_expr_lb_ub(Context, !.Model ^ model_globals, A, _LBA, UBA),
        ( if UBA = int_plus_infinity then
            minizinc_user_error(Context, "Cannot infer upper bound.\n")
        else
            Z = int_const(UBA),
            mzn_constraint_set_empty(AllConstraints),
            KnownFalse = not_known_to_be_false
        )
    ;
        Op = i2i_dom_size,
        get_int_expr_lb_ub(Context, !.Model ^ model_globals, A, LBA, UBA),
        ( if ( UBA = int_plus_infinity ; LBA = int_minus_infinity ) then
            minizinc_user_error(Context, "Cannot infer domain size.\n")
        else
            DomSize0 = UBA - LBA + 1,
            DomSize = (if DomSize0 < 0 then 0 else DomSize0 ),
            Z = int_const(DomSize),
            mzn_constraint_set_empty(AllConstraints),
            KnownFalse = not_known_to_be_false
        )
    ).

%-----------------------------------------------------------------------------%

halfreify_int_int_to_int(Context, Anns, ILHS, Op, A, B, Z,
        AllConstraints, KnownFalse, !Info, !Model) :-
    ( if
        A = int_const(IntA), B = int_const(IntB),
        halfreify_par_int_par_int_to_int(Context, Op, IntA, IntB, IntZ)
    then
        Z = int_const(IntZ),
        mzn_constraint_set_empty(AllConstraints),
        KnownFalse = not_known_to_be_false
    else if
        A = int_const(IntA),
        halfreify_par_int_var_int_to_int(Op, IntA, B, Z0)
    then
        Z = Z0,
        mzn_constraint_set_empty(AllConstraints),
        KnownFalse = not_known_to_be_false
    else if
        B = int_const(IntB),
        halfreify_var_int_par_int_to_int(Op, A, IntB, Z0)
    then
        Z = Z0,
        mzn_constraint_set_empty(AllConstraints),
        KnownFalse = not_known_to_be_false
    else
        halfreify_var_int_var_int_to_int(Context, Anns, ILHS, Op, A, B, Z,
            AllConstraints, KnownFalse, !Info, !Model)
    ).

:- pred halfreify_par_int_par_int_to_int(error_context::in,
    int_int_to_int_op::in, int::in, int::in, int::out) is semidet.

halfreify_par_int_par_int_to_int(Context, Op, IntA, IntB, IntZ) :-
    (
        ( Op = ii2i_add, IntZ = IntA + IntB
        ; Op = ii2i_sub, IntZ = IntA - IntB
        ; Op = ii2i_mul, IntZ = IntA * IntB
        ; Op = ii2i_min, IntZ = int.min(IntA, IntB)
        ; Op = ii2i_max, IntZ = int.max(IntA, IntB)
        )
    ;
        Op = ii2i_div,
        ( if IntB = 0 then
            minizinc_user_error(Context, "Division by zero.\n")
          else
            IntZ = IntA / IntB
        )
    ;
        Op = ii2i_pow,
        ( if IntB < 0 then
            minizinc_user_error(Context,
                "Cannot raise integer to a negative power.\n")
        else
            IntZ = int.pow(IntA, IntB)
        )
    ).

:- pred halfreify_par_int_var_int_to_int(int_int_to_int_op::in,
    int::in, int_expr::in, int_expr::out) is semidet.

halfreify_par_int_var_int_to_int(Op, IntA, B, Z) :-
    % XXX most Ops are missing
    (
        Op = ii2i_mul,
        ( if IntA = 0 then
            Z = int_const(0)
        else if IntA = 1 then
            Z = B
        else if B = IntB * C then
            Z = (IntA * IntB) * C
        else
            Z = IntA * B
        )
    ).

:- pred halfreify_var_int_par_int_to_int(int_int_to_int_op::in,
    int_expr::in, int::in, int_expr::out) is semidet.

halfreify_var_int_par_int_to_int(Op, A, IntB, Z) :-
    % XXX most Ops are missing
    (
        Op = ii2i_mul,
        halfreify_par_int_var_int_to_int(Op, IntB, A, Z)
    ).

:- pred halfreify_var_int_var_int_to_int(error_context::in, mzn_anns::in,
    ilhs::in, int_int_to_int_op::in, int_expr::in, int_expr::in,
    int_expr::out, mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is semidet.

halfreify_var_int_var_int_to_int(Context, Anns, ILHS, Op, A, B, Z,
        AllConstraints, KnownFalse, !Info, !Model) :-
    % XXX OutsideAnns is ASSUMED to be no_anns
    OutsideAnns = no_anns,
    (
        Op = ii2i_add,
        Z = A + B,
        mzn_constraint_set_empty(AllConstraints),
        KnownFalse = not_known_to_be_false
    ;
        Op = ii2i_sub,
        Z = A + -1 * B,
        mzn_constraint_set_empty(AllConstraints),
        KnownFalse = not_known_to_be_false
    ;
        ( Op = ii2i_mul
        ; Op = ii2i_min
        ; Op = ii2i_max
        ),
        hr_simplify_int(Context, OutsideAnns, ILHS, A, SimpleA, ConstraintsA,
            !Info, !Model),
        hr_simplify_int(Context, OutsideAnns, ILHS, B, SimpleB, ConstraintsB,
            !Info, !Model),
        GlobalVarMap = !.Model ^ model_globals,
        get_int_expr_lb_ub(Context, GlobalVarMap, SimpleA, LBA, UBA),
        get_int_expr_lb_ub(Context, GlobalVarMap, SimpleB, LBB, UBB),
        (
            Op = ii2i_mul,
            int_times_bounds(Context, LBA, UBA, LBB, UBB, LB, UB),
            Bounds = int_range_lb_ub(LB, UB),
            hr_add_tmp_int_var(Context, OutsideAnns, ILHS, Bounds, "int_times",
                [int_to_mzn_expr(SimpleA), int_to_mzn_expr(SimpleB)],
                Anns, _VarIdZ, Z, ConstraintsOp, !Info, !Model)
        ;
            Op = ii2i_min,
            int_min_bounds(LBA, UBA, LBB, UBB, LB, UB),
            Bounds = int_range_lb_ub(LB, UB),
            hr_add_tmp_int_var(Context, OutsideAnns, ILHS, Bounds, "int_min",
                [int_to_mzn_expr(SimpleA), int_to_mzn_expr(SimpleB)],
                Anns, _VarIdZ, Z, ConstraintsOp, !Info, !Model)
        ;
            Op = ii2i_max,
            int_max_bounds(LBA, UBA, LBB, UBB, LB, UB),
            Bounds = int_range_lb_ub(LB, UB),
            hr_add_tmp_int_var(Context, OutsideAnns, ILHS, Bounds, "int_max",
                [int_to_mzn_expr(SimpleA), int_to_mzn_expr(SimpleB)],
                Anns, _VarIdZ, Z, ConstraintsOp, !Info, !Model)
        ),
        mzn_constraint_set_union_list([ConstraintsA, ConstraintsB,
            ConstraintsOp], AllConstraints),
        KnownFalse = not_known_to_be_false
    ;
        Op = ii2i_div,
        hr_simplify_int(Context, OutsideAnns, ILHS, A, SimpleA, ConstraintsA,
            !Info, !Model),
        hr_simplify_int(Context, OutsideAnns, ILHS, B, SimpleB, ConstraintsB,
            !Info, !Model),
        mzn_constraint_set_union(ConstraintsA, ConstraintsB, ConstraintsAB),
        (
            ILHS = ilhs_true,
            ( if SimpleB = int_const(0) then
                minizinc_user_error(Context, "Division by zero.\n")
            else if SimpleB = int_const(1) then
                Z = SimpleA,
                AllConstraints = ConstraintsAB
            else if SimpleA = int_const(IntA), SimpleB = int_const(IntB) then
                Z = int_const(IntA / IntB),
                AllConstraints = ConstraintsAB
            else if SimpleB = int_const(-1) then
                halfreify_par_int_var_int_to_int(ii2i_mul, -1, SimpleA, Z),
                AllConstraints = ConstraintsAB
            else
                GlobalVarMap = !.Model ^ model_globals,
                get_int_expr_lb_ub(Context, GlobalVarMap, SimpleA, LBA, UBA),
                get_int_expr_lb_ub(Context, GlobalVarMap, SimpleB, LBB, UBB),
                int_div_bounds(LBA, UBA, LBB, UBB, LB, UB),
                Bounds = int_range_lb_ub(LB, UB),
                hr_add_tmp_int_var(Context, OutsideAnns, ILHS, Bounds,
                    "int_div",
                    [int_to_mzn_expr(SimpleA), int_to_mzn_expr(SimpleB)],
                    Anns, _VarIdZ, Z, OpConstraints, !Info, !Model),
                mzn_constraint_set_union(ConstraintsAB, OpConstraints,
                    AllConstraints)
            ),
            KnownFalse = not_known_to_be_false
        ;
            ILHS = ilhs_var(ILHSVar),
            ( if SimpleB = int_const(0) then
                Z = int_const(0),
                mzn_constraint_set_empty(AllConstraints),
                KnownFalse = known_to_be_false
            else if SimpleB = int_const(1) then
                Z = SimpleA,
                AllConstraints = ConstraintsAB,
                KnownFalse = not_known_to_be_false
            else if SimpleA = int_const(IntA), SimpleB = int_const(IntB) then
                Z = int_const(IntA / IntB),
                AllConstraints = ConstraintsAB,
                KnownFalse = not_known_to_be_false
            else if SimpleB = int_const(-1) then
                halfreify_par_int_var_int_to_int(ii2i_mul, -1, SimpleA, Z),
                AllConstraints = ConstraintsAB,
                KnownFalse = not_known_to_be_false
            else if
                GlobalVarMap = !.Model ^ model_globals,
                get_int_expr_lb_ub(Context, GlobalVarMap, SimpleB, LBB, UBB),
                ( 0 < LBB ; UBB < 0 )
            then
                % SimpleB cannot be zero.
                get_int_expr_lb_ub(Context, GlobalVarMap, SimpleA, LBA, UBA),
                int_div_bounds(LBA, UBA, LBB, UBB, LB, UB),
                Bounds = int_range_lb_ub(LB, UB),
                hr_add_tmp_int_var(Context, OutsideAnns, ILHS, Bounds,
                    "int_div",
                    [int_to_mzn_expr(SimpleA), int_to_mzn_expr(SimpleB)],
                    Anns, _VarIdZ, Z, ConstraintsOp, !Info, !Model),
                mzn_constraint_set_union(ConstraintsAB, ConstraintsOp,
                    AllConstraints),
                KnownFalse = not_known_to_be_false
            else
                GlobalVarMap = !.Model ^ model_globals,
                get_int_expr_lb_ub(Context, GlobalVarMap, SimpleA, LBA, UBA),
                get_int_expr_lb_ub(Context, GlobalVarMap, SimpleB, LBB, UBB),
                int_div_bounds(LBA, UBA, LBB, UBB, LB, UB),
                % The reified form of Z = SimpleA / SimpleB is
                % Z = SimpleA / B1 where
                %
                % R is the reification variable for this expression,
                % SimpleB \= 0  <->  R,
                % SimpleB = B1  <->  R
                %
                BoundsB1 = int_range_lb_ub(LBB, UBB),
                hr_make_tmp_int_var(Context, OutsideAnns, ILHS, BoundsB1,
                    no_anns, _VarB1, B1, B1Constraints, !Info, !Model),
                EqP = ( pred(X::in, Y::in) is semidet :- X = Y ),
                % XXX reif kind
                % XXX _EqMaybeSolved
                make_int_int_constraint(relop_ne, EqP, cns_half,
                    SimpleB, int_const(0), NE0, NE0Args, _EqMaybeSolved),
                AllNE0Args = NE0Args ++ [bool_to_mzn_expr(R)],
                hr_add_primitive_constraint(NE0, AllNE0Args, no_anns,
                    NE0Constraint, !Model),
%               hr_add_tmp_bool_var(Context, OutsideAnns, ILHS, unit,
%                   NE0, NE0Args, no_anns, VarIdR, _ZR, RConstraints,
%                   !Info, !Model),
                R = bool_var(var_no_index(ILHSVar)),
                NeqP = ( pred(X::in, Y::in) is semidet :- X \= Y ),
                % XXX reif kind
                % XXX _NeqMaybeSolved
                make_int_int_constraint(relop_eq, NeqP, cns_half, SimpleB, B1,
                    NEB, NEBArgs, _NeqMaybeSolved),
                AllNEBArgs = NEBArgs ++ [bool_to_mzn_expr(R)],
                hr_add_primitive_constraint(NEB, AllNEBArgs, no_anns,
                    NEBConstraint, !Model),
                BoundsZ = int_range_lb_ub(LB, UB),
                hr_add_tmp_int_var(Context, OutsideAnns, ILHS, BoundsZ,
                    "int_div", [int_to_mzn_expr(SimpleA), int_to_mzn_expr(B1)],
                    Anns, _VarIdZ, Z, DivConstraints, !Info, !Model),
                mzn_constraint_set_union_mixed_list(
                    [NE0Constraint, NEBConstraint],
                    [B1Constraints, DivConstraints], AllConstraints),
                KnownFalse = not_known_to_be_false
            )
        )
    ;
        Op = ii2i_mod,
        minizinc_internal_error([], $pred, "ii2i_mod NYI")
%       hr_simplify_int(Context, OutsideAnns, ILHS, A, SimpleA, ConstraintsA,
%           !Info, !Model),
%       hr_simplify_int(Context, OutsideAnns, ILHS, B, SimpleB, ConstraintsB,
%           !Info, !Model),
%       Reifying = !.Env ^ reifying,
%       (
%           Reifying = not_reifying,
%           ( if SimpleB = int_const(0) then
%               minizinc_user_error(Context, "Modulo reduction by zero.\n")
%           else if SimpleA = int_const(0) then
%               hr_add_constraint(Context, "int_ne",
%                   [int_to_mzn_expr(SimpleB), int_to_mzn_expr(int_const(0))],
%                   no_anns, !Info, !Model),
%               Z = SimpleA
%           else if SimpleA = int_const(IntA), SimpleB = int_const(IntB) then
%               Z = int_const(IntA rem IntB)
%           else
%               get_int_expr_lb_ub(Context, !.Model ^ model_globals, SimpleA,
%                   LBA, UBA),
%               get_int_expr_lb_ub(Context, !.Model ^ model_globals, SimpleB,
%                   LBB, UBB),
%               int_mod_bounds(Context, LBA, UBA, LBB, UBB, LB, UB),
%               Bounds = int_range_lb_ub(LB, UB),
%               hr_add_tmp_int_var(Context, OutsideAnns, ILHS, Bounds, "int_mod",
%                   [int_to_mzn_expr(SimpleA), int_to_mzn_expr(SimpleB)],
%                   Anns, _VarIdZ, Z, !Info, !Model)
%           )
%       ;
%           Reifying = reifying(ReifVars),
%           ( if SimpleB = int_const(0) then
%               !Env ^ reifying := reifying([bool_const(no)]),
%               Z = int_const(0)
%           else if SimpleA = int_const(0) then
%               Z = SimpleA,
%               ( if
%                   get_int_expr_lb_ub(Context, !.Model ^ model_globals, SimpleB,
%                       LBB, UBB),
%                   ( 0 < LBB ; UBB < 0 )
%               then
%                   % SimpleB cannot be zero.
%                   true
%               else
%                   % SimpleB must not be zero.
%                   hr_add_tmp_bool_var(Context, OutsideAnns, ILHS, unit, "int_ne_reif",
%                       [int_to_mzn_expr(SimpleB),
%                           int_to_mzn_expr(int_const(0))],
%                       no_anns, _VarIdR, R, !Info, !Model),
%                   !Env ^ reifying := reifying([R | ReifVars])
%               )
%           else if
%               SimpleA = int_const(IntA), SimpleB = int_const(IntB)
%           then
%               Z = int_const(IntA rem IntB)
%           else if
%               get_int_expr_lb_ub(Context, !.Model ^ model_globals, SimpleB,
%                   LBB, UBB),
%               ( 0 < LBB ; UBB < 0 )
%           then
%               % SimpleB cannot be zero.
%               get_int_expr_lb_ub(Context, !.Model ^ model_globals, SimpleA,
%                   LBA, UBA),
%               int_mod_bounds(Context, LBA, UBA, LBB, UBB, LB, UB),
%               BoundsZ = int_range_lb_ub(LB, UB),
%               hr_add_tmp_int_var(Context, OutsideAnns, ILHS, BoundsZ,
%                   "int_mod",
%                   [int_to_mzn_expr(SimpleA), int_to_mzn_expr(SimpleB)],
%                   Anns, _VarIdZ, Z, !Info, !Model)
%           else
%               % The reified form of Z = SimpleA mod SimpleB is
%               % Z = SimpleA mod B where
%               %
%               % R is the reification variable for this expression,
%               % SimpleB \= 0  <->  R,
%               % SimpleB = B   <->  R
%               %
%               get_int_expr_lb_ub(Context, !.Model ^ model_globals, SimpleB,
%                   LBB, UBB),
%               BoundsB1 = int_range_lb_ub(LBB, UBB),
%               make_tmp_int_var(Context, BoundsB1, no_anns, _VB1, B1, !Info,
%               !Model),
%               EqP = ( pred(X::in, Y::in) is semidet :- X = Y ),
%               make_int_int_reif_constraint(relop_ne, EqP,
%                   SimpleB, int_const(0), NE0, NE0Args, _EqMaybeSolved),
%               hr_add_tmp_bool_var(Context, OutsideAnns, ILHS, unit,
%                   NE0, NE0Args, no_anns,
%                   _VarIdR, R, !Info, !Model),
%               NeqP = ( pred(X::in, Y::in) is semidet :- X \= Y ),
%               make_int_int_reif_constraint(relop_eq, NeqP, SimpleB, B1,
%                   NEB, NEBArgs, _NeqMaybeSolved),
%               hr_add_primitive_constraint(NEB,
%                   NEBArgs ++ [bool_to_mzn_expr(R)],
%                   no_anns, !Model),
%               get_int_expr_lb_ub(Context, !.Model ^ model_globals, SimpleA,
%                   LBA, UBA),
%               get_int_expr_lb_ub(Context, !.Model ^ model_globals, SimpleB,
%                   NewLBB, NewUBB),
%               int_mod_bounds(Context, LBA, UBA, NewLBB, NewUBB, LB, UB),
%               BoundsZ = int_range_lb_ub(LB, UB),
%               hr_add_tmp_int_var(Context, OutsideAnns, ILHS, BoundsZ,
%                   "int_mod",
%                   [int_to_mzn_expr(SimpleA), int_to_mzn_expr(B1)],
%                   Anns, _VarIdZ, Z, !Info, !Model),
%               !Env ^ reifying := reifying([R | ReifVars])
%           )
%       )
    ).

%-----------------------------------------------------------------------------%

halfreify_int_int_to_bool_or_inconsistent(Context, ErrMsg, OutsideAnns, ILHS,
        Op, A, B, CVZ, AllConstraints, !Info, !Model) :-
    ( if
        halfreify_int_int_to_bool(Context, OutsideAnns, ILHS, Op, A, B, CVZ0,
            AllConstraints0, !Info, !Model)
    then
        CVZ = CVZ0,
        AllConstraints = AllConstraints0
    else
        model_inconsistency_detected(Context, ErrMsg)
    ).

halfreify_int_int_to_bool(Context, OutsideAnns, ILHS, Op, A, B, CVZ,
        AllConstraints, !Info, !Model) :-
    ( if
        ( Op = ii2b_ee, RevOp = ii2b_ee
        ; Op = ii2b_ge, RevOp = ii2b_le
        ; Op = ii2b_gt, RevOp = ii2b_lt
        )
    then
        halfreify_int_int_to_bool(Context, OutsideAnns, ILHS,
            RevOp, B, A, CVZ, AllConstraints, !Info, !Model)
    else if
        A = int_const(IntA), B = int_const(IntB),
        halfreify_par_int_par_int_to_bool(Op, IntA, IntB, BoolZ)
    then
        CVZ = boolcv_const(BoolZ),
        mzn_constraint_set_empty(AllConstraints)
    else if
        A = int_const(IntA),
        halfreify_par_int_var_int_to_bool(Context, OutsideAnns, ILHS,
            Op, IntA, B, CVZ0, AllConstraints0, !Info, !Model)
    then
        CVZ = CVZ0,
        AllConstraints = AllConstraints0
    else if
        B = int_const(IntB),
        halfreify_var_int_par_int_to_bool(Context, OutsideAnns, ILHS,
            Op, A, IntB, CVZ0, AllConstraints0, !Info, !Model)
    then
        CVZ = CVZ0,
        AllConstraints = AllConstraints0
    else
        halfreify_var_int_var_int_to_bool(Context, OutsideAnns, ILHS,   
            Op, A, B, CVZ, AllConstraints, !Info, !Model)
    ).

:- pred halfreify_par_int_par_int_to_bool(int_int_to_bool_op::in,
    int::in, int::in, bool::out) is semidet.

halfreify_par_int_par_int_to_bool(Op, IntA, IntB, BoolZ) :-
    ( Op = ii2b_eq, BoolZ = ( if IntA =  IntB then yes else no )
    ; Op = ii2b_ne, BoolZ = ( if IntA \= IntB then yes else no )
    ; Op = ii2b_le, BoolZ = ( if IntA =< IntB then yes else no )
    ; Op = ii2b_lt, BoolZ = ( if IntA <  IntB then yes else no )
    ; Op = ii2b_ge, BoolZ = ( if IntA >= IntB then yes else no )
    ; Op = ii2b_gt, BoolZ = ( if IntA >  IntB then yes else no )
    ).

:- pred halfreify_par_int_var_int_to_bool(error_context::in, mzn_anns::in,
    ilhs::in, int_int_to_bool_op::in, int::in, int_expr::in,
    bool_const_or_var::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is semidet.

halfreify_par_int_var_int_to_bool(Context, OutsideAnns, ILHS, Op, IntA, B, CVZ,
        AllConstraints, !Info, !Model) :-
    (
        Op = ii2b_lt,
        IntA < int_plus_infinity,
        halfreify_par_int_var_int_to_bool(Context, OutsideAnns, ILHS,
            ii2b_le, IntA + 1, B, CVZ, AllConstraints, !Info, !Model)
    ;
        Op = ii2b_le,
        B = int_var(var_no_index(VarIdB)),
        GlobalVarMap0 = !.Model ^ model_globals,
        get_int_lb_ub(GlobalVarMap0, VarIdB, B_LB, B_UB),
        ( if IntA =< B_LB then
            CVZ = boolcv_const(yes),
            mzn_constraint_set_empty(AllConstraints)
        else if B_UB < IntA then
            CVZ = boolcv_const(no),
            mzn_constraint_set_empty(AllConstraints)
        else
            (
                ILHS = ilhs_true,
                set_int_lb(VarIdB, IntA, GlobalVarMap0, GlobalVarMap),
                !Model ^ model_globals := GlobalVarMap,
                CVZ = boolcv_const(yes),
                mzn_constraint_set_empty(AllConstraints)
            ;
                ILHS = ilhs_var(ILHSVar),
                % XXX OutsideAnns
                hr_add_tmp_bool_var(Context, OutsideAnns, ILHS, unit,
                    "int_le_reif",
                    [int_to_mzn_expr(int_const(IntA)), int_to_mzn_expr(B)],
                    OutsideAnns, VarIdZ, Z, LEConstraints, !Info, !Model),
                CVZ = boolcv_var(var_no_index(VarIdZ)),
                hr_add_primitive_constraint("bool_le", 
                    [ilhsv_to_expr(ILHSVar), bool_to_mzn_expr(Z)],
                    OutsideAnns, ImplyConstraint, !Model),
                mzn_constraint_set_insert(ImplyConstraint, LEConstraints,
                    AllConstraints)
            )
        )
    ).

:- pred halfreify_var_int_par_int_to_bool(error_context::in, mzn_anns::in,
    ilhs::in, int_int_to_bool_op::in, int_expr::in, int::in,
    bool_const_or_var::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is semidet.

halfreify_var_int_par_int_to_bool(Context, OutsideAnns, ILHS, Op, A, IntB, CVZ,
        AllConstraints, !Info, !Model) :-
    (
        Op = ii2b_lt,
        int_minus_infinity < IntB,
        halfreify_var_int_par_int_to_bool(Context, OutsideAnns, ILHS,
            ii2b_le, A, IntB - 1, CVZ, AllConstraints, !Info, !Model)
    ;
        Op = ii2b_le,
        A = int_var(var_no_index(VarIdA)),
        GlobalVarMap0 = !.Model ^ model_globals,
        get_int_lb_ub(GlobalVarMap0, VarIdA, A_LB, A_UB),
        ( if A_UB =< IntB then
            CVZ = boolcv_const(yes),
            mzn_constraint_set_empty(AllConstraints)
        else if IntB < A_LB then
            CVZ = boolcv_const(no),
            mzn_constraint_set_empty(AllConstraints)
        else
            (
                ILHS = ilhs_true,
                set_int_ub(VarIdA, IntB, GlobalVarMap0, GlobalVarMap),
                !Model ^ model_globals := GlobalVarMap,
                CVZ = boolcv_const(yes),
                mzn_constraint_set_empty(AllConstraints)
            ;
                ILHS = ilhs_var(ILHSVar),
                % XXX OutsideAnns
                hr_add_tmp_bool_var(Context, OutsideAnns, ILHS, unit,
                    "int_le_reif",
                    [int_to_mzn_expr(A), int_to_mzn_expr(int_const(IntB))],
                    OutsideAnns, VarIdZ, Z, LEConstraints, !Info, !Model),
                CVZ = boolcv_var(var_no_index(VarIdZ)),
                hr_add_primitive_constraint("bool_le", 
                    [ilhsv_to_expr(ILHSVar), bool_to_mzn_expr(Z)],
                    OutsideAnns, ImplyConstraint, !Model),
                mzn_constraint_set_insert(ImplyConstraint, LEConstraints,
                    AllConstraints)
            )
        )
    ).

:- pred halfreify_var_int_var_int_to_bool(error_context::in, mzn_anns::in,
    ilhs::in, int_int_to_bool_op::in, int_expr::in, int_expr::in,
    bool_const_or_var::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is semidet.

halfreify_var_int_var_int_to_bool(Context, OutsideAnns, ILHS, Op, A, B, CVZ,
        AllConstraints, !Info, !Model) :-
    GlobalVarMap0 = !.Model ^ model_globals,
    get_int_expr_lb_ub(Context, GlobalVarMap0, A, LBA, UBA),
    get_int_expr_lb_ub(Context, GlobalVarMap0, B, LBB, UBB),
    (
        Op = ii2b_eq,
        Rel = relop_eq,
        RelP = ( pred(X::in, Y::in) is semidet :- X = Y ),
        ( if A = B then
            Ground = yes(yes),
            mzn_constraint_set_empty(MainConstraints)
        else if ( UBA < LBB ; UBB < LBA ) then
            Ground = yes(no),
            mzn_constraint_set_empty(MainConstraints)
        else
            (
                ILHS = ilhs_true,
                % Refine their bounds if these are variables.
                Bounds = int_range_lb_ub(int.max(LBA, LBB), int.min(UBA, UBB)),
                ( if
                    A = int_var(var_no_index(VarIdA)),
                    hr_get_var_value(!.Info, !.Model, VarIdA) = yes(_)
                then
                    hr_simplify_int(Context, OutsideAnns, ILHS,
                        B, SimpleB, ConstraintsSimpleB, !Info, !Model),
                    hr_refine_int_bounds(Context, ILHS, Bounds, A,
                        ConstraintsToAddA, !Model),
                    hr_refine_int_bounds(Context, ILHS, Bounds, SimpleB,
                        ConstraintsToAddB, !Model),
                    hr_set_var_value(VarIdA, int_to_mzn_expr(SimpleB),
                        !Info, !Model),
                    Ground = yes(yes),
                    ConstraintsToAdd = ConstraintsToAddA ++ ConstraintsToAddB,
                    hr_add_constraints_to_add(OutsideAnns, ILHS,
                        ConstraintsToAdd, AddedConstraints, !Info, !Model),
                    mzn_constraint_set_union(ConstraintsSimpleB,
                        AddedConstraints, MainConstraints)
                else if
                    B = int_var(var_no_index(VarIdB)),
                    hr_get_var_value(!.Info, !.Model, VarIdB) = yes(_)
                then
                    hr_simplify_int(Context, OutsideAnns, ILHS,
                        A, SimpleA, ConstraintsSimpleA, !Info, !Model),
                    hr_refine_int_bounds(Context, ILHS, Bounds, SimpleA,
                        ConstraintsToAddA, !Model),
                    hr_refine_int_bounds(Context, ILHS, Bounds, B,
                        ConstraintsToAddB, !Model),
                    hr_set_var_value(VarIdB, int_to_mzn_expr(SimpleA),
                        !Info, !Model),
                    Ground = yes(yes),
                    ConstraintsToAdd = ConstraintsToAddA ++ ConstraintsToAddB,
                    hr_add_constraints_to_add(OutsideAnns, ILHS,
                        ConstraintsToAdd, AddedConstraints, !Info, !Model),
                    mzn_constraint_set_union(ConstraintsSimpleA,
                        AddedConstraints, MainConstraints)
                else if
                    A = -1 * int_var(var_no_index(VarIdA)),
                    B = int_const(IntB),
                    hr_get_var_value(!.Info, !.Model, VarIdA) = yes(_)
                then
                    RangeForA = int_range_lb_ub(-IntB, -IntB),
                    hr_do_refine_int_bounds(Context, RangeForA, VarIdA,
                        ConstraintsToAdd, !Model),
                    hr_set_var_value(VarIdA, int_to_mzn_expr(int_const(-IntB)),
                        !Info, !Model),
                    Ground = yes(yes),
                    hr_add_constraints_to_add(OutsideAnns, ILHS,
                        ConstraintsToAdd, MainConstraints, !Info, !Model)
                else if
                    A = int_const(IntA),
                    B = -1 * int_var(var_no_index(VarIdB)),
                    hr_get_var_value(!.Info, !.Model, VarIdB) = yes(_)
                then
                    RangeForB = int_range_lb_ub(-IntA, -IntA),
                    hr_do_refine_int_bounds(Context, RangeForB, VarIdB,
                        ConstraintsToAdd, !Model),
                    hr_set_var_value(VarIdB, int_to_mzn_expr(int_const(-IntA)),
                        !Info, !Model),
                    Ground = yes(yes),
                    hr_add_constraints_to_add(OutsideAnns, ILHS,
                        ConstraintsToAdd, MainConstraints, !Info, !Model)
                else
                    Ground = no,
                    mzn_constraint_set_empty(MainConstraints)
                )
            ;
                ILHS = ilhs_var(_),
                Ground = no,
                mzn_constraint_set_empty(MainConstraints)
            )
        )
    ;
        Op = ii2b_ne,
        Rel = relop_ne,
        RelP = ( pred(X::in, Y::in) is semidet :- X \= Y ),
        ( if ( UBA < LBB ; UBB < LBA ) then
            Ground = yes(yes)
        else if A = B then
            Ground = yes(no)
        else
            Ground = no
        ),
        mzn_constraint_set_empty(MainConstraints)
    ;
        Op = ii2b_lt,
        Rel = relop_lt,
        RelP = int.(<),
        ( if UBA < LBB then
            Ground = yes(yes)
        else if UBB < LBA then
            Ground = yes(no)
        else
            Ground = no,
            (
                ILHS = ilhs_true,
                RangeForA = int_bounded_plus(Context, UBB, -1),
                RangeForB = int_bounded_plus(Context, LBA,  1),
                hr_refine_int_ub(ILHS, RangeForA, A, !Model),
                hr_refine_int_lb(ILHS, RangeForB, B, !Model)
            ;
                ILHS = ilhs_var(_)
            )
        ),
        mzn_constraint_set_empty(MainConstraints)
    ;
        Op = ii2b_le,
        Rel = relop_le,
        RelP = int.(=<),
        ( if UBA =< LBB then
            Ground = yes(yes)
        else if UBB < LBA then
            Ground = yes(no)
        else
            Ground = no,
            (
                ILHS = ilhs_true,
                hr_refine_int_ub(ILHS, UBB, A, !Model),
                hr_refine_int_lb(ILHS, LBA, B, !Model)
            ;
                ILHS = ilhs_var(_)
            )
        ),
        mzn_constraint_set_empty(MainConstraints)
    ),
    ( if Ground = yes(Bool) then
        CVZ = boolcv_const(Bool),
        AllConstraints = MainConstraints
    else
        (
            ILHS = ilhs_true,
            make_int_int_constraint(Rel, RelP, cns_none,
                A, B, ConstraintName, Args, MaybeSolved),
            (
                MaybeSolved = no,
                hr_add_primitive_constraint(ConstraintName, Args, OutsideAnns,
                    AddedConstraint, !Model),
                CVZ = boolcv_const(yes),
                mzn_constraint_set_insert(AddedConstraint, MainConstraints,
                    AllConstraints)
            ;
                MaybeSolved = yes(yes),
                % The constraint is trivially true.
                CVZ = boolcv_const(yes),
                AllConstraints = MainConstraints
            ;
                MaybeSolved = yes(no),
                % The constraint is trivially false.
                model_inconsistency_detected(Context,
                    "Unsatisfiable constraint.\n")
            )
        ;
            ILHS = ilhs_var(ILHSVar),
            % XXX cns_reif
            make_int_int_constraint(Rel, RelP, cns_reif, A, B,
                ConstraintName, Args, MaybeSolved),
            (
                MaybeSolved = no,
                hr_add_tmp_bool_var(Context, OutsideAnns, ILHS, unit,
                    ConstraintName, Args, OutsideAnns,
                    VarIdZ, Z, VarConstraints, !Info, !Model),
                CVZ = boolcv_var(var_no_index(VarIdZ)),
                % XXX implication
                hr_add_primitive_constraint("bool_le", 
                    [ilhsv_to_expr(ILHSVar), bool_to_mzn_expr(Z)],
                    OutsideAnns, ImplyConstraint, !Model),
                mzn_constraint_set_union_mixed_list([ImplyConstraint],
                    [MainConstraints, VarConstraints], AllConstraints)
            ;
                MaybeSolved = yes(TorF),
                CVZ = boolcv_const(TorF),
                AllConstraints = MainConstraints
            )
        )
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

hr_simplify_int(Context, OutsideAnns, ILHS, A, Z, AllConstraints,
        !Info, !Model) :-
    ( if int_expr_is_simple(A) then
        Z = A,
        mzn_constraint_set_empty(AllConstraints)
    else
        % This isn't a trivial expression. We need to simplify it to
        % an addition or subtraction or linear sum.
        get_int_expr_lb_ub(Context, !.Model ^ model_globals, A, LB, UB),
        Bounds = int_range_lb_ub(LB, UB),
        flatten_int_expr(A, CoeffsA0, VarsA0, ConstA0),
        CoeffsA = list.map(func(C) = int_const(C), CoeffsA0),
        VarsA = list.map(func(V) = int_var(V), VarsA0),
        ConstA = int_const(-ConstA0),
        ( if CoeffsA0 = [] then
            Z = int_const(ConstA0),
            mzn_constraint_set_empty(AllConstraints)
        else if ConstA0 = 0, CoeffsA0 = [1], VarsA = [V1] then
            Z = V1,
            mzn_constraint_set_empty(AllConstraints)
        else if ConstA0 = 0, CoeffsA0 = [1, 1], VarsA = [V1, V2] then
            hr_add_tmp_int_var(Context, OutsideAnns, ILHS, Bounds, "int_plus",
                [int_to_mzn_expr(V1), int_to_mzn_expr(V2)],
                no_anns, _VarIdZ, Z, AllConstraints, !Info, !Model)
        else if ConstA0 = 0, CoeffsA0 = [1, -1], VarsA = [V1, V2] then
            % NOTE: there is no int_minus/3 builtin in FlatZinc, but in order
            % to simplify CSE, we PRETEND that there. When we output
            % int_minus/3 constraints, we transform them into int_plus/3
            % constraints using the following identity:
            %
            %    int_minus(a, b, c) <=> int_plus(c, b, a)

            hr_add_tmp_int_var(Context, OutsideAnns, ILHS, Bounds, "int_minus",
                [int_to_mzn_expr(V1), int_to_mzn_expr(V2)],
                no_anns, _VarIdZ, Z, AllConstraints, !Info, !Model)
        else
            MznCoeffsA = int_array_to_mzn_expr(list_to_array_expr(CoeffsA)),
            MznVarsA = int_array_to_mzn_expr(list_to_array_expr(VarsA)),
            MznConstA = int_to_mzn_expr(ConstA),
            PartialConstraint = mzn_constraint("int_lin_eq",
                [MznCoeffsA, MznVarsA, MznConstA], no_anns),
            ( if hr_search_for_cse_var(!.Info, PartialConstraint, PCVar) then
                Z = int_var(var_no_index(PCVar)),
                mzn_constraint_set_empty(AllConstraints)
            else
                hr_make_tmp_int_var(Context, OutsideAnns, ILHS, Bounds,
                    just_is_defined_var, VarIdZ, Z, AddVarConstraints,
                    !Info, !Model),
                hr_add_cse_var(PartialConstraint, VarIdZ, !Info),
                MZ = int_to_mzn_expr(Z),
                LinEqArgs =
                    [ int_array_to_mzn_expr(
                        list_to_array_expr([int_const(-1) | CoeffsA])),
                      int_array_to_mzn_expr(
                        list_to_array_expr([Z             | VarsA  ])),
                      MznConstA
                    ],
                hr_add_primitive_constraint("int_lin_eq", LinEqArgs,
                    just_defines_var(MZ), LinEqConstraint, !Model),
                mzn_constraint_set_insert(LinEqConstraint, AddVarConstraints,
                    AllConstraints)
            )
        )
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

hr_refine_int_bounds(Context, ILHS, RefineBounds, A, ConstraintsToAdd,
        !Model) :-
    ( if
        A = int_var(var_no_index(VarId)),
        ILHS = ilhs_true
    then
        hr_do_refine_int_bounds(Context, RefineBounds, VarId, ConstraintsToAdd,
            !Model)
    else
        ConstraintsToAdd = []
    ).

hr_do_refine_int_bounds(Context, RefineBounds, VarId, ConstraintsToAdd,
        !Model) :-
    (
        RefineBounds = int_range_unbounded,
        ConstraintsToAdd = []
    ;
        RefineBounds = int_range_lb_ub(RefineLB, RefineUB),
        GlobalVarMap0 = !.Model ^ model_globals,
        get_int_lb_ub(GlobalVarMap0, VarId, OldLB, OldUB),
        LB = int.max(RefineLB, OldLB),
        UB = int.min(RefineUB, OldUB),
        set_int_lb_ub(VarId, LB, UB, GlobalVarMap0, GlobalVarMap),
        !Model ^ model_globals := GlobalVarMap,
        ConstraintsToAdd = []
    ;
        RefineBounds = int_range_set(RefineSet),
        % GlobalVarMap0 = !.Model ^ model_globals,
        % map.lookup(GlobalVarMap0, VarId, VarInfo0),
        % VarBounds0 = VarInfo0 ^ vi_bounds,
        ( if
            % JJJ FIXME - INTSET REP - simplify the rest of this condition.
            RefineXs = intset.to_sorted_list(RefineSet),
            RefineXs = [RefineLB | _],
            list.last(RefineXs, RefineUB)
        then
            % XXX It should be possible to preserve much more information
            % about the bounds than this.
            GlobalVarMap0 = !.Model ^ model_globals,
            get_int_lb_ub(GlobalVarMap0, VarId, OldLB, OldUB),
            LB = int.max(RefineLB, OldLB),
            UB = int.min(RefineUB, OldUB),
            set_int_lb_ub(VarId, LB, UB, GlobalVarMap0, GlobalVarMap),
            !Model ^ model_globals := GlobalVarMap
        else
            true
        ),
        % JJJ FIXME - INTSET REP - need a better rep for int_set exprs.
        % XXX We could insist that A be not just in Set, but in the
        % intersection of Set and VarBounds0.
        InSet = set.from_sorted_list(intset.to_sorted_list(RefineSet)),
        ConstraintToAdd = mzn_constraint_to_add(Context, "set_in",
            [int_to_mzn_expr(int_var(var_no_index(VarId))),
                int_set_to_mzn_expr(set_items(InSet))],
            no_anns),
        ConstraintsToAdd = [ConstraintToAdd]
    ).

hr_refine_int_lb(ILHS, RefineLB, A, !Model) :-
    ( if
        A = int_var(var_no_index(VarId)),
        ILHS = ilhs_true
    then
        hr_do_refine_int_lb(RefineLB, VarId, !Model)
    else
        true
    ).

hr_do_refine_int_lb(RefineLB, VarId, !Model) :-
    GlobalVarMap0 = !.Model ^ model_globals,
    OldLB = get_int_lb(GlobalVarMap0, VarId),
    LB = int.max(RefineLB, OldLB),
    set_int_lb(VarId, LB, GlobalVarMap0, GlobalVarMap),
    !Model ^ model_globals := GlobalVarMap.

hr_refine_int_ub(ILHS, RefineUB, A, !Model) :-
    ( if
        A = int_var(var_no_index(VarId)),
        ILHS = ilhs_true
    then
        hr_do_refine_int_ub(RefineUB, VarId, !Model)
    else
        true
    ).

hr_do_refine_int_ub(RefineUB, VarId, !Model) :-
    GlobalVarMap0 = !.Model ^ model_globals,
    OldUB = get_int_ub(GlobalVarMap0, VarId),
    UB = int.min(RefineUB, OldUB),
    set_int_ub(VarId, UB, GlobalVarMap0, GlobalVarMap),
    !Model ^ model_globals := GlobalVarMap.

%-----------------------------------------------------------------------------%
:- end_module hr.int.
%-----------------------------------------------------------------------------%
