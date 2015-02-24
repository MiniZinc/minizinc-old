%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2009 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Ralph Becket <rafe@csse.unimelb.edu.au>
%
% We divide up the cases for flattening built-in operators by type and by
% call inst (e.g., par par/par var/var par/var var/var).
%
%-----------------------------------------------------------------------------%

:- module flatten.float.
:- interface.

:- import_module errors.
:- import_module flatten.env.
:- import_module mzn_ops.
:- import_module types.

:- import_module bool.

%-----------------------------------------------------------------------------%
%
% These predicates assume their float_expr arguments have been simplified
% where possible.
%

:- pred flatten_float_to_float(error_context::in, mzn_anns::in,
    float_to_float_op::in, float_expr::in,
    float_expr::out, env::in, env::out) is semidet.

:- pred flatten_float_to_int(error_context::in, mzn_anns::in,
    float_to_int_op::in, float_expr::in,
    int_expr::out, env::in, env::out) is det.

:- pred flatten_float_to_float_set(error_context::in, mzn_anns::in,
    float_to_float_set_op::in, float_expr::in,
    float_set_expr::out, env::in, env::out) is det.

:- pred flatten_float_float_to_float(error_context::in, mzn_anns::in,
    float_float_to_float_op::in, float_expr::in, float_expr::in,
    float_expr::out, env::in, env::out) is semidet.

:- pred flatten_float_float_to_float_set(error_context::in, mzn_anns::in,
    float_float_to_float_set_op::in, float_expr::in, float_expr::in,
    float_set_expr::out, env::in, env::out) is det.

:- pred flatten_float_float_to_bool(error_context::in, mzn_anns::in,
    float_float_to_bool_op::in, float_expr::in, float_expr::in,
    bool_const_or_var::out, env::in, env::out) is semidet.

:- pred flatten_float_float_set_to_bool(error_context::in, mzn_anns::in,
    float_float_set_to_bool_op::in, float_expr::in, float_set_expr::in,
    bool::out, env::in, env::out) is det.

    % Convert an float_expr into a "simple" (i.e., FlatZinc) form (namely
    % either a constant or a variable).  This may require introducing a new
    % temporary variable if the float_expr is a linear sum.
    %
:- pred simplify_float(error_context::in,
    float_expr::in, float_expr::out, env::in, env::out) is det.

    % Refine bounds on a float variable.
    % These do nothing in a reifying context.
    % These do nothing if the float_expr is not a float_var(var_no_index(_)).
    %
:- pred refine_float_bounds(error_context::in,
    float_range::in, float_expr::in, env::in, env::out) is det.
:- pred do_refine_float_bounds(error_context::in,
    float_range::in, var_id::in, env::in, env::out) is det.

:- pred refine_float_lb(float::in, float_expr::in, env::in, env::out) is det.
:- pred do_refine_float_lb(float::in, var_id::in, env::in, env::out) is det.

:- pred refine_float_ub(float::in, float_expr::in, env::in, env::out) is det.
:- pred do_refine_float_ub(float::in, var_id::in, env::in, env::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module bounds.
:- import_module common_array.
:- import_module common_bounds.
:- import_module common_expr.

:- import_module float.
:- import_module list.
:- import_module math.
:- import_module maybe.
:- import_module set.
:- import_module string.
:- import_module unit.

%-----------------------------------------------------------------------------%

flatten_float_to_float(Context, Anns, Op, A, Z, !Env) :-
    ( if
        A = float_const(FloatA),
        flatten_par_float_to_float(Context, Op, FloatA, FloatZ)
    then
        Z = float_const(FloatZ)
    else
        flatten_var_float_to_float(Context, Anns, Op, A, Z, !Env)
    ).

%-----------------------------------------------------------------------------%

flatten_float_to_float_set(Context, _Anns, f2fs_dom, _A, Z, !Env) :-
    ( if semidet_true then   % Silence a compiler warning.
        minizinc_user_error(Context, "'dom' not supported for floats.\n")
    else
        Z = set_items(set.init)
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_par_float_to_float(error_context::in,
    float_to_float_op::in, float::in, float::out) is det.

flatten_par_float_to_float(Context, Op, FloatA, FloatZ) :-
    (
        ( Op = f2f_add,     FloatZ = FloatA
        ; Op = f2f_sub,     FloatZ = -FloatA
        ; Op = f2f_lb,      FloatZ = FloatA
        ; Op = f2f_ub,      FloatZ = FloatA
        ; Op = f2f_abs,     FloatZ = float.abs(FloatA)
        ; Op = f2f_exp,     FloatZ = math.exp(FloatA)
        ; Op = f2f_sin,     FloatZ = math.sin(FloatA)
        ; Op = f2f_cos,     FloatZ = math.cos(FloatA)
        ; Op = f2f_tan,     FloatZ = math.tan(FloatA)
        ; Op = f2f_sinh,    FloatZ = math.sinh(FloatA)
        ; Op = f2f_cosh,    FloatZ = math.cosh(FloatA)
        ; Op = f2f_tanh,    FloatZ = math.tanh(FloatA)
        ; Op = f2f_asin,    FloatZ = math.asin(FloatA)
        ; Op = f2f_acos,    FloatZ = math.acos(FloatA)
        ; Op = f2f_atan,    FloatZ = math.atan(FloatA)
        )
    ;
        ( Op = f2f_ln,      Func = math.ln
        ; Op = f2f_log10,   Func = math.log10
        ; Op = f2f_log2,    Func = math.log2
        ),
        ( if FloatA = 0.0 then
            is_float_to_float_op(OpStr, Op),
            minizinc_user_error(Context,
                "Zero argument to '" ++ OpStr ++ "'.\n")
        else
            FloatZ = Func(FloatA)
        )
    ;
        Op = f2f_sqrt,
        ( if FloatA >= 0.0 then
            FloatZ = math.sqrt(FloatA)
        else
            minizinc_user_error(Context, "Negative argument to 'sqrt'.\n")
        )
    ;
        Op = f2f_fix,
        minizinc_internal_error(Context, $pred,
            "fix should have been handled elsewhere\n")
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_var_float_to_float(error_context::in, mzn_anns::in,
    float_to_float_op::in, float_expr::in, float_expr::out,
    env::in, env::out) is semidet.

flatten_var_float_to_float(Context, Anns, Op, A, Z, !Env) :-
    (
        Op = f2f_add,
        Z = A
    ;
        Op = f2f_sub,
        simplify_float(Context, A, SimpleA, !Env),
        get_float_expr_lb_ub(!.Env ^ env_globals, SimpleA, LBA, UBA),
        ( if UBA = float_plus_infinity then
            LB = float_minus_infinity
        else
            LB = -UBA
        ),
        ( if LBA = float_minus_infinity then
            UB = float_plus_infinity
        else
            UB = -LBA
        ),
        Bounds = float_range_lb_ub(LB, UB),
        add_tmp_float_var(Context, Bounds, "float_negate",
            [float_to_mzn_expr(SimpleA)], Anns, _VarId, Z, !Env)
    ;
        Op = f2f_lb,
        get_float_expr_lb_ub(!.Env ^ env_globals, A, LBA, _UBA),
        ( if LBA = float_minus_infinity then
            minizinc_user_error(Context, "Cannot infer lower bound.\n")
        else
            Z = float_const(LBA)
        )
    ;
        Op = f2f_ub,
        get_float_expr_lb_ub(!.Env ^ env_globals, A, _LBA, UBA),
        ( if UBA = float_plus_infinity then
            minizinc_user_error(Context, "Cannot infer upper bound.\n")
        else
            Z = float_const(UBA)
        )
    ;
        Op = f2f_abs,
        simplify_float(Context, A, SimpleA, !Env),
        get_float_expr_lb_ub(!.Env ^ env_globals, SimpleA, LBA, UBA),
        ( if LBA < 0.0, 0.0 < UBA then
            LB = 0.0,
            ( if
                ( LBA = float_minus_infinity
                ; UBA = float_plus_infinity
                )
            then
                UB = float_plus_infinity
            else
                UB = -LBA
            ),
            Bounds = float_range_lb_ub(LB, UB),
            add_tmp_float_var(Context, Bounds, "float_abs",
                [float_to_mzn_expr(SimpleA)], Anns, _VarId, Z, !Env)
        else if UBA < 0.0 then
            flatten_var_float_to_float(Context, Anns, f2f_sub,
                SimpleA, Z, !Env)
        else
            Z = A
        )
    ;
        Op = f2f_exp,
        simplify_float(Context, A, SimpleA, !Env),
        get_float_expr_lb_ub(!.Env ^ env_globals, SimpleA, LBA, UBA),
        ( if LBA = float_minus_infinity then
            LB = 0.0
        else
            LB = math.exp(LBA)
        ),
        ( if UBA = float_plus_infinity then
            UB = float_plus_infinity
        else
            UB = math.exp(UBA)
        ),
        Bounds = float_range_lb_ub(LB, UB),
        add_tmp_float_var(Context, Bounds, "float_exp",
            [float_to_mzn_expr(SimpleA)], Anns, _VarId, Z, !Env)
    ;
        ( Op = f2f_sin, ConstraintName = "float_sin"
        ; Op = f2f_cos, ConstraintName = "float_cos"
        ),
        simplify_float(Context, A, SimpleA, !Env),
        % XXX For some ranges of A, we could generate tighter bounds.
        Bounds = float_range_lb_ub(-1.0, 1.0),
        add_tmp_float_var(Context, Bounds, ConstraintName,
            [float_to_mzn_expr(SimpleA)], Anns, _VarId, Z, !Env)
    ;
        ( Op = f2f_sqrt
        ; Op = f2f_ln
        ; Op = f2f_log10
        ; Op = f2f_log2
        ; Op = f2f_tan
        ; Op = f2f_cosh
        ; Op = f2f_sinh
        ; Op = f2f_tanh
        ; Op = f2f_acos
        ; Op = f2f_asin
        ; Op = f2f_atan
        ),
        is_float_to_float_op(OpStr, Op),
        minizinc_internal_error(Context, $pred,
            "'" ++ OpStr ++ "' not yet implemented for float variables.\n")
    ).

%-----------------------------------------------------------------------------%

flatten_float_to_int(Context, Anns, Op, A, Z, !Env) :-
    ( Op = f2i_ceil
    ; Op = f2i_floor
    ; Op = f2i_round
    ),
    simplify_float(Context, A, SimpleA, !Env),
    ( if SimpleA = float_const(FloatA) then
        flatten_par_float_to_int(Context, Anns, Op, FloatA, IntZ, !Env),
        Z = int_const(IntZ)
    else
        is_float_to_int_op(OpStr, Op),
        minizinc_internal_error(Context, $pred,
            "'" ++ OpStr ++ "' not yet implemented for float variables.\n")
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_par_float_to_int(error_context::in, mzn_anns::in,
    float_to_int_op::in, float::in, int::out, env::in, env::out) is det.

flatten_par_float_to_int(_Context, _Anns, Op, FloatA, IntZ, !Env) :-
    (
        Op = f2i_ceil,
        IntZ = float.ceiling_to_int(FloatA)
    ;
        Op = f2i_floor,
        IntZ = float.floor_to_int(FloatA)
    ;
        Op = f2i_round,
        IntZ = float.round_to_int(FloatA)
    ).

%-----------------------------------------------------------------------------%

flatten_float_float_to_float(Context, Anns, Op, A, B, Z, !Env) :-
    ( if
        A = float_const(FloatA), B = float_const(FloatB),
        flatten_par_float_par_float_to_float(Context, Op, FloatA, FloatB,
            FloatZ)
    then
        Z = float_const(FloatZ)
    else if
        A = float_const(FloatA),
        flatten_par_float_var_float_to_float(Context, Op, FloatA, B, Z0)
    then
        Z = Z0
    else if
        B = float_const(FloatB),
        flatten_var_float_par_float_to_float(Context, Op, A, FloatB, Z0)
    then
        Z = Z0
    else
        flatten_var_float_var_float_to_float(Context, Anns, Op, A, B, Z, !Env)
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_par_float_par_float_to_float(error_context::in,
    float_float_to_float_op::in, float::in, float::in, float::out) is det.

flatten_par_float_par_float_to_float(Context, Op, FloatA, FloatB, FloatZ) :-
    (
        ( Op = ff2f_add,    FloatZ = FloatA + FloatB
        ; Op = ff2f_sub,    FloatZ = FloatA - FloatB
        ; Op = ff2f_mul,    FloatZ = FloatA * FloatB
        ; Op = ff2f_max,    FloatZ = float.max(FloatA, FloatB)
        ; Op = ff2f_min,    FloatZ = float.min(FloatA, FloatB)
        )
    ;
        Op = ff2f_div,
        ( if FloatB = 0.0 then
            minizinc_user_error(Context, "Division by zero.\n")
        else
            FloatZ = FloatA / FloatB
        )
    ;
        Op = ff2f_log,
        ( if FloatA =< 0.0 then
            minizinc_user_error(Context, "log/2 with negative or zero base.\n")
        else if FloatA = 1.0 then
            minizinc_user_error(Context, "log/2 with base equal to 1.\n")
        else
            compare(Result, FloatB, 0.0),
            (
                Result = (<),
                minizinc_user_error(Context,
                    "Cannot take the logarithm of a negative number.\n")
            ;
                Result = (=),
                minizinc_user_error(Context,
                    "Cannot take the logarithm of zero.\n")
            ;
                Result = (>),
                FloatZ = math.log(FloatA, FloatB)
            )
        )
    ;
        Op = ff2f_pow,
        compare(Res, FloatA, 0.0),
        (
            Res = (>),
            FloatZ = math.pow(FloatA, FloatB)
        ;
            Res = (=),
            ( if FloatB > 0.0 then
                FloatZ = math.pow(FloatA, FloatB)
            else
                minizinc_user_error(Context,
                    "Cannot raise 0.0 to a non-positive power.\n")
            )
        ;
            Res = (<),
            minizinc_user_error(Context,
                "Cannot raise a negative float to any power.\n")
        )
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_par_float_var_float_to_float(error_context::in,
    float_float_to_float_op::in, float::in, float_expr::in, float_expr::out)
    is semidet.

flatten_par_float_var_float_to_float(_Context, ff2f_mul, FloatA, B, Z) :-
    ( if FloatA = 0.0 then
        Z = float_const(0.0)
    else if FloatA = 1.0 then
        Z = B
    else if B = FloatB * C then
        Z = (FloatA * FloatB) * C
    else
        Z = FloatA * B
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_var_float_par_float_to_float(error_context::in,
    float_float_to_float_op::in, float_expr::in, float::in, float_expr::out)
    is semidet.

flatten_var_float_par_float_to_float(Context, Op, A, FloatB, Z) :-
    (
        Op = ff2f_mul,
        flatten_par_float_var_float_to_float(Context, ff2f_mul, FloatB, A, Z)
    ;
        Op = ff2f_div,
        ( if FloatB = 0.0 then
            minizinc_user_error(Context, "Division by zero.\n")
        else
            flatten_par_float_var_float_to_float(Context, ff2f_mul,
                1.0 / FloatB, A, Z)
        )
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_var_float_var_float_to_float(error_context::in, mzn_anns::in,
    float_float_to_float_op::in, float_expr::in, float_expr::in,
    float_expr::out, env::in, env::out) is semidet.

flatten_var_float_var_float_to_float(Context, Anns, Op, A, B, Z, !Env) :-
    (
        Op = ff2f_add,
        Z = A + B
    ;
        Op = ff2f_sub,
        Z = A + -1.0 * B
    ;
        (
            Op = ff2f_mul,
            BoundsP = float_times_bounds,
            ConstraintName = "float_times",
            Reifying = not_reifying
        ;
            Op = ff2f_div,
            BoundsP = float_div_bounds,
            ConstraintName = "float_div",
            Reifying = !.Env ^ reifying
        ;
            Op = ff2f_min,
            BoundsP = float_min_bounds,
            ConstraintName = "float_min",
            Reifying = not_reifying
        ;
            Op = ff2f_max,
            BoundsP = float_max_bounds,
            ConstraintName = "float_max",
            Reifying = not_reifying
        ),
        simplify_float(Context, A, SimpleA, !Env),
        simplify_float(Context, B, SimpleB, !Env),
        get_float_expr_lb_ub(!.Env ^ env_globals, SimpleA, LBA, UBA),
        get_float_expr_lb_ub(!.Env ^ env_globals, SimpleB, LBB, UBB),
        BoundsP(LBA, UBA, LBB, UBB, LB, UB),
        (
            Reifying = not_reifying,
            add_tmp_float_var(Context, float_range_lb_ub(LB, UB),
                ConstraintName,
                [float_to_mzn_expr(SimpleA), float_to_mzn_expr(SimpleB)],
                Anns, _VarId, Z, !Env)
        ;
            Reifying = reifying(ReifVarExprs : bool_exprs),
            make_tmp_float_var(Context, float_range_lb_ub(LB, UB), Anns, _C,
                Z, !Env),
            ReifConstraintName = ConstraintName ++ "_reif",
            add_tmp_bool_var(Context, unit, ReifConstraintName,
                [float_to_mzn_expr(SimpleA), float_to_mzn_expr(SimpleB),
                    float_to_mzn_expr(Z)],
                Anns, _ReifVar, ReifVarExpr, !Env),
            !Env ^ reifying := reifying([ReifVarExpr | ReifVarExprs])
        )
    ).

%-----------------------------------------------------------------------------%

flatten_float_float_to_float_set(Context, _Anns, Op, _A, _B, Z, !Env) :-
    (
        Op = ff2fs_range,
        ( if semidet_true then   % Silence a compiler warning.
            minizinc_user_error(Context,
                "'..' cannot be used for set of float values.\n")
        else
            Z = set_items(set.init)
        )
    ).

%-----------------------------------------------------------------------------%

flatten_float_float_to_bool(Context, Anns, Op, A0, B0, Z, !Env) :-
    simplify_float(Context, A0, A, !Env),
    simplify_float(Context, B0, B, !Env),
    ( if
        ( Op = ff2b_ee,  RevOp = ff2b_eq
        ; Op = ff2b_ge,  RevOp = ff2b_le
        ; Op = ff2b_gt,  RevOp = ff2b_lt
        )
    then
        flatten_float_float_to_bool(Context, Anns, RevOp, B, A, Z, !Env)
    else if
        A = float_const(FA), B = float_const(FB),
        flatten_par_float_par_float_to_bool(Op, FA, FB, BoolZ)
    then
        Z = boolcv_const(BoolZ)
    else if
        A = float_const(FA),
        flatten_par_float_var_float_to_bool(Context, Anns, Op, FA, B, Z0, !Env)
    then
        Z = Z0
    else if
        B = float_const(FB),
        flatten_var_float_par_float_to_bool(Context, Anns, Op, A, FB, Z0, !Env)
    then
        Z = Z0
    else
        flatten_var_float_var_float_to_bool(Context, Anns, Op, A, B, Z, !Env)
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_par_float_par_float_to_bool(float_float_to_bool_op::in,
    float::in, float::in, bool::out) is det.

flatten_par_float_par_float_to_bool(Op, FloatA, FloatB, BoolZ) :-
    ( Op = ff2b_ee, BoolZ = ( if FloatA =  FloatB then yes else no )
    ; Op = ff2b_eq, BoolZ = ( if FloatA =  FloatB then yes else no )
    ; Op = ff2b_ne, BoolZ = ( if FloatA \= FloatB then yes else no )
    ; Op = ff2b_le, BoolZ = ( if FloatA =< FloatB then yes else no )
    ; Op = ff2b_lt, BoolZ = ( if FloatA <  FloatB then yes else no )
    ; Op = ff2b_ge, BoolZ = ( if FloatA >= FloatB then yes else no )
    ; Op = ff2b_gt, BoolZ = ( if FloatA >  FloatB then yes else no )
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_par_float_var_float_to_bool(error_context::in, mzn_anns::in,
    float_float_to_bool_op::in, float::in, float_expr::in,
    bool_const_or_var::out, env::in, env::out) is semidet.

flatten_par_float_var_float_to_bool(Context, Anns, Op, FA, B, CVZ, !Env) :-
    (
        Op = ff2b_le,
        B = float_var(var_no_index(V)),
        LB = !.Env ^ var_float_lb(V),
        ( if FA =< LB then
            CVZ = boolcv_const(yes)
        else if !.Env ^ var_float_ub(V) < FA then
            CVZ = boolcv_const(no)
        else
            Reifying = !.Env ^ reifying,
            (
                Reifying = not_reifying,
                !Env ^ var_float_lb(V) := FA,
                CVZ = boolcv_const(yes)
            ;
                Reifying = reifying(_ : bool_exprs),
                add_tmp_bool_var(Context, unit, "float_le_reif",
                    [float_to_mzn_expr(float_const(FA)), float_to_mzn_expr(B)],
                    Anns, VarIdZ, _Z, !Env),
                CVZ = boolcv_var(var_no_index(VarIdZ))
            )
        )
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_var_float_par_float_to_bool(error_context::in, mzn_anns::in,
    float_float_to_bool_op::in, float_expr::in, float::in,
    bool_const_or_var::out, env::in, env::out) is semidet.

flatten_var_float_par_float_to_bool(Context, Anns, Op, A, FB, CVZ, !Env) :-
    (
        Op = ff2b_le,
        A = float_var(var_no_index(V)),
        UB = !.Env ^ var_float_ub(V),
        ( if UB =< FB then
            CVZ = boolcv_const(yes)
        else if FB < !.Env ^ var_float_lb(V) then
            CVZ = boolcv_const(no)
        else
            Reifying = !.Env ^ reifying,
            (
                Reifying = not_reifying,
                !Env ^ var_float_ub(V) := FB,
                CVZ = boolcv_const(yes)
            ;
                Reifying = reifying(_ : bool_exprs),
                add_tmp_bool_var(Context, unit, "float_le_reif",
                    [float_to_mzn_expr(A), float_to_mzn_expr(float_const(FB))],
                    Anns, VarIdZ, _Z, !Env),
                CVZ = boolcv_var(var_no_index(VarIdZ))
            )
        )
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_var_float_var_float_to_bool(error_context::in, mzn_anns::in,
    float_float_to_bool_op::in, float_expr::in, float_expr::in,
    bool_const_or_var::out, env::in, env::out) is semidet.

flatten_var_float_var_float_to_bool(Context, Anns, Op, A, B, CVZ, !Env) :-
    get_float_expr_lb_ub(!.Env ^ env_globals, A, LBA, UBA),
    get_float_expr_lb_ub(!.Env ^ env_globals, B, LBB, UBB),
    Reifying = !.Env ^ reifying,
    (
        Op = ff2b_eq,
        Rel = relop_eq,
        RelP = ( pred(X::in, Y::in) is semidet :- X = Y ),
        ( if A = B then
            Ground = yes(yes)
        else if ( UBA < LBB ; UBB < LBA ) then
            Ground = yes(no)
        else
            (
                Reifying = not_reifying,
                % Refine their bounds if these are variables.
                Bounds = float_range_lb_ub(
                    float.max(LBA, LBB), float.min(UBA, UBB)),
                refine_float_bounds(Context, Bounds, A, !Env),
                refine_float_bounds(Context, Bounds, B, !Env),
                ( if
                    A = float_var(var_no_index(VarId)),
                    !.Env ^ var_value(VarId) \= _
                then
                    !Env ^ var_value(VarId) := float_to_mzn_expr(B),
                    Ground = yes(yes)
                else if
                    B = float_var(var_no_index(VarId)),
                    !.Env ^ var_value(VarId) \= _
                then
                    !Env ^ var_value(VarId) := float_to_mzn_expr(A),
                    Ground = yes(yes)
                else
                    Ground = no
                )
            ;
                Reifying = reifying(_ : bool_exprs),
                Ground = no
            )
        )
    ;
        Op = ff2b_ne,
        Rel = relop_ne,
        RelP = ( pred(X::in, Y::in) is semidet :- X \= Y ),
        ( if ( UBA < LBB ; UBB < LBA ) then
            Ground = yes(yes)
        else if A = B then
            Ground = yes(no)
        else
            Ground = no
        )
    ;
        Op = ff2b_lt,
        Rel = relop_lt,
        RelP = float.(<),
        ( if UBA < LBB then
            Ground = yes(yes)
        else if UBB =< LBA then
            Ground = yes(no)
        else
            Ground = no,
            (
                Reifying = not_reifying,
                refine_float_ub(UBB, A, !Env),
                refine_float_lb(LBA, B, !Env)
            ;
                Reifying = reifying(_ : bool_exprs)
            )
        )
    ;
        Op = ff2b_le,
        Rel = relop_le,
        RelP = float.(=<),
        ( if UBA =< LBB then
            Ground = yes(yes)
        else if UBB < LBA then
            Ground = yes(no)
        else
            Ground = no,
            (
                Reifying = not_reifying,
                Bounds = float_range_lb_ub(LBA, UBB),
                refine_float_bounds(Context, Bounds, A, !Env),
                refine_float_bounds(Context, Bounds, B, !Env)
            ;
                Reifying = reifying(_ : bool_exprs)
            )
        )
    ),
    ( if Ground = yes(Bool) then
        CVZ = boolcv_const(Bool)
    else
        (
            Reifying = not_reifying,
            make_float_float_constraint(Rel, RelP, A, B, ConstraintName, Args,
                MaybeSolved),
            (
                MaybeSolved = no,
                add_constraint(Context, ConstraintName, Args, Anns, !Env),
                CVZ = boolcv_const(yes)
            ;
                MaybeSolved = yes(yes),
                % The constraint is trivially true.
                CVZ = boolcv_const(yes)
            ;
                MaybeSolved = yes(no),
                % The constraint is trivially false.
                model_inconsistency_detected(Context,
                    "Unsatisfiable constraint.\n")
            )
        ;
            Reifying = reifying(_ : bool_exprs),
            make_float_float_reif_constraint(Rel, RelP, A, B, ConstraintName,
                Args, MaybeSolved),
            (
                MaybeSolved = no,
                add_tmp_bool_var(Context, unit, ConstraintName, Args, Anns,
                    VarIdZ, _Z, !Env),
                CVZ = boolcv_var(var_no_index(VarIdZ))
            ;
                MaybeSolved = yes(TorF),
                CVZ = boolcv_const(TorF)
            )
        )
    ).

%-----------------------------------------------------------------------------%

flatten_float_float_set_to_bool(Context, _Anns, ffs2b_in, A, B, BoolZ, !Env) :-
    simplify_float(Context, A, SimpleA, !Env),
    ( if SimpleA = float_const(FloatA), B = set_items(SetB) then
        BoolZ = (if set.contains(SetB, FloatA) then yes else no)
    else
        minizinc_user_error(Context,
            "Float 'in' application cannot have variable arguments.\n")
    ).

%-----------------------------------------------------------------------------%

simplify_float(Context, A, Z, !Env) :-
    ( if float_expr_is_simple(A) then
        Z = A
    else
        % This isn't a trivial expression. We need to simplify it
        % to an addition or subtraction or linear sum.
        get_float_expr_lb_ub(!.Env ^ env_globals, A, LB, UB),
        flatten_float_expr(A, CoeffsA0, VarsA0, ConstA0),
        CoeffsA1 = list.map(func(C) = float_const(C), CoeffsA0),
        CoeffsA = list_to_array_expr(CoeffsA1),
        VarsA1 = list.map(func(V) = float_var(V), VarsA0),
        VarsA = list_to_array_expr(VarsA1),
        ConstA = float_const(-ConstA0),
        Bounds = float_range_lb_ub(LB, UB),
        ( if CoeffsA0 = [] then
            Z = float_const(ConstA0)
        else if ConstA0 = 0.0, CoeffsA0 = [1.0], VarsA1 = [V1] then
            Z = V1
        else if ConstA0 = 0.0, CoeffsA0 = [1.0, 1.0], VarsA1 = [V1, V2] then
            add_tmp_float_var(Context, Bounds, "float_plus",
                [float_to_mzn_expr(V1), float_to_mzn_expr(V2)],
                no_anns, _VarId, Z, !Env)
        else if ConstA0 = 0.0, CoeffsA0 = [1.0, -1.0], VarsA1 = [V1, V2] then
            % NOTE: there is no float_minus/3 built-in in FlatZinc, but we
            % pretend that there is in order to simplify CSE.  When we
            % output float_minus/3 constraints we transform them into
            % float_plus/3 constraints using the following identity:
            %
            %    float_minus(a, b, c) <=> float_plus(c, b, a)

            add_tmp_float_var(Context, Bounds, "float_minus",
                [float_to_mzn_expr(V1), float_to_mzn_expr(V2)],
                no_anns, _VarId, Z, !Env)
        else
            PartialConstraint = mzn_constraint("float_lin_eq",
                [float_array_to_mzn_expr(CoeffsA),
                 float_array_to_mzn_expr(VarsA),
                 float_to_mzn_expr(ConstA)],
                no_anns
            ),
            ( if !.Env ^ cse_lookup(PartialConstraint) = Var then
                Z = float_var(var_no_index(Var))
            else
                make_tmp_float_var(Context, Bounds, just_is_defined_var,
                    VZ, Z, !Env),
                add_cse_var(PartialConstraint, VZ, !Env),
                add_constraint(Context, "float_lin_eq",
                    [ float_array_to_mzn_expr(
                        list_to_array_expr([float_const(-1.0) | CoeffsA1])),
                      float_array_to_mzn_expr(
                        list_to_array_expr([Z                 | VarsA1  ])),
                      float_to_mzn_expr(ConstA)
                    ],
                    just_defines_var(float_to_mzn_expr(Z)), !Env
                )
            )
        )
    ).

%-----------------------------------------------------------------------------%

:- pred make_float_float_constraint(mzn_relop::in,
    pred(float, float)::in(pred(in, in) is semidet),
    float_expr::in, float_expr::in, string::out, list(mzn_expr)::out,
    maybe(bool)::out) is det.

make_float_float_constraint(RelOp, RelP, A, B, ConstraintName, Args,
        MaybeSolved) :-
    ( if float_expr_is_simple(A), float_expr_is_simple(B) then
        ArgA = float_to_mzn_expr(A),
        ArgB = float_to_mzn_expr(B),
        (
            ( RelOp = relop_eq, ConstraintName = "float_eq"
            ; RelOp = relop_ne, ConstraintName = "float_ne"
            ; RelOp = relop_lt, ConstraintName = "float_lt"
            ; RelOp = relop_le, ConstraintName = "float_le"
            ),
            Args = [ArgA, ArgB]
        ;
            ( RelOp = relop_gt, ConstraintName = "float_lt"
            ; RelOp = relop_ge, ConstraintName = "float_le"
            ),
            Args = [ArgB, ArgA]
        ),
        MaybeSolved = no
    else
        flatten_float_expr(A + -1.0 * B, Coeffs0, Vars0, Const0),
        (
            Coeffs0 = [],
            ConstraintName = "dummy",
            Args = [],
            MaybeSolved = yes( if RelP(0.0, -Const0) then yes else no )
        ;
            Coeffs0 = [_ | _],
            Vars = list_to_array_expr(
                list.map(func(Var) = float_var(Var), Vars0)
            ),
            (
                ( RelOp = relop_eq, ConstraintName = "float_lin_eq"
                ; RelOp = relop_ne, ConstraintName = "float_lin_ne"
                ; RelOp = relop_lt, ConstraintName = "float_lin_lt"
                ; RelOp = relop_le, ConstraintName = "float_lin_le"
                ),
                Coeffs = list_to_array_expr(
                    list.map(func(Coeff) = float_const(Coeff), Coeffs0)
                ),
                Const = float_const(-Const0)
            ;
                ( RelOp = relop_gt, ConstraintName = "float_lin_lt"
                ; RelOp = relop_ge, ConstraintName = "float_lin_le"
                ),
                Coeffs = list_to_array_expr(
                    list.map(func(Coeff) = float_const(-Coeff), Coeffs0)
                ),
                Const = float_const(Const0)
            ),
            Args = [float_array_to_mzn_expr(Coeffs),
                float_array_to_mzn_expr(Vars), float_to_mzn_expr(Const)],
            MaybeSolved = no
        )
    ).

%-----------------------------------------------------------------------------%

:- pred make_float_float_reif_constraint(mzn_relop::in,
    pred(float, float)::in(pred(in, in) is semidet),
    float_expr::in, float_expr::in, string::out, list(mzn_expr)::out,
    maybe(bool)::out) is det.

make_float_float_reif_constraint(RelOp, RelP, A, B, ConstraintName, Args,
        MaybeSolved) :-
    ( if float_expr_is_simple(A), float_expr_is_simple(B) then
        ArgA = float_to_mzn_expr(A),
        ArgB = float_to_mzn_expr(B),
        (
            ( RelOp = relop_eq, ConstraintName = "float_eq_reif"
            ; RelOp = relop_ne, ConstraintName = "float_ne_reif"
            ; RelOp = relop_lt, ConstraintName = "float_lt_reif"
            ; RelOp = relop_le, ConstraintName = "float_le_reif"
            ),
            Args = [ArgA, ArgB]
        ;
            ( RelOp = relop_gt, ConstraintName = "float_lt_reif"
            ; RelOp = relop_ge, ConstraintName = "float_le_reif"
            ),
            Args = [ArgB, ArgA]
        ),
        MaybeSolved = no
    else
        flatten_float_expr(A + -1.0 * B, Coeffs0, Vars0, Const0),
        (
            Coeffs0 = [],
            % The expression reduces to a constant.
            ConstraintName = "dummy",
            Args = [],
            MaybeSolved = yes( if RelP(0.0, -Const0) then yes else no )
        ;
            Coeffs0 = [_ | _],
            Vars = list_to_array_expr(
                list.map(func(Var) = float_var(Var), Vars0)
            ),
            (
                ( RelOp = relop_eq, ConstraintName = "float_lin_eq_reif"
                ; RelOp = relop_ne, ConstraintName = "float_lin_ne_reif"
                ; RelOp = relop_lt, ConstraintName = "float_lin_lt_reif"
                ; RelOp = relop_le, ConstraintName = "float_lin_le_reif"
                ),
                Coeffs = list_to_array_expr(
                    list.map(func(Coeff) = float_const(Coeff), Coeffs0)
                ),
                Const = float_const(-Const0)
            ;
                ( RelOp = relop_gt, ConstraintName = "float_lin_lt_reif"
                ; RelOp = relop_ge, ConstraintName = "float_lin_le_reif"
                ),
                Coeffs = list_to_array_expr(
                    list.map(func(Coeff) = float_const(-Coeff), Coeffs0)
                ),
                Const = float_const(Const0)
            ),
            Args = [float_array_to_mzn_expr(Coeffs),
                float_array_to_mzn_expr(Vars), float_to_mzn_expr(Const)],
            MaybeSolved = no
        )
    ).

%-----------------------------------------------------------------------------%

refine_float_bounds(Context, Bounds, A, !Env) :-
    ( if
        A = float_var(var_no_index(V)),
        !.Env ^ reifying = not_reifying
    then
        do_refine_float_bounds(Context, Bounds, V, !Env)
    else
        true
    ).

do_refine_float_bounds(Context, Bounds, V, !Env) :-
    (
        Bounds = float_range_unbounded
    ;
        Bounds = float_range_lb_ub(LB, UB),
        !Env ^ var_float_lb(V) := float.max(LB, !.Env ^ var_float_lb(V)),
        !Env ^ var_float_ub(V) := float.min(UB, !.Env ^ var_float_ub(V))
    ;
        Bounds = float_range_set(_),
        minizinc_user_error(Context,
            "set membership is not supported for float variables.\n")
    ).

refine_float_lb(LB, A, !Env) :-
    ( if
        A = float_var(var_no_index(V)),
        !.Env ^ reifying = not_reifying
    then
        do_refine_float_lb(LB, V, !Env)
    else
        true
    ).

do_refine_float_lb(LB, V, !Env) :-
    !Env ^ var_float_lb(V) := float.max(LB, !.Env ^ var_float_lb(V)).

refine_float_ub(UB, A, !Env) :-
    ( if
        A = float_var(var_no_index(V)),
        !.Env ^ reifying = not_reifying
    then
        do_refine_float_ub(UB, V, !Env)
    else
        true
    ).

do_refine_float_ub(UB, V, !Env) :-
    !Env ^ var_float_ub(V) := float.min(UB, !.Env ^ var_float_ub(V)).

%-----------------------------------------------------------------------------%
:- end_module flatten.float.
%-----------------------------------------------------------------------------%
