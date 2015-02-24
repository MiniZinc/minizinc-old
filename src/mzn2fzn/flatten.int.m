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
% For some more documentation of the overall approach used by this module,
% see the comment at the start of translate.int.m.
%
%-----------------------------------------------------------------------------%

:- module flatten.int.
:- interface.

:- import_module errors.
:- import_module flatten.env.
:- import_module mzn_ops.
:- import_module types.

%-----------------------------------------------------------------------------%
%
% These predicates assume their int_expr arguments have been simplified
% where possible.
%
% XXX The semidet predicates below should be det.
%

:- pred flatten_int_to_float_semidet(error_context::in, mzn_anns::in,
    int_to_float_op::in, int_expr::in,
    float_expr::out, env::in, env::out) is semidet.

:- pred flatten_int_to_float(error_context::in, mzn_anns::in,
    int_to_float_op::in, int_expr::in,
    float_expr::out, env::in, env::out) is det.

:- pred flatten_int_to_int(error_context::in, mzn_anns::in,
    int_to_int_op::in, int_expr::in,
    int_expr::out, env::in, env::out) is det.

:- pred flatten_int_to_int_set(error_context::in, mzn_anns::in,
    int_to_int_set_op::in, int_expr::in,
    int_set_expr::out, env::in, env::out) is det.

:- pred flatten_int_int_to_int(error_context::in, mzn_anns::in,
    int_int_to_int_op::in, int_expr::in, int_expr::in,
    int_expr::out, env::in, env::out) is semidet.

:- pred flatten_int_int_to_int_set(error_context::in, mzn_anns::in,
    int_int_to_int_set_op::in, int_expr::in, int_expr::in,
    int_set_expr::out, env::in, env::out) is det.

:- pred flatten_int_int_to_bool_or_inconsistent(error_context::in,
    string::in, mzn_anns::in,
    int_int_to_bool_op::in, int_expr::in, int_expr::in,
    bool_const_or_var::out, env::in, env::out) is det.

:- pred flatten_int_int_to_bool(error_context::in, mzn_anns::in,
    int_int_to_bool_op::in, int_expr::in, int_expr::in,
    bool_const_or_var::out, env::in, env::out) is semidet.

:- pred flatten_int_int_set_to_bool(error_context::in, mzn_anns::in,
    int_int_set_to_bool_op::in, int_expr::in, int_set_expr::in,
    bool_const_or_var::out, env::in, env::out) is semidet.

    % Convert an int_expr into a "simple" (i.e., FlatZinc) form (namely either
    % a constant or a variable).  This may require introducing a new temporary
    % variable if the int_expr is a linear sum.
    %
:- pred simplify_int(error_context::in, int_expr::in, int_expr::out,
    env::in, env::out) is det.

    % Refine bounds on an int variable.
    % These do nothing in a reifying context.
    % These do nothing if the int_expr is not a int_var(var_no_index(_)).
    %
:- pred refine_int_bounds(error_context::in, int_range::in, int_expr::in,
    env::in, env::out) is det.
:- pred do_refine_int_bounds(error_context::in, int_range::in, var_id::in,
    env::in, env::out) is det.

:- pred refine_int_lb(int::in, int_expr::in, env::in, env::out) is det.
:- pred do_refine_int_lb(int::in, var_id::in, env::in, env::out) is det.

:- pred refine_int_ub(int::in, int_expr::in, env::in, env::out) is det.
:- pred do_refine_int_ub(int::in, var_id::in, env::in, env::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module bounds.
:- import_module common_array.
:- import_module common_bounds.
:- import_module common_expr.

:- import_module intset.

:- import_module bool.
:- import_module float.
:- import_module int.
:- import_module list.
:- import_module maybe.
:- import_module set.
:- import_module unit.

%-----------------------------------------------------------------------------%

flatten_int_to_float_semidet(Context, Anns, i2f_int2float, A, Z, !Env) :-
    ( if semidet_succeed then
        % XXX infinite loop
        flatten_int_to_float_semidet(Context, Anns, i2f_int2float, A, Z, !Env)
    else
        fail
    ).

flatten_int_to_float(Context, Anns, i2f_int2float, A, Z, !Env) :-
    % XXX should return float_const_or_var
    ( if A = int_const(IntA) then
        Z = float_const(float(IntA))
    else
        simplify_int(Context, A, SimpleA, !Env),
        get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleA, LBA, UBA),
        ( if LBA = int_minus_infinity then
            LB = float_minus_infinity
        else
            LB = float(LBA)
        ),
        ( if UBA = int_plus_infinity then
            UB = float_plus_infinity
        else
            UB = float(UBA)
        ),
        Bounds = float_range_lb_ub(LB, UB),
        add_tmp_float_var(Context, Bounds, "int2float",
            [int_to_mzn_expr(SimpleA)], Anns, _VarId, Z, !Env)
    ).

%-----------------------------------------------------------------------------%

flatten_int_to_int(Context, Anns, Op, A, Z, !Env) :-
    ( if
        A = int_const(IntA)
    then
        flatten_par_int_to_int(Op, IntA, IntZ),
        Z = int_const(IntZ)
    else
        flatten_var_int_to_int(Context, Anns, Op, A, Z, !Env)
    ).

:- pred flatten_par_int_to_int(int_to_int_op::in, int::in, int::out) is det.

flatten_par_int_to_int(i2i_add,      IntA, IntA).
flatten_par_int_to_int(i2i_sub,      IntA, -IntA).
flatten_par_int_to_int(i2i_abs,      IntA, int.abs(IntA)).
flatten_par_int_to_int(i2i_lb,       IntA, IntA).
flatten_par_int_to_int(i2i_ub,       IntA, IntA).
flatten_par_int_to_int(i2i_dom_size, _,    1).
flatten_par_int_to_int(i2i_fix,      IntA, IntA).

:- pred flatten_var_int_to_int(error_context::in, mzn_anns::in,
    int_to_int_op::in, int_expr::in, int_expr::out, env::in, env::out) is det.

flatten_var_int_to_int(Context, Anns, Op, A, Z, !Env) :-
    (
        Op = i2i_add,
        Z = A
    ;
        Op = i2i_sub,
        Z = -1 * A
    ;
        Op = i2i_abs,
        get_int_expr_lb_ub(Context, !.Env ^ env_globals, A, LBA, UBA),
        ( if LBA < 0, 0 < UBA then
            LB = 0,
            ( if ( LBA = int_minus_infinity ; UBA = int_plus_infinity ) then
                UB = int_plus_infinity
            else
                UB = max(-LBA, UBA)
            ),
            Bounds = int_range_lb_ub(LB, UB),
            simplify_int(Context, A, SimpleA, !Env),
            add_tmp_int_var(Context, Bounds, "int_abs",
                [int_to_mzn_expr(SimpleA)], Anns, _VarIdZ, Z, !Env)
        else if UBA =< 0 then
            flatten_var_int_to_int(Context, Anns, i2i_sub, A, Z, !Env)
        else
            Z = A
        )
    ;
        Op = i2i_lb,
        get_int_expr_lb_ub(Context, !.Env ^ env_globals, A, LBA, _UBA),
        ( if LBA = int_minus_infinity then
            minizinc_user_error(Context, "Cannot infer lower bound.\n")
        else
            Z = int_const(LBA)
        )
    ;
        Op = i2i_ub,
        get_int_expr_lb_ub(Context, !.Env ^ env_globals, A, _LBA, UBA),
        ( if UBA = int_plus_infinity then
            minizinc_user_error(Context, "Cannot infer upper bound.\n")
        else
            Z = int_const(UBA)
        )
    ;
        Op = i2i_dom_size,
        get_int_expr_lb_ub(Context, !.Env ^ env_globals, A, LBA, UBA),
        ( if ( UBA = int_plus_infinity ; LBA = int_minus_infinity ) then
            minizinc_user_error(Context, "Cannot infer domain size.\n")
        else
            DomSize0 = UBA - LBA + 1,
            DomSize = (if DomSize0 < 0 then 0 else DomSize0 ),
            Z = int_const(DomSize)
        )
    ;
        Op = i2i_fix,
        minizinc_internal_error(Context, $pred,
            "fix should have been handled elsewhere\n")
    ).

%-----------------------------------------------------------------------------%

flatten_int_to_int_set(Context, _Anns, i2is_dom, A, Z, !Env) :-
    get_int_expr_lb_ub(Context, !.Env ^ env_globals, A, LB, UB),
    % Try to avoid creating ridiculous sets.
    ( if LB + 999 < UB then
        minizinc_user_error(Context,
            "Domain size is too large to represent as a set.\n")
    else
        Z = set_items(set.sorted_list_to_set(LB..UB))
    ).

%-----------------------------------------------------------------------------%

flatten_int_int_to_int(Context, Anns, Op, A, B, Z, !Env) :-
    ( if
        A = int_const(IntA), B = int_const(IntB),
        flatten_par_int_par_int_to_int(Context, Op, IntA, IntB, IntZ)
    then
        Z = int_const(IntZ)
    else if
        A = int_const(IntA),
        flatten_par_int_var_int_to_int(Op, IntA, B, Z0)
    then
        Z = Z0
    else if
        B = int_const(IntB),
        flatten_var_int_par_int_to_int(Op, A, IntB, Z0)
    then
        Z = Z0
    else
        flatten_var_int_var_int_to_int(Context, Anns, Op, A, B, Z, !Env)
    ).

:- pred flatten_par_int_par_int_to_int(error_context::in,
    int_int_to_int_op::in, int::in, int::in, int::out) is semidet.

flatten_par_int_par_int_to_int(Context, Op, IntA, IntB, IntZ) :-
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

:- pred flatten_par_int_var_int_to_int(int_int_to_int_op::in,
    int::in, int_expr::in, int_expr::out) is semidet.

flatten_par_int_var_int_to_int(Op, IntA, B, Z) :-
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

:- pred flatten_var_int_par_int_to_int(int_int_to_int_op::in,
    int_expr::in, int::in, int_expr::out) is semidet.

flatten_var_int_par_int_to_int(Op, A, IntB, Z) :-
    % XXX most Ops are missing
    (
        Op = ii2i_mul,
        flatten_par_int_var_int_to_int(Op, IntB, A, Z)
    ).

:- pred flatten_var_int_var_int_to_int(error_context::in, mzn_anns::in,
    int_int_to_int_op::in, int_expr::in, int_expr::in,
    int_expr::out, env::in, env::out) is semidet.

flatten_var_int_var_int_to_int(Context, Anns, Op, A, B, Z, !Env) :-
    (
        Op = ii2i_add,
        Z = A + B
    ;
        Op = ii2i_sub,
        Z = A + -1 * B
    ;
        Op = ii2i_mul,
        simplify_int(Context, A, SimpleA, !Env),
        simplify_int(Context, B, SimpleB, !Env),
        get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleA, LBA, UBA),
        get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleB, LBB, UBB),
        int_times_bounds(Context, LBA, UBA, LBB, UBB, LB, UB),
        Bounds = int_range_lb_ub(LB, UB),
        add_tmp_int_var(Context, Bounds, "int_times",
            [int_to_mzn_expr(SimpleA), int_to_mzn_expr(SimpleB)],
            Anns, _VarIdZ, Z, !Env)
    ;
        Op = ii2i_min,
        simplify_int(Context, A, SimpleA, !Env),
        simplify_int(Context, B, SimpleB, !Env),
        get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleA, LBA, UBA),
        get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleB, LBB, UBB),
        int_min_bounds(LBA, UBA, LBB, UBB, LB, UB),
        Bounds = int_range_lb_ub(LB, UB),
        add_tmp_int_var(Context, Bounds, "int_min",
            [int_to_mzn_expr(SimpleA), int_to_mzn_expr(SimpleB)],
            Anns, _VarIdZ, Z, !Env)
    ;
        Op = ii2i_max,
        simplify_int(Context, A, SimpleA, !Env),
        simplify_int(Context, B, SimpleB, !Env),
        get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleA, LBA, UBA),
        get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleB, LBB, UBB),
        int_max_bounds(LBA, UBA, LBB, UBB, LB, UB),
        Bounds = int_range_lb_ub(LB, UB),
        add_tmp_int_var(Context, Bounds, "int_max",
            [int_to_mzn_expr(SimpleA), int_to_mzn_expr(SimpleB)],
            Anns, _VarIdZ, Z, !Env)
    ;
        Op = ii2i_div,
        simplify_int(Context, A, SimpleA, !Env),
        simplify_int(Context, B, SimpleB, !Env),
        Reifying = !.Env ^ reifying,
        (
            Reifying = not_reifying,
            ( if SimpleB = int_const(0) then
                minizinc_user_error(Context, "Division by zero.\n")
            else if SimpleB = int_const(1) then
                Z = SimpleA
            else if SimpleA = int_const(IntA), SimpleB = int_const(IntB) then
                Z = int_const(IntA / IntB)
            else if SimpleB = int_const(-1) then
                flatten_par_int_var_int_to_int(ii2i_mul, -1, SimpleA, Z)
            else
                get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleA,
                    LBA, UBA),
                get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleB,
                    LBB, UBB),
                int_div_bounds(LBA, UBA, LBB, UBB, LB, UB),
                Bounds = int_range_lb_ub(LB, UB),
                add_tmp_int_var(Context, Bounds, "int_div",
                    [int_to_mzn_expr(SimpleA), int_to_mzn_expr(SimpleB)],
                    Anns, _VarIdZ, Z, !Env)
            )
        ;
            Reifying = reifying(ReifVars),
            ( if SimpleB = int_const(0) then
                !Env ^ reifying := reifying([bool_const(no)]),
                Z = int_const(0)
            else if SimpleB = int_const(1) then
                Z = SimpleA
            else if SimpleA = int_const(IntA), SimpleB = int_const(IntB) then
                Z = int_const(IntA / IntB)
            else if SimpleB = int_const(-1) then
                flatten_par_int_var_int_to_int(ii2i_mul, -1, SimpleA, Z)
            else if
                get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleB,
                    LBB, UBB),
                ( 0 < LBB ; UBB < 0 )
            then
                % SimpleB cannot be zero.
                get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleA,
                    LBA, UBA),
                int_div_bounds(LBA, UBA, LBB, UBB, LB, UB),
                Bounds = int_range_lb_ub(LB, UB),
                add_tmp_int_var(Context, Bounds, "int_div",
                    [int_to_mzn_expr(SimpleA), int_to_mzn_expr(SimpleB)],
                    Anns, _VarIdZ, Z, !Env)
            else
                % The reified form of Z = SimpleA / SimpleB is
                % Z = SimpleA / B1 where
                %
                % R is the reification variable for this expression,
                % SimpleB \= 0  <->  R,
                % SimpleB = B1  <->  R
                %
                get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleB,
                    LBB, UBB),
                ( if LBB = 0, UBB = 0
                then BoundsB1 = int_range_unbounded
                else BoundsB1 = int_range_lb_ub(LBB, UBB)
                ),
                make_tmp_int_var(Context, BoundsB1, no_anns, _VB1, B1, !Env),
                EqP = ( pred(X::in, Y::in) is semidet :- X = Y ),
                make_int_int_constraint(relop_ne, EqP, cns_reif,
                    SimpleB, int_const(0), NE0, NE0Args, _EqMaybeSolved),
                add_tmp_bool_var(Context, unit, NE0, NE0Args, no_anns,
                    VarIdR, _ZR, !Env),
                R = bool_var(var_no_index(VarIdR)),
                NeqP = ( pred(X::in, Y::in) is semidet :- X \= Y ),
                make_int_int_constraint(relop_eq, NeqP, cns_reif, SimpleB, B1,
                    NEB, NEBArgs, _NeqMaybeSolved),
                add_constraint(Context, NEB, NEBArgs ++ [bool_to_mzn_expr(R)],
                    no_anns, !Env),
                get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleA,
                    LBA, UBA),
                get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleB,
                    NewLBB, NewUBB),
                int_div_bounds(LBA, UBA, NewLBB, NewUBB, LB, UB),
                ( if LB > UB 
                then BoundsZ = int_range_unbounded
                else BoundsZ = int_range_lb_ub(LB, UB)
                ),
                add_tmp_int_var(Context, BoundsZ, "int_div",
                    [int_to_mzn_expr(SimpleA), int_to_mzn_expr(B1)],
                    Anns, _VarIdZ, Z, !Env),
                !Env ^ reifying := reifying([R | ReifVars])
            )
        )
    ;
        Op = ii2i_mod,
        simplify_int(Context, A, SimpleA, !Env),
        simplify_int(Context, B, SimpleB, !Env),
        Reifying = !.Env ^ reifying,
        (
            Reifying = not_reifying,
            ( if SimpleB = int_const(0) then
                minizinc_user_error(Context, "Modulo reduction by zero.\n")
            else if SimpleA = int_const(0) then
                add_constraint(Context, "int_ne",
                    [int_to_mzn_expr(SimpleB), int_to_mzn_expr(int_const(0))],
                    no_anns, !Env),
                Z = SimpleA
            else if SimpleA = int_const(IntA), SimpleB = int_const(IntB) then
                Z = int_const(IntA rem IntB)
            else
                get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleA,
                    LBA, UBA),
                get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleB,
                    LBB, UBB),
                int_mod_bounds(Context, LBA, UBA, LBB, UBB, LB, UB),
                Bounds = int_range_lb_ub(LB, UB),
                add_tmp_int_var(Context, Bounds, "int_mod",
                    [int_to_mzn_expr(SimpleA), int_to_mzn_expr(SimpleB)],
                    Anns, _VarIdZ, Z, !Env)
            )
        ;
            Reifying = reifying(ReifVars),
            ( if SimpleB = int_const(0) then
                !Env ^ reifying := reifying([bool_const(no)]),
                Z = int_const(0)
            else if SimpleA = int_const(0) then
                Z = SimpleA,
                ( if
                    get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleB,
                        LBB, UBB),
                    ( 0 < LBB ; UBB < 0 )
                then
                    % SimpleB cannot be zero.
                    true
                else
                    % SimpleB must not be zero.
                    add_tmp_bool_var(Context, unit, "int_ne_reif",
                        [int_to_mzn_expr(SimpleB),
                            int_to_mzn_expr(int_const(0))],
                        no_anns, _VarIdR, R, !Env),
                    !Env ^ reifying := reifying([R | ReifVars])
                )
            else if
                SimpleA = int_const(IntA), SimpleB = int_const(IntB)
            then
                Z = int_const(IntA rem IntB)
            else if
                get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleB,
                    LBB, UBB),
                ( 0 < LBB ; UBB < 0 )
            then
                % SimpleB cannot be zero.
                get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleA,
                    LBA, UBA),
                int_mod_bounds(Context, LBA, UBA, LBB, UBB, LB, UB),
                BoundsZ = int_range_lb_ub(LB, UB),
                add_tmp_int_var(Context, BoundsZ, "int_mod",
                    [int_to_mzn_expr(SimpleA), int_to_mzn_expr(SimpleB)],
                    Anns, _VarIdZ, Z, !Env)
            else
                % The reified form of Z = SimpleA mod SimpleB is
                % Z = SimpleA mod B where
                %
                % R is the reification variable for this expression,
                % SimpleB \= 0  <->  R,
                % SimpleB = B   <->  R
                %
                get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleB,
                    LBB, UBB),
                ( if LBB = 0, UBB = 0
                then BoundsB1 = int_range_unbounded
                else BoundsB1 = int_range_lb_ub(LBB, UBB)
                ),
                make_tmp_int_var(Context, BoundsB1, no_anns, _VB1, B1, !Env),
                EqP = ( pred(X::in, Y::in) is semidet :- X = Y ),
                make_int_int_constraint(relop_ne, EqP, cns_reif,
                    SimpleB, int_const(0), NE0, NE0Args, _EqMaybeSolved),
                add_tmp_bool_var(Context, unit, NE0, NE0Args, no_anns,
                    _VarIdR, R, !Env),
                NeqP = ( pred(X::in, Y::in) is semidet :- X \= Y ),
                make_int_int_constraint(relop_eq, NeqP, cns_reif,
                    SimpleB, B1, NEB, NEBArgs, _NeqMaybeSolved),
                add_constraint(Context, NEB, NEBArgs ++ [bool_to_mzn_expr(R)],
                    no_anns, !Env),
                get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleA,
                    LBA, UBA),
                get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleB,
                    NewLBB, NewUBB),
                int_mod_bounds(Context, LBA, UBA, NewLBB, NewUBB, LB, UB),
                ( if LB > UB
                then BoundsZ = int_range_unbounded
                else BoundsZ = int_range_lb_ub(LB, UB)
                ),
                add_tmp_int_var(Context, BoundsZ, "int_mod",
                    [int_to_mzn_expr(SimpleA), int_to_mzn_expr(B1)],
                    Anns, _VarIdZ, Z, !Env),
                !Env ^ reifying := reifying([R | ReifVars])
            )
        )
    ).

%-----------------------------------------------------------------------------%

flatten_int_int_to_int_set(Context, _Anns, ii2is_range, A, B, Z, !Env) :-
    ( if A = int_const(IntA), B = int_const(IntB) then
        % XXX The following code used to be:
        %
        %     Z = set_items(set.from_sorted_list(IntA..IntB))
        %
        % For large ranges this caused stack overflows, since
        % from_sorted_list/1 tries to remove duplicates from its argument.
        % The annoying thing is that there won't be any duplicates since
        % the argument is an integer range.
        %
        % Ideally, we should use something like the common library's ranges/0
        % type to represent integer sets here, but that's quite a big change.
        %
        % Instead we use the following horrible workaround.
        Range = IntA..IntB,
        Set = evil_list_to_set(Range),
        Z = set_items(Set)
      else
        minizinc_user_error(Context, "Arguments to '..' are not constant.\n")
    ).

    % XXX Don't try this at home kids!
    %
:- func evil_list_to_set(list(int)) = set(int).
:- pragma foreign_proc("C",
    evil_list_to_set(L::in) = (S::out),
    [will_not_call_mercury, promise_pure],
"
    S = L;
").

%-----------------------------------------------------------------------------%

flatten_int_int_to_bool_or_inconsistent(Context, ErrMsg, Anns,
        Op, A, B, Z, !Env) :-
    ( if flatten_int_int_to_bool(Context, Anns, Op, A, B, Z0, !Env) then
        Z = Z0
    else
        model_inconsistency_detected(Context, ErrMsg)
    ).

flatten_int_int_to_bool(Context, Anns, Op, A, B, Z, !Env) :-
%   A = deref_if_int_var_with_value(Context, A0, !.Env),
%   B = deref_if_int_var_with_value(Context, B0, !.Env),
    ( if
        ( Op = ii2b_ee, RevOp = ii2b_eq
        ; Op = ii2b_ge, RevOp = ii2b_le
        ; Op = ii2b_gt, RevOp = ii2b_lt
        )
    then
        flatten_int_int_to_bool(Context, Anns, RevOp, B, A, Z, !Env)
    else if
        A = int_const(IntA), B = int_const(IntB),
        flatten_par_int_par_int_to_bool(Op, IntA, IntB, BoolZ)
    then
        Z = boolcv_const(BoolZ)
    else if
        A = int_const(IntA),
        flatten_par_int_var_int_to_bool(Context, Anns, Op, IntA, B, Z0, !Env)
    then
        Z = Z0
    else if
        B = int_const(IntB),
        flatten_var_int_par_int_to_bool(Context, Anns, Op, A, IntB, Z0, !Env)
    then
        Z = Z0
    else
        flatten_var_int_var_int_to_bool(Context, Anns, Op, A, B, Z, !Env)
    ).

:- func deref_if_int_var_with_value(error_context, int_expr, env) = int_expr.

deref_if_int_var_with_value(Context, A0, Env) = A :-
    ( if
        A0 = int_var(var_no_index(VarId)),
        Env ^ var_value(VarId) = MZ
    then
        A = mzn_expr_to_int(Context, MZ)
    else
        A = A0
    ).

:- pred flatten_par_int_par_int_to_bool(int_int_to_bool_op::in,
    int::in, int::in, bool::out) is semidet.

flatten_par_int_par_int_to_bool(Op, IntA, IntB, BoolZ) :-
    ( Op = ii2b_eq, BoolZ = ( if IntA =  IntB then yes else no )
    ; Op = ii2b_ne, BoolZ = ( if IntA \= IntB then yes else no )
    ; Op = ii2b_le, BoolZ = ( if IntA =< IntB then yes else no )
    ; Op = ii2b_lt, BoolZ = ( if IntA <  IntB then yes else no )
    ; Op = ii2b_ge, BoolZ = ( if IntA >= IntB then yes else no )
    ; Op = ii2b_gt, BoolZ = ( if IntA >  IntB then yes else no )
    ).

:- pred flatten_par_int_var_int_to_bool(error_context::in, mzn_anns::in,
    int_int_to_bool_op::in, int::in, int_expr::in,
    bool_const_or_var::out, env::in, env::out) is semidet.

flatten_par_int_var_int_to_bool(Context, Anns, Op, IntA, B, CVZ, !Env) :-
    (
        Op = ii2b_lt,
        IntA < int_plus_infinity,
        flatten_par_int_var_int_to_bool(Context, Anns, ii2b_le, IntA + 1, B,
            CVZ, !Env)
    ;
        Op = ii2b_le,
        B = int_var(var_no_index(VarIdB)),
        ( if IntA =< !.Env ^ var_int_lb(VarIdB) then
            CVZ = boolcv_const(yes)
        else if !.Env ^ var_int_ub(VarIdB) < IntA then
            CVZ = boolcv_const(no)
        else
            Reifying = !.Env ^ reifying,
            (
                Reifying = not_reifying,
                !Env ^ var_int_lb(VarIdB) := IntA,
                CVZ = boolcv_const(yes)
            ;
                Reifying = reifying(_ : bool_exprs),
                add_tmp_bool_var(Context, unit, "int_le_reif",
                    [int_to_mzn_expr(int_const(IntA)), int_to_mzn_expr(B)],
                    Anns, VarIdZ, _Z, !Env),
                CVZ = boolcv_var(var_no_index(VarIdZ))
            )
        )
    ).

:- pred flatten_var_int_par_int_to_bool(error_context::in, mzn_anns::in,
    int_int_to_bool_op::in, int_expr::in, int::in,
    bool_const_or_var::out, env::in, env::out) is semidet.

flatten_var_int_par_int_to_bool(Context, Anns, Op, A, IntB, CVZ, !Env) :-
    (
        Op = ii2b_lt,
        int_minus_infinity < IntB,
        flatten_var_int_par_int_to_bool(Context, Anns, ii2b_le, A, IntB - 1,
            CVZ, !Env)
    ;
        Op = ii2b_le,
        A = int_var(var_no_index(VarIdA)),
        ( if !.Env ^ var_int_ub(VarIdA) =< IntB then
            CVZ = boolcv_const(yes)
        else if IntB < !.Env ^ var_int_lb(VarIdA) then
            CVZ = boolcv_const(no)
        else
            Reifying = !.Env ^ reifying,
            (
                Reifying = not_reifying,
                !Env ^ var_int_ub(VarIdA) := IntB,
                CVZ = boolcv_const(yes)
            ;
                Reifying = reifying(_ : bool_exprs),
                add_tmp_bool_var(Context, unit, "int_le_reif",
                    [int_to_mzn_expr(A), int_to_mzn_expr(int_const(IntB))],
                    Anns, VarIdZ, _Z, !Env),
                CVZ = boolcv_var(var_no_index(VarIdZ))
            )
        )
    ).

:- pred flatten_var_int_var_int_to_bool(error_context::in, mzn_anns::in,
    int_int_to_bool_op::in, int_expr::in, int_expr::in,
    bool_const_or_var::out, env::in, env::out) is semidet.

flatten_var_int_var_int_to_bool(Context, Anns, Op, A, B, CVZ, !Env) :-
    get_int_expr_lb_ub(Context, !.Env ^ env_globals, A, LBA, UBA),
    get_int_expr_lb_ub(Context, !.Env ^ env_globals, B, LBB, UBB),
    Reifying = !.Env ^ reifying,
    (
        Op = ii2b_eq,
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
                Bounds = int_range_lb_ub(int.max(LBA, LBB), int.min(UBA, UBB)),
                ( if
                    A = int_var(var_no_index(VarIdA)),
                    !.Env ^ var_value(VarIdA) \= _
                then
                    simplify_int(Context, B, SimpleB, !Env),
                    refine_int_bounds(Context, Bounds, A, !Env),
                    refine_int_bounds(Context, Bounds, SimpleB, !Env),
                    ( if A = SimpleB then
                        % Don't create self-assignments.
                        true
                      else
                        !Env ^ var_value(VarIdA) := int_to_mzn_expr(SimpleB)
                    ),
                    Ground = yes(yes)
                else if
                    B = int_var(var_no_index(VarIdB)),
                    !.Env ^ var_value(VarIdB) \= _
                then
                    simplify_int(Context, A, SimpleA, !Env),
                    refine_int_bounds(Context, Bounds, B, !Env),
                    refine_int_bounds(Context, Bounds, SimpleA, !Env),
                    ( if B = SimpleA then
                        % Don't create self-assignments.
                        true
                      else
                        !Env ^ var_value(VarIdB) := int_to_mzn_expr(SimpleA)
                    ),
                    Ground = yes(yes)
                else if
                    A = -1 * int_var(var_no_index(VarIdA)),
                    B = int_const(IntB),
                    !.Env ^ var_value(VarIdA) \= _
                then
                    RangeForA = int_range_lb_ub(-IntB, -IntB),
                    do_refine_int_bounds(Context, RangeForA, VarIdA, !Env),
                    !Env ^ var_value(VarIdA) :=
                        int_to_mzn_expr(int_const(-IntB)),
                    Ground = yes(yes)
                else if
                    A = int_const(IntA),
                    B = -1 * int_var(var_no_index(VarIdB)),
                    !.Env ^ var_value(VarIdB) \= _
                then
                    RangeForB = int_range_lb_ub(-IntA, -IntA),
                    do_refine_int_bounds(Context, RangeForB, VarIdB, !Env),
                    !Env ^ var_value(VarIdB) :=
                        int_to_mzn_expr(int_const(-IntA)),
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
        Op = ii2b_ne,
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
                Reifying = not_reifying,
                refine_int_ub(int_bounded_plus(Context, UBB, -1), A, !Env),
                refine_int_lb(int_bounded_plus(Context, LBA,  1), B, !Env)
            ;
                Reifying = reifying(_ : bool_exprs)
            )
        )
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
                Reifying = not_reifying,
                refine_int_ub(UBB, A, !Env),
                refine_int_lb(LBA, B, !Env)
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
            make_int_int_constraint(Rel, RelP, cns_none,
                A, B, ConstraintName, Args, MaybeSolved),
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
            make_int_int_constraint(Rel, RelP, cns_reif, A, B,
                ConstraintName, Args, MaybeSolved),
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

flatten_int_int_set_to_bool(Context, Anns, iis2b_in, A, B, CVZ, !Env) :-
    % If B is constant and A's domain is a subset of B then we return true.
    %
    % Otherwise, if A's domain is disjoint with B then we return false.
    %
    % Otherwise we have to post a set_in constraint.

    simplify_int(Context, A, SimpleA, !Env),
    get_int_set_expr_set_bound(!.Env ^ env_globals, B, SetB),
    (
        B = set_items(SetB),
        % B is a constant.
        ( if
            set.is_singleton(SetB, OnlyValueB)
        then
            ConstB = int_const(OnlyValueB),
            flatten_int_int_to_bool(Context, Anns, ii2b_eq, A, ConstB, CVZ,
                !Env)
        else if
            get_int_expr_lb_ub(Context, !.Env ^ env_globals, SimpleA,
                LBA, UBA),
            LBA \= int_minus_infinity,
            UBA \= int_plus_infinity,
            UBA - LBA < 1000
        then
            % A is bounded and not too large.
            SetA = set.from_sorted_list(LBA..UBA),
            ( if
                set.subset(SetA, SetB)
            then
                % A already is in B.
                CVZ = boolcv_const(yes)
            else if
                set.empty(set.intersect(SetA, SetB))
            then
                % A already is not in B.
                CVZ = boolcv_const(no)
            else
                % We have to post a "set_in" constraint.
                add_set_in_constraint(Context, Anns, SimpleA, B, CVZ, !Env)
            )
        else
            % A is not bounded.
            % We have to post a "set_in" constraint.
            add_set_in_constraint(Context, Anns, SimpleA, B, CVZ, !Env)
        )
    ;
        B = set_var(_),
        % B is not constant.
        % We have to post a "set_in" constraint.
        add_set_in_constraint(Context, Anns, SimpleA, B, CVZ, !Env)
    ).

%-----------------------------------------------------------------------------%

    % Precondition: A has been simplified.
    % Precondition: the domain of A is not disjoint with B.
    %
:- pred add_set_in_constraint(error_context::in, mzn_anns::in,
    int_expr::in, int_set_expr::in,
    bool_const_or_var::out, env::in, env::out) is det.

add_set_in_constraint(Context, Anns, A, B, CVZ, !Env) :-
    Reifying = !.Env ^ reifying,
    (
        Reifying = not_reifying,
        get_int_set_expr_lb_ub(!.Env ^ env_globals, B, MinB, MaxB),
        ( if
            A \= int_var(var_index(_, _)),
            B = set_items(_),
            int_set_expr_bound_is_contiguous(!.Env ^ env_globals, B) = yes
        then
            % A is not an array element and B is a contiguous constant, so we
            % can simply refine the bounds on A.
            refine_int_lb(MinB, A, !Env),
            refine_int_ub(MaxB, A, !Env),
            CVZ = boolcv_const(yes)
        else
            % B is a var or not contiguous, so we have to post a set_in
            % constraint.
            refine_int_lb(MinB, A, !Env),
            refine_int_ub(MaxB, A, !Env),
            add_constraint(Context, "set_in",
                [int_to_mzn_expr(A), int_set_to_mzn_expr(B)], Anns, !Env),
            CVZ = boolcv_const(yes)
        )
    ;
        Reifying = reifying(_ : bool_exprs),
        add_tmp_bool_var(Context, unit, "set_in_reif",
            [int_to_mzn_expr(A), int_set_to_mzn_expr(B)],
            Anns, VarIdZ, _Z, !Env),
        CVZ = boolcv_var(var_no_index(VarIdZ))
    ).

%-----------------------------------------------------------------------------%

simplify_int(Context, A, Z, !Env) :-
    ( if int_expr_is_simple(A) then
        Z = A
    else
        % This isn't a trivial expression.  We need to simplify it to
        % an addition or subtraction or linear sum.
        get_int_expr_lb_ub(Context, !.Env ^ env_globals, A, LB, UB),
        Bounds = int_range_lb_ub(LB, UB),
        flatten_int_expr(A, CoeffsA0, VarsA0, ConstA0),
        CoeffsA = list.map(func(C) = int_const(C), CoeffsA0),
        VarsA = list.map(func(V) = int_var(V), VarsA0),
        ConstA = int_const(-ConstA0),
        ( if CoeffsA0 = [] then
            Z = int_const(ConstA0)
        else if ConstA0 = 0, CoeffsA0 = [1], VarsA = [V1] then
            Z = V1
        else if ConstA0 = 0, CoeffsA0 = [1, 1], VarsA = [V1, V2] then
            add_tmp_int_var(Context, Bounds, "int_plus",
                [int_to_mzn_expr(V1), int_to_mzn_expr(V2)],
                no_anns, _VarIdZ, Z, !Env)
        else if ConstA0 = 0, CoeffsA0 = [1, -1], VarsA = [V1, V2] then
            % NOTE: there is no int_minus/3 builtin in FlatZinc, but we pretend
            % that there is in order to simplify CSE. When we output
            % int_minus/3 constraints we transform them into int_plus/3
            % constraints using the following identity:
            %
            %    int_minus(a, b, c) <=> int_plus(c, b, a)

            add_tmp_int_var(Context, Bounds, "int_minus",
                [int_to_mzn_expr(V1), int_to_mzn_expr(V2)],
                no_anns, _VarIdZ, Z, !Env)
        else
            MznCoeffsA = int_array_to_mzn_expr(list_to_array_expr(CoeffsA)),
            MznVarsA = int_array_to_mzn_expr(list_to_array_expr(VarsA)),
            MznConstA = int_to_mzn_expr(ConstA),
            PartialConstraint = mzn_constraint("int_lin_eq",
                [MznCoeffsA, MznVarsA, MznConstA], no_anns),
            ( if !.Env ^ cse_lookup(PartialConstraint) = Var then
                Z = int_var(var_no_index(Var))
            else
                make_tmp_int_var(Context, Bounds, just_is_defined_var,
                    VarIdZ, Z, !Env),
                add_cse_var(PartialConstraint, VarIdZ, !Env),
                MZ = int_to_mzn_expr(Z),
                add_constraint(Context, "int_lin_eq",
                    [ int_array_to_mzn_expr(
                        list_to_array_expr([int_const(-1) | CoeffsA])),
                      int_array_to_mzn_expr(
                        list_to_array_expr([Z             | VarsA  ])),
                      MznConstA
                    ],
                    just_defines_var(MZ), !Env
                )
            )
        )
    ).

%-----------------------------------------------------------------------------%

refine_int_bounds(Context, Bounds, A, !Env) :-
    ( if
        A = int_var(var_no_index(V)),
        !.Env ^ reifying = not_reifying
    then
        do_refine_int_bounds(Context, Bounds, V, !Env)
    else
        true
    ).

do_refine_int_bounds(Context, Bounds, V, !Env) :-
    (
        Bounds = int_range_unbounded
    ;
        Bounds = int_range_lb_ub(LB, UB),
        !Env ^ var_int_lb(V) := int.max(LB, !.Env ^ var_int_lb(V)),
        !Env ^ var_int_ub(V) := int.min(UB, !.Env ^ var_int_ub(V))
    ;
        Bounds = int_range_set(Set),
        ( if
            % JJJ FIXME - INTSET REP - simplify the rest of this condition.
            Xs = intset.to_sorted_list(Set),
            Xs = [LB | _],
            list.last(Xs, UB)
        then
            !Env ^ var_int_lb(V) := int.max(LB, !.Env ^ var_int_lb(V)),
            !Env ^ var_int_ub(V) := int.min(UB, !.Env ^ var_int_ub(V))
        else
            true
        ),
        % JJJ FIXME - INTSET REP - need a better rep for int_set exprs.
        SetPrime = set.from_sorted_list(intset.to_sorted_list(Set)),
        add_constraint(Context, "set_in",
            [int_to_mzn_expr(int_var(var_no_index(V))),
                int_set_to_mzn_expr(set_items(SetPrime))],
            no_anns, !Env)
    ).

refine_int_lb(LB, A, !Env) :-
    ( if
        A = int_var(var_no_index(V)),
        !.Env ^ reifying = not_reifying
    then
        do_refine_int_lb(LB, V, !Env)
    else
        true
    ).

do_refine_int_lb(LB, V, !Env) :-
    !Env ^ var_int_lb(V) := int.max(LB, !.Env ^ var_int_lb(V)).

refine_int_ub(UB, A, !Env) :-
    ( if
        A = int_var(var_no_index(V)),
        !.Env ^ reifying = not_reifying
    then
        do_refine_int_ub(UB, V, !Env)
    else
        true
    ).

do_refine_int_ub(UB, V, !Env) :-
    !Env ^ var_int_ub(V) := int.min(UB, !.Env ^ var_int_ub(V)).

%-----------------------------------------------------------------------------%
:- end_module flatten.int.
%-----------------------------------------------------------------------------%
