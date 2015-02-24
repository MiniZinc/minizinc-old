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

:- module flatten.set.
:- interface.

:- import_module errors.
:- import_module flatten.env.
:- import_module mzn_ops.
:- import_module types.

%-----------------------------------------------------------------------------%

:- pred flatten_set_to_int(error_context::in, mzn_anns::in,
    set_to_int_op::in, set_expr(T)::in,
    int_expr::out, env::in, env::out) is det.

:- pred flatten_set_set_to_set(error_context::in, mzn_anns::in,
    set_set_to_set_op::in, set_expr(T)::in, set_expr(T)::in,
    set_expr(T)::out, env::in, env::out) is semidet.

:- pred flatten_set_set_to_bool(error_context::in, mzn_anns::in,
    set_set_to_bool_op::in, set_expr(T)::in, set_expr(T)::in,
    bool_const_or_var::out, env::in, env::out) is semidet.

:- pred flatten_int_set_to_int_set(error_context::in, mzn_anns::in,
    int_set_to_int_set_op::in, int_set_expr::in,
    int_set_expr::out, env::in, env::out) is det.

:- pred flatten_int_set_to_int(error_context::in, mzn_anns::in,
    int_set_to_int_op::in, int_set_expr::in,
    int_expr::out, env::in, env::out) is semidet.

:- pred flatten_int_set_to_array(error_context::in, mzn_anns::in,
    set_to_array_op::in, int_set_expr::in,
    int_array_expr::out, env::in, env::out) is det.

:- pred refine_int_set_bounds(error_context::in, int_range::in,
    int_set_expr::in, env::in, env::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module common_bounds.
:- import_module flatten.int.

:- import_module intset.

:- import_module array.
:- import_module bool.
:- import_module int.
:- import_module list.
:- import_module set.
:- import_module string.
:- import_module unit.

%-----------------------------------------------------------------------------%

flatten_set_to_int(Context, Anns, Op, A, Z, !Env) :-
    % XXX should return int_const_or_var
    (
        Op = xs2i_card,
        (
            A = set_items(SA),
            Z = int_const(set.count(SA))
        ;
            A = set_var(MZVar),
            ( if dynamic_cast(A, IntSetA : int_set_expr) then
                ( MZVar = var_no_index(V)
                ; MZVar = var_index(V, _)
                ),
                BoundsA = !.Env ^ var_set_ub(V),
                (
                    BoundsA = int_range_lb_ub(LBA, UBA),
                    Bounds = int_range_lb_ub(0, 1 + UBA - LBA)
                ;
                    BoundsA = int_range_set(SetA),
                    Bounds = int_range_lb_ub(0, intset.size(SetA))
                ;
                    BoundsA = int_range_unbounded,
                    Bounds = int_range_unbounded
                ),
                add_tmp_int_var(Context, Bounds, "set_card",
                    [int_set_to_mzn_expr(IntSetA)], Anns, _VarIdZ, Z, !Env)
            else
                minizinc_user_error(Context,
                    "'card' only applies to variables with type set of int.\n")
            )
        )
    ).

%-----------------------------------------------------------------------------%

flatten_int_set_to_int(Context, _Anns, Op, A, Z, !Env) :-
    (
        Op = is2i_min,
        (
            A = set_items(Set),
            Xs = set.to_sorted_list(Set),
            (
                Xs = [],
                Reifying = !.Env ^ reifying,
                (
                    Reifying = not_reifying,
                    minizinc_user_error(Context,
                        "'min' cannot be applied to the empty set.\n")
                ;
                    Reifying = reifying(_ : bool_exprs),
                    Z = int_const(0),   % Dummy value.
                    !Env ^ reifying := reifying([bool_const(no)])
                )
            ;
                Xs = [Min | _],
                Z = int_const(Min)
            )
        ;
            A = set_var(_),
            minizinc_user_error(Context,
                "'min' cannot be applied to set variables.\n")
        )
    ;
        Op = is2i_max,
        (
            A = set_items(Set),
            Xs = set.to_sorted_list(Set),
            (
                Xs = [],
                Reifying = !.Env ^ reifying,
                (
                    Reifying = not_reifying,
                    minizinc_user_error(Context,
                        "'max' cannot be applied to the empty set.\n")
                ;
                    Reifying = reifying(_ : bool_exprs),
                    Z = int_const(0),   % Dummy value.
                    !Env ^ reifying := reifying([bool_const(no)])
                )
            ;
                Xs = [_ | _],
                list.last(Xs, Max),
                Z = int_const(Max)
            )
        ;
            A = set_var(_),
            minizinc_user_error(Context,
                "'max' cannot be applied to set variables.\n")
        )
    ).

%-----------------------------------------------------------------------------%

flatten_int_set_to_int_set(Context, _Anns, Op, A, Z, !Env) :-
    (
        Op = is2is_ub,
        (
            A = set_items(_),
            Z = A
        ;
            A = set_var(MZVar),
            ( MZVar = var_no_index(VarId)
            ; MZVar = var_index(VarId, _)
            ),
            Range = !.Env ^ var_set_ub(VarId),
            (
                Range = int_range_unbounded,
                LB = !.Env ^ var_int_lb(VarId),
                UB = !.Env ^ var_int_ub(VarId),
                ( if LB \= int_minus_infinity, UB \= int_plus_infinity then
                    Z = set_items(set.from_sorted_list(LB..UB))
                else
                    minizinc_user_error(Context,
                        "No upper bound specified for this set variable.\n")
                )
            ;
                Range = int_range_lb_ub(LB, UB),
                Z = set_items(set.from_sorted_list(LB..UB))
            ;
                Range = int_range_set(Set),
                % JJJ - INTSET REP.
                PrimeSet = set.from_sorted_list(intset.to_sorted_list(Set)),
                Z = set_items(PrimeSet)
            )
        )
    ).

%-----------------------------------------------------------------------------%

flatten_set_set_to_set(Context, Anns, Op, A, B, Z, !Env) :-
    ( if A = set_items(SetA), B = set_items(SetB) then
        flatten_par_set_par_set_to_set(Op, SetA, SetB, SetZ),
        Z = set_items(SetZ)
    else
        dynamic_cast(A, IntSetA),
        dynamic_cast(B, IntSetB),
        flatten_var_set_var_set_to_set(Context, Anns, Op, IntSetA, IntSetB,
            IntSetZ, !Env),
        dynamic_cast(IntSetZ, Z)
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_par_set_par_set_to_set(set_set_to_set_op::in,
    set(T)::in, set(T)::in, set(T)::out) is det.

flatten_par_set_par_set_to_set(Op, SetA, SetB, SetZ) :-
    ( Op = xsxs2xs_diff,      SetZ = set.difference(SetA, SetB)
    ; Op = xsxs2xs_intersect, SetZ = set.intersect(SetA, SetB)
    ; Op = xsxs2xs_union,     SetZ = set.union(SetA, SetB)
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_var_set_var_set_to_set(error_context::in, mzn_anns::in,
    set_set_to_set_op::in, set_expr(int)::in, set_expr(int)::in,
    set_expr(int)::out, env::in, env::out) is det.

flatten_var_set_var_set_to_set(Context, Anns, Op, A, B, Z, !Env) :-
    ( Op = xsxs2xs_diff,      ConstraintName = "set_diff"
    ; Op = xsxs2xs_intersect, ConstraintName = "set_intersect"
    ; Op = xsxs2xs_union,     ConstraintName = "set_union"
    ),
    get_int_set_expr_lb_ub(!.Env ^ env_globals, A, LBA, UBA),
    get_int_set_expr_lb_ub(!.Env ^ env_globals, B, LBB, UBB),
    (
        Op = xsxs2xs_diff,
        LB = LBA,
        UB = UBA
    ;
        Op = xsxs2xs_intersect,
        LB = int.max(LBA, LBB),
        UB = int.min(UBA, UBB)
    ;
        Op = xsxs2xs_union,
        LB = int.min(LBA, LBB),
        UB = int.max(UBA, UBB)
    ),
    ( if LB > UB then
        Z = set_items(set.init)
    else if Op = xsxs2xs_diff, LBB > UBB then
        Z = A
    else if Op = xsxs2xs_union, LBA > UBA then
        Z = B
    else if Op = xsxs2xs_union, LBB > UBB then
        Z = A
    else
        Bounds = int_range_lb_ub(LB, UB),
        add_tmp_int_set_var(Context, Bounds, ConstraintName,
            [int_set_to_mzn_expr(A), int_set_to_mzn_expr(B)],
            Anns, _VarIdZ, Z, !Env)
    ).

%-----------------------------------------------------------------------------%

flatten_set_set_to_bool(Context, Anns, Op, A, B, Z, !Env) :-
    ( if
        ( Op = xsxs2b_ee,       RevOp = xsxs2b_eq
        ; Op = xsxs2b_gt,       RevOp = xsxs2b_lt
        ; Op = xsxs2b_ge,       RevOp = xsxs2b_le
        ; Op = xsxs2b_superset, RevOp = xsxs2b_subset
        )
    then
        flatten_set_set_to_bool(Context, Anns, RevOp, B, A, Z, !Env)
    else if
        A = set_items(SA), B = set_items(SB)
    then
        flatten_par_set_par_set_to_bool(Op, SA, SB, BoolZ),
        Z = boolcv_const(BoolZ)
    else
        flatten_var_set_var_set_to_bool(Context, Anns, Op, A, B, Z, !Env)
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_par_set_par_set_to_bool(set_set_to_bool_op::in,
    set(T)::in, set(T)::in, bool::out) is semidet.

flatten_par_set_par_set_to_bool(Op, SA, SB, BoolZ) :-
    ( Op = xsxs2b_eq,     BoolZ = ( if SA = SB then yes else no )
    ; Op = xsxs2b_ne,     BoolZ = ( if SA \= SB then yes else no )
    ; Op = xsxs2b_lt,     BoolZ = ( if SA @< SB then yes else no )
    ; Op = xsxs2b_le,     BoolZ = ( if SA @=< SB then yes else no )
    ; Op = xsxs2b_subset, BoolZ = ( if set.subset(SA, SB) then yes else no )
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_var_set_var_set_to_bool(error_context::in, mzn_anns::in,
    set_set_to_bool_op::in, set_expr(T)::in, set_expr(T)::in,
    bool_const_or_var::out, env::in, env::out) is semidet.

flatten_var_set_var_set_to_bool(Context, Anns, Op, A0, B0, Z, !Env) :-
    ( if dynamic_cast(A0, A), dynamic_cast(B0, B) then
        Reifying = !.Env ^ reifying,
        ( if
            Op = xsxs2b_eq,
            A = set_var(MZVar),
            MZVar = var_no_index(VarId),
            !.Env ^ var_value(VarId) \= _,
            Reifying = not_reifying
        then
            ( if
                (
                    B = set_items(set.init)
                ;
                    get_int_set_expr_lb_ub(!.Env ^ env_globals, B, BMin, BMax),
                    AMin = !.Env ^ var_int_lb(VarId),
                    AMax = !.Env ^ var_int_ub(VarId),
                    AMin =< BMin,
                    BMax =< AMax
                )
            then
                % Avoid introducing a self-assignment.
                ( if A = B then
                    true
                else
                    !Env ^ var_value(VarId) := int_set_to_mzn_expr(B)
                ),
                Z = boolcv_const(yes)
            else
                Z = boolcv_const(no)
            )
        else if
            get_int_set_expr_lb_ub(!.Env ^ env_globals, A, Min, Max),
            Min > Max,
            ( Op = xsxs2b_lt
            ; Op = xsxs2b_le
            ; Op = xsxs2b_subset
            )
        then
            Z = boolcv_const(yes)
        else
            ( Op = xsxs2b_eq,     ConstraintName = "set_eq"
            ; Op = xsxs2b_ne,     ConstraintName = "set_ne"
            ; Op = xsxs2b_lt,     ConstraintName = "set_lt"
            ; Op = xsxs2b_le,     ConstraintName = "set_le"
            ; Op = xsxs2b_subset, ConstraintName = "set_subset"
            ),
            ( if
                ConstraintName = "set_subset",
                A = set_var(MZVar @ var_no_index(_))
            then
                % Refine the bounds on A.
                VarIdA = mzn_var_id(MZVar),
                C = int_var(var_no_index(VarIdA)),
                get_int_set_expr_lb_ub(!.Env ^ env_globals, B, Min, Max),
                refine_int_lb(Min, C, !Env),
                refine_int_ub(Max, C, !Env)
            else
                true
            ),
            (
                Reifying = not_reifying,
                add_constraint(Context, ConstraintName,
                    [int_set_to_mzn_expr(A), int_set_to_mzn_expr(B)],
                    Anns, !Env),
                Z = boolcv_const(yes)
            ;
                Reifying = reifying(_ : bool_exprs),
                ReifConstraintName = ConstraintName ++ "_reif",
                add_tmp_bool_var(Context, unit, ReifConstraintName,
                    [int_set_to_mzn_expr(A), int_set_to_mzn_expr(B)], Anns,
                    VarIdZ, _Z, !Env),
                Z = boolcv_var(var_no_index(VarIdZ))
            )
        )
    else
        is_set_set_to_bool_op(OpStr, Op),
        minizinc_user_error(Context,
            "'" ++ OpStr ++ "' is not defined on non-int set variables.\n")
    ).

%-----------------------------------------------------------------------------%

flatten_int_set_to_array(Context, _Anns, Op, A, Z, !Env) :-
    (
        Op = xs2xa_set2array,
        (
            A = set_var(_),
            minizinc_user_error(Context,
                "'set2array' is only applicable to fixed sets.\n")
        ;
            A = set_items(Set),
            F = ( func(I) = int_const(I) ),
            ArrayItems = array(list.map(F, set.to_sorted_list(Set))),
            N = array.size(ArrayItems),
            IndexRanges = [index_range(1, N)],
            Z = array_items(IndexRanges, ArrayItems)
        )
    ).

%-----------------------------------------------------------------------------%

refine_int_set_bounds(Context, Bounds, A, !Env) :-
    ( if
        !.Env ^ reifying = not_reifying,
        (
            Bounds = int_range_lb_ub(LB, UB),
            LB \= int_minus_infinity,
            UB \= int_plus_infinity,
            LB + 999 >= UB,
            % JJJ - INTSET, don't do LB..UB - it's really not a good idea.
            Set = set.from_sorted_list(LB..UB)
        ;
            Bounds = int_range_set(Set0),
            % JJJ FIXME - INTSET.
            Set = set.from_sorted_list(intset.to_sorted_list(Set0))
        )
    then
        ( if
            flatten_set_set_to_bool(Context, no_anns, xsxs2b_subset,
                A, set_items(Set), Z, !Env),
            Z = boolcv_const(yes)
        then
            true
        else
            arg_out_of_range(Context)
        )
    else
        true
    ).

%-----------------------------------------------------------------------------%
:- end_module flatten.set.
%-----------------------------------------------------------------------------%
