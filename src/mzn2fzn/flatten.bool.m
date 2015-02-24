%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2009,2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Ralph Becket <rafe@csse.unimelb.edu.au>
%
% We divide up the cases for flattening built-in operators by type and by
% call inst (e.g., par par/par var/var par/var var/var).
%
%-----------------------------------------------------------------------------%

:- module flatten.bool.
:- interface.

:- import_module errors.
:- import_module flatten.env.
:- import_module mzn_ops.
:- import_module types.

%-----------------------------------------------------------------------------%

:- pred flatten_bool_to_int_semidet(error_context::in, mzn_anns::in,
    bool_to_int_op::in, bool_expr::in,
    int_expr::out, env::in, env::out) is semidet.

:- pred flatten_bool_to_int(error_context::in, mzn_anns::in,
    bool_to_int_op::in, bool_expr::in,
    int_expr::out, env::in, env::out) is det.

:- pred flatten_bool_to_bool(error_context::in, mzn_anns::in,
    bool_to_bool_op::in, bool_expr::in,
    bool_expr::out, env::in, env::out) is semidet.

:- pred flatten_bool_bool_to_bool(error_context::in, mzn_anns::in,
    bool_bool_to_bool_op::in, bool_expr::in, bool_expr::in,
    bool_expr::out, env::in, env::out) is semidet.

:- pred flatten_bool_array_to_bool(error_context::in, mzn_anns::in,
    bool_array_to_bool_op::in, bool_array_expr::in,
    bool_expr::out, env::in, env::out) is semidet.

:- pred conjoin(error_context::in, bool_expr::in, bool_expr::in,
    bool_expr::out, env::in, env::out) is det.

:- pred disjoin(error_context::in, bool_expr::in, bool_expr::in,
    bool_expr::out, env::in, env::out) is det.

    % Simplify a bool_expr to a bool_const or a bool_var. This may involve
    % adding new constraints.
    %
:- pred simplify_bool(error_context::in, bool_expr::in,
    bool_expr::out, env::in, env::out) is det.
:- pred simplify_bool_cv(error_context::in, bool_expr::in,
    bool_const_or_var::out, env::in, env::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module common_array.
:- import_module flatten.array.

:- import_module array.
:- import_module bool.
:- import_module int.
:- import_module list.
:- import_module set.
:- import_module string.
:- import_module unit.

%-----------------------------------------------------------------------------%

flatten_bool_to_int_semidet(Context, Anns, Op, A, Z, !Env) :-
    ( if semidet_succeed then
        flatten_bool_to_int(Context, Anns, Op, A, Z, !Env)
    else
        fail
    ).

flatten_bool_to_int(Context, Anns, Op, A, Z, !Env) :-
    % XXX should return int_const_or_var
    (
        Op = b2i_bool2int,
        ( if A = bool_const(BoolA) then
            ( BoolA = no,    Z = int_const(0)
            ; BoolA = yes,   Z = int_const(1)
            )
          else
            simplify_bool(Context, A, SimpleA, !Env),
            Bounds = int_range_lb_ub(0, 1),
            add_tmp_int_var(Context, Bounds, "bool2int",
                [bool_to_mzn_expr(SimpleA)], Anns, _VarId, Z, !Env)
        )
    ).

%-----------------------------------------------------------------------------%

flatten_bool_to_bool(Context, Anns, Op, A, Z, !Env) :-
    ( if A = bool_const(BA) then
        (
            Op = b2b_lb,
            Z = A
        ;
            Op = b2b_ub,
            Z = A
        ;
            Op = b2b_not,
            Z = bool_const(bool.not(BA))
        )
    else
        (
            Op = b2b_lb,
            Z = bool_const(no)
        ;
            Op = b2b_ub,
            Z = bool_const(yes)
        ;
            Op = b2b_not,
            flatten_bool_bool_to_bool(Context, Anns,
                bb2b_eq, A, bool_const(no), Z, !Env)
        )
    ).

%-----------------------------------------------------------------------------%

flatten_bool_bool_to_bool(Context, Anns, Op, A, B, Z, !Env) :-
    ( if A = bool_const(BoolA), B = bool_const(BoolB) then
        flatten_par_bool_par_bool_to_bool(Op, BoolA, BoolB, BoolZ),
        Z = bool_const(BoolZ)
    else if A = bool_const(BoolA) then
        flatten_par_bool_var_bool_to_bool(Context, Anns, Op, BoolA, B, Z, !Env)
    else if B = bool_const(BoolB) then
        flatten_var_bool_par_bool_to_bool(Context, Anns, Op, A, BoolB, Z, !Env)
    else
        flatten_var_bool_var_bool_to_bool(Context, Anns, Op, A, B, Z, !Env)
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_par_bool_par_bool_to_bool(bool_bool_to_bool_op::in,
    bool::in, bool::in, bool::out) is det.

flatten_par_bool_par_bool_to_bool(Op, BoolA, BoolB, BoolZ) :-
    ( Op = bb2b_and,    BoolZ = bool.and(BoolA, BoolB)
    ; Op = bb2b_or,     BoolZ = bool.or(BoolA, BoolB)
    ; Op = bb2b_xor,    BoolZ = bool.xor(BoolA, BoolB)
    ; Op = bb2b_imp2r,  BoolZ = bool.or(bool.not(BoolA), BoolB)
    ; Op = bb2b_imp2l,  BoolZ = bool.or(bool.not(BoolB), BoolA)
    ; Op = bb2b_biimp,  BoolZ = bool.not(bool.xor(BoolA, BoolB))
    ; Op = bb2b_min,    BoolZ = bool.and(BoolA, BoolB)
    ; Op = bb2b_max,    BoolZ = bool.or(BoolA, BoolB)
    ; Op = bb2b_eq, BoolZ = ( if BoolA = BoolB then yes else no )
    ; Op = bb2b_ee, BoolZ = ( if BoolA = BoolB then yes else no )
    ; Op = bb2b_ne, BoolZ = ( if BoolA \= BoolB then yes else no )
    ; Op = bb2b_lt, BoolZ = ( if BoolA = no, BoolB = yes then yes else no )
    ; Op = bb2b_le, BoolZ = ( if ( BoolA = no ; BoolB = yes ) then yes else no )
    ; Op = bb2b_gt, BoolZ = ( if BoolA = yes, BoolB = no then yes else no )
    ; Op = bb2b_ge, BoolZ = ( if ( BoolA = yes ; BoolB = no ) then yes else no )
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_par_bool_var_bool_to_bool(error_context::in, mzn_anns::in,
    bool_bool_to_bool_op::in, bool::in, bool_expr::in, bool_expr::out,
    env::in, env::out) is semidet.

flatten_par_bool_var_bool_to_bool(Context, Anns, Op, BoolA, B, Z, !Env) :-
    (
        Op = bb2b_and,
        ( BoolA = no,    Z = bool_const(no)
        ; BoolA = yes,   flatten_var_bool_eq_true(Context, Anns, B, Z, !Env)
        )
    ;
        Op = bb2b_or,
        ( BoolA = no,    flatten_var_bool_eq_true(Context, Anns, B, Z, !Env)
        ; BoolA = yes,   Z = bool_const(yes)
        )
    ;
        Op = bb2b_xor,
        ( BoolA = no,    flatten_var_bool_eq_true(Context, Anns, B, Z, !Env)
        ; BoolA = yes,   flatten_var_bool_eq_false(Context, Anns, B, Z, !Env)
        )
    ;
        Op = bb2b_imp2r,
        ( BoolA = no,    Z = bool_const(yes)
        ; BoolA = yes,   flatten_var_bool_eq_true(Context, Anns, B, Z, !Env)
        )
    ;
        Op = bb2b_imp2l,
        ( BoolA = no,    flatten_var_bool_eq_false(Context, Anns, B, Z, !Env)
        ; BoolA = yes,   Z = bool_const(yes)
        )
    ;
        Op = bb2b_biimp,
        ( BoolA = no,    flatten_var_bool_eq_false(Context, Anns, B, Z, !Env)
        ; BoolA = yes,   flatten_var_bool_eq_true(Context, Anns, B, Z, !Env)
        )
    ;
        Op = bb2b_min,
        ( BoolA = no,    Z = bool_const(no)
        ; BoolA = yes,   flatten_var_bool_eq_true(Context, Anns, B, Z, !Env)
        )
    ;
        Op = bb2b_max,
        ( BoolA = no,    flatten_var_bool_eq_true(Context, Anns, B, Z, !Env)
        ; BoolA = yes,   Z = bool_const(yes)
        )
    ;
        ( Op = bb2b_eq
        ; Op = bb2b_ee
        ),
        ( BoolA = no,    flatten_var_bool_eq_false(Context, Anns, B, Z, !Env)
        ; BoolA = yes,   flatten_var_bool_eq_true(Context, Anns, B, Z, !Env)
        )
    ;
        Op = bb2b_ne,
        ( BoolA = no,    flatten_var_bool_eq_true(Context, Anns, B, Z, !Env)
        ; BoolA = yes,   flatten_var_bool_eq_false(Context, Anns, B, Z, !Env)
        )
    ;
        Op = bb2b_lt,
        ( BoolA = no,    flatten_var_bool_eq_true(Context, Anns, B, Z, !Env)
        ; BoolA = yes,   Z = bool_const(no)
        )
    ;
        Op = bb2b_le,
        ( BoolA = no,    Z = bool_const(yes)
        ; BoolA = yes,   flatten_var_bool_eq_true(Context, Anns, B, Z, !Env)
        )
    ;
        Op = bb2b_gt,
        ( BoolA = no,    Z = bool_const(no)
        ; BoolA = yes,   flatten_var_bool_eq_false(Context, Anns, B, Z, !Env)
        )
    ;
        Op = bb2b_ge,
        ( BoolA = no,    flatten_var_bool_eq_false(Context, Anns, B, Z, !Env)
        ; BoolA = yes,   Z = bool_const(yes)
        )
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_var_bool_par_bool_to_bool(error_context::in, mzn_anns::in,
    bool_bool_to_bool_op::in, bool_expr::in, bool::in, bool_expr::out,
    env::in, env::out) is semidet.

flatten_var_bool_par_bool_to_bool(Context, Anns, Op, A, BoolB, Z, !Env) :-
    (
        ( Op = bb2b_and
        ; Op = bb2b_or
        ; Op = bb2b_xor
        ; Op = bb2b_biimp
        ; Op = bb2b_min
        ; Op = bb2b_max
        ; Op = bb2b_eq
        ; Op = bb2b_ee
        ; Op = bb2b_ne
        ),
        flatten_par_bool_var_bool_to_bool(Context, Anns, Op, BoolB, A, Z, !Env)
    ;
        ( Op = bb2b_imp2l,  RevOp = bb2b_imp2r
        ; Op = bb2b_imp2r,  RevOp = bb2b_imp2l
        ; Op = bb2b_lt,     RevOp = bb2b_gt
        ; Op = bb2b_le,     RevOp = bb2b_ge
        ; Op = bb2b_gt,     RevOp = bb2b_lt
        ; Op = bb2b_ge,     RevOp = bb2b_le
        ),
        flatten_par_bool_var_bool_to_bool(Context, Anns, RevOp, BoolB, A, Z,
            !Env)
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_var_bool_var_bool_to_bool(error_context::in, mzn_anns::in,
    bool_bool_to_bool_op::in, bool_expr::in, bool_expr::in,
    bool_expr::out, env::in, env::out) is semidet.

flatten_var_bool_var_bool_to_bool(Context, Anns, Op, A, B, Z, !Env) :-
    (
        ( Op = bb2b_and
        ; Op = bb2b_min
        ),
        Reifying = !.Env ^ reifying,
        (
            Reifying = not_reifying,
            flatten_var_bool_eq_true(Context, Anns, A, _, !Env),
            flatten_var_bool_eq_true(Context, Anns, B, _, !Env),
            Z = bool_const(yes)
        ;
            Reifying = reifying(_ : bool_exprs),
            conjoin(Context, A, B, Z, !Env)
        )
    ;
        ( Op = bb2b_or
        ; Op = bb2b_max
        ),
        disjoin(Context, A, B, Z, !Env)
    ;
        ( Op = bb2b_gt,     RevOp = bb2b_lt
        ; Op = bb2b_ge,     RevOp = bb2b_le
        ; Op = bb2b_imp2l,  RevOp = bb2b_imp2r
        ),
        flatten_var_bool_var_bool_to_bool(Context, Anns, RevOp, B, A, Z, !Env)
    ;
        Op = bb2b_lt,
        flatten_var_bool_eq_false(Context, Anns, A, ZA, !Env),
        flatten_var_bool_eq_true(Context, Anns, B, ZB, !Env),
        flatten_bool_bool_to_bool(Context, Anns, bb2b_and, ZA, ZB, Z, !Env)
    ;
        ( Op = bb2b_eq,     ConstraintName = "bool_eq"
        ; Op = bb2b_ee,     ConstraintName = "bool_eq"
        ; Op = bb2b_ne,     ConstraintName = "bool_not"
        ; Op = bb2b_xor,    ConstraintName = "bool_not"
        ; Op = bb2b_le,     ConstraintName = "bool_le"
        ; Op = bb2b_imp2r,  ConstraintName = "bool_le"
        ; Op = bb2b_biimp,  ConstraintName = "bool_eq"
        ),
        simplify_bool(Context, A, SimpleA, !Env),
        simplify_bool(Context, B, SimpleB, !Env),
        Reifying = !.Env ^ reifying,
        (
            Reifying = not_reifying,
            ( if ConstraintName = "bool_eq" then
                ( if
                    ( SimpleA = SimpleB
                    ; A = SimpleB
                    ; B = SimpleA
                    )
                then
                    true
                else if
                    SimpleA = bool_var(var_no_index(VarId)),
                    !.Env ^ var_value(VarId) \= _
                then
                    !Env ^ var_value(VarId) := bool_to_mzn_expr(SimpleB)
                else if
                    SimpleB = bool_var(var_no_index(VarId)),
                    !.Env ^ var_value(VarId) \= _
                then
                    !Env ^ var_value(VarId) := bool_to_mzn_expr(SimpleA)
                else
                    add_constraint(Context, ConstraintName,
                        [bool_to_mzn_expr(SimpleA), bool_to_mzn_expr(SimpleB)],
                        Anns, !Env)
                )
            else
                add_constraint(Context, ConstraintName,
                    [bool_to_mzn_expr(SimpleA), bool_to_mzn_expr(SimpleB)],
                    Anns, !Env)
            ),
            Z = bool_const(yes)
        ;
            Reifying = reifying(_ : bool_exprs),
            ( if ConstraintName = "bool_not" then
                ReifConstraintName = "bool_xor"
            else
                ReifConstraintName = ConstraintName ++ "_reif"
            ),
            add_tmp_bool_var(Context, unit, ReifConstraintName,
                [bool_to_mzn_expr(SimpleA), bool_to_mzn_expr(SimpleB)],
                Anns, _VarId, Z, !Env)
        )
    ).

%-----------------------------------------------------------------------------%

flatten_bool_array_to_bool(Context, Anns, Op, A0, Z, !Env) :-
    % XXX should return bool_const_or_var
    (
        Op = ba2b_exists,
        A = fully_deref_bool_array(Context, A0, !.Env),
        (
            A = array_items(_IndexRanges, ItemsA),
            array.foldl2(disjoin(Context), ItemsA, bool_const(no), Z, !Env)
        ;
            A = array_var(_IndexRanges, _VarId),
            Reifying = !.Env ^ reifying,
            (
                Reifying = not_reifying,
                add_constraint(Context, "array_bool_or",
                    [bool_array_to_mzn_expr(A),
                     bool_to_mzn_expr(bool_const(yes))],
                    Anns, !Env),
                Z = bool_const(yes)
            ;
                Reifying = reifying(_ : bool_exprs),
                add_tmp_bool_var(Context, unit, "array_bool_or",
                    [bool_array_to_mzn_expr(A0)],
                    Anns, _VarIdZ, Z, !Env)
            )
        )
    ;
        Op = ba2b_forall,
        A = fully_deref_bool_array(Context, A0, !.Env),
        Reifying = !.Env ^ reifying,
        (
            A = array_items(_IndexRanges, ItemsA),
            (
                Reifying = not_reifying,
                array.map_foldl(flatten_var_bool_eq_true(Context, Anns),
                    ItemsA, _, !Env),
                Z = bool_const(yes)
            ;
                Reifying = reifying(_ : bool_exprs),
                array.foldl2(
                    flatten_bool_bool_to_bool(Context, Anns, bb2b_and),
                    ItemsA, bool_const(yes), Z, !Env)
            )
        ;
            A = array_var(_IndexRanges, _VarId),
            (
                Reifying = not_reifying,
                add_constraint(Context, "array_bool_and",
                    [bool_array_to_mzn_expr(A),
                     bool_to_mzn_expr(bool_const(yes))],
                    Anns, !Env),
                Z = bool_const(yes)
            ;
                Reifying = reifying(_ : bool_exprs),
                add_tmp_bool_var(Context, unit, "array_bool_and",
                    [bool_array_to_mzn_expr(A0)],
                    Anns, _VarIdZ, Z, !Env)
            )
        )
    ;
        (
            Op = ba2b_xorall,
            XorSeed = no
        ;
            Op = ba2b_iffall,
            XorSeed = yes
        ),
        simplify_array_xor(Context, XorSeed, XorResult, A0, A, !Env),
        N = array_size(A),
        ( if N = 0 then
            Z = bool_const(XorResult)
        else if N = 1 then
            (
                A = array_items(_IndexRanges, ItemsA),
                Z0 = lookup(ItemsA, 0)
            ;
                A = array_var(_IndexRanges, VarIdA),
                Z0 = bool_var(var_index(VarIdA, 1))
            ),
            flatten_bool_bool_to_bool(Context, Anns, bb2b_eq,
                Z0, bool_const(not(XorResult)), Z, !Env)
        else
            Reifying = !.Env ^ reifying,
            (
                Reifying = not_reifying,
                Z = bool_const(yes),
                (
                    XorResult = no,
                    FzArray = A
                ;
                    XorResult = yes,
                    array_prepend_value(Context, Anns, Z, A, FzArray, !Env)
                )
            ;
                Reifying = reifying(_ : bool_exprs),
                make_tmp_bool_var(Context, unit, no_anns,
                    _VarIdZ, Z, !Env),
                (
                    XorResult = no,
                    add_tmp_bool_var(Context, unit, "bool_not",
                        [bool_to_mzn_expr(Z)], Anns, _VarIdNotZ, NotZ, !Env),
                    ExtraElem = NotZ
                ;
                    XorResult = yes,
                    ExtraElem = Z
                ),
                array_prepend_value(Context, Anns, ExtraElem, A, FzArray, !Env)
            ),
            add_constraint(Context, "array_bool_xor",
                [bool_array_to_mzn_expr(FzArray)],
                Anns, !Env)
        )
    ).

%-----------------------------------------------------------------------------%

:- pred array_prepend_value(error_context::in, mzn_anns::in,
    bool_expr::in, bool_array_expr::in, bool_array_expr::out,
    env::in, env::out) is semidet.

array_prepend_value(Context, Anns, A0, B, Z, !Env) :-
    A = array_items([index_range(1, 2)], array.init(1, A0)),
    flatten_array_array_to_array(
        % A and B are already dereferenced, so there's no need
        % for fully_deref_bool_array here
        (func(_Context, Array, _Env) = Array),
        (func(V) = bool_var(V) ),
        Context, Anns, "++", A, B, Z, !Env).

%-----------------------------------------------------------------------------%

    % XXX Should return array_expr(bool_const_or_var), but not until
    % flatten_bool_array_to_bool returns bool_const_or_var
:- pred simplify_array_xor(error_context::in, bool::in, bool::out,
    bool_array_expr::in, bool_array_expr::out, env::in, env::out) is det.

simplify_array_xor(Context, XorSeed, XorResult, A0, A, !Env) :-
    DerefA = fully_deref_bool_array(Context, A0, !.Env),
    (
        DerefA = array_var(_IndexRanges, _VarId),
        A = DerefA,
        XorResult = XorSeed
    ;
        DerefA = array_items(_IndexRanges, ItemsA),
        foldr2(xor_accum(Context), ItemsA, {XorSeed, 0, []},
            {XorResult, NVars, Vars}, !Env),
        A = array_items([index_range(1, NVars)], array(Vars))
    ).

    % XXX Should return list(bool_const_or_var), but not until
    % simplify_array_xor returns array_expr(bool_const_or_var)
:- pred xor_accum(error_context::in, bool_expr::in,
    {bool, int, bool_exprs}::in, {bool, int, bool_exprs}::out,
    env::in, env::out) is det.

xor_accum(Context, A, {!.XorAcc, !.NVars, !.Vars},
        {!:XorAcc, !:NVars, !:Vars}, !Env) :-
    simplify_bool_cv(Context, A, SimpleA, !Env),
    (
        SimpleA = boolcv_const(BoolA),
        !:XorAcc = !.XorAcc `xor` BoolA,
        !:NVars = !.NVars,
        !:Vars = !.Vars
    ;
        SimpleA = boolcv_var(VarA),
        !:XorAcc = !.XorAcc,
        !:NVars = !.NVars + 1,
        !:Vars = [ bool_var(VarA) | !.Vars ]
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_var_bool_eq_true(error_context::in, mzn_anns::in,
    bool_expr::in, bool_expr::out, env::in, env::out) is semidet.

flatten_var_bool_eq_true(Context, Anns, A, Z, !Env) :-
    Reifying = !.Env ^ reifying,
    (
        Reifying = not_reifying,
        ( if
            A = bool_const(yes)
        then
            Z = A
        else if
            A = bool_const(no)
        then
            model_inconsistency_detected(Context,
                "Model inconsistency detected.\n")
        else if
            A = bool_var(var_no_index(VarId)),
            !.Env ^ var_value(VarId) \= _
        then
            !Env ^ var_value(VarId) := bool_to_mzn_expr(bool_const(yes)),
            Z = bool_const(yes)
        else
            flatten_var_bool_var_bool_to_bool(Context, Anns,
                bb2b_eq, A, bool_const(yes), Z, !Env)
        )
    ;
        Reifying = reifying(_ : bool_exprs),
        Z = A
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_var_bool_eq_false(error_context::in, mzn_anns::in,
    bool_expr::in, bool_expr::out,
    env::in, env::out) is semidet.

flatten_var_bool_eq_false(Context, Anns, A, Z, !Env) :-
    Reifying = !.Env ^ reifying,
    (
        Reifying = not_reifying,
        ( if
            A = bool_const(no)
        then
            Z = A
        else if
            A = bool_const(yes)
        then
            model_inconsistency_detected(Context,
                "Model inconsistency detected.\n")
        else if
            A = bool_var(var_no_index(VarId)),
            !.Env ^ var_value(VarId) \= _
        then
            !Env ^ var_value(VarId) := bool_to_mzn_expr(bool_const(no)),
            Z = bool_const(yes)
        else
            flatten_var_bool_var_bool_to_bool(Context, Anns,
                bb2b_eq, A, bool_const(no), Z, !Env)
        )
    ;
        Reifying = reifying(_ : bool_exprs),
        flatten_var_bool_var_bool_to_bool(Context, Anns,
            bb2b_eq, A, bool_const(no), Z, !Env)
    ).

%-----------------------------------------------------------------------------%

conjoin(Context, A, B, Z, !Env) :-
    (
        A = bool_const(no),
        Z = A
    ;
        A = bool_const(yes),
        Z = B
    ;
        A = bool_var(_),
        (
            B = bool_const(no),
            Z = B
        ;
            B = bool_const(yes),
            Z = A
        ;
            B = bool_var(_),
            Z = bool_conj([A, B])
        ;
            B = bool_conj(ConjB),
            Z = bool_conj([A | ConjB])
        ;
            B = bool_disj(_),
            simplify_bool(Context, B, SimpleB, !Env),
            conjoin(Context, SimpleB, A, Z, !Env)
        )
    ;
        A = bool_conj(ConjA),
        (
            B = bool_const(no),
            Z = B
        ;
            B = bool_const(yes),
            Z = A
        ;
            B = bool_var(_),
            Z = bool_conj([B | ConjA])
        ;
            B = bool_conj(ConjB),
            Z = bool_conj(ConjA ++ ConjB)
        ;
            B = bool_disj(_),
            simplify_bool(Context, B, SimpleB, !Env),
            conjoin(Context, SimpleB, A, Z, !Env)
        )
    ;
        A = bool_disj(_),
        ( if B = bool_const(no) then
            Z = B
        else
            simplify_bool(Context, A, SimpleA, !Env),
            conjoin(Context, B, SimpleA, Z, !Env)
        )
    ).

%-----------------------------------------------------------------------------%

disjoin(Context, A, B, Z, !Env) :-
    (
        A = bool_const(no),
        Z = B
    ;
        A = bool_const(yes),
        Z = A
    ;
        A = bool_var(_),
        (
            B = bool_const(no),
            Z = A
        ;
            B = bool_const(yes),
            Z = B
        ;
            B = bool_var(_),
            Z = bool_disj([A, B])
        ;
            B = bool_conj(_),
            simplify_bool(Context, B, SimpleB, !Env),
            disjoin(Context, SimpleB, A, Z, !Env)
        ;
            B = bool_disj(DisjB),
            Z = bool_disj([A | DisjB])
        )
    ;
        A = bool_conj(_),
        ( if B = bool_const(yes) then
            Z = B
        else
            simplify_bool(Context, A, SimpleA, !Env),
            disjoin(Context, B, SimpleA, Z, !Env)
        )
    ;
        A = bool_disj(DisjA),
        (
            B = bool_const(no),
            Z = A
        ;
            B = bool_const(yes),
            Z = B
        ;
            B = bool_var(_),
            Z = bool_disj([B | DisjA])
        ;
            B = bool_conj(_),
            simplify_bool(Context, B, SimpleB, !Env),
            disjoin(Context, SimpleB, A, Z, !Env)
        ;
            B = bool_disj(DisjB),
            Z = bool_disj(DisjA ++ DisjB)
        )
    ).

%-----------------------------------------------------------------------------%

% XXX Inspect callers to see whether they would better call simplify_bool_cv.
simplify_bool(Context, A, SimpleA, !Env) :-
    simplify_bool_cv(Context, A, SimpleA_CV, !Env),
    (
        SimpleA_CV = boolcv_const(BoolConst),
        SimpleA = bool_const(BoolConst)
    ;
        SimpleA_CV = boolcv_var(BoolVar),
        SimpleA = bool_var(BoolVar)
    ).

simplify_bool_cv(Context, A, SimpleA, !Env) :-
    (
        A = bool_const(BoolConst),
        SimpleA = boolcv_const(BoolConst)
    ;
        A = bool_var(BoolVar),
        SimpleA = boolcv_var(BoolVar)
    ;
        A = bool_conj(ConjA),
        ArrayA = list_to_array_expr(ConjA),
        add_tmp_bool_var(Context, unit, "array_bool_and",
            [bool_array_to_mzn_expr(ArrayA)], no_anns, VarId, _, !Env),
        SimpleA = boolcv_var(var_no_index(VarId))
    ;
        A = bool_disj(DisjA),
        ArrayA = list_to_array_expr(DisjA),
        add_tmp_bool_var(Context, unit, "array_bool_or",
            [bool_array_to_mzn_expr(ArrayA)], no_anns, VarId, _, !Env),
        SimpleA = boolcv_var(var_no_index(VarId))
    ).

%-----------------------------------------------------------------------------%
:- end_module flatten.bool.
%-----------------------------------------------------------------------------%
