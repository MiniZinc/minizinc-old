%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2009 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
%
%-----------------------------------------------------------------------------%

:- module common_expr.
:- interface.

:- import_module types.

:- import_module bool.
:- import_module list.
:- import_module maybe.

%-----------------------------------------------------------------------------%

:- pred flatten_int_expr(int_expr::in,
    list(int)::out, list(mzn_var)::out, int::out) is det.

:- pred flatten_float_expr(float_expr::in,
    list(float)::out, list(mzn_var)::out, float::out) is det.

%-----------------------------------------------------------------------------%

:- pred make_int_int_constraint(mzn_relop::in,
    pred(int, int)::in(pred(in, in) is semidet),
    constraint_name_suffix_kind::in, int_expr::in, int_expr::in,
    string::out, list(mzn_expr)::out, maybe(bool)::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module common_array.

:- import_module float.
:- import_module int.
:- import_module map.
:- import_module string.

%-----------------------------------------------------------------------------%

flatten_int_expr(LinExpr, Coeffs, Vars, Const) :-
    Scale0 = 1,
    Map0 = map.init,
    Const0 = 0,
    build_int_expr_coeffs(LinExpr, Scale0, Map0, Map, Const0, Const),
    Coeffs = map.values(Map),
    Vars = map.keys(Map).

:- pred build_int_expr_coeffs(int_expr::in, int::in,
    map(mzn_var, int)::in, map(mzn_var, int)::out, int::in, int::out) is det.

build_int_expr_coeffs(Expr, Scale, !Map, !Const) :-
    (
        Expr = int_const(K),
        !:Const = !.Const + Scale * K
    ;
        Expr = int_var(VarId),
        ( if map.search(!.Map, VarId, Coeff0) then
            Coeff = Coeff0 + Scale,
            ( if Coeff = 0 then
                map.delete(VarId, !Map)
            else
                map.det_update(VarId, Coeff, !Map)
            )
        else
            map.det_insert(VarId, Scale, !Map)
        )
    ;
        Expr = (A + B),
        build_int_expr_coeffs(A, Scale, !Map, !Const),
        build_int_expr_coeffs(B, Scale, !Map, !Const)
    ;
        Expr = (K * A),
        ( if K = 0 then
            true
        else
            build_int_expr_coeffs(A, Scale * K, !Map, !Const)
        )
    ).

%-----------------------------------------------------------------------------%

flatten_float_expr(LinExpr, Coeffs, Vars, Const) :-
    Scale0 = 1.0,
    Map0 = map.init,
    Const0 = 0.0,
    build_float_expr_coeffs(LinExpr, Scale0, Map0, Map, Const0, Const),
    Coeffs = map.values(Map),
    Vars = map.keys(Map).

:- pred build_float_expr_coeffs(float_expr::in, float::in,
    map(mzn_var, float)::in, map(mzn_var, float)::out,
    float::in, float::out) is det.

build_float_expr_coeffs(Expr, Scale, !Map, !Const) :-
    (
        Expr = float_const(K),
        !:Const = !.Const + Scale * K
    ;
        Expr = float_var(VarId),
        ( if map.search(!.Map, VarId, Coeff0) then
            Coeff = Coeff0 + Scale,
            ( if Coeff = 0.0 then
                map.delete(VarId, !Map)
            else
                map.det_update(VarId, Coeff, !Map)
            )
        else
            map.det_insert(VarId, Scale, !Map)
        )
    ;
        Expr = (A + B),
        build_float_expr_coeffs(A, Scale, !Map, !Const),
        build_float_expr_coeffs(B, Scale, !Map, !Const)
    ;
        Expr = (K * A),
        ( if K = 0.0 then
            true
        else
            build_float_expr_coeffs(A, Scale * K, !Map, !Const)
        )
    ).

%-----------------------------------------------------------------------------%

make_int_int_constraint(RelOp, RelP, SuffixKind, A, B, ConstraintName, Args,
        MaybeSolved) :-
    Suffix = cns_kind_to_string(SuffixKind),
    % We have "simple" constraints, such as "int_le", for simple int_exprs,
    % and "linear" constraints, as "int_lin_le", for non-simple int_exprs.
    %
    ( if int_expr_is_simple(A), int_expr_is_simple(B) then
        ArgA = int_to_mzn_expr(A),
        ArgB = int_to_mzn_expr(B),
        (
            ( RelOp = relop_eq, ConstraintName = "int_eq" ++ Suffix
            ; RelOp = relop_ne, ConstraintName = "int_ne" ++ Suffix
            ; RelOp = relop_lt, ConstraintName = "int_lt" ++ Suffix
            ; RelOp = relop_le, ConstraintName = "int_le" ++ Suffix
            ),
            Args = [ArgA, ArgB]
        ;
            ( RelOp = relop_gt, ConstraintName = "int_lt" ++ Suffix
            ; RelOp = relop_ge, ConstraintName = "int_le" ++ Suffix
            ),
            Args = [ArgB, ArgA]
        ),
        MaybeSolved = no
    else
        flatten_int_expr(A + -1 * B, Coeffs0, Vars0, Const0),
        (
            Coeffs0 = [],
            % The expression reduces to a constant.
            ConstraintName = "dummy",
            Args = [],
            MaybeSolved = yes( if RelP(0, -Const0) then yes else no )
        ;
            Coeffs0 = [_ | _],
            Vars = list_to_array_expr(
                list.map(func(Var) = int_var(Var), Vars0)
            ),
            (
                ( RelOp = relop_eq, ConstraintName = "int_lin_eq" ++ Suffix
                ; RelOp = relop_ne, ConstraintName = "int_lin_ne" ++ Suffix
                ; RelOp = relop_le, ConstraintName = "int_lin_le" ++ Suffix
                ),
                Coeffs = list_to_array_expr(
                    list.map(func(Coeff) = int_const(Coeff), Coeffs0)
                ),
                Const = int_const(-Const0)
            ;
                RelOp = relop_lt,
                ConstraintName = "int_lin_le" ++ Suffix,
                Coeffs = list_to_array_expr(
                    list.map(func(Coeff) = int_const(Coeff), Coeffs0)
                ),
                Const = int_const(-Const0 - 1)
            ;
                (
                    RelOp = relop_gt,
                    Const = int_const(Const0 - 1)
                ;
                    RelOp = relop_ge,
                    Const = int_const(Const0)
                ),
                ConstraintName = "int_lin_le" ++ Suffix,
                Coeffs = list_to_array_expr(
                    list.map(func(Coeff) = int_const(-Coeff), Coeffs0)
                )
            ),
            Args = [int_array_to_mzn_expr(Coeffs), int_array_to_mzn_expr(Vars),
                int_to_mzn_expr(Const)],
            MaybeSolved = no
        )
    ).

%-----------------------------------------------------------------------------%
:- end_module common_expr.
%-----------------------------------------------------------------------------%
