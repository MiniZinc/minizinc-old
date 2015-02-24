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

:- module flatten.array.
:- interface.

:- import_module errors.
:- import_module flatten.env.
:- import_module types.

:- import_module types_and_insts.

:- import_module list.

%-----------------------------------------------------------------------------%

:- pred flatten_array_access(error_context::in, type_inst::in,
    mzn_expr::in, mzn_exprs::in, mzn_expr::out, env::in, env::out) is det.

:- pred flatten_arbitrary_array_to_int(error_context::in, mzn_anns::in,
    string::in, array_expr(T)::in,
    int_expr::out, env::in, env::out) is semidet.

:- pred flatten_array_array_to_bool(
    (func(error_context, array_expr(T), env) = array_expr(T))::in,
    (func(T) = mzn_expr)::in,
    error_context::in, mzn_anns::in, string::in,
    mzn_expr::in, mzn_expr::in, array_expr(T)::in, array_expr(T)::in,
    bool_expr::out, env::in, env::out) is semidet.

:- pred flatten_array_array_to_array(
    (func(error_context, array_expr(T), env) = array_expr(T))::in,
    (func(mzn_var) = T)::in,
    error_context::in, mzn_anns::in, string::in,
    array_expr(T)::in, array_expr(T)::in,
    array_expr(T)::out, env::in, env::out) is semidet.

:- pred flatten_array_redim(error_context::in, mzn_anns::in, string::in,
    list(int_set_expr)::in, array_expr(T)::in,
    array_expr(T)::out, env::in, env::out) is semidet.

:- pred flatten_float_array_to_float(error_context::in, mzn_anns::in,
    string::in, float_array_expr::in,
    float_expr::out, env::in, env::out) is semidet.

:- pred flatten_int_array_to_int(error_context::in, mzn_anns::in,
    string::in, int_array_expr::in,
    int_expr::out, env::in, env::out) is semidet.

:- pred flatten_array_to_int_set(error_context::in, mzn_anns::in,
    string::in, array_expr(T)::in,
    int_set_expr::out, env::in, env::out) is semidet.

:- pred flatten_string_array_to_string(error_context::in, mzn_anns::in,
    string::in, string_array_expr::in, string_expr::out,
    env::in, env::out) is semidet.
            
:- pred flatten_string_string_array_to_string(error_context::in, mzn_anns::in,
    string::in, string_expr::in, string_array_expr::in, string_expr::out,
    env::in, env::out) is semidet.

:- pred flatten_bool_set_array_to_set(error_context::in, mzn_anns::in,
    string::in, bool_set_array_expr::in,
    bool_set_expr::out, env::in, env::out) is semidet.

:- pred flatten_float_set_array_to_set(error_context::in, mzn_anns::in,
    string::in, float_set_array_expr::in,
    float_set_expr::out, env::in, env::out) is semidet.

:- pred flatten_int_set_array_to_set(error_context::in,mzn_anns::in,
    string::in, int_set_array_expr::in,
    int_set_expr::out, env::in, env::out) is semidet.

    % We don't fully expand global variables bound to literal array values
    % in order to avoid duplicating the same array multiple times in the
    % FlatZinc model. However, sometimes it is necessary to do so, hence
    % these functions.
    %
:- func fully_deref_bool_array(error_context, bool_array_expr, env) =
    bool_array_expr.

:- func fully_deref_float_array(error_context, float_array_expr, env) =
    float_array_expr.

:- func fully_deref_int_array(error_context, int_array_expr, env) =
    int_array_expr.

:- func fully_deref_bool_set_array(error_context, bool_set_array_expr, env) =
    bool_set_array_expr.

:- func fully_deref_float_set_array(error_context, float_set_array_expr, env) =
    float_set_array_expr.

:- func fully_deref_int_set_array(error_context, int_set_array_expr, env) =
    int_set_array_expr.

:- func fully_deref_string_array(error_context, string_array_expr, env) =
    string_array_expr.

:- func fully_deref_ann_array(error_context, ann_array_expr, env) =
    ann_array_expr.

    % Ensure an array value is in FlatZinc form.
    %
:- pred simplify_array(
    pred(T, T, env, env):: in(pred(in, out, in, out) is det),
    array_expr(T)::in, array_expr(T)::out, env::in, env::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module common_bounds.
:- import_module flatten.bool.
:- import_module flatten.expr.
:- import_module flatten.float.
:- import_module flatten.int.
:- import_module flatten.set.
:- import_module mzn_ops.

:- import_module intset.

:- import_module array.
:- import_module bool.
:- import_module float.
:- import_module int.
:- import_module set.
:- import_module string.
:- import_module unit.

%-----------------------------------------------------------------------------%

flatten_array_access(Context, TI, MZA, MZIndices, MZ, !Env) :-
    AccessContext = [["In array access.\n"] | Context],
    Bs = list.map(mzn_expr_to_int(AccessContext), MZIndices),
    type_inst_to_mzn_type(Context, TI, _VarPar, MZType),
    ( if
        (
            MZType = mzn_bool,
            A = mzn_expr_to_bool_array(AccessContext, MZA),
            flatten_bool_array_lookup(AccessContext, A, Bs, Z, !Env),
            MZ0 = bool_to_mzn_expr(Z)
        ;
            MZType = mzn_float(_),
            A = mzn_expr_to_float_array(AccessContext, MZA),
            flatten_float_array_lookup(AccessContext, A, Bs, Z, !Env),
            MZ0 = float_to_mzn_expr(Z)
        ;
            MZType = mzn_int(_),
            A = mzn_expr_to_int_array(AccessContext, MZA),
            flatten_int_array_lookup(AccessContext, A, Bs, Z, !Env),
            MZ0 = int_to_mzn_expr(Z)
        ;
            MZType = mzn_bool_set,
            A = mzn_expr_to_bool_set_array(AccessContext, MZA),
            flatten_bool_set_array_lookup(AccessContext, A, Bs, Z, !Env),
            MZ0 = bool_set_to_mzn_expr(Z)
        ;
            MZType = mzn_float_set(_),
            A = mzn_expr_to_float_set_array(AccessContext, MZA),
            flatten_float_set_array_lookup(AccessContext, A, Bs, Z, !Env),
            MZ0 = float_set_to_mzn_expr(Z)
        ;
            MZType = mzn_int_set(_),
            A = mzn_expr_to_int_set_array(AccessContext, MZA),
            flatten_int_set_array_lookup(AccessContext, A, Bs, Z, !Env),
            MZ0 = int_set_to_mzn_expr(Z)
        ;
            MZType = mzn_string,
            A = mzn_expr_to_string_array(AccessContext, MZA),
            flatten_string_array_lookup(AccessContext, A, Bs, Z, !Env),
            MZ0 = string_to_mzn_expr(Z)
        ;
            MZType = mzn_ann,
            A = mzn_expr_to_ann_array(AccessContext, MZA),
            flatten_ann_array_lookup(AccessContext, A, Bs, Z, !Env),
            MZ0 = ann_to_mzn_expr(Z)
        )
    then
        MZ = MZ0
    else
        minizinc_user_error(AccessContext,
            "Array accesses not supported for this type.\n")
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_bool_array_lookup(error_context::in,
    bool_array_expr::in, list(int_expr)::in,
    bool_expr::out, env::in, env::out) is det.

:- pred flatten_float_array_lookup(error_context::in,
    float_array_expr::in, list(int_expr)::in,
    float_expr::out, env::in, env::out) is det.

:- pred flatten_int_array_lookup(error_context::in,
    int_array_expr::in, list(int_expr)::in,
    int_expr::out, env::in, env::out) is det.

:- pred flatten_bool_set_array_lookup(error_context::in,
    bool_set_array_expr::in, list(int_expr)::in,
    bool_set_expr::out, env::in, env::out) is det.

:- pred flatten_float_set_array_lookup(error_context::in,
    float_set_array_expr::in, list(int_expr)::in,
    float_set_expr::out, env::in, env::out) is det.

:- pred flatten_int_set_array_lookup(error_context::in,
    int_set_array_expr::in, list(int_expr)::in,
    int_set_expr::out, env::in, env::out) is det.

:- pred flatten_string_array_lookup(error_context::in,
    string_array_expr::in, list(int_expr)::in,
    string_expr::out, env::in, env::out) is det.

:- pred flatten_ann_array_lookup(error_context::in,
    ann_array_expr::in, list(int_expr)::in,
    mzn_ann::out, env::in, env::out) is det.

flatten_bool_array_lookup(Context, A0, Bs, Z, !Env) :-
    A = fully_deref_bool_array(Context, A0, !.Env),
    TypeName = "bool",
    IsGround = bool_is_par,
    ArrayElemBounds = bool_array_bounds(Context),
    AddTmpVar = add_tmp_bool_var,
    DefaultValue = bool_const(no),
    MznArrayExpr = bool_array_to_mzn_expr,
    ElemExpr = ( func(V, I) = bool_var(var_index(V, I)) ),
    flatten_array_lookup(Context, TypeName, IsGround, ArrayElemBounds,
        AddTmpVar, DefaultValue, MznArrayExpr, ElemExpr,
        simplify_bool(Context), A0, A, Bs, Z, !Env).

flatten_float_array_lookup(Context, A0, Bs, Z, !Env) :-
    A = fully_deref_float_array(Context, A0, !.Env),
    TypeName = "float",
    IsGround = float_is_par,
    ArrayElemBounds = float_array_bounds(Context),
    AddTmpVar = add_tmp_float_var,
    DefaultValue = float_const(0.0),
    MznArrayExpr = float_array_to_mzn_expr,
    ElemExpr = ( func(V, I) = float_var(var_index(V, I)) ),
    flatten_array_lookup(Context, TypeName, IsGround, ArrayElemBounds,
        AddTmpVar, DefaultValue, MznArrayExpr, ElemExpr,
        simplify_float(Context), A0, A, Bs, Z, !Env).

flatten_int_array_lookup(Context, A0, Bs, Z, !Env) :-
    A = fully_deref_int_array(Context, A0, !.Env),
    TypeName = "int",
    IsGround = int_is_par,
    ArrayElemBounds = int_array_bounds(Context),
    AddTmpVar = add_tmp_int_var,
    DefaultValue = int_const(0),
    MznArrayExpr = int_array_to_mzn_expr,
    ElemExpr = ( func(V, I) = int_var(var_index(V, I)) ),
    flatten_array_lookup(Context, TypeName, IsGround, ArrayElemBounds,
        AddTmpVar, DefaultValue, MznArrayExpr, ElemExpr,
        simplify_int(Context), A0, A, Bs, Z, !Env).

flatten_bool_set_array_lookup(Context, A0, Bs, Z, !Env) :-
    A = fully_deref_bool_set_array(Context, A0, !.Env),
    TypeName = "set",
    IsGround = bool_set_is_par,
    ArrayElemBounds = bool_set_array_bounds(Context),
    AddTmpVar = var_type_unsupported("set of bool"),
    DefaultValue = set_items(set.init),
    MznArrayExpr = bool_set_array_to_mzn_expr,
    ElemExpr = ( func(V, I) = set_var(var_index(V, I)) ),
    flatten_array_lookup(Context, TypeName, IsGround, ArrayElemBounds,
        AddTmpVar, DefaultValue, MznArrayExpr, ElemExpr, nonvar_simplify,
        A0, A, Bs, Z, !Env).

flatten_float_set_array_lookup(Context, A0, Bs, Z, !Env) :-
    A = fully_deref_float_set_array(Context, A0, !.Env),
    TypeName = "set",
    IsGround = float_set_is_par,
    ArrayElemBounds = float_set_array_bounds(Context),
    AddTmpVar = var_type_unsupported("set of float"),
    DefaultValue = set_items(set.init),
    MznArrayExpr = float_set_array_to_mzn_expr,
    ElemExpr = ( func(V, I) = set_var(var_index(V, I)) ),
    flatten_array_lookup(Context, TypeName, IsGround, ArrayElemBounds,
        AddTmpVar, DefaultValue, MznArrayExpr, ElemExpr, nonvar_simplify,
        A0, A, Bs, Z, !Env).

flatten_int_set_array_lookup(Context, A0, Bs, Z, !Env) :-
    A = fully_deref_int_set_array(Context, A0, !.Env),
    TypeName = "set",
    IsGround = int_set_is_par,
    ArrayElemBounds = int_set_array_bounds(Context),
    AddTmpVar = add_tmp_int_set_var,
    DefaultValue = set_items(set.init),
    MznArrayExpr = int_set_array_to_mzn_expr,
    ElemExpr = ( func(V, I) = set_var(var_index(V, I)) ),
    flatten_array_lookup(Context, TypeName, IsGround, ArrayElemBounds,
        AddTmpVar, DefaultValue, MznArrayExpr, ElemExpr, nonvar_simplify,
        A0, A, Bs, Z, !Env).

flatten_string_array_lookup(Context, A0, Bs, Z, !Env) :-
    A = fully_deref_string_array(Context, A0, !.Env),
    TypeName = "string",
    IsGround = string_is_par,
    ArrayElemBounds = string_array_bounds(Context),
    AddTmpVar = add_tmp_string_var,
    DefaultValue = string_const(""),
    MznArrayExpr = string_array_to_mzn_expr,
    ElemExpr = ( func(_, _) = _ :-
        minizinc_internal_error(Context, $pred,
            "ElemExpr should not be called!")
    ),
    flatten_array_lookup(Context, TypeName, IsGround, ArrayElemBounds,
        AddTmpVar, DefaultValue, MznArrayExpr, ElemExpr, nonvar_simplify,
        A0, A, Bs, Z, !Env).

flatten_ann_array_lookup(Context, A0, Bs, Z, !Env) :-
    A = fully_deref_ann_array(Context, A0, !.Env),
    TypeName = "ann",
    IsGround = ann_is_par,
    ArrayElemBounds = ann_array_bounds(Context),
    AddTmpVar = add_tmp_ann_var,
    DefaultValue = mzn_ann("dummy", []),
    MznArrayExpr = ann_array_to_mzn_expr,
    ElemExpr = ( func(_, _) = _ :-
        minizinc_internal_error(Context, $pred,
            "ElemExpr should not be called!")
    ),
    flatten_array_lookup(Context, TypeName, IsGround, ArrayElemBounds,
        AddTmpVar, DefaultValue, MznArrayExpr, ElemExpr, nonvar_simplify,
        A0, A, Bs, Z, !Env).

:- pred var_type_unsupported(string::in, error_context::in, BoundsT::in,
    string::in, mzn_exprs::in, mzn_anns::in, var_id::out, ElemT::out,
    env::in, env::out) is det.

var_type_unsupported(VarTypeName, Context, _, _, _, _, _, _, !Env) :-
    minizinc_user_error(Context, "Variables of type var " ++ VarTypeName ++
        " are not supported in FlatZinc.\n").

    % For use with flatten_array_lookup and par types.
    %
:- pred nonvar_simplify(T::in, T::out, env::in, env::out) is det.

nonvar_simplify(!T, !Env).

%-----------------------------------------------------------------------------%

fully_deref_bool_array(Context, A, Env) =
    ( if
        A = array_var(IndexRanges, V),
        Env ^ var_value(V) = MZA
    then
        replace_index_ranges(IndexRanges, mzn_expr_to_bool_array(Context, MZA))
    else
        A
    ).

fully_deref_float_array(Context, A, Env) =
    ( if
        A = array_var(IndexRanges, V),
        Env ^ var_value(V) = MZA
    then
        replace_index_ranges(IndexRanges,
            mzn_expr_to_float_array(Context, MZA))
    else
        A
    ).

fully_deref_int_array(Context, A, Env) =
    ( if
        A = array_var(IndexRanges, V),
        Env ^ var_value(V) = MZA
    then
        replace_index_ranges(IndexRanges, mzn_expr_to_int_array(Context, MZA))
    else
        A
    ).

fully_deref_bool_set_array(Context, A, Env) =
    ( if
        A = array_var(IndexRanges, V),
        Env ^ var_value(V) = MZA
    then
        replace_index_ranges(IndexRanges,
            mzn_expr_to_bool_set_array(Context, MZA))
    else
        A
    ).

fully_deref_float_set_array(Context, A, Env) =
    ( if
        A = array_var(IndexRanges, V),
        Env ^ var_value(V) = MZA
    then
        replace_index_ranges(IndexRanges,
            mzn_expr_to_float_set_array(Context, MZA))
    else
        A
    ).

fully_deref_int_set_array(Context, A, Env) =
    ( if
        A = array_var(IndexRanges, V),
        Env ^ var_value(V) = MZA
    then
        replace_index_ranges(IndexRanges,
            mzn_expr_to_int_set_array(Context, MZA))
    else
        A
    ).

fully_deref_string_array(Context, A, Env) =
    ( if
        A = array_var(IndexRanges, V),
        Env ^ var_value(V) = MZA
    then
        replace_index_ranges(IndexRanges,
            mzn_expr_to_string_array(Context, MZA))
    else
        A
    ).

fully_deref_ann_array(Context, A, Env) =
    ( if
        A = array_var(IndexRanges, V),
        Env ^ var_value(V) = MZA
    then
        replace_index_ranges(IndexRanges,
            mzn_expr_to_ann_array(Context, MZA))
    else
        A
    ).

%-----------------------------------------------------------------------------%

    % Note: array literals containing var elements may not be flat by this
    % point - we need to simplify (flatten) when using them in FlatZinc.
    % The predicate SimplifyElem is used to do this flattening.  For, types
    % that are not MiniZinc decision variables this predidate can be a no-op.
    %
    % XXX why does the array expression get passed into this twice, arguments
    % A0 and A?  This whole predicate is very confusing - juliensf.
    %
:- pred flatten_array_lookup(error_context::in, string::in,
    pred(ElemT)::in(pred(in) is semidet),
    (func(global_var_map, array_expr(ElemT)) = BoundsT)::in,
    pred(error_context, BoundsT, string, list(mzn_expr), mzn_anns,
        var_id, ElemT, env, env)::
        in(pred(in, in, in, in, in, out, out, in, out) is det),
    ElemT::in,
    (func(array_expr(ElemT)) = mzn_expr)::in,
    (func(var_id, int) = ElemT)::in,
    pred(ElemT, ElemT, env, env)::in(pred(in, out, in, out) is det),
    array_expr(ElemT)::in, array_expr(ElemT)::in, list(int_expr)::in,
    ElemT::out, env::in, env::out) is det.

flatten_array_lookup(Context, TypeName, IsGround, ArrayElemBounds,
        AddTmpVar, DefaultValue, MznArrayExpr, ElemExpr, SimplifyElem, 
        A0, A, Bs, Z, !Env) :-
    (
        A = array_items(IndexRanges, Xs),
        flatten_array_indices_to_int(Context, IndexRanges, Bs, B, !Env),
        ( if B = int_const(IB) then
            flatten_array_lookup_par_par(Context, DefaultValue,
                Xs, IB, Z, !Env)
        else
            ( if
                (
                    A0 = array_var(_, V),
                    !.Env ^ var_is_var(V) = yes
                ;
                    some [X] ( array.member(Xs, X), not IsGround(X) )
                )
            then
                ConstraintName = "array_var_" ++ TypeName ++ "_element"
            else
                ConstraintName = "array_" ++ TypeName ++ "_element"
            ),
            simplify_array(SimplifyElem, A0, FlatA0, !Env),
            flatten_array_lookup_var(Context, ConstraintName,
                ArrayElemBounds, AddTmpVar, MznArrayExpr, FlatA0, B, Z, !Env)
        )
    ;
        A = array_var(IndexRanges, V),
        flatten_array_indices_to_int(Context, IndexRanges, Bs, B, !Env),
        ( if B = int_const(IB) then
            Z = ElemExpr(V, IB)
        else
            ( if !.Env ^ var_is_var(V) = no then
                ConstraintName = "array_" ++ TypeName ++ "_element"
            else
                ConstraintName = "array_var_" ++ TypeName ++ "_element"
            ),
            flatten_array_lookup_var(Context, ConstraintName,
                ArrayElemBounds, AddTmpVar, MznArrayExpr, A, B, Z, !Env)
        )
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_array_lookup_par_par(error_context::in, ElemT::in,
    array(ElemT)::in, int::in, ElemT::out, env::in, env::out) is det.

flatten_array_lookup_par_par(Context, DefaultValue, Xs, I, Z, !Env) :-
    I0 = I - 1,
    Reifying = !.Env ^ reifying,
    (
        Reifying = not_reifying,
        ( if array.semidet_lookup(Xs, I0, Z0)
        then Z = Z0
        else minizinc_user_error(Context, "Array index out of range.\n")
        )
    ;
        Reifying = reifying(_ : bool_exprs),
        ( if array.semidet_lookup(Xs, I0, Z0) then
            Z = Z0
        else
            Z = DefaultValue,
            !Env ^ reifying := reifying([bool_const(no)])
        )
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_array_lookup_var(error_context::in, string::in,
    (func(global_var_map, array_expr(ElemT)) = BoundsT)::in,
    pred(error_context, BoundsT, string, list(mzn_expr), mzn_anns,
        var_id, ElemT, env, env)::
        in(pred(in, in, in, in, in, out, out, in, out) is det),
    (func(array_expr(ElemT)) = mzn_expr)::in,
    array_expr(ElemT)::in, int_expr::in, ElemT::out, env::in, env::out) is det.

flatten_array_lookup_var(Context, ConstraintName, ArrayElemBounds, AddTmpVar,
        MznArrayExpr, A, B, Z, !Env) :-
    % NOTE: B must be simplified before calling this predicate.
    BoundsA = ArrayElemBounds(!.Env ^ env_globals, A),
    Reifying = !.Env ^ reifying,
    (
        Reifying = not_reifying,
        AddTmpVar(Context, BoundsA, ConstraintName,
            [int_to_mzn_expr(B), MznArrayExpr(A)], no_anns, _VarIdZ, Z, !Env)
    ;
        Reifying = reifying(ReifVars),
        ( if ReifVars = [IndexIsInRange | _] then
            Size = array_size(A),
            BoundsTmpB = int_range_lb_ub(1, Size),
            make_tmp_int_var(Context, BoundsTmpB, just_is_defined_var,
                _, TmpB, !Env),
            AddTmpVar(Context, BoundsA, ConstraintName,
                [int_to_mzn_expr(TmpB), MznArrayExpr(A)],
                no_anns, _VarIdZ, Z, !Env),
            add_constraint(Context, "int_eq_reif",
                [int_to_mzn_expr(B), int_to_mzn_expr(TmpB),
                bool_to_mzn_expr(IndexIsInRange)], no_anns, !Env)
        else
            AddTmpVar(Context, BoundsA, ConstraintName,
                [int_to_mzn_expr(B), MznArrayExpr(A)],
                no_anns, _VarIdZ, Z, !Env)
%           add_constraint(Context, "int_eq",
%               [int_to_mzn_expr(B), int_to_mzn_expr(TmpB)], no_anns, !Env)
        )
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_array_indices_to_int(error_context::in, index_ranges::in,
    list(int_expr)::in, int_expr::out, env::in, env::out) is det.

flatten_array_indices_to_int(Context, IndexRanges, IndexExprs, OffsetExpr,
        !Env) :-
    flatten_array_indices_to_int_2(Context, IndexRanges, IndexExprs, 1, _Size,
        OffsetExpr0, !Env),
    ( if int_expr_is_simple(OffsetExpr0) then
        OffsetExpr = OffsetExpr0
    else
        % Ensure we use domain consistency to compute the FlatZinc array index.
        % XXX why?
        Anns = !.Env ^ anns,
        add_anns(just_domain, !Env),
        simplify_int(Context, OffsetExpr0, OffsetExpr, !Env),
        !Env ^ anns := Anns
    ).

    % Given a list of index ranges [{LB1, UB1}, {LB2, UB2}, {LB3, UB3}]
    % and a list of index exprs [A1, A2, A3] we want to impose the following
    % constraints:
    %   LB1 <= A1 <= UB1
    %   LB2 <= A2 <= UB2
    %   LB3 <= A3 <= UB3
    % and compute the following result as the corresponding 1D index:
    %   (A1 - LB1) * ((1 + UB2 - LB2) * (1 + UB3 - LB3) * 1) +
    %   (A2 - LB2) *                   ((1 + UB3 - LB3) * 1) +
    %   (A3 - LB3) *                                     (1) +
    %   1
    %
:- pred flatten_array_indices_to_int_2(error_context::in, index_ranges::in,
    list(int_expr)::in, int::in, int::out, int_expr::out,
    env::in, env::out) is det.

flatten_array_indices_to_int_2(Context, IndexRanges, IndexExprs, IndexNo,
        Size, OffsetExpr, !Env) :-
    (
        IndexRanges = [],
        IndexExprs = [],
        Size = 1,
        OffsetExpr = int_const(1)
    ;
        IndexRanges = [HeadIndexRange | TailIndexRanges],
        IndexExprs = [HeadIndexExpr | TailIndexExprs],
        flatten_array_indices_to_int_2(Context,
            TailIndexRanges, TailIndexExprs, IndexNo + 1,
            TailSize, TailOffsetExpr, !Env),
        (
            HeadIndexRange = index_range(LB, UB)
        ;
            HeadIndexRange = index_implicit,
            minizinc_internal_error(Context, $pred, "implicit array index")
        ),
        Size = (1 + UB - LB) * TailSize,
        IndexContext =
            [ ["In index argument ", string.int_to_string(IndexNo), "\n"]
            | Context
            ],
        ErrMsg = "Index out of range.\n",
        get_int_expr_lb_ub(IndexContext, !.Env ^ env_globals, HeadIndexExpr,
            LB0, UB0),
        ( if ( UB < LB0 ; UB0 < LB ) then
            % This index is necessarily out of range.
            Reifying = !.Env ^ reifying,
            (
                Reifying = not_reifying,
                minizinc_user_error(IndexContext, ErrMsg)
            ;
                Reifying = reifying(_ : bool_exprs),
                !Env ^ reifying := reifying([bool_const(no)]),
                % This is a bust, so just return a dummy value for OffsetExpr.
                OffsetExpr = TailOffsetExpr
            )
        else
            
            % Add constraints on the domain of the index variable.
            %
            flatten_int_int_to_bool_or_inconsistent(Context, ErrMsg, no_anns,
                ii2b_le, int_const(LB), HeadIndexExpr, CVCheckLB, !Env),
            CVCheckLBExpr = bool_const_or_var_to_expr(CVCheckLB),
            impose_constraint(IndexContext, ErrMsg, CVCheckLBExpr, !Env),
            flatten_int_int_to_bool_or_inconsistent(Context, ErrMsg, no_anns,
                ii2b_le, HeadIndexExpr, int_const(UB), CVCheckUB, !Env),
            CVCheckUBExpr = bool_const_or_var_to_expr(CVCheckUB),
            impose_constraint(IndexContext, ErrMsg, CVCheckUBExpr, !Env),

            % In a reifying context it is actually the conjunction of the
            % inequality constraints we just introduced that is reified;
            % add that conjunction.
            % (In a non-reifying context the next bit will flatten directly
            % to true or false.)
            ( if
                flatten_bool_bool_to_bool(Context, no_anns, bb2b_and,
                    CVCheckLBExpr, CVCheckUBExpr, IndexReifExpr0, !Env)
              then
                IndexReifExpr = IndexReifExpr0 
              else
                minizinc_internal_error(IndexContext, $pred,
                    "flatten_bool_bool_to_bool failed.\n")
            ),
            impose_constraint(IndexContext, ErrMsg, IndexReifExpr, !Env),
            ( if
                flatten_int_int_to_int(IndexContext, no_anns,
                    ii2i_sub, HeadIndexExpr, int_const(LB), TmpExpr1, !Env),
                flatten_int_int_to_int(IndexContext, no_anns,
                    ii2i_mul, TmpExpr1, int_const(TailSize), TmpExpr2, !Env),
                flatten_int_int_to_int(IndexContext, no_anns,
                    ii2i_add, TmpExpr2, TailOffsetExpr, OffsetExprPrime, !Env)
            then
                OffsetExpr = OffsetExprPrime
            else
                minizinc_internal_error(IndexContext, $pred,
                    "flatten_int_int_to_int failed.\n")
            )
        )
    ;
        (
            IndexRanges = [],
            IndexExprs = [_ | _]
        ;
            IndexRanges = [_ | _],
            IndexExprs = []
        ),
        minizinc_internal_error(Context, $pred, "list lengths don't match.\n")
    ).

%-----------------------------------------------------------------------------%

simplify_array(P, A0, A, !Env) :-
    (
        A0 = array_var(_, _),
        A = index_ranges_to_fzn_form(A0)
    ;
        A0 = array_items(IndexRanges0, Items0),
        IndexRanges = [index_range(1, index_ranges_to_size(IndexRanges0))],
        array.map_foldl(P, Items0, Items, !Env),
        A = array_items(IndexRanges, Items)
    ).

%-----------------------------------------------------------------------------%

flatten_array_array_to_bool(FullyDeref, ToMZNExpr, Context, _Anns, "=",
        MZA, MZB, A0, B0, Z, !Env) :-
    A = FullyDeref(Context, A0, !.Env),
    B = FullyDeref(Context, B0, !.Env),
    ( A = array_var(IndexRangesA, _)
    ; A = array_items(IndexRangesA, _)
    ),
    ( B = array_var(IndexRangesB, _)
    ; B = array_items(IndexRangesB, _)
    ),
    ( if IndexRangesA = IndexRangesB then
        (
            A = array_items(_, ItemsA),
            B = array_items(_, ItemsB),
            MZItemsA = array.map(ToMZNExpr, ItemsA),
            MZItemsB = array.map(ToMZNExpr, ItemsB),
            P = ( pred(MZItemA::in, MZItemB::in, MZ::out, E0::in, E::out)
                    is semidet :-
                flatten_builtin(Context, "=", [MZItemA, MZItemB], MZ, E0, E)
            ),
            array.map_corresponding_foldl(P, MZItemsA, MZItemsB, MZBools, !Env),
            Bools = array.map(mzn_expr_to_bool(Context), MZBools),
            array.foldl2(conjoin(Context), Bools, bool_const(yes), Z, !Env)
        ;
            A = array_items(_, ItemsA),
            B = array_var(_, VarIdB),
            refine_array_var_items_bounds(Context, VarIdB, ItemsA, Z, !Env),
            !Env ^ var_value(VarIdB) := MZA
        ;
            A = array_var(_, VarIdA),
            B = array_items(_, ItemsB),
            refine_array_var_items_bounds(Context, VarIdA, ItemsB, Z, !Env),
            !Env ^ var_value(VarIdA) := MZB
        ;
            A = array_var(_, VarIdA),
            B = array_var(_, VarIdB),
            refine_array_var_var_bounds(Context, VarIdA, VarIdB, Z, !Env),
            !Env ^ var_value(VarIdA) := MZB
        )
    else
        minizinc_user_error(Context, "Array index ranges do not match.\n")
    ).

%-----------------------------------------------------------------------------%

:- pred refine_array_var_items_bounds(error_context::in, var_id::in,
    array(T)::in, bool_expr::out, env::in, env::out) is semidet.

refine_array_var_items_bounds(Context, VarIdA, ItemsB, Z, !Env) :-
    % NOTE: we can only refine bounds on array items for non-empty arrays.
    array.size(ItemsB, NumItemsB),
    ( if
        dynamic_cast(ItemsB, FloatItems0 : float_exprs),
        NumItemsB > 0
     then
        array.map_foldl(simplify_float(Context), FloatItems0, FloatItems, !Env),
        LBA = !.Env ^ var_float_lb(VarIdA),
        UBA = !.Env ^ var_float_ub(VarIdA),
        A = float_var(var_no_index(VarIdA)),
        refine_array_var_items_float_bounds(Context, A, LBA, UBA,
            FloatItems, float_plus_infinity, float_minus_infinity, Z, !Env)
    else if
        dynamic_cast(ItemsB, IntItems0 : int_exprs),
        NumItemsB > 0
    then
        array.map_foldl(simplify_int(Context), IntItems0, IntItems, !Env),
        LBA = !.Env ^ var_int_lb(VarIdA),
        UBA = !.Env ^ var_int_ub(VarIdA),
        A = int_var(var_no_index(VarIdA)),
        refine_array_var_items_int_bounds(Context, A, LBA, UBA,
            IntItems, int_plus_infinity, int_minus_infinity, Z, !Env)
    else if
        dynamic_cast(ItemsB, SetItems : int_set_exprs),
        NumItemsB > 0
    then
        UBA = !.Env ^ var_set_ub(VarIdA),
        A = int_var(var_no_index(VarIdA)),
        refine_array_var_items_int_set_bounds(Context, A, UBA,
            SetItems, int_plus_infinity, int_minus_infinity, Z, !Env)
    else
        Z = bool_const(yes)
    ).

%-----------------------------------------------------------------------------%

:- pred refine_array_var_items_float_bounds(error_context::in, float_expr::in,
    float::in, float::in, float_exprs::in, float::in, float::in,
    bool_expr::out, env::in, env::out) is semidet.

refine_array_var_items_float_bounds(Context, A, LBA, UBA,
        Items, LBItems0, UBItems0, Z, !Env) :-
    refine_array_var_items_float_bounds_2(Context, A, LBA, UBA,
        0, Items, LBItems0, UBItems0, Z, !Env).

%-----------------------------------------------------------------------------%

:- pred refine_array_var_items_float_bounds_2(error_context::in,
    float_expr::in, float::in, float::in, int::in, float_exprs::in,
    float::in, float::in, bool_expr::out, env::in, env::out) is semidet.

refine_array_var_items_float_bounds_2(Context, A, LBA, UBA,
        I, Items, LBItems0, UBItems0, Z, !Env) :-
    ( if I < array.size(Items) then
        Item = Items ^ elem(I),
        refine_float_lb(LBA, Item, !Env),
        refine_float_ub(UBA, Item, !Env),
        get_float_expr_lb_ub(!.Env ^ env_globals, Item, LBItem, UBItem),
        LBItems = float.min(LBItems0, LBItem),
        UBItems = float.max(UBItems0, UBItem),
        refine_array_var_items_float_bounds_2(Context, A, LBA, UBA,
            I + 1, Items, LBItems, UBItems, Z, !Env)
    else if LBA =< LBItems0, UBItems0 =< UBA then
        refine_float_lb(LBItems0, A, !Env),
        refine_float_ub(UBItems0, A, !Env),
        Z = bool_const(yes)
    else
        Z = bool_const(no)
    ).

%-----------------------------------------------------------------------------%

:- pred refine_array_var_items_int_bounds(error_context::in, int_expr::in,
    int::in, int::in, int_exprs::in, int::in, int::in,
    bool_expr::out, env::in, env::out) is semidet.

refine_array_var_items_int_bounds(Context, A, LBA, UBA,
        Items, LBItems0, UBItems0, Z, !Env) :-
    refine_array_var_items_int_bounds_2(Context, A, LBA, UBA,
        0, Items, LBItems0, UBItems0, Z, !Env).

%-----------------------------------------------------------------------------%

:- pred refine_array_var_items_int_bounds_2(error_context::in,
    int_expr::in, int::in, int::in, int::in, int_exprs::in,
    int::in, int::in, bool_expr::out, env::in, env::out) is semidet.

refine_array_var_items_int_bounds_2(Context, A, LBA, UBA,
        I, Items, LBItems0, UBItems0, Z, !Env) :-
    ( if I < array.size(Items) then
        Item = Items ^ elem(I),
        refine_int_lb(LBA, Item, !Env),
        refine_int_ub(UBA, Item, !Env),
        get_int_expr_lb_ub(Context, !.Env ^ env_globals, Item, LBItem, UBItem),
        LBItems = int.min(LBItems0, LBItem),
        UBItems = int.max(UBItems0, UBItem),
        refine_array_var_items_int_bounds_2(Context, A, LBA, UBA,
            I + 1, Items, LBItems, UBItems, Z, !Env)
    else if LBA =< LBItems0, UBItems0 =< UBA then
        refine_int_lb(LBItems0, A, !Env),
        refine_int_ub(UBItems0, A, !Env),
        Z = bool_const(yes)
    else
        Z = bool_const(no)
    ).

%-----------------------------------------------------------------------------%

:- pred refine_array_var_items_int_set_bounds(error_context::in,
    int_expr::in, int_range::in, int_set_exprs::in, int::in, int::in,
    bool_expr::out, env::in, env::out) is semidet.

refine_array_var_items_int_set_bounds(Context, IntA, BoundsA,
        Items, LBItems, UBItems, Z, !Env) :-
    refine_array_var_items_int_set_bounds_2(Context, IntA, BoundsA,
        0, Items, LBItems, UBItems, Z, !Env).

%-----------------------------------------------------------------------------%

:- pred refine_array_var_items_int_set_bounds_2(error_context::in,
    int_expr::in, int_range::in, int::in, int_set_exprs::in,
    int::in, int::in, bool_expr::out, env::in, env::out) is semidet.

refine_array_var_items_int_set_bounds_2(Context, IntA, BoundsA,
        I, Items, LBItems0, UBItems0, Z, !Env) :-
    ( if I < array.size(Items) then
        Item = Items ^ elem(I),
        refine_int_set_bounds(Context, BoundsA, Item, !Env),
        get_int_set_expr_lb_ub(!.Env ^ env_globals, Item, LBItem, UBItem),
        LBItems = int.min(LBItems0, LBItem),
        UBItems = int.max(UBItems0, UBItem),
        refine_array_var_items_int_set_bounds_2(Context, IntA, BoundsA,
            I + 1, Items, LBItems, UBItems, Z, !Env)
    else if
        (
            BoundsA = int_range_unbounded
        ;
            BoundsA = int_range_lb_ub(LBA, UBA),
            LBA =< LBItems0, UBItems0 =< UBA
        ;
            BoundsA = int_range_set(IntSet),
            % JJJ FIXME
            Set = set.from_sorted_list(intset.to_sorted_list(IntSet)),
            get_int_set_expr_lb_ub(!.Env ^ env_globals, set_items(Set),
                LBA, UBA),
            LBA =< LBItems0, UBItems0 =< UBA
        )
    then
        refine_int_lb(LBItems0, IntA, !Env),
        refine_int_ub(UBItems0, IntA, !Env),
        Z = bool_const(yes)
    else
        Z = bool_const(no)
    ).

%-----------------------------------------------------------------------------%

:- pred int_set_array_items_min_max(error_context::in, int_set_exprs::in,
    int::in, int::in, int::in, int::out, int::in, int::out,
    env::in, env::out) is semidet.

int_set_array_items_min_max(Context, Items, LBA, UBA, !LB, !UB, !Env) :-
    int_set_array_items_min_max_2(Context, 0, Items, LBA, UBA, !LB, !UB, !Env).

%-----------------------------------------------------------------------------%

:- pred int_set_array_items_min_max_2(error_context::in,
    int::in, int_set_exprs::in,
    int::in, int::in, int::in, int::out, int::in, int::out,
    env::in, env::out) is semidet.

int_set_array_items_min_max_2(Context, I, Items, LBA, UBA, !LB, !UB, !Env) :-
    ( if I < array.size(Items) then
        Item = Items ^ elem(I),
        ( if Item = set_var(MZVar) then
            VarId = mzn_var_id(MZVar),
            C = int_var(var_no_index(VarId)),
            refine_int_lb(LBA, C, !Env),
            refine_int_ub(UBA, C, !Env)
        else
            true
        ),
        get_int_set_expr_lb_ub(!.Env ^ env_globals, Item, ItemLB, ItemUB),
        int.min(ItemLB, !LB),
        int.max(ItemUB, !UB),
        int_set_array_items_min_max_2(Context, I + 1, Items, LBA, UBA,
            !LB, !UB, !Env)
    else
        true
    ).

%-----------------------------------------------------------------------------%

:- pred refine_array_var_var_bounds(error_context::in,
    var_id::in, var_id::in, bool_expr::out, env::in, env::out) is det.

refine_array_var_var_bounds(_Context, VarIdA, VarIdB, Z, !Env) :-
    VarType = !.Env ^ var_type(VarIdA),
    ( if VarType = mzn_float_array(_) then
        FloatA = float_var(var_no_index(VarIdA)),
        FloatB = float_var(var_no_index(VarIdB)),
        FloatLBA = !.Env ^ var_float_lb(VarIdA),
        FloatUBA = !.Env ^ var_float_ub(VarIdA),
        FloatLBB = !.Env ^ var_float_lb(VarIdB),
        FloatUBB = !.Env ^ var_float_ub(VarIdB),
        FloatLB = float.max(FloatLBA, FloatLBB),
        FloatUB = float.min(FloatUBA, FloatUBB),
        refine_float_lb(FloatLB, FloatA, !Env),
        refine_float_ub(FloatUB, FloatA, !Env),
        refine_float_lb(FloatLB, FloatB, !Env),
        refine_float_ub(FloatUB, FloatB, !Env),
        ( if
            ( FloatUBA < FloatLBB
            ; FloatUBB < FloatLBA
            )
        then
            Z = bool_const(no)
        else
            Z = bool_const(yes)
        )
      else if VarType = mzn_int_array(_) then
        IntA = int_var(var_no_index(VarIdA)),
        IntB = int_var(var_no_index(VarIdB)),
        IntLBA = !.Env ^ var_int_lb(VarIdA),
        IntUBA = !.Env ^ var_int_ub(VarIdA),
        IntLBB = !.Env ^ var_int_lb(VarIdB),
        IntUBB = !.Env ^ var_int_ub(VarIdB),
        IntLB = int.max(IntLBA, IntLBB),
        IntUB = int.min(IntUBA, IntUBB),
        refine_int_lb(IntLB, IntA, !Env),
        refine_int_ub(IntUB, IntA, !Env),
        refine_int_lb(IntLB, IntB, !Env),
        refine_int_ub(IntUB, IntB, !Env),
        ( if
            ( IntUBA < IntLBB
            ; IntUBB < IntLBA
            )
        then
            Z = bool_const(no)
        else
            Z = bool_const(yes)
        )
    else
        Z = bool_const(yes)
    ).

%-----------------------------------------------------------------------------%

flatten_array_redim(Context, _Anns, "array1d", [A], B, Z, !Env) :-
    IndexRangeA = int_set_to_index_range(Context, !.Env ^ env_globals, A),
    NewIndexRanges = [IndexRangeA],
    NewN = index_ranges_to_size(NewIndexRanges),
    ( B = array_items(OldIndexRanges, _)
    ; B = array_var(OldIndexRanges, _)
    ),
    OldN = index_ranges_to_size(OldIndexRanges),
    ( if NewN = OldN then
        (
            B = array_items(_, Items),
            Z = array_items(NewIndexRanges, Items)
        ;
            B = array_var(_, VarId),
            Z = array_var(NewIndexRanges, VarId)
        )
    else
        string.format("Array size mismatch: expected %d, actual %d.\n",
            [i(NewN), i(OldN)], Msg),
        minizinc_user_error(Context, Msg)
    ).

flatten_array_redim(Context, _Anns, "array2d", [A, B], C, Z, !Env) :-
    IndexRangeA = int_set_to_index_range(Context, !.Env ^ env_globals, A),
    IndexRangeB = int_set_to_index_range(Context, !.Env ^ env_globals, B),
    NewIndexRanges = [IndexRangeA, IndexRangeB],
    NewN = index_ranges_to_size(NewIndexRanges),
    ( C = array_items(OldIndexRanges, _)
    ; C = array_var(OldIndexRanges, _)
    ),
    OldN = index_ranges_to_size(OldIndexRanges),
    ( if NewN = OldN then
        (
            C = array_items(_, Items),
            Z = array_items(NewIndexRanges, Items)
        ;
            C = array_var(_, VarId),
            Z = array_var(NewIndexRanges, VarId)
        )
    else
        string.format("Array size mismatch: expected %d, actual %d.\n",
            [i(NewN), i(OldN)], Msg),
        minizinc_user_error(Context, Msg)
    ).

flatten_array_redim(Context, _Anns, "array3d", [A, B, C], D, Z, !Env) :-
    IndexRangeA = int_set_to_index_range(Context, !.Env ^ env_globals, A),
    IndexRangeB = int_set_to_index_range(Context, !.Env ^ env_globals, B),
    IndexRangeC = int_set_to_index_range(Context, !.Env ^ env_globals, C),
    NewIndexRanges = [IndexRangeA, IndexRangeB, IndexRangeC],
    NewN = index_ranges_to_size(NewIndexRanges),
    ( D = array_items(OldIndexRanges, _)
    ; D = array_var(OldIndexRanges, _)
    ),
    OldN = index_ranges_to_size(OldIndexRanges),
    ( if NewN = OldN then
        (
            D = array_items(_, Items),
            Z = array_items(NewIndexRanges, Items)
        ;
            D = array_var(_, VarId),
            Z = array_var(NewIndexRanges, VarId)
        )
    else
        string.format("Array size mismatch: expected %d, actual %d.\n",
            [i(NewN), i(OldN)], Msg),
        minizinc_user_error(Context, Msg)
    ).

flatten_array_redim(Context, _Anns, "array4d", [A, B, C, D], E, Z, !Env) :-
    IndexRangeA = int_set_to_index_range(Context, !.Env ^ env_globals, A),
    IndexRangeB = int_set_to_index_range(Context, !.Env ^ env_globals, B),
    IndexRangeC = int_set_to_index_range(Context, !.Env ^ env_globals, C),
    IndexRangeD = int_set_to_index_range(Context, !.Env ^ env_globals, D),
    NewIndexRanges = [IndexRangeA, IndexRangeB, IndexRangeC, IndexRangeD],
    NewN = index_ranges_to_size(NewIndexRanges),
    ( E = array_items(OldIndexRanges, _)
    ; E = array_var(OldIndexRanges, _)
    ),
    OldN = index_ranges_to_size(OldIndexRanges),
    ( if NewN = OldN then
        (
            E = array_items(_, Items),
            Z = array_items(NewIndexRanges, Items)
        ;
            E = array_var(_, VarId),
            Z = array_var(NewIndexRanges, VarId)
        )
    else
        string.format("Array size mismatch: expected %d, actual %d.\n",
            [i(NewN), i(OldN)], Msg),
        minizinc_user_error(Context, Msg)
    ).

flatten_array_redim(Context, _Anns, "array5d", [I1, I2, I3, I4, I5], E, Z, !Env) :-
    Index1Range = int_set_to_index_range(Context, !.Env ^ env_globals, I1),
    Index2Range = int_set_to_index_range(Context, !.Env ^ env_globals, I2),
    Index3Range = int_set_to_index_range(Context, !.Env ^ env_globals, I3),
    Index4Range = int_set_to_index_range(Context, !.Env ^ env_globals, I4),
    Index5Range = int_set_to_index_range(Context, !.Env ^ env_globals, I5),
    NewIndexRanges = [Index1Range, Index2Range, Index3Range, Index4Range,
        Index5Range],
    NewN = index_ranges_to_size(NewIndexRanges),
    ( E = array_items(OldIndexRanges, _)
    ; E = array_var(OldIndexRanges, _)
    ),
    OldN = index_ranges_to_size(OldIndexRanges),
    ( if NewN = OldN then
        (
            E = array_items(_, Items),
            Z = array_items(NewIndexRanges, Items)
        ;
            E = array_var(_, VarId),
            Z = array_var(NewIndexRanges, VarId)
        )
    else
        string.format("Array size mismatch: expected %d, actual %d.\n",
            [i(NewN), i(OldN)], Msg),
        minizinc_user_error(Context, Msg)
    ).

flatten_array_redim(Context, _Anns, "array6d", [I1, I2, I3, I4, I5, I6], E, Z, !Env) :-
    Index1Range = int_set_to_index_range(Context, !.Env ^ env_globals, I1),
    Index2Range = int_set_to_index_range(Context, !.Env ^ env_globals, I2),
    Index3Range = int_set_to_index_range(Context, !.Env ^ env_globals, I3),
    Index4Range = int_set_to_index_range(Context, !.Env ^ env_globals, I4),
    Index5Range = int_set_to_index_range(Context, !.Env ^ env_globals, I5),
    Index6Range = int_set_to_index_range(Context, !.Env ^ env_globals, I6),
    NewIndexRanges = [Index1Range, Index2Range, Index3Range, Index4Range,
        Index5Range, Index6Range],
    NewN = index_ranges_to_size(NewIndexRanges),
    ( E = array_items(OldIndexRanges, _)
    ; E = array_var(OldIndexRanges, _)
    ),
    OldN = index_ranges_to_size(OldIndexRanges),
    ( if NewN = OldN then
        (
            E = array_items(_, Items),
            Z = array_items(NewIndexRanges, Items)
        ;
            E = array_var(_, VarId),
            Z = array_var(NewIndexRanges, VarId)
        )
    else
        string.format("Array size mismatch: expected %d, actual %d.\n",
            [i(NewN), i(OldN)], Msg),
        minizinc_user_error(Context, Msg)
    ).

%-----------------------------------------------------------------------------%

flatten_float_array_to_float(Context, Anns, "sum", A0, Z, !Env) :-
    A = fully_deref_float_array(Context, A0, !.Env),
    (
        A = array_items(_, Items)
    ;
        A = array_var(IndexRanges, VarId),
        N = index_ranges_to_size(IndexRanges),
        F = (func(I) = float_var(var_index(VarId, I + 1))),
        Items = array.generate(N, F)
    ),
    array.foldl2(flatten_float_float_to_float(Context, Anns, ff2f_add),
        Items, float_const(0.0), Z, !Env).

flatten_float_array_to_float(Context, Anns, "product", A0, Z, !Env) :-
    A = fully_deref_float_array(Context, A0, !.Env),
    (
        A = array_items(_, Items)
    ;
        A = array_var(IndexRanges, VarId),
        N = index_ranges_to_size(IndexRanges),
        F = (func(I) = float_var(var_index(VarId, I + 1))),
        Items = array.generate(N, F)
    ),
    array.foldl2(flatten_float_float_to_float(Context, Anns, ff2f_mul),
        Items, float_const(1.0), Z, !Env).

flatten_float_array_to_float(Context, Anns, "min", A0, Z, !Env) :-
    A = fully_deref_float_array(Context, A0, !.Env),
    (
        A = array_items(_, Items)
    ;
        A = array_var(IndexRanges, VarId),
        N = index_ranges_to_size(IndexRanges),
        F = (func(I) = float_var(var_index(VarId, I + 1))),
        Items = array.generate(N, F)
    ),
    ( if array.size(Items) = 0 then
        minizinc_user_error(Context, "Array is empty.\n")
    else
        Item0 = Items ^ unsafe_elem(0),
        array.foldl2(
            flatten_float_float_to_float(Context, Anns, ff2f_min),
            Items, Item0, Z, !Env)
    ).

flatten_float_array_to_float(Context, Anns, "max", A0, Z, !Env) :-
    A = fully_deref_float_array(Context, A0, !.Env),
    (
        A = array_items(_, Items)
    ;
        A = array_var(IndexRanges, VarId),
        N = index_ranges_to_size(IndexRanges),
        F = (func(I) = float_var(var_index(VarId, I + 1))),
        Items = array.generate(N, F)
    ),
    ( if array.size(Items) = 0 then
        minizinc_user_error(Context, "Array is empty.\n")
    else
        Item0 = Items ^ unsafe_elem(0),
        array.foldl2(
            flatten_float_float_to_float(Context, Anns, ff2f_max),
            Items, Item0, Z, !Env)
    ).

flatten_float_array_to_float(Context, Anns, "lb_array", A0, Z, !Env) :-
    A = fully_deref_float_array(Context, A0, !.Env),
    (
        A = array_var(_, VarId),
        LB = !.Env ^ var_float_lb(VarId),
        Z = float_const(LB)
    ;
        A = array_items(_, Items),
        ( if array.size(Items) = 0 then
            minizinc_user_error(Context, "Array is empty.\n")
        else
            array.foldl2(
                find_float_extremal_bound(Context, Anns, f2f_lb, ff2f_min),
                Items, float_const(float_plus_infinity), Z, !Env)
        )
    ).

flatten_float_array_to_float(Context, Anns, "ub_array", A0, Z, !Env) :-
    A = fully_deref_float_array(Context, A0, !.Env),
    (
        A = array_var(_, VarId),
        UB = !.Env ^ var_float_ub(VarId),
        Z = float_const(UB)
    ;
        A = array_items(_, Items),
        ( if array.size(Items) = 0 then
            minizinc_user_error(Context, "Array is empty.\n")
        else
            array.foldl2(
                find_float_extremal_bound(Context, Anns, f2f_ub, ff2f_max),
                Items, float_const(float_minus_infinity), Z, !Env)
        )
    ).

%-----------------------------------------------------------------------------%

:- pred find_float_extremal_bound(error_context::in, mzn_anns::in,
    float_to_float_op::in, float_float_to_float_op::in,
    float_expr::in, float_expr::in,
    float_expr::out, env::in, env::out) is semidet.

find_float_extremal_bound(Context, Anns, LBorUB, MinMax, A, B, Z, !Env) :-
    flatten_float_to_float(Context, Anns, LBorUB, A, C, !Env),
    flatten_float_float_to_float(Context, Anns, MinMax, C, B, Z, !Env).

%-----------------------------------------------------------------------------%

flatten_int_array_to_int(Context, Anns, Op, A0, Z, !Env) :-
    (
        Op = "sum",
        A = fully_deref_int_array(Context, A0, !.Env),
        (
            A = array_items(_, Items)
        ;
            A = array_var(IndexRanges, VarId),
            N = index_ranges_to_size(IndexRanges),
            F = (func(I) = int_var(var_index(VarId, I + 1))),
            Items = array.generate(N, F)
        ),
        array.foldl2(flatten_int_int_to_int(Context, Anns, ii2i_add), Items,
            int_const(0), Z, !Env)
    ;
        Op = "product",
        A = fully_deref_int_array(Context, A0, !.Env),
        (
            A = array_items(_, Items)
        ;
            A = array_var(IndexRanges, VarId),
            N = index_ranges_to_size(IndexRanges),
            F = (func(I) = int_var(var_index(VarId, I + 1))),
            Items = array.generate(N, F)
        ),
        array.foldl2(flatten_int_int_to_int(Context, Anns, ii2i_mul), Items,
            int_const(1), Z, !Env)
    ;
        Op = "min",
        A = fully_deref_int_array(Context, A0, !.Env),
        (
            A = array_items(_, Items)
        ;
            A = array_var(IndexRanges, VarId),
            N = index_ranges_to_size(IndexRanges),
            F = (func(I) = int_var(var_index(VarId, I + 1))),
            Items = array.generate(N, F)
        ),
        ( if array.size(Items) = 0 then
            minizinc_user_error(Context, "Array is empty.\n")
        else
            Item0 = Items ^ unsafe_elem(0),
            array.foldl2(flatten_int_int_to_int(Context, Anns, ii2i_min),
                Items, Item0, Z, !Env)
        )
    ;
        Op = "max",
        A = fully_deref_int_array(Context, A0, !.Env),
        (
            A = array_items(_, Items)
        ;
            A = array_var(IndexRanges, VarId),
            N = index_ranges_to_size(IndexRanges),
            F = (func(I) = int_var(var_index(VarId, I + 1))),
            Items = array.generate(N, F)
        ),
        ( if array.size(Items) = 0 then
            minizinc_user_error(Context, "Array is empty.\n")
        else
            Item0 = Items ^ unsafe_elem(0),
            array.foldl2(flatten_int_int_to_int(Context, Anns, ii2i_max),
                Items, Item0, Z, !Env)
        )
    ;
        Op = "lb",
        flatten_int_array_to_int(Context, Anns, "lb_array", A0, Z, !Env)
    ;
        Op = "ub",
        flatten_int_array_to_int(Context, Anns, "ub_array", A0, Z, !Env)
    ;
        Op = "lb_array",
        (
            A0 = array_var(_, VarId),
            LB = !.Env ^ var_int_lb(VarId),
            Z = int_const(LB)
        ;
            A0 = array_items(_, Items),
            ( if array.size(Items) = 0 then
                minizinc_user_error(Context, "Array is empty.\n")
            else
                array.foldl2(
                    find_int_extremal_bound(Context, Anns, i2i_lb, ii2i_min),
                    Items, int_const(int_plus_infinity), Z, !Env)
            )
        )
    ;
        Op = "ub_array",
        (
            A0 = array_var(_, VarId),
            UB = !.Env ^ var_int_ub(VarId),
            Z = int_const(UB)
        ;
            A0 = array_items(_, Items),
            ( if array.size(Items) = 0 then
                minizinc_user_error(Context, "Array is empty.\n")
            else
                array.foldl2(
                    find_int_extremal_bound(Context, Anns, i2i_ub, ii2i_max),
                    Items, int_const(int_minus_infinity), Z, !Env)
            )
        )
    ).

:- pred find_int_extremal_bound(error_context::in, mzn_anns::in,
    int_to_int_op::in, int_int_to_int_op::in, int_expr::in, int_expr::in,
    int_expr::out, env::in, env::out) is semidet.

find_int_extremal_bound(Context, Anns, LBorUB, MinMax, A, B, Z, !Env) :-
    flatten_int_to_int(Context, Anns, LBorUB, A, C, !Env),
    flatten_int_int_to_int(Context, Anns, MinMax, C, B, Z, !Env).

%-----------------------------------------------------------------------------%

:- pred flatten_int_set_array_to_int(error_context::in, mzn_anns::in,
    string::in, int_set_array_expr::in,
    int_expr::out, env::in, env::out) is semidet.

flatten_int_set_array_to_int(Context, Anns, "min", A, Z, !Env) :-
    (
        A = array_var(_, VarId),
        LB = !.Env ^ var_int_lb(VarId),
        Z = int_const(LB)
    ;
        A = array_items(_, Items),
        ( if array.size(Items) = 0 then
            Z = int_const(int_minus_infinity)
        else
            array.foldl2(
                find_int_set_extremal_bound(Context, Anns,
                    is2i_min, ii2i_min),
                Items, int_const(int_plus_infinity), Z, !Env)
        )
    ).
flatten_int_set_array_to_int(Context, Anns, "max", A, Z, !Env) :-
    (
        A = array_var(_, VarId),
        UB = !.Env ^ var_int_ub(VarId),
        Z = int_const(UB)
    ;
        A = array_items(_, Items),
        ( if array.size(Items) = 0 then
            Z = int_const(int_plus_infinity)
        else
            array.foldl2(
                find_int_set_extremal_bound(Context, Anns,
                    is2i_max, ii2i_max),
                Items, int_const(int_minus_infinity), Z, !Env)
        )
    ).

:- pred find_int_set_extremal_bound(error_context::in, mzn_anns::in,
    int_set_to_int_op::in, int_int_to_int_op::in,
    int_set_expr::in, int_expr::in,
    int_expr::out, env::in, env::out) is semidet.

find_int_set_extremal_bound(Context, Anns, IS2I_MinMax, II2I_MinMax,
        A, B, Z, !Env) :-
    flatten_int_set_to_int(Context, Anns, IS2I_MinMax, A, C, !Env),
    flatten_int_int_to_int(Context, Anns, II2I_MinMax, C, B, Z, !Env).

%-----------------------------------------------------------------------------%

flatten_string_array_to_string(Context, _Anns, "concat", A, Z, !Env) :-
    (
        A = array_var(_, _VarId),
        minizinc_internal_error(Context, $pred, "string var array?")
    ;
        A = array_items(_, Items)
    ),
    ItemList = array.to_list(Items),
    Z = string_concat(ItemList).

%-----------------------------------------------------------------------------%

flatten_string_string_array_to_string(Context, _Anns, "join", A, B, Z,
        !Env) :-
    (
        B = array_var(_, _VarId),
        minizinc_internal_error(Context, $pred, "string var array?")
    ;
        B = array_items(_, Items)
    ),
    ItemList = array.to_list(Items),
    Z = string_join(A, ItemList).

%-----------------------------------------------------------------------------%

flatten_array_to_int_set(Context, _Anns, Op, A, Z, !Env) :-
    ( Op = "index_set",       ExpectedDims = 1, ResultDim = 1
    ; Op = "index_set_1of2",  ExpectedDims = 2, ResultDim = 1
    ; Op = "index_set_2of2",  ExpectedDims = 2, ResultDim = 2
    ; Op = "index_set_1of3",  ExpectedDims = 3, ResultDim = 1
    ; Op = "index_set_2of3",  ExpectedDims = 3, ResultDim = 2
    ; Op = "index_set_3of3",  ExpectedDims = 3, ResultDim = 3
    ; Op = "index_set_1of4",  ExpectedDims = 4, ResultDim = 1
    ; Op = "index_set_2of4",  ExpectedDims = 4, ResultDim = 2
    ; Op = "index_set_3of4",  ExpectedDims = 4, ResultDim = 3
    ; Op = "index_set_4of4",  ExpectedDims = 4, ResultDim = 4
    ),
    ( A = array_items(IndexRanges, _)
    ; A = array_var(IndexRanges, _)
    ),
    NumDims = list.length(IndexRanges),
    ( if NumDims = ExpectedDims then
        index_range(LB, UB) = list.det_index1(IndexRanges, ResultDim),
        % XXX This code used to be:
        %
        % Z = set_items(set.from_sorted_list(LB..UB))
        % 
        % We use the following work around to avoid stack overflows in
        % from_sorted_list/1.
        % (The problem and workaround here are identical that to that in
        % flatten_int_int_to_int_set/8.  See the comments in that predicate
        % for further details.)
        %
        Range = LB..UB,
        Set = evil_list_to_set(Range),
        Z = set_items(Set)
    else
        minizinc_user_error(Context,
            string.format("Expected %d dimensions, found %d.\n",
                [i(ExpectedDims), i(NumDims)]))
    ).

flatten_array_to_int_set(Context, Anns, "dom_array", A0, Z, !Env) :-
    ( if dynamic_cast(A0, A : array_expr(int_expr)) then
        flatten_int_array_to_int(Context, Anns, "lb_array", A, int_const(LB),
            !Env),
        flatten_int_array_to_int(Context, Anns, "ub_array", A, int_const(UB),
            !Env),
        % Try to avoid creating ridiculous sets.
        ( if LB + 999 < UB then
            minizinc_user_error(Context,
                "Domain size is too large to represent as a set.\n")
        else
            Z = set_items(set.sorted_list_to_set(LB..UB))
        )
    else
        minizinc_user_error(Context,
            "'dom_array' is only applicable to variables of type\n" ++
            "array of int, or array of set of int.\n")
    ).
    
:- func evil_list_to_set(list(int)) = set(int).
:- pragma foreign_proc("C",
    evil_list_to_set(L::in) = (S::out),
    [will_not_call_mercury, promise_pure],
"
    S = L;
").

%-----------------------------------------------------------------------------%

flatten_bool_set_array_to_set(Context, Anns, Name, A0, Z, !Env) :-
    A = fully_deref_bool_set_array(Context, A0, !.Env),
    flatten_set_array_to_set(Context, Anns, Name, A, Z, !Env).

%-----------------------------------------------------------------------------%

flatten_float_set_array_to_set(Context, Anns, Name, A0, Z, !Env) :-
    A = fully_deref_float_set_array(Context, A0, !.Env),
    flatten_set_array_to_set(Context, Anns, Name, A, Z, !Env).

%-----------------------------------------------------------------------------%

flatten_int_set_array_to_set(Context, Anns, Name, A0, Z, !Env) :-
    A = fully_deref_int_set_array(Context, A0, !.Env),
    flatten_set_array_to_set(Context, Anns, Name, A, Z, !Env).

%-----------------------------------------------------------------------------%

    % The array must be fully dereferenced before calling this predicate.
    %
:- pred flatten_set_array_to_set(error_context::in, mzn_anns::in,
    string::in, array_expr(set_expr(T))::in,
    set_expr(T)::out, env::in, env::out) is semidet.

flatten_set_array_to_set(Context, Anns, "array_union", A, Z, !Env) :-
    (
        A = array_items(_, Items),
        Z0 = set_items(set.init),
        array.foldl2(flatten_set_set_to_set(Context, Anns, xsxs2xs_union),
            Items, Z0, Z, !Env)
    ;
        A = array_var(IndexRanges, VarId),
        N = index_ranges_to_size(IndexRanges),
        F = (func(I) = set_var(var_index(VarId, I + 1))),
        Items = array.generate(N, F),
        flatten_set_array_to_set(Context, Anns, "array_union",
            array_items(IndexRanges, Items), Z, !Env)
    ).

flatten_set_array_to_set(Context, Anns, "array_intersect", A, Z, !Env) :-
    (
        A = array_items(_, Items),
        ( if array.size(Items) = 0 then
            Z = set_items(set.init)
        else
            Item0 = Items ^ unsafe_elem(0),
            array.foldl2(
                flatten_set_set_to_set(Context, Anns, xsxs2xs_intersect),
                Items, Item0, Z, !Env)
        )
    ;
        A = array_var(IndexRanges, VarId),
        N = index_ranges_to_size(IndexRanges),
        F = (func(I) = set_var(var_index(VarId, I + 1))),
        Items = array.generate(N, F),
        flatten_set_array_to_set(Context, Anns, "array_intersect",
            array_items(IndexRanges, Items), Z, !Env)
    ).

%-----------------------------------------------------------------------------%

flatten_array_array_to_array(FullyDeref, MkElem, Context, _Anns, "++", A0, B0,
        Z, !Env) :-
    A = FullyDeref(Context, A0, !.Env),
    B = FullyDeref(Context, B0, !.Env),
    (
        A = array_items(_IndexRangesA, ItemsA)
    ;
        A = array_var(IndexRangesA, VarIdA),
        FA = (func(I) = MkElem(var_index(VarIdA, I + 1))),
        NA = index_ranges_to_size(IndexRangesA),
        ItemsA = array.generate(NA, FA)
    ),
    (
        B = array_items(_IndexRangesB, ItemsB)
    ;
        B = array_var(IndexRangesB, VarIdB),
        FB = (func(I) = MkElem(var_index(VarIdB, I + 1))),
        NB = index_ranges_to_size(IndexRangesB),
        ItemsB = array.generate(NB, FB)
    ),
    Items = array.append(ItemsA, ItemsB),
    N = array.size(Items),
    IndexRanges = [index_range(1, N)],
    Z = array_items(IndexRanges, Items).

%-----------------------------------------------------------------------------%

flatten_arbitrary_array_to_int(_Context, _Anns, "length", A, Z, !Env) :-
    ( A = array_items(IndexRanges, _)
    ; A = array_var(IndexRanges, _)
    ),
    Z = int_const(index_ranges_to_size(IndexRanges)).

%-----------------------------------------------------------------------------%
:- end_module flatten.array.
%-----------------------------------------------------------------------------%
