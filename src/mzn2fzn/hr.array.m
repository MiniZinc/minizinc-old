%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
% We divide up the cases for flattening built-in operators by type and by
% call inst (e.g., par par/par var/var par/var var/var).
%
%-----------------------------------------------------------------------------%

:- module hr.array.
:- interface.

:- import_module errors.
:- import_module hr.info.
:- import_module types.

:- import_module types_and_insts.

:- import_module list.

%-----------------------------------------------------------------------------%

:- pred halfreify_array_access(error_context::in, mzn_anns::in, ilhs::in,
    type_inst::in, mzn_expr::in, list(mzn_expr)::in, mzn_expr::out,
    mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

%-----------------------------------------------------------------------------%

    % We don't fully expand global variables bound to literal array values
    % in order to avoid duplicating the same array multiple times in the
    % FlatZinc model. However, sometimes it is necessary to do so, hence
    % these functions.
    %
:- func hr_fully_deref_bool_array(hr_info, model, error_context,
    bool_array_expr) = bool_array_expr.

:- func hr_fully_deref_float_array(hr_info, model, error_context,
    float_array_expr) = float_array_expr.

:- func hr_fully_deref_int_array(hr_info, model, error_context,
    int_array_expr) = int_array_expr.

:- func hr_fully_deref_bool_set_array(hr_info, model, error_context,
    bool_set_array_expr) = bool_set_array_expr.

:- func hr_fully_deref_float_set_array(hr_info, model, error_context,
    float_set_array_expr) = float_set_array_expr.

:- func hr_fully_deref_int_set_array(hr_info, model, error_context,
    int_set_array_expr) = int_set_array_expr.

:- func hr_fully_deref_string_array(hr_info, model, error_context,
    string_array_expr) = string_array_expr.

:- func hr_fully_deref_ann_array(hr_info, model, error_context,
    ann_array_expr) = ann_array_expr.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module common_array.
:- import_module common_bounds.
:- import_module hr.float.
:- import_module hr.int.
:- import_module mzn_ops.
% :- import_module flatten.ann.
% :- import_module flatten.bool.
% :- import_module flatten.expr.
% :- import_module flatten.set.
% :- import_module flatten.string.

:- import_module intset.

:- import_module array.
:- import_module bool.
:- import_module float.
:- import_module int.
:- import_module map.
:- import_module maybe.
:- import_module set.
:- import_module string.
:- import_module unit.

%-----------------------------------------------------------------------------%

halfreify_array_access(Context, OutsideAnns, ILHS, TI, MZA, IndexMZs, MZ,
        AllConstraints, KnownFalse, !Info, !Model) :-
    AccessContext = [["In array access.\n"] | Context],
    Indexes = list.map(mzn_expr_to_int(AccessContext), IndexMZs),
    type_inst_to_mzn_type(Context, TI, _VarPar, MZType),
    ( if
        (
            MZType = mzn_bool,
            A = mzn_expr_to_bool_array(AccessContext, MZA),
            halfreify_bool_array_lookup(AccessContext, OutsideAnns, ILHS,
                A, Indexes, Z, AllConstraints0, KnownFalse0, !Info, !Model),
            MZ0 = bool_to_mzn_expr(Z)
        ;
            MZType = mzn_float(_),
            A = mzn_expr_to_float_array(AccessContext, MZA),
            halfreify_float_array_lookup(AccessContext, OutsideAnns, ILHS,
                A, Indexes, Z, AllConstraints0, KnownFalse0, !Info, !Model),
            MZ0 = float_to_mzn_expr(Z)
        ;
            MZType = mzn_int(_),
            A = mzn_expr_to_int_array(AccessContext, MZA),
            halfreify_int_array_lookup(AccessContext, OutsideAnns, ILHS,
                A, Indexes, Z, AllConstraints0, KnownFalse0, !Info, !Model),
            MZ0 = int_to_mzn_expr(Z)
        ;
            MZType = mzn_bool_set,
            A = mzn_expr_to_bool_set_array(AccessContext, MZA),
            halfreify_bool_set_array_lookup(AccessContext, OutsideAnns, ILHS,
                A, Indexes, Z, AllConstraints0, KnownFalse0, !Info, !Model),
            MZ0 = bool_set_to_mzn_expr(Z)
        ;
            MZType = mzn_float_set(_),
            A = mzn_expr_to_float_set_array(AccessContext, MZA),
            halfreify_float_set_array_lookup(AccessContext, OutsideAnns, ILHS,
                A, Indexes, Z, AllConstraints0, KnownFalse0, !Info, !Model),
            MZ0 = float_set_to_mzn_expr(Z)
        ;
            MZType = mzn_int_set(_),
            A = mzn_expr_to_int_set_array(AccessContext, MZA),
            halfreify_int_set_array_lookup(AccessContext, OutsideAnns, ILHS,
                A, Indexes, Z, AllConstraints0, KnownFalse0, !Info, !Model),
            MZ0 = int_set_to_mzn_expr(Z)
        ;
            MZType = mzn_string,
            A = mzn_expr_to_string_array(AccessContext, MZA),
            halfreify_string_array_lookup(AccessContext, OutsideAnns, ILHS,
                A, Indexes, Z, AllConstraints0, KnownFalse0, !Info, !Model),
            MZ0 = string_to_mzn_expr(Z)
        ;
            MZType = mzn_ann,
            A = mzn_expr_to_ann_array(AccessContext, MZA),
            halfreify_ann_array_lookup(AccessContext, OutsideAnns, ILHS,
                A, Indexes, Z, AllConstraints0, KnownFalse0, !Info, !Model),
            MZ0 = ann_to_mzn_expr(Z)
        )
    then
        MZ = MZ0,
        AllConstraints = AllConstraints0,
        KnownFalse = KnownFalse0
    else
        minizinc_user_error(AccessContext,
            "Array accesses not supported for this type.\n")
    ).

%-----------------------------------------------------------------------------%

:- pred halfreify_bool_array_lookup(error_context::in, mzn_anns::in,
    ilhs::in, bool_array_expr::in, list(int_expr)::in,
    bool_expr::out, mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

:- pred halfreify_float_array_lookup(error_context::in, mzn_anns::in,
    ilhs::in, float_array_expr::in, list(int_expr)::in,
    float_expr::out, mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

:- pred halfreify_int_array_lookup(error_context::in, mzn_anns::in,
    ilhs::in, int_array_expr::in, list(int_expr)::in,
    int_expr::out, mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

:- pred halfreify_bool_set_array_lookup(error_context::in, mzn_anns::in,
    ilhs::in, bool_set_array_expr::in, list(int_expr)::in,
    bool_set_expr::out, mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

:- pred halfreify_float_set_array_lookup(error_context::in, mzn_anns::in,
    ilhs::in, float_set_array_expr::in, list(int_expr)::in,
    float_set_expr::out, mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

:- pred halfreify_int_set_array_lookup(error_context::in, mzn_anns::in,
    ilhs::in, int_set_array_expr::in, list(int_expr)::in,
    int_set_expr::out, mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

:- pred halfreify_string_array_lookup(error_context::in, mzn_anns::in,
    ilhs::in, string_array_expr::in, list(int_expr)::in,
    string_expr::out, mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

:- pred halfreify_ann_array_lookup(error_context::in, mzn_anns::in,
    ilhs::in, ann_array_expr::in, list(int_expr)::in,
    mzn_ann::out, mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

halfreify_bool_array_lookup(Context, OutsideAnns, ILHS, ArrayExpr0,
        IndexExprs, Z, AllConstraints, KnownFalse, !Info, !Model) :-
    ArrayExpr =
        hr_fully_deref_bool_array(!.Info, !.Model, Context, ArrayExpr0),
    TypeName = "bool",
    IsGround = bool_is_par,
    ArrayElemBounds = bool_array_bounds(Context),
    AddTmpVar = hr_add_tmp_bool_var,
    DefaultValue = bool_const(no),
    MznArrayExpr = bool_array_to_mzn_expr,
    ElemExpr = ( func(V, I) = bool_var(var_index(V, I)) ),
    halfreify_array_lookup(Context, OutsideAnns, ILHS, TypeName,
        IsGround, ArrayElemBounds, AddTmpVar, DefaultValue,
        MznArrayExpr, ElemExpr, ArrayExpr0, ArrayExpr, IndexExprs, Z,
        AllConstraints, KnownFalse, !Info, !Model).

halfreify_float_array_lookup(Context, OutsideAnns, ILHS, ArrayExpr0,
        IndexExprs, Z, AllConstraints, KnownFalse, !Info, !Model) :-
    ArrayExpr =
        hr_fully_deref_float_array(!.Info, !.Model, Context, ArrayExpr0),
    TypeName = "float",
    IsGround = float_is_par,
    ArrayElemBounds = float_array_bounds(Context),
    AddTmpVar = hr_add_tmp_float_var,
    DefaultValue = float_const(0.0),
    MznArrayExpr = float_array_to_mzn_expr,
    ElemExpr = ( func(V, I) = float_var(var_index(V, I)) ),
    halfreify_array_lookup(Context, OutsideAnns, ILHS, TypeName,
        IsGround, ArrayElemBounds, AddTmpVar, DefaultValue,
        MznArrayExpr, ElemExpr, ArrayExpr0, ArrayExpr, IndexExprs, Z,
        AllConstraints, KnownFalse, !Info, !Model).

halfreify_int_array_lookup(Context, OutsideAnns, ILHS, ArrayExpr0,
        IndexExprs, Z, AllConstraints, KnownFalse, !Info, !Model) :-
    ArrayExpr = hr_fully_deref_int_array(!.Info, !.Model, Context, ArrayExpr0),
    TypeName = "int",
    IsGround = int_is_par,
    ArrayElemBounds = int_array_bounds(Context),
    AddTmpVar = hr_add_tmp_int_var,
    DefaultValue = int_const(0),
    MznArrayExpr = int_array_to_mzn_expr,
    ElemExpr = ( func(V, I) = int_var(var_index(V, I)) ),
    halfreify_array_lookup(Context, OutsideAnns, ILHS, TypeName,
        IsGround, ArrayElemBounds, AddTmpVar, DefaultValue,
        MznArrayExpr, ElemExpr, ArrayExpr0, ArrayExpr, IndexExprs, Z,
        AllConstraints, KnownFalse, !Info, !Model).

halfreify_bool_set_array_lookup(Context, OutsideAnns, ILHS, ArrayExpr0,
        IndexExprs, Z, AllConstraints, KnownFalse, !Info, !Model) :-
    ArrayExpr =
        hr_fully_deref_bool_set_array(!.Info, !.Model, Context, ArrayExpr0),
    TypeName = "set",
    IsGround = bool_set_is_par,
    ArrayElemBounds = bool_set_array_bounds(Context),
    AddTmpVar = hr_var_type_unsupported("set of bool"),
    DefaultValue = set_items(set.init),
    MznArrayExpr = bool_set_array_to_mzn_expr,
    ElemExpr = ( func(V, I) = set_var(var_index(V, I)) ),
    halfreify_array_lookup(Context, OutsideAnns, ILHS, TypeName,
        IsGround, ArrayElemBounds, AddTmpVar, DefaultValue,
        MznArrayExpr, ElemExpr, ArrayExpr0, ArrayExpr, IndexExprs, Z,
        AllConstraints, KnownFalse, !Info, !Model).

halfreify_float_set_array_lookup(Context, OutsideAnns, ILHS, ArrayExpr0,
        IndexExprs, Z, AllConstraints, KnownFalse, !Info, !Model) :-
    ArrayExpr =
        hr_fully_deref_float_set_array(!.Info, !.Model, Context, ArrayExpr0),
    TypeName = "set",
    IsGround = float_set_is_par,
    ArrayElemBounds = float_set_array_bounds(Context),
    AddTmpVar = hr_var_type_unsupported("set of float"),
    DefaultValue = set_items(set.init),
    MznArrayExpr = float_set_array_to_mzn_expr,
    ElemExpr = ( func(V, I) = set_var(var_index(V, I)) ),
    halfreify_array_lookup(Context, OutsideAnns, ILHS, TypeName,
        IsGround, ArrayElemBounds, AddTmpVar, DefaultValue,
        MznArrayExpr, ElemExpr, ArrayExpr0, ArrayExpr, IndexExprs, Z,
        AllConstraints, KnownFalse, !Info, !Model).

halfreify_int_set_array_lookup(Context, OutsideAnns, ILHS, ArrayExpr0,
        IndexExprs, Z, AllConstraints, KnownFalse, !Info, !Model) :-
    ArrayExpr =
        hr_fully_deref_int_set_array(!.Info, !.Model, Context, ArrayExpr0),
    TypeName = "set",
    IsGround = int_set_is_par,
    ArrayElemBounds = int_set_array_bounds(Context),
    AddTmpVar = hr_add_tmp_int_set_var,
    DefaultValue = set_items(set.init),
    MznArrayExpr = int_set_array_to_mzn_expr,
    ElemExpr = ( func(V, I) = set_var(var_index(V, I)) ),
    halfreify_array_lookup(Context, OutsideAnns, ILHS, TypeName,
        IsGround, ArrayElemBounds, AddTmpVar, DefaultValue,
        MznArrayExpr, ElemExpr, ArrayExpr0, ArrayExpr, IndexExprs, Z,
        AllConstraints, KnownFalse, !Info, !Model).

halfreify_string_array_lookup(Context, OutsideAnns, ILHS, ArrayExpr0,
        IndexExprs, Z, AllConstraints, KnownFalse, !Info, !Model) :-
    ArrayExpr =
        hr_fully_deref_string_array(!.Info, !.Model, Context, ArrayExpr0),
    TypeName = "string",
    IsGround = string_is_par,
    ArrayElemBounds = string_array_bounds(Context),
    AddTmpVar = hr_add_tmp_string_var,
    DefaultValue = string_const(""),
    MznArrayExpr = string_array_to_mzn_expr,
    ElemExpr = ( func(_, _) = _ :-
        minizinc_internal_error(Context, $pred,
            "ElemExpr should not be called!")
    ),
    halfreify_array_lookup(Context, OutsideAnns, ILHS, TypeName,
        IsGround, ArrayElemBounds, AddTmpVar, DefaultValue,
        MznArrayExpr, ElemExpr, ArrayExpr0, ArrayExpr, IndexExprs, Z,
        AllConstraints, KnownFalse, !Info, !Model).

halfreify_ann_array_lookup(Context, OutsideAnns, ILHS, ArrayExpr0,
        IndexExprs, Z, AllConstraints, KnownFalse, !Info, !Model) :-
    ArrayExpr = hr_fully_deref_ann_array(!.Info, !.Model, Context, ArrayExpr0),
    TypeName = "ann",
    IsGround = ann_is_par,
    ArrayElemBounds = ann_array_bounds(Context),
    AddTmpVar = hr_add_tmp_ann_var,
    DefaultValue = mzn_ann("dummy", []),
    MznArrayExpr = ann_array_to_mzn_expr,
    ElemExpr = ( func(_, _) = _ :-
        minizinc_internal_error(Context, $pred,
            "ElemExpr should not be called!")
    ),
    halfreify_array_lookup(Context, OutsideAnns, ILHS, TypeName,
        IsGround, ArrayElemBounds, AddTmpVar, DefaultValue,
        MznArrayExpr, ElemExpr, ArrayExpr0, ArrayExpr, IndexExprs, Z,
        AllConstraints, KnownFalse, !Info, !Model).

:- pred hr_var_type_unsupported(string::in, error_context::in, mzn_anns::in, 
    ilhs::in, BoundsT::in, string::in, mzn_exprs::in, mzn_anns::in,
    var_id::out, ElemT::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

hr_var_type_unsupported(VarTypeName, Context, _, _, _, _, _, _, _, _, _,
        !Info, !Model) :-
    minizinc_user_error(Context, "Variables of type var " ++ VarTypeName ++
        " are not supported in FlatZinc.\n").

%-----------------------------------------------------------------------------%

:- pred halfreify_array_lookup(error_context::in, mzn_anns::in,
    ilhs::in, string::in, pred(ElemT)::in(pred(in) is semidet),
    (func(global_var_map, array_expr(ElemT)) = BoundsT)::in,
    pred(error_context, mzn_anns, ilhs, BoundsT,
        string, list(mzn_expr), mzn_anns,
        var_id, ElemT, mzn_constraint_set, hr_info, hr_info, model, model)::
    in(pred(in, in, in, in, in, in, in, out, out, out, in, out, in, out)
        is det),
    ElemT::in,
    (func(array_expr(ElemT)) = mzn_expr)::in,
    (func(var_id, int) = ElemT)::in,
    array_expr(ElemT)::in, array_expr(ElemT)::in, list(int_expr)::in,
    ElemT::out, mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

halfreify_array_lookup(Context, OutsideAnns, ILHS, TypeName,
        IsGround, ArrayElemBounds, AddTmpVar, DefaultValue, MznArrayExpr,
        ElemExpr, ArrayExpr0, ArrayExpr, IndexExprs, Z,
        AllConstraints, KnownFalse, !Info, !Model) :-
    % XXX Why does one of the calls to halfreify_array_lookup_var pass
    % ArrayExpr0 and the other ArrayExpr?
    (
        ArrayExpr = array_items(IndexRanges, Xs),
        hr_flatten_array_indices_to_int(Context, OutsideAnns, ILHS,
            IndexRanges, IndexExprs, OffsetExpr,
            OffsetConstraints, OffsetKnownFalse, !Info, !Model),
        ( if OffsetExpr = int_const(Offset) then
            halfreify_array_lookup_par_par(Context, ILHS, DefaultValue,
                Xs, Offset, Z, LookupKnownFalse),
            AllConstraints = OffsetConstraints,
            KnownFalse = combine_known_to_be_false(OffsetKnownFalse,
                LookupKnownFalse)
        else
            ( if
                (
                    ArrayExpr0 = array_var(_, ArrayVar),
                    map.lookup(!.Model ^ model_globals, ArrayVar, VarInfo),
                    VarInfo ^ vi_inst = var_is_var
                ;
                    some [X] ( array.member(Xs, X) => not IsGround(X) )
                )
            then
                ConstraintName = "array_var_" ++ TypeName ++ "_element"
            else
                ConstraintName = "array_" ++ TypeName ++ "_element"
            ),
            halfreify_array_lookup_var(Context, OutsideAnns, ILHS,
                ConstraintName, ArrayElemBounds, AddTmpVar, MznArrayExpr,
                ArrayExpr0, OffsetExpr, Z, LookupConstraints, !Info, !Model),
            mzn_constraint_set_union(OffsetConstraints, LookupConstraints,
                AllConstraints),
            KnownFalse = not_known_to_be_false
        )
    ;
        ArrayExpr = array_var(IndexRanges, ArrayVar),
        hr_flatten_array_indices_to_int(Context, OutsideAnns, ILHS,
            IndexRanges, IndexExprs, OffsetExpr,
            OffsetConstraints, OffsetKnownFalse, !Info, !Model),
        ( if OffsetExpr = int_const(Offset) then
            Z = ElemExpr(ArrayVar, Offset),
            AllConstraints = OffsetConstraints,
            KnownFalse = OffsetKnownFalse
        else
            map.lookup(!.Model ^ model_globals, ArrayVar, ArrayVarInfo),
            ArrayVarInst = ArrayVarInfo ^ vi_inst,
            (
                ArrayVarInst = var_is_var,
                ConstraintName = "array_var_" ++ TypeName ++ "_element"
            ;
                ArrayVarInst = var_is_par,
                ConstraintName = "array_" ++ TypeName ++ "_element"
            ),
            halfreify_array_lookup_var(Context, OutsideAnns, ILHS,
                ConstraintName, ArrayElemBounds, AddTmpVar, MznArrayExpr,
                ArrayExpr, OffsetExpr, Z, LookupConstraints, !Info, !Model),
            mzn_constraint_set_union(OffsetConstraints, LookupConstraints,
                AllConstraints),
            KnownFalse = OffsetKnownFalse
        )
    ).

%-----------------------------------------------------------------------------%

:- pred halfreify_array_lookup_par_par(error_context::in, ilhs::in, ElemT::in,
    array(ElemT)::in, int::in, ElemT::out, known_to_be_false::out) is det.

halfreify_array_lookup_par_par(Context, ILHS, DefaultValue, Xs, I, Z,
        KnownFalse) :-
    I0 = I - 1,
    ( if array.semidet_lookup(Xs, I0, Z0) then
        Z = Z0,
        KnownFalse = not_known_to_be_false
    else
        (
            ILHS = ilhs_true,
            minizinc_user_error(Context, "Array index out of range.\n")
        ;
            ILHS = ilhs_var(_),
            Z = DefaultValue,
            KnownFalse = known_to_be_false
            % XXX ZZZ !Env ^ reifying := reifying([bool_const(no)])
        )
    ).

%-----------------------------------------------------------------------------%

:- pred halfreify_array_lookup_var(error_context::in, mzn_anns::in, ilhs::in,
    string::in,
    (func(global_var_map, array_expr(ElemT)) = BoundsT)::in,
    pred(error_context, mzn_anns, ilhs, BoundsT,
        string, list(mzn_expr), mzn_anns,
        var_id, ElemT, mzn_constraint_set, hr_info, hr_info, model, model)::
    in(pred(in, in, in, in, in, in, in, out, out, out, in, out, in, out)
        is det),
    (func(array_expr(ElemT)) = mzn_expr)::in,
    array_expr(ElemT)::in, int_expr::in, ElemT::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

halfreify_array_lookup_var(Context, OutsideAnns, ILHS,
        ConstraintName, ArrayElemBounds, AddTmpVar, MznArrayExpr,
        ArrayExpr, OffsetExpr, Z, AllConstraints, !Info, !Model) :-
    % NOTE: OffsetExpr must be simplified before calling this predicate.
    BoundsA = ArrayElemBounds(!.Model ^ model_globals, ArrayExpr),
    (
        ILHS = ilhs_true,
        AddTmpVar(Context, OutsideAnns, ILHS, BoundsA, ConstraintName,
            [int_to_mzn_expr(OffsetExpr), MznArrayExpr(ArrayExpr)], no_anns,
            _VarIdZ, Z, AllConstraints, !Info, !Model)
    ;
        ILHS = ilhs_var(IndexIsInRange),
        % XXX Reifying = reifying(ReifVars),
        % ( if ReifVars = [IndexIsInRange | _] then
        Size = array_size(ArrayExpr),
        BoundsTmpB = int_range_lb_ub(1, Size),
        hr_make_tmp_int_var(Context, OutsideAnns, ILHS, BoundsTmpB,
            just_is_defined_var, _VarIdOffset, TmpOffsetExpr,
            VarConstraints, !Info, !Model),
        AddTmpVar(Context, OutsideAnns, ILHS, BoundsA, ConstraintName,
            [int_to_mzn_expr(TmpOffsetExpr), MznArrayExpr(ArrayExpr)],
            no_anns, _VarIdZ, Z, AddVarConstraints, !Info, !Model),
        hr_add_primitive_constraint("int_eq_reif",
            [int_to_mzn_expr(OffsetExpr), int_to_mzn_expr(TmpOffsetExpr),
            bool_to_mzn_expr(bool_var(var_no_index(IndexIsInRange)))], no_anns,
            EqConstraint, !Model),
        mzn_constraint_set_union_mixed_list([EqConstraint],
            [VarConstraints, AddVarConstraints], AllConstraints)
%       else
%           AddTmpVar(Context, OutsideAnns, ILHS, BoundsA, ConstraintName,
%               [int_to_mzn_expr(OffsetExpr), MznArrayExpr(ArrayExpr)],
%               no_anns, _VarIdZ, Z, AllConstraints, !Info, !Model)
%%          add_constraint(Context, "int_eq",
%%              [int_to_mzn_expr(OffsetExpr), int_to_mzn_expr(TmpOffsetExpr)],
%%              no_anns, !Info, !Model)
%       )
    ).

%-----------------------------------------------------------------------------%

:- pred hr_flatten_array_indices_to_int(error_context::in, mzn_anns::in,
    ilhs::in, index_ranges::in, list(int_expr)::in, int_expr::out,
    mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

hr_flatten_array_indices_to_int(Context, OutsideAnns, ILHS,
        IndexRanges, IndexExprs, OffsetExpr, AllConstraints, KnownFalse,
        !Info, !Model) :-
    hr_flatten_array_indices_to_int_loop(Context, OutsideAnns, ILHS,
        IndexRanges, IndexExprs, 1, _Size, OffsetExpr0,
        OffsetConstraints, KnownFalse, !Info, !Model),
    ( if int_expr_is_simple(OffsetExpr0) then
        OffsetExpr = OffsetExpr0,
        AllConstraints = OffsetConstraints
    else
        % Ensure we use domain consistency to compute the FlatZinc array index.
        SimplifyAnns = add_ann(domain, OutsideAnns),
        hr_simplify_int(Context, SimplifyAnns, ILHS, OffsetExpr0, OffsetExpr,
            SimplifyConstraints, !Info, !Model),
        mzn_constraint_set_union(OffsetConstraints, SimplifyConstraints,
            AllConstraints)
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
:- pred hr_flatten_array_indices_to_int_loop(error_context::in, mzn_anns::in,
    ilhs::in, index_ranges::in, list(int_expr)::in, int::in,
    int::out, int_expr::out, mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

hr_flatten_array_indices_to_int_loop(Context, OutsideAnns, ILHS,
        IndexRanges, IndexExprs, IndexNo, Size, OffsetExpr,
        AllConstraints, KnownFalse, !Info, !Model) :-
    (
        IndexRanges = [],
        IndexExprs = [],
        Size = 1,
        OffsetExpr = int_const(1),
        mzn_constraint_set_empty(AllConstraints),
        KnownFalse = not_known_to_be_false
    ;
        IndexRanges = [HeadIndexRange | TailIndexRanges],
        IndexExprs = [HeadIndexExpr | TailIndexExprs],
        hr_flatten_array_indices_to_int_loop(Context, OutsideAnns, ILHS,
            TailIndexRanges, TailIndexExprs, IndexNo + 1, TailSize,
            TailOffsetExpr, TailConstraints, TailKnownFalse, !Info, !Model),
        (
            HeadIndexRange = index_range(LB, UB)
        ;
            HeadIndexRange = index_implicit,
            minizinc_internal_error(Context, $pred, "implicit index")
        ),
        Size = (1 + UB - LB) * TailSize,
        IndexContext =
            [ ["In index argument ", string.int_to_string(IndexNo), "\n"]
            | Context
            ],
        ErrMsg = "Index out of range.\n",
        get_int_expr_lb_ub(IndexContext, !.Model ^ model_globals,
            HeadIndexExpr, LB0, UB0),
        ( if ( UB < LB0 ; UB0 < LB ) then
            % This index is necessarily out of range.
            AllConstraints = TailConstraints,
            (
                ILHS = ilhs_true,
                minizinc_user_error(IndexContext, ErrMsg)
            ;
                ILHS = ilhs_var(_),
                KnownFalse = known_to_be_false,
                % This is a bust, so just return a dummy value for OffsetExpr.
                OffsetExpr = TailOffsetExpr
            )
        else
            % XXX no_anns vs OutsideAnns
            halfreify_int_int_to_bool_or_inconsistent(Context, ErrMsg,
                OutsideAnns, ILHS, ii2b_le, int_const(LB), HeadIndexExpr,
                CVCheckLB, CheckLBSubConstraints, !Info, !Model),
            hr_impose_constraint(IndexContext, ErrMsg, ILHS,
                bool_const_or_var_to_expr(CVCheckLB), CheckLBConstraints,
                KnownFalseLB, !Info, !Model),

            halfreify_int_int_to_bool_or_inconsistent(Context, ErrMsg,
                OutsideAnns, ILHS, ii2b_le, HeadIndexExpr, int_const(UB), 
                CVCheckUB, CheckUBSubConstraints, !Info, !Model),
            hr_impose_constraint(IndexContext, ErrMsg, ILHS,
                bool_const_or_var_to_expr(CVCheckUB), CheckUBConstraints,
                KnownFalseUB, !Info, !Model),

            ( if
                halfreify_int_int_to_int(IndexContext, OutsideAnns, ilhs_true,
                    ii2i_sub, HeadIndexExpr, int_const(LB), ShiftedExpr,
                    Step1Constraints, KnownFalseStep1, !Info, !Model),
                halfreify_int_int_to_int(IndexContext, OutsideAnns, ilhs_true,
                    ii2i_mul, ShiftedExpr, int_const(TailSize), ScaledExpr,
                    Step2Constraints, KnownFalseStep2, !Info, !Model),
                halfreify_int_int_to_int(IndexContext, OutsideAnns, ilhs_true,
                    ii2i_add, ScaledExpr, TailOffsetExpr, OffsetExprPrime,
                    Step3Constraints, KnownFalseStep3, !Info, !Model)
            then
                OffsetExpr = OffsetExprPrime,
                mzn_constraint_set_union_list(
                    [TailConstraints,
                    CheckLBSubConstraints, CheckLBConstraints,
                    CheckUBSubConstraints, CheckUBConstraints,
                    Step1Constraints, Step2Constraints, Step3Constraints],
                    AllConstraints),
                KnownFalse = combine_known_to_be_false_list([TailKnownFalse,
                    KnownFalseLB, KnownFalseUB,
                    KnownFalseStep1, KnownFalseStep2, KnownFalseStep3])
            else
                minizinc_internal_error(IndexContext, $pred,
                    "halfreify_int_int_to_int failed.\n")
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

hr_fully_deref_bool_array(Info, Model, Context, A) =
    ( if
        A = array_var(IndexRanges, V),
        hr_get_var_value(Info, Model, V) = yes(MZA)
    then
        replace_index_ranges(IndexRanges, mzn_expr_to_bool_array(Context, MZA))
    else
        A
    ).

hr_fully_deref_float_array(Info, Model, Context, A) =
    ( if
        A = array_var(IndexRanges, V),
        hr_get_var_value(Info, Model, V) = yes(MZA)
    then
        replace_index_ranges(IndexRanges,
            mzn_expr_to_float_array(Context, MZA))
    else
        A
    ).

hr_fully_deref_int_array(Info, Model, Context, A) =
    ( if
        A = array_var(IndexRanges, V),
        hr_get_var_value(Info, Model, V) = yes(MZA)
    then
        replace_index_ranges(IndexRanges, mzn_expr_to_int_array(Context, MZA))
    else
        A
    ).

hr_fully_deref_bool_set_array(Info, Model, Context, A) =
    ( if
        A = array_var(IndexRanges, V),
        hr_get_var_value(Info, Model, V) = yes(MZA)
    then
        replace_index_ranges(IndexRanges,
            mzn_expr_to_bool_set_array(Context, MZA))
    else
        A
    ).

hr_fully_deref_float_set_array(Info, Model, Context, A) =
    ( if
        A = array_var(IndexRanges, V),
        hr_get_var_value(Info, Model, V) = yes(MZA)
    then
        replace_index_ranges(IndexRanges,
            mzn_expr_to_float_set_array(Context, MZA))
    else
        A
    ).

hr_fully_deref_int_set_array(Info, Model, Context, A) =
    ( if
        A = array_var(IndexRanges, V),
        hr_get_var_value(Info, Model, V) = yes(MZA)
    then
        replace_index_ranges(IndexRanges,
            mzn_expr_to_int_set_array(Context, MZA))
    else
        A
    ).

hr_fully_deref_string_array(Info, Model, Context, A) =
    ( if
        A = array_var(IndexRanges, V),
        hr_get_var_value(Info, Model, V) = yes(MZA)
    then
        replace_index_ranges(IndexRanges,
            mzn_expr_to_string_array(Context, MZA))
    else
        A
    ).

hr_fully_deref_ann_array(Info, Model, Context, A) =
    ( if
        A = array_var(IndexRanges, V),
        hr_get_var_value(Info, Model, V) = yes(MZA)
    then
        replace_index_ranges(IndexRanges,
            mzn_expr_to_ann_array(Context, MZA))
    else
        A
    ).

%-----------------------------------------------------------------------------%
:- end_module hr.array.
%-----------------------------------------------------------------------------%
