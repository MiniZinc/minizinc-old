%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
% Process MiniZinc specification items.
%
%-----------------------------------------------------------------------------%

:- module translate.item.
:- interface.

:- import_module tmzn_ast.
:- import_module translate.info.

:- import_module list.

:- pred tr_process_var_decl_item(tmzn_var_decl_item::in,
    list(tmzn_assign_item)::in, list(tmzn_assign_item)::out,
    tr_info::in, tr_info::out) is det.

:- pred tr_process_assign_item(tmzn_assign_item::in,
    list(tmzn_constraint_item)::in, list(tmzn_constraint_item)::out,
    tr_info::in, tr_info::out) is det.

:- type seen_unsatisfiable_constraint
    --->    not_seen_unsatisfiable_constraint
    ;       seen_unsatisfiable_constraint.

:- pred tr_process_constraint_item(tmzn_constraint_item::in,
    seen_unsatisfiable_constraint::in, seen_unsatisfiable_constraint::out,
    tfzn_constraint_set::in, tfzn_constraint_set::out,
    tr_info::in, tr_info::out) is det.

%-----------------------------------------------------------------------------%

:- implementation.

:- import_module error_util.
:- import_module mzn_ops.
:- import_module output_common.
:- import_module output_tfzn.
:- import_module output_tmzn.
:- import_module tfzn_ast.
:- import_module translate.bool.
:- import_module translate.vars.
:- import_module types.
:- import_module zinc_common.

:- import_module bool.
:- import_module io.
:- import_module map.
:- import_module maybe.
:- import_module set.
:- import_module string.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

tr_process_var_decl_item(Item, !RevAssignItems, !Info) :-
    Item = tmzn_item_var_decl(SrcPos, VarName, VarInst, TypeMaybeValue),
    (
        TypeMaybeValue = tmtmv_bool(MaybeBoolExpr),
        tr_info_get_var_info_maps(!.Info, VarInfoMaps0),
        vim_get_bool_map(VarInfoMaps0, BoolMap0),
        BoolVar = tfzn_bool_var_named(VarName),
        BoolVarInfo = var_info_bool(VarInst, var_is_not_output, no,
            MaybeBoolExpr),
        map.det_insert(BoolVar, BoolVarInfo, BoolMap0, BoolMap),
        vim_set_bool_map(BoolMap, VarInfoMaps0, VarInfoMaps),
        tr_info_set_var_info_maps(VarInfoMaps, !Info),
        (
            MaybeBoolExpr = no
        ;
            MaybeBoolExpr = yes(BoolExpr),
            SrcPos = src_pos(_, SrcLocn),
            AssignNestPos = outermost(op_assign(assign_from_var_decl)),
            AssignSrcPos = src_pos(AssignNestPos, SrcLocn),
            ImplicitAssignItem = tmzn_assign_item(AssignSrcPos,
                VarName, tmzn_gen_expr_bool(BoolExpr)),
            !:RevAssignItems = [ImplicitAssignItem | !.RevAssignItems]
        )
    ;
        TypeMaybeValue = tmtmv_bool_array(_, _),
        TypeMaybeValue = tmtmv_bool_array(IndexRanges, MaybeBoolExprs),
        tr_info_get_var_info_maps(!.Info, VarInfoMaps0),
        vim_get_bool_array_map(VarInfoMaps0, BoolArrayMap0),
        BoolArrayVar = tfzn_bool_array_var_named(VarName),
        BoolArrayVarInfo = var_info_bool_array(VarInst, var_is_not_output,
            IndexRanges, MaybeBoolExprs),
        map.det_insert(BoolArrayVar, BoolArrayVarInfo,
            BoolArrayMap0, BoolArrayMap),
        vim_set_bool_array_map(BoolArrayMap, VarInfoMaps0, VarInfoMaps),
        tr_info_set_var_info_maps(VarInfoMaps, !Info)
    ;
        TypeMaybeValue = tmtmv_int(IntRange, MaybeIntExpr),
        int_range_to_bounds(SrcPos, IntRange, IntBounds, !Info),
        tr_info_get_var_info_maps(!.Info, VarInfoMaps0),
        vim_get_int_map(VarInfoMaps0, IntMap0),
        IntVar = tfzn_int_var_named(VarName),
        IntVarInfo = var_info_int(VarInst, var_is_not_output, IntBounds,
            MaybeIntExpr),
        map.det_insert(IntVar, IntVarInfo, IntMap0, IntMap),
        vim_set_int_map(IntMap, VarInfoMaps0, VarInfoMaps),
        tr_info_set_var_info_maps(VarInfoMaps, !Info),
        (
            MaybeIntExpr = no
        ;
            MaybeIntExpr = yes(IntExpr),
            SrcPos = src_pos(_, SrcLocn),
            AssignNestPos = outermost(op_assign(assign_from_var_decl)),
            AssignSrcPos = src_pos(AssignNestPos, SrcLocn),
            ImplicitAssignItem = tmzn_assign_item(AssignSrcPos,
                VarName, tmzn_gen_expr_int(IntExpr)),
            !:RevAssignItems = [ImplicitAssignItem | !.RevAssignItems]
        )
    ;
        TypeMaybeValue = tmtmv_int_array(IntRange, IndexRanges, MaybeIntExprs),
        int_range_to_bounds(SrcPos, IntRange, IntBounds, !Info),
        tr_info_get_var_info_maps(!.Info, VarInfoMaps0),
        vim_get_int_array_map(VarInfoMaps0, IntArrayMap0),
        IntArrayVar = tfzn_int_array_var_named(VarName),
        IntArrayVarInfo = var_info_int_array(VarInst, var_is_not_output,
            IntBounds, IndexRanges, MaybeIntExprs),
        map.det_insert(IntArrayVar, IntArrayVarInfo,
            IntArrayMap0, IntArrayMap),
        vim_set_int_array_map(IntArrayMap, VarInfoMaps0, VarInfoMaps),
        tr_info_set_var_info_maps(VarInfoMaps, !Info)
    ;
        TypeMaybeValue = tmtmv_int_set(_, _),
        add_nyi_error_info($pred, phase_var_decl, SrcPos,
            "int set", !Info)
    ;
        TypeMaybeValue = tmtmv_int_set_array(_, _, _),
        add_nyi_error_info($pred, phase_var_decl, SrcPos,
            "int set array", !Info)
    ;
        TypeMaybeValue = tmtmv_float(FloatRange, MaybeFloatExpr),
        float_range_to_bounds(SrcPos, FloatRange, FloatBounds, !Info),
        tr_info_get_var_info_maps(!.Info, VarInfoMaps0),
        vim_get_float_map(VarInfoMaps0, FloatMap0),
        FloatVar = tfzn_float_var_named(VarName),
        FloatVarInfo = var_info_float(VarInst, var_is_not_output,
            FloatBounds, MaybeFloatExpr),
        map.det_insert(FloatVar, FloatVarInfo, FloatMap0, FloatMap),
        vim_set_float_map(FloatMap, VarInfoMaps0, VarInfoMaps),
        tr_info_set_var_info_maps(VarInfoMaps, !Info),
        (
            MaybeFloatExpr = no
        ;
            MaybeFloatExpr = yes(_),
            MaybeFloatExpr = yes(FloatExpr),
            SrcPos = src_pos(_, SrcLocn),
            AssignNestPos = outermost(op_assign(assign_from_var_decl)),
            AssignSrcPos = src_pos(AssignNestPos, SrcLocn),
            ImplicitAssignItem = tmzn_assign_item(AssignSrcPos,
                VarName, tmzn_gen_expr_float(FloatExpr)),
            !:RevAssignItems = [ImplicitAssignItem | !.RevAssignItems]
        )
    ;
        TypeMaybeValue = tmtmv_float_array(FloatRange, IndexRanges,
            MaybeFloatExprs),
        float_range_to_bounds(SrcPos, FloatRange, FloatBounds, !Info),
        tr_info_get_var_info_maps(!.Info, VarInfoMaps0),
        vim_get_float_array_map(VarInfoMaps0, FloatArrayMap0),
        FloatArrayVar = tfzn_float_array_var_named(VarName),
        FloatArrayVarInfo = var_info_float_array(VarInst, var_is_not_output,
            FloatBounds, IndexRanges, MaybeFloatExprs),
        map.det_insert(FloatArrayVar, FloatArrayVarInfo,
            FloatArrayMap0, FloatArrayMap),
        vim_set_float_array_map(FloatArrayMap, VarInfoMaps0, VarInfoMaps),
        tr_info_set_var_info_maps(VarInfoMaps, !Info)
    ).

:- pred int_range_to_bounds(src_pos::in, int_range::in, bounds_int::out,
    tr_info::in, tr_info::out) is det.

int_range_to_bounds(SrcPos, IntRange, IntBounds, !Info) :-
    (
        IntRange = int_range_unbounded,
        IntBounds =
            int_bounds_range(int_minus_infinity, int_plus_infinity)
    ;
        IntRange = int_range_lb_ub(LB, UB),
        IntBounds = int_bounds_range(LB, UB)
    ;
        IntRange = int_range_set(_),
        % IntBounds is a dummy.
        IntBounds =
            int_bounds_range(int_minus_infinity, int_plus_infinity),
        add_nyi_error_info($pred, phase_var_decl, SrcPos,
            "int_range_set", !Info)
    ).

:- pred float_range_to_bounds(src_pos::in, float_range::in, bounds_float::out,
    tr_info::in, tr_info::out) is det.

float_range_to_bounds(SrcPos, FloatRange, FloatBounds, !Info) :-
    (
        FloatRange = float_range_unbounded,
        FloatBounds =
            float_bounds_range(float_minus_infinity, float_plus_infinity)
    ;
        FloatRange = float_range_lb_ub(LB, UB),
        FloatBounds = float_bounds_range(LB, UB)
    ;
        FloatRange = float_range_set(_),
        % FloatBounds is a dummy.
        FloatBounds =
            float_bounds_range(float_minus_infinity, float_plus_infinity),
        add_nyi_error_info($pred, phase_var_decl, SrcPos,
            "float_range_set", !Info)
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

tr_process_assign_item(TMznAssignItem, !RevTMznConstraints, !Info) :-
    TMznAssignItem = tmzn_assign_item(SrcPos, VarName, GeneralExpr),
    % XXX record the relevant AssignExpr in VarInfoMaps
    (
        GeneralExpr = tmzn_gen_expr_bool(BoolAssignExpr),
        BoolVar = tmzn_bool_var_named(VarName),
        % XXX flatten.item.m handles this specially in some cases
        % IFF the assignment is part of a variable declaration.
        BoolVarExpr = tmzn_bool_expr_var(SrcPos, BoolVar),
        ConstraintExpr = tmzn_bool_expr_bb2b(SrcPos, bb2b_eq,
            BoolVarExpr, BoolAssignExpr)
    ;
        GeneralExpr = tmzn_gen_expr_bool_array(_BoolArrayAssignExpr),
        add_nyi_error_info($pred, phase_assign, SrcPos,
            "bool_array assign", !Info),
        ConstraintExpr = tmzn_bool_expr_const(SrcPos, yes)
    ;
        GeneralExpr = tmzn_gen_expr_int(IntAssignExpr),
        IntVar = tmzn_int_var_named(VarName),
        IntVarExpr = tmzn_int_expr_var(SrcPos, IntVar),
        ConstraintExpr = tmzn_bool_expr_ii2b(SrcPos, ii2b_eq,
            IntVarExpr, IntAssignExpr)
    ;
        GeneralExpr = tmzn_gen_expr_int_array(_IntArrayAssignExpr),
        add_nyi_error_info($pred, phase_assign, SrcPos,
            "int_array assign", !Info),
        ConstraintExpr = tmzn_bool_expr_const(SrcPos, yes)
    ;
        GeneralExpr = tmzn_gen_expr_int_set(_IntSetAssignExpr),
        add_nyi_error_info($pred, phase_assign, SrcPos,
            "int_set assign", !Info),
        ConstraintExpr = tmzn_bool_expr_const(SrcPos, yes)
    ;
        GeneralExpr = tmzn_gen_expr_int_set_array(_IntSetArrayAssignExpr),
        add_nyi_error_info($pred, phase_assign, SrcPos,
            "int_set_array assign", !Info),
        ConstraintExpr = tmzn_bool_expr_const(SrcPos, yes)
    ;
        GeneralExpr = tmzn_gen_expr_float(FloatAssignExpr),
        FloatVar = tmzn_float_var_named(VarName),
        FloatVarExpr = tmzn_float_expr_var(SrcPos, FloatVar),
        ConstraintExpr = tmzn_bool_expr_ff2b(SrcPos, ff2b_eq,
            FloatVarExpr, FloatAssignExpr)
    ;
        GeneralExpr = tmzn_gen_expr_float_array(_FloatArrayAssignExpr),
        add_nyi_error_info($pred, phase_assign, SrcPos,
            "float_array assign", !Info),
        ConstraintExpr = tmzn_bool_expr_const(SrcPos, yes)
    ;
        GeneralExpr = tmzn_gen_expr_float_set(_FloatSetAssignExpr),
        add_nyi_error_info($pred, phase_assign, SrcPos,
            "float_set assign", !Info),
        ConstraintExpr = tmzn_bool_expr_const(SrcPos, yes)
    ;
        GeneralExpr = tmzn_gen_expr_string(StringAssignExpr),
        StringVar = tmzn_string_var_named(VarName),
        StringVarExpr = tmzn_string_expr_var(SrcPos, StringVar),
        ConstraintExpr = tmzn_bool_expr_ss2b(SrcPos, ss2b_eq,
            StringVarExpr, StringAssignExpr)
    ;
        GeneralExpr = tmzn_gen_expr_string_array(_StringArrayAssignExpr),
        add_nyi_error_info($pred, phase_assign, SrcPos,
            "string_array assign", !Info),
        ConstraintExpr = tmzn_bool_expr_const(SrcPos, yes)
    ),
    ( if ConstraintExpr = tmzn_bool_expr_const(_, _) then
        true
    else
        Constraint = tmzn_constr_bool_expr(ConstraintExpr),
        % XXX Anns
        set.init(Anns),
        TMznConstraint = tmzn_constraint_item(SrcPos, Constraint, Anns),
        !:RevTMznConstraints = [TMznConstraint | !.RevTMznConstraints]
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

tr_process_constraint_item(TMznConstraintItem, !SeenUnsatisfiableConstraint,
        !TFznConstraints, !Info) :-
    % XXX We could avoid doing anything if !.SeenUnsatisfiableConstraint
    % is seen_unsatisfiable_constraint, but that case shouldn't be common,
    % so we don't optimize mzn2fzn for it.

    trace [io(!IO)] (
        ConstraintStr = dump_tmzn_constraint_item(TMznConstraintItem),
        ConstraintMsg = "Converting " ++ ConstraintStr,
        io.write_string(ConstraintMsg, !IO)
    ),

    TMznConstraintItem = tmzn_constraint_item(SrcPos, Constraint, _Anns),
    % XXX _Anns
    Constraint = tmzn_constr_bool_expr(BoolExpr),
    translate_bool_expr_to_tfzn_constraints(ilhs_true, ctxt_pos,
        yes(asserted_true), BoolExpr, MaybeKnownTruth, NewConstraints, !Info),
    (
        MaybeKnownTruth = unknown_truth,
        MaybeSpec = no
    ;
        MaybeKnownTruth = known_truth(known_true),
        SrcPos = src_pos(_, SrcLocn),
        Pieces = [words("Constraint statically known to be true."), nl],
        Msg = simple_msg(SrcLocn, [always(Pieces)]),
        Spec = error_spec(severity_warning, phase_constraint, [Msg]),
        add_error(Spec, !Info),
        MaybeSpec = yes(Spec)
    ;
        MaybeKnownTruth = known_truth(known_false),
        !:SeenUnsatisfiableConstraint = seen_unsatisfiable_constraint,
        SrcPos = src_pos(_, SrcLocn),
        Pieces = [words("Constraint statically known to be false."), nl],
        Msg = simple_msg(SrcLocn, [always(Pieces)]),
        Spec = error_spec(severity_warning, phase_constraint, [Msg]),
        add_error(Spec, !Info),
        MaybeSpec = yes(Spec)
    ),
    trace [io(!IO)] (
        io.write_string("\nResult of translating constraint:\n", !IO),
        OutputTFznOpts = output_opts(yes, 2),
        list.foldl(
            output_tfzn_constraint_item(OutputTFznOpts, io.stdout_stream),
            tfzn_constraint_set_to_list(NewConstraints), !IO),
        (
            MaybeSpec = no
        ;
            MaybeSpec = yes(ErrorSpec),
            set.init(ErrorOptions),
            write_error_spec(ErrorSpec, ErrorOptions, 0, _, 0, _, !IO)
        ),
        io.nl(!IO),
        io.flush_output(!IO)
    ),
    !:TFznConstraints = !.TFznConstraints ++ NewConstraints.

%-----------------------------------------------------------------------------%
:- end_module translate.item.
%-----------------------------------------------------------------------------%
