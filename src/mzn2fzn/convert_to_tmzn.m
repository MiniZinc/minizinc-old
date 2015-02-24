%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
% Code to convert constraints to the typed MiniZinc representation.
%
%-----------------------------------------------------------------------------%

:- module convert_to_tmzn.
:- interface.

:- import_module error_util.
:- import_module zinc_ast.
:- import_module tmzn_ast.

:- import_module io.
:- import_module list.

:- pred convert_model_to_tmzn(string::in, sast::in, tmzn::out,
    list(error_spec)::out, io::di, io::uo) is det.

%-----------------------------------------------------------------------------%

:- implementation.

:- import_module mzn_ops.
:- import_module types.
:- import_module types_and_insts.
:- import_module zinc_common.

:- import_module bool.
:- import_module int.
:- import_module maybe.
:- import_module set.
:- import_module string.

%-----------------------------------------------------------------------------%

convert_model_to_tmzn(ModelFileName, SAST, TMzn, !:Specs, !IO) :-
    SAST = sast(Items, SolveItem, MaybeOutputItem),

    io.open_append("/home/workspaces/g6/g12/zinc/src/mzn2fzn/CONVERT", Res,
        !IO),
    ( if Res = ok(Stream) then
        US = Stream
    else
        io.open_append("/dev/null", Res2, !IO),
        ( if Res2 = ok(Stream) then
            US = Stream
        else
            unexpected("cannot open /dev/null")
        )
    ),
    io.format(US, "MODEL %s\n", [s(ModelFileName)], !IO),

    list.foldl5(convert_item_to_tmzn(US), Items,
        [], RevVarDeclItems, [], RevAssignItems, [], RevConstraintItems,
        [], !:Specs, !IO),
    % XXX These calls to list.reverse *should* put the items into the correct
    % order, but the items are not in source order in SAST to begin with.
    list.reverse(RevVarDeclItems, VarDeclItems),
    list.reverse(RevAssignItems, AssignItems),
    list.reverse(RevConstraintItems, ConstraintItems),

    % list.sort(compare_var_decl_items, RevVarDeclItems, VarDeclItems),
    % list.sort(compare_assign_items, RevAssignItems, AssignItems),
    % list.sort(compare_constraint_items, RevConstraintItems, ConstraintItems),

    % XXX _SolveAnns
    SolveItem = sast_solve_item(SolveKind, _SolveAnns, SolveSrcLocn),
    SolveNest = outermost(op_solve),
    SolveSrcPos = src_pos(SolveNest, SolveSrcLocn),
    (
        SolveKind = satisfy,
        Solve = tmzn_sk_satisfy
    ;
        SolveKind = minimize(SolveExpr),
        ( if is_int_expr(SolveExpr) then
            convert_int_expr_to_tmzn(US, SolveNest, SolveExpr, IntExpr,
                !Specs, !IO),
            Solve = tmzn_sk_minimize_int(IntExpr)
        else if is_float_expr(SolveExpr) then
            convert_float_expr_to_tmzn(US, SolveNest, SolveExpr, FloatExpr,
                !Specs, !IO),
            Solve = tmzn_sk_minimize_float(FloatExpr)
        else
            io.write_string(US, "SOLVE minimize ", !IO),
            io.write(US, SolveExpr, !IO),
            io.nl(US, !IO),
            add_nyi_error($pred, phase_conversion, SolveSrcPos,
                "solve minimize", !Specs),
            Solve = tmzn_sk_satisfy
        )
    ;
        SolveKind = maximize(SolveExpr),
        ( if is_int_expr(SolveExpr) then
            convert_int_expr_to_tmzn(US, SolveNest, SolveExpr,
                IntExpr, !Specs, !IO),
            Solve = tmzn_sk_maximize_int(IntExpr)
        else if is_float_expr(SolveExpr) then
            convert_float_expr_to_tmzn(US, SolveNest, SolveExpr, FloatExpr,
                !Specs, !IO),
            Solve = tmzn_sk_maximize_float(FloatExpr)
        else
            io.write_string(US, "SOLVE maximize ", !IO),
            io.write(US, SolveExpr, !IO),
            io.nl(US, !IO),
            add_nyi_error($pred, phase_conversion, SolveSrcPos,
                "solve maximize", !Specs),
            Solve = tmzn_sk_satisfy
        )
    ),
    TMznSolveItem = tmzn_solve_item(SolveSrcPos, Solve, set.init),

    (
        MaybeOutputItem = yes(OutputItem),
        OutputItem = item(RawOutputItem, OutputSrcLocn),
        OutputNest = outermost(op_output),
        OutputSrcPos = src_pos(OutputNest, OutputSrcLocn),
        ( if RawOutputItem = output_item(OutputExpr) then
            ( if is_string_array_expr(OutputExpr) then
                convert_string_array_expr_to_tmzn(US, OutputNest,
                    OutputExpr, StrArrayExpr, !Specs, !IO),
                TMznOutputItem = tmzn_output_item(OutputSrcPos, StrArrayExpr),
                TMznMaybeOutputItem = yes(TMznOutputItem)
            else
                io.write_string(US, "OUTPUT bad expr ", !IO),
                io.write(US, OutputExpr, !IO),
                io.nl(US, !IO),
                add_internal_error($pred, phase_conversion, OutputSrcPos,
                    "output item is wrong type", !Specs),
                TMznMaybeOutputItem = no
            )
        else
            add_internal_error($pred, phase_conversion, OutputSrcPos,
                "output item is wrong kind", !Specs),
            TMznMaybeOutputItem = no
        )
    ;
        MaybeOutputItem = no,
        TMznMaybeOutputItem = no
    ),

    io.close_output(US, !IO),
    TMzn = tmzn(VarDeclItems, AssignItems, ConstraintItems, TMznSolveItem,
        TMznMaybeOutputItem).

:- pred convert_item_to_tmzn(io.output_stream::in, item::in,
    list(tmzn_var_decl_item)::in, list(tmzn_var_decl_item)::out,
    list(tmzn_assign_item)::in, list(tmzn_assign_item)::out,
    list(tmzn_constraint_item)::in, list(tmzn_constraint_item)::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_item_to_tmzn(US, Item, !RevVarDeclItems, !RevAssignItems,
        !RevConstraintItems, !Specs, !IO) :-
    Item = item(RawItem, DeclSrcLocn),
    (
        RawItem = constraint_item(Expr),
        DeclSrcPos = src_pos(outermost(op_constraint(constr_explicit)),
            DeclSrcLocn),
        convert_constraint_to_tmzn_item(US, DeclSrcPos, Expr, ConstraintItem,
            !Specs, !IO),
        !:RevConstraintItems = [ConstraintItem | !.RevConstraintItems]
    ;
        % XXX _VarAnnExprs
        RawItem = var_decl_item(TIExpr, VarName, _VarAnnExprs, MaybeValueExpr),
        DeclSrcPos = src_pos(outermost(op_var_decl), DeclSrcLocn),
        NestPos = nest(DeclSrcPos, is_var_decl_init),
        TIExpr = ti_expr(RawTIExpr, _ExprInfo),
        RawTIExpr = raw_ti_expr(VarPar, BaseTIExprTail),
        (
            VarPar = par,
            VarInst = var_is_par
        ;
            VarPar = var,
            VarInst = var_is_var
        ),
        (
            BaseTIExprTail = bte_bool,
            (
                MaybeValueExpr = no_assignment,
                TypeMaybeValue = tmtmv_bool(no)
            ;
                ( MaybeValueExpr = rhs_assignment(ValueExpr)
                ; MaybeValueExpr = separate_assignment(_, ValueExpr)
                ),
                convert_bool_expr_to_tmzn(US, NestPos, ValueExpr,
                    BoolValueExpr, !Specs, !IO),
                TypeMaybeValue = tmtmv_bool(yes(BoolValueExpr))
            )
        ;
            BaseTIExprTail = bte_int,
            (
                MaybeValueExpr = no_assignment,
                TypeMaybeValue = tmtmv_int(int_range_unbounded, no)
            ;
                ( MaybeValueExpr = rhs_assignment(ValueExpr)
                ; MaybeValueExpr = separate_assignment(_, ValueExpr)
                ),
                convert_int_expr_to_tmzn(US, NestPos, ValueExpr,
                    IntValueExpr, !Specs, !IO),
                TypeMaybeValue = tmtmv_int(int_range_unbounded,
                    yes(IntValueExpr))
            )
        ;
            BaseTIExprTail = bte_float,
            (
                MaybeValueExpr = no_assignment,
                TypeMaybeValue = tmtmv_float(float_range_unbounded, no)
            ;
                ( MaybeValueExpr = rhs_assignment(ValueExpr)
                ; MaybeValueExpr = separate_assignment(_, ValueExpr)
                ),
                convert_float_expr_to_tmzn(US, NestPos, ValueExpr,
                    FloatValueExpr, !Specs, !IO),
                TypeMaybeValue = tmtmv_float(float_range_unbounded,
                    yes(FloatValueExpr))
            )
        ;
            BaseTIExprTail = bte_string,
            add_nyi_error($pred, phase_conversion, DeclSrcPos,
                "string", !Specs),
            TypeMaybeValue = tmtmv_bool(no)
        ;
            BaseTIExprTail = bte_array_of(IndexTypeExprs, EltTypeExpr, _),
            % XXX I (zs) have no idea what the significance of the third
            % argument may be.
            pos_map_foldl2(DeclSrcPos, islk_init_index_type, 1,
                convert_tmzn_index_range(US), IndexTypeExprs, IndexRanges,
                !Specs, !IO),
            convert_tmzn_element_type_and_maybe_values(US,
                nest(DeclSrcPos, is_init_elt_type),
                EltTypeExpr, IndexRanges, MaybeValueExpr, TypeMaybeValue,
                !Specs, !IO)
        ;
            BaseTIExprTail = bte_ann,
            add_nyi_error($pred, phase_conversion, DeclSrcPos,
                "ann", !Specs),
            TypeMaybeValue = tmtmv_bool(no)
        ;
            BaseTIExprTail = bte_range_expr_as_type_expr(_LBExpr, _UBExpr),
            add_nyi_error($pred, phase_conversion, DeclSrcPos,
                "range expr", !Specs),
            TypeMaybeValue = tmtmv_bool(no)
        ;
            BaseTIExprTail = bte_set_expr_as_type_expr(_UBExpr),
            add_nyi_error($pred, phase_conversion, DeclSrcPos,
                "set expr", !Specs),
            TypeMaybeValue = tmtmv_bool(no)
        ;
            BaseTIExprTail = bte_ident(_),
            add_nyi_error($pred, phase_conversion, DeclSrcPos,
                "ident", !Specs),
            TypeMaybeValue = tmtmv_bool(no)
        ;
            BaseTIExprTail = bte_set_of(_),
            add_nyi_error($pred, phase_conversion, DeclSrcPos,
                "set", !Specs),
            TypeMaybeValue = tmtmv_bool(no)
        ;
            ( BaseTIExprTail = bte_typeinst_var(_)
            ; BaseTIExprTail = bte_any_typeinst_var(_)
            ; BaseTIExprTail = bte_tuple_of(_)
            ; BaseTIExprTail = bte_bottom
            ; BaseTIExprTail = bte_error
            ),
            add_internal_error($pred, phase_conversion, DeclSrcPos,
                "expected a MiniZinc type", !Specs),
            TypeMaybeValue = tmtmv_bool(no)
        ),
        VarDeclItem = tmzn_item_var_decl(DeclSrcPos, VarName, VarInst,
            TypeMaybeValue),
        !:RevVarDeclItems = [VarDeclItem | !.RevVarDeclItems]
    ;
        RawItem = assign_item(_, _),
        DeclSrcPos = src_pos(outermost(op_assign(assign_explicit)),
            DeclSrcLocn),
        add_nyi_error($pred, phase_conversion, DeclSrcPos,
            "assign_item", !Specs)
    ;
        RawItem = predfunc_item(_, _, _, _, _, _),
        DeclSrcPos = src_pos(outermost(op_predfunc), DeclSrcLocn),
        add_nyi_error($pred, phase_conversion, DeclSrcPos,
            "predfunc item", !Specs)
    ;
        RawItem = annotation_item(_, _),
        ( DeclSrcLocn = src_locn("stdlib.mzn", _) ->
            % XXX The warnings from here are only a distraction while
            % getting half-reification to work.
            true
        ;
            DeclSrcPos = src_pos(outermost(op_annotation), DeclSrcLocn),
            add_nyi_error($pred, phase_conversion, DeclSrcPos,
                "annotation item", !Specs)
        )
    ;
        RawItem = solve_item(_, _),
        DeclSrcPos = src_pos(outermost(op_solve), DeclSrcLocn),
        add_internal_error($pred, phase_conversion, DeclSrcPos,
            "solve item in wrong place", !Specs)
    ;
        RawItem = output_item(_),
        DeclSrcPos = src_pos(outermost(op_output), DeclSrcLocn),
        add_internal_error($pred, phase_conversion, DeclSrcPos,
            "output item in wrong place", !Specs)
    ).

:- pred convert_tmzn_index_range(io.output_stream::in, nest_pos::in,
    ti_expr::in, index_range::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_tmzn_index_range(_US, NestPos, TIExpr, IndexRange, !Specs, !IO) :-
    TIExpr = ti_expr(RawTIExpr, ExprInfo),
    ExprInfo = expr_info(SrcLocn, _TI),
    SrcPos = src_pos(NestPos, SrcLocn),
    RawTIExpr = raw_ti_expr(_VarPar, BaseTIExprTail),
    % XXX _VarPar
    (
        BaseTIExprTail = bte_range_expr_as_type_expr(LBExpr, UBExpr),
        LBExpr = expr(LBRawExpr, _, _),
        UBExpr = expr(UBRawExpr, _, _),
        ( if LBRawExpr = lit(int(LB)), UBRawExpr = lit(int(UB)) then
            IndexRange = index_range(LB, UB)
        else
            add_user_error($pred, phase_conversion, SrcPos,
                "expected constant lower and upper bounds", !Specs),
            IndexRange = index_range(0, 0)
        )
    ;
        ( BaseTIExprTail = bte_set_expr_as_type_expr(_UBExpr)
        ; BaseTIExprTail = bte_int
        ; BaseTIExprTail = bte_bool
        ; BaseTIExprTail = bte_float
        ; BaseTIExprTail = bte_string
        ; BaseTIExprTail = bte_ann
        ; BaseTIExprTail = bte_ident(_)
        ; BaseTIExprTail = bte_set_of(_)
        ; BaseTIExprTail = bte_array_of(_, _, _)
        ),
        add_internal_error($pred, phase_conversion, SrcPos,
            "expected a valid index type", !Specs),
        IndexRange = index_range(0, 0)
    ;
        ( BaseTIExprTail = bte_typeinst_var(_)
        ; BaseTIExprTail = bte_any_typeinst_var(_)
        ; BaseTIExprTail = bte_tuple_of(_)
        ; BaseTIExprTail = bte_bottom
        ; BaseTIExprTail = bte_error
        ),
        add_internal_error($pred, phase_conversion, SrcPos,
            "expected a MiniZinc type", !Specs),
        IndexRange = index_range(0, 0)
    ).

:- pred convert_tmzn_element_type_and_maybe_values(io.output_stream::in,
    nest_pos::in, ti_expr::in, index_ranges::in, var_decl_assignment::in,
    tmzn_var_type_maybe_value::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_tmzn_element_type_and_maybe_values(US, NestPos, EltTypeExpr,
        IndexRanges, MaybeValueExpr, TypeMaybeValue, !Specs, !IO) :-
    EltTypeExpr = ti_expr(RawTIExpr, ExprInfo),
    ExprInfo = expr_info(SrcLocn, _TI),
    SrcPos = src_pos(NestPos, SrcLocn),
    RawTIExpr = raw_ti_expr(_VarPar, BaseTIExprTail),
    % XXX _VarPar
    (
        BaseTIExprTail = bte_bool,
        (
            MaybeValueExpr = no_assignment,
            TypeMaybeValue = tmtmv_bool_array(IndexRanges, no)
        ;
            ( MaybeValueExpr = rhs_assignment(_ValueExpr)
            ; MaybeValueExpr = separate_assignment(_, _ValueExpr)
            ),
            % XXX
            BoolExprs = [],
            TypeMaybeValue = tmtmv_bool_array(IndexRanges, yes(BoolExprs))
        )
    ;
        (
            BaseTIExprTail = bte_int,
            IntRange = int_range_unbounded
        ;
            BaseTIExprTail = bte_range_expr_as_type_expr(LBExpr, UBExpr),
            LBExpr = expr(LBRawExpr, _, _),
            UBExpr = expr(UBRawExpr, _, _),
            ( if LBRawExpr = lit(int(LB)), UBRawExpr = lit(int(UB)) then
                IntRange = int_range_lb_ub(LB, UB)
            else
                add_internal_error($pred, phase_conversion, SrcPos,
                    "expected constant lower and upper bounds", !Specs),
                IntRange = int_range_lb_ub(0, 0)
            )
        ),
        (
            MaybeValueExpr = no_assignment,
            TypeMaybeValue = tmtmv_int_array(IntRange, IndexRanges, no)
        ;
            ( MaybeValueExpr = rhs_assignment(ValueExpr)
            ; MaybeValueExpr = separate_assignment(_, ValueExpr)
            ),
            ValueExpr = expr(RawValueExpr, ValueAnns, _ValueExprInfo),
            (
                ValueAnns = []
            ;
                ValueAnns = [_ | _],
                io.write_string(US, "INT ARRAY VALUE: ANNS", !IO),
                io.write(US, ValueAnns, !IO),
                io.nl(US, !IO),
                add_nyi_error($pred, phase_conversion, SrcPos,
                    "int_array value anns", !Specs)
            ),
            ( if RawValueExpr = lit_simple_array(ValueExprs) then
                pos_map_foldl2(SrcPos, islk_simple_array, 1,
                    convert_int_expr_to_tmzn(US),
                    ValueExprs, IntExprs, !Specs, !IO),
                TypeMaybeValue = tmtmv_int_array(IntRange, IndexRanges,
                    yes(IntExprs))
            else
                add_internal_error($pred, phase_conversion, SrcPos,
                    "expected lit_simple_array", !Specs),
                TypeMaybeValue = tmtmv_int_array(IntRange, IndexRanges, no)
            )
        )
    ;
        ( BaseTIExprTail = bte_set_expr_as_type_expr(_UBExpr)
        ; BaseTIExprTail = bte_float
        ; BaseTIExprTail = bte_string
        ; BaseTIExprTail = bte_ann
        ; BaseTIExprTail = bte_ident(_)
        ; BaseTIExprTail = bte_set_of(_)
        ; BaseTIExprTail = bte_array_of(_, _, _)
        ),
        add_internal_error($pred, phase_conversion, SrcPos,
            "expected a valid index type", !Specs),
        IntRange = int_range_lb_ub(0, 0),
        TypeMaybeValue = tmtmv_int_array(IntRange, IndexRanges, no)
    ;
        ( BaseTIExprTail = bte_typeinst_var(_)
        ; BaseTIExprTail = bte_any_typeinst_var(_)
        ; BaseTIExprTail = bte_tuple_of(_)
        ; BaseTIExprTail = bte_bottom
        ; BaseTIExprTail = bte_error
        ),
        add_internal_error($pred, phase_conversion, SrcPos,
            "expected a MiniZinc type", !Specs),
        IntRange = int_range_lb_ub(0, 0),
        TypeMaybeValue = tmtmv_int_array(IntRange, IndexRanges, no)
    ).

%-----------------------------------------------------------------------------%

:- pred convert_constraint_to_tmzn_item(io.output_stream::in, src_pos::in,
    expr::in, tmzn_constraint_item::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_constraint_to_tmzn_item(US, SrcPos, Expr, ConstraintItem,
        !Specs, !IO) :-
    % _Expr = expr(_RawExpr, _AnnExprs, _ExprInfo),
    % XXX Check TI
    % XXX Convert AnnExprs
    % ExprInfo = expr_info(_SrcLocn, _TI),
    % convert_ann_exprs_to_tmzn(US, AnnExprs, TMznAnns, !IO),
    set.init(TMznAnns),
    NestPos = nest(SrcPos, is_constr_expr),
    convert_bool_expr_to_tmzn(US, NestPos, Expr, BoolExpr, !Specs, !IO),
    Constraint = tmzn_constr_bool_expr(BoolExpr),
    ConstraintItem = tmzn_constraint_item(SrcPos, Constraint, TMznAnns).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred convert_bool_expr_to_tmzn(io.output_stream::in, nest_pos::in,
    expr::in, tmzn_bool_expr::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_bool_expr_to_tmzn(US, NestPos, Expr, BoolExpr, !Specs, !IO) :-
    Expr = expr(RawExpr, _AnnExprs, ExprInfo),
    % XXX Check TI
    % XXX Convert AnnExprs
    ExprInfo = expr_info(SrcLocn, TI),
    SrcPos = src_pos(NestPos, SrcLocn),
    ( if ( TI = ti_par_bool ; TI = ti_var_bool ) then
        true
    else
        add_internal_error($pred, phase_conversion, SrcPos, "bad TI", !Specs)
    ),
    % convert_ann_exprs_to_tmzn(US, AnnExprs, TMznAnns, !IO),
    (
        RawExpr = ident(VarId),
        BoolVar = tmzn_bool_var_named(id_name(VarId)),
        BoolExpr = tmzn_bool_expr_var(SrcPos, BoolVar)
    ;
        RawExpr = lit(Literal),
        (
            Literal = bool(Bool),
            BoolExpr = tmzn_bool_expr_const(SrcPos, Bool)
        ;
            (
                Literal = int(_),
                io.write_string(US, "BOOL: LIT INT\n", !IO),
                add_internal_error($pred, phase_conversion, SrcPos,
                    "lit int", !Specs)
            ;
                Literal = floatstr(_),
                io.write_string(US, "BOOL: LIT FLOAT\n", !IO),
                add_internal_error($pred, phase_conversion, SrcPos,
                    "lit float", !Specs)
            ;
                Literal = string(_),
                io.write_string(US, "BOOL: LIT STRING\n", !IO),
                add_internal_error($pred, phase_conversion, SrcPos,
                    "lit string", !Specs)
            ),
            BoolExpr = tmzn_bool_expr_const(SrcPos, no)
        )
    ;
        RawExpr = app(PredId, _ProcNo, _AppKind, ArgExprs),
        PredName = id_name(PredId),
        list.length(ArgExprs, Arity),
        ( if
            is_builtin_op(PredName, Arity, _, _, BuiltinOp)
        then
            convert_builtin_app_to_bool_expr(US, SrcPos, PredName,
                BuiltinOp, ArgExprs, BoolExpr, !Specs, !IO)
        else if
            PredName = "is_fixed",
            ArgExprs = [ArgExpr1]
        then
            Arg1NestPos = nest(SrcPos, is_arg("is_fixed", 1)),
            convert_general_expr_to_tmzn(US, Arg1NestPos, ArgExpr1, GenExpr1,
                !Specs, !IO),
            BoolExpr = tmzn_bool_expr_is_fixed(SrcPos, GenExpr1)
        else
            pos_map_foldl2(SrcPos, islk_pred(PredName), 1,
                convert_general_expr_to_tmzn(US),
                ArgExprs, GenExprs, !Specs, !IO),
            BoolExpr = tmzn_bool_expr_general(SrcPos, PredName, GenExprs)
        )
    ;
        RawExpr = array_access(ArrayExpr, IndexExprs),
        ( if is_bool_array_expr(ArrayExpr) then
            convert_bool_array_expr_to_tmzn(US, nest(SrcPos, is_array_id),
                ArrayExpr, BoolArray, !Specs, !IO),
            pos_map_foldl2(SrcPos, islk_index, 1, convert_int_expr_to_tmzn(US),
                IndexExprs, Indexes, !Specs, !IO),
            BoolVar = tmzn_bool_var_array_slot(BoolArray, Indexes),
            BoolExpr = tmzn_bool_expr_var(SrcPos, BoolVar)
        else
            io.write_string(US, "INT SET: ARRAY_ACCESS\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "array_access", !Specs),
            BoolExpr = tmzn_bool_expr_const(SrcPos, no)
        )
    ;
        RawExpr = lit_set(_ItemExprs),
        io.write_string(US, "BOOL: LIT_SET\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos,
            "lit_set", !Specs),
        BoolExpr = tmzn_bool_expr_const(SrcPos, no)
    ;
        RawExpr = lit_simple_array(_ItemExprs),
        io.write_string(US, "BOOL: LIT_SIMPLE_ARRAY\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos,
            "lit_simple_array", !Specs),
        BoolExpr = tmzn_bool_expr_const(SrcPos, no)
    ;
        RawExpr = lit_ann(_AnnId, _ArgExprs),
        io.write_string(US, "BOOL: LIT_ANN\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos,
            "lit_ann", !Specs),
        BoolExpr = tmzn_bool_expr_const(SrcPos, no)
    ;
        RawExpr = comprehension(_CompKind, _Generators, _MaybeCondExpr),
        io.write_string(US, "BOOL: COMPREHENSION\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos,
            "comprehension", !Specs),
        BoolExpr = tmzn_bool_expr_const(SrcPos, no)
    ;
        RawExpr = anon_var,
        BoolExpr = tmzn_bool_expr_var(SrcPos, tmzn_bool_var_anon)
    ;
        RawExpr = if_then_else(CondExpr, ThenExpr, ElseExpr),
        convert_bool_expr_to_tmzn(US, nest(SrcPos, is_cond), CondExpr, Cond,
            !Specs, !IO),
        convert_bool_expr_to_tmzn(US, nest(SrcPos, is_then), ThenExpr, Then,
            !Specs, !IO),
        convert_bool_expr_to_tmzn(US, nest(SrcPos, is_else), ElseExpr, Else,
            !Specs, !IO),
        BoolExpr = tmzn_bool_expr_ite(SrcPos, Cond, Then, Else)
    ;
        RawExpr = let(_LetVars, _LetExpr),
        io.write_string(US, "BOOL: LET\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "let", !Specs),
        BoolExpr = tmzn_bool_expr_const(SrcPos, no)
    ;
        RawExpr = coerce(FromTI, ToTI, CoerceExpr),
        CoerceContext = [["In coercion.\n"]],
        type_inst_to_mzn_type(CoerceContext, FromTI, FromInst, FromType),
        type_inst_to_mzn_type(CoerceContext, ToTI, ToInst, ToType),
        ( if
            FromInst = par,
            ToInst = var,
            FromType = ToType
        then
            Arg1Nest = nest(SrcPos, is_unop_arg("coerce")),
            convert_bool_expr_to_tmzn(US, Arg1Nest, CoerceExpr, BoolExpr,
                !Specs, !IO)
        else
            io.write_string(US, "BOOL: COERCE\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "coerce", !Specs),
            BoolExpr = tmzn_bool_expr_const(SrcPos, no)
        )
    ;
        RawExpr = lit_tuple(_),
        add_internal_error($pred, phase_conversion, SrcPos,
            "non-MiniZinc syntax item", !Specs),
        BoolExpr = tmzn_bool_expr_const(SrcPos, no)
    ).

%-----------------------------------------------------------------------------%

:- pred convert_builtin_app_to_bool_expr(io.output_stream::in,
    src_pos::in, string::in, builtin_op_type::in,
    list(expr)::in, tmzn_bool_expr::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_builtin_app_to_bool_expr(US, SrcPos, PredName, BuiltinOp, Args,
        BoolExpr, !Specs, !IO) :-
    (
        (
            BuiltinOp = bo_not,
            B2BOp = b2b_not
        ;
            BuiltinOp = bo_lb,
            B2BOp = b2b_lb
        ;
            BuiltinOp = bo_ub,
            B2BOp = b2b_ub
        ;
            BuiltinOp = bo_fix,
            B2BOp = b2b_fix
        ),
        ( if Args = [Arg1] then
            builtin_op_table(OpStr, _, _, _, BuiltinOp),
            Arg1Nest = nest(SrcPos, is_unop_arg(OpStr)),
            convert_bool_expr_to_tmzn(US, Arg1Nest, Arg1, BoolArg1,
                !Specs, !IO),
            BoolExpr = tmzn_bool_expr_b2b(SrcPos, B2BOp, BoolArg1)
        else
            io.write_string(US,
                "BOOL OP: bad arity for not/lb/ub/fix\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity", !Specs),
            BoolExpr = tmzn_bool_expr_const(SrcPos, no)
        )
    ;
        (
            BuiltinOp = bo_and,
            BB2BOp = bb2b_and
        ;
            BuiltinOp = bo_or,
            BB2BOp = bb2b_or
        ;
            BuiltinOp = bo_xor,
            BB2BOp = bb2b_xor
        ;
            BuiltinOp = bo_imp2r,
            BB2BOp = bb2b_imp2r
        ;
            BuiltinOp = bo_imp2l,
            BB2BOp = bb2b_imp2l
        ;
            BuiltinOp = bo_biimp,
            BB2BOp = bb2b_biimp
        ;
            BuiltinOp = bo_min,
            BB2BOp = bb2b_min
        ;
            BuiltinOp = bo_max,
            BB2BOp = bb2b_max
        ),
        ( if Args = [Arg1, Arg2] then
            builtin_op_table(OpStr, _, _, _, BuiltinOp),
            Arg1Nest = nest(SrcPos, is_binop_arg(OpStr, left)),
            Arg2Nest = nest(SrcPos, is_binop_arg(OpStr, right)),
            convert_bool_expr_to_tmzn(US, Arg1Nest, Arg1, BoolArg1,
                !Specs, !IO),
            convert_bool_expr_to_tmzn(US, Arg2Nest, Arg2, BoolArg2,
                !Specs, !IO),
            BoolExpr = tmzn_bool_expr_bb2b(SrcPos, BB2BOp, BoolArg1, BoolArg2)
        else
            io.write_string(US,
                "BOOL OP: bad arity for and/or/etc\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity", !Specs),
            BoolExpr = tmzn_bool_expr_const(SrcPos, no)
        )
    ;
        (
            BuiltinOp = bo_exists,
            BA2BOp = ba2b_exists
        ;
            BuiltinOp = bo_forall,
            BA2BOp = ba2b_forall
        ;
            BuiltinOp = bo_iffall,
            BA2BOp = ba2b_iffall
        ;
            BuiltinOp = bo_xorall,
            BA2BOp = ba2b_xorall
        ),
        ( if Args = [Arg1] then
            builtin_op_table(OpStr, _, _, _, BuiltinOp),
            Arg1Nest = nest(SrcPos, is_unop_arg(OpStr)),
            convert_bool_array_expr_to_tmzn(US, Arg1Nest, Arg1, Array,
                !Specs, !IO),
            BoolExpr = tmzn_bool_expr_ba2b(SrcPos, BA2BOp, Array)
        else
            io.write_string(US,
                "BOOL OP: bad arity for exists/forall/iffall/xorall\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity", !Specs),
            BoolExpr = tmzn_bool_expr_const(SrcPos, no)
        )
    ;
        (
            BuiltinOp = bo_eq,
            BB2BOp = bb2b_eq,
            II2BOp = ii2b_eq,
            FF2BOp = ff2b_eq,
            SS2BOp = ss2b_eq,
            XSXS2BOp = xsxs2b_eq
        ;
            BuiltinOp = bo_ne,
            BB2BOp = bb2b_ne,
            II2BOp = ii2b_ne,
            FF2BOp = ff2b_ne,
            SS2BOp = ss2b_ne,
            XSXS2BOp = xsxs2b_ne
        ;
            BuiltinOp = bo_lt,
            BB2BOp = bb2b_lt,
            II2BOp = ii2b_lt,
            FF2BOp = ff2b_lt,
            SS2BOp = ss2b_lt,
            XSXS2BOp = xsxs2b_lt
        ;
            BuiltinOp = bo_le,
            BB2BOp = bb2b_le,
            II2BOp = ii2b_le,
            FF2BOp = ff2b_le,
            SS2BOp = ss2b_le,
            XSXS2BOp = xsxs2b_le
        ;
            BuiltinOp = bo_gt,
            BB2BOp = bb2b_gt,
            II2BOp = ii2b_gt,
            FF2BOp = ff2b_gt,
            SS2BOp = ss2b_gt,
            XSXS2BOp = xsxs2b_gt
        ;
            BuiltinOp = bo_ge,
            BB2BOp = bb2b_ge,
            II2BOp = ii2b_ge,
            FF2BOp = ff2b_ge,
            SS2BOp = ss2b_ge,
            XSXS2BOp = xsxs2b_ge
        ),
        ( if Args = [Arg1, Arg2] then
            builtin_op_table(OpStr, _, _, _, BuiltinOp),
            Arg1Nest = nest(SrcPos, is_binop_arg(OpStr, left)),
            Arg2Nest = nest(SrcPos, is_binop_arg(OpStr, right)),
            ( if is_bool_expr(Arg1) then
                convert_bool_expr_to_tmzn(US, Arg1Nest, Arg1, BoolArg1,
                    !Specs, !IO),
                convert_bool_expr_to_tmzn(US, Arg2Nest, Arg2, BoolArg2,
                    !Specs, !IO),
                BoolExpr = tmzn_bool_expr_bb2b(SrcPos, BB2BOp,
                    BoolArg1, BoolArg2)
            else if is_int_expr(Arg1) then
                convert_int_expr_to_tmzn(US, Arg1Nest, Arg1, IntArg1,
                    !Specs, !IO),
                convert_int_expr_to_tmzn(US, Arg2Nest, Arg2, IntArg2,
                    !Specs, !IO),
                BoolExpr = tmzn_bool_expr_ii2b(SrcPos, II2BOp,
                    IntArg1, IntArg2)
            else if is_float_expr(Arg1) then
                convert_float_expr_to_tmzn(US, Arg1Nest, Arg1, FltArg1,
                    !Specs, !IO),
                convert_float_expr_to_tmzn(US, Arg2Nest, Arg2, FltArg2,
                    !Specs, !IO),
                BoolExpr = tmzn_bool_expr_ff2b(SrcPos, FF2BOp,
                    FltArg1, FltArg2)
            else if is_string_expr(Arg1) then
                convert_string_expr_to_tmzn(US, Arg1Nest, Arg1, StrArg1,
                    !Specs, !IO),
                convert_string_expr_to_tmzn(US, Arg2Nest, Arg2, StrArg2,
                    !Specs, !IO),
                BoolExpr = tmzn_bool_expr_ss2b(SrcPos, SS2BOp,
                    StrArg1, StrArg2)
            else if is_int_set_expr(Arg1) then
                convert_int_set_expr_to_tmzn(US, Arg1Nest, Arg1, ISet1,
                    !Specs, !IO),
                convert_int_set_expr_to_tmzn(US, Arg2Nest, Arg2, ISet2,
                    !Specs, !IO),
                BoolExpr = tmzn_bool_expr_isis2b(SrcPos, XSXS2BOp,
                    ISet1, ISet2)
% XXX
%           else if is_float_set(Arg1) then
%               convert_float_set_expr_to_tmzn(US, Arg1Nest, Arg1, FSet1,
%                  !Specs, !IO),
%               convert_float_set_expr_to_tmzn(US, Arg2Nest, Arg2, FSet2,
%                  !Specs, !IO),
%               BoolExpr = tmzn_bool_expr_fsfs2b(SrcPos, XSXS2BOp,
%                   FSet1, FSet2)
            else
                io.write_string(US,
                    "BOOL OP: bad type for comparison\n", !IO),
                add_internal_error($pred, phase_conversion, SrcPos,
                    "bad type for comparison", !Specs),
                BoolExpr = tmzn_bool_expr_const(SrcPos, no)
            )
        else
            io.write_string(US,
                "BOOL OP: bad arity for comparison\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity", !Specs),
            BoolExpr = tmzn_bool_expr_const(SrcPos, no)
        )
    ;
        BuiltinOp = bo_in,
        IIS2BOp = iis2b_in,
        % FFS2BOp = ffs2b_in,
        ( if Args = [Arg1, Arg2] then
            builtin_op_table(OpStr, _, _, _, BuiltinOp),
            Arg1Nest = nest(SrcPos, is_binop_arg(OpStr, left)),
            Arg2Nest = nest(SrcPos, is_binop_arg(OpStr, right)),
            ( if is_int_expr(Arg1) then
                convert_int_expr_to_tmzn(US, Arg1Nest, Arg1, Int,
                    !Specs, !IO),
                convert_int_set_expr_to_tmzn(US, Arg2Nest, Arg2, ISet,
                    !Specs, !IO),
                BoolExpr = tmzn_bool_expr_iis2b(SrcPos, IIS2BOp, Int, ISet)
% XXX
%           else if is_float_expr(Arg2) then
%               convert_float_expr_to_tmzn(US, Arg1Nest, Arg1, Flt,
%                   !Specs, !IO),
%               convert_float_set_expr_to_tmzn(US, Arg2Nest, Arg2, FSet,
%                   !Specs, !IO),
%               BoolExpr = tmzn_bool_expr_ffs2b(SrcPos, FFS2BOp, Flt, FSet)
            else
                io.write_string(US, "BOOL OP: bad type for in\n", !IO),
                add_internal_error($pred, phase_conversion, SrcPos,
                    "bad type", !Specs),
                BoolExpr = tmzn_bool_expr_const(SrcPos, no)
            )
        else
            io.write_string(US, "BOOL OP: bad arity for in\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity", !Specs),
            BoolExpr = tmzn_bool_expr_const(SrcPos, no)
        )
    ;
        (
            BuiltinOp = bo_subset,
            XSXS2BOp = xsxs2b_subset
        ;
            BuiltinOp = bo_superset,
            XSXS2BOp = xsxs2b_superset
        ),
        ( if Args = [Arg1, Arg2] then
            builtin_op_table(OpStr, _, _, _, BuiltinOp),
            Arg1Nest = nest(SrcPos, is_binop_arg(OpStr, left)),
            Arg2Nest = nest(SrcPos, is_binop_arg(OpStr, right)),
            ( if is_int_set_expr(Arg1) then
                convert_int_set_expr_to_tmzn(US, Arg1Nest, Arg1, ISet1,
                    !Specs, !IO),
                convert_int_set_expr_to_tmzn(US, Arg2Nest, Arg2, ISet2,
                    !Specs, !IO),
                BoolExpr = tmzn_bool_expr_isis2b(SrcPos, XSXS2BOp,
                    ISet1, ISet2)
% XXX
%           else if is_float_set_expr(Arg2) then
%               convert_float_set_expr_to_tmzn(US, Arg1Nest, Arg1, FSet1,
%                   !Specs, !IO),
%               convert_float_set_expr_to_tmzn(US, Arg2Nest, Arg2, FSet2,
%                   !Specs, !IO),
%               BoolExpr = tmzn_bool_expr_fsfs2b(SrcPos, XSXS2BOp,
%                   FSet1, FSet2)
            else
                io.write_string(US,
                    "BOOL OP: bad type for sub/super\n", !IO),
                add_internal_error($pred, phase_conversion, SrcPos,
                    "bad type", !Specs),
                BoolExpr = tmzn_bool_expr_const(SrcPos, no)
            )
        else
            io.write_string(US,
                "BOOL OP: bad arity for sub/super\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity", !Specs),
            BoolExpr = tmzn_bool_expr_const(SrcPos, no)
        )
    ;
        BuiltinOp = bo_assert,
        io.write_string(US, "BOOL OP: assert\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "assert", !Specs),
        BoolExpr = tmzn_bool_expr_const(SrcPos, no)
    ;
        ( BuiltinOp = bo_abort
        ; BuiltinOp = bo_dom
        ; BuiltinOp = bo_dom_array
        ; BuiltinOp = bo_lb_array
        ; BuiltinOp = bo_ub_array
        ; BuiltinOp = bo_dom_size
        ; BuiltinOp = bo_bool2int
        ; BuiltinOp = bo_int2float
        ; BuiltinOp = bo_negate
        ; BuiltinOp = bo_abs
        ; BuiltinOp = bo_add
        ; BuiltinOp = bo_sub
        ; BuiltinOp = bo_mul
        ; BuiltinOp = bo_fdiv
        ; BuiltinOp = bo_idiv
        ; BuiltinOp = bo_mod
        ; BuiltinOp = bo_array_max  % XXX
        ; BuiltinOp = bo_array_min  % XXX
        ; BuiltinOp = bo_array_sum
        ; BuiltinOp = bo_array_product
        ; BuiltinOp = bo_array_length
        ; BuiltinOp = bo_ceil
        ; BuiltinOp = bo_floor
        ; BuiltinOp = bo_round
        ; BuiltinOp = bo_exp
        ; BuiltinOp = bo_ln
        ; BuiltinOp = bo_log10
        ; BuiltinOp = bo_log2
        ; BuiltinOp = bo_log
        ; BuiltinOp = bo_pow
        ; BuiltinOp = bo_sqrt
        ; BuiltinOp = bo_sin
        ; BuiltinOp = bo_cos
        ; BuiltinOp = bo_tan
        ; BuiltinOp = bo_sinh
        ; BuiltinOp = bo_cosh
        ; BuiltinOp = bo_tanh
        ; BuiltinOp = bo_asin
        ; BuiltinOp = bo_acos
        ; BuiltinOp = bo_atan
        ; BuiltinOp = bo_card
        ; BuiltinOp = bo_set2array
        ; BuiltinOp = bo_range
        ; BuiltinOp = bo_diff
        ; BuiltinOp = bo_intersect
        ; BuiltinOp = bo_union
        ; BuiltinOp = bo_array_intersect
        ; BuiltinOp = bo_array_union
        ; BuiltinOp = bo_append
        ; BuiltinOp = bo_array1d
        ; BuiltinOp = bo_array2d
        ; BuiltinOp = bo_array3d
        ; BuiltinOp = bo_array4d
        ; BuiltinOp = bo_array5d
        ; BuiltinOp = bo_array6d
        ; BuiltinOp = bo_index_set
        ; BuiltinOp = bo_index_set_1of2
        ; BuiltinOp = bo_index_set_2of2
        ; BuiltinOp = bo_index_set_1of3
        ; BuiltinOp = bo_index_set_2of3
        ; BuiltinOp = bo_index_set_3of3
        ; BuiltinOp = bo_index_set_1of4
        ; BuiltinOp = bo_index_set_2of4
        ; BuiltinOp = bo_index_set_3of4
        ; BuiltinOp = bo_index_set_4of4
        ; BuiltinOp = bo_show
        ; BuiltinOp = bo_show_int
        ; BuiltinOp = bo_show_float
        ; BuiltinOp = bo_concat
        ; BuiltinOp = bo_join
        ),
        io.format(US, "BOOL OP: bad op %s\n", [s(PredName)], !IO),
        add_internal_error($pred, phase_conversion, SrcPos,
            "bad op " ++ PredName, !Specs),
        BoolExpr = tmzn_bool_expr_const(SrcPos, no)
    ).

%-----------------------------------------------------------------------------%

:- pred convert_bool_array_expr_to_tmzn(io.output_stream::in, nest_pos::in,
    expr::in, tmzn_bool_array_expr::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_bool_array_expr_to_tmzn(US, NestPos, Expr, BoolArrayExpr,
        !Specs, !IO) :-
    Expr = expr(RawExpr, AnnExprs, ExprInfo),
    ExprInfo = expr_info(SrcLocn, TI),
    SrcPos = src_pos(NestPos, SrcLocn),
    % XXX _IndexTI
    ( if
        TI = ti_array(_IndexTI, EltTI),
        ( EltTI = ti_par_bool ; EltTI = ti_var_bool )
    then
        true
    else
        io.write_string(US, "BOOL ARRAY: BAD TI\n", !IO),
        add_internal_error($pred, phase_conversion, SrcPos, "bad TI", !Specs)
    ),
    (
        AnnExprs = []
    ;
        AnnExprs = [_ | _],
        io.write_string(US, "BOOL ARRAY: ANNS ", !IO),
        io.write(US, AnnExprs, !IO),
        io.nl(US, !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "anns", !Specs)
    ),
    (
        RawExpr = ident(VarId),
        StrVar = tmzn_bool_array_var_named(id_name(VarId)),
        BoolArrayExpr = tmzn_bool_array_expr_var(SrcPos, StrVar)
    ;
        RawExpr = lit(_Literal),
        io.write_string(US, "BOOL ARRAY: LIT\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit", !Specs),
        BoolArrayExpr = tmzn_bool_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = app(PredId, _ProcNo, _AppKind, _ArgExprs),
        PredName = id_name(PredId),
        io.format(US, "BOOL ARRAY: APP %s\n", [s(PredName)], !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "app", !Specs),
        BoolArrayExpr = tmzn_bool_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = array_access(_ArrayExpr, _IndexExprs),
        io.write_string(US, "BOOL ARRAY: ARRAY_ACCESS\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "array_access", !Specs),
        BoolArrayExpr = tmzn_bool_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = lit_set(_ItemExprs),
        io.write_string(US, "BOOL ARRAY: LIT_SET\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit_set", !Specs),
        BoolArrayExpr = tmzn_bool_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = lit_simple_array(ItemExprs),
        list.length(ItemExprs, N),
        IRs = [index_range(1, N)],
        pos_map_foldl2(SrcPos, islk_simple_array, 1,
            convert_bool_expr_to_tmzn(US), ItemExprs, BoolExprs, !Specs, !IO),
        ( if
            list.map(try_project_bool_expr_to_const, BoolExprs, Bools)
        then
            BoolArrayExpr = tmzn_bool_array_expr_consts(SrcPos, IRs, Bools)
        else if
            list.map(try_project_bool_expr_to_var, BoolExprs, BoolVars)
        then
            BoolArrayExpr = tmzn_bool_array_expr_vars(SrcPos, IRs, BoolVars)
        else
            BoolArrayExpr = tmzn_bool_array_expr_exprs(SrcPos, IRs, BoolExprs)
        )
    ;
        RawExpr = lit_ann(_AnnId, _ArgExprs),
        io.write_string(US, "BOOL ARRAY: LIT_ANN\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit_ann", !Specs),
        BoolArrayExpr = tmzn_bool_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = comprehension(CompKind, Generators, MaybeCondExpr),
        (
            MaybeCondExpr = no,
            MaybeBoolCondExpr = no
        ;
            MaybeCondExpr = yes(CondExpr),
            convert_bool_expr_to_tmzn(US, nest(SrcPos, is_compre_cond),
                CondExpr, BoolCondExpr, !Specs, !IO),
            MaybeBoolCondExpr = yes(BoolCondExpr)
        ),
        (
            CompKind = simple_array_comp(HeadExpr),
            convert_bool_expr_to_tmzn(US, nest(SrcPos, is_compre_head),
                HeadExpr, HeadBoolExpr, !Specs, !IO),
            pos_map_foldl2(SrcPos, islk_compre_array, 1,
                convert_generator_to_tmzn(US),
                Generators, GeneratorExprs, !Specs, !IO),
            BoolArrayExpr = tmzn_bool_array_expr_comprehension(SrcPos,
                HeadBoolExpr, GeneratorExprs, MaybeBoolCondExpr)
        ;
            CompKind = set_comp(_),
            io.write_string(US, "BOOL ARRAY: SET COMPREHENSION\n", !IO),
            add_nyi_error($pred, phase_conversion, SrcPos, "set_comp", !Specs),
            BoolArrayExpr = tmzn_bool_array_expr_consts(SrcPos, [], [])
        )
    ;
        RawExpr = anon_var,
        BoolArrayExpr = tmzn_bool_array_expr_var(SrcPos,
            tmzn_bool_array_var_anon)
    ;
        RawExpr = if_then_else(_CondExpr, _ThenExpr, _ElseExpr),
        io.write_string(US, "BOOL ARRAY: IF_THEN_ELSE\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "if_then_else", !Specs),
        BoolArrayExpr = tmzn_bool_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = let(_LetVars, _LetExpr),
        io.write_string(US, "BOOL ARRAY: LET\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "let", !Specs),
        BoolArrayExpr = tmzn_bool_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = coerce(_FromTI, _ToTI, _CoerceExpr),
        io.write_string(US, "BOOL ARRAY: COERCE\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "coerce", !Specs),
        BoolArrayExpr = tmzn_bool_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = lit_tuple(_),
        add_internal_error($pred, phase_conversion, SrcPos,
            "non-MiniZinc expression", !Specs),
        BoolArrayExpr = tmzn_bool_array_expr_consts(SrcPos, [], [])
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred convert_int_expr_to_tmzn(io.output_stream::in, nest_pos::in,
    expr::in, tmzn_int_expr::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_int_expr_to_tmzn(US, NestPos, Expr, IntExpr, !Specs, !IO) :-
    Expr = expr(RawExpr, AnnExprs, ExprInfo),
    ExprInfo = expr_info(SrcLocn, TI),
    SrcPos = src_pos(NestPos, SrcLocn),
    ( if ( TI = ti_par_int ; TI = ti_var_int ) then
        true
    else
        io.write_string(US, "INT: BAD TI\n", !IO)
    ),
    (
        AnnExprs = []
    ;
        AnnExprs = [_ | _],
        io.write_string(US, "INT: ANNS ", !IO),
        io.write(US, AnnExprs, !IO),
        io.nl(US, !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "anns", !Specs)
    ),
    (
        RawExpr = ident(VarId),
        IntVar = tmzn_int_var_named(id_name(VarId)),
        IntExpr = tmzn_int_expr_var(SrcPos, IntVar)
    ;
        RawExpr = lit(Literal),
        (
            Literal = int(Int),
            IntExpr = tmzn_int_expr_const(SrcPos, Int)
        ;
            (
                Literal = bool(_),
                io.write_string(US, "INT: LIT BOOL\n", !IO),
                add_internal_error($pred, phase_conversion, SrcPos,
                    "lit bool", !Specs)
            ;
                Literal = floatstr(_),
                io.write_string(US, "INT: LIT FLOAT\n", !IO),
                add_internal_error($pred, phase_conversion, SrcPos,
                    "lit float", !Specs)
            ;
                Literal = string(_),
                io.write_string(US, "INT: LIT STRING\n", !IO),
                add_internal_error($pred, phase_conversion, SrcPos,
                    "lit string", !Specs)
            ),
            IntExpr = tmzn_int_expr_const(SrcPos, 0)
        )
    ;
        RawExpr = app(PredId, _ProcNo, _AppKind, ArgExprs),
        PredName = id_name(PredId),
        list.length(ArgExprs, Arity),
        ( if
            is_builtin_op(PredName, Arity, _, _, BuiltinOp)
        then
            convert_builtin_app_to_int_expr(US, SrcPos, PredName,
                BuiltinOp, ArgExprs, IntExpr, !Specs, !IO)
        else
            io.format(US, "INT: APP %s\n", [s(PredName)], !IO),
            add_nyi_error($pred, phase_conversion, SrcPos, "app", !Specs),
            IntExpr = tmzn_int_expr_const(SrcPos, 0)
        )
    ;
        RawExpr = array_access(ArrayExpr, IndexExprs),
        ( if is_int_array_expr(ArrayExpr) then
            convert_int_array_expr_to_tmzn(US, nest(SrcPos, is_array_id),
                ArrayExpr, IntArray, !Specs, !IO),
            pos_map_foldl2(SrcPos, islk_index, 1, convert_int_expr_to_tmzn(US),
                IndexExprs, Indexes, !Specs, !IO),
            IntVar = tmzn_int_var_array_slot(IntArray, Indexes),
            IntExpr = tmzn_int_expr_var(SrcPos, IntVar)
        else
            io.write_string(US, "INT SET: ARRAY_ACCESS\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "array_acccess", !Specs),
            IntExpr = tmzn_int_expr_const(SrcPos, 0)
        )
    ;
        RawExpr = lit_set(_ItemExprs),
        io.write_string(US, "INT: LIT_SET\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit_set", !Specs),
        IntExpr = tmzn_int_expr_const(SrcPos, 0)
    ;
        RawExpr = lit_simple_array(_ItemExprs),
        io.write_string(US, "INT: LIT_SIMPLE_ARRAY\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos,
            "lit_simple_array", !Specs),
        IntExpr = tmzn_int_expr_const(SrcPos, 0)
    ;
        RawExpr = lit_ann(_AnnId, _ArgExprs),
        io.write_string(US, "INT: LIT_ANN\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit_ann", !Specs),
        IntExpr = tmzn_int_expr_const(SrcPos, 0)
    ;
        RawExpr = comprehension(_CompKind, _Generators, _MaybeCondExpr),
        io.write_string(US, "INT: COMPREHENSION\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos,
            "comprehension", !Specs),
        IntExpr = tmzn_int_expr_const(SrcPos, 0)
    ;
        RawExpr = anon_var,
        IntExpr = tmzn_int_expr_var(SrcPos, tmzn_int_var_anon)
    ;
        RawExpr = if_then_else(CondExpr, ThenExpr, ElseExpr),
        convert_bool_expr_to_tmzn(US, nest(SrcPos, is_cond), CondExpr, Cond,
            !Specs, !IO),
        convert_int_expr_to_tmzn(US, nest(SrcPos, is_then), ThenExpr, Then,
            !Specs, !IO),
        convert_int_expr_to_tmzn(US, nest(SrcPos, is_else), ElseExpr, Else,
            !Specs, !IO),
        IntExpr = tmzn_int_expr_ite(SrcPos, Cond, Then, Else)
    ;
        RawExpr = let(_LetVars, _LetExpr),
        io.write_string(US, "INT: LET\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "let", !Specs),
        IntExpr = tmzn_int_expr_const(SrcPos, 0)
    ;
        RawExpr = coerce(FromTI, ToTI, CoerceExpr),
        CoerceContext = [["In coercion.\n"]],
        type_inst_to_mzn_type(CoerceContext, FromTI, FromInst, FromType),
        type_inst_to_mzn_type(CoerceContext, ToTI, ToInst, ToType),
        ( if
            FromInst = par,
            ToInst = var,
            FromType = ToType
        then
            Arg1Nest = nest(SrcPos, is_unop_arg("coerce")),
            convert_int_expr_to_tmzn(US, Arg1Nest, CoerceExpr, IntExpr,
                !Specs, !IO)
        else if
            FromType = mzn_bool,
            ToType = mzn_int(_)
        then
            Arg1Nest = nest(SrcPos, is_unop_arg("coerce")),
            convert_bool_expr_to_tmzn(US, Arg1Nest, CoerceExpr, BoolExpr,
                !Specs, !IO),
            IntExpr = tmzn_int_expr_b2i(SrcPos, b2i_bool2int, BoolExpr)
        else
            io.write_string(US, "INT: COERCE\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "coerce", !Specs),
            IntExpr = tmzn_int_expr_const(SrcPos, 0)
        )
    ;
        RawExpr = lit_tuple(_),
        add_internal_error($pred, phase_conversion, SrcPos,
            "non-MiniZinc expression", !Specs),
        IntExpr = tmzn_int_expr_const(SrcPos, 0)
    ).

:- pred convert_builtin_app_to_int_expr(io.output_stream::in, src_pos::in,
    string::in, builtin_op_type::in, list(expr)::in, tmzn_int_expr::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_builtin_app_to_int_expr(US, SrcPos, PredName, BuiltinOp, Args,
        IntExpr, !Specs, !IO) :-
    (
        (
            BuiltinOp = bo_negate,
            I2IOp = i2i_sub             % XXX
        ;
            BuiltinOp = bo_abs,
            I2IOp = i2i_abs
        ;
            BuiltinOp = bo_lb,
            I2IOp = i2i_lb
        ;
            BuiltinOp = bo_ub,
            I2IOp = i2i_ub
        ;
            BuiltinOp = bo_dom_size,
            I2IOp = i2i_dom_size
        ;
            BuiltinOp = bo_fix,
            I2IOp = i2i_fix
        ),
        % XXX i2i_add is missing; is_builtin_op does not recognize +/1
        ( if Args = [Arg1] then
            builtin_op_table(OpStr, _, _, _, BuiltinOp),
            Arg1Nest = nest(SrcPos, is_unop_arg(OpStr)),
            convert_int_expr_to_tmzn(US, Arg1Nest, Arg1, IntArg1, !Specs, !IO),
            IntExpr = tmzn_int_expr_i2i(SrcPos, I2IOp, IntArg1)
        else
            io.write_string(US,
                "INT OP: bad arity for -/abs/lb/ub/ds\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity", !Specs),
            IntExpr = tmzn_int_expr_const(SrcPos, 0)
        )
    ;
        (
            BuiltinOp = bo_add,
            II2IOp = ii2i_add
        ;
            BuiltinOp = bo_sub,
            II2IOp = ii2i_sub
        ;
            BuiltinOp = bo_mul,
            II2IOp = ii2i_mul
        ;
            BuiltinOp = bo_idiv,
            II2IOp = ii2i_div
        ;
            BuiltinOp = bo_mod,
            II2IOp = ii2i_mod
        ;
            BuiltinOp = bo_pow,
            II2IOp = ii2i_pow
        ;
            BuiltinOp = bo_min,
            II2IOp = ii2i_min
        ;
            BuiltinOp = bo_max,
            II2IOp = ii2i_max
        ),
        ( if Args = [Arg1, Arg2] then
            builtin_op_table(OpStr, _, _, _, BuiltinOp),
            Arg1Nest = nest(SrcPos, is_binop_arg(OpStr, left)),
            Arg2Nest = nest(SrcPos, is_binop_arg(OpStr, right)),
            convert_int_expr_to_tmzn(US, Arg1Nest, Arg1, IntArg1, !Specs, !IO),
            convert_int_expr_to_tmzn(US, Arg2Nest, Arg2, IntArg2, !Specs, !IO),
            IntExpr = tmzn_int_expr_ii2i(SrcPos, II2IOp, IntArg1, IntArg2)
        else
            io.write_string(US, "INT OP: bad arity for arith\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity", !Specs),
            IntExpr = tmzn_int_expr_const(SrcPos, 0)
        )
    ;
        BuiltinOp = bo_bool2int,
        B2IOp = b2i_bool2int,
        ( if Args = [Arg1] then
            builtin_op_table(OpStr, _, _, _, BuiltinOp),
            Arg1Nest = nest(SrcPos, is_unop_arg(OpStr)),
            convert_bool_expr_to_tmzn(US, Arg1Nest, Arg1, BoolArg1,
                !Specs, !IO),
            IntExpr = tmzn_int_expr_b2i(SrcPos, B2IOp, BoolArg1)
        else
            io.write_string(US, "INT OP: bad arity for b2i\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity", !Specs),
            IntExpr = tmzn_int_expr_const(SrcPos, 0)
        )
    ;
        BuiltinOp = bo_card,
        XS2IOp = xs2i_card,
        ( if Args = [Arg1] then
            builtin_op_table(OpStr, _, _, _, BuiltinOp),
            Arg1Nest = nest(SrcPos, is_unop_arg(OpStr)),
            ( if is_int_set_expr(Arg1) then
                convert_int_set_expr_to_tmzn(US, Arg1Nest, Arg1, ISet1,
                    !Specs, !IO),
                IntExpr = tmzn_int_expr_xs2i(SrcPos, XS2IOp, ISet1)
% XXX
%           else if is_float_set_expr(Arg1) then
%               convert_float_set_expr_to_tmzn(US, Arg1Nest, Arg1, FSet1,
%                   !Specs, !IO),
%               IntExpr = tmzn_int_expr_xs2i(SrcPos, XS2IOp, FSet1)
            else
                io.write_string(US, "INT OP: bad type for card\n", !IO),
                add_internal_error($pred, phase_conversion, SrcPos,
                    "bad type", !Specs),
                IntExpr = tmzn_int_expr_const(SrcPos, 0)
            )
        else
            io.write_string(US, "INT OP: bad arity for card\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity", !Specs),
            IntExpr = tmzn_int_expr_const(SrcPos, 0)
        )
    ;
        (
            BuiltinOp = bo_array_min,
            IS2IOp = is2i_min,
            IA2IOp = ia2i_min
        ;
            BuiltinOp = bo_array_max,
            IS2IOp = is2i_max,
            IA2IOp = ia2i_max
        ),
        ( if Args = [Arg1] then
            builtin_op_table(OpStr, _, _, _, BuiltinOp),
            Arg1Nest = nest(SrcPos, is_unop_arg(OpStr)),
            ( if is_int_set_expr(Arg1) then
                convert_int_set_expr_to_tmzn(US, Arg1Nest, Arg1, ISet,
                    !Specs, !IO),
                IntExpr = tmzn_int_expr_is2i(SrcPos, IS2IOp, ISet)
            else if is_int_array_expr(Arg1) then
                convert_int_array_expr_to_tmzn(US, Arg1Nest, Arg1, IArray,
                    !Specs, !IO),
                IntExpr = tmzn_int_expr_ia2i(SrcPos, IA2IOp, IArray)
            else
                io.write_string(US, "INT OP: bad type for min/max\n", !IO),
                add_internal_error($pred, phase_conversion, SrcPos,
                    "bad type", !Specs),
                IntExpr = tmzn_int_expr_const(SrcPos, 0)
            )
        else
            io.write_string(US, "INT OP: bad arity for min/max\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity", !Specs),
            IntExpr = tmzn_int_expr_const(SrcPos, 0)
        )
    ;
        (
            BuiltinOp = bo_array_sum,
            IA2IOp = ia2i_sum
        ;
            BuiltinOp = bo_array_product,
            IA2IOp = ia2i_product
        ;
            BuiltinOp = bo_lb_array,
            IA2IOp = ia2i_lb_array
        ;
            BuiltinOp = bo_ub_array,
            IA2IOp = ia2i_ub_array
        ),
        ( if Args = [Arg1] then
            ( if is_int_array_expr(Arg1) then
                builtin_op_table(OpStr, _, _, _, BuiltinOp),
                Arg1Nest = nest(SrcPos, is_unop_arg(OpStr)),
                convert_int_array_expr_to_tmzn(US, Arg1Nest, Arg1, IntArray,
                    !Specs, !IO),
                IntExpr = tmzn_int_expr_ia2i(SrcPos, IA2IOp, IntArray)
            else
                io.write_string(US,
                    "INT OP: bad type for array_sum/prod\n", !IO),
                add_internal_error($pred, phase_conversion, SrcPos,
                    "bad type", !Specs),
                IntExpr = tmzn_int_expr_const(SrcPos, 0)
            )
        else
            io.write_string(US,
                "INT OP: bad arity for array_sum/prod\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity", !Specs),
            IntExpr = tmzn_int_expr_const(SrcPos, 0)
        )
    ;
        BuiltinOp = bo_assert,
        io.write_string(US, "INT OP: assert\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "assert", !Specs),
        IntExpr = tmzn_int_expr_const(SrcPos, 0)
    ;
        ( BuiltinOp = bo_abort
        ; BuiltinOp = bo_not
        ; BuiltinOp = bo_and
        ; BuiltinOp = bo_or
        ; BuiltinOp = bo_xor
        ; BuiltinOp = bo_imp2r
        ; BuiltinOp = bo_imp2l
        ; BuiltinOp = bo_biimp
        ; BuiltinOp = bo_exists
        ; BuiltinOp = bo_forall
        ; BuiltinOp = bo_iffall
        ; BuiltinOp = bo_xorall
        ; BuiltinOp = bo_eq
        ; BuiltinOp = bo_ne
        ; BuiltinOp = bo_lt
        ; BuiltinOp = bo_le
        ; BuiltinOp = bo_gt
        ; BuiltinOp = bo_ge
        ; BuiltinOp = bo_in
        ; BuiltinOp = bo_subset
        ; BuiltinOp = bo_superset
        ; BuiltinOp = bo_dom
        ; BuiltinOp = bo_dom_array
        ; BuiltinOp = bo_int2float
        ; BuiltinOp = bo_fdiv
        ; BuiltinOp = bo_array_length
        ; BuiltinOp = bo_ceil
        ; BuiltinOp = bo_floor
        ; BuiltinOp = bo_round
        ; BuiltinOp = bo_exp
        ; BuiltinOp = bo_ln
        ; BuiltinOp = bo_log10
        ; BuiltinOp = bo_log2
        ; BuiltinOp = bo_log
        ; BuiltinOp = bo_sqrt
        ; BuiltinOp = bo_sin
        ; BuiltinOp = bo_cos
        ; BuiltinOp = bo_tan
        ; BuiltinOp = bo_sinh
        ; BuiltinOp = bo_cosh
        ; BuiltinOp = bo_tanh
        ; BuiltinOp = bo_asin
        ; BuiltinOp = bo_acos
        ; BuiltinOp = bo_atan
        ; BuiltinOp = bo_set2array
        ; BuiltinOp = bo_range
        ; BuiltinOp = bo_diff
        ; BuiltinOp = bo_intersect
        ; BuiltinOp = bo_union
        ; BuiltinOp = bo_array_intersect
        ; BuiltinOp = bo_array_union
        ; BuiltinOp = bo_append
        ; BuiltinOp = bo_array1d
        ; BuiltinOp = bo_array2d
        ; BuiltinOp = bo_array3d
        ; BuiltinOp = bo_array4d
        ; BuiltinOp = bo_array5d
        ; BuiltinOp = bo_array6d
        ; BuiltinOp = bo_index_set
        ; BuiltinOp = bo_index_set_1of2
        ; BuiltinOp = bo_index_set_2of2
        ; BuiltinOp = bo_index_set_1of3
        ; BuiltinOp = bo_index_set_2of3
        ; BuiltinOp = bo_index_set_3of3
        ; BuiltinOp = bo_index_set_1of4
        ; BuiltinOp = bo_index_set_2of4
        ; BuiltinOp = bo_index_set_3of4
        ; BuiltinOp = bo_index_set_4of4
        ; BuiltinOp = bo_show
        ; BuiltinOp = bo_show_int
        ; BuiltinOp = bo_show_float
        ; BuiltinOp = bo_concat
        ; BuiltinOp = bo_join
        ),
        io.format(US, "INT OP: bad op %s\n", [s(PredName)], !IO),
        add_internal_error($pred, phase_conversion, SrcPos, "bad op", !Specs),
        IntExpr = tmzn_int_expr_const(SrcPos, 0)
    ).

%-----------------------------------------------------------------------------%

:- pred convert_int_set_expr_to_tmzn(io.output_stream::in, nest_pos::in,
    expr::in, tmzn_int_set_expr::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_int_set_expr_to_tmzn(US, NestPos, Expr, IntSetExpr, !Specs, !IO) :-
    Expr = expr(RawExpr, AnnExprs, ExprInfo),
    ExprInfo = expr_info(SrcLocn, TI),
    SrcPos = src_pos(NestPos, SrcLocn),
    % XXX combinations
    ( if
        (
            TI = ti_par_set(EltTI),
            ( EltTI = ti_par_int ; EltTI = ti_var_int )
        ;
            TI = ti_var_set(EltTI),
            ( EltTI = ti_par_int ; EltTI = ti_var_int )
        )
    then
        true
    else
        io.write_string(US, "INT SET: BAD TI\n", !IO),
        add_internal_error($pred, phase_conversion, SrcPos, "bad TI", !Specs)
    ),
    (
        AnnExprs = []
    ;
        AnnExprs = [_ | _],
        io.write_string(US, "INT SET: ANNS ", !IO),
        io.write(US, AnnExprs, !IO),
        io.nl(US, !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "anns", !Specs)
    ),
    (
        RawExpr = ident(VarId),
        StrVar = tmzn_int_set_var_named(id_name(VarId)),
        IntSetExpr = tmzn_int_set_expr_var(SrcPos, StrVar)
    ;
        RawExpr = lit(_Literal),
        io.write_string(US, "INT SET: LIT\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit", !Specs),
        IntSetExpr = tmzn_int_set_expr_const(SrcPos, set.init)
    ;
        RawExpr = app(PredId, _ProcNo, _AppKind, ArgExprs),
        PredName = id_name(PredId),
        list.length(ArgExprs, Arity),
        ( if
            is_builtin_op(PredName, Arity, _, _, BuiltinOp)
        then
            convert_builtin_app_to_int_set_expr(US, SrcPos, PredName,
                BuiltinOp, ArgExprs, IntSetExpr, !Specs, !IO)
        else
            io.format(US, "INT SET: APP %s\n", [s(PredName)], !IO),
            add_nyi_error($pred, phase_conversion, SrcPos, "app", !Specs),
            IntSetExpr = tmzn_int_set_expr_const(SrcPos, set.init)
        )
    ;
        RawExpr = array_access(ArrayExpr, IndexExprs),
        ( if is_int_set_array_expr(ArrayExpr) then
            convert_int_set_array_expr_to_tmzn(US, nest(SrcPos, is_array_id),
                ArrayExpr, IntSetArray, !Specs, !IO),
            pos_map_foldl2(SrcPos, islk_index, 1,
                convert_int_expr_to_tmzn(US),
                IndexExprs, Indexes, !Specs, !IO),
            IntSetVar = tmzn_int_set_var_array_slot(IntSetArray, Indexes),
            IntSetExpr = tmzn_int_set_expr_var(SrcPos, IntSetVar)
        else
            io.write_string(US, "INT SET: ARRAY_ACCESS\n", !IO),
            add_nyi_error($pred, phase_conversion, SrcPos,
                "array access", !Specs),
            IntSetExpr = tmzn_int_set_expr_const(SrcPos, set.init)
        )
    ;
        RawExpr = lit_set(ItemExprs),
        pos_map_foldl2(SrcPos, islk_lit_set, 1, convert_int_expr_to_tmzn(US),
            ItemExprs, IntExprs, !Specs, !IO),
        ( if
            list.map(try_project_int_expr_to_const, IntExprs, IntConsts)
        then
            IntSetExpr = tmzn_int_set_expr_const(SrcPos,
                set.list_to_set(IntConsts))
        else
            IntSetExpr = tmzn_int_set_expr_exprs(SrcPos,
                set.list_to_set(IntExprs))
        )
    ;
        RawExpr = lit_simple_array(_ItemExprs),
        add_nyi_error($pred, phase_conversion, SrcPos, "simple array", !Specs),
        IntSetExpr = tmzn_int_set_expr_const(SrcPos, set.init)
    ;
        RawExpr = lit_ann(_AnnId, _ArgExprs),
        io.write_string(US, "INT SET: LIT_ANN\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit ann", !Specs),
        IntSetExpr = tmzn_int_set_expr_const(SrcPos, set.init)
    ;
        RawExpr = comprehension(CompKind, Generators, MaybeCondExpr),
        (
            MaybeCondExpr = no,
            MaybeBoolCondExpr = no
        ;
            MaybeCondExpr = yes(CondExpr),
            convert_bool_expr_to_tmzn(US, nest(SrcPos, is_compre_cond),
                CondExpr, BoolCondExpr, !Specs, !IO),
            MaybeBoolCondExpr = yes(BoolCondExpr)
        ),
        (
            CompKind = simple_array_comp(_),
            io.write_string(US, "INT SET: SIMPLE ARRAY COMPREHENSION\n", !IO),
            add_nyi_error($pred, phase_conversion, SrcPos,
                "simple comprehension", !Specs),
            IntSetExpr = tmzn_int_set_expr_const(SrcPos, set.init)
        ;
            CompKind = set_comp(HeadExpr),
            convert_int_expr_to_tmzn(US, nest(SrcPos, is_compre_head),
                HeadExpr, HeadIntExpr, !Specs, !IO),
            pos_map_foldl2(SrcPos, islk_compre_array, 1,
                convert_generator_to_tmzn(US),
                Generators, GeneratorExprs, !Specs, !IO),
            IntSetExpr = tmzn_int_set_expr_comprehension(SrcPos,
                HeadIntExpr, GeneratorExprs, MaybeBoolCondExpr)
        )
    ;
        RawExpr = anon_var,
        IntSetExpr = tmzn_int_set_expr_var(SrcPos, tmzn_int_set_var_anon)
    ;
        RawExpr = if_then_else(_CondExpr, _ThenExpr, _ElseExpr),
        io.write_string(US, "INT SET: IF_THEN_ELSE\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "if_then_else", !Specs),
        IntSetExpr = tmzn_int_set_expr_const(SrcPos, set.init)
    ;
        RawExpr = let(_LetVars, _LetExpr),
        io.write_string(US, "INT SET: LET\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "let", !Specs),
        IntSetExpr = tmzn_int_set_expr_const(SrcPos, set.init)
    ;
        RawExpr = coerce(FromTI, ToTI, CoerceExpr),
        CoerceContext = [["In coercion.\n"]],
        type_inst_to_mzn_type(CoerceContext, FromTI, FromInst, FromType),
        type_inst_to_mzn_type(CoerceContext, ToTI, ToInst, ToType),
        ( if
            FromInst = par,
            ToInst = var,
            FromType = ToType
        then
            Arg1Nest = nest(SrcPos, is_unop_arg("coerce")),
            convert_int_set_expr_to_tmzn(US, Arg1Nest, CoerceExpr, IntSetExpr,
                !Specs, !IO)
        else
            io.write_string(US, "INT SET: COERCE\n", !IO),
            add_nyi_error($pred, phase_conversion, SrcPos, "coerce", !Specs),
            IntSetExpr = tmzn_int_set_expr_const(SrcPos, set.init)
        )
    ;
        RawExpr = lit_tuple(_),
        add_internal_error($pred, phase_conversion, SrcPos,
            "non-MiniZinc expression", !Specs),
        IntSetExpr = tmzn_int_set_expr_const(SrcPos, set.init)
    ).

:- pred convert_builtin_app_to_int_set_expr(io.output_stream::in, src_pos::in,
    string::in, builtin_op_type::in, list(expr)::in, tmzn_int_set_expr::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_builtin_app_to_int_set_expr(US, SrcPos, PredName, BuiltinOp, Args,
        IntSetExpr, !Specs, !IO) :-
    (
        BuiltinOp = bo_dom,
        I2ISOp = i2is_dom,
        ( if Args = [Arg1] then
            builtin_op_table(OpStr, _, _, _, BuiltinOp),
            Arg1Nest = nest(SrcPos, is_unop_arg(OpStr)),
            convert_int_expr_to_tmzn(US, Arg1Nest, Arg1, Int1, !Specs, !IO),
            IntSetExpr = tmzn_int_set_expr_i2is(SrcPos, I2ISOp, Int1)
        else
            io.write_string(US, "INT SET OP: bad arity for dom\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity", !Specs),
            IntSetExpr = tmzn_int_set_expr_const(SrcPos, set.init)
        )
    ;
        BuiltinOp = bo_range,
        II2ISOp = ii2is_range,
        ( if Args = [Arg1, Arg2] then
            builtin_op_table(OpStr, _, _, _, BuiltinOp),
            Arg1Nest = nest(SrcPos, is_binop_arg(OpStr, left)),
            Arg2Nest = nest(SrcPos, is_binop_arg(OpStr, right)),
            convert_int_expr_to_tmzn(US, Arg1Nest, Arg1, Int1, !Specs, !IO),
            convert_int_expr_to_tmzn(US, Arg2Nest, Arg2, Int2, !Specs, !IO),
            IntSetExpr = tmzn_int_set_expr_ii2is(SrcPos, II2ISOp, Int1, Int2)
        else
            io.write_string(US, "INT SET OP: bad arity for range\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity", !Specs),
            IntSetExpr = tmzn_int_set_expr_const(SrcPos, set.init)
        )
    ;
        (
            BuiltinOp = bo_diff,
            ISIS2ISOp = xsxs2xs_diff
        ;
            BuiltinOp = bo_intersect,
            ISIS2ISOp = xsxs2xs_intersect
        ;
            BuiltinOp = bo_union,
            ISIS2ISOp = xsxs2xs_union
        ),
        ( if Args = [Arg1, Arg2] then
            builtin_op_table(OpStr, _, _, _, BuiltinOp),
            Arg1Nest = nest(SrcPos, is_binop_arg(OpStr, left)),
            Arg2Nest = nest(SrcPos, is_binop_arg(OpStr, right)),
            convert_int_set_expr_to_tmzn(US, Arg1Nest, Arg1, IntSet1,
                !Specs, !IO),
            convert_int_set_expr_to_tmzn(US, Arg2Nest, Arg2, IntSet2,
                !Specs, !IO),
            IntSetExpr = tmzn_int_set_expr_isis2is(SrcPos, ISIS2ISOp,
                IntSet1, IntSet2)
        else
            io.write_string(US,
                "INT SET OP: bad arity for diff/intersect/union\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity", !Specs),
            IntSetExpr = tmzn_int_set_expr_const(SrcPos, set.init)
        )
    ;
        ( BuiltinOp = bo_abort
        ; BuiltinOp = bo_lb
        ; BuiltinOp = bo_ub
        ; BuiltinOp = bo_dom_array
        ; BuiltinOp = bo_lb_array
        ; BuiltinOp = bo_ub_array
        ; BuiltinOp = bo_dom_size
        ; BuiltinOp = bo_exists
        ; BuiltinOp = bo_forall
        ; BuiltinOp = bo_iffall
        ; BuiltinOp = bo_xorall
        ; BuiltinOp = bo_not
        ; BuiltinOp = bo_assert
        ; BuiltinOp = bo_and
        ; BuiltinOp = bo_or
        ; BuiltinOp = bo_xor
        ; BuiltinOp = bo_imp2l
        ; BuiltinOp = bo_imp2r
        ; BuiltinOp = bo_biimp
        ; BuiltinOp = bo_negate
        ; BuiltinOp = bo_abs
        ; BuiltinOp = bo_add
        ; BuiltinOp = bo_sub
        ; BuiltinOp = bo_mul
        ; BuiltinOp = bo_fdiv
        ; BuiltinOp = bo_idiv
        ; BuiltinOp = bo_mod
        ; BuiltinOp = bo_min
        ; BuiltinOp = bo_max
        ; BuiltinOp = bo_array_min
        ; BuiltinOp = bo_array_max
        ; BuiltinOp = bo_array_sum
        ; BuiltinOp = bo_array_product
        ; BuiltinOp = bo_array_length
        ; BuiltinOp = bo_eq
        ; BuiltinOp = bo_ne
        ; BuiltinOp = bo_lt
        ; BuiltinOp = bo_le
        ; BuiltinOp = bo_gt
        ; BuiltinOp = bo_ge
        ; BuiltinOp = bo_in
        ; BuiltinOp = bo_subset
        ; BuiltinOp = bo_superset
        ; BuiltinOp = bo_bool2int
        ; BuiltinOp = bo_int2float
        ; BuiltinOp = bo_ceil
        ; BuiltinOp = bo_floor
        ; BuiltinOp = bo_round
        ; BuiltinOp = bo_exp
        ; BuiltinOp = bo_ln
        ; BuiltinOp = bo_log10
        ; BuiltinOp = bo_log2
        ; BuiltinOp = bo_log
        ; BuiltinOp = bo_pow
        ; BuiltinOp = bo_sqrt
        ; BuiltinOp = bo_sin
        ; BuiltinOp = bo_cos
        ; BuiltinOp = bo_tan
        ; BuiltinOp = bo_sinh
        ; BuiltinOp = bo_cosh
        ; BuiltinOp = bo_tanh
        ; BuiltinOp = bo_asin
        ; BuiltinOp = bo_acos
        ; BuiltinOp = bo_atan
        ; BuiltinOp = bo_card
        ; BuiltinOp = bo_set2array
        ; BuiltinOp = bo_array_intersect
        ; BuiltinOp = bo_array_union
        ; BuiltinOp = bo_append
        ; BuiltinOp = bo_array1d
        ; BuiltinOp = bo_array2d
        ; BuiltinOp = bo_array3d
        ; BuiltinOp = bo_array4d
        ; BuiltinOp = bo_array5d
        ; BuiltinOp = bo_array6d
        ; BuiltinOp = bo_index_set
        ; BuiltinOp = bo_index_set_1of2
        ; BuiltinOp = bo_index_set_2of2
        ; BuiltinOp = bo_index_set_1of3
        ; BuiltinOp = bo_index_set_2of3
        ; BuiltinOp = bo_index_set_3of3
        ; BuiltinOp = bo_index_set_1of4
        ; BuiltinOp = bo_index_set_2of4
        ; BuiltinOp = bo_index_set_3of4
        ; BuiltinOp = bo_index_set_4of4
        ; BuiltinOp = bo_show
        ; BuiltinOp = bo_show_int
        ; BuiltinOp = bo_show_float
        ; BuiltinOp = bo_concat
        ; BuiltinOp = bo_join
        ; BuiltinOp = bo_fix                % XXX
        ),
        io.format(US, "INT SET OP: bad op %s\n", [s(PredName)], !IO),
        add_internal_error($pred, phase_conversion, SrcPos, "bad op", !Specs),
        IntSetExpr = tmzn_int_set_expr_const(SrcPos, set.init)
    ).

%-----------------------------------------------------------------------------%

:- pred convert_int_array_expr_to_tmzn(io.output_stream::in, nest_pos::in,
    expr::in, tmzn_int_array_expr::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_int_array_expr_to_tmzn(US, NestPos, Expr, IntArrayExpr, !Specs, !IO) :-
    Expr = expr(RawExpr, AnnExprs, ExprInfo),
    ExprInfo = expr_info(SrcLocn, TI),
    SrcPos = src_pos(NestPos, SrcLocn),
    % XXX _IndexTI
    ( if
        TI = ti_array(_IndexTI, EltTI),
        ( EltTI = ti_par_int ; EltTI = ti_var_int )
    then
        true
    else
        io.write_string(US, "INT ARRAY: BAD TI\n", !IO),
        add_internal_error($pred, phase_conversion, SrcPos, "bad TI", !Specs)
    ),
    (
        AnnExprs = []
    ;
        AnnExprs = [_ | _],
        io.write_string(US, "INT ARRAY: ANNS ", !IO),
        io.write(US, AnnExprs, !IO),
        io.nl(US, !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "anns", !Specs)
    ),
    (
        RawExpr = ident(VarId),
        StrVar = tmzn_int_array_var_named(id_name(VarId)),
        IntArrayExpr = tmzn_int_array_expr_var(SrcPos, StrVar)
    ;
        RawExpr = lit(_Literal),
        io.write_string(US, "INT ARRAY: LIT\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit", !Specs),
        IntArrayExpr = tmzn_int_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = app(PredId, _ProcNo, _AppKind, _ArgExprs),
        PredName = id_name(PredId),
        io.format(US, "INT ARRAY: APP %s\n", [s(PredName)], !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "app", !Specs),
        IntArrayExpr = tmzn_int_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = array_access(_ArrayExpr, _IndexExprs),
        io.write_string(US, "INT ARRAY: ARRAY_ACCESS\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "array_access", !Specs),
        IntArrayExpr = tmzn_int_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = lit_set(_ItemExprs),
        io.write_string(US, "INT ARRAY: LIT_SET\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit set", !Specs),
        IntArrayExpr = tmzn_int_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = lit_simple_array(ItemExprs),
        list.length(ItemExprs, N),
        IRs = [index_range(1, N)],
        pos_map_foldl2(SrcPos, islk_simple_array, 1,
            convert_int_expr_to_tmzn(US),
            ItemExprs, IntExprs, !Specs, !IO),
        ( if
            list.map(try_project_int_expr_to_const, IntExprs, Ints)
        then
            IntArrayExpr = tmzn_int_array_expr_consts(SrcPos, IRs, Ints)
        else if
            list.map(try_project_int_expr_to_var, IntExprs, IntVars)
        then
            IntArrayExpr = tmzn_int_array_expr_vars(SrcPos, IRs, IntVars)
        else
            IntArrayExpr = tmzn_int_array_expr_exprs(SrcPos, IRs, IntExprs)
        )
    ;
        RawExpr = lit_ann(_AnnId, _ArgExprs),
        io.write_string(US, "INT ARRAY: LIT_ANN\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit ann", !Specs),
        IntArrayExpr = tmzn_int_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = comprehension(CompKind, Generators, MaybeCondExpr),
        (
            MaybeCondExpr = no,
            MaybeBoolCondExpr = no
        ;
            MaybeCondExpr = yes(CondExpr),
            convert_bool_expr_to_tmzn(US, nest(SrcPos, is_compre_cond),
                CondExpr, BoolCondExpr, !Specs, !IO),
            MaybeBoolCondExpr = yes(BoolCondExpr)
        ),
        (
            CompKind = simple_array_comp(HeadExpr),
            convert_int_expr_to_tmzn(US, nest(SrcPos, is_compre_head),
                HeadExpr, HeadIntExpr, !Specs, !IO),
            pos_map_foldl2(SrcPos, islk_compre_array, 1,
                convert_generator_to_tmzn(US),
                Generators, GeneratorExprs, !Specs, !IO),
            IntArrayExpr = tmzn_int_array_expr_comprehension(SrcPos,
                HeadIntExpr, GeneratorExprs, MaybeBoolCondExpr)
        ;
            CompKind = set_comp(_),
            io.write_string(US, "BOOL ARRAY: SET COMPREHENSION\n", !IO),
            add_nyi_error($pred, phase_conversion, SrcPos,
                "set comprehension", !Specs),
            IntArrayExpr = tmzn_int_array_expr_consts(SrcPos, [], [])
        )
    ;
        RawExpr = anon_var,
        IntArrayExpr = tmzn_int_array_expr_var(SrcPos, tmzn_int_array_var_anon)
    ;
        RawExpr = if_then_else(_CondExpr, _ThenExpr, _ElseExpr),
        io.write_string(US, "INT ARRAY: IF_THEN_ELSE\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "if_then_else", !Specs),
        IntArrayExpr = tmzn_int_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = let(_LetVars, _LetExpr),
        io.write_string(US, "INT ARRAY: LET\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "let", !Specs),
        IntArrayExpr = tmzn_int_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = coerce(FromTI, ToTI, CoerceExpr),
        ( if
            FromTI = ti_par_set(ti_par_int),
            ToTI = ti_array(ti_par_int, ti_par_int)
        then
            Arg1Nest = nest(SrcPos, is_unop_arg("coerce")),
            convert_int_set_expr_to_tmzn(US, Arg1Nest, CoerceExpr, IntSet,
                !Specs, !IO),
            IntArrayExpr = tmzn_int_array_expr_from_set(SrcPos, IntSet)
        else
            io.write_string(US, "INT ARRAY: COERCE\n", !IO),
            add_nyi_error($pred, phase_conversion, SrcPos, "coerce", !Specs),
            IntArrayExpr = tmzn_int_array_expr_consts(SrcPos, [], [])
        )
    ;
        RawExpr = lit_tuple(_),
        add_internal_error($pred, phase_conversion, SrcPos,
            "non-MiniZinc expression", !Specs),
        IntArrayExpr = tmzn_int_array_expr_consts(SrcPos, [], [])
    ).

%-----------------------------------------------------------------------------%

:- pred convert_int_set_array_expr_to_tmzn(io.output_stream::in, nest_pos::in,
    expr::in, tmzn_int_set_array_expr::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_int_set_array_expr_to_tmzn(US, NestPos, Expr, IntSetArrayExpr,
        !Specs, !IO) :-
    Expr = expr(RawExpr, AnnExprs, ExprInfo),
    ExprInfo = expr_info(SrcLocn, TI),
    SrcPos = src_pos(NestPos, SrcLocn),
    % XXX _IndexTI
    ( if
        TI = ti_array(_IndexTI, ArrayEltTI),
        (
            ArrayEltTI = ti_par_set(SetEltTI),
            ( SetEltTI = ti_par_int ; SetEltTI = ti_var_int )
        ;
            ArrayEltTI = ti_var_set(SetEltTI),
            ( SetEltTI = ti_par_int ; SetEltTI = ti_var_int )
        )
    then
        true
    else
        io.write_string(US, "INT SET ARRAY: BAD TI\n", !IO),
        add_internal_error($pred, phase_conversion, SrcPos, "bad TI", !Specs)
    ),
    (
        AnnExprs = []
    ;
        AnnExprs = [_ | _],
        io.write_string(US, "INT SET ARRAY: ANNS ", !IO),
        io.write(US, AnnExprs, !IO),
        io.nl(US, !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "anns", !Specs)
    ),
    (
        RawExpr = ident(VarId),
        StrVar = tmzn_int_set_array_var_named(id_name(VarId)),
        IntSetArrayExpr = tmzn_int_set_array_expr_var(SrcPos, StrVar)
    ;
        RawExpr = lit(_Literal),
        io.write_string(US, "INT SET ARRAY: LIT\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit", !Specs),
        IntSetArrayExpr = tmzn_int_set_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = app(PredId, _ProcNo, _AppKind, _ArgExprs),
        PredName = id_name(PredId),
        io.format(US, "INT SET ARRAY: APP %s\n", [s(PredName)], !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "app", !Specs),
        IntSetArrayExpr = tmzn_int_set_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = array_access(_ArrayExpr, _IndexExprs),
        io.write_string(US, "INT SET ARRAY: ARRAY_ACCESS\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "array_access", !Specs),
        IntSetArrayExpr = tmzn_int_set_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = lit_set(_ItemExprs),
        io.write_string(US, "INT SET ARRAY: LIT_SET\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit set", !Specs),
        IntSetArrayExpr = tmzn_int_set_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = lit_simple_array(ItemExprs),
        list.length(ItemExprs, N),
        IRs = [index_range(1, N)],
        pos_map_foldl2(SrcPos, islk_simple_array, 1,
            convert_int_set_expr_to_tmzn(US),
            ItemExprs, IntSetExprs, !Specs, !IO),
        ( if
            list.map(try_project_int_set_expr_to_const, IntSetExprs, IntSets)
        then
            IntSetArrayExpr = tmzn_int_set_array_expr_consts(SrcPos,
                IRs, IntSets)
        else if
            list.map(try_project_int_set_expr_to_var, IntSetExprs, IntSetVars)
        then
            IntSetArrayExpr = tmzn_int_set_array_expr_vars(SrcPos,
                IRs, IntSetVars)
        else
            IntSetArrayExpr = tmzn_int_set_array_expr_exprs(SrcPos,
                IRs, IntSetExprs)
        )
    ;
        RawExpr = lit_ann(_AnnId, _ArgExprs),
        io.write_string(US, "INT SET ARRAY: LIT_ANN\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit ann", !Specs),
        IntSetArrayExpr = tmzn_int_set_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = comprehension(CompKind, Generators, MaybeCondExpr),
        (
            MaybeCondExpr = no,
            MaybeBoolCondExpr = no
        ;
            MaybeCondExpr = yes(CondExpr),
            convert_bool_expr_to_tmzn(US, nest(SrcPos, is_compre_cond),
                CondExpr, BoolCondExpr, !Specs, !IO),
            MaybeBoolCondExpr = yes(BoolCondExpr)
        ),
        (
            CompKind = simple_array_comp(HeadExpr),
            convert_int_set_expr_to_tmzn(US, nest(SrcPos, is_compre_head),
                HeadExpr, HeadIntSetExpr, !Specs, !IO),
            pos_map_foldl2(SrcPos, islk_compre_array, 1,
                convert_generator_to_tmzn(US),
                Generators, GeneratorExprs, !Specs, !IO),
            IntSetArrayExpr = tmzn_int_set_array_expr_comprehension(SrcPos,
                HeadIntSetExpr, GeneratorExprs, MaybeBoolCondExpr)
        ;
            CompKind = set_comp(_),
            io.write_string(US, "BOOL ARRAY: SET COMPREHENSION\n", !IO),
            add_nyi_error($pred, phase_conversion, SrcPos,
                "set comprehension", !Specs),
            IntSetArrayExpr = tmzn_int_set_array_expr_consts(SrcPos, [], [])
        )
    ;
        RawExpr = anon_var,
        IntSetArrayExpr = tmzn_int_set_array_expr_var(SrcPos,
            tmzn_int_set_array_var_anon)
    ;
        RawExpr = if_then_else(_CondExpr, _ThenExpr, _ElseExpr),
        io.write_string(US, "INT SET ARRAY: IF_THEN_ELSE\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "if_then_else", !Specs),
        IntSetArrayExpr = tmzn_int_set_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = let(_LetVars, _LetExpr),
        io.write_string(US, "INT SET ARRAY: LET\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "let", !Specs),
        IntSetArrayExpr = tmzn_int_set_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = coerce(_FromTI, _ToTI, _CoerceExpr),
        io.write_string(US, "INT SET ARRAY: COERCE\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "coerce", !Specs),
        IntSetArrayExpr = tmzn_int_set_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = lit_tuple(_),
        add_internal_error($pred, phase_conversion, SrcPos,
            "non-MiniZinc expression", !Specs),
        IntSetArrayExpr = tmzn_int_set_array_expr_consts(SrcPos, [], [])
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred convert_float_expr_to_tmzn(io.output_stream::in, nest_pos::in,
    expr::in, tmzn_float_expr::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_float_expr_to_tmzn(US, NestPos, Expr, FloatExpr, !Specs, !IO) :-
    Expr = expr(RawExpr, AnnExprs, ExprInfo),
    ExprInfo = expr_info(SrcLocn, TI),
    SrcPos = src_pos(NestPos, SrcLocn),
    ( if ( TI = ti_par_float ; TI = ti_var_float ) then
        true
    else
        io.write_string(US, "FLOAT: BAD TI\n", !IO),
        add_internal_error($pred, phase_conversion, SrcPos, "bad TI", !Specs)
    ),
    (
        AnnExprs = []
    ;
        AnnExprs = [_ | _],
        io.write_string(US, "FLOAT: ANNS ", !IO),
        io.write(US, AnnExprs, !IO),
        io.nl(US, !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "anns", !Specs)
    ),
    (
        RawExpr = ident(VarId),
        FloatVar = tmzn_float_var_named(id_name(VarId)),
        FloatExpr = tmzn_float_expr_var(SrcPos, FloatVar)
    ;
        RawExpr = lit(Literal),
        (
            Literal = floatstr(Str),
            Float = string.det_to_float(Str),
            FloatExpr = tmzn_float_expr_const(SrcPos, Float)
        ;
            (
                Literal = bool(_),
                io.write_string(US, "FLOAT: LIT BOOL\n", !IO),
                add_internal_error($pred, phase_conversion, SrcPos,
                    "lit bool", !Specs)
            ;
                Literal = int(_),
                io.write_string(US, "FLOAT: LIT INT\n", !IO),
                add_internal_error($pred, phase_conversion, SrcPos,
                    "lit int", !Specs)
            ;
                Literal = string(_),
                io.write_string(US, "FLOAT: LIT STRING\n", !IO),
                add_internal_error($pred, phase_conversion, SrcPos,
                    "lit string", !Specs)
            ),
            FloatExpr = tmzn_float_expr_const(SrcPos, 0.0)
        )
    ;
        RawExpr = app(PredId, _ProcNo, _AppKind, ArgExprs),
        PredName = id_name(PredId),
        list.length(ArgExprs, Arity),
        ( if
            is_builtin_op(PredName, Arity, _, _, BuiltinOp)
        then
            convert_builtin_app_to_float_expr(US, SrcPos, PredName,
                BuiltinOp, ArgExprs, FloatExpr, !Specs, !IO)
        else
            io.format(US, "FLOAT: APP %s\n", [s(PredName)], !IO),
            add_nyi_error($pred, phase_conversion, SrcPos, "app", !Specs),
            FloatExpr = tmzn_float_expr_const(SrcPos, 0.0)
        )
    ;
        RawExpr = array_access(ArrayExpr, IndexExprs),
        ( if is_float_array_expr(ArrayExpr) then
            convert_float_array_expr_to_tmzn(US, nest(SrcPos, is_array_id),
                ArrayExpr, FloatArray, !Specs, !IO),
            pos_map_foldl2(SrcPos, islk_index, 1,
                convert_int_expr_to_tmzn(US),
                IndexExprs, Indexes, !Specs, !IO),
            FloatVar = tmzn_float_var_array_slot(FloatArray, Indexes),
            FloatExpr = tmzn_float_expr_var(SrcPos, FloatVar)
        else
            io.write_string(US, "INT SET: ARRAY_ACCESS\n", !IO),
            add_nyi_error($pred, phase_conversion, SrcPos,
                "array access", !Specs),
            FloatExpr = tmzn_float_expr_const(SrcPos, 0.0)
        )
    ;
        RawExpr = lit_set(_ItemExprs),
        io.write_string(US, "FLOAT: LIT_SET\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit set", !Specs),
        FloatExpr = tmzn_float_expr_const(SrcPos, 0.0)
    ;
        RawExpr = lit_simple_array(_ItemExprs),
        io.write_string(US, "FLOAT: LIT_SIMPLE_ARRAY\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "simple array", !Specs),
        FloatExpr = tmzn_float_expr_const(SrcPos, 0.0)
    ;
        RawExpr = lit_ann(_AnnId, _ArgExprs),
        io.write_string(US, "FLOAT: LIT_ANN\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit ann", !Specs),
        FloatExpr = tmzn_float_expr_const(SrcPos, 0.0)
    ;
        RawExpr = comprehension(_CompKind, _Generators, _MaybeCondExpr),
        io.write_string(US, "FLOAT: COMPREHENSION\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos,
            "comprehension", !Specs),
        FloatExpr = tmzn_float_expr_const(SrcPos, 0.0)
    ;
        RawExpr = anon_var,
        io.write_string(US, "FLOAT: ANON_VAR\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "anon_var", !Specs),
        FloatExpr = tmzn_float_expr_var(SrcPos, tmzn_float_var_anon)
    ;
        RawExpr = if_then_else(CondExpr, ThenExpr, ElseExpr),
        convert_bool_expr_to_tmzn(US, nest(SrcPos, is_cond), CondExpr, Cond,
            !Specs, !IO),
        convert_float_expr_to_tmzn(US, nest(SrcPos, is_then), ThenExpr, Then,
            !Specs, !IO),
        convert_float_expr_to_tmzn(US, nest(SrcPos, is_else), ElseExpr, Else,
            !Specs, !IO),
        FloatExpr = tmzn_float_expr_ite(SrcPos, Cond, Then, Else)
    ;
        RawExpr = let(_LetVars, _LetExpr),
        io.write_string(US, "FLOAT: LET\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "let", !Specs),
        FloatExpr = tmzn_float_expr_const(SrcPos, 0.0)
    ;
        RawExpr = coerce(FromTI, ToTI, CoerceExpr),
        CoerceContext = [["In coercion.\n"]],
        type_inst_to_mzn_type(CoerceContext, FromTI, FromInst, FromType),
        type_inst_to_mzn_type(CoerceContext, ToTI, ToInst, ToType),
        ( if
            FromInst = par,
            ToInst = var,
            FromType = ToType
        then
            Arg1Nest = nest(SrcPos, is_unop_arg("coerce")),
            convert_float_expr_to_tmzn(US, Arg1Nest, CoerceExpr, FloatExpr,
                !Specs, !IO)
        else if
            FromType = mzn_int(_),
            ToType = mzn_float(_)
        then
            Arg1Nest = nest(SrcPos, is_unop_arg("coerce")),
            convert_int_expr_to_tmzn(US, Arg1Nest, CoerceExpr, IntExpr,
                !Specs, !IO),
            FloatExpr = tmzn_float_expr_i2f(SrcPos, i2f_int2float, IntExpr)
        else
            io.write_string(US, "FLOAT: COERCE\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "coerce", !Specs),
            FloatExpr = tmzn_float_expr_const(SrcPos, 0.0)
        )
    ;
        RawExpr = lit_tuple(_),
        add_internal_error($pred, phase_conversion, SrcPos,
            "non-MiniZinc expression", !Specs),
        FloatExpr = tmzn_float_expr_const(SrcPos, 0.0)
    ).

:- pred convert_builtin_app_to_float_expr(io.output_stream::in, src_pos::in,
    string::in, builtin_op_type::in, list(expr)::in, tmzn_float_expr::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_builtin_app_to_float_expr(US, SrcPos, PredName, BuiltinOp, Args,
        FloatExpr, !Specs, !IO) :-
    (
        BuiltinOp = bo_int2float,
        I2FOp = i2f_int2float,
        ( if Args = [Arg1] then
            builtin_op_table(OpStr, _, _, _, BuiltinOp),
            Arg1Nest = nest(SrcPos, is_unop_arg(OpStr)),
            convert_int_expr_to_tmzn(US, Arg1Nest, Arg1, IntArg1, !Specs, !IO),
            FloatExpr = tmzn_float_expr_i2f(SrcPos, I2FOp, IntArg1)
        else
            io.write_string(US,
                "FLOAT OP: bad arity for i2f\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity", !Specs),
            FloatExpr = tmzn_float_expr_const(SrcPos, 0.0)
        )
    ;
        % XXX f2f_add is missing; is_builtin_op does not recognize +/1
        (
            BuiltinOp = bo_negate,
            F2FOp = f2f_sub
        ;
            BuiltinOp = bo_lb,
            F2FOp = f2f_lb
        ;
            BuiltinOp = bo_ub,
            F2FOp = f2f_ub
        ;
            BuiltinOp = bo_abs,
            F2FOp = f2f_abs
        ;
            BuiltinOp = bo_sqrt,
            F2FOp = f2f_sqrt
        ;
            BuiltinOp = bo_exp,
            F2FOp = f2f_exp
        ;
            BuiltinOp = bo_ln,
            F2FOp = f2f_ln
        ;
            BuiltinOp = bo_log10,
            F2FOp = f2f_log10
        ;
            BuiltinOp = bo_log2,
            F2FOp = f2f_log2
        ;
            BuiltinOp = bo_sin,
            F2FOp = f2f_sin
        ;
            BuiltinOp = bo_cos,
            F2FOp = f2f_cos
        ;
            BuiltinOp = bo_tan,
            F2FOp = f2f_tan
        ;
            BuiltinOp = bo_sinh,
            F2FOp = f2f_sinh
        ;
            BuiltinOp = bo_cosh,
            F2FOp = f2f_cosh
        ;
            BuiltinOp = bo_tanh,
            F2FOp = f2f_tanh
        ;
            BuiltinOp = bo_asin,
            F2FOp = f2f_asin
        ;
            BuiltinOp = bo_acos,
            F2FOp = f2f_acos
        ;
            BuiltinOp = bo_atan,
            F2FOp = f2f_atan
        ;
            BuiltinOp = bo_fix,
            F2FOp = f2f_fix
        ),
        ( if Args = [Arg1] then
            builtin_op_table(OpStr, _, _, _, BuiltinOp),
            Arg1Nest = nest(SrcPos, is_unop_arg(OpStr)),
            convert_float_expr_to_tmzn(US, Arg1Nest, Arg1, FloatArg1,
                !Specs, !IO),
            FloatExpr = tmzn_float_expr_f2f(SrcPos, F2FOp, FloatArg1)
        else
            io.write_string(US, "FLOAT OP: bad arity for i2f\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity", !Specs),
            FloatExpr = tmzn_float_expr_const(SrcPos, 0.0)
        )
    ;
        (
            BuiltinOp = bo_add,
            FF2FOp = ff2f_add
        ;
            BuiltinOp = bo_sub,
            FF2FOp = ff2f_sub
        ;
            BuiltinOp = bo_mul,
            FF2FOp = ff2f_mul
        ;
            BuiltinOp = bo_fdiv,
            FF2FOp = ff2f_div
        ;
            BuiltinOp = bo_min,
            FF2FOp = ff2f_min
        ;
            BuiltinOp = bo_max,
            FF2FOp = ff2f_max
        ;
            BuiltinOp = bo_pow,
            FF2FOp = ff2f_pow
        ;
            BuiltinOp = bo_log,
            FF2FOp = ff2f_log
        ),
        ( if Args = [Arg1, Arg2] then
            builtin_op_table(OpStr, _, _, _, BuiltinOp),
            Arg1Nest = nest(SrcPos, is_binop_arg(OpStr, left)),
            Arg2Nest = nest(SrcPos, is_binop_arg(OpStr, right)),
            convert_float_expr_to_tmzn(US, Arg1Nest, Arg1, FloatArg1,
                !Specs, !IO),
            convert_float_expr_to_tmzn(US, Arg2Nest, Arg2, FloatArg2,
                !Specs, !IO),
            FloatExpr = tmzn_float_expr_ff2f(SrcPos, FF2FOp,
                FloatArg1, FloatArg2)
        else
            io.write_string(US, "FLOAT OP: bad arity for i2f\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity", !Specs),
            FloatExpr = tmzn_float_expr_const(SrcPos, 0.0)
        )
    ;
        ( BuiltinOp = bo_abort
        ; BuiltinOp = bo_dom
        ; BuiltinOp = bo_dom_array
        ; BuiltinOp = bo_lb_array
        ; BuiltinOp = bo_ub_array
        ; BuiltinOp = bo_dom_size
        ; BuiltinOp = bo_exists
        ; BuiltinOp = bo_forall
        ; BuiltinOp = bo_iffall
        ; BuiltinOp = bo_xorall
        ; BuiltinOp = bo_not
        ; BuiltinOp = bo_assert
        ; BuiltinOp = bo_and
        ; BuiltinOp = bo_or
        ; BuiltinOp = bo_xor
        ; BuiltinOp = bo_imp2l
        ; BuiltinOp = bo_imp2r
        ; BuiltinOp = bo_biimp
        ; BuiltinOp = bo_idiv
        ; BuiltinOp = bo_mod
        ; BuiltinOp = bo_array_min
        ; BuiltinOp = bo_array_max
        ; BuiltinOp = bo_array_sum
        ; BuiltinOp = bo_array_product
        ; BuiltinOp = bo_array_length
        ; BuiltinOp = bo_eq
        ; BuiltinOp = bo_ne
        ; BuiltinOp = bo_lt
        ; BuiltinOp = bo_le
        ; BuiltinOp = bo_gt
        ; BuiltinOp = bo_ge
        ; BuiltinOp = bo_in
        ; BuiltinOp = bo_subset
        ; BuiltinOp = bo_superset
        ; BuiltinOp = bo_bool2int
        ; BuiltinOp = bo_ceil
        ; BuiltinOp = bo_floor
        ; BuiltinOp = bo_round
        ; BuiltinOp = bo_card
        ; BuiltinOp = bo_set2array
        ; BuiltinOp = bo_range
        ; BuiltinOp = bo_diff
        ; BuiltinOp = bo_intersect
        ; BuiltinOp = bo_union
        ; BuiltinOp = bo_array_intersect
        ; BuiltinOp = bo_array_union
        ; BuiltinOp = bo_append
        ; BuiltinOp = bo_array1d
        ; BuiltinOp = bo_array2d
        ; BuiltinOp = bo_array3d
        ; BuiltinOp = bo_array4d
        ; BuiltinOp = bo_array5d
        ; BuiltinOp = bo_array6d
        ; BuiltinOp = bo_index_set
        ; BuiltinOp = bo_index_set_1of2
        ; BuiltinOp = bo_index_set_2of2
        ; BuiltinOp = bo_index_set_1of3
        ; BuiltinOp = bo_index_set_2of3
        ; BuiltinOp = bo_index_set_3of3
        ; BuiltinOp = bo_index_set_1of4
        ; BuiltinOp = bo_index_set_2of4
        ; BuiltinOp = bo_index_set_3of4
        ; BuiltinOp = bo_index_set_4of4
        ; BuiltinOp = bo_show
        ; BuiltinOp = bo_show_int
        ; BuiltinOp = bo_show_float
        ; BuiltinOp = bo_concat
        ; BuiltinOp = bo_join
        ),
        io.format(US, "FLOAT OP: bad op %s\n", [s(PredName)], !IO),
        add_internal_error($pred, phase_conversion, SrcPos, "bad op", !Specs),
        FloatExpr = tmzn_float_expr_const(SrcPos, 0.0)
    ).

%-----------------------------------------------------------------------------%

:- pred convert_float_array_expr_to_tmzn(io.output_stream::in, nest_pos::in,
    expr::in, tmzn_float_array_expr::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_float_array_expr_to_tmzn(US, NestPos, Expr, FloatArrayExpr,
        !Specs, !IO) :-
    Expr = expr(RawExpr, AnnExprs, ExprInfo),
    ExprInfo = expr_info(SrcLocn, TI),
    SrcPos = src_pos(NestPos, SrcLocn),
    % XXX _IndexTI
    ( if
        TI = ti_array(_IndexTI, EltTI),
        ( EltTI = ti_par_float ; EltTI = ti_var_float )
    then
        true
    else
        io.write_string(US, "FLOAT ARRAY: BAD TI\n", !IO),
        add_internal_error($pred, phase_conversion, SrcPos, "bad TI", !Specs)
    ),
    (
        AnnExprs = []
    ;
        AnnExprs = [_ | _],
        io.write_string(US, "FLOAT ARRAY: ANNS ", !IO),
        io.write(US, AnnExprs, !IO),
        io.nl(US, !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "anns", !Specs)
    ),
    (
        RawExpr = ident(VarId),
        StrVar = tmzn_float_array_var_named(id_name(VarId)),
        FloatArrayExpr = tmzn_float_array_expr_var(SrcPos, StrVar)
    ;
        RawExpr = lit(_Literal),
        io.write_string(US, "FLOAT ARRAY: LIT\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit", !Specs),
        FloatArrayExpr = tmzn_float_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = app(PredId, _ProcNo, _AppKind, _ArgExprs),
        PredName = id_name(PredId),
        io.format(US, "FLOAT ARRAY: APP %s\n", [s(PredName)], !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "app", !Specs),
        FloatArrayExpr = tmzn_float_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = array_access(_ArrayExpr, _IndexExprs),
        io.write_string(US, "FLOAT ARRAY: ARRAY_ACCESS\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "array_access", !Specs),
        FloatArrayExpr = tmzn_float_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = lit_set(_ItemExprs),
        io.write_string(US, "FLOAT ARRAY: LIT_SET\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit set", !Specs),
        FloatArrayExpr = tmzn_float_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = lit_simple_array(ItemExprs),
        list.length(ItemExprs, N),
        IRs = [index_range(1, N)],
        pos_map_foldl2(SrcPos, islk_simple_array, 1,
            convert_float_expr_to_tmzn(US),
            ItemExprs, FloatExprs, !Specs, !IO),
        ( if
            list.map(try_project_float_expr_to_const, FloatExprs, Floats)
        then
            FloatArrayExpr = tmzn_float_array_expr_consts(SrcPos,
                IRs, Floats)
        else if
            list.map(try_project_float_expr_to_var, FloatExprs, FloatVars)
        then
            FloatArrayExpr = tmzn_float_array_expr_vars(SrcPos,
                IRs, FloatVars)
        else
            FloatArrayExpr = tmzn_float_array_expr_exprs(SrcPos,
                IRs, FloatExprs)
        )
    ;
        RawExpr = lit_ann(_AnnId, _ArgExprs),
        io.write_string(US, "FLOAT ARRAY: LIT_ANN\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit ann", !Specs),
        FloatArrayExpr = tmzn_float_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = comprehension(CompKind, Generators, MaybeCondExpr),
        (
            MaybeCondExpr = no,
            MaybeBoolCondExpr = no
        ;
            MaybeCondExpr = yes(CondExpr),
            convert_bool_expr_to_tmzn(US, nest(SrcPos, is_compre_cond),
                CondExpr, BoolCondExpr, !Specs, !IO),
            MaybeBoolCondExpr = yes(BoolCondExpr)
        ),
        (
            CompKind = simple_array_comp(HeadExpr),
            convert_float_expr_to_tmzn(US, nest(SrcPos, is_compre_head),
                HeadExpr, HeadFloatExpr, !Specs, !IO),
            pos_map_foldl2(SrcPos, islk_compre_array, 1,
                convert_generator_to_tmzn(US),
                Generators, GeneratorExprs, !Specs, !IO),
            FloatArrayExpr = tmzn_float_array_expr_comprehension(SrcPos,
                HeadFloatExpr, GeneratorExprs, MaybeBoolCondExpr)
        ;
            CompKind = set_comp(_),
            io.write_string(US, "BOOL ARRAY: SET COMPREHENSION\n", !IO),
            add_nyi_error($pred, phase_conversion, SrcPos,
                "set comprehension", !Specs),
            FloatArrayExpr = tmzn_float_array_expr_consts(SrcPos, [], [])
        )
    ;
        RawExpr = anon_var,
        FloatArrayExpr = tmzn_float_array_expr_var(SrcPos,
            tmzn_float_array_var_anon)
    ;
        RawExpr = if_then_else(_CondExpr, _ThenExpr, _ElseExpr),
        io.write_string(US, "FLOAT ARRAY: IF_THEN_ELSE\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "if_then_else", !Specs),
        FloatArrayExpr = tmzn_float_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = let(_LetVars, _LetExpr),
        io.write_string(US, "FLOAT ARRAY: LET\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "let", !Specs),
        FloatArrayExpr = tmzn_float_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = coerce(_FromTI, _ToTI, _CoerceExpr),
        io.write_string(US, "FLOAT ARRAY: COERCE\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "coerce", !Specs),
        FloatArrayExpr = tmzn_float_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = lit_tuple(_),
        add_internal_error($pred, phase_conversion, SrcPos,
            "non-MiniZinc expression", !Specs),
        FloatArrayExpr = tmzn_float_array_expr_consts(SrcPos, [], [])
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred convert_string_expr_to_tmzn(io.output_stream::in, nest_pos::in,
    expr::in, tmzn_string_expr::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_string_expr_to_tmzn(US, NestPos, Expr, StrExpr, !Specs, !IO) :-
    Expr = expr(RawExpr, AnnExprs, ExprInfo),
    ExprInfo = expr_info(SrcLocn, TI),
    SrcPos = src_pos(NestPos, SrcLocn),
    ( if TI = ti_par_string then
        true
    else
        io.write_string(US, "STRING: BAD TI\n", !IO),
        add_internal_error($pred, phase_conversion, SrcPos, "bad TI", !Specs)
    ),
    (
        AnnExprs = []
    ;
        AnnExprs = [_ | _],
        io.write_string(US, "STRING: ANNS ", !IO),
        io.write(US, AnnExprs, !IO),
        io.nl(US, !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "anns", !Specs)
    ),
    (
        RawExpr = ident(VarId),
        StrVar = tmzn_string_var_named(id_name(VarId)),
        StrExpr = tmzn_string_expr_var(SrcPos, StrVar)
    ;
        RawExpr = lit(Literal),
        (
            Literal = string(Str),
            StrExpr = tmzn_string_expr_const(SrcPos, Str)
        ;
            (
                Literal = bool(_),
                io.write_string(US, "STRING: LIT BOOL\n", !IO),
                add_nyi_error($pred, phase_conversion, SrcPos,
                    "bool lit", !Specs)
            ;
                Literal = int(_),
                io.write_string(US, "STRING: LIT INT\n", !IO),
                add_nyi_error($pred, phase_conversion, SrcPos,
                    "int lit", !Specs)
            ;
                Literal = floatstr(_),
                io.write_string(US, "STRING: LIT FLOAT\n", !IO),
                add_nyi_error($pred, phase_conversion, SrcPos,
                    "float lit", !Specs)
            ),
            StrExpr = tmzn_string_expr_const(SrcPos, "")
        )
    ;
        RawExpr = app(PredId, _ProcNo, _AppKind, ArgExprs),
        PredName = id_name(PredId),
        list.length(ArgExprs, Arity),
        ( if
            is_builtin_op(PredName, Arity, _, _, BuiltinOp)
        then
            convert_builtin_app_to_string_expr(US, SrcPos, PredName,
                BuiltinOp, ArgExprs, StrExpr, !Specs, !IO)
        else
            io.format(US, "STRING: APP %s\n", [s(PredName)], !IO),
            add_nyi_error($pred, phase_conversion, SrcPos, "app", !Specs),
            StrExpr = tmzn_string_expr_const(SrcPos, "")
        )
    ;
        RawExpr = array_access(ArrayExpr, IndexExprs),
        ( if is_string_array_expr(ArrayExpr) then
            convert_string_array_expr_to_tmzn(US, nest(SrcPos, is_array_id),
                ArrayExpr, StrArray, !Specs, !IO),
            pos_map_foldl2(SrcPos, islk_index, 1,
                convert_int_expr_to_tmzn(US),
                IndexExprs, Indexes, !Specs, !IO),
            StrVar = tmzn_string_var_array_slot(StrArray, Indexes),
            StrExpr = tmzn_string_expr_var(SrcPos, StrVar)
        else
            io.write_string(US, "STRING: ARRAY_ACCESS\n", !IO),
            add_nyi_error($pred, phase_conversion, SrcPos,
                "array_access", !Specs),
            StrExpr = tmzn_string_expr_const(SrcPos, "")
        )
    ;
        RawExpr = lit_set(_ItemExprs),
        io.write_string(US, "STRING: LIT_SET\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos,
            "lit_set", !Specs),
        StrExpr = tmzn_string_expr_const(SrcPos, "")
    ;
        RawExpr = lit_simple_array(_ItemExprs),
        io.write_string(US, "STRING: LIT_SIMPLE_ARRAY\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos,
            "lit_simple_array", !Specs),
        StrExpr = tmzn_string_expr_const(SrcPos, "")
    ;
        RawExpr = lit_ann(_AnnId, _ArgExprs),
        io.write_string(US, "STRING: LIT_ANN\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos,
            "lit_ann", !Specs),
        StrExpr = tmzn_string_expr_const(SrcPos, "")
    ;
        RawExpr = comprehension(_CompKind, _Generators, _MaybeCondExpr),
        io.write_string(US, "STRING: COMPREHENSION\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos,
            "comprehension", !Specs),
        StrExpr = tmzn_string_expr_const(SrcPos, "")
    ;
        RawExpr = anon_var,
        StrExpr = tmzn_string_expr_var(SrcPos, tmzn_string_var_anon)
    ;
        RawExpr = if_then_else(CondExpr, ThenExpr, ElseExpr),
        convert_bool_expr_to_tmzn(US, nest(SrcPos, is_cond),
            CondExpr, Cond, !Specs, !IO),
        convert_string_expr_to_tmzn(US, nest(SrcPos, is_then),
            ThenExpr, Then, !Specs, !IO),
        convert_string_expr_to_tmzn(US, nest(SrcPos, is_else),
            ElseExpr, Else, !Specs, !IO),
        StrExpr = tmzn_string_expr_ite(SrcPos, Cond, Then, Else)
    ;
        RawExpr = let(_LetVars, _LetExpr),
        io.write_string(US, "STRING: LET\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "let", !Specs),
        StrExpr = tmzn_string_expr_const(SrcPos, "")
    ;
        RawExpr = coerce(_FromTI, _ToTI, _CoerceExpr),
        io.write_string(US, "STRING: COERCE\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "coerce", !Specs),
        StrExpr = tmzn_string_expr_const(SrcPos, "")
    ;
        RawExpr = lit_tuple(_),
        add_internal_error($pred, phase_conversion, SrcPos,
            "non-MiniZinc expression", !Specs),
        StrExpr = tmzn_string_expr_const(SrcPos, "")
    ).

:- pred convert_builtin_app_to_string_expr(io.output_stream::in, src_pos::in,
    string::in, builtin_op_type::in, list(expr)::in, tmzn_string_expr::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_builtin_app_to_string_expr(US, SrcPos, PredName, BuiltinOp, Args,
        StrExpr, !Specs, !IO) :-
    (
        BuiltinOp = bo_append,
        SS2SOp = ss2s_append,
        ( if Args = [Arg1, Arg2] then
            builtin_op_table(OpStr, _, _, _, BuiltinOp),
            Arg1Nest = nest(SrcPos, is_binop_arg(OpStr, left)),
            Arg2Nest = nest(SrcPos, is_binop_arg(OpStr, right)),
            convert_string_expr_to_tmzn(US, Arg1Nest, Arg1, Str1,
                !Specs, !IO),
            convert_string_expr_to_tmzn(US, Arg2Nest, Arg2, Str2,
                !Specs, !IO),
            StrExpr = tmzn_string_expr_ss2s(SrcPos, SS2SOp, Str1, Str2)
        else
            io.write_string(US,
                "STRING OP: bad arity for append\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity for append", !Specs),
            StrExpr = tmzn_string_expr_const(SrcPos, "")
        )
    ;
        BuiltinOp = bo_show,
        X2SOp = x2s_show,
        ( if Args = [Arg1] then
            Arg1Nest = nest(SrcPos, is_unop_arg("show")),
            convert_general_expr_to_tmzn(US, Arg1Nest, Arg1, GenExpr1,
                !Specs, !IO),
            StrExpr = tmzn_string_expr_x2s(SrcPos, X2SOp, GenExpr1)
        else
            io.write_string(US,
                "STRING OP: bad arity for show\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity for show", !Specs),
            StrExpr = tmzn_string_expr_const(SrcPos, "")
        )
    ;
        BuiltinOp = bo_show_int,
        II2SOp = ii2s_show_int,
        ( if Args = [Arg1, Arg2] then
            Arg1Nest = nest(SrcPos, is_arg("show_int", 1)),
            Arg2Nest = nest(SrcPos, is_arg("show_int", 2)),
            convert_int_expr_to_tmzn(US, Arg1Nest, Arg1, IntExpr1,
                !Specs, !IO),
            convert_int_expr_to_tmzn(US, Arg2Nest, Arg2, IntExpr2,
                !Specs, !IO),
            StrExpr = tmzn_string_expr_ii2s(SrcPos, II2SOp, IntExpr1,
                IntExpr2)
          else
            io.write_string(US,
                "STRING OP: bad arity for show_int\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity for show_int", !Specs),
            StrExpr = tmzn_string_expr_const(SrcPos, "")
        )
    ;
        BuiltinOp = bo_show_float,
        IIF2SOp = iif2s_show_float,
        ( if Args = [Arg1, Arg2, Arg3] then
            Arg1Nest = nest(SrcPos, is_arg("show_float", 1)),
            Arg2Nest = nest(SrcPos, is_arg("show_float", 2)),
            Arg3Nest = nest(SrcPos, is_arg("show_float", 3)),
            convert_int_expr_to_tmzn(US, Arg1Nest, Arg1, IntExpr1,
                !Specs, !IO),
            convert_int_expr_to_tmzn(US, Arg2Nest, Arg2, IntExpr2,
                !Specs, !IO),
            convert_float_expr_to_tmzn(US, Arg3Nest, Arg3, FloatExpr3,
                !Specs, !IO),
            StrExpr = tmzn_string_expr_iif2s(SrcPos, IIF2SOp, IntExpr1,
                IntExpr2, FloatExpr3)
         else
            io.write_string(US,
                "STRING OP: bad arity for show_float\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity for show_float", !Specs),
            StrExpr = tmzn_string_expr_const(SrcPos, "")
        )
    ;
        BuiltinOp = bo_concat,
        SA2SOp = sa2s_concat,
        ( if Args = [Arg1] then
            Arg1Nest = nest(SrcPos, is_arg("concat", 1)),
            convert_string_array_expr_to_tmzn(US, Arg1Nest, Arg1,
                StrArrayExpr1, !Specs, !IO),
            StrExpr = tmzn_string_expr_sa2s(SrcPos, SA2SOp, StrArrayExpr1)
        else
            io.write_string(US,
                "STRING OP: bad arity for concat\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity for concat", !Specs),
            StrExpr = tmzn_string_expr_const(SrcPos, "")
        )
    ;
        BuiltinOp = bo_join,
        SSA2SOp = ssa2s_join,
        ( if Args = [Arg1, Arg2] then
            Arg1Nest = nest(SrcPos, is_arg("join", 1)),
            Arg2Nest = nest(SrcPos, is_arg("join", 2)),
            convert_string_expr_to_tmzn(US, Arg1Nest, Arg1,
                StrExpr1, !Specs, !IO),
            convert_string_array_expr_to_tmzn(US, Arg2Nest, Arg2,   
                StrArrayExpr2, !Specs, !IO),
            StrExpr = tmzn_string_expr_ssa2s(SrcPos, SSA2SOp, StrExpr1,
                StrArrayExpr2)
        else
            io.write_string(US,
                "STRING OP: bad arity for join\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity for join", !Specs),
            StrExpr = tmzn_string_expr_const(SrcPos, "")
        )
    ;
        ( BuiltinOp = bo_abort
        ; BuiltinOp = bo_dom
        ; BuiltinOp = bo_lb
        ; BuiltinOp = bo_ub
        ; BuiltinOp = bo_dom_array
        ; BuiltinOp = bo_lb_array
        ; BuiltinOp = bo_ub_array
        ; BuiltinOp = bo_dom_size
        ; BuiltinOp = bo_exists
        ; BuiltinOp = bo_forall
        ; BuiltinOp = bo_iffall
        ; BuiltinOp = bo_xorall
        ; BuiltinOp = bo_not
        ; BuiltinOp = bo_assert
        ; BuiltinOp = bo_and
        ; BuiltinOp = bo_or
        ; BuiltinOp = bo_xor
        ; BuiltinOp = bo_imp2r
        ; BuiltinOp = bo_imp2l
        ; BuiltinOp = bo_biimp
        ; BuiltinOp = bo_negate
        ; BuiltinOp = bo_abs
        ; BuiltinOp = bo_add
        ; BuiltinOp = bo_sub
        ; BuiltinOp = bo_mul
        ; BuiltinOp = bo_fdiv
        ; BuiltinOp = bo_idiv
        ; BuiltinOp = bo_mod
        ; BuiltinOp = bo_min
        ; BuiltinOp = bo_max
        ; BuiltinOp = bo_array_min
        ; BuiltinOp = bo_array_max
        ; BuiltinOp = bo_array_sum
        ; BuiltinOp = bo_array_product
        ; BuiltinOp = bo_array_length
        ; BuiltinOp = bo_eq
        ; BuiltinOp = bo_ne
        ; BuiltinOp = bo_lt
        ; BuiltinOp = bo_le
        ; BuiltinOp = bo_gt
        ; BuiltinOp = bo_ge
        ; BuiltinOp = bo_in
        ; BuiltinOp = bo_subset
        ; BuiltinOp = bo_superset
        ; BuiltinOp = bo_bool2int
        ; BuiltinOp = bo_int2float
        ; BuiltinOp = bo_ceil
        ; BuiltinOp = bo_floor
        ; BuiltinOp = bo_round
        ; BuiltinOp = bo_exp
        ; BuiltinOp = bo_ln
        ; BuiltinOp = bo_log10
        ; BuiltinOp = bo_log2
        ; BuiltinOp = bo_log
        ; BuiltinOp = bo_pow
        ; BuiltinOp = bo_sqrt
        ; BuiltinOp = bo_sin
        ; BuiltinOp = bo_cos
        ; BuiltinOp = bo_tan
        ; BuiltinOp = bo_sinh
        ; BuiltinOp = bo_cosh
        ; BuiltinOp = bo_tanh
        ; BuiltinOp = bo_asin
        ; BuiltinOp = bo_acos
        ; BuiltinOp = bo_atan
        ; BuiltinOp = bo_card
        ; BuiltinOp = bo_set2array
        ; BuiltinOp = bo_range
        ; BuiltinOp = bo_diff
        ; BuiltinOp = bo_intersect
        ; BuiltinOp = bo_union
        ; BuiltinOp = bo_array_intersect
        ; BuiltinOp = bo_array_union
        ; BuiltinOp = bo_array1d
        ; BuiltinOp = bo_array2d
        ; BuiltinOp = bo_array3d
        ; BuiltinOp = bo_array4d
        ; BuiltinOp = bo_array5d
        ; BuiltinOp = bo_array6d
        ; BuiltinOp = bo_index_set
        ; BuiltinOp = bo_index_set_1of2
        ; BuiltinOp = bo_index_set_2of2
        ; BuiltinOp = bo_index_set_1of3
        ; BuiltinOp = bo_index_set_2of3
        ; BuiltinOp = bo_index_set_3of3
        ; BuiltinOp = bo_index_set_1of4
        ; BuiltinOp = bo_index_set_2of4
        ; BuiltinOp = bo_index_set_3of4
        ; BuiltinOp = bo_index_set_4of4
        ; BuiltinOp = bo_fix                % XXX
        ),
        io.format(US, "STRING OP: bad op %s\n", [s(PredName)], !IO),
        add_internal_error($pred, phase_conversion, SrcPos, "bad op", !Specs),
        StrExpr = tmzn_string_expr_const(SrcPos, "")
    ).

:- pred convert_string_array_expr_to_tmzn(io.output_stream::in, nest_pos::in,
    expr::in, tmzn_string_array_expr::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_string_array_expr_to_tmzn(US, NestPos, Expr, StrArrayExpr,
        !Specs, !IO) :-
    Expr = expr(RawExpr, AnnExprs, ExprInfo),
    ExprInfo = expr_info(SrcLocn, TI),
    SrcPos = src_pos(NestPos, SrcLocn),
    % XXX _IndexTI
    ( if
        TI = ti_array(_IndexTI, EltTI),
        EltTI = ti_par_string
    then
        true
    else
        io.write_string(US, "STRING ARRAY: BAD TI\n", !IO),
        add_internal_error($pred, phase_conversion, SrcPos, "bad TI", !Specs)
    ),
    (
        AnnExprs = []
    ;
        AnnExprs = [_ | _],
        io.write_string(US, "STRING ARRAY: ANNS ", !IO),
        io.write(US, AnnExprs, !IO),
        io.nl(US, !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "anns", !Specs)
    ),
    (
        RawExpr = ident(VarId),
        StrVar = tmzn_string_array_var_named(id_name(VarId)),
        StrArrayExpr = tmzn_string_array_expr_var(SrcPos, StrVar)
    ;
        RawExpr = lit(_Literal),
        io.write_string(US, "STRING ARRAY: LIT\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit", !Specs),
        StrArrayExpr = tmzn_string_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = app(PredId, _ProcNo, _AppKind, ArgExprs),
        PredName = id_name(PredId),
        list.length(ArgExprs, Arity),
        ( if
            is_builtin_op(PredName, Arity, _, _, BuiltinOp)
        then
            convert_builtin_app_to_string_array_expr(US, SrcPos, PredName,
                BuiltinOp, ArgExprs, StrArrayExpr, !Specs, !IO)
        else
            io.format(US, "STRING: ARRAY APP %s\n", [s(PredName)], !IO),
            add_nyi_error($pred, phase_conversion, SrcPos, "app", !Specs),
            StrArrayExpr = tmzn_string_array_expr_consts(SrcPos, [], [])
        )
    ;
        RawExpr = array_access(_ArrayExpr, _IndexExprs),
        io.write_string(US, "STRING ARRAY: ARRAY_ACCESS\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "array_access", !Specs),
        StrArrayExpr = tmzn_string_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = lit_set(_ItemExprs),
        io.write_string(US, "STRING ARRAY: LIT_SET\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit_set", !Specs),
        StrArrayExpr = tmzn_string_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = lit_simple_array(ItemExprs),
        list.length(ItemExprs, N),
        IRs = [index_range(1, N)],
        pos_map_foldl2(SrcPos, islk_simple_array, 1,
            convert_string_expr_to_tmzn(US),
            ItemExprs, StrExprs, !Specs, !IO),
        ( if
            list.map(try_project_string_expr_to_const, StrExprs, Strs)
        then
            StrArrayExpr = tmzn_string_array_expr_consts(SrcPos, IRs, Strs)
        else
            StrArrayExpr = tmzn_string_array_expr_exprs(SrcPos, IRs, StrExprs)
        )
    ;
        RawExpr = lit_ann(_AnnId, _ArgExprs),
        io.write_string(US, "STRING ARRAY: LIT_ANN\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "lit_ann", !Specs),
        StrArrayExpr = tmzn_string_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = comprehension(CompKind, Generators, MaybeCondExpr),
        (
            MaybeCondExpr = no,
            MaybeBoolCondExpr = no
        ;
            MaybeCondExpr = yes(CondExpr),
            convert_bool_expr_to_tmzn(US, nest(SrcPos, is_compre_cond),
                CondExpr, BoolCondExpr, !Specs, !IO),
            MaybeBoolCondExpr = yes(BoolCondExpr)
        ),
        (
            CompKind = simple_array_comp(HeadExpr),
            convert_string_expr_to_tmzn(US, nest(SrcPos, is_compre_head),
                HeadExpr, HeadStrExpr, !Specs, !IO),
            pos_map_foldl2(SrcPos, islk_compre_array, 1,
                convert_generator_to_tmzn(US),
                Generators, GeneratorExprs, !Specs, !IO),
            StrArrayExpr = tmzn_string_array_expr_comprehension(SrcPos,
                HeadStrExpr, GeneratorExprs, MaybeBoolCondExpr)
        ;
            CompKind = set_comp(_),
            io.write_string(US, "STRING ARRAY: SET COMPREHENSION\n", !IO),
            add_nyi_error($pred, phase_conversion, SrcPos, "set_comp", !Specs),
            StrArrayExpr = tmzn_string_array_expr_consts(SrcPos, [], [])
        )
    ;
        RawExpr = anon_var,
        io.write_string(US, "STRING ARRAY: ANON_VAR\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "anon_var", !Specs),
        StrArrayExpr = tmzn_string_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = if_then_else(_CondExpr, _ThenExpr, _ElseExpr),
        io.write_string(US, "STRING ARRAY: IF_THEN_ELSE\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "if_then_else", !Specs),
        StrArrayExpr = tmzn_string_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = let(_LetVars, _LetExpr),
        io.write_string(US, "STRING ARRAY: LET\n", !IO),
        add_nyi_error($pred, phase_conversion, SrcPos, "let", !Specs),
        StrArrayExpr = tmzn_string_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = coerce(_FromTI, _ToTI, _CoerceExpr),
        add_nyi_error($pred, phase_conversion, SrcPos, "coerce", !Specs),
        StrArrayExpr = tmzn_string_array_expr_consts(SrcPos, [], [])
    ;
        RawExpr = lit_tuple(_),
        add_internal_error($pred, phase_conversion, SrcPos,
            "non-MiniZinc expression", !Specs),
        StrArrayExpr = tmzn_string_array_expr_consts(SrcPos, [], [])
    ).

:- pred convert_builtin_app_to_string_array_expr(io.output_stream::in,
    src_pos::in, string::in, builtin_op_type::in, list(expr)::in,
    tmzn_string_array_expr::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_builtin_app_to_string_array_expr(US, SrcPos, PredName, BuiltinOp, Args,
        StrArrayExpr, !Specs, !IO) :-
    (
        BuiltinOp = bo_append,
        SASA2SAOp = xaxa2xa_append,
        ( if Args = [Arg1, Arg2] then
            builtin_op_table(OpStr, _, _, _, BuiltinOp),
            Arg1Nest = nest(SrcPos, is_binop_arg(OpStr, left)),
            Arg2Nest = nest(SrcPos, is_binop_arg(OpStr, right)),
            convert_string_array_expr_to_tmzn(US, Arg1Nest, Arg1, Array1,
                !Specs, !IO),
            convert_string_array_expr_to_tmzn(US, Arg2Nest, Arg2, Array2,
                !Specs, !IO),
            StrArrayExpr = tmzn_string_array_expr_sasa2sa(SrcPos, SASA2SAOp,
                Array1, Array2)
        else
            io.write_string(US,
                "STRING ARRAY OP: bad arity for append\n", !IO),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad arity", !Specs),
            StrArrayExpr = tmzn_string_array_expr_consts(SrcPos, [], [])
        )
    ;
        ( BuiltinOp = bo_abort
        ; BuiltinOp = bo_dom
        ; BuiltinOp = bo_lb
        ; BuiltinOp = bo_ub
        ; BuiltinOp = bo_dom_array
        ; BuiltinOp = bo_lb_array
        ; BuiltinOp = bo_ub_array
        ; BuiltinOp = bo_dom_size
        ; BuiltinOp = bo_exists
        ; BuiltinOp = bo_forall
        ; BuiltinOp = bo_iffall
        ; BuiltinOp = bo_xorall
        ; BuiltinOp = bo_not
        ; BuiltinOp = bo_assert
        ; BuiltinOp = bo_and
        ; BuiltinOp = bo_or
        ; BuiltinOp = bo_xor
        ; BuiltinOp = bo_imp2r
        ; BuiltinOp = bo_imp2l
        ; BuiltinOp = bo_biimp
        ; BuiltinOp = bo_negate
        ; BuiltinOp = bo_abs
        ; BuiltinOp = bo_add
        ; BuiltinOp = bo_sub
        ; BuiltinOp = bo_mul
        ; BuiltinOp = bo_fdiv
        ; BuiltinOp = bo_idiv
        ; BuiltinOp = bo_mod
        ; BuiltinOp = bo_min
        ; BuiltinOp = bo_max
        ; BuiltinOp = bo_array_min
        ; BuiltinOp = bo_array_max
        ; BuiltinOp = bo_array_sum
        ; BuiltinOp = bo_array_product
        ; BuiltinOp = bo_array_length
        ; BuiltinOp = bo_eq
        ; BuiltinOp = bo_ne
        ; BuiltinOp = bo_lt
        ; BuiltinOp = bo_le
        ; BuiltinOp = bo_gt
        ; BuiltinOp = bo_ge
        ; BuiltinOp = bo_in
        ; BuiltinOp = bo_subset
        ; BuiltinOp = bo_superset
        ; BuiltinOp = bo_bool2int
        ; BuiltinOp = bo_int2float
        ; BuiltinOp = bo_ceil
        ; BuiltinOp = bo_floor
        ; BuiltinOp = bo_round
        ; BuiltinOp = bo_exp
        ; BuiltinOp = bo_ln
        ; BuiltinOp = bo_log10
        ; BuiltinOp = bo_log2
        ; BuiltinOp = bo_log
        ; BuiltinOp = bo_pow
        ; BuiltinOp = bo_sqrt
        ; BuiltinOp = bo_sin
        ; BuiltinOp = bo_cos
        ; BuiltinOp = bo_tan
        ; BuiltinOp = bo_sinh
        ; BuiltinOp = bo_cosh
        ; BuiltinOp = bo_tanh
        ; BuiltinOp = bo_asin
        ; BuiltinOp = bo_acos
        ; BuiltinOp = bo_atan
        ; BuiltinOp = bo_card
        ; BuiltinOp = bo_set2array
        ; BuiltinOp = bo_range
        ; BuiltinOp = bo_diff
        ; BuiltinOp = bo_intersect
        ; BuiltinOp = bo_union
        ; BuiltinOp = bo_array_intersect
        ; BuiltinOp = bo_array_union
        ; BuiltinOp = bo_array1d
        ; BuiltinOp = bo_array2d
        ; BuiltinOp = bo_array3d
        ; BuiltinOp = bo_array4d
        ; BuiltinOp = bo_array5d
        ; BuiltinOp = bo_array6d
        ; BuiltinOp = bo_index_set
        ; BuiltinOp = bo_index_set_1of2
        ; BuiltinOp = bo_index_set_2of2
        ; BuiltinOp = bo_index_set_1of3
        ; BuiltinOp = bo_index_set_2of3
        ; BuiltinOp = bo_index_set_3of3
        ; BuiltinOp = bo_index_set_1of4
        ; BuiltinOp = bo_index_set_2of4
        ; BuiltinOp = bo_index_set_3of4
        ; BuiltinOp = bo_index_set_4of4
        ; BuiltinOp = bo_show
        ; BuiltinOp = bo_show_int
        ; BuiltinOp = bo_show_float
        ; BuiltinOp = bo_fix                % XXX
        ; BuiltinOp = bo_concat
        ; BuiltinOp = bo_join
        ),
        io.format(US, "STRING ARRAY OP: bad op %s\n", [s(PredName)], !IO),
        add_internal_error($pred, phase_conversion, SrcPos, "bad op", !Specs),
        StrArrayExpr = tmzn_string_array_expr_consts(SrcPos, [], [])
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred convert_general_expr_to_tmzn(io.output_stream::in, nest_pos::in,
    expr::in, tmzn_general_expr::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_general_expr_to_tmzn(US, NestPos, Expr, GenExpr, !Specs, !IO) :-
    ( if is_bool_expr(Expr) then
        convert_bool_expr_to_tmzn(US, NestPos, Expr, BoolExpr, !Specs, !IO),
        GenExpr = tmzn_gen_expr_bool(BoolExpr)
    else if is_bool_array_expr(Expr) then
        convert_bool_array_expr_to_tmzn(US, NestPos, Expr, BoolArrayExpr,
            !Specs, !IO),
        GenExpr = tmzn_gen_expr_bool_array(BoolArrayExpr)
    else if is_int_expr(Expr) then
        convert_int_expr_to_tmzn(US, NestPos, Expr, IntExpr, !Specs, !IO),
        GenExpr = tmzn_gen_expr_int(IntExpr)
    else if is_int_array_expr(Expr) then
        convert_int_array_expr_to_tmzn(US, NestPos, Expr, IntArrayExpr,
            !Specs, !IO),
        GenExpr = tmzn_gen_expr_int_array(IntArrayExpr)
    else if is_int_set_expr(Expr) then
        convert_int_set_expr_to_tmzn(US, NestPos, Expr, IntSetExpr,
            !Specs, !IO),
        GenExpr = tmzn_gen_expr_int_set(IntSetExpr)
    else if is_int_set_array_expr(Expr) then
        convert_int_set_array_expr_to_tmzn(US, NestPos, Expr, IntSetArrayExpr,
            !Specs, !IO),
        GenExpr = tmzn_gen_expr_int_set_array(IntSetArrayExpr)
    else if is_float_expr(Expr) then
        convert_float_expr_to_tmzn(US, NestPos, Expr, FloatExpr, !Specs, !IO),
        GenExpr = tmzn_gen_expr_float(FloatExpr)
    else if is_float_array_expr(Expr) then
        convert_float_array_expr_to_tmzn(US, NestPos, Expr, FloatArrayExpr,
            !Specs, !IO),
        GenExpr = tmzn_gen_expr_float_array(FloatArrayExpr)
    else if is_string_expr(Expr) then
        convert_string_expr_to_tmzn(US, NestPos, Expr, StrExpr, !Specs, !IO),
        GenExpr = tmzn_gen_expr_string(StrExpr)
    else if is_string_array_expr(Expr) then
        convert_string_array_expr_to_tmzn(US, NestPos, Expr, StrArrayExpr,
            !Specs, !IO),
        GenExpr = tmzn_gen_expr_string_array(StrArrayExpr)
    else
        Expr = expr(RawExpr, AnnExprs, ExprInfo),
        ExprInfo = expr_info(SrcLocn, TI),
        ( if
            TI = ti_array(ti_par_int, ti_par_bottom),
            RawExpr = lit_simple_array([])
        then
            FixedTI = ti_array(ti_par_int, ti_par_int),
            FixedExprInfo = expr_info(SrcLocn, FixedTI),
            FixedExpr = expr(RawExpr, AnnExprs, FixedExprInfo),
            convert_general_expr_to_tmzn(US, NestPos, FixedExpr, GenExpr,
                !Specs, !IO)
        else if
            TI = ti_par_set(ti_par_bottom),
            RawExpr = lit_set([])
        then
            FixedTI = ti_par_set(ti_par_int),
            FixedExprInfo = expr_info(SrcLocn, FixedTI),
            FixedExpr = expr(RawExpr, AnnExprs, FixedExprInfo),
            convert_general_expr_to_tmzn(US, NestPos, FixedExpr, GenExpr,
                !Specs, !IO)
        else
            io.write_string(US, "GENERAL: bad type ", !IO),
            io.write(US, Expr, !IO),
            io.nl(US, !IO),
            SrcPos = src_pos(NestPos, SrcLocn),
            add_internal_error($pred, phase_conversion, SrcPos,
                "bad type", !Specs),
            GenExpr = tmzn_gen_expr_bool(tmzn_bool_expr_const(SrcPos, no))
        )
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred is_bool_expr(expr::in) is semidet.
:- pred is_bool_array_expr(expr::in) is semidet.
:- pred is_int_expr(expr::in) is semidet.
:- pred is_int_set_expr(expr::in) is semidet.
:- pred is_int_array_expr(expr::in) is semidet.
:- pred is_int_set_array_expr(expr::in) is semidet.
:- pred is_float_expr(expr::in) is semidet.
:- pred is_float_array_expr(expr::in) is semidet.
:- pred is_string_expr(expr::in) is semidet.
:- pred is_string_array_expr(expr::in) is semidet.

is_bool_expr(Expr) :-
    Expr = expr(_RawExpr, _AnnExprs, ExprInfo),
    ExprInfo = expr_info(_SrcLocn, TI),
    ( TI = ti_par_bool ; TI = ti_var_bool ).

is_bool_array_expr(Expr) :-
    Expr = expr(_RawExpr, _AnnExprs, ExprInfo),
    ExprInfo = expr_info(_SrcLocn, TI),
    TI = ti_array(_IndexTI, EltTI),
    ( EltTI = ti_par_bool ; EltTI = ti_var_bool ).

is_int_expr(Expr) :-
    Expr = expr(_RawExpr, _AnnExprs, ExprInfo),
    ExprInfo = expr_info(_SrcLocn, TI),
    ( TI = ti_par_int ; TI = ti_var_int ).

is_int_set_expr(Expr) :-
    Expr = expr(_RawExpr, _AnnExprs, ExprInfo),
    ExprInfo = expr_info(_SrcLocn, TI),
    % XXX combinations
    (
        TI = ti_par_set(EltTI),
        ( EltTI = ti_par_int ; EltTI = ti_var_int )
    ;
        TI = ti_var_set(EltTI),
        ( EltTI = ti_par_int ; EltTI = ti_var_int )
    ).

is_int_array_expr(Expr) :-
    Expr = expr(_RawExpr, _AnnExprs, ExprInfo),
    ExprInfo = expr_info(_SrcLocn, TI),
    TI = ti_array(_IndexTI, EltTI),
    ( EltTI = ti_par_int ; EltTI = ti_var_int ).

is_int_set_array_expr(Expr) :-
    Expr = expr(_RawExpr, _AnnExprs, ExprInfo),
    ExprInfo = expr_info(_SrcLocn, TI),
    TI = ti_array(_IndexTI, ArrayEltTI),
    % XXX combinations
    (
        ArrayEltTI = ti_par_set(SetEltTI),
        ( SetEltTI = ti_par_int ; SetEltTI = ti_var_int )
    ;
        ArrayEltTI = ti_var_set(SetEltTI),
        ( SetEltTI = ti_par_int ; SetEltTI = ti_var_int )
    ).

is_float_expr(Expr) :-
    Expr = expr(_RawExpr, _AnnExprs, ExprInfo),
    ExprInfo = expr_info(_SrcLocn, TI),
    ( TI = ti_par_float ; TI = ti_var_float ).

is_float_array_expr(Expr) :-
    Expr = expr(_RawExpr, _AnnExprs, ExprInfo),
    ExprInfo = expr_info(_SrcLocn, TI),
    TI = ti_array(_IndexTI, EltTI),
    ( EltTI = ti_par_float ; EltTI = ti_var_float ).

is_string_expr(Expr) :-
    Expr = expr(_RawExpr, _AnnExprs, ExprInfo),
    ExprInfo = expr_info(_SrcLocn, TI),
    TI = ti_par_string.

is_string_array_expr(Expr) :-
    Expr = expr(_RawExpr, _AnnExprs, ExprInfo),
    ExprInfo = expr_info(_SrcLocn, TI),
    TI = ti_array(_IndexTI, EltTI),
    EltTI = ti_par_string.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred convert_generator_to_tmzn(io.output_stream::in, nest_pos::in,
    generator::in, tmzn_generator::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

convert_generator_to_tmzn(US, NestPos, Generator, GeneratorExpr,
        !Specs, !IO) :-
    Generator = generator(Ids, Expr),
    Names = list.map(id_name, Ids),
    ( if is_bool_expr(Expr) then
        convert_bool_expr_to_tmzn(US, NestPos, Expr, BoolExpr, !Specs, !IO),
        GenExpr = tmzn_gen_expr_bool(BoolExpr)
    else if is_bool_array_expr(Expr) then
        convert_bool_array_expr_to_tmzn(US, NestPos, Expr, BoolArrayExpr,
            !Specs, !IO),
        GenExpr = tmzn_gen_expr_bool_array(BoolArrayExpr)
    else if is_int_expr(Expr) then
        convert_int_expr_to_tmzn(US, NestPos, Expr, IntExpr, !Specs, !IO),
        GenExpr = tmzn_gen_expr_int(IntExpr)
    else if is_int_array_expr(Expr) then
        convert_int_array_expr_to_tmzn(US, NestPos, Expr, IntArrayExpr,
            !Specs, !IO),
        GenExpr = tmzn_gen_expr_int_array(IntArrayExpr)
    else if is_int_set_expr(Expr) then
        convert_int_set_expr_to_tmzn(US, NestPos, Expr, IntSetExpr,
            !Specs, !IO),
        GenExpr = tmzn_gen_expr_int_set(IntSetExpr)
    else if is_int_set_array_expr(Expr) then
        convert_int_set_array_expr_to_tmzn(US, NestPos, Expr, IntSetArrayExpr,
            !Specs, !IO),
        GenExpr = tmzn_gen_expr_int_set_array(IntSetArrayExpr)
    else if is_float_expr(Expr) then
        convert_float_expr_to_tmzn(US, NestPos, Expr, FloatExpr, !Specs, !IO),
        GenExpr = tmzn_gen_expr_float(FloatExpr)
    else if is_float_array_expr(Expr) then
        convert_float_array_expr_to_tmzn(US, NestPos, Expr, FloatArrayExpr,
            !Specs, !IO),
        GenExpr = tmzn_gen_expr_float_array(FloatArrayExpr)
    else if is_string_expr(Expr) then
        convert_string_expr_to_tmzn(US, NestPos, Expr, StrExpr, !Specs, !IO),
        GenExpr = tmzn_gen_expr_string(StrExpr)
    else
        io.write_string(US, "GENERATOR: bad type ", !IO),
        io.write(US, Expr, !IO),
        io.nl(US, !IO),
        Expr = expr(_, _, ExprInfo),
        ExprInfo = expr_info(SrcLocn, _TI),
        SrcPos = src_pos(NestPos, SrcLocn),
        add_internal_error($pred, phase_conversion, SrcPos,
            "bad type", !Specs),
        GenExpr = tmzn_gen_expr_bool(tmzn_bool_expr_const(SrcPos, no))
    ),
    GeneratorExpr = tmzn_generator(Names, GenExpr).

%-----------------------------------------------------------------------------%

:- type inner_step_loop_kind
    --->    islk_init_index_type
    ;       islk_simple_array
    ;       islk_lit_set
    ;       islk_compre_array
    ;       islk_index
    ;       islk_pred(string).  % predicate name

:- pred pos_map_foldl2(src_pos::in, inner_step_loop_kind::in, int::in,
    pred(nest_pos, T, U, list(error_spec), list(error_spec), io, io)
    ::in(pred(in, in, out, in, out, di, uo) is det),
    list(T)::in, list(U)::out,
    list(error_spec)::in, list(error_spec)::out, io::di, io::uo) is det.

pos_map_foldl2(_SrcPos, _ISLK, _ArgNum, _Pred, [], [], !Specs, !IO).
pos_map_foldl2(SrcPos, ISLK, ArgNum, Pred, [X | Xs], [Y | Ys],
        !Specs, !IO) :-
    (
        ISLK = islk_init_index_type,
        InnerStep = is_init_index_type(ArgNum)
    ;
        ISLK = islk_simple_array,
        InnerStep = is_simple_array(ArgNum)
    ;
        ISLK = islk_lit_set,
        InnerStep = is_lit_set(ArgNum)
    ;
        ISLK = islk_compre_array,
        InnerStep = is_compre_array(ArgNum)
    ;
        ISLK = islk_index,
        InnerStep = is_index(ArgNum)
    ;
        ISLK = islk_pred(PredName),
        InnerStep = is_arg(PredName, ArgNum)
    ),
    InnerNestPos = nest(SrcPos, InnerStep),
    Pred(InnerNestPos, X, Y, !Specs, !IO),
    pos_map_foldl2(SrcPos, ISLK, ArgNum + 1, Pred, Xs, Ys, !Specs, !IO).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
