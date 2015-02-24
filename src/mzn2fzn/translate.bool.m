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

:- module translate.bool.
:- interface.

:- import_module error_util.
:- import_module tmzn_ast.
:- import_module translate.info.

:- import_module bool.
:- import_module list.
:- import_module maybe.

:- type bool_context
    --->    ctxt_pos
    ;       ctxt_neg
    ;       ctxt_mix.

    % XXX Should we combine the ilhs and maybe(asserted_truth) args into one?
    % We cannot assert TMznBoolExpr to have a truth value unless ILHS
    % is ilhs_true.
    % XXX No, that is wrong

:- pred translate_bool_expr_to_tfzn_constraints(ilhs::in, bool_context::in,
    maybe(asserted_truth)::in, tmzn_bool_expr::in, maybe_known_truth::out,
    tfzn_constraint_set::out, tr_info::in, tr_info::out) is det.

:- pred is_bool_const_expr(tr_info::in, tmzn_bool_expr::in, maybe(bool)::out,
    list(error_spec)::in, list(error_spec)::out) is det.

%-----------------------------------------------------------------------------%

:- implementation.

:- import_module bounds.
:- import_module error_util.
:- import_module mzn_ops.
:- import_module output_common.
:- import_module output_tfzn.
:- import_module output_tmzn.
:- import_module tfzn_ast.
:- import_module translate.float.
:- import_module translate.int.
:- import_module translate.string.
:- import_module translate.vars.
:- import_module types.
:- import_module zinc_common.

:- import_module assoc_list.
:- import_module bool.
:- import_module float.
:- import_module int.
:- import_module io.
:- import_module map.
:- import_module maybe.
:- import_module pair.
:- import_module require.
:- import_module set.
:- import_module set_tree234.
:- import_module unit.

%-----------------------------------------------------------------------------%

translate_bool_expr_to_tfzn_constraints(ILHS, BoolContext, MaybeAssertedTruth,
        TMznBoolExpr, MaybeKnownTruth, Constraints, !Info) :-
    optimize_special_patterns_bool(ILHS, BoolContext, MaybeAssertedTruth,
        TMznBoolExpr, OptResult, !Info),
    (
        OptResult = opt_all_done(MaybeKnownTruth, Constraints)
    ;
        OptResult = opt_flattening_required(MaybeUpdatedTMznBoolExpr),
        translate_bool_expr_to_tfzn_constraints_std(ILHS, BoolContext,
            MaybeAssertedTruth, MaybeUpdatedTMznBoolExpr, MaybeKnownTruth,
            Constraints, !Info)
    ).

%-----------------------------------------------------------------------------%

:- pred optimize_special_patterns_bool(ilhs::in, bool_context::in,
    maybe(asserted_truth)::in, tmzn_bool_expr::in, optimize_result_bool::out,
    tr_info::in, tr_info::out) is det.

optimize_special_patterns_bool(ILHS, _BoolContext, _MaybeAssertedTruth,
        TMznBoolExpr, Result, !Info) :-
    % XXX We should also look for these additional optimizable patterns:
    %
    % b1 and b2 and b3 and ... and bn: array_bool_and
    % b1 or b2 or b3 or ... or bn: array_bool_or
    % allow some bi to be constants
    %
    % c1*x1 + c2*xs + ... + xn*xn compare_op c: int_lin_le, int_lin_lt
    % c compare_op c1*x1 + c2*xs + ... + xn*xn: int_lin_le, int_lin_lt
    %
    is_bool_const_expr(!.Info, TMznBoolExpr, MaybeBoolConst, [], Specs),
    add_errors(Specs, !Info),
    (
        MaybeBoolConst = yes(Bool),
        constraint_reduced_to_bool(ILHS, Bool, MaybeKnownTruth, Constraints,
            !Info),
        Result = opt_all_done(MaybeKnownTruth, Constraints)
    ;
        MaybeBoolConst = no,
        Result = opt_flattening_required(TMznBoolExpr)
    ).

%-----------------------------------------------------------------------------%

is_bool_const_expr(Info, TMznBoolExpr, MaybeBoolConst, !Specs) :-
    (
        TMznBoolExpr = tmzn_bool_expr_const(_SrcPos, BoolConst),
        MaybeBoolConst = yes(BoolConst)
    ;
        TMznBoolExpr = tmzn_bool_expr_var(_SrcPos, TMznBoolVar),
        tr_info_get_var_info_maps(Info, VarInfoMaps),
        vim_get_bool_map(VarInfoMaps, BoolMap),
        ( if
            TMznBoolVar = tmzn_bool_var_named(BoolVarName),
            TFznBoolVar = tfzn_bool_var_named(BoolVarName),
            map.search(BoolMap, TFznBoolVar, BoolVarInfo)
        then
            MaybeBoolConst = BoolVarInfo ^ vib_is_known
        else
            MaybeBoolConst = no
        )
    ;
        TMznBoolExpr = tmzn_bool_expr_b2b(_SrcPos, B2BOp, TMznBoolA),
        is_bool_const_expr(Info, TMznBoolA, MaybeBoolConstA, !Specs),
        ( if
            MaybeBoolConstA = yes(BoolConstA)
        then
            translate_par_bool_to_bool(B2BOp, BoolConstA, BoolConst),
            MaybeBoolConst = yes(BoolConst)
        else
            MaybeBoolConst = no
        )
    ;
        TMznBoolExpr = tmzn_bool_expr_bb2b(_SrcPos, BB2BOp,
            TMznBoolA, TMznBoolB),
        is_bool_const_expr(Info, TMznBoolA, MaybeBoolConstA, !Specs),
        is_bool_const_expr(Info, TMznBoolB, MaybeBoolConstB, !Specs),
        ( if
            MaybeBoolConstA = yes(BoolConstA),
            MaybeBoolConstB = yes(BoolConstB)
        then
            translate_par_bool_par_bool_to_bool(BB2BOp, BoolConstA, BoolConstB,
                BoolConst),
            MaybeBoolConst = yes(BoolConst)
        else
            MaybeBoolConst = no
        )
    ;
        TMznBoolExpr = tmzn_bool_expr_ii2b(_SrcPos, II2BOp,
            TMznIntA, TMznIntB),
        is_int_const_expr(Info, TMznIntA, MaybeIntConstA, !Specs),
        is_int_const_expr(Info, TMznIntB, MaybeIntConstB, !Specs),
        ( if
            MaybeIntConstA = yes(IntConstA),
            MaybeIntConstB = yes(IntConstB)
        then
            translate_par_int_par_int_to_bool(II2BOp, IntConstA, IntConstB,
                BoolConst),
            MaybeBoolConst = yes(BoolConst)
        else
            MaybeBoolConst = no
        )
    ;
        TMznBoolExpr = tmzn_bool_expr_ff2b(_SrcPos, FF2BOp,
            TMznFloatA, TMznFloatB),
        is_float_const_expr(Info, TMznFloatA, MaybeFloatConstA, !Specs),
        is_float_const_expr(Info, TMznFloatB, MaybeFloatConstB, !Specs),
        ( if
            MaybeFloatConstA = yes(FloatConstA),
            MaybeFloatConstB = yes(FloatConstB)
        then
            translate_par_float_par_float_to_bool(FF2BOp,
                FloatConstA, FloatConstB, BoolConst),
            MaybeBoolConst = yes(BoolConst)
        else
            MaybeBoolConst = no
        )
    ;
        TMznBoolExpr = tmzn_bool_expr_ss2b(_SrcPos, SS2BOp,
            TMznStrA, TMznStrB),
        is_string_const_expr(Info, TMznStrA, MaybeStrConstA, !Specs),
        is_string_const_expr(Info, TMznStrB, MaybeStrConstB, !Specs),
        ( if
            MaybeStrConstA = yes(StrConstA),
            MaybeStrConstB = yes(StrConstB)
        then
            translate_par_string_par_string_to_bool(SS2BOp,
                StrConstA, StrConstB, BoolConst),
            MaybeBoolConst = yes(BoolConst)
        else
            MaybeBoolConst = no
        )
    ;
        TMznBoolExpr = tmzn_bool_expr_ite(_SrcPos, TMznCondExpr,
            TMznThenExpr, TMznElseExpr),
        is_bool_const_expr(Info, TMznCondExpr, MaybeCondConst, !Specs),
        ( if
            MaybeCondConst = yes(CondConst)
        then
            (
                CondConst = yes,
                is_bool_const_expr(Info, TMznThenExpr, MaybeThenConst, !Specs),
                MaybeBoolConst = MaybeThenConst
            ;
                CondConst = no,
                is_bool_const_expr(Info, TMznElseExpr, MaybeElseConst, !Specs),
                MaybeBoolConst = MaybeElseConst
            )
        else
            MaybeBoolConst = no
        )
    ;
        ( TMznBoolExpr = tmzn_bool_expr_ba2b(_SrcPos, _Op, _A)
        ; TMznBoolExpr = tmzn_bool_expr_iis2b(_SrcPos, _Op, _A, _B)
        ; TMznBoolExpr = tmzn_bool_expr_isis2b(_SrcPos, _Op, _A, _B)
        ; TMznBoolExpr = tmzn_bool_expr_ffs2b(_SrcPos, _Op, _A, _B)
        ; TMznBoolExpr = tmzn_bool_expr_fsfs2b(_SrcPos, _Op, _A, _B)
        ; TMznBoolExpr = tmzn_bool_expr_is_fixed(_SrcPos, _A)
        ; TMznBoolExpr = tmzn_bool_expr_general(_SrcPos, _Pred, _Args)
        ),
        % XXX In theory, we *could* try to figure out whether some of these
        % are constants.
        MaybeBoolConst = no
    ).

:- pred translate_par_bool_to_bool(bool_to_bool_op::in, bool::in, bool::out)
    is det.

translate_par_bool_to_bool(B2BOp, BoolA, BoolZ) :-
    ( B2BOp = b2b_not,      bool.not(BoolA, BoolZ)
    ; B2BOp = b2b_lb,       BoolZ = BoolA
    ; B2BOp = b2b_ub,       BoolZ = BoolA
    ; B2BOp = b2b_fix,      BoolZ = BoolA
    ).

:- pred translate_par_bool_par_bool_to_bool(bool_bool_to_bool_op::in,
    bool::in, bool::in, bool::out) is det.

translate_par_bool_par_bool_to_bool(BB2BOp, BoolA, BoolB, BoolZ) :-
    ( BB2BOp = bb2b_and,    BoolZ = bool.and(BoolA, BoolB)
    ; BB2BOp = bb2b_or,     BoolZ = bool.or(BoolA, BoolB)
    ; BB2BOp = bb2b_xor,    BoolZ = bool.xor(BoolA, BoolB)
    ; BB2BOp = bb2b_imp2l,  BoolZ = bool.or(bool.not(BoolA), BoolB)
    ; BB2BOp = bb2b_imp2r,  BoolZ = bool.or(bool.not(BoolB), BoolA)
    ; BB2BOp = bb2b_biimp,  BoolZ = bool.not(bool.xor(BoolA, BoolB))
    ; BB2BOp = bb2b_min,    BoolZ = bool.and(BoolA, BoolB)
    ; BB2BOp = bb2b_max,    BoolZ = bool.or(BoolA, BoolB)
    ; BB2BOp = bb2b_eq,     BoolZ = ( if BoolA = BoolB then yes else no )
    ; BB2BOp = bb2b_ee,     BoolZ = ( if BoolA = BoolB then yes else no )
    ; BB2BOp = bb2b_ne,     BoolZ = ( if BoolA \= BoolB then yes else no )
    ; BB2BOp = bb2b_lt,
        BoolZ = ( if BoolA = no, BoolB = yes then yes else no )
    ; BB2BOp = bb2b_le,
        BoolZ = ( if ( BoolA = no ; BoolB = yes ) then yes else no )
    ; BB2BOp = bb2b_gt,
        BoolZ = ( if BoolA = yes, BoolB = no then yes else no )
    ; BB2BOp = bb2b_ge,
        BoolZ = ( if ( BoolA = yes ; BoolB = no ) then yes else no )
    ).

:- pred translate_par_int_par_int_to_bool(int_int_to_bool_op::in,
    int::in, int::in, bool::out) is det.

translate_par_int_par_int_to_bool(II2BOp, IntA, IntB, BoolZ) :-
    ( II2BOp = ii2b_ee, BoolZ = ( if IntA =  IntB then yes else no )
    ; II2BOp = ii2b_eq, BoolZ = ( if IntA =  IntB then yes else no )
    ; II2BOp = ii2b_ne, BoolZ = ( if IntA \= IntB then yes else no )
    ; II2BOp = ii2b_le, BoolZ = ( if IntA =< IntB then yes else no )
    ; II2BOp = ii2b_lt, BoolZ = ( if IntA <  IntB then yes else no )
    ; II2BOp = ii2b_ge, BoolZ = ( if IntA >= IntB then yes else no )
    ; II2BOp = ii2b_gt, BoolZ = ( if IntA >  IntB then yes else no )
    ).

:- pred translate_par_float_par_float_to_bool(float_float_to_bool_op::in,
    float::in, float::in, bool::out) is det.

translate_par_float_par_float_to_bool(FF2BOp, FloatA, FloatB, BoolZ) :-
    ( FF2BOp = ff2b_ee, BoolZ = ( if FloatA =  FloatB then yes else no )
    ; FF2BOp = ff2b_eq, BoolZ = ( if FloatA =  FloatB then yes else no )
    ; FF2BOp = ff2b_ne, BoolZ = ( if FloatA \= FloatB then yes else no )
    ; FF2BOp = ff2b_le, BoolZ = ( if FloatA =< FloatB then yes else no )
    ; FF2BOp = ff2b_lt, BoolZ = ( if FloatA <  FloatB then yes else no )
    ; FF2BOp = ff2b_ge, BoolZ = ( if FloatA >= FloatB then yes else no )
    ; FF2BOp = ff2b_gt, BoolZ = ( if FloatA >  FloatB then yes else no )
    ).

:- pred translate_par_string_par_string_to_bool(string_string_to_bool_op::in,
    string::in, string::in, bool::out) is det.

translate_par_string_par_string_to_bool(SS2BOp, StrA, StrB, BoolZ) :-
    compare(Result, StrA, StrB),
    ( SS2BOp = ss2b_eq, BoolZ = ( if Result = (=)  then yes else no )
    ; SS2BOp = ss2b_ee, BoolZ = ( if Result = (=)  then yes else no )
    ; SS2BOp = ss2b_ne, BoolZ = ( if Result \= (=) then yes else no )
    ; SS2BOp = ss2b_lt, BoolZ = ( if Result = (<)  then yes else no )
    ; SS2BOp = ss2b_le, BoolZ = ( if Result \= (>) then yes else no )
    ; SS2BOp = ss2b_gt, BoolZ = ( if Result = (>)  then yes else no )
    ; SS2BOp = ss2b_ge, BoolZ = ( if Result \= (<) then yes else no )
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred translate_bool_expr_to_tfzn_constraints_std(ilhs::in, bool_context::in,
    maybe(asserted_truth)::in, tmzn_bool_expr::in, maybe_known_truth::out,
    tfzn_constraint_set::out, tr_info::in, tr_info::out) is det.

translate_bool_expr_to_tfzn_constraints_std(ILHS, BoolContext,
        MaybeAssertedTruth, TMznBoolExpr, MaybeKnownTruth, Constraints,
        !Info) :-
    (
        TMznBoolExpr = tmzn_bool_expr_const(_, Bool),
        % XXX This should have been caught and handled by the optimizer.
        constraint_reduced_to_bool(ILHS, Bool, MaybeKnownTruth, Constraints,
            !Info)
    ;
        TMznBoolExpr = tmzn_bool_expr_var(SrcPos, TMznBoolVar),
        maybe_asserted_to_maybe_value(MaybeAssertedTruth, MaybeValue),
        (
            TMznBoolVar = tmzn_bool_var_named(BoolVarName),
            TFznBoolVar = tfzn_bool_var_named(BoolVarName),
            maybe_update_bool_var_known(TFznBoolVar, MaybeValue,
                MaybeKnownTruth, !Info),
            (
                MaybeKnownTruth = unknown_truth,
                constraint_reduced_to_var(ILHS, TFznBoolVar, Constraints)
            ;
                MaybeKnownTruth = known_truth(KnownTruth),
                (
                    ILHS = ilhs_true,
                    Constraints = no_tfzn_constraints
                ;
                    ILHS = ilhs_var(ILHSVar),
                    (
                        KnownTruth = known_false,
                        % `ILHSVar -> false' can hold only if ILHSVar = false.
                        constrain_var_to_bool(ilhs_true, ILHSVar, no,
                            Constraints)
                    ;
                        KnownTruth = known_true,
                        % `ILHSVar -> true' holds for all values of ILHSVar.
                        Constraints = no_tfzn_constraints
                    )
                ;
                    ILHS = ilhs_reif(ILHSVar),
                    ILHSTFznTerm = tfzn_bool_term_var(ILHSVar),
                    TFznTerm = tfzn_bool_term_var(TFznBoolVar),
                    Constraint = tfzn_constr_bool_compare(bool_eq,
                        TFznTerm, ILHSTFznTerm, not_reified),
                    % XXX Anns
                    ConstraintItem =
                        tfzn_item_constraint(Constraint, set.init),
                    Constraints = one_tfzn_constraint(ConstraintItem)
                )
            )
        ;
            TMznBoolVar = tmzn_bool_var_anon,
            % XXX Inst: should we take it from an extended TMznBoolExpr?
            TmpVarInfo = var_info_bool(var_is_var, var_is_not_output,
                MaybeValue, no),
            add_tmp_var_bool(TmpVarInfo, TFznBoolVar, !Info),
            constraint_reduced_to_var(ILHS, TFznBoolVar, Constraints),
            MaybeKnownTruth = unknown_truth
        ;
            TMznBoolVar = tmzn_bool_var_array_slot(_, _),
            add_nyi_error_info($pred, phase_constraint, SrcPos, "array_slot",
                !Info),
            TFznBoolVar = tfzn_bool_var_named("dummy"),
            constraint_reduced_to_var(ILHS, TFznBoolVar, Constraints),
            MaybeKnownTruth = unknown_truth
        )
    ;
        TMznBoolExpr = tmzn_bool_expr_b2b(SrcPos, B2BOp, TMznBoolA),
        translate_bool_to_bool(ILHS, BoolContext, MaybeAssertedTruth,
            SrcPos, B2BOp, TMznBoolA, MaybeKnownTruth, Constraints, !Info)
    ;
        TMznBoolExpr = tmzn_bool_expr_bb2b(SrcPos, BB2BOp,
            TMznBoolA, TMznBoolB),
        translate_bool_bool_to_bool(ILHS, BoolContext, MaybeAssertedTruth,
            SrcPos, BB2BOp, TMznBoolA, TMznBoolB, MaybeKnownTruth,
            Constraints, !Info)
    ;
        TMznBoolExpr = tmzn_bool_expr_ba2b(SrcPos, _Op, _A),
        add_nyi_error_info($pred, phase_constraint, SrcPos, "ba2b", !Info),
        MaybeKnownTruth = unknown_truth,
        Constraints = no_tfzn_constraints
    ;
        TMznBoolExpr = tmzn_bool_expr_ii2b(SrcPos, II2BOp, TMznIntA, TMznIntB),
        translate_int_int_to_bool(ILHS, BoolContext, SrcPos,
            II2BOp, TMznIntA, TMznIntB, MaybeKnownTruth, Constraints, !Info)
    ;
        TMznBoolExpr = tmzn_bool_expr_iis2b(SrcPos, _Op, _A, _B),
        add_nyi_error_info($pred, phase_constraint, SrcPos, "iis2b", !Info),
        MaybeKnownTruth = unknown_truth,
        Constraints = no_tfzn_constraints
    ;
        TMznBoolExpr = tmzn_bool_expr_isis2b(SrcPos, _Op, _A, _B),
        add_nyi_error_info($pred, phase_constraint, SrcPos, "isis2b", !Info),
        MaybeKnownTruth = unknown_truth,
        Constraints = no_tfzn_constraints
    ;
        TMznBoolExpr = tmzn_bool_expr_ff2b(SrcPos, _Op, _A, _B),
        add_nyi_error_info($pred, phase_constraint, SrcPos, "ff2b", !Info),
        MaybeKnownTruth = unknown_truth,
        Constraints = no_tfzn_constraints
    ;
        TMznBoolExpr = tmzn_bool_expr_ffs2b(SrcPos, _Op, _A, _B),
        add_nyi_error_info($pred, phase_constraint, SrcPos, "ffs2b", !Info),
        MaybeKnownTruth = unknown_truth,
        Constraints = no_tfzn_constraints
    ;
        TMznBoolExpr = tmzn_bool_expr_fsfs2b(SrcPos, _Op, _A, _B),
        add_nyi_error_info($pred, phase_constraint, SrcPos, "fsfs2b", !Info),
        MaybeKnownTruth = unknown_truth,
        Constraints = no_tfzn_constraints
    ;
        TMznBoolExpr = tmzn_bool_expr_ss2b(SrcPos, _Op, _A, _B),
        add_nyi_error_info($pred, phase_constraint, SrcPos, "ss2b", !Info),
        MaybeKnownTruth = unknown_truth,
        Constraints = no_tfzn_constraints
    ;
        TMznBoolExpr = tmzn_bool_expr_is_fixed(SrcPos, _A),
        add_nyi_error_info($pred, phase_constraint, SrcPos, "is_fixed", !Info),
        MaybeKnownTruth = unknown_truth,
        Constraints = no_tfzn_constraints
    ;
        TMznBoolExpr = tmzn_bool_expr_ite(SrcPos, _C, _T, _E),
        add_nyi_error_info($pred, phase_constraint, SrcPos, "ite", !Info),
        MaybeKnownTruth = unknown_truth,
        Constraints = no_tfzn_constraints
    ;
        TMznBoolExpr = tmzn_bool_expr_general(SrcPos, _P, _A),
        add_nyi_error_info($pred, phase_constraint, SrcPos, "general", !Info),
        MaybeKnownTruth = unknown_truth,
        Constraints = no_tfzn_constraints
    ),
    trace [compiletime(flag("bool_expr")), io(!IO)] (
        io.write_string("\ntranslate_bool_expr_to_tfzn_constraints_std(", !IO),
        io.write_string(dump_ilhs(ILHS), !IO),
        io.write_string(", ", !IO),
        io.write_string(dump_tmzn_bool_expr(no_parens, TMznBoolExpr), !IO),
        io.write_string("):\n", !IO),
        OutputTFznOpts = output_opts(yes, 2),
        list.foldl(
            output_tfzn_constraint_item(OutputTFznOpts, io.stdout_stream),
            tfzn_constraint_set_to_list(Constraints), !IO)
    ).

:- pred maybe_asserted_to_maybe_value(maybe(asserted_truth)::in,
    maybe(bool)::out) is det.

maybe_asserted_to_maybe_value(MaybeAssertedTruth, MaybeValue) :-
    (
        MaybeAssertedTruth = no,
        MaybeValue = no
    ;
        MaybeAssertedTruth = yes(AssertedTruth),
        (
            AssertedTruth = asserted_false,
            Value = no
        ;
            AssertedTruth = asserted_true,
            Value = yes
        ),
        MaybeValue = yes(Value)
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred translate_bool_to_bool(ilhs::in, bool_context::in,
    maybe(asserted_truth)::in, src_pos::in,
    bool_to_bool_op::in, tmzn_bool_expr::in,
    maybe_known_truth::out, tfzn_constraint_set::out,
    tr_info::in, tr_info::out) is det.

translate_bool_to_bool(ILHS, BoolContext, MaybeAssertedTruth, SrcPos,
        B2BOp, TMznBoolA, MaybeKnownTruth, Constraints, !Info) :-
    (
        B2BOp = b2b_not,
        asserted_truth_not(MaybeAssertedTruth, MaybeAssertedTruthA),
        (
            (
                ILHS = ilhs_true,
                ILHSBoolTerm = tfzn_bool_term_const(yes)
            ;
                ILHS = ilhs_var(ILHSVar),
                ILHSBoolTerm = tfzn_bool_term_var(ILHSVar)
            ),
            can_be_safely_negated(!.Info, TMznBoolA, MaybeTMznBoolNegA),
            (
                MaybeTMznBoolNegA = yes(TMznBoolNegA),
                % XXX Is it correct to pass BoolContext unchanged?
                translate_bool_expr_to_tfzn_constraints(ILHS, BoolContext,
                    MaybeAssertedTruthA, TMznBoolNegA, MaybeKnownTruth,
                    Constraints, !Info)
            ;
                MaybeTMznBoolNegA = no,
                NewILHSVarInfo = var_info_bool(var_is_var, var_is_not_output,
                    no, no),
                add_tmp_var_bool(NewILHSVarInfo, NewILHSVar, !Info),
                translate_negation_using_reification(NewILHSVar, BoolContext,
                    MaybeAssertedTruthA, TMznBoolA, MaybeKnownTruth,
                    ConstraintsA, !Info),

                % This constraint implements "ILHSBoolTerm -> NewILHSVar".
                Constraint = tfzn_constr_bool_compare(bool_le,
                    ILHSBoolTerm, tfzn_bool_term_var(NewILHSVar),
                    not_reified),
                % XXX Anns
                set.init(Anns),
                ConstraintItem = tfzn_item_constraint(Constraint, Anns),
                Constraints =
                    one_tfzn_constraint(ConstraintItem) ++ ConstraintsA
            )
        ;
            ILHS = ilhs_reif(ILHSVar),
            % XXX Should we try can_be_safely_negated here?
            % It COULD be an improvement over the standard algorithm followed
            % by flatc.
            translate_negation_using_reification(ILHSVar, BoolContext,
                MaybeAssertedTruthA, TMznBoolA, MaybeKnownTruth,
                Constraints, !Info)
        )
    ;
        B2BOp = b2b_lb,
        % XXX Such constraints do not make sense.
        MaybeKnownTruth = known_truth(known_false),
        Constraints = no_tfzn_constraints
    ;
        B2BOp = b2b_ub,
        % XXX Such constraints do not make sense.
        MaybeKnownTruth = known_truth(known_true),
        Constraints = no_tfzn_constraints
    ;
        B2BOp = b2b_fix,
        add_nyi_error_info($pred, phase_constraint, SrcPos, "fix", !Info),
        MaybeKnownTruth = unknown_truth,
        Constraints = no_tfzn_constraints
    ),
    trace [compiletime(flag("bool_expr")), io(!IO)] (
        io.write_string("\ntranslate_bool_to_bool(", !IO),
        io.write_string(dump_ilhs(ILHS), !IO),
        io.write_string(", ", !IO),
        io.write(B2BOp, !IO),
        io.write_string(", ", !IO),
        io.write_string(dump_tmzn_bool_expr(no_parens, TMznBoolA), !IO),
        io.write_string("):\n", !IO),
        OutputTFznOpts = output_opts(yes, 2),
        list.foldl(
            output_tfzn_constraint_item(OutputTFznOpts, io.stdout_stream),
            tfzn_constraint_set_to_list(Constraints), !IO)
    ).

:- pred can_be_safely_negated(tr_info::in, tmzn_bool_expr::in,
    maybe(tmzn_bool_expr)::out) is det.

can_be_safely_negated(_Info, Expr, MaybeNegatedExpr) :-
    (
        Expr = tmzn_bool_expr_const(SrcPos, Bool),
        NegatedExpr = tmzn_bool_expr_const(SrcPos, bool.not(Bool)),
        MaybeNegatedExpr = yes(NegatedExpr)
    ;
        Expr = tmzn_bool_expr_var(_SrcPos, _TMznBoolVar),
        MaybeNegatedExpr = no
    ;
        Expr = tmzn_bool_expr_b2b(_SrcPos, B2BOp, ArgA),
        (
            B2BOp = b2b_not,
            NegatedExpr = ArgA,
            MaybeNegatedExpr = yes(NegatedExpr)
        ;
            ( B2BOp = b2b_lb        % XXX Can we do better?
            ; B2BOp = b2b_ub        % XXX Can we do better?
            ; B2BOp = b2b_fix
            ),
            MaybeNegatedExpr = no
        )
    ;
        Expr = tmzn_bool_expr_bb2b(SrcPos, BB2BOp, ArgA, ArgB),
        (
            ( BB2BOp = bb2b_and
            ; BB2BOp = bb2b_min
            ),
            % XXX SrcPos
            NotArgA = tmzn_bool_expr_b2b(SrcPos, b2b_not, ArgA),
            NotArgB = tmzn_bool_expr_b2b(SrcPos, b2b_not, ArgB),
            NegatedExpr = tmzn_bool_expr_bb2b(SrcPos, bb2b_or,
                NotArgA, NotArgB),
            MaybeNegatedExpr = yes(NegatedExpr)
        ;
            ( BB2BOp = bb2b_or
            ; BB2BOp = bb2b_max
            ),
            % XXX SrcPos
            NotArgA = tmzn_bool_expr_b2b(SrcPos, b2b_not, ArgA),
            NotArgB = tmzn_bool_expr_b2b(SrcPos, b2b_not, ArgB),
            NegatedExpr = tmzn_bool_expr_bb2b(SrcPos, bb2b_and,
                NotArgA, NotArgB),
            MaybeNegatedExpr = yes(NegatedExpr)
        ;
            BB2BOp = bb2b_xor,
            NegatedExpr = tmzn_bool_expr_bb2b(SrcPos, bb2b_eq, ArgA, ArgB),
            MaybeNegatedExpr = yes(NegatedExpr)
        ;
            ( BB2BOp = bb2b_imp2r
            ; BB2BOp = bb2b_le
            ),
            % XXX SrcPos
            NotArgB = tmzn_bool_expr_b2b(SrcPos, b2b_not, ArgB),
            NegatedExpr = tmzn_bool_expr_bb2b(SrcPos, bb2b_and, ArgA, NotArgB),
            MaybeNegatedExpr = yes(NegatedExpr)
        ;
            ( BB2BOp = bb2b_imp2l
            ; BB2BOp = bb2b_ge
            ),
            % XXX SrcPos
            NotArgA = tmzn_bool_expr_b2b(SrcPos, b2b_not, ArgA),
            NegatedExpr = tmzn_bool_expr_bb2b(SrcPos, bb2b_and, NotArgA, ArgB),
            MaybeNegatedExpr = yes(NegatedExpr)
        ;
            BB2BOp = bb2b_gt,
            % XXX SrcPos
            NegatedExpr = tmzn_bool_expr_bb2b(SrcPos, bb2b_le, ArgA, ArgB),
            MaybeNegatedExpr = yes(NegatedExpr)
        ;
            BB2BOp = bb2b_lt,
            % XXX SrcPos
            NegatedExpr = tmzn_bool_expr_bb2b(SrcPos, bb2b_ge, ArgA, ArgB),
            MaybeNegatedExpr = yes(NegatedExpr)
        ;
            ( BB2BOp = bb2b_eq
            ; BB2BOp = bb2b_ee
            ; BB2BOp = bb2b_biimp
            ),
            % XXX SrcPos
            NegatedExpr = tmzn_bool_expr_bb2b(SrcPos, bb2b_ne, ArgA, ArgB),
            MaybeNegatedExpr = yes(NegatedExpr)
        ;
            BB2BOp = bb2b_ne,
            % XXX SrcPos
            NegatedExpr = tmzn_bool_expr_bb2b(SrcPos, bb2b_eq, ArgA, ArgB),
            MaybeNegatedExpr = yes(NegatedExpr)
        )
    ;
        Expr = tmzn_bool_expr_ii2b(SrcPos, II2BOp, ArgA, ArgB),
        (
            ( II2BOp = ii2b_eq
            ; II2BOp = ii2b_ee
            ),
            NegatedExpr = tmzn_bool_expr_ii2b(SrcPos, ii2b_ne, ArgA, ArgB)
        ;
            II2BOp = ii2b_ne,
            NegatedExpr = tmzn_bool_expr_ii2b(SrcPos, ii2b_eq, ArgA, ArgB)
        ;
            II2BOp = ii2b_lt,
            NegatedExpr = tmzn_bool_expr_ii2b(SrcPos, ii2b_ge, ArgA, ArgB)
        ;
            II2BOp = ii2b_le,
            NegatedExpr = tmzn_bool_expr_ii2b(SrcPos, ii2b_gt, ArgA, ArgB)
        ;
            II2BOp = ii2b_gt,
            NegatedExpr = tmzn_bool_expr_ii2b(SrcPos, ii2b_le, ArgA, ArgB)
        ;
            II2BOp = ii2b_ge,
            NegatedExpr = tmzn_bool_expr_ii2b(SrcPos, ii2b_lt, ArgA, ArgB)
        ),
        MaybeNegatedExpr = yes(NegatedExpr)
    ;
        Expr = tmzn_bool_expr_ff2b(SrcPos, FF2BOp, ArgA, ArgB),
        (
            ( FF2BOp = ff2b_eq
            ; FF2BOp = ff2b_ee
            ),
            NegatedExpr = tmzn_bool_expr_ff2b(SrcPos, ff2b_ne, ArgA, ArgB)
        ;
            FF2BOp = ff2b_ne,
            NegatedExpr = tmzn_bool_expr_ff2b(SrcPos, ff2b_eq, ArgA, ArgB)
        ;
            FF2BOp = ff2b_lt,
            NegatedExpr = tmzn_bool_expr_ff2b(SrcPos, ff2b_ge, ArgA, ArgB)
        ;
            FF2BOp = ff2b_le,
            NegatedExpr = tmzn_bool_expr_ff2b(SrcPos, ff2b_gt, ArgA, ArgB)
        ;
            FF2BOp = ff2b_gt,
            NegatedExpr = tmzn_bool_expr_ff2b(SrcPos, ff2b_le, ArgA, ArgB)
        ;
            FF2BOp = ff2b_ge,
            NegatedExpr = tmzn_bool_expr_ff2b(SrcPos, ff2b_lt, ArgA, ArgB)
        ),
        MaybeNegatedExpr = yes(NegatedExpr)
    ;
        Expr = tmzn_bool_expr_ss2b(SrcPos, SS2BOp, ArgA, ArgB),
        (
            ( SS2BOp = ss2b_eq
            ; SS2BOp = ss2b_ee
            ),
            NegatedExpr = tmzn_bool_expr_ss2b(SrcPos, ss2b_ne, ArgA, ArgB)
        ;
            SS2BOp = ss2b_ne,
            NegatedExpr = tmzn_bool_expr_ss2b(SrcPos, ss2b_eq, ArgA, ArgB)
        ;
            SS2BOp = ss2b_lt,
            NegatedExpr = tmzn_bool_expr_ss2b(SrcPos, ss2b_ge, ArgA, ArgB)
        ;
            SS2BOp = ss2b_le,
            NegatedExpr = tmzn_bool_expr_ss2b(SrcPos, ss2b_gt, ArgA, ArgB)
        ;
            SS2BOp = ss2b_gt,
            NegatedExpr = tmzn_bool_expr_ss2b(SrcPos, ss2b_le, ArgA, ArgB)
        ;
            SS2BOp = ss2b_ge,
            NegatedExpr = tmzn_bool_expr_ss2b(SrcPos, ss2b_lt, ArgA, ArgB)
        ),
        MaybeNegatedExpr = yes(NegatedExpr)
    ;
        Expr = tmzn_bool_expr_ite(SrcPos, Cond, Then, Else),
        NotThen = tmzn_bool_expr_b2b(SrcPos, b2b_not, Then),
        NotElse = tmzn_bool_expr_b2b(SrcPos, b2b_not, Else),
        NegatedExpr = tmzn_bool_expr_ite(SrcPos, Cond, NotThen, NotElse),
        MaybeNegatedExpr = yes(NegatedExpr)
    ;
        ( Expr = tmzn_bool_expr_ba2b(_SrcPos, _Op, _A)
        ; Expr = tmzn_bool_expr_iis2b(_SrcPos, _Op, _A, _B)
        ; Expr = tmzn_bool_expr_isis2b(_SrcPos, _Op, _A, _B)
        ; Expr = tmzn_bool_expr_ffs2b(_SrcPos, _Op, _A, _B)
        ; Expr = tmzn_bool_expr_fsfs2b(_SrcPos, _Op, _A, _B)
        ; Expr = tmzn_bool_expr_is_fixed(_SrcPos, _A)
        ; Expr = tmzn_bool_expr_general(_SrcPos, _P, _A)
        ),
        MaybeNegatedExpr = no
    ).

:- pred translate_negation_using_reification(tfzn_bool_var::in,
    bool_context::in, maybe(asserted_truth)::in, tmzn_bool_expr::in,
    maybe_known_truth::out, tfzn_constraint_set::out,
    tr_info::in, tr_info::out) is det.

translate_negation_using_reification(ILHSVar, BoolContext, MaybeAssertedTruthA,
        TMznBoolA, MaybeKnownTruth, Constraints, !Info) :-
    NegILHSVarInfo = var_info_bool(var_is_var, var_is_not_output, no, no),
    add_tmp_var_bool(NegILHSVarInfo, NegILHSVar, !Info),
    NegILHS = ilhs_reif(NegILHSVar),
    ( BoolContext = ctxt_pos, BoolContextA = ctxt_neg
    ; BoolContext = ctxt_neg, BoolContextA = ctxt_pos
    ; BoolContext = ctxt_mix, BoolContextA = ctxt_mix
    ),
    % XXX Is MaybeKnownTruthA the right thing to pass here?
    translate_bool_expr_to_tfzn_constraints(NegILHS, BoolContextA,
        MaybeAssertedTruthA, TMznBoolA, MaybeKnownTruthA, ConstraintsA, !Info),
    MaybeKnownTruth = maybe_known_truth_not(MaybeKnownTruthA),

    % This constraint implements "ILHSVar <-> not NegILHSVar".
    Constraint = tfzn_constr_bool_arith_unop(bool_not,
        tfzn_bool_term_var(ILHSVar), tfzn_bool_term_var(NegILHSVar)),
    % XXX Anns
    % Ann = constr_ann_defines_var(def_bool_var(NegILHSVar)),
    % Anns = set.make_singleton_set(Ann),
    set.init(Anns),
    ConstraintItem = tfzn_item_constraint(Constraint, Anns),
    Constraints = one_tfzn_constraint(ConstraintItem) ++ ConstraintsA.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred translate_bool_bool_to_bool(ilhs::in, bool_context::in,
    maybe(asserted_truth)::in, src_pos::in, bool_bool_to_bool_op::in,
    tmzn_bool_expr::in, tmzn_bool_expr::in, maybe_known_truth::out,
    tfzn_constraint_set::out, tr_info::in, tr_info::out) is det.

translate_bool_bool_to_bool(ILHS, BoolContext, MaybeAssertedTruth, SrcPos,
        BB2BOp, TMznBoolA, TMznBoolB, MaybeKnownTruth, Constraints, !Info) :-
    (
        ( BB2BOp = bb2b_and
        ; BB2BOp = bb2b_min
        ),
        translate_bool_bool_to_bool_and(ILHS, BoolContext, MaybeAssertedTruth,
            SrcPos, TMznBoolA, TMznBoolB, MaybeKnownTruth, Constraints, !Info)
    ;
        ( BB2BOp = bb2b_or
        ; BB2BOp = bb2b_max
        ),
        translate_bool_bool_to_bool_or(ILHS, BoolContext, MaybeAssertedTruth,
            SrcPos, TMznBoolA, TMznBoolB, MaybeKnownTruth, Constraints, !Info)
    ;
        (
            BB2BOp = bb2b_lt,
            asserted_truth_lt(MaybeAssertedTruth,
                MaybeAssertedTruthA, MaybeAssertedTruthB),
            TMznBoolN = TMznBoolA,
            TMznBoolY = TMznBoolB,
            MaybeAssertedTruthN = MaybeAssertedTruthA,
            MaybeAssertedTruthY = MaybeAssertedTruthB
        ;
            BB2BOp = bb2b_gt,
            asserted_truth_lt(MaybeAssertedTruth,
                MaybeAssertedTruthA, MaybeAssertedTruthB),
            TMznBoolY = TMznBoolA,
            TMznBoolN = TMznBoolB,
            MaybeAssertedTruthY = MaybeAssertedTruthA,
            MaybeAssertedTruthN = MaybeAssertedTruthB
        ),
        translate_bool_bool_to_bool_lt(ILHS, BoolContext, MaybeAssertedTruth,
            MaybeAssertedTruthN, MaybeAssertedTruthY,
            SrcPos, TMznBoolN, TMznBoolY, MaybeKnownTruth, Constraints, !Info)
    ;
        (
            BB2BOp = bb2b_le,
            TMznBoolL = TMznBoolA,
            TMznBoolG = TMznBoolB
        ;
            BB2BOp = bb2b_imp2r,
            TMznBoolL = TMznBoolA,
            TMznBoolG = TMznBoolB
        ;
            BB2BOp = bb2b_ge,
            TMznBoolG = TMznBoolA,
            TMznBoolL = TMznBoolB
        ;
            BB2BOp = bb2b_imp2l,
            TMznBoolG = TMznBoolA,
            TMznBoolL = TMznBoolB
        ),
        translate_bool_bool_to_bool_le(ILHS, BoolContext, MaybeAssertedTruth,
            SrcPos, TMznBoolL, TMznBoolG, MaybeKnownTruth, Constraints, !Info)
    ;
        ( BB2BOp = bb2b_ee
        ; BB2BOp = bb2b_eq
        ; BB2BOp = bb2b_biimp
        ),
        translate_bool_bool_to_bool_eq(ILHS, BoolContext, MaybeAssertedTruth,
            SrcPos, TMznBoolA, TMznBoolB, MaybeKnownTruth, Constraints, !Info)
    ;
        ( BB2BOp = bb2b_ne
        ; BB2BOp = bb2b_xor
        ),
        add_nyi_error_info($pred, phase_constraint, SrcPos, "ne", !Info),
        MaybeKnownTruth = unknown_truth,
        Constraints = no_tfzn_constraints
    ),
    trace [compiletime(flag("bool_expr")), io(!IO)] (
        io.write_string("\ntranslate_bool_bool_to_bool(", !IO),
        io.write_string(dump_ilhs(ILHS), !IO),
        io.write_string(", ", !IO),
        io.write(BB2BOp, !IO),
        io.write_string(", ", !IO),
        io.write_string(dump_tmzn_bool_expr(no_parens, TMznBoolA), !IO),
        io.write_string(", ", !IO),
        io.write_string(dump_tmzn_bool_expr(no_parens, TMznBoolB), !IO),
        io.write_string("):\n", !IO),
        OutputTFznOpts = output_opts(yes, 2),
        list.foldl(
            output_tfzn_constraint_item(OutputTFznOpts, io.stdout_stream),
            tfzn_constraint_set_to_list(Constraints), !IO)
    ).

:- pred translate_bool_bool_to_bool_and(ilhs::in, bool_context::in,
    maybe(asserted_truth)::in, src_pos::in,
    tmzn_bool_expr::in, tmzn_bool_expr::in, maybe_known_truth::out,
    tfzn_constraint_set::out, tr_info::in, tr_info::out) is det.

translate_bool_bool_to_bool_and(ILHS, BoolContext, MaybeAssertedTruth,
        _SrcPos, TMznBoolA, TMznBoolB, MaybeKnownTruth, Constraints, !Info) :-
    (
        (
            ILHS = ilhs_true,
            asserted_truth_and(MaybeAssertedTruth,
                MaybeAssertedTruthA, MaybeAssertedTruthB)
        ;
            ILHS = ilhs_var(_ILHSVar),
            MaybeAssertedTruthA = no,
            MaybeAssertedTruthB = no
        ),
        translate_bool_expr_to_tfzn_constraints(ILHS, BoolContext,
            MaybeAssertedTruthA, TMznBoolA, MaybeKnownTruthA,
            ConstraintsA, !Info),
        translate_bool_expr_to_tfzn_constraints(ILHS, BoolContext,
            MaybeAssertedTruthB, TMznBoolB, MaybeKnownTruthB,
            ConstraintsB, !Info),
        MaybeKnownTruth =
            maybe_known_truth_and(MaybeKnownTruthA, MaybeKnownTruthB),
        Constraints = ConstraintsA ++ ConstraintsB
    ;
        ILHS = ilhs_reif(ILHSVar),
        MaybeAssertedTruthA = no,
        MaybeAssertedTruthB = no,
        ILHSVarInfoA = var_info_bool(var_is_var, var_is_not_output, no, no),
        ILHSVarInfoB = var_info_bool(var_is_var, var_is_not_output, no, no),
        add_tmp_var_bool(ILHSVarInfoA, ILHSVarA, !Info),
        add_tmp_var_bool(ILHSVarInfoB, ILHSVarB, !Info),
        ILHSA = ilhs_reif(ILHSVarA),
        ILHSB = ilhs_reif(ILHSVarB),
        translate_bool_expr_to_tfzn_constraints(ILHSA, BoolContext,
            MaybeAssertedTruthA, TMznBoolA, MaybeKnownTruthA,
            ConstraintsA, !Info),
        translate_bool_expr_to_tfzn_constraints(ILHSB, BoolContext,
            MaybeAssertedTruthB, TMznBoolB, MaybeKnownTruthB,
            ConstraintsB, !Info),
        MaybeKnownTruth =
            maybe_known_truth_and(MaybeKnownTruthA, MaybeKnownTruthB),

        % This constraint implements "ILHSVar <-> ILHSVarA and ILHSVarB".
        Constraint = tfzn_constr_bool_arith_binop(bool_and,
            tfzn_bool_term_var(ILHSVarA), tfzn_bool_term_var(ILHSVarB),
            tfzn_bool_term_var(ILHSVar)),
        % XXX Anns
        set.init(Anns),
        ConstraintItem = tfzn_item_constraint(Constraint, Anns),
        Constraints = one_tfzn_constraint(ConstraintItem) ++
            ConstraintsA ++ ConstraintsB
    ).

:- pred translate_bool_bool_to_bool_or(ilhs::in, bool_context::in,
    maybe(asserted_truth)::in, src_pos::in,
    tmzn_bool_expr::in, tmzn_bool_expr::in, maybe_known_truth::out,
    tfzn_constraint_set::out, tr_info::in, tr_info::out) is det.

translate_bool_bool_to_bool_or(ILHS, BoolContext, MaybeAssertedTruth,
        _SrcPos, TMznBoolA, TMznBoolB, MaybeKnownTruth, Constraints, !Info) :-
    ( BoolContext = ctxt_pos, BoolContextArg = ctxt_pos
    ; BoolContext = ctxt_neg, BoolContextArg = ctxt_mix % XXX ???
    ; BoolContext = ctxt_mix, BoolContextArg = ctxt_mix
    ),
    ILHSVarInfoA = var_info_bool(var_is_var, var_is_not_output, no, no),
    ILHSVarInfoB = var_info_bool(var_is_var, var_is_not_output, no, no),
    add_tmp_var_bool(ILHSVarInfoA, ILHSVarA, !Info),
    add_tmp_var_bool(ILHSVarInfoB, ILHSVarB, !Info),
    (
        (
            ILHS = ilhs_true,
            asserted_truth_or(MaybeAssertedTruth,
                MaybeAssertedTruthA, MaybeAssertedTruthB)
        ;
            ILHS = ilhs_var(_),
            MaybeAssertedTruthA = no,
            MaybeAssertedTruthB = no
        ),
        ILHSA = ilhs_var(ILHSVarA),
        ILHSB = ilhs_var(ILHSVarB),
        translate_bool_expr_to_tfzn_constraints(ILHSA, BoolContextArg,
            MaybeAssertedTruthA, TMznBoolA, MaybeKnownTruthA,
            ConstraintsA, !Info),
        translate_bool_expr_to_tfzn_constraints(ILHSB, BoolContextArg,
            MaybeAssertedTruthB, TMznBoolB, MaybeKnownTruthB,
            ConstraintsB, !Info),
        MaybeKnownTruth =
            maybe_known_truth_or(MaybeKnownTruthA, MaybeKnownTruthB),

        % These constraints implement "ILHSVar -> ILHSVarA or ILHSVarB".
        % XXX Anns
        set.init(Anns),
        (
            ILHS = ilhs_true,
            ConstraintOr = tfzn_constr_bool_arith_binop(bool_or,
                tfzn_bool_term_var(ILHSVarA), tfzn_bool_term_var(ILHSVarB),
                tfzn_bool_term_const(yes)),
            ConstraintItemOr =
                tfzn_item_constraint(ConstraintOr, Anns),
            Constraints = one_tfzn_constraint(ConstraintItemOr) ++
                ConstraintsA ++ ConstraintsB
        ;
            ILHS = ilhs_var(ILHSVar),
            VarAorBInfo = var_info_bool(var_is_var, var_is_not_output, no, no),
            add_tmp_var_bool(VarAorBInfo, VarAorB, !Info),
            ConstraintOr = tfzn_constr_bool_arith_binop(bool_or,
                tfzn_bool_term_var(ILHSVarA), tfzn_bool_term_var(ILHSVarB),
                tfzn_bool_term_var(VarAorB)),
            ConstraintImply = tfzn_constr_bool_compare(bool_le,
                tfzn_bool_term_var(ILHSVar), tfzn_bool_term_var(VarAorB),
                not_reified),
            ConstraintItemOr = tfzn_item_constraint(ConstraintOr, Anns),
            ConstraintItemImply = tfzn_item_constraint(ConstraintImply, Anns),
            Constraints =
                one_tfzn_constraint(ConstraintItemOr) ++
                one_tfzn_constraint(ConstraintItemImply) ++
                ConstraintsA ++ ConstraintsB
        )
    ;
        ILHS = ilhs_reif(ILHSVar),
        MaybeAssertedTruthA = no,
        MaybeAssertedTruthB = no,
        ILHSA = ilhs_reif(ILHSVarA),
        ILHSB = ilhs_reif(ILHSVarB),
        translate_bool_expr_to_tfzn_constraints(ILHSA, BoolContextArg,
            MaybeAssertedTruthA, TMznBoolA, MaybeKnownTruthA,
            ConstraintsA, !Info),
        translate_bool_expr_to_tfzn_constraints(ILHSB, BoolContextArg,
            MaybeAssertedTruthB, TMznBoolB, MaybeKnownTruthB,
            ConstraintsB, !Info),
        MaybeKnownTruth =
            maybe_known_truth_or(MaybeKnownTruthA, MaybeKnownTruthB),

        % This constraint implements "ILHSVar <-> ILHSVarA and ILHSVarB".
        Constraint = tfzn_constr_bool_arith_binop(bool_or,
            tfzn_bool_term_var(ILHSVarA), tfzn_bool_term_var(ILHSVarB),
            tfzn_bool_term_var(ILHSVar)),
        % XXX Anns
        set.init(Anns),
        ConstraintItem = tfzn_item_constraint(Constraint, Anns),
        Constraints = one_tfzn_constraint(ConstraintItem) ++
            ConstraintsA ++ ConstraintsB
    ).

:- pred translate_bool_bool_to_bool_lt(ilhs::in, bool_context::in,
    maybe(asserted_truth)::in,
    maybe(asserted_truth)::in, maybe(asserted_truth)::in, src_pos::in,
    tmzn_bool_expr::in, tmzn_bool_expr::in, maybe_known_truth::out,
    tfzn_constraint_set::out, tr_info::in, tr_info::out) is det.

translate_bool_bool_to_bool_lt(ILHS, _BoolContext, _MaybeAssertedTruth,
        MaybeAssertedTruthN, MaybeAssertedTruthY,
        _SrcPos, TMznBoolN, TMznBoolY, MaybeKnownTruth, Constraints, !Info) :-
    ILHSVarInfoN = var_info_bool(var_is_var, var_is_not_output, no, no),
    ILHSVarInfoY = var_info_bool(var_is_var, var_is_not_output, no, no),
    add_tmp_var_bool(ILHSVarInfoN, ILHSVarN, !Info),
    add_tmp_var_bool(ILHSVarInfoY, ILHSVarY, !Info),
    ILHSN = ilhs_reif(ILHSVarN),
    ILHSY = ilhs_reif(ILHSVarY),
    % XXX BoolContexts
    translate_bool_expr_to_tfzn_constraints(ILHSN, ctxt_mix,
        MaybeAssertedTruthN, TMznBoolN, _MaybeKnownTruthN,
        ConstraintsN, !Info),
    translate_bool_expr_to_tfzn_constraints(ILHSY, ctxt_mix,
        MaybeAssertedTruthY, TMznBoolY, _MaybeKnownTruthY,
        ConstraintsY, !Info),
    % XXX Can we compute a more useful MaybeKnownTruth, given that
    % the value of the whole boolean expression is not a constant?
    MaybeKnownTruth = unknown_truth,

    % XXX Anns
    set.init(Anns),
    Reification = ilhs_to_tfzn_reification(ILHS),

    % This constraint implements "ILHSVar -> ILHSVarN = false".
    ConstraintN = tfzn_constr_bool_compare(bool_eq,
        tfzn_bool_term_var(ILHSVarN), tfzn_bool_term_const(no), Reification),
    ConstraintItemN = tfzn_item_constraint(ConstraintN, Anns),

    % This constraint implements "ILHSVar -> ILHSVarY = true".
    ConstraintY = tfzn_constr_bool_compare(bool_eq,
        tfzn_bool_term_var(ILHSVarY), tfzn_bool_term_const(yes), Reification),
    ConstraintItemY = tfzn_item_constraint(ConstraintY, Anns),

    Constraints =
        one_tfzn_constraint(ConstraintItemN) ++ ConstraintsN ++
        one_tfzn_constraint(ConstraintItemY) ++ ConstraintsY.

:- pred translate_bool_bool_to_bool_le(ilhs::in, bool_context::in,
    maybe(asserted_truth)::in, src_pos::in,
    tmzn_bool_expr::in, tmzn_bool_expr::in, maybe_known_truth::out,
    tfzn_constraint_set::out, tr_info::in, tr_info::out) is det.

translate_bool_bool_to_bool_le(ILHS, _BoolContext, _MaybeAssertedTruth,
        _SrcPos, TMznBoolA, TMznBoolB, MaybeKnownTruth, Constraints, !Info) :-
    % This alternate solution generates a suboptimal translation, one that
    % breaks down the problem too far, into too many constraints.
    %
    % % Implement "A =< B" as "(not A) or B".
    % (
    %     ILHS = ilhs_true,
    %     MaybeAssertedTruthNew = MaybeAssertedTruth
    % ;
    %     ILHS = ilhs_var(_),
    %     MaybeAssertedTruthNew = no
    % ),
    % TMznBoolSubExpr = tmzn_bool_expr_b2b(SrcPos, b2b_not, TMznBoolA),
    % % XXX SrcPos
    % TMznBoolExpr = tmzn_bool_expr_bb2b(SrcPos, bb2b_or,
    %     TMznBoolSubExpr, TMznBoolB),
    % % XXX BoolContext
    % translate_bool_expr_to_tfzn_constraints(ILHS, ctxt_mix,
    %     MaybeAssertedTruthNew, TMznBoolExpr, MaybeKnownTruth,
    %     Constraints, !Info)

    (
        
        ILHS = ilhs_true,
        Reification = not_reified
    ;
        ILHS = ilhs_var(ILHSVar),
        Reification = half_reified(tfzn_bool_term_var(ILHSVar))
    ;
        ILHS = ilhs_reif(ILHSVar),
        Reification = fully_reified(tfzn_bool_term_var(ILHSVar))
    ),

    % XXX
    MaybeAssertedTruthA = no,
    MaybeAssertedTruthB = no,
    % XXX BoolContext
    represent_bool_expr_by_var_if_needed(ctxt_mix, MaybeAssertedTruthA,
        TMznBoolA, MaybeKnownTruthA, ILHSVarA, ConstraintsA, !Info),
    % XXX BoolContext
    represent_bool_expr_by_var_if_needed(ctxt_mix, MaybeAssertedTruthB,
        TMznBoolB, MaybeKnownTruthB, ILHSVarB, ConstraintsB, !Info),
    (
        MaybeKnownTruthA = unknown_truth,
        MaybeKnownTruthB = unknown_truth,
        MaybeKnownTruth = unknown_truth
    ;
        MaybeKnownTruthA = known_truth(_),
        MaybeKnownTruthB = unknown_truth,
        MaybeKnownTruth = unknown_truth
    ;
        MaybeKnownTruthA = unknown_truth,
        MaybeKnownTruthB = known_truth(_),
        MaybeKnownTruth = unknown_truth
    ;
        MaybeKnownTruthA = known_truth(KnownTruthA),
        MaybeKnownTruthB = known_truth(KnownTruthB),
        (
            KnownTruthA = known_false,
            KnownTruthB = known_false,
            KnownTruth = known_true
        ;
            KnownTruthA = known_false,
            KnownTruthB = known_true,
            KnownTruth = known_true
        ;
            KnownTruthA = known_true,
            KnownTruthB = known_false,
            KnownTruth = known_false
        ;
            KnownTruthA = known_true,
            KnownTruthB = known_true,
            KnownTruth = known_true
        ),
        MaybeKnownTruth = known_truth(KnownTruth)
    ),

    ConstraintLE = tfzn_constr_bool_compare(bool_le,
        tfzn_bool_term_var(ILHSVarA), tfzn_bool_term_var(ILHSVarB),
        Reification),
    % XXX Anns
    set.init(Anns),
    ConstraintItem = tfzn_item_constraint(ConstraintLE, Anns),
    Constraints = ConstraintsA ++ ConstraintsB ++
        one_tfzn_constraint(ConstraintItem).

:- pred translate_bool_bool_to_bool_eq(ilhs::in, bool_context::in,
    maybe(asserted_truth)::in, src_pos::in,
    tmzn_bool_expr::in, tmzn_bool_expr::in, maybe_known_truth::out,
    tfzn_constraint_set::out, tr_info::in, tr_info::out) is det.

translate_bool_bool_to_bool_eq(ILHS, BoolContext, MaybeAssertedTruth,
        SrcPos, TMznBoolA, TMznBoolB, MaybeKnownTruth, Constraints, !Info) :-
    % Note: any errors in TMznBoolExprA/B should have been discovered
    % and added to !Info when we called is_bool_const_expr on the WHOLE
    % TMznBoolExpr.
    is_bool_const_expr(!.Info, TMznBoolA, MaybeBoolConstA, [], _SpecsA),
    is_bool_const_expr(!.Info, TMznBoolB, MaybeBoolConstB, [], _SpecsB),
    (
        MaybeBoolConstA = no,
        MaybeBoolConstB = no,

        % XXX draft translation

        MaybeAssertedTruthA = no,
        MaybeAssertedTruthB = no,
        % XXX BoolContext
        represent_bool_expr_by_var_if_needed(ctxt_mix, MaybeAssertedTruthA,
            TMznBoolA, MaybeKnownTruthA, ILHSVarA, ConstraintsA, !Info),
        % XXX BoolContext
        represent_bool_expr_by_var_if_needed(ctxt_mix, MaybeAssertedTruthB,
            TMznBoolB, MaybeKnownTruthB, ILHSVarB, ConstraintsB, !Info),
        MaybeKnownTruth =
            maybe_known_truth_eq(MaybeKnownTruthA, MaybeKnownTruthB),
        (
            ILHS = ilhs_true,
            % Implement the constraint "ILHSVarA <-> ILHSVarB".
            Reification = not_reified
        ;
            ILHS = ilhs_var(ILHSVar),
            % Implement the constraint "ILHSVar -> (ILHSVarA <-> ILHSVarB)".
            Reification = half_reified(tfzn_bool_term_var(ILHSVar))
        ;
            ILHS = ilhs_reif(ILHSVar),
            % Implement the constraint "ILHSVar <-> (ILHSVarA <-> ILHSVarB)".
            Reification = fully_reified(tfzn_bool_term_var(ILHSVar))
        ),
        ConstraintEq = tfzn_constr_bool_compare(bool_eq,
            tfzn_bool_term_var(ILHSVarA), tfzn_bool_term_var(ILHSVarB),
            Reification),
        % XXX Anns
        set.init(Anns),
        ConstraintItem = tfzn_item_constraint(ConstraintEq, Anns),
        Constraints = ConstraintsA ++ ConstraintsB ++
            one_tfzn_constraint(ConstraintItem)
    ;
        MaybeBoolConstA = no,
        MaybeBoolConstB = yes(BoolConstB),
        translate_bool_bool_to_bool_eq_const(ILHS, BoolContext,
            MaybeAssertedTruth, SrcPos, TMznBoolA, BoolConstB,
            MaybeKnownTruth, Constraints, !Info)
    ;
        MaybeBoolConstA = yes(BoolConstA),
        MaybeBoolConstB = no,
        translate_bool_bool_to_bool_eq_const(ILHS, BoolContext,
            MaybeAssertedTruth, SrcPos, TMznBoolB, BoolConstA,
            MaybeKnownTruth, Constraints, !Info)
    ;
        MaybeBoolConstA = yes(_),
        MaybeBoolConstB = yes(_),
        % In this case, the WHOLE of TMznBoolExpr should have been
        % seen to be a constant, and we should never have got here.
        unexpected($module, $pred, "MaybeBoolConst A & B both yes(_)")
    ).

:- pred translate_bool_bool_to_bool_eq_const(ilhs::in, bool_context::in,
    maybe(asserted_truth)::in, src_pos::in,
    tmzn_bool_expr::in, bool::in, maybe_known_truth::out,
    tfzn_constraint_set::out, tr_info::in, tr_info::out) is det.

translate_bool_bool_to_bool_eq_const(ILHS, BoolContext,
        MaybeAssertedTruth, _SrcPos, TMznBoolA, BoolConstB,
        MaybeKnownTruth, Constraints, !Info) :-
    % XXX draft translation
    ( if
        ILHS = ilhs_true,
        BoolContext = ctxt_pos,
        MaybeAssertedTruth = yes(asserted_true),
        BoolConstB = yes
    then
        % XXX BoolContext
        translate_bool_expr_to_tfzn_constraints(ilhs_true, BoolContext,
            yes(asserted_true), TMznBoolA, MaybeKnownTruth, Constraints, !Info)
    else
        MaybeAssertedTruthA = no,
        % XXX BoolContext
        represent_bool_expr_by_var_if_needed(BoolContext, MaybeAssertedTruthA,
            TMznBoolA, MaybeKnownTruthA, ILHSVarA, ConstraintsA, !Info),
        MaybeKnownTruth =
            maybe_known_truth_eq(MaybeKnownTruthA, known_truth(known_true)),
        (
            ILHS = ilhs_true,
            % Implement the constraint "ILHSVarA <-> BoolConstB".
            Reification = not_reified
        ;
            ILHS = ilhs_var(ILHSVar),
            % Implement the constraint "ILHSVar -> (ILHSVarA <-> BoolConstB)".
            Reification = half_reified(tfzn_bool_term_var(ILHSVar))
        ;
            ILHS = ilhs_reif(ILHSVar),
            % Implement the constraint "ILHSVar <-> (ILHSVarA <-> BoolConstB)".
            Reification = fully_reified(tfzn_bool_term_var(ILHSVar))
        ),
        ConstraintEq = tfzn_constr_bool_compare(bool_eq,
            tfzn_bool_term_var(ILHSVarA), tfzn_bool_term_const(BoolConstB),
            Reification),
        % XXX Anns
        set.init(Anns),
        ConstraintItem = tfzn_item_constraint(ConstraintEq, Anns),
        Constraints = ConstraintsA ++ one_tfzn_constraint(ConstraintItem)
    ).

:- pred bool_context_for_bb2b_op(bool_bool_to_bool_op::in, bool_context::in,
    bool_context::out, bool_context::out) is det.

% XXX check this
bool_context_for_bb2b_op(bb2b_and,   ctxt_pos, ctxt_pos, ctxt_pos).
bool_context_for_bb2b_op(bb2b_and,   ctxt_neg, ctxt_neg, ctxt_neg).
bool_context_for_bb2b_op(bb2b_and,   ctxt_mix, ctxt_mix, ctxt_mix).
bool_context_for_bb2b_op(bb2b_or,    ctxt_pos, ctxt_pos, ctxt_pos).
bool_context_for_bb2b_op(bb2b_or,    ctxt_neg, ctxt_mix, ctxt_mix).
bool_context_for_bb2b_op(bb2b_or,    ctxt_mix, ctxt_mix, ctxt_mix).
bool_context_for_bb2b_op(bb2b_xor,   _,        ctxt_mix, ctxt_mix).
bool_context_for_bb2b_op(bb2b_imp2r, ctxt_pos, ctxt_neg, ctxt_pos).
bool_context_for_bb2b_op(bb2b_imp2r, ctxt_neg, ctxt_pos, ctxt_neg).
bool_context_for_bb2b_op(bb2b_imp2r, ctxt_mix, ctxt_mix, ctxt_mix).
bool_context_for_bb2b_op(bb2b_imp2l, ctxt_pos, ctxt_pos, ctxt_neg).
bool_context_for_bb2b_op(bb2b_imp2l, ctxt_neg, ctxt_neg, ctxt_pos).
bool_context_for_bb2b_op(bb2b_imp2l, ctxt_mix, ctxt_mix, ctxt_mix).
bool_context_for_bb2b_op(bb2b_biimp, _,        ctxt_mix, ctxt_mix).
bool_context_for_bb2b_op(bb2b_min,   ctxt_pos, ctxt_pos, ctxt_pos).
bool_context_for_bb2b_op(bb2b_min,   ctxt_neg, ctxt_neg, ctxt_neg).
bool_context_for_bb2b_op(bb2b_min,   ctxt_mix, ctxt_mix, ctxt_mix).
bool_context_for_bb2b_op(bb2b_max,   ctxt_pos, ctxt_pos, ctxt_pos).
bool_context_for_bb2b_op(bb2b_max,   ctxt_neg, ctxt_mix, ctxt_mix).
bool_context_for_bb2b_op(bb2b_max,   ctxt_mix, ctxt_mix, ctxt_mix).
bool_context_for_bb2b_op(bb2b_eq,    _,        ctxt_mix, ctxt_mix).
bool_context_for_bb2b_op(bb2b_ee,    _,        ctxt_mix, ctxt_mix).
bool_context_for_bb2b_op(bb2b_ne,    _,        ctxt_mix, ctxt_mix).
bool_context_for_bb2b_op(bb2b_le,    _,        ctxt_mix, ctxt_mix).
bool_context_for_bb2b_op(bb2b_lt,    _,        ctxt_mix, ctxt_mix).
bool_context_for_bb2b_op(bb2b_ge,    _,        ctxt_mix, ctxt_mix).
bool_context_for_bb2b_op(bb2b_gt,    _,        ctxt_mix, ctxt_mix).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred translate_int_int_to_bool(ilhs::in, bool_context::in,
    src_pos::in, int_int_to_bool_op::in,
    tmzn_int_expr::in, tmzn_int_expr::in, maybe_known_truth::out,
    tfzn_constraint_set::out, tr_info::in, tr_info::out) is det.

translate_int_int_to_bool(ILHS, _BoolContext, _SrcPos, II2BOp,
        TMznIntA, TMznIntB, MaybeKnownTruth, Constraints, !Info) :-
    translate_int_expr_to_tfzn_term(ILHS, TMznIntA, TFznIntA,
        ConstraintsA, !Info),
    translate_int_expr_to_tfzn_term(ILHS, TMznIntB, TFznIntB,
        ConstraintsB, !Info),
    ( if
        TFznIntA = tfzn_int_term_const(IntA),
        TFznIntB = tfzn_int_term_const(IntB)
    then
        ( II2BOp = ii2b_eq, BoolZ = ( if IntA = IntB  then yes else no )
        ; II2BOp = ii2b_ee, BoolZ = ( if IntA = IntB  then yes else no )
        ; II2BOp = ii2b_ne, BoolZ = ( if IntA \= IntB then yes else no )
        ; II2BOp = ii2b_le, BoolZ = ( if IntA =< IntB then yes else no )
        ; II2BOp = ii2b_lt, BoolZ = ( if IntA < IntB  then yes else no )
        ; II2BOp = ii2b_gt, BoolZ = ( if IntA >= IntB then yes else no )
        ; II2BOp = ii2b_ge, BoolZ = ( if IntA > IntB  then yes else no )
        ),
        constraint_reduced_to_bool(ILHS, BoolZ, MaybeKnownTruth, Constraints,
            !Info)
    else
%       XXX We cannot make this a switch without a bug fix in the Mercury
%       compiler.
%       (
%           TFznIntA = tfzn_int_term_const(_),
%           TFznIntB = tfzn_int_term_var(_)
%       ;
%           TFznIntA = tfzn_int_term_var(_),
%           TFznIntB = tfzn_int_term_const(_)
%       ;
%           TFznIntA = tfzn_int_term_var(_),
%           TFznIntB = tfzn_int_term_var(_)
%       ),
        int_bounds_range(LBA, UBA) = find_int_term_bounds(!.Info, TFznIntA),
        int_bounds_range(LBB, UBB) = find_int_term_bounds(!.Info, TFznIntB),
        (
            ( II2BOp = ii2b_eq
            ; II2BOp = ii2b_ee
            ),
            ( if TFznIntA = TFznIntB then
                MaybeKnownTruth = known_truth(known_true),
                % XXX Should we keep ConstraintsA ++ ConstraintsB?
                Constraints = no_tfzn_constraints
            else if ( UBA < LBB ; UBB < LBA ) then
                MaybeKnownTruth = known_truth(known_false),
                Constraints = no_tfzn_constraints
            else
                (
                    ILHS = ilhs_true,
                    LB = int.max(LBA, LBB),
                    UB = int.min(UBA, UBB),
                    Bounds = int_bounds_range(LB, UB),
                    update_int_term_bounds(TFznIntA, Bounds, !Info),
                    update_int_term_bounds(TFznIntB, Bounds, !Info)
                ;
                    ( ILHS = ilhs_var(_)
                    ; ILHS = ilhs_reif(_)
                    )
                    % We cannot update the bounds.
                ),
                MaybeKnownTruth = unknown_truth,
                Reification = ilhs_to_tfzn_reification(ILHS),
                Constraint = tfzn_constr_int_compare(int_eq,
                    TFznIntA, TFznIntB, Reification),
                % XXX Anns
                set.init(Anns),
                ConstraintItem = tfzn_item_constraint(Constraint, Anns),
                Constraints = ConstraintsA ++ ConstraintsB ++
                    one_tfzn_constraint(ConstraintItem)
            )
        ;
            II2BOp = ii2b_ne,
            ( if TFznIntA = TFznIntB then
                MaybeKnownTruth = known_truth(known_false),
                % XXX Should we keep ConstraintsA ++ ConstraintsB?
                Constraints = no_tfzn_constraints
            else if ( UBA < LBB ; UBB < LBA ) then
                MaybeKnownTruth = known_truth(known_true),
                Constraints = no_tfzn_constraints
            else
                MaybeKnownTruth = unknown_truth,
                Reification = ilhs_to_tfzn_reification(ILHS),
                Constraint = tfzn_constr_int_compare(int_ne,
                    TFznIntA, TFznIntB, Reification),
                % XXX Anns
                set.init(Anns),
                ConstraintItem = tfzn_item_constraint(Constraint, Anns),
                Constraints = ConstraintsA ++ ConstraintsB ++
                    one_tfzn_constraint(ConstraintItem)
            )
        ;
            (
                II2BOp = ii2b_lt,
                % Transform A < B into X < Y with A = X and B = Y.
                TMznIntX = TMznIntA,
                TMznIntY = TMznIntB,
                TFznIntX = TFznIntA,
                TFznIntY = TFznIntB,
                LBX = LBA,
                UBX = UBA,
                LBY = LBB,
                UBY = UBB
            ;
                II2BOp = ii2b_gt,
                % Transform A > B into X < Y with A = Y and B = X.
                TMznIntY = TMznIntA,
                TMznIntX = TMznIntB,
                TFznIntY = TFznIntA,
                TFznIntX = TFznIntB,
                LBY = LBA,
                UBY = UBA,
                LBX = LBB,
                UBX = UBB
            ),
            ( if UBX < LBY then
                MaybeKnownTruth = known_truth(known_true),
                Constraints = no_tfzn_constraints
            else if UBY < LBX then
                MaybeKnownTruth = known_truth(known_false),
                Constraints = no_tfzn_constraints
            else
                (
                    ILHS = ilhs_true,
                    MaybeNewUBX = int_bounded_plus_maybe(UBY, -1),
                    MaybeNewLBY = int_bounded_plus_maybe(LBX, 1),
                    (
                        MaybeNewUBX = no,
                        SrcPosX = get_src_pos_from_int_expr(TMznIntX),
                        add_overflow_error_info($pred, phase_constraint,
                            SrcPosX, !Info)
                    ;
                        MaybeNewUBX = yes(_)
                    ),
                    (
                        MaybeNewLBY = no,
                        SrcPosY = get_src_pos_from_int_expr(TMznIntY),
                        add_overflow_error_info($pred, phase_constraint,
                            SrcPosY, !Info)
                    ;
                        MaybeNewLBY = yes(_)
                    ),
                    ( if
                        MaybeNewUBX = yes(NewUBX),
                        MaybeNewLBY = yes(NewLBY)
                    then
                        NewBoundsX = int_bounds_range(LBX, NewUBX),
                        NewBoundsY = int_bounds_range(NewLBY, UBY),
                        update_int_term_bounds(TFznIntX, NewBoundsX, !Info),
                        update_int_term_bounds(TFznIntY, NewBoundsY, !Info)
                    else
                        true
                    )
                ;
                    ( ILHS = ilhs_var(_)
                    ; ILHS = ilhs_reif(_)
                    )
                    % We cannot update the bounds.
                ),
                MaybeKnownTruth = unknown_truth,
                Reification = ilhs_to_tfzn_reification(ILHS),
                Constraint = tfzn_constr_int_compare(int_lt,
                    TFznIntX, TFznIntY, Reification),
                % XXX Anns
                set.init(Anns),
                ConstraintItem = tfzn_item_constraint(Constraint, Anns),
                Constraints = ConstraintsA ++ ConstraintsB ++
                    one_tfzn_constraint(ConstraintItem)
            )
        ;
            (
                II2BOp = ii2b_le,
                % Transform A =< B into X =< Y with A = X and B = Y.
                TFznIntX = TFznIntA,
                TFznIntY = TFznIntB,
                LBX = LBA,
                UBX = UBA,
                LBY = LBB,
                UBY = UBB
            ;
                II2BOp = ii2b_ge,
                % Transform A >= B into X =< Y with A = Y and B = X.
                TFznIntY = TFznIntA,
                TFznIntX = TFznIntB,
                LBY = LBA,
                UBY = UBA,
                LBX = LBB,
                UBX = UBB
            ),
            ( if UBX =< LBY then
                MaybeKnownTruth = known_truth(known_true),
                Constraints = no_tfzn_constraints
            else if UBY < LBX then
                MaybeKnownTruth = known_truth(known_false),
                Constraints = no_tfzn_constraints
            else
                (
                    ILHS = ilhs_true,
                    NewUBX = UBY,
                    NewLBY = LBX,
                    NewBoundsX = int_bounds_range(LBX, NewUBX),
                    NewBoundsY = int_bounds_range(NewLBY, UBY),
                    update_int_term_bounds(TFznIntX, NewBoundsX, !Info),
                    update_int_term_bounds(TFznIntY, NewBoundsY, !Info)
                ;
                    ( ILHS = ilhs_var(_)
                    ; ILHS = ilhs_reif(_)
                    )
                    % We cannot update the bounds.
                ),
                MaybeKnownTruth = unknown_truth,
                Reification = ilhs_to_tfzn_reification(ILHS),
                Constraint = tfzn_constr_int_compare(int_le,
                    TFznIntX, TFznIntY, Reification),
                % XXX Anns
                set.init(Anns),
                ConstraintItem = tfzn_item_constraint(Constraint, Anns),
                Constraints = ConstraintsA ++ ConstraintsB ++
                    one_tfzn_constraint(ConstraintItem)
            )
        )
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred constraint_reduced_to_bool(ilhs::in, bool::in,
    maybe_known_truth::out, tfzn_constraint_set::out,
    tr_info::in, tr_info::out) is det.

constraint_reduced_to_bool(ILHS, Bool, MaybeKnownTruth, Constraints, !Info) :-
    (
        ILHS = ilhs_true,
        (
            Bool = no,
            KnownTruth = known_false
        ;
            Bool = yes,
            KnownTruth = known_true
        ),
        MaybeKnownTruth = known_truth(KnownTruth),
        Constraints = no_tfzn_constraints
    ;
        ILHS = ilhs_var(ILHSVar),
        (
            Bool = no,
            % ILHSVar -> false
            constrain_var_to_bool(ilhs_true, ILHSVar, no, Constraints),
            maybe_update_bool_var_known(ILHSVar, yes(no), MaybeKnownTruth,
                !Info)
        ;
            Bool = yes,
            MaybeKnownTruth = known_truth(known_true),
            Constraints = no_tfzn_constraints
        )
    ;
        ILHS = ilhs_reif(ILHSVar),
        % ILHSVar <-> Bool
        constrain_var_to_bool(ilhs_true, ILHSVar, Bool, Constraints),
        maybe_update_bool_var_known(ILHSVar, yes(Bool), MaybeKnownTruth, !Info)
    ).

:- pred maybe_update_bool_var_known(tfzn_bool_var::in,
    maybe(bool)::in, maybe_known_truth::out, tr_info::in, tr_info::out) is det.

maybe_update_bool_var_known(TFznBoolVar, MaybeValue, MaybeKnownTruth, !Info) :-
    tr_info_get_var_info_maps(!.Info, VarInfoMaps0),
    vim_get_bool_map(VarInfoMaps0, BoolMap0),
    ( if map.search(BoolMap0, TFznBoolVar, OldVarInfo) then
        MaybeOldVarValue = OldVarInfo ^ vib_is_known,
        (
            MaybeOldVarValue = no,
            (
                MaybeValue = no
                % We didn't used to know the value; we still do not.
            ;
                MaybeValue = yes(_Value),
                % We didn't used to know the value, but now we do.
                NewVarInfo = OldVarInfo ^ vib_is_known := MaybeValue,
                map.det_update(TFznBoolVar, NewVarInfo, BoolMap0, BoolMap),
                vim_set_bool_map(BoolMap, VarInfoMaps0, VarInfoMaps),
                tr_info_set_var_info_maps(VarInfoMaps, !Info)
            ),
            MaybeKnownTruth = unknown_truth
        ;
            MaybeOldVarValue = yes(OldVarValue),
            (
                MaybeValue = no,
                % We used to know the value, and we see no information
                % to contradict it.
                MaybeKnownTruth = unknown_truth
            ;
                MaybeValue = yes(NewValue),
                ( if OldVarValue = NewValue then
                    % We used to know the value, and we now confirm it.
                    MaybeKnownTruth = known_truth(known_true)
                else
                    % We used to know the value, and we now CONTRADICT it.
                    MaybeKnownTruth = known_truth(known_false)
                )
            )
        )
    else
        % XXX MaybeExpr
        MaybeExpr = no,
        VarInfo = var_info_bool(var_is_var, var_is_not_output,
            MaybeValue, MaybeExpr),
        map.det_insert(TFznBoolVar, VarInfo, BoolMap0, BoolMap),
        vim_set_bool_map(BoolMap, VarInfoMaps0, VarInfoMaps),
        tr_info_set_var_info_maps(VarInfoMaps, !Info),
        MaybeKnownTruth = unknown_truth
    ).

:- pred represent_bool_expr_by_var_if_needed(bool_context::in,
    maybe(asserted_truth)::in, tmzn_bool_expr::in,
    maybe_known_truth::out, tfzn_bool_var::out, tfzn_constraint_set::out,
    tr_info::in, tr_info::out) is det.

represent_bool_expr_by_var_if_needed(BoolContext, MaybeAssertedTruth,
        TMznBoolExpr, MaybeKnownTruth, RepresentingTFznVar, Constraints,
        !Info) :-
    ( if
        TMznBoolExpr = tmzn_bool_expr_var(_, TMznBoolVar),
        TMznBoolVar = tmzn_bool_var_named(VarName)
    then
        RepresentingTFznVar = tfzn_bool_var_named(VarName),
        maybe_asserted_to_maybe_value(MaybeAssertedTruth, MaybeValue),
        maybe_update_bool_var_known(RepresentingTFznVar, MaybeValue,
            MaybeKnownTruth, !Info),
        Constraints = no_tfzn_constraints
    else
        RepresentingVarInfo = var_info_bool(var_is_var, var_is_not_output,
            no, yes(TMznBoolExpr)),
        add_tmp_var_bool(RepresentingVarInfo, RepresentingTFznVar, !Info),
        % XXX BoolContext
        ILHS = ilhs_reif(RepresentingTFznVar),
        translate_bool_expr_to_tfzn_constraints(ILHS, BoolContext,
            MaybeAssertedTruth, TMznBoolExpr, MaybeKnownTruth,
            Constraints, !Info)
    ).

:- pred constraint_reduced_to_var(ilhs::in, tfzn_bool_var::in,
    tfzn_constraint_set::out) is det.

constraint_reduced_to_var(ILHS, BoolVar, Constraints) :-
    constrain_var_to_bool(ILHS, BoolVar, yes, Constraints).

:- pred constrain_var_to_bool(ilhs::in, tfzn_bool_var::in, bool::in,
    tfzn_constraint_set::out) is det.

constrain_var_to_bool(ILHS, BoolVar, BoolConst, Constraints) :-
    TFznTerm = tfzn_bool_term_var(BoolVar),
    Reification = ilhs_to_tfzn_reification(ILHS),
    Constraint = tfzn_constr_bool_compare(bool_eq,
        TFznTerm, tfzn_bool_term_const(BoolConst), Reification),
    % XXX Anns
    ConstraintItem = tfzn_item_constraint(Constraint, set.init),
    Constraints = one_tfzn_constraint(ConstraintItem).

%-----------------------------------------------------------------------------%
:- end_module translate.bool.
%-----------------------------------------------------------------------------%
