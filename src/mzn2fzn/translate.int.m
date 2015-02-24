%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
% There are at least three possible approaches to flattening MiniZinc
% expressions into FlatZinc terms; let us call them the Naive, TopDownOpt
% and BottomUpOpt approaches. They all translate MiniZinc expressions
% bottom up, translating the arguments of an operation before translating
% the operation itself. They differ in whether and how they do optimization.
%
%--------------%
%
% The Naive approach does not do any optimization. This has two main
% drawbacks.
%
% First, some operations that could be executed at compile time get executed
% at runtime. Consider the MiniZinc expression
%
%   c1 * (v1 * c2)
%
% This could be transformed into (c1 * c2) * v1, with the multiplication
% of the constants done at compile time, but the Naive approach cannot
% discover this.
%
% Second, the Naive approach cannot discover that complex expressions such as
%
%   c1*v1 + c2*v2 + c3*v3 + c
%
% can be translated into a single int_lin_eq constraint, a constraint that
% is not only more compact than the alternative, a set of times and plus
% constraints, but also has more effective propagation behavior.
%
%--------------%
%
% The TopDown approach is a variant of Naive, but when given a MiniZinc
% expression Expr = Op(Arg1, ..., Argn), BEFORE it tries to translate
% the Argi or Op, it tries to look for optimizable patterns at the top
% level of Expr (patterns involving Op). If it finds such a pattern,
% it would do one of two things.
%
% - First, it could transform Expr to make it optimizable by the normal
%   translation process. For example, transforming c1 * (v1 * c2) into
%   (c1 * c2) * v1 allows the translation process to evaluate c1 * c2
%   at compile time.
%
% - Second, it could handle the translation of the pattern itself, leaving
%   the translation of the leaves of the pattern to recursive invocations
%   of the whole algorithm. For example, one optimizable pattern would be
%   c1*e1 + c2*e2 + c3*e3 + c. The recursive invocations would translate
%   each ei into vi, and the optimizer would then generate a single int_lin_eq
%   constraint.
%
% The problem of this approach is that it does not integrate its two halves
% well. An expression of the form c1a*(e1*c1b+c1c) + c2*e2 + c3*e3 + c does NOT
% match the obvious pattern for the int_lin_eq constraint, yet we want its
% translation to use int_lin_eq. The only way to get there is to use a
% significantly more complex pattern, a pattern that effectively encodes
% the combination of the pattern we are trying to optimize NOW with every
% other pattern we CAN optimize.
%
% One potential strength of this approach is that it CAN be used, at least
% in theory, to look for and optimize any pattern in expressions.
%
% Another strength of this approach is that if some optimizations generate
% kinds of constraints that are available with some solvers but not others,
% then we can make looking for the pattern conditional on targeting a solver
% that can handle those kinds of constraints.
%
%--------------%
%
% The BottomUp approach, which was implemented in flatten.int.m by Ralph
% Becket, does the translation in two stages: translating MiniZinc expressions
% into an intermediate form, and then translating that intermediate form
% into FlatZinc. The first stage does naive translation; the optimizations
% happen in the second stage. (In flatten.int.m, the first stage is done
% by the flatten predicates, the second stage is done by the simplify_int
% predicate, and the intermediate representation is defined by the int_expr
% type.)
%
% This approach is conceptually more complex than the TopDown approach.
% However, it can be easier to build an effective system with it, because
% we can design the intermediate form to represent ONLY the situations
% we want to optimize, with the leaves of a term in the representation
% standing for already translated entities that the pattern match can ignore.
%
% This approach wouldn't be feasible if we wanted to optimize many patterns,
% since that would require the intermediate form to be unreasonably complex.
%
% It is also quite rigid: if you want to expand the set of patterns you want
% to optimize, you may have to redesign the intermediate representation,
% which will probably require changes to MOST of the existing code.
%
%--------------%
%
% This module uses the TopDown approach. To reduce the difficulty of coding
% the pattern match, we make the pattern match try to fit the expression
% into an intermediate representation borrowed by the BottomUp approach.
%
%-----------------------------------------------------------------------------%

:- module translate.int.
:- interface.

:- import_module error_util.
:- import_module tfzn_ast.
:- import_module tmzn_ast.
:- import_module translate.info.

:- import_module assoc_list.
:- import_module list.
:- import_module maybe.

%-----------------------------------------------------------------------------%

    % Translate an integer expression from typed MiniZinc to typed FlatZinc
    % in the given context, and return the constraints generated by the
    % translation.
    %
:- pred translate_int_expr_to_tfzn_term(ilhs::in,
    tmzn_int_expr::in, tfzn_int_term::out, tfzn_constraint_set::out,
    tr_info::in, tr_info::out) is det.

:- type int_linear_expr.

    % Convert the given TMznIntExpr into a form (defined by the type
    % int_linear_expr) from which it is guaranteed to be transformable
    % to a form that matches the expectations of the int_lin_eq constraint
    % (the form is represented by the type int_coeffs_form).
    %
    % Note that every TMznIntExpr can be transformed into this form,
    % since 1 * TMznIntExpr + 0 is of this form. Our caller will decide
    % whether implementing TMznIntExpr using int_lin_eq or similar constraints
    % is USEFUL or not.
    %
:- pred is_int_linear_expr(tr_info::in, tmzn_int_expr::in,
    int_linear_expr::out, list(error_spec)::in, list(error_spec)::out) is det.

    % int_coeffs_form([a - X, b - Y], c) represents the expression
    % aX + bY + c.
    %
:- type int_coeffs_form
    --->    int_coeffs_form(
                assoc_list(int, tmzn_int_expr),
                int
            ).

    % Convert an integer expression from int_linear_expr form to
    % int_coeffs_form.
    %
:- pred int_linear_expr_build_coeffs_form(int_linear_expr::in,
    int_coeffs_form::out) is det.

%-----------------------------------------------------------------------------%

    % Does the given integer MiniZinc expression represent a constant?
    % If it does, return the constant's value.
    %
:- pred is_int_const_expr(tr_info::in, tmzn_int_expr::in, maybe(int)::out,
    list(error_spec)::in, list(error_spec)::out) is det.

%-----------------------------------------------------------------------------%

:- pred int_plus_bounds_specs(src_pos::in, int::in, int::in, int::in, int::in,
    int::out, int::out, list(error_spec)::out) is det.
:- pred int_times_bounds_specs(src_pos::in, int::in, int::in, int::in, int::in,
    int::out, int::out, list(error_spec)::out) is det.

:- pred int_bounded_plus_specs(src_pos::in, int::in, int::in, int::out,
    list(error_spec)::out) is det.
:- pred int_bounded_times_specs(src_pos::in, int::in, int::in, int::out,
    list(error_spec)::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module bounds.
:- import_module mzn_ops.
:- import_module translate.array.
:- import_module translate.bool.
:- import_module translate.vars.
:- import_module types.

:- import_module bool.
:- import_module int.
:- import_module map.
:- import_module pair.
:- import_module set.
:- import_module set_tree234.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

translate_int_expr_to_tfzn_term(ILHS, TMznIntExpr, TFznIntTerm,
        Constraints, !Info) :-
    optimize_special_patterns_int(ILHS, TMznIntExpr, OptResult, !Info),
    (
        OptResult = opt_all_done(TFznIntTerm, Constraints)
    ;
        OptResult = opt_flattening_required(MaybeUpdatedTMznIntExpr),
        translate_int_expr_to_tfzn_term_std(ILHS,
            MaybeUpdatedTMznIntExpr, TFznIntTerm, Constraints, !Info)
    ).

%-----------------------------------------------------------------------------%

:- pred optimize_special_patterns_int(ilhs::in, tmzn_int_expr::in,
    optimize_result_int::out, tr_info::in, tr_info::out) is det.

optimize_special_patterns_int(ILHS, TMznIntExpr, Result, !Info) :-
    is_int_linear_expr(!.Info, TMznIntExpr, LinearExpr, [], Specs),
    add_errors(Specs, !Info),
    ( if LinearExpr = ile_const(IntConst) then
        ResultTerm = tfzn_int_term_const(IntConst),
        Result = opt_all_done(ResultTerm, no_tfzn_constraints)
    else
        int_linear_expr_build_coeffs_form(LinearExpr, CoeffsForm),
        CoeffsForm = int_coeffs_form(CoeffsTMznExprs, Const),
        list.length(CoeffsTMznExprs, NumCoeffsExprs),
        ( if NumCoeffsExprs >= 2 then
            translate_int_lin_eq_args_to_tfzn_terms(ILHS,
                CoeffsTMznExprs, CoeffsTFznTerms,
                no_tfzn_constraints, ArgConstraints, !Info),
            tr_info_get_var_info_maps(!.Info, VarInfoMaps0),
            vim_get_int_map(VarInfoMaps0, IntMap0),
            SrcPos = get_src_pos_from_int_expr(TMznIntExpr),
            verify_and_transform_vectors_int(SrcPos, IntMap0, set_tree234.init,
                CoeffsTFznTerms, Coeffs, TFznVars, LinLB, LinUB, !Info),
            % XXX SrcPos
            int_plus_bounds([], Const, Const, LinLB, LinUB, LBZ, UBZ),
            tr_info_get_cse_maps(!.Info, CSEMaps0),
            get_cse_map_int_lin_eq(CSEMaps0, IntLinEqMap0),
            ( if
                map.search(IntLinEqMap0, {Coeffs, TFznVars, Const}, CSEResult)
            then
                % XXX Can we tighten the bounds on IntVarZ?
                CSEResult = {IntVarZ, ConstraintItem},
                Z = tfzn_int_term_var(IntVarZ)
            else
                IntBoundsZ = int_bounds_range(LBZ, UBZ),
                MaybeIntExpr = yes(TMznIntExpr),
                IntVarInfoZ = var_info_int(var_is_var, var_is_not_output,
                    IntBoundsZ, MaybeIntExpr),
                add_tmp_var_int(IntVarInfoZ, IntVarZ, !Info),
                Z = tfzn_int_term_var(IntVarZ),

                % Given: c1*v1 + c2*v2 + ... + cn*vn + c = z, therefore
                % -1*z + c1*v1 + c2*v2 + ... + cn*vn + c = 0.
                AllCoeffs = [-1 | Coeffs],
                AllTFznVars = [IntVarZ | TFznVars],

                % XXX Should we make the constraint half-reified if ILHS is
                % ilhs_var(BoolVar)? (If we do, we cannot add to CSEMaps0.)
                % If BoolVar = false, then we may not have to compute Z,
                % but testing BoolVar can be more expensive than computing Z.
                Constraint = tfzn_constr_int_linear(int_lin_eq,
                    tfzn_int_array_term_consts(AllCoeffs),
                    tfzn_int_array_term_vars(AllTFznVars),
                    tfzn_int_term_const(Const), not_reified),
                Ann = constr_ann_defines_var(tfzn_def_int_var(IntVarZ)),
                Anns = set.make_singleton_set(Ann),
                ConstraintItem = tfzn_item_constraint(Constraint, Anns),

                map.det_insert({Coeffs, TFznVars, Const},
                    {IntVarZ, ConstraintItem}, IntLinEqMap0, IntLinEqMap),
                set_cse_map_int_lin_eq(IntLinEqMap, CSEMaps0, CSEMaps),
                tr_info_set_cse_maps(CSEMaps, !Info)
            ),
            Constraints = ArgConstraints ++
                one_tfzn_constraint(ConstraintItem),
            Result = opt_all_done(Z, Constraints)
        else
            % We haven't matched the pattern of any implemented optimization.

            % XXX If LinearExpr is of the form c1*v1 + c, but this is derived
            % from a more complex TMznIntExpr like c1a*v1 + c1b*v1 + ca + cb
            % where c1 = c1a+c1b and c = ca + cb, then we should construct
            % and return a tmzn expression for c1*v1 + c. The reason why we
            % don't (yet) do so is that this requires setting useful src_locns
            % on the constructed tmzn_int_exprs, and without an otherwise
            % working transformation, we can't experimentally verify what
            % src_locn would be useful.

            Result = opt_flattening_required(TMznIntExpr)
        )
    ).

:- pred translate_int_lin_eq_args_to_tfzn_terms(ilhs::in,
    assoc_list(int, tmzn_int_expr)::in, assoc_list(int, tfzn_int_term)::out,
    tfzn_constraint_set::in, tfzn_constraint_set::out,
    tr_info::in, tr_info::out) is det.

translate_int_lin_eq_args_to_tfzn_terms(_ILHS, [], [],
        !Constraints, !Info).
translate_int_lin_eq_args_to_tfzn_terms(ILHS,
        [Coeff - TMznExpr | CoeffsTMznExprs],
        [Coeff - TFznTerm | CoeffsTFznTerms], !Constraints, !Info) :-
    translate_int_expr_to_tfzn_term(ILHS, TMznExpr, TFznTerm,
        HeadConstraints, !Info),
    !:Constraints = !.Constraints ++ HeadConstraints,
    translate_int_lin_eq_args_to_tfzn_terms(ILHS,
        CoeffsTMznExprs, CoeffsTFznTerms, !Constraints, !Info).

:- pred verify_and_transform_vectors_int(src_pos::in, var_info_map_int::in,
    set_tree234(tfzn_int_var)::in, assoc_list(int, tfzn_int_term)::in,
    list(int)::out, list(tfzn_int_var)::out, int::out, int::out,
    tr_info::in, tr_info::out) is det.

verify_and_transform_vectors_int(_, _, _, [], [], [], 0, 0, !Info).
verify_and_transform_vectors_int(SrcPos, IntMap, !.SeenVars,
        [CoeffTFznTerm | CoeffsTFznTerms], Coeffs, TFznVars, LB, UB, !Info) :-
    CoeffTFznTerm = Coeff - TFznTerm,
    (
        TFznTerm = tfzn_int_term_const(_),
        add_internal_error_info($pred, phase_constraint, SrcPos,
            "constant term", !Info),
        TFznVar = tfzn_int_var_named("dummy")
    ;
        TFznTerm = tfzn_int_term_var(TFznVar),
        set_tree234.is_member(!.SeenVars, TFznVar, IsMember),
        (
            IsMember = yes,
            add_internal_error_info($pred, phase_constraint, SrcPos,
                "repeated var", !Info)
        ;
            IsMember = no,
            set_tree234.insert(TFznVar, !SeenVars)
        )
    ),
    verify_and_transform_vectors_int(SrcPos, IntMap, !.SeenVars,
        CoeffsTFznTerms, TailCoeffs, TailTFznVars, TailLB, TailUB, !Info),
    Coeffs = [Coeff | TailCoeffs],
    TFznVars = [TFznVar | TailTFznVars],

    map.lookup(IntMap, TFznVar, VarInfo),
    % XXX use VarExpr to update the bounds?
    VarInfo = var_info_int(_Inst, _Output, Bounds, _MaybeVarExpr),
    Bounds = int_bounds_range(HeadLB, HeadUB),
    int_times_bounds_specs(SrcPos, Coeff, Coeff, HeadLB, HeadUB,
        CoeffHeadLB, CoeffHeadUB, CoeffSpecs),
    int_plus_bounds_specs(SrcPos, CoeffHeadLB, CoeffHeadUB, TailLB, TailUB,
        LB, UB, Specs),
    add_errors(CoeffSpecs, !Info),
    add_errors(Specs, !Info).

%-----------------------------------------------------------------------------%

:- type int_linear_expr
    --->    ile_const(int)
    ;       ile_translate_to_var(tmzn_int_expr)
    ;       ile_sum(int_linear_expr, int_linear_expr)
    ;       ile_scale(int, int_linear_expr).

is_int_linear_expr(Info, TMznIntExpr, LinearExpr, !Specs) :-
    % TMznIntExpr may be a constant expression even if it is NOT
    % of the form tmzn_int_expr_const(_).
    is_int_const_expr(Info, TMznIntExpr, MaybeIntConst, !Specs),
    (
        MaybeIntConst = yes(IntConst),
        LinearExpr = ile_const(IntConst)
    ;
        MaybeIntConst = no,
        (
            TMznIntExpr = tmzn_int_expr_const(SrcPos, _Int),
            add_internal_error($pred, phase_constraint, SrcPos,
                "non-constant constant", !Specs),
            LinearExpr = ile_translate_to_var(TMznIntExpr)
        ;
            TMznIntExpr = tmzn_int_expr_i2i(_SrcPos, I2IOp, TMznIntA),
            (
                I2IOp = i2i_add,
                is_int_linear_expr(Info, TMznIntA, LinearExpr, !Specs)
            ;
                I2IOp = i2i_sub,
                is_int_linear_expr(Info, TMznIntA, LinearExprA, !Specs),
                LinearExpr = ile_scale(-1, LinearExprA)
            ;
                ( I2IOp = i2i_abs
                ; I2IOp = i2i_lb
                ; I2IOp = i2i_ub
                ; I2IOp = i2i_dom_size
                ; I2IOp = i2i_fix
                ),
                LinearExpr = ile_translate_to_var(TMznIntExpr)
            )
        ;
            TMznIntExpr = tmzn_int_expr_ii2i(_SrcPos, II2IOp,
                TMznIntA, TMznIntB),
            (
                II2IOp = ii2i_add,
                is_int_linear_expr(Info, TMznIntA, LinearExprA, !Specs),
                is_int_linear_expr(Info, TMznIntB, LinearExprB, !Specs),
                LinearExpr = ile_sum(LinearExprA, LinearExprB)
            ;
                II2IOp = ii2i_sub,
                is_int_linear_expr(Info, TMznIntA, LinearExprA, !Specs),
                is_int_linear_expr(Info, TMznIntB, LinearExprB, !Specs),
                LinearExpr = ile_sum(LinearExprA, ile_scale(-1, LinearExprB))
            ;
                II2IOp = ii2i_mul,
                % We don't care here whether IntConstA or IntConstB are
                % equal to 1; we will simplify such cases later.
                is_int_const_expr(Info, TMznIntA, MaybeIntConstA, !Specs),
                (
                    MaybeIntConstA = yes(IntConstA),
                    is_int_linear_expr(Info, TMznIntB, LinearExprB, !Specs),
                    LinearExpr = ile_scale(IntConstA, LinearExprB)
                ;
                    MaybeIntConstA = no,
                    is_int_const_expr(Info, TMznIntB, MaybeIntConstB, !Specs),
                    (
                        MaybeIntConstB = yes(IntConstB),
                        is_int_linear_expr(Info, TMznIntA, LinearExprA,
                            !Specs),
                        LinearExpr = ile_scale(IntConstB, LinearExprA)
                    ;
                        MaybeIntConstB = no,
                        % TMznIntB is non-linear.
                        LinearExpr = ile_translate_to_var(TMznIntExpr)
                    )
                )
            ;
                II2IOp = ii2i_div,
                is_int_const_expr(Info, TMznIntB, MaybeIntConstB, !Specs),
                (
                    MaybeIntConstB = yes(IntConstB),
                    ( if IntConstB = 1 then
                        is_int_linear_expr(Info, TMznIntA, LinearExpr, !Specs)
                    else if IntConstB = -1 then
                        is_int_linear_expr(Info, TMznIntA, LinearExprA,
                            !Specs),
                        LinearExpr = ile_scale(-1, LinearExprA)
                    else
                        % We could translate TMznIntExpr into
                        % ile_scale(1/IntConstB, LinearExprA) only if
                        % the coefficients were floats, not ints.
                        LinearExpr = ile_translate_to_var(TMznIntExpr)
                    )
                ;
                    MaybeIntConstB = no,
                    LinearExpr = ile_translate_to_var(TMznIntExpr)
                )
            ;
                ( II2IOp = ii2i_min
                ; II2IOp = ii2i_max
                ; II2IOp = ii2i_mod
                ; II2IOp = ii2i_pow
                ),
                LinearExpr = ile_translate_to_var(TMznIntExpr)
            )
        ;
            ( TMznIntExpr = tmzn_int_expr_var(_SrcPos, _TMznIntVar)
            ; TMznIntExpr = tmzn_int_expr_b2i(_SrcPos, _B2IOp, _BoolExprA)
            ; TMznIntExpr = tmzn_int_expr_is2i(_SrcPos, _IS2IOp, _IntSetExprA)
            ; TMznIntExpr = tmzn_int_expr_ia2i(_SrcPos, _IA2IOp, _IntArrayExprA)
            ; TMznIntExpr = tmzn_int_expr_xs2i(_SrcPos, _XS2IOp, _IntSetExprA)
            ; TMznIntExpr = tmzn_int_expr_ite(_SrcPos, _Cond, _Then, _Else)
            ),
            LinearExpr = ile_translate_to_var(TMznIntExpr)
        )
    ).

%-----------------------------------------------------------------------------%

int_linear_expr_build_coeffs_form(LinearExpr, CoeffsForm) :-
    Scale0 = 1,
    map.init(CoeffsMap0),
    Const0 = 0,
    int_linear_expr_build_coeffs(Scale0, LinearExpr, CoeffsMap0, CoeffsMap,
        Const0, Const),
    map.to_assoc_list(CoeffsMap, CoeffsExprInts),
    assoc_list.reverse_members(CoeffsExprInts, CoeffsIntExprs),
    CoeffsForm = int_coeffs_form(CoeffsIntExprs, Const).

:- pred int_linear_expr_build_coeffs(int::in, int_linear_expr::in,
    map(tmzn_int_expr, int)::in, map(tmzn_int_expr, int)::out,
    int::in, int::out) is det.

int_linear_expr_build_coeffs(Scale, LinearExpr, !CoeffsMap, !Const) :-
    (
        LinearExpr = ile_const(K),
        !:Const = !.Const + K
    ;
        LinearExpr = ile_translate_to_var(TMznIntExpr),
        ( if map.search(!.CoeffsMap, TMznIntExpr, OldCoeff) then
            UpdatedCoeff = OldCoeff + Scale,
            ( if UpdatedCoeff = 0 then
                % We do this so that testing the size of the final CoeffsForm
                % is more meaningful.
                map.delete(TMznIntExpr, !CoeffsMap)
            else
                map.det_update(TMznIntExpr, UpdatedCoeff, !CoeffsMap)
            )
        else
            map.det_insert(TMznIntExpr, Scale, !CoeffsMap)
        )
    ;
        LinearExpr = ile_sum(LinearExprA, LinearExprB),
        int_linear_expr_build_coeffs(Scale, LinearExprA, !CoeffsMap, !Const),
        int_linear_expr_build_coeffs(Scale, LinearExprB, !CoeffsMap, !Const)
    ;
        LinearExpr = ile_scale(K, LinearExprA),
        ( if K = 0 then
            true
        else
            int_linear_expr_build_coeffs(Scale * K, LinearExprA,
                !CoeffsMap, !Const)
        )
    ).

%-----------------------------------------------------------------------------%

is_int_const_expr(Info, TMznIntExpr, MaybeIntConst, !Specs) :-
    (
        TMznIntExpr = tmzn_int_expr_const(_SrcPos, IntConst),
        MaybeIntConst = yes(IntConst)
    ;
        TMznIntExpr = tmzn_int_expr_var(_SrcPos, TMznIntVar),
        tr_info_get_var_info_maps(Info, VarInfoMaps),
        vim_get_int_map(VarInfoMaps, IntMap),
        ( if
            TMznIntVar = tmzn_int_var_named(IntVarName),
            TFznIntVar = tfzn_int_var_named(IntVarName),
            map.search(IntMap, TFznIntVar, IntVarInfo),
            IntVarInfo ^ vii_bounds = int_bounds_range(IntConst, IntConst)
        then
            MaybeIntConst = yes(IntConst)
        else
            MaybeIntConst = no
        )
    ;
        TMznIntExpr = tmzn_int_expr_i2i(_SrcPos, I2IOp, TMznIntA),
        is_int_const_expr(Info, TMznIntA, MaybeIntConstA, !Specs),
        (
            MaybeIntConstA = yes(IntConstA),
            translate_par_int_to_int(I2IOp, IntConstA, IntConst),
            MaybeIntConst = yes(IntConst)
        ;
            MaybeIntConstA = no,
            MaybeIntConst = no
        )
    ;
        TMznIntExpr = tmzn_int_expr_ii2i(SrcPos, II2IOp, TMznIntA, TMznIntB),
        is_int_const_expr(Info, TMznIntA, MaybeIntConstA, !Specs),
        is_int_const_expr(Info, TMznIntB, MaybeIntConstB, !Specs),
        ( if
            MaybeIntConstA = yes(IntConstA),
            MaybeIntConstB = yes(IntConstB)
        then
            translate_par_int_par_int_to_int(SrcPos, II2IOp,
                IntConstA, IntConstB, IntConst, !Specs),
            MaybeIntConst = yes(IntConst)
        else
            MaybeIntConst = no
        )
    ;
        TMznIntExpr = tmzn_int_expr_ite(_SrcPos, Cond, Then, Else),
        is_bool_const_expr(Info, Cond, MaybeCondConst, !Specs),
        (
            MaybeCondConst = yes(CondConst),
            (
                CondConst = yes,
                is_int_const_expr(Info, Then, MaybeThenConst, !Specs),
                MaybeIntConst = MaybeThenConst
            ;
                CondConst = no,
                is_int_const_expr(Info, Else, MaybeElseConst, !Specs),
                MaybeIntConst = MaybeElseConst
            )
        ;
            MaybeCondConst = no,
            MaybeIntConst = no
        )
    ;
        TMznIntExpr = tmzn_int_expr_b2i(_SrcPos, B2IOp, BoolExprA),
        (
            B2IOp = b2i_bool2int,
            is_bool_const_expr(Info, BoolExprA, MaybeBoolConstA, !Specs),
            (
                MaybeBoolConstA = yes(BoolConstA),
                (
                    BoolConstA = no,
                    MaybeIntConst = yes(0)
                ;
                    BoolConstA = yes,
                    MaybeIntConst = yes(1)
                )
            ;
                MaybeBoolConstA = no,
                MaybeIntConst = no
            )
        )
    ;
        ( TMznIntExpr = tmzn_int_expr_is2i(_SrcPos, _IS2IOp, _IntSetExprA)
        ; TMznIntExpr = tmzn_int_expr_ia2i(_SrcPos, _IA2IOp, _IntArrayExprA)
        ; TMznIntExpr = tmzn_int_expr_xs2i(_SrcPos, _XS2IOp, _IntSetExprA)
        ),
        % XXX We should try to figure out whether these are constants.
        MaybeIntConst = no
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred translate_int_expr_to_tfzn_term_std(ilhs::in,
    tmzn_int_expr::in, tfzn_int_term::out, tfzn_constraint_set::out,
    tr_info::in, tr_info::out) is det.

translate_int_expr_to_tfzn_term_std(ILHS, TMznIntExpr, TFznIntTerm,
        Constraints, !Info) :-
    (
        TMznIntExpr = tmzn_int_expr_const(SrcPos, Int),
        % This should have been caught and handled by the optimizer.
        add_internal_error_info($pred, phase_constraint, SrcPos,
            "const not caught by optimizer", !Info),
        TFznIntTerm = tfzn_int_term_const(Int),
        Constraints = no_tfzn_constraints
    ;
        TMznIntExpr = tmzn_int_expr_var(SrcPos, TMznIntVar),
        (
            TMznIntVar = tmzn_int_var_named(IntVarName),
            % XXX Could we optimize this if IntVarName has had its value
            % fixed already, by earlier constraints?
            TFznIntVar = tfzn_int_var_named(IntVarName),
            TFznIntTerm = tfzn_int_term_var(TFznIntVar),
            Constraints = no_tfzn_constraints
        ;
            TMznIntVar = tmzn_int_var_anon,
            % XXX Inst: should we take it from an extended TMznIntExpr?
            % XXX Bounds: should we take it from an extended TMznIntExpr?
            MaybeTmpVarExpr = no,
            TmpVarInfo = var_info_int(var_is_var, var_is_not_output,
                int_bounds_range(int_minus_infinity, int_plus_infinity),
                MaybeTmpVarExpr),
            add_tmp_var_int(TmpVarInfo, TFznIntVar, !Info),
            TFznIntTerm = tfzn_int_term_var(TFznIntVar),
            Constraints = no_tfzn_constraints
        ;
            TMznIntVar = tmzn_int_var_array_slot(TMznIntArrayExpr, IndexExprs),
            translate_int_array_access(ILHS, SrcPos, TMznIntArrayExpr,
                IndexExprs, TFznIntTerm, Constraints, !Info)
        )
    ;
        TMznIntExpr = tmzn_int_expr_b2i(SrcPos, _B2IOp, _BoolExprA),
        add_nyi_error_info($pred, phase_constraint, SrcPos, "b2i", !Info),
        TFznIntTerm = tfzn_int_term_const(0),
        Constraints = no_tfzn_constraints
    ;
        TMznIntExpr = tmzn_int_expr_i2i(SrcPos, I2IOp, TMznIntA),
        % XXX Update SrcPos?
        translate_int_expr_to_tfzn_term(ILHS, TMznIntA, TFznIntA,
            ConstraintsA, !Info),
        translate_int_to_int(ILHS, SrcPos, I2IOp, TFznIntA, TFznIntTerm,
            ConstraintsOp, !Info),
        Constraints = ConstraintsA ++ ConstraintsOp
    ;
        TMznIntExpr = tmzn_int_expr_ii2i(SrcPos, II2IOp, TMznIntA, TMznIntB),
        % XXX Update SrcPos?
        translate_int_expr_to_tfzn_term(ILHS, TMznIntA, TFznIntA,
            ConstraintsA, !Info),
        translate_int_expr_to_tfzn_term(ILHS, TMznIntB, TFznIntB,
            ConstraintsB, !Info),
        translate_int_int_to_int(ILHS, SrcPos, II2IOp,
            TFznIntA, TFznIntB, TFznIntTerm, ConstraintsOp, !Info),
        Constraints = ConstraintsA ++ ConstraintsB ++ ConstraintsOp
    ;
        TMznIntExpr = tmzn_int_expr_is2i(SrcPos, _IS2IOp, _IntSetExprA),
        add_nyi_error_info($pred, phase_constraint, SrcPos, "is2i", !Info),
        TFznIntTerm = tfzn_int_term_const(0),
        Constraints = no_tfzn_constraints
    ;
        TMznIntExpr = tmzn_int_expr_ia2i(SrcPos, _IA2IOp, _IntArrayExprA),
        add_nyi_error_info($pred, phase_constraint, SrcPos, "ia2i", !Info),
        TFznIntTerm = tfzn_int_term_const(0),
        Constraints = no_tfzn_constraints
    ;
        TMznIntExpr = tmzn_int_expr_xs2i(SrcPos, _XS2IOp, _IntSetExprA),
        add_nyi_error_info($pred, phase_constraint, SrcPos, "xs2i", !Info),
        TFznIntTerm = tfzn_int_term_const(0),
        Constraints = no_tfzn_constraints
    ;
        TMznIntExpr = tmzn_int_expr_ite(SrcPos, _BoolCondExpr,
            _IntThenExpr, _IntElseExpr),
        add_nyi_error_info($pred, phase_constraint, SrcPos, "ite", !Info),
        TFznIntTerm = tfzn_int_term_const(0),
        Constraints = no_tfzn_constraints
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred translate_int_to_int(ilhs::in, src_pos::in, int_to_int_op::in,
    tfzn_int_term::in, tfzn_int_term::out, tfzn_constraint_set::out,
    tr_info::in, tr_info::out) is det.

translate_int_to_int(ILHS, SrcPos, I2IOp, A, Z, Constraints, !Info) :-
    (
        A = tfzn_int_term_const(IntA),
        add_internal_error_info($pred, phase_constraint, SrcPos,
            "const not caught by optimizer", !Info),
        translate_par_int_to_int(I2IOp, IntA, IntZ),
        Z = tfzn_int_term_const(IntZ),
        Constraints = no_tfzn_constraints
    ;
        A = tfzn_int_term_var(IntVarA),
        translate_var_int_to_int(ILHS, SrcPos, I2IOp, IntVarA, Z,
            Constraints, !Info)
    ).

:- pred translate_par_int_to_int(int_to_int_op::in, int::in, int::out) is det.

translate_par_int_to_int(I2IOp, IntA, IntZ) :-
    ( I2IOp = i2i_add,      IntZ = IntA
    ; I2IOp = i2i_sub,      IntZ = -IntA
    ; I2IOp = i2i_abs,      IntZ = int.abs(IntA)
    ; I2IOp = i2i_lb,       IntZ = IntA
    ; I2IOp = i2i_ub,       IntZ = IntA
    ; I2IOp = i2i_dom_size, IntZ = 1
    ; I2IOp = i2i_fix,      IntZ = IntA
    ).

:- pred translate_var_int_to_int(ilhs::in, src_pos::in,
    int_to_int_op::in, tfzn_int_var::in, tfzn_int_term::out,
    tfzn_constraint_set::out, tr_info::in, tr_info::out) is det.

translate_var_int_to_int(ILHS, SrcPos, I2IOp, IntVarA, Z, Constraints,
        !Info) :-
    (
        I2IOp = i2i_add,
        Z = tfzn_int_term_var(IntVarA),
        Constraints = no_tfzn_constraints
    ;
        I2IOp = i2i_sub,
        % XXX We could see whether we already have a constraint like this.
        tr_info_get_cse_maps(!.Info, CSEMaps0),
        get_cse_map_i2i(CSEMaps0, I2IMap0),
        A = tfzn_int_term_var(IntVarA),
        ( if map.search(I2IMap0, {int_negate, A}, CSEResult) then
            % XXX Can we tighten the bounds on IntVarZ?
            CSEResult = {IntVarZ, ConstraintItem},
            Z = tfzn_int_term_var(IntVarZ)
        else
            int_bounds_range(LBA, UBA) = find_int_var_bounds(!.Info, IntVarA),
            % XXX SrcPos
            int_times_bounds([], -1, -1, LBA, UBA, LBZ, UBZ),
            IntBoundsZ = int_bounds_range(LBZ, UBZ),
            % XXX If we have IntExprA, can we use it to set MaybeIntExprZ?
            MaybeIntExprZ = no,
            IntVarInfoZ = var_info_int(var_is_var, var_is_not_output,
                IntBoundsZ, MaybeIntExprZ),
            add_tmp_var_int(IntVarInfoZ, IntVarZ, !Info),
            Z = tfzn_int_term_var(IntVarZ),

            % XXX Should we make the constraint half-reified if ILHS is
            % ilhs_var(BoolVar)? (If we do, we cannot add to CSEMaps0.)
            % If BoolVar = false, then we may not have to compute Z,
            % but testing BoolVar can be more expensive than computing Z.
            Constraint = tfzn_constr_int_arith_unop(int_negate, A, Z),
            Ann = constr_ann_defines_var(tfzn_def_int_var(IntVarZ)),
            Anns = set.make_singleton_set(Ann),
            ConstraintItem = tfzn_item_constraint(Constraint, Anns),

            map.det_insert({int_negate, A}, {IntVarZ, ConstraintItem},
                I2IMap0, I2IMap),
            set_cse_map_i2i(I2IMap, CSEMaps0, CSEMaps),
            tr_info_set_cse_maps(CSEMaps, !Info)
        ),
        Constraints = one_tfzn_constraint(ConstraintItem)
    ;
        I2IOp = i2i_abs,
        int_bounds_range(LBA, UBA) = find_int_var_bounds(!.Info, IntVarA),
        ( if LBA < 0, 0 < UBA then
            % A may be negative, zero or positive.
            tr_info_get_cse_maps(!.Info, CSEMaps0),
            get_cse_map_i2i(CSEMaps0, I2IMap0),
            A = tfzn_int_term_var(IntVarA),
            ( if map.search(I2IMap0, {int_abs, A}, CSEResult) then
                % XXX Can we tighten the bounds on IntVarZ?
                CSEResult = {IntVarZ, ConstraintItem},
                Z = tfzn_int_term_var(IntVarZ)
            else
                LBZ = 0,
                ( if
                    ( LBA = int_minus_infinity ; UBA = int_plus_infinity )
                then
                    UBZ = int_plus_infinity
                else
                    UBZ = int.max(-LBA, UBA)
                ),
                IntBoundsZ = int_bounds_range(LBZ, UBZ),
                % XXX If we have IntExprA, can we use it to set MaybeIntExprZ?
                MaybeIntExprZ = no,
                IntVarInfoZ = var_info_int(var_is_var, var_is_not_output,
                    IntBoundsZ, MaybeIntExprZ),
                add_tmp_var_int(IntVarInfoZ, IntVarZ, !Info),
                Z = tfzn_int_term_var(IntVarZ),

                % XXX Should we make the constraint half-reified if ILHS is
                % ilhs_var(BoolVar)? (If we do, we cannot add to CSEMaps0.)
                % If BoolVar = false, then we may not have to compute Z,
                % but testing BoolVar can be more expensive than computing Z.
                Constraint = tfzn_constr_int_arith_unop(int_abs, A, Z),
                Ann = constr_ann_defines_var(tfzn_def_int_var(IntVarZ)),
                Anns = set.make_singleton_set(Ann),
                ConstraintItem = tfzn_item_constraint(Constraint, Anns),

                map.det_insert({int_abs, A}, {IntVarZ, ConstraintItem},
                    I2IMap0, I2IMap),
                set_cse_map_i2i(I2IMap, CSEMaps0, CSEMaps),
                tr_info_set_cse_maps(CSEMaps, !Info)
            ),
            Constraints = one_tfzn_constraint(ConstraintItem)
        else if UBA < 0 then
            % A may only be negative.
            % Instead of computing the absolute value, compute the negation.
            translate_var_int_to_int(ILHS, SrcPos, i2i_sub,
                IntVarA, Z, Constraints, !Info)
        else
            % A may only be zero or positive.
            % There is no need for the absolute value operation: it would
            % always return its operand.
            Z = tfzn_int_term_var(IntVarA),
            Constraints = no_tfzn_constraints
        )
    ;
        I2IOp = i2i_lb,
        int_bounds_range(LBA, _UBA) = find_int_var_bounds(!.Info, IntVarA),
        ( if LBA = int_minus_infinity then
            add_user_error_info($pred, phase_constraint, SrcPos,
                "cannot infer lower bound", !Info),
            Z = tfzn_int_term_const(0),
            Constraints = no_tfzn_constraints
        else
            Z = tfzn_int_term_const(LBA),
            Constraints = no_tfzn_constraints
        )
    ;
        I2IOp = i2i_ub,
        int_bounds_range(_LBA, UBA) = find_int_var_bounds(!.Info, IntVarA),
        ( if UBA = int_plus_infinity then
            add_user_error_info($pred, phase_constraint, SrcPos,
                "cannot infer upper bound", !Info),
            Z = tfzn_int_term_const(0),
            Constraints = no_tfzn_constraints
        else
            Z = tfzn_int_term_const(UBA),
            Constraints = no_tfzn_constraints
        )
    ;
        I2IOp = i2i_dom_size,
        int_bounds_range(LBA, UBA) = find_int_var_bounds(!.Info, IntVarA),
        ( if ( LBA = int_minus_infinity ; UBA = int_plus_infinity ) then
            add_user_error_info($pred, phase_constraint, SrcPos,
                "cannot infer domain size", !Info),
            Z = tfzn_int_term_const(0),
            Constraints = no_tfzn_constraints
        else
            DomSize0 = UBA - LBA + 1,
            DomSize = ( if DomSize0 < 0 then 0 else DomSize0 ),
            Z = tfzn_int_term_const(DomSize),
            Constraints = no_tfzn_constraints
        )
    ;
        I2IOp = i2i_fix,
        add_nyi_error_info($pred, phase_constraint, SrcPos, "i2i_fix", !Info),
        Z = tfzn_int_term_const(0),
        Constraints = no_tfzn_constraints
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred translate_int_int_to_int(ilhs::in, src_pos::in, int_int_to_int_op::in,
    tfzn_int_term::in, tfzn_int_term::in, tfzn_int_term::out,
    tfzn_constraint_set::out, tr_info::in, tr_info::out) is det.

translate_int_int_to_int(ILHS, SrcPos, II2IOp, A, B, Z, Constraints, !Info) :-
    (
        A = tfzn_int_term_const(IntA),
        B = tfzn_int_term_const(IntB),
        % XXX This case should have been handled by the optimization step.
        translate_par_int_par_int_to_int(SrcPos, II2IOp, IntA, IntB, IntZ,
            [], Specs),
        add_errors(Specs, !Info),
        Z = tfzn_int_term_const(IntZ),
        Constraints = no_tfzn_constraints
    ;
        A = tfzn_int_term_const(IntA),
        B = tfzn_int_term_var(IntVarB),
        translate_par_int_var_int_to_int(ILHS, SrcPos, II2IOp,
            IntA, IntVarB, Z, Constraints, !Info)
    ;
        A = tfzn_int_term_var(IntVarA),
        B = tfzn_int_term_const(IntB),
        translate_var_int_par_int_to_int(ILHS, SrcPos, II2IOp,
            IntVarA, IntB, Z, Constraints, !Info)
    ;
        A = tfzn_int_term_var(_IntVarA),
        B = tfzn_int_term_var(_IntVarB),
        translate_var_int_var_int_to_int(ILHS, SrcPos, II2IOp, A, B, Z,
            Constraints, !Info)
    ).

:- pred translate_par_int_par_int_to_int(src_pos::in, int_int_to_int_op::in,
    int::in, int::in, int::out, list(error_spec)::in, list(error_spec)::out)
    is det.

translate_par_int_par_int_to_int(SrcPos, II2IOp, IntA, IntB, IntZ, !Specs) :-
    (
        ( II2IOp = ii2i_add,      IntZ = IntA + IntB
        ; II2IOp = ii2i_sub,      IntZ = IntA - IntB
        ; II2IOp = ii2i_mul,      IntZ = IntA * IntB
        ; II2IOp = ii2i_min,      IntZ = int.min(IntA, IntB)
        ; II2IOp = ii2i_max,      IntZ = int.max(IntA, IntB)
        )
    ;
        II2IOp = ii2i_div,
        ( if IntB = 0 then
            add_user_error($pred, phase_constraint, SrcPos,
                "division by zero", !Specs),
            IntZ = 0
        else
            IntZ = IntA / IntB
        )
    ;
        II2IOp = ii2i_mod,
        ( if IntB = 0 then
            add_user_error($pred, phase_constraint, SrcPos,
                "division by zero", !Specs),
            IntZ = 0
        else
            IntZ = IntA mod IntB
        )
    ;
        II2IOp = ii2i_pow,
        ( if IntB < 0 then
            add_user_error($pred, phase_constraint, SrcPos,
                "cannot raise integer to a negative power", !Specs),
            IntZ = 0
        else
            IntZ = int.pow(IntA, IntB)
        )
    ).

:- pred translate_par_int_var_int_to_int(ilhs::in, src_pos::in,
    int_int_to_int_op::in, int::in, tfzn_int_var::in,
    tfzn_int_term::out, tfzn_constraint_set::out,
    tr_info::in, tr_info::out) is det.

translate_par_int_var_int_to_int(ILHS, SrcPos, II2IOp, IntA, IntVarB, Z,
        Constraints, !Info) :-
    (
        II2IOp = ii2i_mul,
        ( if IntA = 0 then
            Z = tfzn_int_term_const(0),
            Constraints = no_tfzn_constraints
        else if IntA = 1 then
            Z = tfzn_int_term_var(IntVarB),
            Constraints = no_tfzn_constraints
        else
            A = tfzn_int_term_const(IntA),
            B = tfzn_int_term_var(IntVarB),
            translate_var_int_var_int_to_int(ILHS, SrcPos, II2IOp, A, B, Z,
                Constraints, !Info)
        )
    ;
        ( II2IOp = ii2i_add
        ; II2IOp = ii2i_sub
        ; II2IOp = ii2i_min
        ; II2IOp = ii2i_max
        ; II2IOp = ii2i_div
        ; II2IOp = ii2i_mod
        ; II2IOp = ii2i_pow
        ),
        A = tfzn_int_term_const(IntA),
        B = tfzn_int_term_var(IntVarB),
        translate_var_int_var_int_to_int(ILHS, SrcPos, II2IOp, A, B, Z,
            Constraints, !Info)
    ).

:- pred translate_var_int_par_int_to_int(ilhs::in, src_pos::in,
    int_int_to_int_op::in, tfzn_int_var::in, int::in,
    tfzn_int_term::out, tfzn_constraint_set::out,
    tr_info::in, tr_info::out) is det.

translate_var_int_par_int_to_int(ILHS, SrcPos, II2IOp, IntVarA, IntB, Z,
        Constraints, !Info) :-
    (
        II2IOp = ii2i_mul,
        ( if IntB = 0 then
            Z = tfzn_int_term_const(0),
            Constraints = no_tfzn_constraints
        else if IntB = 1 then
            Z = tfzn_int_term_var(IntVarA),
            Constraints = no_tfzn_constraints
        else
            A = tfzn_int_term_var(IntVarA),
            B = tfzn_int_term_const(IntB),
            translate_var_int_var_int_to_int(ILHS, SrcPos, II2IOp, A, B, Z,
                Constraints, !Info)
        )
    ;
        ( II2IOp = ii2i_add
        ; II2IOp = ii2i_sub
        ; II2IOp = ii2i_min
        ; II2IOp = ii2i_max
        ; II2IOp = ii2i_div
        ; II2IOp = ii2i_mod
        ; II2IOp = ii2i_pow
        ),
        A = tfzn_int_term_var(IntVarA),
        B = tfzn_int_term_const(IntB),
        translate_var_int_var_int_to_int(ILHS, SrcPos, II2IOp, A, B, Z,
            Constraints, !Info)
    ).

:- pred translate_var_int_var_int_to_int(ilhs::in, src_pos::in,
    int_int_to_int_op::in, tfzn_int_term::in, tfzn_int_term::in,
    tfzn_int_term::out, tfzn_constraint_set::out,
    tr_info::in, tr_info::out) is det.

translate_var_int_var_int_to_int(_ILHS, SrcPos, II2IOp, A, B, Z, Constraints,
        !Info) :-
    (
        ( II2IOp = ii2i_add, TFznOp = int_plus
        ; II2IOp = ii2i_sub, TFznOp = int_minus
        ; II2IOp = ii2i_mul, TFznOp = int_times
        ; II2IOp = ii2i_min, TFznOp = int_min
        ; II2IOp = ii2i_max, TFznOp = int_max
        ),
        tr_info_get_cse_maps(!.Info, CSEMaps0),
        get_cse_map_ii2i(CSEMaps0, II2IMap0),
        ( if map.search(II2IMap0, {TFznOp, A, B}, CSEResult) then
            % XXX Can we tighten the bounds on IntVarZ?
            CSEResult = {IntVarZ, ConstraintItem},
            Z = tfzn_int_term_var(IntVarZ)
        else
            int_bounds_range(LBA, UBA) = find_int_term_bounds(!.Info, A),
            int_bounds_range(LBB, UBB) = find_int_term_bounds(!.Info, B),
            (
                II2IOp = ii2i_add,
                int_plus_bounds_specs(SrcPos, LBA, UBA, LBB, UBB, LBZ, UBZ,
                    Specs),
                add_errors(Specs, !Info)
            ;
                II2IOp = ii2i_sub,
                int_times_bounds_specs(SrcPos, -1, -1, LBB, UBB, LBMB, UBMB,
                    SpecsA),
                int_plus_bounds_specs(SrcPos, LBA, UBA, LBMB, UBMB, LBZ, UBZ,
                    SpecsB),
                add_errors(SpecsA, !Info),
                add_errors(SpecsB, !Info)
            ;
                II2IOp = ii2i_mul,
                int_times_bounds_specs(SrcPos, LBA, UBA, LBB, UBB, LBZ, UBZ,
                    Specs),
                add_errors(Specs, !Info)
            ;
                II2IOp = ii2i_min,
                int_min_bounds(LBA, UBA, LBB, UBB, LBZ, UBZ)
            ;
                II2IOp = ii2i_max,
                int_max_bounds(LBA, UBA, LBB, UBB, LBZ, UBZ)
            ),
            IntBoundsZ = int_bounds_range(LBZ, UBZ),
            % XXX If we have IntExprA and IntExprB, can we use them
            % to set MaybeIntExprZ?
            MaybeIntExprZ = no,
            IntVarInfoZ = var_info_int(var_is_var, var_is_not_output,
                IntBoundsZ, MaybeIntExprZ),
            add_tmp_var_int(IntVarInfoZ, IntVarZ, !Info),

            % XXX Should we make the constraint half-reified if ILHS is
            % ilhs_var(BoolVar)? (If we do, we cannot add to CSEMaps0.)
            % If BoolVar = false, then we may not have to compute Z,
            % but testing BoolVar can be more expensive than computing Z.
            Z = tfzn_int_term_var(IntVarZ),
            Constraint = tfzn_constr_int_arith_binop(TFznOp, A, B, Z),
            Ann = constr_ann_defines_var(tfzn_def_int_var(IntVarZ)),
            Anns = set.make_singleton_set(Ann),
            ConstraintItem = tfzn_item_constraint(Constraint, Anns),

            map.det_insert({TFznOp, A, B}, {IntVarZ, ConstraintItem},
                II2IMap0, II2IMap),
            set_cse_map_ii2i(II2IMap, CSEMaps0, CSEMaps),
            tr_info_set_cse_maps(CSEMaps, !Info)
        ),
        Constraints = one_tfzn_constraint(ConstraintItem)
    ;
        II2IOp = ii2i_div,
        add_nyi_error_info($pred, phase_constraint, SrcPos, "ii2i_div", !Info),
        Z = tfzn_int_term_const(0),
        Constraints = no_tfzn_constraints
    ;
        II2IOp = ii2i_mod,
        add_nyi_error_info($pred, phase_constraint, SrcPos, "ii2i_mod", !Info),
        Z = tfzn_int_term_const(0),
        Constraints = no_tfzn_constraints
    ;
        II2IOp = ii2i_pow,
        add_nyi_error_info($pred, phase_constraint, SrcPos, "ii2i_pow", !Info),
        Z = tfzn_int_term_const(0),
        Constraints = no_tfzn_constraints
    ).

%-----------------------------------------------------------------------------%

int_plus_bounds_specs(SrcPos, LBA, UBA, LBB, UBB, LB, UB, Specs) :-
    int_bounded_plus_specs(SrcPos, LBA, LBB, LB, SpecsLB),
    int_bounded_plus_specs(SrcPos, UBA, UBB, UB, SpecsUB),
    Specs = SpecsLB ++ SpecsUB.

int_times_bounds_specs(SrcPos, LBA, UBA, LBB, UBB, LB, UB, Specs) :-
    int_bounded_times_specs(SrcPos, LBA, LBB, Xa, SpecsA),
    int_bounded_times_specs(SrcPos, LBA, UBB, Xb, SpecsB),
    int_bounded_times_specs(SrcPos, UBA, LBB, Xc, SpecsC),
    int_bounded_times_specs(SrcPos, UBA, UBB, Xd, SpecsD),
    LB = int.min(Xa, int.min(Xb, int.min(Xc, Xd))),
    UB = int.max(Xa, int.max(Xb, int.max(Xc, Xd))),
    Specs = SpecsA ++ SpecsB ++ SpecsC ++ SpecsD.

int_bounded_plus_specs(SrcPos, X, Y, Z, Specs) :-
    MaybeZ = int_bounded_plus_maybe(X, Y),
    (
        MaybeZ = yes(Z),
        Specs = []
    ;
        MaybeZ = no,
        make_overflow_error($pred, phase_constraint, SrcPos, Spec),
        Specs = [Spec],
        Z = 1       % dummy
    ).

int_bounded_times_specs(SrcPos, X, Y, Z, Specs) :-
    MaybeZ = int_bounded_times_maybe(X, Y),
    (
        MaybeZ = yes(Z),
        Specs = []
    ;
        MaybeZ = no,
        make_overflow_error($pred, phase_constraint, SrcPos, Spec),
        Specs = [Spec],
        Z = 1       % dummy
    ).

%-----------------------------------------------------------------------------%
:- end_module translate.int.
%-----------------------------------------------------------------------------%
