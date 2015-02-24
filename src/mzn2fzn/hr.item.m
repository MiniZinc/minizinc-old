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

:- module hr.item.
:- interface.

:- import_module hr.info.
:- import_module types.

:- import_module zinc_ast.

    % If an item is a predfunc_item then process it.
    %
:- pred hr_process_predfunc_item(item::in, model::in, model::out)
    is det.

    % If an item is a var_decl_item then process it.
    %
:- pred hr_process_var_decl_item(item::in, hr_info::in, hr_info::out,
    model::in, model::out) is det.

    % If an item is a constraint_item then process it.
    %
:- pred hr_process_constraint_item(item::in, hr_info::in, hr_info::out,
    model::in, model::out) is det.

    % If an item is the output_item then process it.
    %
    % FlatZinc has no output items, even though MiniZinc does. A MiniZinc
    % interpreter can produce output by evaluating the output item.
    % A FlatZinc interpreter, however, can only output the variables that
    % appear in the MiniZinc output item. This predicate identifies those
    % variables and marks them as output. (NB: annotations on expressions
    % are ignored.)
    %
:- pred hr_process_output_item(item::in, hr_info::in, hr_info::out,
    model::in, model::out) is det.

    % If an item is the solve_item then update the environment.
    %
:- pred hr_process_solve_item(sast_solve_item::in,
    hr_info::in, hr_info::out, model::in, model::out) is det.

%-----------------------------------------------------------------------------%

:- implementation.

:- import_module errors.
:- import_module global_vars.
:- import_module hr.convert.
:- import_module hr.expr.
:- import_module hr.int.
:- import_module utilities.

:- import_module zinc_common.

:- import_module bool.
:- import_module list.
:- import_module map.
:- import_module maybe.
:- import_module set.

%-----------------------------------------------------------------------------%

hr_process_predfunc_item(Item, !Model) :-
    Item = item(RawItem, _SrcLocn),
    ( if
        RawItem = predfunc_item(_Ret, PredName, ProcNum, Params,
            AnnExprs, MaybeBodyExpr)
      then
        PredProcId = pred_proc_id(PredName, ProcNum),
        PredInfo = predicate_info(Params, AnnExprs, MaybeBodyExpr),
        model_add_predicate_info(PredProcId, PredInfo, !Model)
      else
        true
    ).

%-----------------------------------------------------------------------------%

hr_process_var_decl_item(Item, !Info, !Model) :-
    Item = item(RawItem, SrcLocn),
    ( if
        RawItem = var_decl_item(TIExpr, VarName, VarAnnExprs, MaybeValueExpr)
    then
        VarId = id_global(VarName),
        Context = [["In variable declaration for '", VarName, "'.\n"] |
            init_context(SrcLocn)],
        hr_flatten_ti_expr(Context, no_anns, ilhs_true, TIExpr,
            VarPar, MZType, IndexRanges, !Info, !Model),
        hr_flatten_anns(Context, no_anns, ilhs_true, VarAnnExprs, Anns,
            !Info, !Model),
        ( if VarPar = var then
            hr_add_global_permanent_var(VarId, MZType, IndexRanges, Anns,
                ConstraintsToAdd, !Model),
            list.map_foldl2(hr_add_constraint_to_add(no_anns, ilhs_true),
                ConstraintsToAdd, _AllConstraints, !Info, !Model)
        else
            hr_add_global_par(VarId, MZType, IndexRanges, !Model)
        ),
        (
            ( MaybeValueExpr = rhs_assignment(ValueExpr)
            ; MaybeValueExpr = separate_assignment(_, ValueExpr)
            ),
            % We treat assignment as a constraint because we want to do
            % bounds checking on the value.
            ( if
                % If this is a var bool or array of var bool then we want to
                % reify the value (e.g., we don't want to do any assignments
                % when processing, say, x = [y = 1, y = 2, y = 3]).
                ( if
                    VarPar = var,
                    ( MZType = mzn_bool
                    ; MZType = mzn_bool_array
                    )
                then
                    hr_flatten_expr_must_reify(Context, no_anns,
                        ValueExpr, MZValue, _FlattenConstraints, !Info, !Model)
                else
                    hr_flatten_expr(Context, no_anns, ilhs_true,
                        ValueExpr, MZValue, _FlattenConstraints, !Info, !Model)
                ),
                GlobalVarMap0 = !.Model ^ model_globals,
                map.lookup(GlobalVarMap0, VarId, VarInfo0),
                MaybeVarValue0 = VarInfo0 ^ vi_value,
                (
                    MaybeVarValue0 = yes(ExistingMZValue),
                    hr_flatten_builtin(Context, no_anns, ilhs_true,
                        "=", [ExistingMZValue, MZValue], MZ,
                        _BuiltinConstraints, !Info, !Model)
                ;
                    MaybeVarValue0 = no,
                    % Handle strings and annotations specially.
                    ( if
                        ( MZValue = mzn_expr(string_expr(_), _)
                        ; MZValue = mzn_expr(string_array_expr(_), _)
                        ; MZValue = mzn_expr(ann_expr(_), _)
                        ; MZValue = mzn_expr(ann_array_expr(_), _)
                        )
                    then
                        VarInfo = VarInfo0 ^ vi_value := yes(MZValue),
                        map.det_update(VarId, VarInfo,
                            GlobalVarMap0, GlobalVarMap),
                        !Model ^ model_globals := GlobalVarMap,
                        MZ = bool_to_mzn_expr(bool_const(yes))
                    else
                        MZVarExpr = make_var_mzn_expr(IndexRanges, MZType,
                            VarId),
                        % XXX halfreify_builtin ... ilhs_true
                        hr_flatten_builtin(Context, no_anns, ilhs_true,
                            "=", [MZVarExpr, MZValue], MZ,
                            _BuiltinConstraints, !Info, !Model)
                    )
                ),
                MZ = mzn_expr(bool_expr(bool_const(yes)), _)
            then
                true
            else
                value_out_of_range(Context)
            )
        ;
            MaybeValueExpr = no_assignment
        )
    else if
        RawItem = assign_item(VarName, AssignedExpr)
    then
        VarId = id_global(VarName),
        Context =
            [["In assignment for '", VarName, "'.\n"] | init_context(SrcLocn)],
        GlobalVarMap0 = !.Model ^ model_globals,
        map.lookup(GlobalVarMap0, VarId, VarInfo0),
        MaybeVarValue0 = VarInfo0 ^ vi_value,
        (
            MaybeVarValue0 = yes(_),
            % We clearly have multiple assignments for the same variable, which
            % is an error.
            minizinc_user_error(Context,
                "A variable cannot have more than one assignment.\n")
        ;
            MaybeVarValue0 = no,
            ( if
                % We treat assignment as a constraint because we want to do
                % bounds checking on the value.
                IndexRanges = VarInfo0 ^ vi_index_ranges,
                MZType = var_get_updated_var_type(VarInfo0),
                % XXX we could use _TermKnownFalse
                halfreify_term(Context, no_anns, ilhs_true,
                    AssignedExpr, MZValue, _TermConstraints, _TermKnownFalse,
                    !Info, !Model),
                ( if
                    % Handle strings specially.
                    ( MZType = mzn_string
                    ; MZType = mzn_string_array
                    )
                then
                    VarInfo = VarInfo0 ^ vi_value := yes(MZValue),
                    map.det_update(VarId, VarInfo,
                        GlobalVarMap0, GlobalVarMap),
                    !Model ^ model_globals := GlobalVarMap
                else
                    MZVar = make_var_mzn_expr(IndexRanges, MZType, VarId),
                    hr_flatten_builtin(Context, no_anns, ilhs_true,
                        "=", [MZVar, MZValue], MZ,
                        _BuiltinConstraints, !Info, !Model),
                    MZ = mzn_expr(bool_expr(bool_const(yes)), _)
                )
            then
                true
            else
                value_out_of_range(Context)
            )
        )
    else
        true
    ).

%-----------------------------------------------------------------------------%

hr_process_constraint_item(_Item, !Info, !Model).
%   Item = item(RawItem, SrcLocn),
%   ( if
%       RawItem = constraint_item(Expr)
%     then
%       Context = [["In constraint.\n"] | init_context(SrcLocn)],
%       % Optimisation: at the top-level we can process all arguments of
%       % a non-logical operator in a non-reifying context. This saves a whole
%       % pile of temporary bool variable creation (all of which must turn out
%       % to be true!). We can't process boolean operators this way: consider
%       % the constraint x1 = x2 /\ x3 -- in this case our optimisation
%       % would work incorrectly.
%       InconsistencyMsg = "Model inconsistency detected.\n",
%       ( if
%           Expr = expr(RawExpr, AnnExprs, _ExprInfo),
%           RawExpr = app(AppId, _AppProcNo, _AppKind, AppArgExprs),
%           AppArgExprs = [ArgExprA, ArgExprB],
%           ArgExprA ^ expr_info ^ expr_type_inst \= ti_var_bool,
%           ArgExprB ^ expr_info ^ expr_type_inst \= ti_var_bool,
%           Op = id_name(AppId),
%           Arity = 2,
%           is_builtin_op(Op, Arity, _, _)
%         then
%           flatten_anns(Context, AnnExprs, Anns, !Env),
%           !Env ^ anns := Anns,
%           flatten_expr(Context, ArgExprA, ArgMZA, !Env),
%           flatten_expr(Context, ArgExprB, ArgMZB, !Env),
%           ( if
%               flatten_builtin(Context, Op, [ArgMZA, ArgMZB], MZ, !Env),
%               Z = mzn_expr_to_bool(Context, MZ)
%             then
%               impose_constraint(Context, InconsistencyMsg, Z, !Env)
%             else
%               model_inconsistency_detected(Context, InconsistencyMsg)
%           )
%         else
%           flatten_expr(Context, Expr, MZ, !Env),
%           Z = mzn_expr_to_bool(Context, MZ),
%           impose_constraint(Context, InconsistencyMsg, Z, !Env)
%       ),
%       !Env ^ anns := no_anns
%     else
%       true
%   ).

%-----------------------------------------------------------------------------%

hr_process_output_item(Item, !Info, !Model) :-
    Item = item(RawItem, _SrcLocn),
    ( if
        RawItem = output_item(OutputExpr)
      then
        OutputExprVars = global_vars_in_output_expr(!.Model, OutputExpr),
        GlobalVarMap0 = !.Model ^ model_globals,
        set.fold(mark_var_for_output, OutputExprVars,
            GlobalVarMap0, GlobalVarMap),
        !Model ^ model_globals := GlobalVarMap
      else
        minizinc_user_error([], "output item isn't.\n")
    ).

%-----------------------------------------------------------------------------%

hr_process_solve_item(Item, !Info, !Model) :-
    Item = sast_solve_item(SolveKind, AnnExprs, SrcLocn),
    Context = [["In solve item.\n"] | init_context(SrcLocn)],
    hr_flatten_anns(Context, no_anns, ilhs_true, AnnExprs, Anns,
        !Info, !Model),
    % XXX we could use _KnownFalse
    (
        SolveKind = satisfy,
        MZSolveKind = mzn_solve_satisfy
    ;
        SolveKind = minimize(ObjFnExpr),
        halfreify_term(Context, no_anns, ilhs_true, ObjFnExpr, MZObjFn0,
            _ExprConstraints, _KnownFalse, !Info, !Model),
        hr_maybe_simplify_objective_func(Context,
            MZObjFn0, MZObjFn, _ObjFuncConstraints, !Info, !Model),
        MZSolveKind = mzn_solve_minimize(MZObjFn)
    ;
        SolveKind = maximize(ObjFnExpr),
        halfreify_term(Context, no_anns, ilhs_true, ObjFnExpr, MZObjFn0,
            _ExprConstraints, _KnownFalse, !Info, !Model),
        hr_maybe_simplify_objective_func(Context,
            MZObjFn0, MZObjFn, _ObjFuncConstraints, !Info, !Model),
        MZSolveKind = mzn_solve_maximize(MZObjFn)
    ),
    OldSolveGoal = !.Model ^ model_solve_goal,
    (
        OldSolveGoal = no,
        NewSolveGoal = mzn_solve_goal(Anns, MZSolveKind),
        !Model ^ model_solve_goal := yes(NewSolveGoal)
    ;
        OldSolveGoal = yes(_),
        minizinc_user_error([], "Models cannot have multiple solve items.\n")
    ).

:- pred hr_maybe_simplify_objective_func(error_context::in,
    mzn_expr::in, mzn_expr::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

hr_maybe_simplify_objective_func(Context, MZObjFn0, MZObjFn, AllConstraints,
        !Info, !Model) :-
    ( if
        (
            MZObjFn0 = mzn_expr(bool_expr(A), ObjFnAnns),
            hr_simplify_bool_cv(Context, no_anns, ilhs_true, A, CVZ,
                Constraints, !Info, !Model),
            Z = bool_const_or_var_to_expr(CVZ),
            MZObjFn1 = mzn_expr(bool_expr(Z), ObjFnAnns)
        ;
            MZObjFn0 = mzn_expr(float_expr(A), ObjFnAnns),
            hr_simplify_float(Context, no_anns, ilhs_true, A, Z,
                Constraints, !Info, !Model),
            MZObjFn1 = mzn_expr(float_expr(Z), ObjFnAnns)
        ;
            MZObjFn0 = mzn_expr(int_expr(A), ObjFnAnns),
            hr_simplify_int(Context, no_anns, ilhs_true, A, Z,
                Constraints, !Info, !Model),
            MZObjFn1 = mzn_expr(int_expr(Z), ObjFnAnns)
        )
    then
        MZObjFn = MZObjFn1,
        AllConstraints = Constraints
    else
        MZObjFn = MZObjFn0,
        mzn_constraint_set_empty(AllConstraints)
    ).

%-----------------------------------------------------------------------------%
:- end_module hr.item.
%-----------------------------------------------------------------------------%
