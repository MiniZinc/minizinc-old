%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Authors:
% Nicholas Nethercote   <njn@csse.unimelb.edu.au>
% Ralph Becket          <rafe@csse.unimelb.edua.u>
% Julien Fischer        <juliensf@csse.unimelb.edu.au>
%
% Process MiniZinc specification items.
%
%-----------------------------------------------------------------------------%

:- module flatten.item.
:- interface.

:- import_module flatten.env.

:- import_module zinc_ast.

    % If an item is a predfunc_item then update the environment.
    %
:- pred flatten_process_predfunc_item(item::in, env::in, env::out) is det.

    % If an item is a var_decl_item then update the environment.
    %
:- pred flatten_process_var_decl_item(item::in, env::in, env::out) is det.

    % If an item is a constraint_item then update the environment.
    %
:- pred flatten_process_constraint_item(item::in, env::in, env::out) is det.

    % If an item is the output_item then update the environment.
    %
    % FlatZinc has no output items, even though MiniZinc does. A MiniZinc
    % interpreter can produce output by evaluating the output item.
    % A FlatZinc interpreter, however, can only output the variables that
    % appear in the MiniZinc output item. This predicate identifies those
    % variables and marks them for output. (NB: annotations on expressions
    % are ignored.)
    %
:- pred flatten_process_output_item(item::in, env::in, env::out) is det.

    % If an item is the solve_item then update the environment.
    %
:- pred flatten_process_solve_item(sast_solve_item::in, env::in, env::out)
    is det.

    % Ensure we don't try to optimise a constant objective.
    % MiniZinc supports constant objectives, but FlatZinc does not.
    % If the current objective is constant, introduce a new variable
    % of the appropriate type, assign it to the constant and "optimise" that.
    %
:- pred flatten_finalise_solve_item(env::in, env::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module errors.
:- import_module flatten.ann.
:- import_module flatten.bool.
:- import_module flatten.expr.
:- import_module flatten.float.
:- import_module flatten.int.
:- import_module mzn_ops.
:- import_module types.
:- import_module utilities.

:- import_module types_and_insts.
:- import_module zinc_common.
:- import_module compiler_common.

:- import_module bool.
:- import_module list.
:- import_module maybe.
:- import_module require.
:- import_module set.
:- import_module string.

%-----------------------------------------------------------------------------%

flatten_process_predfunc_item(Item, !Env) :-
    Item = item(RawItem, _SrcLocn),
    ( if
        RawItem = predfunc_item(_Ret, Name, ProcNo, Params,
            AnnExprs, MaybeBodyExpr)
    then
        PredInfo = predicate_info(Params, AnnExprs, MaybeBodyExpr),
        !Env ^ predicate(Name, ProcNo) := PredInfo
    else
        true
    ).

%-----------------------------------------------------------------------------%

flatten_process_var_decl_item(Item, !Env) :-
    Item = item(RawItem, SrcLocn),
    ( 
        RawItem = var_decl_item(TIExpr, VarName, VarAnnExprs, MaybeValueExpr),
        trace [io(!IO)] (
            get_very_verbose_flag(VeryVerbose, !IO),
            (
                VeryVerbose = yes,
                Msg = "     Flattening variable `" ++ VarName ++
                    "' (" ++ show(SrcLocn) ++ ")",
                very_verbose(Msg, !IO)
            ;
                VeryVerbose = no
            )
        ),
        VarId = id_global(VarName),
        Context = [["In variable declaration for '", VarName, "'.\n"] |
            init_context(SrcLocn)],
        flatten_ti_expr(Context, TIExpr, VarPar, MZType, IndexRanges0, !Env),
        flatten_anns(Context, VarAnnExprs, Anns, !Env),
        (
            VarPar = var,
            add_global_permanent_var(VarId, MZType, IndexRanges0, Anns, !Env)
        ;
            VarPar = par, 
            add_global_par(VarId, MZType, IndexRanges0, !Env)
        ),
        (
            (
                MaybeValueExpr = rhs_assignment(ValueExpr),
                ValueContext = Context
            ;
                % If the assignment was originally a separate assign item
                % then use its context, not that of the variable declaration,
                % in error messages.
                MaybeValueExpr = separate_assignment(AssignSrcLocn, ValueExpr),
                ValueContext = [
                    ["In assignment for '", VarName, "'.\n"] | init_context(AssignSrcLocn)
                ]
            ),
            % We treat assignment as a constraint because we want to do bounds
            % checking on the value.
            ( if
                % If this is a var bool or array of var bool then we want to
                % reify the value (for example, we don't want to do any
                % assignments when processing, say, x = [y = 1, y = 2, y = 3]).
                ( if
                    VarPar = var,
                    ( MZType = mzn_bool
                    ; MZType = mzn_bool_array
                    )
                then
                    flatten_expr_must_reify(ValueContext, ValueExpr, MZValue, !Env)
                else
                    flatten_expr(ValueContext, ValueExpr, MZValue, !Env)
                ),
                replace_implicit_indexes(MZValue, IndexRanges0, IndexRanges),
                !Env ^ var_index_ranges(VarId) := IndexRanges,
                ( if
                    % Handle strings and annotations specially.
                    ( MZValue = mzn_expr(string_expr(_), _)
                    ; MZValue = mzn_expr(string_array_expr(_), _)
                    ; MZValue = mzn_expr(ann_expr(_), _)
                    ; MZValue = mzn_expr(ann_array_expr(_), _)
                    )
                then
                    !Env ^ var_value(VarId) := MZValue,
                    MZ = bool_to_mzn_expr(bool_const(yes))
                else
                    MZVarExpr = make_var_mzn_expr(IndexRanges, MZType, VarId),
                    flatten_builtin(ValueContext, "=", [MZVarExpr, MZValue],
                        MZ, !Env)
                ),
                MZ = mzn_expr(bool_expr(bool_const(yes)), _)
            then
                true
            else
                value_out_of_range(ValueContext)
            )
        ;
            MaybeValueExpr = no_assignment
        )
    ;
        RawItem = assign_item(VarName, AssignedExpr),
        VarId = id_global(VarName),
        Context =
            [["In assignment for '", VarName, "'.\n"] | init_context(SrcLocn)],
        ( if !.Env ^ var_value(VarId) = _ then
            % We clearly have multiple assignments for the same variable, which
            % is an error.
            minizinc_user_error(Context,
                "A variable cannot have more than one assignment.\n")
        else
            % We treat assignment as a constraint because we want to do bounds
            % checking on the value.
            IndexRanges = !.Env ^ var_index_ranges(VarId),
            MZType = !.Env ^ var_type(VarId),
            flatten_expr(Context, AssignedExpr, MZValue, !Env),
            ( if
                % Handle strings specially.
                ( MZType = mzn_string
                ; MZType = mzn_string_array
                )
              then
                !Env ^ var_value(VarId) := MZValue
              else
                MZVar = make_var_mzn_expr(IndexRanges, MZType, VarId),
                ( if
                    flatten_builtin(Context, "=", [MZVar, MZValue], MZ, !Env),
                    MZ = mzn_expr(bool_expr(bool_const(yes)), _)
                then
                    true
                else
                    value_out_of_range(Context)
                )
            )
        )
    ;
        ( RawItem = constraint_item(_)
        ; RawItem = predfunc_item(_, _, _, _, _, _)
        ; RawItem = annotation_item(_, _)
        ; RawItem = solve_item(_, _)
        ; RawItem = output_item(_)
        )
    ).

%-----------------------------------------------------------------------------/

flatten_process_constraint_item(Item, !Env) :-
    Item = item(RawItem, SrcLocn),
    ( if
        RawItem = constraint_item(Expr)
    then
        trace [io(!IO)] (
            get_very_verbose_flag(VeryVerbose, !IO),
            (
                VeryVerbose = yes,
                Msg = "     Flattening constraint (" ++ show(SrcLocn) ++ ")",
                very_verbose(Msg, !IO)
            ;
                VeryVerbose = no
            )
        ),
        Context = [["In constraint.\n"] | init_context(SrcLocn)],
        % Optimisation: at the top-level we can process all arguments of
        % a non-logical operator in a non-reifying context.  This saves a whole
        % pile of temporary bool variable creation (all of which must turn out
        % to be true!)  We can't process boolean operators this way: consider
        % the constraint x1 = x2 /\ x3 -- in this case our optimisation
        % would work incorrectly.
        InconsistencyMsg = "Model inconsistency detected.\n",
        ( if
            Expr = expr(RawExpr, AnnExprs, _ExprInfo),
            RawExpr = app(AppId, _AppProcNo, _AppKind, AppArgExprs),
            AppArgExprs = [ArgExprA, ArgExprB],
            ArgExprA ^ expr_info ^ expr_type_inst \= ti_var_bool,
            ArgExprB ^ expr_info ^ expr_type_inst \= ti_var_bool,
            Op = id_name(AppId),
            Arity = 2,
            is_builtin_op(Op, Arity, _, _, _)
        then
            flatten_anns(Context, AnnExprs, Anns, !Env),
            !Env ^ anns := Anns,
            flatten_expr(Context, ArgExprA, ArgMZA, !Env),
            flatten_expr(Context, ArgExprB, ArgMZB, !Env),
            ( if
                flatten_builtin(Context, Op, [ArgMZA, ArgMZB], MZ, !Env)
            then
                Z = mzn_expr_to_bool(Context, MZ),
                impose_constraint(Context, InconsistencyMsg, Z, !Env)
            else
                model_inconsistency_detected(Context, InconsistencyMsg)
            )
        else
            flatten_expr(Context, Expr, MZ, !Env),
            Z = mzn_expr_to_bool(Context, MZ),
            impose_constraint(Context, InconsistencyMsg, Z, !Env)
        ),
        !Env ^ anns := no_anns
    else
        true
    ).

%-----------------------------------------------------------------------------%

flatten_process_output_item(Item, !Env) :-
    Item = item(RawItem, _SrcLocn),
    ( if
        RawItem = output_item(OutputExpr)
    then
        get_model(!.Env, Model),
        OutputExprVars = global_vars_in_output_expr(Model, OutputExpr),
        set.fold(mark_var_for_output, OutputExprVars, !Env)
    else
        true    % XXX Should abort here.
    ).

%-----------------------------------------------------------------------------%

flatten_process_solve_item(Item, !Env) :-
    Item = sast_solve_item(SolveKind, AnnExprs, SrcLocn),
    Context = [["In solve item.\n"] | init_context(SrcLocn)],
    flatten_anns(Context, AnnExprs, Anns, !Env),
    (
        SolveKind = satisfy,
        MZSolveKind = mzn_solve_satisfy
    ;
        SolveKind = minimize(ObjFnExpr),
        flatten_expr(Context, ObjFnExpr, MZObjFn0, !Env),
        maybe_simplify_objective_func(Context, MZObjFn0, MZObjFn, !Env),
        MZSolveKind = mzn_solve_minimize(MZObjFn)
    ;
        SolveKind = maximize(ObjFnExpr),
        flatten_expr(Context, ObjFnExpr, MZObjFn0, !Env),
        maybe_simplify_objective_func(Context, MZObjFn0, MZObjFn, !Env),
        MZSolveKind = mzn_solve_maximize(MZObjFn)
    ),
    set_solve_goal(mzn_solve_goal(Anns, MZSolveKind), !Env).

:- pred maybe_simplify_objective_func(error_context::in,
    mzn_expr::in, mzn_expr::out, env::in, env::out) is det.

maybe_simplify_objective_func(Context, MZObjFn0, MZObjFn, !Env) :-
    ( if
        (
            MZObjFn0 = mzn_expr(bool_expr(A), ObjFnAnns),
            simplify_bool(Context, A, Z, !Env),
            MZObjFn1 = mzn_expr(bool_expr(Z), ObjFnAnns)
        ;
            MZObjFn0 = mzn_expr(float_expr(A), ObjFnAnns),
            simplify_float(Context, A, Z, !Env),
            MZObjFn1 = mzn_expr(float_expr(Z), ObjFnAnns)
        ;
            MZObjFn0 = mzn_expr(int_expr(A), ObjFnAnns),
            simplify_int(Context, A, Z, !Env),
            MZObjFn1 = mzn_expr(int_expr(Z), ObjFnAnns)
        )
    then
        MZObjFn = MZObjFn1
    else
        MZObjFn = MZObjFn0
    ).

%-----------------------------------------------------------------------------%

flatten_finalise_solve_item(!Env) :-
    MaybeSolveGoal = get_maybe_solve_goal(!.Env),
    (
        MaybeSolveGoal = yes(SolveGoal0),
        SolveGoal0 = mzn_solve_goal(SolveAnns, Kind),
        (
            (   
                Kind = mzn_solve_minimize(MZObjFn0),
                IsMinimiseProb = yes
            ;
                Kind = mzn_solve_maximize(MZObjFn0),
                IsMinimiseProb = no
            ),
            MZObjFn0 = mzn_expr(RawMZObjFn0, ObjAnns),
            ( if RawMZObjFn0 = float_expr(float_const(Float)) then
                make_tmp_float_var([], float_range_lb_ub(Float, Float),
                    no_anns, ObjVarId, ObjFloatExpr, !Env),
                !Env ^ var_value(ObjVarId) := mzn_expr(RawMZObjFn0, no_anns),
                RawMZObjExpr = float_expr(ObjFloatExpr),
                MZObjFn = mzn_expr(RawMZObjExpr, ObjAnns),
                rebuild_and_update_solve_goal(IsMinimiseProb, SolveAnns,
                    MZObjFn, !Env)
              else if RawMZObjFn0 = int_expr(int_const(Int)) then
                make_tmp_int_var([], int_range_lb_ub(Int, Int), no_anns,
                    ObjVarId, ObjIntExpr, !Env),
                !Env ^ var_value(ObjVarId) := mzn_expr(RawMZObjFn0, no_anns),
                RawMZObjExpr = int_expr(ObjIntExpr),
                MZObjFn = mzn_expr(RawMZObjExpr, ObjAnns),
                rebuild_and_update_solve_goal(IsMinimiseProb, SolveAnns,
                    MZObjFn, !Env)
              else  
                true
            )
        ;
            Kind = mzn_solve_satisfy
        ) 
    ;
        MaybeSolveGoal = no,
        unexpected($pred, "no solve goal")
    ).

:- pred rebuild_and_update_solve_goal(bool::in, mzn_anns::in, mzn_expr::in,
    env::in, env::out) is det.

rebuild_and_update_solve_goal(IsMinimiseProb, SolveAnns, ObjFn, !Env) :-
    (
        IsMinimiseProb = yes,
        Kind = mzn_solve_minimize(ObjFn)
    ;
        IsMinimiseProb = no,
        Kind = mzn_solve_maximize(ObjFn)
    ),
    SolveGoal = mzn_solve_goal(SolveAnns, Kind),
    update_solve_goal(SolveGoal, !Env).

%-----------------------------------------------------------------------------%
:- end_module flatten.item.
%-----------------------------------------------------------------------------%
