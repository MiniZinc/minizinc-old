%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2009 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Ralph Becket <rafe@csse.unimelb.edu.au>
%
% Handle expansion of applications.
%
%-----------------------------------------------------------------------------%

:- module flatten.app.
:- interface.

:- import_module errors.
:- import_module flatten.env.
:- import_module types.

%-----------------------------------------------------------------------------%

:- pred flatten_predicate(error_context::in, pred_name::in, proc_no::in,
    mzn_exprs::in, mzn_anns::in, bool_expr::out, env::in, env::out) is det.

    % Bind a local variable to a value.
    % Impose any constraints on the value induced from the local's type.
    %
:- pred bind_local(error_context::in, mzn_type::in, var_id::in, mzn_expr::in,
    env::in, env::out) is det.

    % These predicates are used to impose constraints on arguments,
    % but can also be used in other situations, such as let expressions.
    % Note that an error is emitted for out-of-range par assignments and alike,
    % so this is not appropriate for use in reified context where we need the
    % failure to propagate to the enclosing Boolean context.
    %
:- pred impose_float_bounds(error_context::in,
    float_range::in, float_expr::in, env::in, env::out) is det.

:- pred impose_float_set_bounds(error_context::in,
    float_range::in, float_set_expr::in, env::in, env::out) is det.

:- pred impose_float_array_bounds(error_context::in,
    float_range::in, float_array_expr::in, env::in, env::out) is det.

:- pred impose_float_set_array_bounds(error_context::in,
    float_range::in, float_set_array_expr::in, env::in, env::out) is det.

:- pred impose_int_bounds(error_context::in,
    int_range::in, int_expr::in, env::in, env::out) is det.

:- pred impose_int_set_bounds(error_context::in,
    int_range::in, int_set_expr::in, env::in, env::out) is det.

:- pred impose_int_array_bounds(error_context::in,
    int_range::in, int_array_expr::in, env::in, env::out) is det.

:- pred impose_int_set_array_bounds(error_context::in,
    int_range::in, int_set_array_expr::in, env::in, env::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module flatten.ann.
:- import_module flatten.array.
:- import_module flatten.bool.
:- import_module flatten.expr.
:- import_module flatten.float.
:- import_module flatten.int.
:- import_module mzn_ops.

:- import_module intset.
:- import_module zinc_ast.

:- import_module array.
:- import_module bool.
:- import_module float.
:- import_module int.
:- import_module list.
:- import_module maybe.
:- import_module pair.
:- import_module set.
:- import_module string.
:- import_module unit.

%-----------------------------------------------------------------------------%

flatten_predicate(Context, PredName, ProcNum, Args, PredAnns0, Z, !Env) :-
    % We clear out the local variables for the new predicate expansion
    % (MiniZinc doesn't have nested predicates).
    OldLocals = !.Env ^ locals,
    !Env ^ locals := empty_local_var_map,
    Reifying = !.Env ^ reifying,
    (
        Reifying = reifying(_ : bool_exprs),
        flatten_predicate_reif(Context, PredName, ProcNum, Args, PredAnns0,
            Reifying, Z, !Env)
    ;
        Reifying = not_reifying,
        flatten_predicate_non_reif(Context, PredName, ProcNum, Args, PredAnns0,
            Z, !Env)
    ),
    !Env ^ locals := OldLocals.

%-----------------------------------------------------------------------------%
%
% Flattening predicates in reified contexts.
%

:- pred flatten_predicate_reif(error_context::in, pred_name::in, proc_no::in,
    mzn_exprs::in, mzn_anns::in, reifying::in, bool_expr::out,
    env::in, env::out) is det.

flatten_predicate_reif(Context, PredName, ProcNum, Args, PredAnns0, 
        Reifying, Z, !Env) :-
    % Check if we have a specialised reified definition for the predicate.
    % A specialised reified definition will have the suffix "_reif" appended
    % to its name and an extra Boolean parameter appended to its parameter list.
    % (The latter will be checked when we attempt to bind the arguments.)
    % XXX: this code assumes that the reified version will also have the same
    % proc number as the non-reified form; nothing actually gurantees this
    % however.
    ( if
        ReifPredName = string.(PredName ++ "_reif"),
        ReifPredInfo = !.Env ^ predicate(ReifPredName, ProcNum)
      then
        flatten_predicate_reif_special(Context, ReifPredName, ReifPredInfo,
            Args, PredAnns0, Reifying, Z, !Env)
      else
        flatten_predicate_reif_non_special(Context, PredName, ProcNum,
            Args, PredAnns0, Z, !Env)
    ).

    % Flatten a predicate in a reifying context where we have a specialised
    % reified form of the predicate.
    %
:- pred flatten_predicate_reif_special(error_context::in, pred_name::in,
    predicate_info::in, mzn_exprs::in, mzn_anns::in,
    reifying::in, bool_expr::out, env::in, env::out) is det.

flatten_predicate_reif_special(Context, ReifPredName, ReifPredInfo, Args,
        PredAnns0, Reifying, Z, !Env) :-
    
    % Begin by flattening the arguments in the current reifying context (new
    % constraints may be induced from parameter types).
    ReifPredInfo = predicate_info(ArgTypesAndIds, PredAnnExprs, MaybeBody),

    % Add a reification argument to the arguments.
    % Save the environment beforehand since we need to add a new variable and
    % if binding the arguments fails then we want to restore the envionment to
    % the state that it was in _before_ the reification variable was added.
    % Not doing so would leave an unused Boolean variable in the model.
    SavedEnv = !.Env,
    make_tmp_bool_var(Context, unit, no_anns, _ReifVarId, Reif, !Env),
    ReifExpr = bool_to_mzn_expr(Reif),
    ArgsWithReif = list.(Args ++ [ReifExpr]),

    ( if
        bind_predicate_args_reif(Context, ArgTypesAndIds, ArgsWithReif, !Env)
      then
        flatten_anns(Context, PredAnnExprs, PredAnns1, !Env),
        PredAnns = join_anns(PredAnns0, PredAnns1),
        OldAnns = !.Env ^ anns,
        add_anns(PredAnns, !Env),

        % Since we have a specialised reified form, we need to flatten the body
        % in a non-reifying context.
        !Env ^ reifying := not_reifying,
        (
            MaybeBody = no,
            % We're in a reifying context and this predicate has a reified form
            % with no body, so we just generate a constraint for it.
            simplify_args(Context, ArgsWithReif, SimplifiedArgs, !Env),
            add_constraint(Context, ReifPredName, SimplifiedArgs, no_anns,
                !Env),
            Z = Reif
        ;
            MaybeBody = yes(Body),
            % We're in a reifying context and this predicate has a reified form
            % with a body, so we expand it.
            flatten_expr(Context, Body, MZ, !Env),
            flatten.bool.conjoin(Context, mzn_expr_to_bool(Context, MZ), Reif,
                Z, !Env)
        ),
        !Env ^ anns := OldAnns
     else
        % Some of the constraints induced by the predicate parameter types
        % failed - propagate the failure up to the enclosing Boolean context.
        Z = bool_const(no),

        % Restore the environment to the state it was in before we added the
        % reification variable, i.e. uncreate that variable.
        !:Env = SavedEnv
    ),
    % Restore the reifying context for the caller.
    !Env ^ reifying := Reifying.
        
    % Flatten a predicate in a reifying context where do *not* have a
    % a specialised reified version of the predicate.
    %
:- pred flatten_predicate_reif_non_special(error_context::in, pred_name::in,
    proc_no::in, mzn_exprs::in, mzn_anns::in, bool_expr::out,
    env::in, env::out) is det.

flatten_predicate_reif_non_special(Context, PredName, ProcNum,
            Args, PredAnns0, Z, !Env) :-
    PredInfo = get_predicate_info_or_report_error(Context, PredName, ProcNum,
        !.Env),
    PredInfo = predicate_info(ArgTypesAndIds, PredAnnExprs, MaybeBody),
    (
        MaybeBody = no,
        % We're in a reifying context and this predicate only has a non-reified
        % form without a body, so we're stuck.
        minizinc_user_error(Context,
            "'" ++ PredName ++ "' is used in a reified context, " ++
            "but has no body to expand.\n")
    ;
        MaybeBody = yes(Body),
        % We're in a reifying context and this predicate has a body, so we
        % expand it.
        ( if
            bind_predicate_args_reif(Context, ArgTypesAndIds, Args, !Env)
          then
            flatten_anns(Context, PredAnnExprs, PredAnns1, !Env),
            PredAnns = join_anns(PredAnns0, PredAnns1),
            OldAnns = !.Env ^ anns,
            add_anns(PredAnns, !Env),
            flatten_expr(Context, Body, MZ, !Env),
            Z = mzn_expr_to_bool(Context, MZ),
            !Env ^ anns := OldAnns
          else
            % Some of the constraints induced by the predicate parameter types
            % failed - propagate the failure up to the enclosing Boolean
            % context.
            Z = bool_const(no)
        )
    ).

%-----------------------------------------------------------------------------%
%
% Flattening predicates in non-reified contexts.
%

:- pred flatten_predicate_non_reif(error_context::in, pred_name::in,
    proc_no::in, mzn_exprs::in, mzn_anns::in, bool_expr::out,
    env::in, env::out) is det.

flatten_predicate_non_reif(Context, PredName, ProcNum, Args, PredAnns0, 
        Z, !Env) :-
    PredInfo = get_predicate_info_or_report_error(Context, PredName,
        ProcNum, !.Env),
    PredInfo = predicate_info(ArgTypesAndIds, PredAnnExprs, MaybeBody),
    flatten_anns(Context, PredAnnExprs, PredAnns1, !Env),
    PredAnns = join_anns(PredAnns0, PredAnns1),
    OldAnns = !.Env ^ anns,
    add_anns(PredAnns, !Env),
    (
        MaybeBody = no,
        % We are not in a reifying context and this predicate has no body, so
        % we just generate a constraint for it.
        simplify_args(Context, Args, SimplifiedArgs, !Env),
        % We still have to bind the arguments to ensure we impose any
        % constraints induced from the predicate parameter types.
        bind_predicate_args(Context, ArgTypesAndIds, SimplifiedArgs, !Env),
        add_constraint(Context, PredName, SimplifiedArgs, no_anns, !Env),
        Z = bool_const(yes)
    ;
        MaybeBody = yes(Body),
        % We are not in a reifying context and this predicate has a body, so we
        % expand it.
        bind_predicate_args(Context, ArgTypesAndIds, Args, !Env),
        flatten_expr(Context, Body, MZ, !Env),
        Z = mzn_expr_to_bool(Context, MZ)
    ),
    !Env ^ anns := OldAnns.
    
%-----------------------------------------------------------------------------%

    % Look up the predicate_info for the given predicate in the enviroment
    % or, if it cannot be found, emit an error message saying that the
    % predicate is unrecognised.
    %
:- func get_predicate_info_or_report_error(error_context, pred_name, proc_no,
    env) = predicate_info.

get_predicate_info_or_report_error(Context, PredName, ProcNo, Env)
        = PredInfo :-
    ( if PredInfo0 = Env ^ predicate(PredName, ProcNo) then
        PredInfo = PredInfo0
      else
        minizinc_user_error(Context, "Unrecognised predicate.\n")
    ).

%-----------------------------------------------------------------------------%
%
% We need to ensure that constraint arguments are "simplified" (i.e., are
% valid FlatZinc terms).
%

:- pred simplify_args(error_context::in, mzn_exprs::in, mzn_exprs::out,
    env::in, env::out) is det.

simplify_args(Context, MZs, SimplifiedMZs, !Env) :-
    list.map_foldl2(simplify_arg(Context), MZs, SimplifiedMZs, 1, _, !Env).

:- pred simplify_arg(error_context::in,
    mzn_expr::in, mzn_expr::out, int::in, int::out, env::in, env::out) is det.

simplify_arg(Context, MZ, SimplifiedMZ, ArgNum, ArgNum + 1, !Env) :-
    ArgContext =
        [["In argument ", string.int_to_string(ArgNum), "\n"] | Context],
    MZ = mzn_expr(Arg, Anns),
    (
        Arg = bool_expr(A),
        simplify_bool(ArgContext, A, SimplifiedA, !Env),
        SimplifiedArg = bool_expr(SimplifiedA)
    ;
        Arg = float_expr(A),
        simplify_float(ArgContext, A, SimplifiedA, !Env),
        SimplifiedArg = float_expr(SimplifiedA)
    ;
        Arg = int_expr(A),
        simplify_int(ArgContext, A, SimplifiedA, !Env),
        SimplifiedArg = int_expr(SimplifiedA)
    ;
        Arg = bool_array_expr(A),
        simplify_array(simplify_bool(ArgContext), A, SimplifiedA, !Env),
        SimplifiedArg = bool_array_expr(SimplifiedA)
    ;
        Arg = float_array_expr(A),
        simplify_array(simplify_float(ArgContext), A, SimplifiedA, !Env),
        SimplifiedArg = float_array_expr(SimplifiedA)
    ;
        Arg = int_array_expr(A),
        simplify_array(simplify_int(ArgContext), A, SimplifiedA, !Env),
        SimplifiedArg = int_array_expr(SimplifiedA)
    ;
        Arg = int_set_expr(_),
        SimplifiedArg = Arg
    ;
        Arg = int_set_array_expr(A),
        SimplifiedA = index_ranges_to_fzn_form(A),
        SimplifiedArg = int_set_array_expr(SimplifiedA)
    ;
        ( Arg = bool_set_expr(_),         TypeName = "set of bool"
        ; Arg = float_set_expr(_),        TypeName = "set of float"
        ; Arg = bool_set_array_expr(_),   TypeName = "array of set of bool"
        ; Arg = float_set_array_expr(_),  TypeName = "array of set of float"
        ; Arg = string_expr(_),           TypeName = "string"
        ; Arg = string_array_expr(_),     TypeName = "array of string"
        ; Arg = bottom_expr(_),           TypeName = "bottom"
        ; Arg = bottom_array_expr(_),     TypeName = "array of bottom"
        ),
        minizinc_user_error(ArgContext,
            TypeName ++ " is not a FlatZinc type.\n")
    ;
        ( Arg = ann_expr(_)
        ; Arg = ann_array_expr(_)
        ),
        minizinc_user_error(ArgContext,
            "Annotations are not first class FlatZinc values.\n")
    ),
    SimplifiedMZ = mzn_expr(SimplifiedArg, Anns).

%-----------------------------------------------------------------------------%
%
% Binding predicate arguments.
%

% NOTE: there are two versions of the code for binding predicate arguments.
% This one is intended for use in non-reified contexts; par expressions that
% evaluate to false will cause an error message to be emitted.
%
% The versions of these predicate with the prefix "_reif" attached to their
% names are identical except that the will fail rather than generating
% an error message.
% XXX we could (but currently don't) generate warning messages for false par
% expressions.  To do this we we need to emit the warning just before the goal
% "false" in the reified versions of the argument binding predicates.
%
% XXX this code could be better factored since the two versions almost do the
% same thing.

:- pred bind_predicate_args(error_context::in,
    ti_exprs_and_ids::in, mzn_exprs::in, env::in, env::out) is det.

bind_predicate_args(Context, TIExprsAndIds, Args, !Env) :-
    bind_predicate_args_2(Context, TIExprsAndIds, Args, 1, !Env).

:- pred bind_predicate_args_2(error_context::in,
    ti_exprs_and_ids::in, mzn_exprs::in, int::in, env::in, env::out) is det.

bind_predicate_args_2(Context, TIExprsAndIds0, Args0, ArgNum, !Env) :-
    (
        TIExprsAndIds0 = [], Args0 = []
    ;
        TIExprsAndIds0 = [TIExprAndId | TIExprsAndIds], Args0 = [Arg | Args],
        ArgContext =
            [["In argument ", string.int_to_string(ArgNum), ".\n"] | Context],
        TIExprAndId = TIExpr - VarId,
        flatten_ti_expr(ArgContext, TIExpr, _VarPar, MZType, _IndexRanges,
            !Env),
        bind_local(ArgContext, MZType, VarId, Arg, !Env),
        bind_predicate_args_2(Context, TIExprsAndIds, Args, ArgNum + 1, !Env)
    ;
        ( TIExprsAndIds0 = [], Args0 = [_ | _]
        ; TIExprsAndIds0 = [_ | _], Args0 = []
        ),
        ArgContext =
            [["In argument ", string.int_to_string(ArgNum), ".\n"] | Context],
        minizinc_internal_error(ArgContext, $pred,
            "mismatched list lengths.\n")
    ).

%-----------------------------------------------------------------------------%

bind_local(Context, MZType, VarId, Arg, !Env) :-
    add_local_var(VarId, Arg, !Env),
    (
        MZType = mzn_bool
    ;
        MZType = mzn_bool_array
    ;
        MZType = mzn_bool_set
    ;
        MZType = mzn_bool_set_array
    ;
        MZType = mzn_float(Bounds),
        A = mzn_expr_to_float(Context, Arg),
        impose_float_bounds(Context, Bounds, A, !Env)
    ;
        MZType = mzn_float_array(Bounds),
        A = mzn_expr_to_float_array(Context, Arg),
        impose_float_array_bounds(Context, Bounds, A, !Env)
    ;
        MZType = mzn_float_set(Bounds),
        A = mzn_expr_to_float_set(Context, Arg),
        impose_float_set_bounds(Context, Bounds, A, !Env)
    ;
        MZType = mzn_float_set_array(Bounds),
        A = mzn_expr_to_float_set_array(Context, Arg),
        impose_float_set_array_bounds(Context, Bounds, A, !Env)
    ;
        MZType = mzn_int(Bounds),
        A = mzn_expr_to_int(Context, Arg),
        impose_int_bounds(Context, Bounds, A, !Env)
    ;
        MZType = mzn_int_array(Bounds),
        A = mzn_expr_to_int_array(Context, Arg),
        impose_int_array_bounds(Context, Bounds, A, !Env)
    ;
        MZType = mzn_int_set(Bounds),
        A = mzn_expr_to_int_set(Context, Arg),
        impose_int_set_bounds(Context, Bounds, A, !Env)
    ;
        MZType = mzn_int_set_array(Bounds),
        A = mzn_expr_to_int_set_array(Context, Arg),
        impose_int_set_array_bounds(Context, Bounds, A, !Env)
    ;
        MZType = mzn_string
    ;
        MZType = mzn_string_array
    ;
        MZType = mzn_bottom
    ;
        MZType = mzn_bottom_array
    ;
        ( MZType = mzn_ann
        ; MZType = mzn_ann_array
        ),
        minizinc_internal_error(Context, $pred,
            "Unexpected annotation type.\n")
    ).

%-----------------------------------------------------------------------------%

impose_float_bounds(_Context, float_range_unbounded, _A, !Env).
impose_float_bounds(Context, float_range_lb_ub(LB, UB), A0, !Env) :-
    simplify_float(Context, A0, A, !Env),
    impose_float_le(Context, float_const(LB), A, !Env),
    impose_float_le(Context, A, float_const(UB), !Env).
impose_float_bounds(Context, float_range_set(Set), A0, !Env) :-
    simplify_float(Context, A0, A, !Env),
    impose_float_in(Context, A, set_items(Set), !Env).

%-----------------------------------------------------------------------------%

impose_float_array_bounds(Context, Bounds, A0, !Env) :-
    A = fully_deref_float_array(Context, A0, !.Env),
    (
        A = array_var(_, V),
        impose_float_var_bounds(Context, Bounds, V, !Env)
    ;
        A = array_items(_, ItemsA),
        array.foldl(impose_float_bounds(Context, Bounds), ItemsA, !Env)
    ).

%-----------------------------------------------------------------------------%

:- pred impose_float_var_bounds(error_context::in, float_range::in, var_id::in,
    env::in, env::out) is det.

impose_float_var_bounds(Context, Bounds, Var, !Env) :-
    (
        Bounds = float_range_unbounded
    ;
        Bounds = float_range_lb_ub(LBB, UBB),
        LBA = !.Env ^ var_float_lb(Var),
        !Env ^ var_float_lb(Var) := float.max(LBA, LBB),
        UBA = !.Env ^ var_float_ub(Var),
        !Env ^ var_float_ub(Var) := float.min(UBA, UBB)
    ;
        Bounds = float_range_set(Set),
        ( if
            Xs = set.to_sorted_list(Set),
            Xs = [LB | _],
            list.det_last(Xs, UB)
        then
            impose_float_var_bounds(Context, float_range_lb_ub(LB, UB), Var,
                !Env)
        else
            arg_out_of_range(Context)
        )
    ).

%-----------------------------------------------------------------------------%

impose_float_set_bounds(Context, Bounds, A, !Env) :-
    (
        (
            A = set_var(var_no_index(V))
        ;
            A = set_var(var_index(V, _))
        ),
        impose_float_var_bounds(Context, Bounds, V, !Env)
    ;
        A = set_items(SetA),
        (
            Bounds = float_range_unbounded
        ;
            Bounds = float_range_lb_ub(LB, UB),
            ( if
                XsA = set.to_sorted_list(SetA),
                XsA = [LBA | _],
                list.det_last(XsA, UBA),
                LB =< LBA, UBA =< UB
            then
                true
            else
                arg_out_of_range(Context)
            )
        ;
            Bounds = float_range_set(SetB),
            ( if set.subset(SetA, SetB) then
                true
            else
                arg_out_of_range(Context)
            )
        )
    ).

%-----------------------------------------------------------------------------%

impose_float_set_array_bounds(Context, Bounds, A, !Env) :-
    ( if Bounds = float_range_unbounded then
        true
    else
        (
            A = array_var(_, V),
            impose_float_var_bounds(Context, Bounds, V, !Env)
        ;
            A = array_items(_, Xs),
            array.foldl(impose_float_set_bounds(Context, Bounds), Xs, !Env)
        )
    ).

%-----------------------------------------------------------------------------%

impose_int_bounds(_Context, int_range_unbounded, _A, !Env).
impose_int_bounds(Context, int_range_lb_ub(LB, UB), A0, !Env) :-
    simplify_int(Context, A0, A, !Env),
    impose_int_le(Context, int_const(LB), A, !Env),
    impose_int_le(Context, A, int_const(UB), !Env).
impose_int_bounds(Context, int_range_set(Set0), A0, !Env) :-
    simplify_int(Context, A0, A, !Env),
    % JJJ - INTSET REPN
    Set = set.from_sorted_list(intset.to_sorted_list(Set0)),
    impose_int_in(Context, A, set_items(Set), !Env).

%-----------------------------------------------------------------------------%

impose_int_array_bounds(Context, Bounds, A0, !Env) :-
    A = fully_deref_int_array(Context, A0, !.Env),
    (
        A = array_var(_, V),
        impose_int_var_bounds(Context, Bounds, V, !Env)
    ;
        A = array_items(_, ItemsA),
        array.foldl(impose_int_bounds(Context, Bounds), ItemsA, !Env)
    ).

%-----------------------------------------------------------------------------%

:- pred impose_int_var_bounds(error_context::in, int_range::in, var_id::in,
    env::in, env::out) is det.

impose_int_var_bounds(Context, Bounds, Var, !Env) :-
    (
        Bounds = int_range_unbounded
    ;
        Bounds = int_range_lb_ub(LBB, UBB),
        LBA = !.Env ^ var_int_lb(Var),
        !Env ^ var_int_lb(Var) := int.max(LBA, LBB),
        UBA = !.Env ^ var_int_ub(Var),
        !Env ^ var_int_ub(Var) := int.min(UBA, UBB)
    ;
        Bounds = int_range_set(Set),
        ( if
            % JJJ - INTSET REPN.
            Xs = intset.to_sorted_list(Set),
            Xs = [LB | _],
            list.det_last(Xs, UB)
        then
            impose_int_var_bounds(Context, int_range_lb_ub(LB, UB), Var, !Env)
        else
            arg_out_of_range(Context)
        )
    ).

%-----------------------------------------------------------------------------%

impose_int_set_bounds(Context, Bounds, A, !Env) :-
    (
        (
            A = set_var(var_no_index(V))
        ;
            A = set_var(var_index(V, _))
        ),
        impose_int_set_var_bounds(Context, Bounds, V, !Env)
    ;
        A = set_items(SetA),
        (
            Bounds = int_range_unbounded
        ;
            Bounds = int_range_lb_ub(LB, UB),
            ( if
                XsA = set.to_sorted_list(SetA),
                XsA = [LBA | _],
                list.det_last(XsA, UBA),
                LB =< LBA, UBA =< UB
            then
                true
            else
                arg_out_of_range(Context)
            )
        ;
            Bounds = int_range_set(SetB),
            ( if intset.subset(from_set(SetA), SetB) then
                true
            else
                arg_out_of_range(Context)
            )
        )
    ).

%-----------------------------------------------------------------------------%

impose_int_set_array_bounds(Context, Bounds, A, !Env) :-
    ( if Bounds = int_range_unbounded then
        true
    else
        (
            A = array_var(_, V),
            impose_int_set_var_bounds(Context, Bounds, V, !Env)
        ;
            A = array_items(_, Xs),
            array.foldl(impose_int_set_bounds(Context, Bounds), Xs, !Env)
        )
    ).

%-----------------------------------------------------------------------------%

:- pred impose_int_set_var_bounds(error_context::in, int_range::in, var_id::in,
    env::in, env::out) is det.

impose_int_set_var_bounds(Context, Bounds, Var, !Env) :-
    A = int_var(var_no_index(Var)),
    refine_int_bounds(Context, Bounds, A, !Env),
    (
        Bounds = int_range_unbounded
    ;
        Bounds = int_range_lb_ub(LBB, UBB),
        BoundsVar = !.Env ^ var_set_ub(Var),
        (
            BoundsVar = int_range_unbounded,
            !Env ^ var_set_ub(Var) := Bounds
        ;
            BoundsVar = int_range_lb_ub(LBA, UBA),
            !Env ^ var_set_ub(Var) :=
                int_range_lb_ub(int.max(LBA, LBB), int.min(UBA, UBB))
        ;
            BoundsVar = int_range_set(SetA),
            !Env ^ var_set_ub(Var) :=
                int_range_set(intset.intersection(SetA, intset(LBB, UBB)))
        )
    ;
        Bounds = int_range_set(SetB),
        BoundsVar = !.Env ^ var_set_ub(Var),
        (
            BoundsVar = int_range_unbounded,
            !Env ^ var_set_ub(Var) := Bounds
        ;
            BoundsVar = int_range_lb_ub(LBA, UBA),
            !Env ^ var_set_ub(Var) :=
                int_range_set(intset.intersection(SetB, intset(LBA, UBA)))
        ;
            BoundsVar = int_range_set(SetA),
            !Env ^ var_set_ub(Var) :=
                int_range_set(intset.intersection(SetA, SetB))
        )
    ).

%-----------------------------------------------------------------------------%

:- pred impose_float_le(error_context::in,
    float_expr::in, float_expr::in, env::in, env::out) is det.

impose_float_le(Context, A, B, !Env) :-
    ( if
        flatten_float_float_to_bool(Context, no_anns, ff2b_le, A, B, Z, !Env)
    then
        post_process_flatten_to_bool(Context, Z, !Env)
    else
        minizinc_internal_error(Context, $pred, "flattening '<=' failed.\n")
    ).

:- pred impose_float_in(error_context::in,
    float_expr::in, float_set_expr::in, env::in, env::out) is det.

impose_float_in(Context, A, B, !Env) :-
    flatten_float_float_set_to_bool(Context, no_anns, ffs2b_in, A, B, BoolZ,
        !Env),
    post_process_flatten_to_bool(Context, boolcv_const(BoolZ), !Env).

:- pred impose_int_le(error_context::in,
    int_expr::in, int_expr::in, env::in, env::out) is det.

impose_int_le(Context, A, B, !Env) :-
    ( if
        flatten_int_int_to_bool(Context, no_anns, ii2b_le, A, B, Z, !Env)
    then
        post_process_flatten_to_bool(Context, Z, !Env)
    else
        minizinc_internal_error(Context, $pred, "flattening '<=' failed.\n")
    ).

:- pred impose_int_in(error_context::in,
    int_expr::in, int_set_expr::in, env::in, env::out) is det.

impose_int_in(Context, A, B, !Env) :-
    ( if
        flatten_int_int_set_to_bool(Context, no_anns, iis2b_in, A, B, Z, !Env)
    then
        post_process_flatten_to_bool(Context, Z, !Env)
    else
        minizinc_internal_error(Context, $pred, "flattening 'in' failed.\n")
    ).

%-----------------------------------------------------------------------------%

:- pred post_process_flatten_to_bool(error_context::in, bool_const_or_var::in,
    env::in, env::out) is det.

post_process_flatten_to_bool(Context, Z, !Env) :-
    (
        Z = boolcv_const(yes)
    ;
        Z = boolcv_const(no),
        arg_out_of_range(Context)
    ;
        Z = boolcv_var(MZVar),
        ( if !.Env ^ reifying = reifying(ReifVars) then
            !Env ^ reifying := reifying([bool_var(MZVar) | ReifVars])
        else
            minizinc_internal_error(Context, $pred,
                "bool_var constraint in non-reifying context.\n")
        )
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

% Code for binding predicate arguments in reified contexts.

:- pred bind_predicate_args_reif(error_context::in,
    ti_exprs_and_ids::in, mzn_exprs::in, env::in, env::out) is semidet.

bind_predicate_args_reif(Context, TIExprsAndIds, Args, !Env) :-
    bind_predicate_args_reif_2(Context, TIExprsAndIds, Args, 1, !Env).

:- pred bind_predicate_args_reif_2(error_context::in,
    ti_exprs_and_ids::in, mzn_exprs::in, int::in, env::in, env::out)
    is semidet.

bind_predicate_args_reif_2(Context, TIExprsAndIds0, Args0, ArgNum, !Env) :-
    (
        TIExprsAndIds0 = [], Args0 = []
    ;
        TIExprsAndIds0 = [TIExprAndId | TIExprsAndIds], Args0 = [Arg | Args],
        ArgContext =
            [["In argument ", string.int_to_string(ArgNum), ".\n"] | Context],
        TIExprAndId = TIExpr - VarId,
        flatten_ti_expr(ArgContext, TIExpr, _VarPar, MZType, _IndexRanges,
            !Env),
        bind_local_reif(ArgContext, MZType, VarId, Arg, !Env),
        bind_predicate_args_reif_2(Context, TIExprsAndIds, Args, ArgNum + 1,
            !Env)
    ;
        ( TIExprsAndIds0 = [], Args0 = [_ | _]
        ; TIExprsAndIds0 = [_ | _], Args0 = []
        ),
        ArgContext =
            [["In argument ", string.int_to_string(ArgNum), ".\n"] | Context],
        minizinc_internal_error(ArgContext, $pred,
            "mismatched list lengths.\n")
    ).

:- pred bind_local_reif(error_context::in, mzn_type::in, var_id::in,
    mzn_expr::in, env::in, env::out) is semidet.

bind_local_reif(Context, MZType, VarId, Arg, !Env) :-
    add_local_var(VarId, Arg, !Env),
    (
        ( MZType = mzn_bool
        ; MZType = mzn_bool_array
        ; MZType = mzn_bool_set
        ; MZType = mzn_bool_set_array
        ; MZType = mzn_string
        ; MZType = mzn_string_array
        ; MZType = mzn_bottom
        ; MZType = mzn_bottom_array
        )
    ;
        MZType = mzn_float(Bounds),
        A = mzn_expr_to_float(Context, Arg),
        impose_float_bounds_reif(Context, Bounds, A, !Env)
    ;
        MZType = mzn_float_array(Bounds),
        A = mzn_expr_to_float_array(Context, Arg),
        impose_float_array_bounds_reif(Context, Bounds, A, !Env)
    ;
        MZType = mzn_float_set(Bounds),
        A = mzn_expr_to_float_set(Context, Arg),
        impose_float_set_bounds_reif(Context, Bounds, A, !Env)
    ;
        MZType = mzn_float_set_array(Bounds),
        A = mzn_expr_to_float_set_array(Context, Arg),
        impose_float_set_array_bounds_reif(Context, Bounds, A, !Env)
    ;
        MZType = mzn_int(Bounds),
        A = mzn_expr_to_int(Context, Arg),
        impose_int_bounds_reif(Context, Bounds, A, !Env)
    ;
        MZType = mzn_int_array(Bounds),
        A = mzn_expr_to_int_array(Context, Arg),
        impose_int_array_bounds_reif(Context, Bounds, A, !Env)
    ;
        MZType = mzn_int_set(Bounds),
        A = mzn_expr_to_int_set(Context, Arg),
        impose_int_set_bounds_reif(Context, Bounds, A, !Env)
    ;
        MZType = mzn_int_set_array(Bounds),
        A = mzn_expr_to_int_set_array(Context, Arg),
        impose_int_set_array_bounds_reif(Context, Bounds, A, !Env)
    ;
        ( MZType = mzn_ann
        ; MZType = mzn_ann_array
        ),
        minizinc_internal_error(Context, $pred,
            "Unexpected annotation type.\n")
    ).

%-----------------------------------------------------------------------------%

:- pred impose_float_bounds_reif(error_context::in,
    float_range::in, float_expr::in, env::in, env::out) is semidet.

impose_float_bounds_reif(_Context, float_range_unbounded, _A, !Env).
impose_float_bounds_reif(Context, float_range_lb_ub(LB, UB), A0, !Env) :-
    simplify_float(Context, A0, A, !Env),
    impose_float_le_reif(Context, float_const(LB), A, !Env),
    impose_float_le_reif(Context, A, float_const(UB), !Env).
impose_float_bounds_reif(Context, float_range_set(Set), A0, !Env) :-
    simplify_float(Context, A0, A, !Env),
    impose_float_in_reif(Context, A, set_items(Set), !Env).

:- pred impose_float_array_bounds_reif(error_context::in,
    float_range::in, float_array_expr::in, env::in, env::out) is semidet.

impose_float_array_bounds_reif(Context, Bounds, A0, !Env) :-
    A = fully_deref_float_array(Context, A0, !.Env),
    (
        A = array_var(_, V),
        impose_float_var_bounds_reif(Context, Bounds, V, !Env)
    ;
        A = array_items(_, ItemsA),
        array.foldl(impose_float_bounds_reif(Context, Bounds), ItemsA, !Env)
    ).

:- pred impose_float_var_bounds_reif(error_context::in, float_range::in,
    var_id::in, env::in, env::out) is semidet.

impose_float_var_bounds_reif(Context, Bounds, Var, !Env) :-
    (
        Bounds = float_range_unbounded
    ;
        Bounds = float_range_lb_ub(LBB, UBB),
        LBA = !.Env ^ var_float_lb(Var),
        !Env ^ var_float_lb(Var) := float.max(LBA, LBB),
        UBA = !.Env ^ var_float_ub(Var),
        !Env ^ var_float_ub(Var) := float.min(UBA, UBB)
    ;
        Bounds = float_range_set(Set),
        ( if
            Xs = set.to_sorted_list(Set),
            Xs = [LB | _],
            list.det_last(Xs, UB)
        then
            impose_float_var_bounds_reif(Context, float_range_lb_ub(LB, UB),
                Var, !Env)
        else
            false
        )
    ).

:- pred impose_float_set_bounds_reif(error_context::in,
    float_range::in, float_set_expr::in, env::in, env::out) is semidet.

impose_float_set_bounds_reif(Context, Bounds, A, !Env) :-
    (
        ( A = set_var(var_no_index(V))
        ; A = set_var(var_index(V, _))
        ),
        impose_float_var_bounds_reif(Context, Bounds, V, !Env)
    ;
        A = set_items(SetA),
        (
            Bounds = float_range_unbounded
        ;
            Bounds = float_range_lb_ub(LB, UB),
            ( if
                XsA = set.to_sorted_list(SetA),
                XsA = [LBA | _],
                list.det_last(XsA, UBA),
                LB =< LBA, UBA =< UB
            then
                true
            else
                false
            )
        ;
            Bounds = float_range_set(SetB),
            ( if set.subset(SetA, SetB) then
                true
            else
                false
            )
        )
    ).

:- pred impose_float_set_array_bounds_reif(error_context::in,
    float_range::in, float_set_array_expr::in, env::in, env::out) is semidet.

impose_float_set_array_bounds_reif(Context, Bounds, A, !Env) :-
    ( if Bounds = float_range_unbounded then
        true
    else
        (
            A = array_var(_, V),
            impose_float_var_bounds_reif(Context, Bounds, V, !Env)
        ;
            A = array_items(_, Xs),
            array.foldl(impose_float_set_bounds_reif(Context, Bounds), Xs,
                !Env)
        )
    ).

%-----------------------------------------------------------------------------%

:- pred impose_int_bounds_reif(error_context::in,
    int_range::in, int_expr::in, env::in, env::out) is semidet.

impose_int_bounds_reif(_Context, int_range_unbounded, _A, !Env).
impose_int_bounds_reif(Context, int_range_lb_ub(LB, UB), A0, !Env) :-
    simplify_int(Context, A0, A, !Env),
    impose_int_le_reif(Context, int_const(LB), A, !Env),
    impose_int_le_reif(Context, A, int_const(UB), !Env).
impose_int_bounds_reif(Context, int_range_set(Set0), A0, !Env) :-
    simplify_int(Context, A0, A, !Env),
    % JJJ - INTSET REPN
    Set = set.from_sorted_list(intset.to_sorted_list(Set0)),
    impose_int_in_reif(Context, A, set_items(Set), !Env).

%-----------------------------------------------------------------------------%

:- pred impose_int_array_bounds_reif(error_context::in,
    int_range::in, int_array_expr::in, env::in, env::out) is semidet.

impose_int_array_bounds_reif(Context, Bounds, A0, !Env) :-
    A = fully_deref_int_array(Context, A0, !.Env),
    (
        A = array_var(_, V),
        impose_int_var_bounds_reif(Context, Bounds, V, !Env)
    ;
        A = array_items(_, ItemsA),
        array.foldl(impose_int_bounds_reif(Context, Bounds), ItemsA, !Env)
    ).

%-----------------------------------------------------------------------------%

:- pred impose_int_var_bounds_reif(error_context::in, int_range::in, var_id::in,
    env::in, env::out) is semidet.

impose_int_var_bounds_reif(Context, Bounds, Var, !Env) :-
    (
        Bounds = int_range_unbounded
    ;
        Bounds = int_range_lb_ub(LBB, UBB),
        LBA = !.Env ^ var_int_lb(Var),
        !Env ^ var_int_lb(Var) := int.max(LBA, LBB),
        UBA = !.Env ^ var_int_ub(Var),
        !Env ^ var_int_ub(Var) := int.min(UBA, UBB)
    ;
        Bounds = int_range_set(Set),
        ( if
            % JJJ - INTSET REPN.
            Xs = intset.to_sorted_list(Set),
            Xs = [LB | _],
            list.det_last(Xs, UB)
        then
            impose_int_var_bounds_reif(Context, int_range_lb_ub(LB, UB), Var,
                !Env)
        else
            false
        )
    ).

%-----------------------------------------------------------------------------%

:- pred impose_int_set_bounds_reif(error_context::in,
    int_range::in, int_set_expr::in, env::in, env::out) is semidet.

impose_int_set_bounds_reif(Context, Bounds, A, !Env) :-
    (
        (
            A = set_var(var_no_index(V))
        ;
            A = set_var(var_index(V, _))
        ),
        impose_int_set_var_bounds_reif(Context, Bounds, V, !Env)
    ;
        A = set_items(SetA),
        (
            Bounds = int_range_unbounded
        ;
            Bounds = int_range_lb_ub(LB, UB),
            ( if
                XsA = set.to_sorted_list(SetA),
                XsA = [LBA | _],
                list.det_last(XsA, UBA),
                LB =< LBA, UBA =< UB
            then
                true
            else
                false
            )
        ;
            Bounds = int_range_set(SetB),
            ( if intset.subset(from_set(SetA), SetB) then
                true
            else
                false
            )
        )
    ).

%-----------------------------------------------------------------------------%

:- pred impose_int_set_array_bounds_reif(error_context::in,
    int_range::in, int_set_array_expr::in, env::in, env::out) is semidet.

impose_int_set_array_bounds_reif(Context, Bounds, A, !Env) :-
    ( if Bounds = int_range_unbounded then
        true
    else
        (
            A = array_var(_, V),
            impose_int_set_var_bounds_reif(Context, Bounds, V, !Env)
        ;
            A = array_items(_, Xs),
            array.foldl(impose_int_set_bounds_reif(Context, Bounds), Xs, !Env)
        )
    ).

%-----------------------------------------------------------------------------%

    % XXX This is the same as impose_int_set_var bounds.
    %
:- pred impose_int_set_var_bounds_reif(error_context::in, int_range::in,
    var_id::in, env::in, env::out) is det.

impose_int_set_var_bounds_reif(Context, Bounds, Var, !Env) :-
    A = int_var(var_no_index(Var)),
    refine_int_bounds(Context, Bounds, A, !Env),
    (
        Bounds = int_range_unbounded
    ;
        Bounds = int_range_lb_ub(LBB, UBB),
        BoundsVar = !.Env ^ var_set_ub(Var),
        (
            BoundsVar = int_range_unbounded,
            !Env ^ var_set_ub(Var) := Bounds
        ;
            BoundsVar = int_range_lb_ub(LBA, UBA),
            !Env ^ var_set_ub(Var) :=
                int_range_lb_ub(int.max(LBA, LBB), int.min(UBA, UBB))
        ;
            BoundsVar = int_range_set(SetA),
            !Env ^ var_set_ub(Var) :=
                int_range_set(intset.intersection(SetA, intset(LBB, UBB)))
        )
    ;
        Bounds = int_range_set(SetB),
        BoundsVar = !.Env ^ var_set_ub(Var),
        (
            BoundsVar = int_range_unbounded,
            !Env ^ var_set_ub(Var) := Bounds
        ;
            BoundsVar = int_range_lb_ub(LBA, UBA),
            !Env ^ var_set_ub(Var) :=
                int_range_set(intset.intersection(SetB, intset(LBA, UBA)))
        ;
            BoundsVar = int_range_set(SetA),
            !Env ^ var_set_ub(Var) :=
                int_range_set(intset.intersection(SetA, SetB))
        )
    ).

%-----------------------------------------------------------------------------%

:- pred impose_float_le_reif(error_context::in,
    float_expr::in, float_expr::in, env::in, env::out) is semidet.

impose_float_le_reif(Context, A, B, !Env) :-
    ( if
        flatten_float_float_to_bool(Context, no_anns, ff2b_le, A, B, Z, !Env)
    then
        post_process_flatten_to_bool_reif(Context, Z, !Env)
    else
        minizinc_internal_error(Context, $pred, "flattening '<=' failed.\n")
    ).

:- pred impose_float_in_reif(error_context::in,
    float_expr::in, float_set_expr::in, env::in, env::out) is semidet.

impose_float_in_reif(Context, A, B, !Env) :-
    flatten_float_float_set_to_bool(Context, no_anns, ffs2b_in, A, B, BoolZ,
        !Env),
    post_process_flatten_to_bool_reif(Context, boolcv_const(BoolZ), !Env).

:- pred impose_int_le_reif(error_context::in,
    int_expr::in, int_expr::in, env::in, env::out) is semidet.

impose_int_le_reif(Context, A, B, !Env) :-
    ( if
        flatten_int_int_to_bool(Context, no_anns, ii2b_le, A, B, Z, !Env)
    then
        post_process_flatten_to_bool_reif(Context, Z, !Env)
    else
        minizinc_internal_error(Context, $pred, "flattening '<=' failed.\n")
    ).

:- pred impose_int_in_reif(error_context::in,
    int_expr::in, int_set_expr::in, env::in, env::out) is semidet.

impose_int_in_reif(Context, A, B, !Env) :-
    ( if
        flatten_int_int_set_to_bool(Context, no_anns, iis2b_in, A, B, Z, !Env)
    then
        post_process_flatten_to_bool_reif(Context, Z, !Env)
    else
        minizinc_internal_error(Context, $pred, "flattening 'in' failed.\n")
    ).

%-----------------------------------------------------------------------------%

:- pred post_process_flatten_to_bool_reif(error_context::in,
    bool_const_or_var::in, env::in, env::out) is semidet.

post_process_flatten_to_bool_reif(Context, Z, !Env) :-
    require_complete_switch [Z] (
        Z = boolcv_const(yes)
    ;
        Z = boolcv_const(no),
        false
    ;
        Z = boolcv_var(MZVar),
        ( if !.Env ^ reifying = reifying(ReifVars) then
            !Env ^ reifying := reifying([bool_var(MZVar) | ReifVars])
        else
            minizinc_internal_error(Context, $pred,
                "bool_var constraint in non-reifying context.\n")
        )
    ).

%-----------------------------------------------------------------------------%
:- end_module flatten.app.
%-----------------------------------------------------------------------------%
