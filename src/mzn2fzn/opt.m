%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2009 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Ralph Becket <rafe@csse.unimelb.edu.au>

%-----------------------------------------------------------------------------%
%
% FlatZinc Optimisation
%
% The flattening process makes a reasonable effort at optimising the
% resulting FlatZinc, however it will miss some opportunities because
% it is essentially a single-pass algorithm.
%
% This stage attempts to do more comprehensive optimisation of the
% resulting FlatZinc. In particular, it seeks to
%
% - remove all variables with known values;
% - remove all variables known to be aliases of other variables;
% - simplify FlatZinc constraints where possible given knowledge
%   of variable domains.
%
% This process is managed via these data structures:
%
% - GlobalVarMap, recording bounds and assignment information
%   for each variable;
% - VarIdToConstraintIds, mapping each variable to the set of constraint ids
%   corresponding to constraints featuring the variable;
% - IdsToConstraints, mapping each constraint id to the corresponding
%   constraint (we can infer from the constraint the set of variables on which
%   it depends);
% - Props, a set of propagation operations to be carried out;
% - AffectedConstraintIds, a set of affected constraint (ids) which need
%   to be reconsidered to see if further propagation is possible.
%
% A propagation operation is one of:
% - simplify scalar var bound to a constant
%   -- handled by substitution;
% - simplify equality of two variables
%   -- handled by substitution for one of the variables;
% - simplify due to bounds change of some variable.
%
% Each simplification removed from Props may change the dependent constraints
% and will add the dependent constraints to AffectedConstraintIds.
% Once Props is empty, the constraints listed in AffectedConstraintIds are
% checked to see if further propagation is possible, in which case the
% PropQueue is extended.
%
% This process repeats until a fixed point is reached.

:- module opt.
:- interface.

:- import_module types.

    % Propagate var/constant and var/var assignments through the model
    % (since the main flattening procedure is done in a single pass,
    % it is possible for it to miss these opportunities for optimisation).
    %
:- pred optimise_flatzinc(model::in, model::out) is det.

%-----------------------------------------------------------------------------%

:- implementation.

:- import_module errors.

:- import_module intset.
:- import_module zinc_common.

:- import_module array.
:- import_module bool.
:- import_module counter.
:- import_module float.
:- import_module int.
:- import_module list.
:- import_module map.
:- import_module maybe.
:- import_module set.
:- import_module set_tree234.

%-----------------------------------------------------------------------------%

:- type var_id_to_constraint_ids == map(var_id, constraint_ids).

:- type constraint_id_ctr == counter.

:- type constraint_id == int.

:- type constraint_ids == intset.

:- type id_to_constraint_map == map(constraint_id, mzn_constraint).

:- type affected_constraint_ids == intset.

%-----------------------------------------------------------------------------%

optimise_flatzinc(Model0, Model) :-
    some [!GlobalVarMap, !VarIdToConstraintIds, !IdsToConstraints,
        !ConstraintIdCtr, !Props, !AffectedConstraintIds, !MaybeSolveGoal]
    (
        Model0 = model(PredMap, !:GlobalVarMap, Constraints0,
            !:MaybeSolveGoal),

        !:ConstraintIdCtr = counter.init(1),
        !:VarIdToConstraintIds = map.init,
        !:IdsToConstraints = map.init,
        !:AffectedConstraintIds = intset.empty,
        propagator_set_init(!:Props),

        prepare_optimisation(Constraints0, !GlobalVarMap, !.ConstraintIdCtr, _,
            !VarIdToConstraintIds, !IdsToConstraints,
            !Props, !AffectedConstraintIds),
        optimise_to_fixed_point(!GlobalVarMap,
            !.VarIdToConstraintIds, _, !IdsToConstraints,
            !.Props, _, !.AffectedConstraintIds, _, !MaybeSolveGoal),
        recover_constraints(!.IdsToConstraints, Constraints),

        Model = model(PredMap, !.GlobalVarMap, Constraints, !.MaybeSolveGoal)
    ).

:- pred recover_constraints(id_to_constraint_map::in, mzn_constraint_set::out)
    is det.

recover_constraints(IdsToConstraints, Constraints) :-
    F = ( func(_Id, C, Cs) = set_tree234.insert(C, Cs) ),
    Constraints = map.foldl(F, IdsToConstraints, set_tree234.init).

%-----------------------------------------------------------------------------%
%
% Model simplification propagators.
%

    % These propagators only apply to scalar variables (i.e., not to arrays).
    %
:- type propagator
    --->    var_is_const(var_id, mzn_expr)
    ;       var_is_alias(var_id, var_id, mzn_expr) % (id, alias id, alias expr)
    ;       var_bnd_changed(var_id).

:- type propagator_set
    --->    propagator_set(
                list(propagator)
            ).

:- type propagators == propagator_set.

:- pred propagator_set_init(propagator_set::out) is det.

propagator_set_init(PSet) :-
    PSet = propagator_set([]).

:- pred propagator_set_is_empty(propagator_set::in) is semidet.

propagator_set_is_empty(PSet) :-
    PSet = propagator_set([]).

    % Return the next propagator to run.
    %
:- pred propagator_set_next(propagator::out,
    propagator_set::in, propagator_set::out) is semidet.

propagator_set_next(Prop, !PSet) :-
    !.PSet = propagator_set(Props),
    Props = [Prop | PropsPrime],
    !:PSet = propagator_set(PropsPrime).

%-----------------------------------------------------------------------------%

    % Process each FlatZinc constraint in preparation for optimisation.
    % Assign an id to each constraint.
    % Map the id to the constraint itself.
    % Add the constraint id to the var id-to-constraint id map.
    % Add the constraint id to the affected constraints set (so we
    % check each constraint at least once for simplification).
    % Add propagators for any scalar vars with known assignments.
    %
:- pred prepare_optimisation(mzn_constraint_set::in,
    global_var_map::in, global_var_map::out,
    constraint_id_ctr::in, constraint_id_ctr::out,
    var_id_to_constraint_ids::in, var_id_to_constraint_ids::out,
    id_to_constraint_map::in, id_to_constraint_map::out,
    propagators::in, propagators::out,
    affected_constraint_ids::in, affected_constraint_ids::out)
    is det.

prepare_optimisation(Constraints, !GlobalVarMap, !ConstraintIdCtr,
          !VarIdToConstraintIds, !IdsToConstraints,
          !Props, !AffectedConstraintIds) :-
    set_tree234.fold4(prepare_constraint, Constraints, !ConstraintIdCtr,
        !VarIdToConstraintIds, !IdsToConstraints, !AffectedConstraintIds),
    map.foldl(maybe_add_var_prop(!.GlobalVarMap), !.GlobalVarMap, !Props).

:- pred prepare_constraint(mzn_constraint::in,
    constraint_id_ctr::in, constraint_id_ctr::out,
    var_id_to_constraint_ids::in, var_id_to_constraint_ids::out,
    id_to_constraint_map::in, id_to_constraint_map::out,
    affected_constraint_ids::in, affected_constraint_ids::out)
    is det.

prepare_constraint(Constraint, !ConstraintIdCtr,
          !VarIdToConstraintIds, !IdsToConstraints, !AffectedConstraintIds) :-
    counter.allocate(ConstraintId, !ConstraintIdCtr),
    map.det_insert(ConstraintId, Constraint, !IdsToConstraints),
    connect_constraint_vars_to_constraint_id(ConstraintId, Constraint,
        !VarIdToConstraintIds),
    !:AffectedConstraintIds = intset.insert(ConstraintId,
        !.AffectedConstraintIds).

%-----------------------------------------------------------------------------%

    % Add an initial propagator for a var if it has a known scalar value
    % (we need to perform substitution on such variables in the constraints).
    %
:- pred maybe_add_var_prop(global_var_map::in, var_id::in, var_info::in,
    propagators::in, propagators::out) is det.

maybe_add_var_prop(GlobalVarMap, XVarId, XVarInfo, !Props) :-
    ( if
        % We only want to substitute for scalar variables with values.
        XVarInfo ^ vi_inst = var_is_var,
        XVarInfo ^ vi_index_ranges = IndexRanges,
        IndexRanges = [],
        XVarInfo ^ vi_type = XMZType,
        XVarInfo ^ vi_value = yes(YMZExpr)
    then
        XMZExpr = make_var_mzn_expr(IndexRanges, XMZType, XVarId),
        add_eq_propagator(GlobalVarMap, XMZExpr, YMZExpr, !Props)
    else
        % Nothing to do here.
        true
    ).

%-----------------------------------------------------------------------------%

:- pred add_propagator(propagator::in,
    propagators::in, propagators::out) is det.

add_propagator(Prop, !PSet) :-
    !.PSet = propagator_set(Props),
    !:PSet = propagator_set([Prop | Props]).

%-----------------------------------------------------------------------------%

:- pred mzn_expr_is_scalar_var(mzn_expr::in, var_id::out) is semidet.

mzn_expr_is_scalar_var(MZExpr, VarId) :-
    MZExpr = mzn_expr(RawMZExpr, _MZAnns),
    ( RawMZExpr = bool_expr(bool_var(MZVar))
    ; RawMZExpr = bool_set_expr(set_var(MZVar))
    ; RawMZExpr = float_expr(float_var(MZVar))
    ; RawMZExpr = int_expr(int_var(MZVar))
    ; RawMZExpr = int_set_expr(set_var(MZVar))
    ),
    MZVar = var_no_index(VarId).

%-----------------------------------------------------------------------------%

:- pred mzn_expr_is_scalar_const(mzn_expr::in) is semidet.

mzn_expr_is_scalar_const(MZExpr) :-
    MZExpr = mzn_expr(RawMZExpr, _MZAnns),
    ( RawMZExpr = bool_expr(bool_const(_))
    ; RawMZExpr = bool_set_expr(set_items(_))
    ; RawMZExpr = float_expr(float_const(_))
    ; RawMZExpr = int_expr(int_const(_))
    ; RawMZExpr = int_set_expr(set_items(_))
    ; RawMZExpr = bool_expr(bool_var(var_index(_, _)))
    ; RawMZExpr = bool_set_expr(set_var(var_index(_, _)))
    ; RawMZExpr = float_expr(float_var(var_index(_, _)))
    ; RawMZExpr = int_expr(int_var(var_index(_, _)))
    ; RawMZExpr = int_set_expr(set_var(var_index(_, _)))
    ).

%-----------------------------------------------------------------------------%

    % Traverse a constraint adding connections from variables in the
    % constraint to the constraint id.
    %
:- pred connect_constraint_vars_to_constraint_id(constraint_id::in,
    mzn_constraint::in,
    var_id_to_constraint_ids::in, var_id_to_constraint_ids::out) is det.

connect_constraint_vars_to_constraint_id(ConstraintId, Constraint,
        !VarIdToConstraintIds) :-
    Constraint = mzn_constraint(_Name, Args, MZAnns),
    connect_anns_vars_to_constraint_id(ConstraintId, MZAnns,
        !VarIdToConstraintIds),
    connect_exprs_vars_to_constraint_id(ConstraintId, Args,
        !VarIdToConstraintIds).

%-----------------------------------------------------------------------------%

:- pred connect_anns_vars_to_constraint_id(constraint_id::in, mzn_anns::in,
    var_id_to_constraint_ids::in, var_id_to_constraint_ids::out) is det.

connect_anns_vars_to_constraint_id(ConstraintId, MZAnns,
        !VarIdToConstraintIds) :-
    set.fold(connect_ann_vars_to_constraint_id(ConstraintId), MZAnns,
        !VarIdToConstraintIds).

%-----------------------------------------------------------------------------%

:- pred connect_ann_vars_to_constraint_id(constraint_id::in, mzn_ann::in,
    var_id_to_constraint_ids::in, var_id_to_constraint_ids::out) is det.

connect_ann_vars_to_constraint_id(ConstraintId, mzn_ann_var(MZVar),
        !VarIdToConstraintIds) :-
    connect_var_to_constraint_id(ConstraintId, MZVar,
        !VarIdToConstraintIds).
connect_ann_vars_to_constraint_id(ConstraintId, mzn_ann(_Name, MZArgs),
        !VarIdToConstraintIds) :-
    connect_exprs_vars_to_constraint_id(ConstraintId, MZArgs,
        !VarIdToConstraintIds).

%-----------------------------------------------------------------------------%

:- pred connect_exprs_vars_to_constraint_id(constraint_id::in, mzn_exprs::in,
    var_id_to_constraint_ids::in, var_id_to_constraint_ids::out) is det.

connect_exprs_vars_to_constraint_id(ConstraintId, MZExprs,
        !VarIdToConstraintIds) :-
    list.foldl(connect_expr_vars_to_constraint_id(ConstraintId), MZExprs,
        !VarIdToConstraintIds).

%-----------------------------------------------------------------------------%

:- pred connect_expr_vars_to_constraint_id(constraint_id::in, mzn_expr::in,
    var_id_to_constraint_ids::in, var_id_to_constraint_ids::out) is det.

connect_expr_vars_to_constraint_id(ConstraintId, MZExpr,
        !VarIdToConstraintIds) :-
    MZExpr = mzn_expr(RawMZExpr, MZAnns),
    connect_raw_expr_vars_to_constraint_id(ConstraintId, RawMZExpr,
        !VarIdToConstraintIds),
    connect_anns_vars_to_constraint_id(ConstraintId, MZAnns,
        !VarIdToConstraintIds).

%-----------------------------------------------------------------------------%

:- pred connect_raw_expr_vars_to_constraint_id(constraint_id::in,
    mzn_raw_expr::in,
    var_id_to_constraint_ids::in, var_id_to_constraint_ids::out) is det.

connect_raw_expr_vars_to_constraint_id(ConstraintId, RawMZExpr,
        !VarIdToConstraintIds) :-
    (
        RawMZExpr = bool_expr(A),
        connect_bool_expr_to_constraint_id(ConstraintId, A,
            !VarIdToConstraintIds)
    ;
        RawMZExpr = bool_set_expr(A),
        connect_set_expr_to_constraint_id(ConstraintId, A,
            !VarIdToConstraintIds)
    ;
        RawMZExpr = bool_array_expr(A),
        connect_array_vars_to_constraint_id(ConstraintId, A,
            connect_bool_expr_to_constraint_id(ConstraintId),
            !VarIdToConstraintIds)
    ;
        RawMZExpr = bool_set_array_expr(A),
        connect_array_vars_to_constraint_id(ConstraintId, A,
            connect_set_expr_to_constraint_id(ConstraintId),
            !VarIdToConstraintIds)
    ;
        RawMZExpr = float_expr(A),
        connect_float_expr_to_constraint_id(ConstraintId, A,
            !VarIdToConstraintIds)
    ;
        RawMZExpr = float_set_expr(A),
        connect_set_expr_to_constraint_id(ConstraintId, A,
            !VarIdToConstraintIds)
    ;
        RawMZExpr = float_array_expr(A),
        connect_array_vars_to_constraint_id(ConstraintId, A,
            connect_float_expr_to_constraint_id(ConstraintId),
            !VarIdToConstraintIds)
    ;
        RawMZExpr = float_set_array_expr(A),
        connect_array_vars_to_constraint_id(ConstraintId, A,
            connect_set_expr_to_constraint_id(ConstraintId),
            !VarIdToConstraintIds)
    ;
        RawMZExpr = int_expr(A),
        connect_int_expr_to_constraint_id(ConstraintId, A,
            !VarIdToConstraintIds)
    ;
        RawMZExpr = int_set_expr(A),
        connect_set_expr_to_constraint_id(ConstraintId, A,
            !VarIdToConstraintIds)
    ;
        RawMZExpr = int_array_expr(A),
        connect_array_vars_to_constraint_id(ConstraintId, A,
            connect_int_expr_to_constraint_id(ConstraintId),
            !VarIdToConstraintIds)
    ;
        RawMZExpr = int_set_array_expr(A),
        connect_array_vars_to_constraint_id(ConstraintId, A,
            connect_set_expr_to_constraint_id(ConstraintId),
            !VarIdToConstraintIds)
    ;
        RawMZExpr = ann_expr(A),
        connect_ann_vars_to_constraint_id(ConstraintId, A,
            !VarIdToConstraintIds)
    ;
        RawMZExpr = ann_array_expr(A),
        connect_array_vars_to_constraint_id(ConstraintId, A,
            connect_ann_vars_to_constraint_id(ConstraintId),
            !VarIdToConstraintIds)
    ;
        ( RawMZExpr = string_expr(_)
        ; RawMZExpr = string_array_expr(_)
        )
    ;
        ( RawMZExpr = bottom_expr(_)
        ; RawMZExpr = bottom_array_expr(_)
        ),
        report_unexpected_non_flatzinc_expr($pred)
    ).

%-----------------------------------------------------------------------------%

:- pred connect_set_expr_to_constraint_id(constraint_id::in, set_expr(T)::in,
    var_id_to_constraint_ids::in, var_id_to_constraint_ids::out) is det.

connect_set_expr_to_constraint_id(ConstraintId, A, !VarIdToConstraintIds) :-
    (
        A = set_items(_)
    ;
        A = set_var(MZVar),
        connect_var_to_constraint_id(ConstraintId, MZVar,
            !VarIdToConstraintIds)
    ).

%-----------------------------------------------------------------------------%

:- pred connect_array_vars_to_constraint_id(constraint_id::in,
    array_expr(T)::in,
    pred(T, var_id_to_constraint_ids, var_id_to_constraint_ids) ::
        in(pred(in, in, out) is det),
    var_id_to_constraint_ids::in, var_id_to_constraint_ids::out) is det.

connect_array_vars_to_constraint_id(ConstraintId, A, P,
        !VarIdToConstraintIds) :-
    (
        A = array_items(_IndexRanges, Bs),
        array.foldl(P, Bs, !VarIdToConstraintIds)
    ;
        A = array_var(_IndexRanges, VarId),
        connect_var_id_to_constraint_id(ConstraintId, VarId,
            !VarIdToConstraintIds)
    ).

%-----------------------------------------------------------------------------%

:- pred connect_bool_expr_to_constraint_id(constraint_id::in, bool_expr::in,
    var_id_to_constraint_ids::in, var_id_to_constraint_ids::out) is det.

connect_bool_expr_to_constraint_id(ConstraintId, A, !VarIdToConstraintIds) :-
    (
        A = bool_const(_)
    ;
        A = bool_var(MZVar),
        connect_var_to_constraint_id(ConstraintId, MZVar,
            !VarIdToConstraintIds)
    ;
        A = bool_conj(_),
        report_unexpected_non_flatzinc_expr(
            "connect_bool_expr_to_constraint_id")
    ;
        A = bool_disj(_),
        report_unexpected_non_flatzinc_expr(
            "connect_bool_expr_to_constraint_id")
    ).

%-----------------------------------------------------------------------------%

:- pred connect_float_expr_to_constraint_id(constraint_id::in, float_expr::in,
    var_id_to_constraint_ids::in, var_id_to_constraint_ids::out) is det.

connect_float_expr_to_constraint_id(ConstraintId, A, !VarIdToConstraintIds) :-
    (
        A = float_const(_)
    ;
        A = float_var(MZVar),
        connect_var_to_constraint_id(ConstraintId, MZVar,
            !VarIdToConstraintIds)
    ;
        A = (_ + _),
        report_unexpected_non_flatzinc_expr(
            "connect_float_expr_to_constraint_id")
    ;
        A = (_ * _),
        report_unexpected_non_flatzinc_expr(
            "connect_float_expr_to_constraint_id")
    ).

%-----------------------------------------------------------------------------%

:- pred connect_int_expr_to_constraint_id(constraint_id::in, int_expr::in,
    var_id_to_constraint_ids::in, var_id_to_constraint_ids::out) is det.

connect_int_expr_to_constraint_id(ConstraintId, A, !VarIdToConstraintIds) :-
    (
        A = int_const(_)
    ;
        A = int_var(MZVar),
        connect_var_to_constraint_id(ConstraintId, MZVar,
            !VarIdToConstraintIds)
    ;
        A = (_ + _),
        report_unexpected_non_flatzinc_expr(
            "connect_int_expr_to_constraint_id")
    ;
        A = (_ * _),
        report_unexpected_non_flatzinc_expr(
            "connect_int_expr_to_constraint_id")
    ).

%-----------------------------------------------------------------------------%

:- pred connect_var_to_constraint_id(constraint_id::in, mzn_var::in,
    var_id_to_constraint_ids::in, var_id_to_constraint_ids::out) is det.

connect_var_to_constraint_id(ConstraintId, MZVar, !VarIdToConstraintIds) :-
    VarId = mzn_var_id(MZVar),
    connect_var_id_to_constraint_id(ConstraintId, VarId,
        !VarIdToConstraintIds).

%-----------------------------------------------------------------------------%

:- pred connect_var_id_to_constraint_id(constraint_id::in, var_id::in,
    var_id_to_constraint_ids::in, var_id_to_constraint_ids::out) is det.

connect_var_id_to_constraint_id(ConstraintId, VarId, !VarIdToConstraintIds) :-
    ( if map.search(!.VarIdToConstraintIds, VarId, ConstraintIds) then
        map.det_update(VarId, intset.insert(ConstraintId, ConstraintIds),
            !VarIdToConstraintIds)
    else
        map.det_insert(VarId, intset.singleton(ConstraintId),
            !VarIdToConstraintIds)
    ).

%-----------------------------------------------------------------------------%

:- pred optimise_to_fixed_point(global_var_map::in, global_var_map::out,
    var_id_to_constraint_ids::in, var_id_to_constraint_ids::out,
    id_to_constraint_map::in, id_to_constraint_map::out,
    propagators::in, propagators::out,
    affected_constraint_ids::in, affected_constraint_ids::out,
    maybe(mzn_solve_goal)::in, maybe(mzn_solve_goal)::out) is det.

optimise_to_fixed_point(!GlobalVarMap, !VarIdToConstraintIds,
        !IdsToConstraints, !Props, !AffectedConstraintIds, !SolveGoal) :-
    ( if
        propagator_set_is_empty(!.Props),
        !.AffectedConstraintIds = intset.empty
    then
        % We have reached the fixed point.
        true
    else
        % Run all the propagators.
        run_propagators(!GlobalVarMap, !VarIdToConstraintIds,
            !IdsToConstraints, !Props, !AffectedConstraintIds, !SolveGoal),
        % Reconsider all affected constraints.
        reconsider_affected_constraints(!GlobalVarMap, !IdsToConstraints,
            !Props, !AffectedConstraintIds),
        % And go around the loop again.
        optimise_to_fixed_point(!GlobalVarMap, !VarIdToConstraintIds,
            !IdsToConstraints, !Props, !AffectedConstraintIds, !SolveGoal)
    ).

    % XXX FILL THIS IN!
    %
:- pred reconsider_affected_constraints(
    global_var_map::in, global_var_map::out,
    id_to_constraint_map::in, id_to_constraint_map::out,
    propagators::in, propagators::out,
    affected_constraint_ids::in, affected_constraint_ids::out) is det.

reconsider_affected_constraints(!GlobalVarMap, !IdsToConstraints, !Props,
        !AffectedConstraintIds) :-
    !.AffectedConstraintIds = _,
    !:AffectedConstraintIds = intset.empty.

%-----------------------------------------------------------------------------%

:- pred run_propagators(global_var_map::in, global_var_map::out,
    var_id_to_constraint_ids::in, var_id_to_constraint_ids::out,
    id_to_constraint_map::in, id_to_constraint_map::out,
    propagators::in, propagators::out,
    affected_constraint_ids::in, affected_constraint_ids::out,
    maybe(mzn_solve_goal)::in, maybe(mzn_solve_goal)::out) is det.

run_propagators(!GlobalVarMap, !VarIdToConstraintIds, !IdsToConstraints,
        !Props, !AffectedConstraintIds, !SolveGoal) :-
    ( if propagator_set_next(Prop, !Props) then
        (
            Prop = var_is_const(VarId, MZExpr),
            ( if map.search(!.VarIdToConstraintIds, VarId, ConstraintIds0) then
                ConstraintIds = ConstraintIds0
            else
                ConstraintIds = intset.empty
            ),
            propagate_var_is_const(VarId, MZExpr, ConstraintIds,
                !GlobalVarMap, !IdsToConstraints, !Props, !SolveGoal)
        ;
            Prop = var_is_alias(VarId, AliasVarId, AliasMZExpr),
            ( if map.search(!.VarIdToConstraintIds, VarId, ConstraintIds0) then
                ConstraintIds = ConstraintIds0
            else
                ConstraintIds = intset.empty
            ),
            propagate_var_is_alias(VarId, AliasVarId, AliasMZExpr,
                ConstraintIds, !GlobalVarMap,
                !VarIdToConstraintIds,!IdsToConstraints, !Props, !SolveGoal)
        ;
            Prop = var_bnd_changed(VarId),
            ( if map.search(!.VarIdToConstraintIds, VarId, ConstraintIds0) then
                ConstraintIds = ConstraintIds0
            else
                ConstraintIds = intset.empty
            )
            % In this case we only need to reconsider the affected constraints,
            % which is handled below.
        ),

        % Update the set of affected constraints.
        !:AffectedConstraintIds = intset.union(ConstraintIds,
            !.AffectedConstraintIds),

        % Repeat until we've handled all the current propagators.
        run_propagators(!GlobalVarMap, !VarIdToConstraintIds,
            !IdsToConstraints, !Props, !AffectedConstraintIds, !SolveGoal)
    else
        true
    ).

%-----------------------------------------------------------------------------%

    % Var X has constant value A.
    % Substitute A for X in all constraints.
    % If X is already assigned constant B, verify that A = B.
    % If X aliases Y, propagate that Y has constant value A.
    % If X is unbound, assign it A (checking that X's bounds are consistent
    % and appropriately refined if necessary).
    % If X is an introduced variable, we remove it completely from the model.
    % NOTE: remember to remove defines_var(X) annotations from constraints
    % in this case.
    %
:- pred propagate_var_is_const(var_id::in, mzn_expr::in, constraint_ids::in,
    global_var_map::in, global_var_map::out,
    id_to_constraint_map::in, id_to_constraint_map::out,
    propagators::in, propagators::out,
    maybe(mzn_solve_goal)::in, maybe(mzn_solve_goal)::out) is det.

propagate_var_is_const(VarId, MZExpr, ConstraintIds, !GlobalVarMap,
        !IdsToConstraints, !Props, !SolveGoal) :-
    ( if
        map.search(!.GlobalVarMap, VarId, VarInfo0)
    then
        MZExpr = mzn_expr(RawMZExpr, _MZAnns),

        % Check the binding status of this variable.
        ( if VarInfo0 ^ vi_value = yes(CurrentMZExpr) then
            add_eq_propagator(!.GlobalVarMap, MZExpr, CurrentMZExpr, !Props)
        else
            true
        ),

        % Check the bounds on the variable against the value.
        VarBounds0 = VarInfo0 ^ vi_bounds,
        ( if
            RawMZExpr = float_expr(float_const(X))
        then
            ( if
                VarBounds0 = float_bounds(LB, UB),
                LB =< X,
                X =< UB
              then
                VarInfo1 = VarInfo0 ^ vi_bounds := float_bounds(X, X),
                VarInfo  = VarInfo1 ^ vi_value := yes(MZExpr),
                map.det_update(VarId, VarInfo, !GlobalVarMap)
              else
                report_model_inconsistency_detected
            )
        else if
            RawMZExpr = int_expr(int_const(X))
        then
            ( if
                (
                    VarBounds0 = int_bounds(LB, UB),
                    LB =< X,
                    X =< UB,
                    VarBounds = int_bounds(X, X)
                ;
                    VarBounds0 = int_set_bounds(Set),
                    intset.member(X, Set),
                    VarBounds = int_set_bounds(intset.singleton(X))
                )
            then
                VarInfo1 = VarInfo0 ^ vi_bounds := VarBounds,
                VarInfo  = VarInfo1 ^ vi_value := yes(MZExpr),
                map.det_update(VarId, VarInfo, !GlobalVarMap)
            else
                report_model_inconsistency_detected
            )
        else if
            RawMZExpr = int_set_expr(set_items(Xs0))
        then
            % JJJ FIXME - SET REP.
            % XXX if-then-else is reversed
            Xs = intset.from_set(Xs0),
            ( if
                VarBounds0 = int_set_bounds(Set),
                not intset.subset(Xs, Set)
            then
                report_model_inconsistency_detected
            else
                VarInfo1 = VarInfo0 ^ vi_bounds := int_set_bounds(Xs),
                VarInfo  = VarInfo1 ^ vi_value := yes(MZExpr),
                map.det_update(VarId, VarInfo, !GlobalVarMap)
            )
        else
            % We don't need to worry about bounds.
            VarInfo = VarInfo0 ^ vi_value := yes(MZExpr),
            map.det_update(VarId, VarInfo, !GlobalVarMap)
        ),

        % Apply the substitution.
        substitute_var_with_expr(VarId, MZExpr, ConstraintIds, !GlobalVarMap,
            !IdsToConstraints, !Props, !SolveGoal)
    else
        % This var has already been removed.
        true
    ).

    % Substitute an expression for a variable throughout the model.
    %
:- pred substitute_var_with_expr(var_id::in, mzn_expr::in, constraint_ids::in,
    global_var_map::in, global_var_map::out,
    id_to_constraint_map::in, id_to_constraint_map::out,
    propagators::in, propagators::out,
    maybe(mzn_solve_goal)::in, maybe(mzn_solve_goal)::out) is det.

substitute_var_with_expr(VarId, MZExpr, ConstraintIds, !GlobalVarMap,
        !IdsToConstraints, !Props, !SolveGoal) :-
    % Don't apply the substitution if the replacement is for a variable
    % that no longer exists (i.e., has already been optimised away).
    ( if
        mzn_expr_is_scalar_var(MZExpr, AliasVarId),
        not map.contains(!.GlobalVarMap, AliasVarId)
    then
        true
    else
        % Apply the substitution to the constraints.
        intset_elems_foldl(substitute_for_var(VarId, MZExpr), ConstraintIds,
            !IdsToConstraints),

        % Apply the substitution to the globals (removing the var
        % if it was introduced during flattening).
        substitute_for_var_in_globals(VarId, MZExpr, !GlobalVarMap, !Props),

        % Apply the substitution to the solve goal.
        (
            !.SolveGoal = no
        ;
            !.SolveGoal = yes(MZSolveGoal0),
            MZSolveGoal0 = mzn_solve_goal(GoalMZAnns0, SolveKind0),
            substitute_for_var_in_anns(VarId, MZExpr, GoalMZAnns0, GoalMZAnns),
            (
                SolveKind0 = mzn_solve_satisfy,
                SolveKind = mzn_solve_satisfy
            ;
                SolveKind0 = mzn_solve_minimize(GoalMZExpr0),
                substitute_for_var_in_expr(VarId, MZExpr,
                    GoalMZExpr0, GoalMZExpr),
                SolveKind = mzn_solve_minimize(GoalMZExpr)
            ;
                SolveKind0 = mzn_solve_maximize(GoalMZExpr0),
                substitute_for_var_in_expr(VarId, MZExpr,
                    GoalMZExpr0, GoalMZExpr),
                SolveKind = mzn_solve_maximize(GoalMZExpr)
            ),
            MZSolveGoal = mzn_solve_goal(GoalMZAnns, SolveKind),
            !:SolveGoal = yes(MZSolveGoal)
        )
    ).

%-----------------------------------------------------------------------------%

    % Var X aliases var Y.
    %
:- pred propagate_var_is_alias(var_id::in, var_id::in, mzn_expr::in,
    constraint_ids::in, global_var_map::in, global_var_map::out,
    var_id_to_constraint_ids::in, var_id_to_constraint_ids::out,
    id_to_constraint_map::in, id_to_constraint_map::out,
    propagators::in, propagators::out,
    maybe(mzn_solve_goal)::in, maybe(mzn_solve_goal)::out) is det.

propagate_var_is_alias(XVarId, YVarId, YMZExpr, ConstraintIds, !GlobalVarMap,
        !VarIdToConstraintIds, !IdsToConstraints, !Props, !SolveGoal) :-
    ( if
        map.search(!.GlobalVarMap, XVarId, XVarInfo0),
        map.search(!.GlobalVarMap, YVarId, YVarInfo0)
    then
        % Check the bounds on the variables.
        XVarBounds0 = XVarInfo0 ^ vi_bounds,
        YVarBounds0 = YVarInfo0 ^ vi_bounds,

        YMZExpr = mzn_expr(YRawMZExpr, _YAnns),
        ( if
            YRawMZExpr = float_expr(_)
        then
            get_float_bounds(XVarBounds0, XLB, XUB),
            get_float_bounds(YVarBounds0, YLB, YUB),
            LB = float.max(XLB, YLB),
            UB = float.min(XUB, YUB),
            ( if LB =< UB then
                VarBounds = float_bounds(LB, UB),
                XVarInfo  = XVarInfo0 ^ vi_bounds := VarBounds,
                YVarInfo  = YVarInfo0 ^ vi_bounds := VarBounds,
                map.det_update(XVarId, XVarInfo, !GlobalVarMap),
                map.det_update(YVarId, YVarInfo, !GlobalVarMap)
            else
                report_model_inconsistency_detected
            )
        else if
            YRawMZExpr = int_expr(_)
        then
            get_int_bounds(XVarBounds0, XLB, XUB),
            get_int_bounds(YVarBounds0, YLB, YUB),
            LB = int.max(XLB, YLB),
            UB = int.min(XUB, YUB),
            ( if
                LB =< UB
            then
                % XXX We lose information if either was int_set_bounds.
                VarBounds = int_bounds(LB, UB),
                XVarInfo  = XVarInfo0 ^ vi_bounds := VarBounds,
                YVarInfo  = YVarInfo0 ^ vi_bounds := VarBounds,
                map.det_update(XVarId, XVarInfo, !GlobalVarMap),
                map.det_update(YVarId, YVarInfo, !GlobalVarMap)
            else
                report_model_inconsistency_detected
            )
        else if
            YRawMZExpr = int_set_expr(_)
        then
            ( if
                ( if XVarBounds0 = int_set_bounds(XSet0) then
                    XSet = XSet0
                else
                    XVarInfo0 ^ vi_type = mzn_int_set(XRange),
                    XRange = int_range_lb_ub(XMin, XMax),
                    XSet = intset(XMin, XMax)
                ),
                ( if YVarBounds0 = int_set_bounds(YSet0) then
                    YSet = YSet0
                else
                    YVarInfo0 ^ vi_type = mzn_int_set(YRange),
                    YRange = int_range_lb_ub(YMin, YMax),
                    YSet = intset(YMin, YMax)
                )
            then
                Set = intset.intersection(XSet, YSet),
                VarBounds = int_set_bounds(Set),
                XVarInfo  = XVarInfo0 ^ vi_bounds := VarBounds,
                YVarInfo  = YVarInfo0 ^ vi_bounds := VarBounds,
                map.det_update(XVarId, XVarInfo, !GlobalVarMap),
                map.det_update(YVarId, YVarInfo, !GlobalVarMap)
            else
                % One of the sets is unbounded...
                % XXX So? If the other is bounded, we should give its bounds
                % to the other one. The float_expr and int_expr cases set both
                % vars to the intersection of X and Y's bounds, and so does the
                % int_set_expr case if both vars are bounded; why should we let
                % one of the vars keep the union of the two old bounds in this
                % one case?

                true
            )
        else
            % We don't need to worry about bounds.
            true
        ),
        % Now apply the substitution.
        (
            XVarInfo0 ^ vi_value = yes(XMZExpr),
            % Substitute for X...
            substitute_var_with_expr(XVarId, YMZExpr, ConstraintIds,
                !GlobalVarMap, !IdsToConstraints, !Props, !SolveGoal),
            % ...then handle the value bound to X.
            add_eq_propagator(!.GlobalVarMap, XMZExpr, YMZExpr, !Props)
        ;
            XVarInfo0 ^ vi_value = no,
            % X has no assigned value, the substitution is straightforward.
            substitute_var_with_expr(XVarId, YMZExpr, ConstraintIds,
                !GlobalVarMap, !IdsToConstraints, !Props, !SolveGoal)
        ),

        % We now need to update the var id -> constraint ids map for YVarId,
        % so that any future propagators involving YVarId will be applied to
        % all the constraints containing it.
        %
        ( if map.search(!.VarIdToConstraintIds, YVarId, YConstraintIds0) then
            YConstraintIds = intset.union(ConstraintIds, YConstraintIds0),
            map.det_update(YVarId, YConstraintIds, !VarIdToConstraintIds)
        else
            map.det_insert(YVarId, ConstraintIds, !VarIdToConstraintIds)
        )

    else
        true % One or both of these vars has already been removed.
    ).

%-----------------------------------------------------------------------------%

:- pred add_eq_propagator(global_var_map::in, mzn_expr::in, mzn_expr::in,
    propagators::in, propagators::out) is det.

add_eq_propagator(GlobalVarMap, XMZExpr, YMZExpr, !Props) :-
    ( if XMZExpr = YMZExpr then
        % Waste no time here!
        true
    else if
        (
            mzn_expr_is_scalar_var(XMZExpr, XVarId),
            not map.contains(GlobalVarMap, XVarId)
        ;
            mzn_expr_is_scalar_var(YMZExpr, YVarId),
            not map.contains(GlobalVarMap, YVarId)
        )
    then
        % We've already removed one or both of these variables.
        true
    else if mzn_expr_is_scalar_const(XMZExpr) then
        % X is not a variable, so is not a candidate for replacement.
        ( if mzn_expr_is_scalar_var(YMZExpr, YVarId) then
            add_propagator(var_is_const(YVarId, XMZExpr), !Props)
        else
            % Nothing to do here.
            true
        )
    else if
        mzn_expr_is_scalar_var(XMZExpr, XVarId),
        map.lookup(GlobalVarMap, XVarId, XVarInfo),
        XVarInfo ^ vi_output = var_is_not_output
    then
        % X is a variable and therefore a candidate for replacement,
        % except if it is an output variable.
        ( if mzn_expr_is_scalar_var(YMZExpr, YVarId) then
            % Y is a variable. Replace a temporary if possible.
            ( if
                XVarInfo ^ vi_kind = var_is_temporary
            then
                add_propagator(var_is_alias(XVarId, YVarId, YMZExpr), !Props)
            else if
                map.lookup(GlobalVarMap, YVarId, YVarInfo),
                YVarInfo ^ vi_output = var_is_not_output
            then
                add_propagator(var_is_alias(YVarId, XVarId, XMZExpr), !Props)
            else
                true
            )
        else
            % Y is a constant, so we replace X with Y.
            add_propagator(var_is_const(XVarId, YMZExpr), !Props)
        )
    else
        % X is neither fish nor fowl.
        % minizinc_internal_error([], $pred, "X has unexpected form")
        true
    ).

%-----------------------------------------------------------------------------%

    % Substitute an expression for a variable in the global assignments
    % by adding propagators where necessary.
    % Remove the variable altogether if the variable was introduced during
    % flattening.
    %
:- pred substitute_for_var_in_globals(var_id::in, mzn_expr::in,
    global_var_map::in, global_var_map::out,
    propagators::in, propagators::out) is det.

substitute_for_var_in_globals(VarId, MZExpr, !GlobalVarMap, !Props) :-
    ( if
        % Remove this var's value entry if either
        % - MZExpr is just a wrapper around VarId or
        % - MZExpr denotes a var that has been removed.
        mzn_expr_is_scalar_var(MZExpr, AliasVarId),
        (
            AliasVarId = VarId
        ;
            not map.contains(!.GlobalVarMap, AliasVarId)
        )
    then
        map.lookup(!.GlobalVarMap, VarId, VarInfo0),
        VarInfo = VarInfo0 ^ vi_value := no,
        map.det_update(VarId, VarInfo, !GlobalVarMap)
    else if
        % Remove this variable from the globals if it is an introduced
        % variable with a (different) value AND the replacement variable
        % has bounds that are at least as tight.
        map.search(!.GlobalVarMap, VarId, VarInfo0),
        VarInfo0 ^ vi_kind = var_is_temporary,
        not var_bounds_are_tighter_than_var_expr_bounds(!.GlobalVarMap,
            VarId, MZExpr)
    then
        map.delete(VarId, !GlobalVarMap),
        % And perform the substitution in the other variables.
        map.foldl(substitute_for_var_in_global(VarId, MZExpr),
            !.GlobalVarMap, !GlobalVarMap)
    else
        % Perform the substitution in the other variables.
        map.foldl(substitute_for_var_in_global(VarId, MZExpr),
            !.GlobalVarMap, !GlobalVarMap)
    ).

%-----------------------------------------------------------------------------%

:- pred var_bounds_are_tighter_than_var_expr_bounds(global_var_map::in,
    var_id::in, mzn_expr::in) is semidet.

var_bounds_are_tighter_than_var_expr_bounds(GlobalVarMap, XVarId, YMZExpr) :-
    map.search(GlobalVarMap, XVarId, XVarInfo),
    YMZExpr = mzn_expr(YRawMZExpr, _YAnns),
    (
        (
            YRawMZExpr = float_expr(float_var(YRawMZVar)),
            YVarId = mzn_var_id(YRawMZVar)
        ;
            YRawMZExpr = float_array_expr(array_var(_IndexRanges, YVarId))
        ),
        map.search(GlobalVarMap, YVarId, YVarInfo),
        get_float_bounds(XVarInfo ^ vi_bounds, XLB, XUB),
        get_float_bounds(YVarInfo ^ vi_bounds, YLB, YUB),
        (
            YLB < XLB
        ;
            XUB < YUB
        )
    ;
        (
            YRawMZExpr = int_expr(int_var(YRawMZVar)),
            YVarId = mzn_var_id(YRawMZVar)
        ;
            YRawMZExpr = int_array_expr(array_var(_IndexRanges, YVarId))
        ),
        map.search(GlobalVarMap, YVarId, YVarInfo),
        get_int_bounds(XVarInfo ^ vi_bounds, XLB, XUB),
        get_int_bounds(YVarInfo ^ vi_bounds, YLB, YUB),
        (
            YLB < XLB
        ;
            XUB < YUB
        )
    ;
        (
            YRawMZExpr = int_set_expr(set_var(YMZVar)),
            YVarId = mzn_var_id(YMZVar)
        ;
            YRawMZExpr = int_set_array_expr(array_var(_IndexRanges, YVarId))
        ),
        map.search(GlobalVarMap, YVarId, YVarInfo),
        ( if XVarInfo ^ vi_bounds = int_set_bounds(XSet) then
            ( if YVarInfo ^ vi_bounds = int_set_bounds(YSet) then
                not intset.subset(XSet, YSet)
            else
                not (
                    get_int_bounds(YVarInfo ^ vi_bounds, YMin, YMax),
                    YMax - YMin =< 1000, % Limit the set we might manifest.
                    intset.subset(XSet, intset(YMin, YMax))
                )
            )
        else
            ( if YVarInfo ^ vi_bounds = int_set_bounds(YSet) then
                get_int_bounds(XVarInfo ^ vi_bounds, XMin, XMax),
                not (
                    XMax - XMin =< 1000, % Limit the set we might manifest.
                    intset.subset(intset(XMin, XMax), YSet)
                )
            else
                get_int_bounds(XVarInfo ^ vi_bounds, XMin, XMax),
                get_int_bounds(YVarInfo ^ vi_bounds, YMin, YMax),
                (
                    YMin < XMin
                ;
                    XMax < YMax
                )
            )
        )
    ).

%-----------------------------------------------------------------------------%

:- pred substitute_for_var_in_global(var_id::in, mzn_expr::in,
    var_id::in, var_info::in, global_var_map::in, global_var_map::out) is det.

substitute_for_var_in_global(VarId, MZExpr, GlobalVarId, GlobalVarInfo0,
        !GlobalVarMap) :-
    % XXX Calling this predicate using map.foldl seems wasteful;
    % using map.map_values would seem more efficient.
    ( if
        GlobalVarInfo0 ^ vi_inst = var_is_var,
        GlobalVarInfo0 ^ vi_value = yes(GlobalMZExpr0),
        substitute_for_var_in_expr(VarId, MZExpr, GlobalMZExpr0, GlobalMZExpr),
        GlobalMZExpr \= GlobalMZExpr0
    then
        % If the substitution results in an assignment 'x = x' and this
        % is a temporary variable, then delete the assignment. Otherwise,
        % update the assignment.
        ( if mzn_expr_is_scalar_var(GlobalMZExpr, GlobalVarId) then
            ( if
                (
                    not map.contains(!.GlobalVarMap, VarId)
                ;
                    map.search(!.GlobalVarMap, VarId, VarInfo),
                    VarInfo ^ vi_kind = var_is_temporary
                )
            then
                GlobalVarInfo = GlobalVarInfo0 ^ vi_value := no
            else
                GlobalVarInfo = GlobalVarInfo0
            )
        else
            GlobalVarInfo = GlobalVarInfo0 ^ vi_value := yes(GlobalMZExpr)
        ),
        map.det_update(GlobalVarId, GlobalVarInfo, !GlobalVarMap)
    else
        % This substitution didn't apply: do nothing.
        true
    ).

%-----------------------------------------------------------------------------%

    % Substitute an expression for a variable in a given constraint.
    %
:- pred substitute_for_var(var_id::in, mzn_expr::in, constraint_id::in,
    id_to_constraint_map::in, id_to_constraint_map::out) is det.

substitute_for_var(VarId, MZExpr, ConstraintId, !IdsToConstraints) :-
    ( if
        % Check the constraint in question is still there.
        !.IdsToConstraints ^ elem(ConstraintId) = Constraint0
    then
        Constraint0 = mzn_constraint(Name, MZArgs0, MZAnns0),
        substitute_for_var_in_anns(VarId, MZExpr, MZAnns0, MZAnns),
        substitute_for_var_in_expr_list(VarId, MZExpr, MZArgs0, MZArgs),
        Constraint = mzn_constraint(Name, MZArgs, MZAnns),
        !IdsToConstraints ^ elem(ConstraintId) := Constraint
    else
        % Presumably this constraint has been removed for being trivially
        % true or otherwise entailed.
        true
    ).

%-----------------------------------------------------------------------------%

    % Substitute an expression for a variable in a set of annotations.
    % Remove any corresponding defines_var annotation if present.
    %
:- pred substitute_for_var_in_anns(var_id::in, mzn_expr::in,
    mzn_anns::in, mzn_anns::out) is det.

substitute_for_var_in_anns(VarId, MZExpr, MZAnns0, MZAnns) :-
    set.map(substitute_for_var_in_ann(VarId, MZExpr), MZAnns0, MZAnns1),
    MZAnns = set.delete(MZAnns1, defines_var(MZExpr)).

%-----------------------------------------------------------------------------%

:- pred substitute_for_var_in_ann(var_id::in, mzn_expr::in,
    mzn_ann::in, mzn_ann::out) is det.

substitute_for_var_in_ann(VarId, MZExpr, MZAnn0, MZAnn) :-
    (
        MZAnn0 = mzn_ann(Name, MZArgs0),
        substitute_for_var_in_ann_args(VarId, MZExpr, MZArgs0, MZArgs),
        MZAnn = mzn_ann(Name, MZArgs)
    ;
        MZAnn0 = mzn_ann_var(AnnVar),
        AnnVarId = mzn_var_id(AnnVar),
        ( if
            AnnVarId \= VarId
        then
            % This is a different variable.
            MZAnn = MZAnn0
        else if
            % This is our variable: perform the substitution.
            % Just do a quick type check first...
            MZExpr = mzn_expr(ann_expr(MZAnn1), _)
        then
            MZAnn = MZAnn1
        else
            % Oops!  The value of our variable *ought* to be an annotation!
            Context = [["In FlatZinc optimisation.\n"]],
            PredName = "substitute_for_var_in_ann",
            minizinc_internal_error(Context, PredName, "expected ann expr")
        )
    ).

%-----------------------------------------------------------------------------%

:- pred substitute_for_var_in_ann_args(var_id::in, mzn_expr::in,
    mzn_exprs::in, mzn_exprs::out) is det.

substitute_for_var_in_ann_args(_, _, [], []).
substitute_for_var_in_ann_args(VarId, MZExpr,
        [MZArg0 | MZArgs0], [MZArg | MZArgs]) :-
    substitute_for_var_in_ann_arg(VarId, MZExpr, MZArg0, MZArg),
    substitute_for_var_in_ann_args(VarId, MZExpr, MZArgs0, MZArgs).

:- pred substitute_for_var_in_ann_arg(var_id::in, mzn_expr::in,
    mzn_expr::in, mzn_expr::out) is det.

substitute_for_var_in_ann_arg(VarId, MZExpr, MZArg0, MZArg) :-
    MZArg0 = mzn_expr(MZArgRawExpr0, ExprAnns),
    % Annotations may be nested in FlatZinc.
    ( if
        MZArgRawExpr0 = ann_expr(AnnExpr0)
      then
        substitute_for_var_in_ann(VarId, MZExpr, AnnExpr0, AnnExpr),
        MZArg = mzn_expr(ann_expr(AnnExpr), ExprAnns)
      else if
        MZArgRawExpr0 = ann_array_expr(array_items(IndexRanges, Items0))
      then
        MZItems0 = array.map(ann_to_mzn_expr, Items0),
        substitute_for_var_in_ann_array(VarId, MZExpr, MZItems0, MZItems),
        Context = [["In FlatZinc optimisation.\n"]],
        Items = array.map(mzn_expr_to_ann(Context), MZItems),
        MZArg = mzn_expr(ann_array_expr(array_items(IndexRanges, Items)),
            ExprAnns)
      else
        substitute_for_var_in_expr(VarId, MZExpr, MZArg0, MZArg)
    ).

:- pred substitute_for_var_in_ann_array(var_id::in, mzn_expr::in,
    mzn_expr_array::in, mzn_expr_array::out) is det.

substitute_for_var_in_ann_array(VarId, MZExpr, MZArgs0, MZArgs) :-
    MZArgs1 = array.copy(MZArgs0),
    array.map(substitute_for_var_in_ann_arg(VarId, MZExpr), MZArgs1, MZArgs).

%-----------------------------------------------------------------------------%

:- pred substitute_for_var_in_expr_list(var_id::in, mzn_expr::in,
    mzn_exprs::in, mzn_exprs::out) is det.

substitute_for_var_in_expr_list(VarId, MZExpr, MZArgs0, MZArgs) :-
    list.map(substitute_for_var_in_expr(VarId, MZExpr), MZArgs0, MZArgs).

%-----------------------------------------------------------------------------%

:- pred substitute_for_var_in_expr_array(var_id::in, mzn_expr::in,
    mzn_expr_array::in, mzn_expr_array::out) is det.

substitute_for_var_in_expr_array(VarId, MZExpr, MZArgs0, MZArgs) :-
    MZArgs1 = array.copy(MZArgs0),
    array.map(substitute_for_var_in_expr(VarId, MZExpr), MZArgs1, MZArgs).

%-----------------------------------------------------------------------------%

:- pred substitute_for_var_in_expr(var_id::in, mzn_expr::in,
    mzn_expr::in, mzn_expr::out) is det.

substitute_for_var_in_expr(VarId, MZExpr, MZArg0, MZArg) :-
    ( if mzn_expr_is_scalar_const(MZArg0) then
        % This arg is a constant, hence cannot refer to our variable.
        MZArg = MZArg0
    else if mzn_expr_is_scalar_var(MZArg0, ArgVarId) then
        ( if ArgVarId = VarId then
            % This is our variable: perform the substitution.
            MZArg = MZExpr
        else
            % This is a different variable: do nothing.
            MZArg = MZArg0
        )
    else if
        % If this is an array then we have to look at the arguments
        % for substition opportunities.
        MZArg0 = mzn_expr(RawMZArg0, MZAnns0),
        Context = [["In FlatZinc optimisation.\n"]],
        (
            RawMZArg0 = bool_array_expr(array_items(IndexRanges, Items0)),
            MZItems0 = array.map(bool_to_mzn_expr, Items0),
            substitute_for_var_in_expr_array(VarId, MZExpr, MZItems0, MZItems),
            Items = array.map(mzn_expr_to_bool(Context), MZItems),
            RawMZArg = bool_array_expr(array_items(IndexRanges, Items))
        ;
            RawMZArg0 = float_array_expr(array_items(IndexRanges, Items0)),
            MZItems0 = array.map(float_to_mzn_expr, Items0),
            substitute_for_var_in_expr_array(VarId, MZExpr, MZItems0, MZItems),
            Items = array.map(mzn_expr_to_float(Context), MZItems),
            RawMZArg = float_array_expr(array_items(IndexRanges, Items))
        ;
            RawMZArg0 = int_array_expr(array_items(IndexRanges, Items0)),
            MZItems0 = array.map(int_to_mzn_expr, Items0),
            substitute_for_var_in_expr_array(VarId, MZExpr, MZItems0, MZItems),
            Items = array.map(mzn_expr_to_int(Context), MZItems),
            RawMZArg = int_array_expr(array_items(IndexRanges, Items))
        )
    then
        % NOTE that we don't have annotations on expressions in FlatZinc,
        % so we don't need to do any substitutions there.
        MZArg = mzn_expr(RawMZArg, MZAnns0)
    else
        % This is not of a type which can contain variables: do nothing.
        MZArg = MZArg0
    ).

%-----------------------------------------------------------------------------%

:- pred report_model_inconsistency_detected is erroneous.

report_model_inconsistency_detected :-
    Context = [],
    model_inconsistency_detected(Context, "In FlatZinc optimisation.\n").

%-----------------------------------------------------------------------------%

:- pred report_unexpected_non_flatzinc_expr(string::in) is erroneous.

report_unexpected_non_flatzinc_expr(PredName) :-
    Context = [["In FlatZinc optimisation.\n"]],
    minizinc_internal_error(Context, PredName, "unexpected non-FlatZinc expr").

%-----------------------------------------------------------------------------%
:- end_module opt.
%-----------------------------------------------------------------------------%
