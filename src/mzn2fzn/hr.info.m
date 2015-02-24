%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
% The persistent data structures used by the half-reification transformation.
%
%-----------------------------------------------------------------------------%

:- module hr.info.
:- interface.

:- import_module errors.
:- import_module global_vars.
:- import_module types.

:- import_module counter.
:- import_module list.
:- import_module maybe.
:- import_module unit.

%-----------------------------------------------------------------------------%

    % Half-reification generates implications of the form
    %   lhs -> constraint
    % This type (implication lhs) represents the left hand side
    % of the implication.
:- type ilhs
    --->    ilhs_true
    ;       ilhs_var(var_id).   % This will be a global var.

:- func ilhsv_to_expr(var_id) = mzn_expr.

:- type known_to_be_false
    --->    not_known_to_be_false
    ;       known_to_be_false.

:- func combine_known_to_be_false(known_to_be_false, known_to_be_false)
    = known_to_be_false.

:- func combine_known_to_be_false_list(list(known_to_be_false))
    = known_to_be_false.

%-----------------------------------------------------------------------------%

    % The flattening environment.
    %
:- type hr_info.

:- pred init_hr_info(hr_info::out) is det.

    % Exported for hr.convert.m. Other modules should not use these predicates.
    %
:- pred construct_hr_info(local_var_map::in, counter::in, cse_map::in,
    hr_info::out) is det.
:- pred deconstruct_hr_info(hr_info::in,
    local_var_map::out, counter::out, cse_map::out) is det.

%-----------------------------------------------------------------------------%

:- pred model_add_predicate_info(pred_proc_id::in, predicate_info::in,
    model::in, model::out) is det.

%-----------------------------------------------------------------------------%

:- pred hr_add_local_var(var_id::in, mzn_expr::in, hr_info::in, hr_info::out)
    is det.

    % Initialise local and global variables.
    % N.B.: a "tmp" var is an intermediate variable introduced by flattening.
    %
:- pred hr_add_global_par(var_id::in, mzn_type::in, index_ranges::in,
    model::in, model::out) is det.
:- pred hr_add_global_permanent_var(var_id::in, mzn_type::in, index_ranges::in,
    mzn_anns::in, list(mzn_constraint_to_add)::out,
    model::in, model::out) is det.
:- pred hr_add_global_tmp_var(var_id::in, mzn_type::in, index_ranges::in,
    mzn_anns::in, list(mzn_constraint_to_add)::out,
    model::in, model::out) is det.

%-----------------------------------------------------------------------------%

    % Construct a new (global) temp var var_id using the string argument to
    % construct the name (a unique number is appended).
    %
:- pred hr_new_tmp_var_id(string::in, var_id::out, hr_info::in, hr_info::out)
    is det.

%-----------------------------------------------------------------------------%

    % Create a new temporary bool var.
    %
:- pred hr_make_tmp_bool_var(error_context::in, mzn_anns::in, ilhs::in,
    _DummyRange::in, mzn_anns::in, var_id::out, bool_expr::out,
    mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

    % Create a new temporary float var.
    %
:- pred hr_make_tmp_float_var(error_context::in, mzn_anns::in, ilhs::in,
    float_range::in, mzn_anns::in, var_id::out, float_expr::out,
    mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

    % Create a new temporary int var.
    %
:- pred hr_make_tmp_int_var(error_context::in, mzn_anns::in, ilhs::in,
    int_range::in, mzn_anns::in, var_id::out, int_expr::out,
    mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

    % Create a new temporary int set var.
    %
:- pred hr_make_tmp_int_set_var(error_context::in, mzn_anns::in, ilhs::in,
    int_range::in, mzn_anns::in, var_id::out, int_set_expr::out,
    mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

%-----------------------------------------------------------------------------%

:- pred hr_add_tmp_ann_var(error_context::in, mzn_anns::in, ilhs::in,
    unit::in, string::in, list(mzn_expr)::in, mzn_anns::in,
    var_id::out, mzn_ann::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

:- pred hr_add_tmp_string_var(error_context::in, mzn_anns::in, ilhs::in,
    unit::in, string::in, list(mzn_expr)::in, mzn_anns::in,
    var_id::out, string_expr::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

:- pred hr_add_tmp_bool_var(error_context::in, mzn_anns::in, ilhs::in,
    _DummyRange::in, string::in, list(mzn_expr)::in, mzn_anns::in,
    var_id::out, bool_expr::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

:- pred hr_add_tmp_float_var(error_context::in, mzn_anns::in, ilhs::in,
    float_range::in, string::in, list(mzn_expr)::in, mzn_anns::in,
    var_id::out, float_expr::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

:- pred hr_add_tmp_int_var(error_context::in, mzn_anns::in, ilhs::in,
    int_range::in, string::in, list(mzn_expr)::in, mzn_anns::in,
    var_id::out, int_expr::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

:- pred hr_add_tmp_int_set_var(error_context::in, mzn_anns::in, ilhs::in,
    int_range::in, string::in, list(mzn_expr)::in, mzn_anns::in,
    var_id::out, int_set_expr::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

%-----------------------------------------------------------------------------%

:- func hr_get_var_value(hr_info, model, var_id) = maybe(mzn_expr).
:- pred hr_set_var_value(var_id::in, mzn_expr::in,
    hr_info::in, hr_info::out, model::in, model::out) is det.

%-----------------------------------------------------------------------------%

:- pred hr_impose_constraint(error_context::in, string::in,
    ilhs::in, bool_expr::in, mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

:- pred hr_add_constraint_to_add(mzn_anns::in, ilhs::in,
    mzn_constraint_to_add::in, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.
:- pred hr_add_constraints_to_add(mzn_anns::in, ilhs::in,
    list(mzn_constraint_to_add)::in, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

:- pred hr_add_primitive_constraint(string::in, list(mzn_expr)::in,
    mzn_anns::in, mzn_constraint::out, model::in, model::out) is det.
:- pred hr_add_maybe_complex_constraint(error_context::in, mzn_anns::in,
    ilhs::in, string::in, list(mzn_expr)::in, mzn_anns::in,
    mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

%-----------------------------------------------------------------------------%

:- pred hr_search_for_cse_var(hr_info::in, mzn_constraint::in, var_id::out)
    is semidet.

:- pred hr_add_cse_var(mzn_constraint::in, var_id::in,
    hr_info::in, hr_info::out) is det.

%-----------------------------------------------------------------------------%

    % These functions are exported only so that we can create a flatten.env
    % structure from the structures used by the hr package.
    %
:- func hr_info_get_local_var_map(hr_info) = local_var_map.
:- func hr_info_get_tmp_var_counter(hr_info) = counter.
:- func hr_info_get_cse_map(hr_info) = cse_map.

%-----------------------------------------------------------------------------%

    % Post-process vars after the model has been constructed.
    %
    % - Ensure all var bounds are sensible (i.e., either both or neither
    %   of a variable's bounds are +/-infinity). This may mean adding
    %   new constraints to handle variables with half-open domains.
    %
    % - Accumulate groups of tmp vars with the same domain into arrays
    %   (this can substantially reduce the number of variable declarations in
    %   the FlatZinc model). This requires applying a substitution over the
    %   tmp vars in the model.
    %
:- pred hr_post_process_vars(hr_info::in, hr_info::out, model::in, model::out)
    is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module errors.
:- import_module hr.convert.
:- import_module hr.float.
:- import_module hr.int.
:- import_module mzn_ops.

:- import_module bool.
:- import_module counter.
:- import_module map.
:- import_module string.

%-----------------------------------------------------------------------------%

ilhsv_to_expr(ILHSVar) = bool_to_mzn_expr(bool_var(var_no_index(ILHSVar))).

combine_known_to_be_false(known_to_be_false, _) = known_to_be_false.
combine_known_to_be_false(not_known_to_be_false, KTBF) = KTBF.

combine_known_to_be_false_list([]) = _ :-
    minizinc_internal_error([], $pred, "[]").
combine_known_to_be_false_list([A | Bs]) =
    combine_known_to_be_false_list_2(A, Bs).

:- func combine_known_to_be_false_list_2(known_to_be_false,
    list(known_to_be_false)) = known_to_be_false.

combine_known_to_be_false_list_2(known_to_be_false, _) =
    known_to_be_false.
combine_known_to_be_false_list_2(not_known_to_be_false, []) =
    not_known_to_be_false.
combine_known_to_be_false_list_2(not_known_to_be_false, [H | T]) =
    combine_known_to_be_false_list_2(H, T).

%-----------------------------------------------------------------------------%

:- type hr_info
    --->    hr_info(
                % Locals are predicate parameters and let vars.
                hri_locals                  :: local_var_map,

                % Used to allocate new temporary global variables.
                hri_tmp_var_counter         :: counter,

                % Common subexpression elimination map.
                hri_cse_map                 :: cse_map
            ).

construct_hr_info(LocalVarMap, TmpCounter, CSEMap, Info) :-
    Info = hr_info(LocalVarMap, TmpCounter, CSEMap).

deconstruct_hr_info(Info, LocalVarMap, TmpCounter, CSEMap) :-
    Info = hr_info(LocalVarMap, TmpCounter, CSEMap).

%-----------------------------------------------------------------------------%

init_hr_info(Info) :-
    map.init(LocalVarMap),
    counter.init(1, TmpCounter),
    map.init(CSEMap),
    Info = hr_info(LocalVarMap, TmpCounter, CSEMap).

%-----------------------------------------------------------------------------%

model_add_predicate_info(PredProcId, PredicateInfo, !Model) :-
    PredMap0 = !.Model ^ model_pred_map,
    map.det_insert(PredProcId, PredicateInfo, PredMap0, PredMap),
    !Model ^ model_pred_map := PredMap.

%-----------------------------------------------------------------------------%

hr_add_local_var(VarId, MZ, !Info) :-
    ( if
        % Don't introduce a loop if a local variable aliases a global
        % variable of the same name.
        MZ = mzn_expr(RawMZ, _),
        (
            ( RawMZ = bool_expr(bool_var(MZVar))
            ; RawMZ = float_expr(float_var(MZVar))
            ; RawMZ = int_expr(int_var(MZVar))
            ; RawMZ = int_set_expr(set_var(MZVar))
            ),
            mzn_var_id(MZVar) = VarId
        ;
            ( RawMZ = bool_array_expr(array_var(_, VarId))
            ; RawMZ = float_array_expr(array_var(_, VarId))
            ; RawMZ = int_array_expr(array_var(_, VarId))
            ; RawMZ = bool_set_array_expr(array_var(_, VarId))
            ; RawMZ = float_set_array_expr(array_var(_, VarId))
            ; RawMZ = int_set_array_expr(array_var(_, VarId))
            )
        )
      then
        % This would introduce a loop: we don't need to introduce a local.
        true
      else
        LocalVarMap0 = hr_info_get_local_var_map(!.Info),
        map.set(VarId, MZ, LocalVarMap0, LocalVarMap),
        hr_info_set_local_var_map(LocalVarMap, !Info)
    ).

%-----------------------------------------------------------------------------%

hr_add_global_par(VarId, MZType, IndexRanges, !Model) :-
    GlobalVarMap0 = !.Model ^ model_globals,
    global_vars.add_global_par(VarId, MZType, IndexRanges,
        GlobalVarMap0, GlobalVarMap),
    !Model ^ model_globals := GlobalVarMap.

hr_add_global_permanent_var(VarId, MZType, IndexRanges, Anns, ConstraintsToAdd,
        !Model) :-
    GlobalVarMap0 = !.Model ^ model_globals,
    global_vars.add_global_permanent_var(VarId, MZType, IndexRanges, Anns,
        ConstraintsToAdd, GlobalVarMap0, GlobalVarMap),
    !Model ^ model_globals := GlobalVarMap.
    % list.foldl2(hr_add_constraint_to_add_not_reified, ConstraintsToAdd,
    %   !Info, !Model).

hr_add_global_tmp_var(VarId, MZType, IndexRanges, Anns, ConstraintsToAdd,
        !Model) :-
    GlobalVarMap0 = !.Model ^ model_globals,
    global_vars.add_global_tmp_var(VarId, MZType, IndexRanges, Anns,
        ConstraintsToAdd, GlobalVarMap0, GlobalVarMap),
    !Model ^ model_globals := GlobalVarMap.
    % list.foldl2(hr_add_constraint_to_add_not_reified, ConstraintsToAdd,
    %   !Info, !Model).

%-----------------------------------------------------------------------------%

hr_new_tmp_var_id(Name, VarId, !Info) :-
    Counter0 = hr_info_get_tmp_var_counter(!.Info),
    counter.allocate(VarNo, Counter0, Counter),
    hr_info_set_tmp_var_counter(Counter, !Info),
    VarName = string.(Name ++ "____" ++ string.int_to_string(VarNo)),
    VarId = name_to_global_var(VarName).

%-----------------------------------------------------------------------------%

hr_make_tmp_bool_var(Context, _OutsideAnns, _ILHS, _Bounds, Anns, VarId, Z,
        AllConstraints, !Info, !Model) :-
    hr_new_tmp_var_id("BOOL", VarId, !Info),
    hr_add_global_tmp_var(VarId, mzn_bool, [], Anns, ConstraintsToAdd, !Model),
    minizinc_require(Context, unify(ConstraintsToAdd, []), $pred,
        "constraints added"),
    Z = bool_var(var_no_index(VarId)),
    mzn_constraint_set_empty(AllConstraints).

hr_make_tmp_float_var(Context, OutsideAnns, ILHS, Bounds, Anns, VarId, Z,
        AllConstraints, !Info, !Model) :-
    hr_new_tmp_var_id("FLOAT", VarId, !Info),
    IndexRanges = [],
    hr_add_global_tmp_var(VarId, mzn_float(Bounds), IndexRanges, Anns,
        ConstraintsToAdd, !Model),
    hr_add_constraints_to_add(OutsideAnns, ILHS, ConstraintsToAdd,
        AllConstraints, !Info, !Model),
    Z = float_var(var_no_index(VarId)),
    hr_refine_float_bounds(Context, ILHS, Bounds, Z, !Model).

hr_make_tmp_int_var(Context, OutsideAnns, ILHS, Bounds, Anns, VarId, Z,
        AllConstraints, !Info, !Model) :-
    hr_new_tmp_var_id("INT", VarId, !Info),
    IndexRanges = [],
    hr_add_global_tmp_var(VarId, mzn_int(Bounds), IndexRanges, Anns,
        VarConstraintsToAdd, !Model),
    hr_add_constraints_to_add(OutsideAnns, ILHS, VarConstraintsToAdd,
        VarConstraints, !Info, !Model),
    Z = int_var(var_no_index(VarId)),
    hr_refine_int_bounds(Context, ILHS, Bounds, Z, RefineConstraintsToAdd,
        !Model),
    hr_add_constraints_to_add(OutsideAnns, ILHS, RefineConstraintsToAdd,
        RefineConstraints, !Info, !Model),
    mzn_constraint_set_union(VarConstraints, RefineConstraints,
        AllConstraints).

hr_make_tmp_int_set_var(_Context, OutsideAnns, ILHS, Bounds, Anns, VarId, Z,
        AllConstraints, !Info, !Model) :-
    hr_new_tmp_var_id("SET", VarId, !Info),
    IndexRanges = [],
    hr_add_global_tmp_var(VarId, mzn_int_set(Bounds), IndexRanges, Anns,
        ConstraintsToAdd, !Model),
    hr_add_constraints_to_add(OutsideAnns, ILHS, ConstraintsToAdd,
        AllConstraints, !Info, !Model),
    Z = set_var(var_no_index(VarId)),
    GlobalVarMap0 = !.Model ^ model_globals,
    set_int_set_bounds(VarId, Bounds, GlobalVarMap0, GlobalVarMap),
    !Model ^ model_globals := GlobalVarMap.

%-----------------------------------------------------------------------------%

hr_add_tmp_ann_var(Context, _, _, _, _, _, _, VarId, Z, AllConstraints,
        !Info, !Model) :-
    ( if semidet_true then
        minizinc_internal_error(Context, $pred, "should not be called")
    else
        hr_new_tmp_var_id("DUMMY", VarId, !Info),
        Z = mzn_ann("dummy", []),
        mzn_constraint_set_empty(AllConstraints)
    ).

hr_add_tmp_string_var(Context, _, _, _, _, _, _, VarId, Z, AllConstraints,
        !Info, !Model) :-
    ( if semidet_true then
        minizinc_internal_error(Context, $pred, "should not be called")
    else
        hr_new_tmp_var_id("DUMMY", VarId, !Info),
        Z = string_const("dummy"),
        mzn_constraint_set_empty(AllConstraints)
    ).

hr_add_tmp_bool_var(Context, OutsideAnns, ILHS, Bounds,
        ConstraintName, Args0, ConstraintAnns, VarId, Z, AllConstraints,
        !Info, !Model) :-
    InsideAnns = join_anns(ConstraintAnns, OutsideAnns),
    PartialConstraint = mzn_constraint(ConstraintName, Args0, InsideAnns),
    ( if hr_search_for_cse_var(!.Info, PartialConstraint, VarIdPrime) then
        VarId = VarIdPrime,
        Z = bool_var(var_no_index(VarId)),
        mzn_constraint_set_singleton(PartialConstraint, AllConstraints)
    else
        hr_make_tmp_bool_var(Context, InsideAnns, ILHS, Bounds,
            just_is_defined_var, VarId, Z, VarConstraints, !Info, !Model),
        MZ = bool_to_mzn_expr(Z),
        Args = Args0 ++ [MZ],
        DefAnns = add_ann(defines_var(MZ), InsideAnns),
        hr_add_maybe_complex_constraint(Context, OutsideAnns, ILHS,
            ConstraintName, Args, DefAnns, AddConstraints, !Info, !Model),
        hr_add_cse_var(PartialConstraint, VarId, !Info),
        mzn_constraint_set_union(VarConstraints, AddConstraints,
            AllConstraints)
    ).

hr_add_tmp_float_var(Context, OutsideAnns, ILHS, Bounds,
        ConstraintName, Args0, ConstraintAnns, VarId, Z, AllConstraints,
        !Info, !Model) :-
    InsideAnns = join_anns(ConstraintAnns, OutsideAnns),
    PartialConstraint = mzn_constraint(ConstraintName, Args0, InsideAnns),
    ( if hr_search_for_cse_var(!.Info, PartialConstraint, VarIdPrime) then
        VarId = VarIdPrime,
        Z = float_var(var_no_index(VarId)),
        mzn_constraint_set_singleton(PartialConstraint, AllConstraints)
    else
        hr_make_tmp_float_var(Context, InsideAnns, ILHS, Bounds,
            just_is_defined_var, VarId, Z, VarConstraints, !Info, !Model),
        MZ = float_to_mzn_expr(Z),
        Args = Args0 ++ [MZ],
        DefAnns = add_ann(defines_var(MZ), InsideAnns),
        hr_add_maybe_complex_constraint(Context, OutsideAnns, ILHS,
            ConstraintName, Args, DefAnns, AddConstraints, !Info, !Model),
        hr_add_cse_var(PartialConstraint, VarId, !Info),
        mzn_constraint_set_union(VarConstraints, AddConstraints,
            AllConstraints)
    ).

hr_add_tmp_int_var(Context, OutsideAnns, ILHS, Bounds,
        ConstraintName, Args0, ConstraintAnns, VarId, Z, AllConstraints,
        !Info, !Model) :-
    InsideAnns = join_anns(ConstraintAnns, OutsideAnns),
    PartialConstraint = mzn_constraint(ConstraintName, Args0, InsideAnns),
    ( if hr_search_for_cse_var(!.Info, PartialConstraint, VarIdPrime) then
        VarId = VarIdPrime,
        Z = int_var(var_no_index(VarId)),
        mzn_constraint_set_singleton(PartialConstraint, AllConstraints)
    else
        hr_make_tmp_int_var(Context, InsideAnns, ILHS, Bounds,
            just_is_defined_var, VarId, Z, VarConstraints, !Info, !Model),
        MZ = int_to_mzn_expr(Z),
        Args = Args0 ++ [MZ],
        DefAnns = add_ann(defines_var(MZ), InsideAnns),
        hr_add_maybe_complex_constraint(Context, OutsideAnns, ILHS,
            ConstraintName, Args, DefAnns, AddConstraints, !Info, !Model),
        hr_add_cse_var(PartialConstraint, VarId, !Info),
        mzn_constraint_set_union(VarConstraints, AddConstraints,
            AllConstraints)
    ).

hr_add_tmp_int_set_var(Context, OutsideAnns, ILHS, Bounds,
        ConstraintName, Args0, ConstraintAnns, VarId, Z, AllConstraints,
        !Info, !Model) :-
    % XXX why isn't this InsideAnns = join_anns(ConstraintAnns, OutsideAnns)?
    InsideAnns = ConstraintAnns,
    PartialConstraint = mzn_constraint(ConstraintName, Args0, InsideAnns),
    ( if hr_search_for_cse_var(!.Info, PartialConstraint, VarIdPrime) then
        VarId = VarIdPrime,
        Z = set_var(var_no_index(VarId)),
        mzn_constraint_set_singleton(PartialConstraint, AllConstraints)
    else
        hr_make_tmp_int_set_var(Context, OutsideAnns, ILHS, Bounds,
            just_is_defined_var, VarId, Z, VarConstraints, !Info, !Model),
        MZ = int_set_to_mzn_expr(Z),
        Args = Args0 ++ [MZ],
        DefAnns = add_ann(defines_var(MZ), InsideAnns),
        hr_add_maybe_complex_constraint(Context, InsideAnns, ILHS,
            ConstraintName, Args, DefAnns, AddConstraints, !Info, !Model),
        hr_add_cse_var(PartialConstraint, VarId, !Info),
        mzn_constraint_set_union(VarConstraints, AddConstraints,
            AllConstraints)
    ).

%-----------------------------------------------------------------------------%

hr_get_var_value(Info, Model, VarId) = MaybeValue :-
    ( if map.search(Info ^ hri_locals, VarId, LocalValue) then
        MaybeValue = yes(LocalValue)
    else
        map.lookup(Model ^ model_globals, VarId, VarInfo),
        MaybeValue = VarInfo ^ vi_value
    ).

hr_set_var_value(VarId, Value, !Info, !Model) :-
    ( if
        LocalVarMap0 = !.Info ^ hri_locals,
        map.search(!.Info ^ hri_locals, VarId, _)
    then
        map.det_update(VarId, Value, LocalVarMap0, LocalVarMap),
        !Info ^ hri_locals := LocalVarMap
    else
        GlobalVarMap0 = !.Model ^ model_globals,
        map.lookup(GlobalVarMap0, VarId, VarInfo0),
        VarInfo = VarInfo0 ^ vi_value := yes(Value),
        map.det_update(VarId, VarInfo, GlobalVarMap0, GlobalVarMap),
        !Model ^ model_globals := GlobalVarMap
    ).

%-----------------------------------------------------------------------------%

:- func hr_var_kind(hr_info, model, var_id) = var_kind.
:- func hr_var_inst(hr_info, model, var_id) = var_inst.

hr_var_kind(_Info, Model, VarId) = Kind :-
    GlobalVarMap = Model ^ model_globals,
    map.lookup(GlobalVarMap, VarId, VarInfo),
    Kind = VarInfo ^ vi_kind.

hr_var_inst(_Info, Model, VarId) = Inst :-
    GlobalVarMap = Model ^ model_globals,
    map.lookup(GlobalVarMap, VarId, VarInfo),
    Inst = VarInfo ^ vi_inst.

%-----------------------------------------------------------------------------%

hr_impose_constraint(Context, ErrMsg, ILHS, Z, AllConstraints, KnownFalse,
        !Info, !Model) :-
    OutsideAnns = no_anns,
    hr_simplify_bool_cv(Context, OutsideAnns, ILHS, Z, CVZ,
        SimplifyConstraints, !Info, !Model),
    (
        CVZ = boolcv_const(yes),
        KnownFalse = not_known_to_be_false,
        AllConstraints = SimplifyConstraints
    ;
        CVZ = boolcv_const(no),
        (
            ILHS = ilhs_true,
            model_inconsistency_detected(Context, ErrMsg)
        ;
            ILHS = ilhs_var(_),
            KnownFalse = known_to_be_false,
            AllConstraints = SimplifyConstraints
        )
    ;
        CVZ = boolcv_var(MZVar),
        (
            ILHS = ilhs_var(ILHSVar),
            hr_add_primitive_constraint("bool_le",
                [bool_to_mzn_expr(bool_var(var_no_index(ILHSVar))),
                 bool_to_mzn_expr(bool_var(MZVar))],
                no_anns, ImplyConstraint, !Model),
            mzn_constraint_set_insert(ImplyConstraint, SimplifyConstraints,
                AllConstraints),
            KnownFalse = not_known_to_be_false
        ;
            ILHS = ilhs_true,
            MZTrue = bool_to_mzn_expr(bool_const(yes)),
            ( if MZVar = var_no_index(VarId) then
                hr_set_var_value(VarId, MZTrue, !Info, !Model),
                AllConstraints = SimplifyConstraints,
                KnownFalse = not_known_to_be_false
            else
                hr_add_primitive_constraint("bool_eq",
                    [bool_to_mzn_expr(bool_var(MZVar)), MZTrue],
                    no_anns, EqConstraint, !Model),
                mzn_constraint_set_insert(EqConstraint, SimplifyConstraints,
                    AllConstraints),
                KnownFalse = not_known_to_be_false
            )
        )
    ).

%-----------------------------------------------------------------------------%

hr_add_constraint_to_add(OutsideAnns, ILHS, ConstraintToAdd, AllConstraints,
        !Info, !Model) :-
    % XXX HR: flatten gets reification from Env.
    % XXX HR: flatten gets outside annotations from Env.
    ConstraintToAdd =
        mzn_constraint_to_add(Context, ConstraintName, Args, Anns),
    hr_add_maybe_complex_constraint(Context, OutsideAnns, ILHS,
        ConstraintName, Args, Anns, AllConstraints, !Info, !Model).

hr_add_constraints_to_add(_, _, [], AllConstraints, !Info, !Model) :-
    mzn_constraint_set_empty(AllConstraints).
hr_add_constraints_to_add(OutsideAnns, ILHS,
        [HeadConstraintToAdd | TailConstraintToAdd], AllConstraints,
        !Info, !Model) :-
    hr_add_constraint_to_add(OutsideAnns, ILHS, HeadConstraintToAdd,
        HeadConstraints, !Info, !Model),
    hr_add_constraints_to_add(OutsideAnns, ILHS, TailConstraintToAdd,
        TailConstraints, !Info, !Model),
    mzn_constraint_set_union(HeadConstraints, TailConstraints, AllConstraints).

%-----------------------------------------------------------------------------%

hr_add_primitive_constraint(ConstraintName, Args, Anns, Constraint, !Model) :-
    Constraint = mzn_constraint(ConstraintName, Args, Anns),
    OldConstraints = !.Model ^ model_constraints,
    mzn_constraint_set_insert(Constraint, OldConstraints, NewConstraints),
    !Model ^ model_constraints := NewConstraints.

hr_add_maybe_complex_constraint(Context, OutsideAnns, ILHS,
        ConstraintName, Args, ConstraintAnns, AllConstraints, !Info, !Model) :-
    Anns = join_anns(ConstraintAnns, OutsideAnns),
    ( if
        hr_flatten_predicate_call(Context, OutsideAnns,
            ConstraintName, Args, Anns, CVZ, PredConstraints, !Info, !Model)
    then
        (
            CVZ = boolcv_const(yes),
            AllConstraints = PredConstraints
        ;
            CVZ = boolcv_const(no),
            unsatisfiable_constraint(Context)
        ;
            CVZ = boolcv_var(MZVar),
            (
                ILHS = ilhs_true,
                ( if
                    hr_flatten_bool_bool_to_bool(Context, Anns, ilhs_true,
                        bb2b_eq, bool_var(MZVar), bool_const(yes), EqZ,
                        BoolEqConstraints, !Info, !Model),
                    EqZ = bool_const(BoolEq)
                then
                    (
                        BoolEq = yes,
                        mzn_constraint_set_union(PredConstraints,
                            BoolEqConstraints, AllConstraints)
                    ;
                        BoolEq = no,
                        unsatisfiable_constraint(Context)
                    )
                else
                    minizinc_internal_error(Context, $pred,
                        "bool_eq failed!\n")
                )
            ;
                ILHS = ilhs_var(_),
                AllConstraints = PredConstraints
            )
        )
    else
        hr_add_primitive_constraint(ConstraintName, Args, Anns, Constraint,
            !Model),
        mzn_constraint_set_singleton(Constraint, AllConstraints)
    ).

:- pred hr_flatten_predicate_call(error_context::in, mzn_anns::in,
    string::in, list(mzn_expr)::in, mzn_anns::in, bool_const_or_var::out,
    mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is semidet.

hr_flatten_predicate_call(Context, OutsideAnns, ConstraintName, Args, PredAnns,
        CVZ, AllConstraints, !Info, !Model) :-
    ProcNum = 1,
    PredProcId = pred_proc_id(ConstraintName, ProcNum),
    map.search(!.Model ^ model_pred_map, PredProcId, PredInfo),
    PredInfo ^ pred_body = yes(_),
    % XXX different from flatten.env wrt annotations
    hr_flatten_predicate(Context, OutsideAnns, ilhs_true,
        ConstraintName, ProcNum, Args, PredAnns, Z, FlattenConstraints,
        !Info, !Model),
    hr_simplify_bool_cv(Context, OutsideAnns, ilhs_true, Z, CVZ,
        SimplifyConstraints, !Info, !Model),
    mzn_constraint_set_union(FlattenConstraints, SimplifyConstraints,
        AllConstraints).

%-----------------------------------------------------------------------------%

hr_search_for_cse_var(Info, PartialConstraint, VarId) :-
    CSEMap = hr_info_get_cse_map(Info),
    map.search(CSEMap, PartialConstraint, VarId).

hr_add_cse_var(PartialConstraint, VarId, !Info) :-
    CSEMap0 = hr_info_get_cse_map(!.Info),
    map.det_insert(PartialConstraint, VarId, CSEMap0, CSEMap),
    hr_info_set_cse_map(CSEMap, !Info).

%-----------------------------------------------------------------------------%

hr_post_process_vars(!Info, !Model).
    % NYI

%-----------------------------------------------------------------------------%

hr_info_get_local_var_map(Info) = Info ^ hri_locals.
hr_info_get_tmp_var_counter(Info) = Info ^ hri_tmp_var_counter.
hr_info_get_cse_map(Info) = Info ^ hri_cse_map.

:- pred hr_info_set_local_var_map(local_var_map::in,
    hr_info::in, hr_info::out) is det.
:- pred hr_info_set_tmp_var_counter(counter::in,
    hr_info::in, hr_info::out) is det.
:- pred hr_info_set_cse_map(cse_map::in,
    hr_info::in, hr_info::out) is det.

hr_info_set_local_var_map(LocalVarMap, !Info) :-
    !Info ^ hri_locals := LocalVarMap.
hr_info_set_tmp_var_counter(TmpVarCounter, !Info) :-
    !Info ^ hri_tmp_var_counter := TmpVarCounter.
hr_info_set_cse_map(CSEMap, !Info) :-
    !Info ^ hri_cse_map := CSEMap.

%-----------------------------------------------------------------------------%
:- end_module hr.info.
%-----------------------------------------------------------------------------%
