%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2009 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Ralph Becket <rafe@csse.unimelb.edu.au>
%
% The flattening environment.
%
%-----------------------------------------------------------------------------%

:- module flatten.env.
:- interface.

:- import_module errors.
:- import_module types.

:- import_module zinc_ast.

:- import_module bool.
:- import_module counter.
:- import_module list.
:- import_module maybe.
:- import_module unit.

%-----------------------------------------------------------------------------%

    % The flattening environment.
    %
:- type env.

:- func new_env = env.

:- func env ^ predicate(pred_name, proc_no) = predicate_info is semidet.
:- func (env ^ predicate(pred_name, proc_no) := predicate_info) = env.

    % Reification status.  When reifying, we collect any reification variables
    % from flattening partial functions such as integer division.
    %
:- type reifying
    --->    not_reifying
    ;       reifying(bool_exprs).

    % The reification status.
    %
:- func env ^ reifying = reifying.
:- func (env ^ reifying := reifying) = env.

    % Annotations in force in a given context.
    %
:- func env ^ anns = mzn_anns.
:- func (env ^ anns := mzn_anns) = env.
:- pred add_anns(mzn_anns::in, env::in, env::out) is det.

    % Construct a new (global) temp var var_id using the string argument to
    % construct the name (a unique number is appended).
    %
:- pred new_tmp_var_id(string::in, var_id::out, env::in, env::out) is det.

%-----------------------------------------------------------------------------%

    % Create a new temporary bool var.
    %
:- pred make_tmp_bool_var(error_context::in, _Dummy::in, mzn_anns::in,
    var_id::out, bool_expr::out, env::in, env::out) is det.

    % Create a new temporary float var.
    %
:- pred make_tmp_float_var(error_context::in, float_range::in, mzn_anns::in,
    var_id::out, float_expr::out, env::in, env::out) is det.

    % Create a new temporary int var.
    %
:- pred make_tmp_int_var(error_context::in, int_range::in, mzn_anns::in,
    var_id::out, int_expr::out, env::in, env::out) is det.

    % Create a new temporary int set var.
    %
:- pred make_tmp_int_set_var(error_context::in, int_range::in, mzn_anns::in,
    var_id::out, int_set_expr::out, env::in, env::out) is det.

%-----------------------------------------------------------------------------%

:- pred add_tmp_ann_var(error_context::in, unit::in,
    string::in, list(mzn_expr)::in, mzn_anns::in,
    var_id::out, mzn_ann::out, env::in, env::out) is det.

:- pred add_tmp_string_var(error_context::in, unit::in,
    string::in, list(mzn_expr)::in, mzn_anns::in,
    var_id::out, string_expr::out, env::in, env::out) is det.

:- pred add_tmp_bool_var(error_context::in, _Dummy::in,
    string::in, mzn_exprs::in, mzn_anns::in,
    var_id::out, bool_expr::out, env::in, env::out) is det.

:- pred add_tmp_float_var(error_context::in, float_range::in,
    string::in, list(mzn_expr)::in, mzn_anns::in,
    var_id::out, float_expr::out, env::in, env::out) is det.

:- pred add_tmp_int_var(error_context::in, int_range::in,
    string::in, list(mzn_expr)::in, mzn_anns::in,
    var_id::out, int_expr::out, env::in, env::out) is det.

:- pred add_tmp_int_set_var(error_context::in, int_range::in,
    string::in, list(mzn_expr)::in, mzn_anns::in,
    var_id::out, int_set_expr::out, env::in, env::out) is det.

%-----------------------------------------------------------------------------%

:- func empty_local_var_map = local_var_map.
:- func env ^ locals = local_var_map.
:- func (env ^ locals := local_var_map) = env.
:- pred add_local_var(var_id::in, mzn_expr::in, env::in, env::out) is det.

    % Initialise local and global variables.
    % N.B.: a "tmp" var is an intermediate variable introduced by flattening.
    %
:- pred add_global_par(var_id::in, mzn_type::in, index_ranges::in,
    env::in, env::out) is det.
:- pred add_global_permanent_var(var_id::in, mzn_type::in, index_ranges::in,
    mzn_anns::in, env::in, env::out) is det.
:- pred add_global_tmp_var(var_id::in, mzn_type::in, index_ranges::in,
    mzn_anns::in, env::in, env::out) is det.

:- func env ^ env_globals = global_var_map.

    % Is the given var temporary? Is it var (i.e., not par)?
    %
:- func env ^ var_is_tmp(var_id) = bool.
:- func env ^ var_is_var(var_id) = bool.
:- func env ^ var_is_local(var_id) = bool.

    % Array variable index ranges.
    %
:- func env ^ var_index_ranges(var_id) = index_ranges.
:- func (env ^ var_index_ranges(var_id) := index_ranges) = env.

    % Variable bounds.
    %
:- func env ^ var_float_lb(var_id) = float.
:- func (env ^ var_float_lb(var_id) := float) = env.

:- func env ^ var_float_ub(var_id) = float.
:- func (env ^ var_float_ub(var_id) := float) = env.

:- func env ^ var_int_lb(var_id) = int.
:- func (env ^ var_int_lb(var_id) := int) = env.

:- func env ^ var_int_ub(var_id) = int.
:- func (env ^ var_int_ub(var_id) := int) = env.

:- func env ^ var_set_ub(var_id) = int_range.
:- func (env ^ var_set_ub(var_id) := int_range) = env.

:- func env ^ var_set_ub_is_contiguous(var_id) = bool.

    % Variable values.
    %
:- func env ^ var_value(var_id) = mzn_expr is semidet.
:- func (env ^ var_value(var_id) := mzn_expr) = env.

:- func env ^ var_type(var_id) = mzn_type.
:- func env ^ var_inst(var_id) = var_inst.

    % Variable annotations.
    %
:- func env ^ var_anns(var_id) = mzn_anns.
:- func (env ^ var_anns(var_id) := mzn_anns) = env.

    % Marks the given variable as an output, provided it is a global var,
    % and not local or a parameter.
    %
:- pred mark_var_for_output(var_id::in, env::in, env::out) is det.

:- pred impose_constraint(error_context::in, string::in, bool_expr::in,
    env::in, env::out) is det.

:- pred add_constraint(error_context::in, string::in, list(mzn_expr)::in,
    mzn_anns::in, env::in, env::out) is det.

:- func get_maybe_solve_goal(env) = maybe(mzn_solve_goal).
:- pred set_solve_goal(mzn_solve_goal::in, env::in, env::out) is det.
:- pred update_solve_goal(mzn_solve_goal::in, env::in, env::out) is det.

    % Common subexpression elimination.
    %
:- func env ^ cse_lookup(mzn_constraint) = var_id is semidet.
:- pred add_cse_var(mzn_constraint::in, var_id::in, env::in, env::out) is det.

%-----------------------------------------------------------------------------%

:- pred diff_constraints_in_envs(env::in, env::in, mzn_constraint_set::out)
    is det.

:- pred construct_env(reifying::in, mzn_anns::in, local_var_map::in,
    counter::in, cse_map::in, model::in, env::out) is det.

:- pred deconstruct_env(env::in, reifying::out, mzn_anns::out,
    local_var_map::out, counter::out, cse_map::out, model::out) is det.

:- pred get_model(env::in, model::out) is det.

:- pred set_model(model::in, env::in, env::out) is det.

:- pred extend_model_to_env(counter::in, model::in, env::out) is det.

%-----------------------------------------------------------------------------%

:- pred flatten_ti_expr(error_context::in, ti_expr::in,
    var_par::out, mzn_type::out, index_ranges::out, env::in, env::out) is det.

%-----------------------------------------------------------------------------%

:- pred replace_implicit_indexes(mzn_expr::in,
    index_ranges::in, index_ranges::out) is det.

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
:- pred flatten_post_process_vars(env::in, env::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module common_bounds.
:- import_module flatten.app.
:- import_module flatten.bool.
:- import_module flatten.expr.
:- import_module flatten.float.
:- import_module flatten.int.
:- import_module global_vars.
:- import_module mzn_ops.

:- import_module intset.
:- import_module zinc_common.

:- import_module array.
:- import_module map.
:- import_module require.
:- import_module set.
:- import_module set_tree234.
:- import_module string.

%-----------------------------------------------------------------------------%

:- type env
    --->    env(
                % Locals are predicate parameters and let vars.
                env_locals              :: local_var_map,

                % Globals are model parameters and variables.
                env_globals             :: global_var_map,

                % Are we in a reifying context?
                env_reifying            :: reifying,

                % Annotations in force in the current context.
                env_anns                :: mzn_anns,

                % Predicates defined in the model.
                env_predicates          :: predicate_map,

                % Common subexpression elimination map.
                env_cse_map             :: cse_map,

                % Constraints.
                env_constraints         :: mzn_constraint_set,

                % Used to allocate new variables.
                env_tmp_var_counter     :: counter,

                % The solve goal.
                env_solve_goal          :: maybe(mzn_solve_goal)
            ).

%-----------------------------------------------------------------------------%

new_env = Env :-
    Locals = map.init,
    Globals = map.init,
    Reifying = not_reifying,
    Anns = no_anns,
    Predicates = map.init,
    CSEMap = map.init,
    mzn_constraint_set_empty(ConstraintSet),
    TmpVCounter = counter.init(1),
    MaybeSolveGoal = no : maybe(mzn_solve_goal),
    Env = env(Locals, Globals, Reifying, Anns, Predicates, CSEMap,
        ConstraintSet, TmpVCounter, MaybeSolveGoal).

%-----------------------------------------------------------------------------%

Env ^ predicate(PredName, ProcNo) =
    Env ^ env_predicates ^ elem(pred_proc_id(PredName, ProcNo)).

(Env ^ predicate(PredName, ProcNo) := PredInfo) =
    Env ^ env_predicates ^ elem(pred_proc_id(PredName, ProcNo)) := PredInfo.

%-----------------------------------------------------------------------------%

Env ^ reifying = Env ^ env_reifying.

(Env ^ reifying := Reifying) =
    Env ^ env_reifying := Reifying.

%-----------------------------------------------------------------------------%

Env ^ anns = Env ^ env_anns.

(Env ^ anns := Anns) =
    Env ^ env_anns := Anns.

add_anns(NewAnns, !Env) :-
    ( if NewAnns = no_anns then
        true
    else
        !Env ^ env_anns := join_anns(NewAnns, !.Env ^ env_anns)
    ).

%-----------------------------------------------------------------------------%

new_tmp_var_id(Name, VarId, !Env) :-
    Counter0 = !.Env ^ env_tmp_var_counter,
    counter.allocate(VarNo, Counter0, Counter),
    !Env ^ env_tmp_var_counter := Counter,
    VarNumStr = string.int_to_string(VarNo),
    VarName = string.(Name ++ "____" ++ string.pad_left(VarNumStr, '0', 5)),
    VarId = name_to_global_var(VarName).

%-----------------------------------------------------------------------------%

make_tmp_bool_var(_Context, _Bounds, Anns, VarId, Z, !Env) :-
    new_tmp_var_id("BOOL", VarId, !Env),
    add_global_tmp_var(VarId, mzn_bool, [], Anns, !Env),
    Z = bool_var(var_no_index(VarId)).

make_tmp_float_var(Context, Bounds, Anns, VarId, Z, !Env) :-
    new_tmp_var_id("FLOAT", VarId, !Env),
    IndexRanges = [],
    add_global_tmp_var(VarId, mzn_float(Bounds), IndexRanges, Anns, !Env),
    Z = float_var(var_no_index(VarId)),
    refine_float_bounds(Context, Bounds, Z, !Env).

make_tmp_int_var(Context, Bounds, Anns, VarId, Z, !Env) :-
    new_tmp_var_id("INT", VarId, !Env),
    IndexRanges = [],
    add_global_tmp_var(VarId, mzn_int(Bounds), IndexRanges, Anns, !Env),
    Z = int_var(var_no_index(VarId)),
    refine_int_bounds(Context, Bounds, Z, !Env).

make_tmp_int_set_var(_Context, Bounds, Anns, VarId, Z, !Env) :-
    new_tmp_var_id("SET", VarId, !Env),
    IndexRanges = [],
    add_global_tmp_var(VarId, mzn_int_set(Bounds), IndexRanges, Anns, !Env),
    Z = set_var(var_no_index(VarId)),
    !Env ^ var_set_ub(VarId) := Bounds.

%-----------------------------------------------------------------------------%

add_tmp_ann_var(Context, _, _, _, _, VarId, Z, !Env) :-
    ( if semidet_true then
        minizinc_internal_error(Context, $pred, "should not be called")
    else
        new_tmp_var_id("DUMMY", VarId, !Env),
        Z = mzn_ann("dummy", [])
    ).

add_tmp_string_var(Context, _, _, _, _, VarId, Z, !Env) :-
    ( if semidet_true then
        minizinc_internal_error(Context, $pred, "should not be called")
    else
        new_tmp_var_id("DUMMY", VarId, !Env),
        Z = string_const("dummy")
    ).

add_tmp_bool_var(Context, Bounds, ConstraintName, Args0, Anns0, VarId, Z,
        !Env) :-
    Anns = join_anns(Anns0, !.Env ^ anns),
    PartialConstraint = mzn_constraint(ConstraintName, Args0, Anns),
    ( if !.Env ^ cse_lookup(PartialConstraint) = VarIdPrime then
        VarId = VarIdPrime,
        Z = bool_var(var_no_index(VarId))
    else
        make_tmp_bool_var(Context, Bounds, just_is_defined_var, VarId, Z,
            !Env),
        MZ = bool_to_mzn_expr(Z),
        Args = Args0 ++ [MZ],
        Anns1 = add_ann(defines_var(MZ), Anns),
        add_constraint(Context, ConstraintName, Args, Anns1, !Env),
        add_cse_var(PartialConstraint, VarId, !Env)
    ).

add_tmp_float_var(Context, Bounds, ConstraintName, Args0, Anns0, VarId, Z,
        !Env) :-
    Anns = join_anns(Anns0, !.Env ^ anns),
    PartialConstraint = mzn_constraint(ConstraintName, Args0, Anns),
    ( if !.Env ^ cse_lookup(PartialConstraint) = VarIdPrime then
        VarId = VarIdPrime,
        Z = float_var(var_no_index(VarId))
    else
        make_tmp_float_var(Context, Bounds, just_is_defined_var, VarId, Z,
            !Env),
        MZ = float_to_mzn_expr(Z),
        Args = Args0 ++ [MZ],
        Anns1 = add_ann(defines_var(MZ), Anns),
        add_constraint(Context, ConstraintName, Args, Anns1, !Env),
        add_cse_var(PartialConstraint, VarId, !Env)
    ).

add_tmp_int_var(Context, Bounds, ConstraintName, Args0, Anns0, VarId, Z,
        !Env) :-
    Anns = join_anns(Anns0, !.Env ^ anns),
    PartialConstraint = mzn_constraint(ConstraintName, Args0, Anns),
    ( if !.Env ^ cse_lookup(PartialConstraint) = VarIdPrime then
        VarId = VarIdPrime,
        Z = int_var(var_no_index(VarId))
    else
        make_tmp_int_var(Context, Bounds, just_is_defined_var, VarId, Z, !Env),
        MZ = int_to_mzn_expr(Z),
        Args = Args0 ++ [MZ],
        Anns1 = add_ann(defines_var(MZ), Anns),
        add_constraint(Context, ConstraintName, Args, Anns1, !Env),
        add_cse_var(PartialConstraint, VarId, !Env)
    ).

add_tmp_int_set_var(Context, Bounds, ConstraintName, Args0, Anns0, VarId, Z,
        !Env) :-
    % XXX why isn't this Anns = join_anns(Anns0, !.Env ^ anns)?
    Anns = Anns0,
    PartialConstraint = mzn_constraint(ConstraintName, Args0, Anns),
    ( if !.Env ^ cse_lookup(PartialConstraint) = VarIdPrime then
        VarId = VarIdPrime,
        Z = set_var(var_no_index(VarId))
    else
        make_tmp_int_set_var(Context, Bounds, just_is_defined_var,
            VarId, Z, !Env),
        MZ = int_set_to_mzn_expr(Z),
        Args = Args0 ++ [MZ],
        Anns1 = add_ann(defines_var(MZ), Anns),
        add_constraint(Context, ConstraintName, Args, Anns1, !Env),
        add_cse_var(PartialConstraint, VarId, !Env)
    ).

%-----------------------------------------------------------------------------%

empty_local_var_map = map.init.

Env ^ locals = Env ^ env_locals.

(Env ^ locals := Locals) =
    Env ^ env_locals := Locals.

add_local_var(VarId, MZ, !Env) :-
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
        LocalVarMap0 = !.Env ^ env_locals,
        map.set(VarId, MZ, LocalVarMap0, LocalVarMap),
        !Env ^ env_locals := LocalVarMap
    ).

%-----------------------------------------------------------------------------%

add_global_par(VarId, MZType, IndexRanges, !Env) :-
    GlobalVarMap0 = !.Env ^ env_globals,
    global_vars.add_global_par(VarId, MZType, IndexRanges,
        GlobalVarMap0, GlobalVarMap),
    !Env ^ env_globals := GlobalVarMap.

add_global_permanent_var(VarId, MZType, IndexRanges, Anns, !Env) :-
    GlobalVarMap0 = !.Env ^ env_globals,
    global_vars.add_global_permanent_var(VarId, MZType, IndexRanges, Anns,
        ConstraintsToAdd,
        GlobalVarMap0, GlobalVarMap),
    !Env ^ env_globals := GlobalVarMap,
    list.foldl(add_constraint_to_add, ConstraintsToAdd, !Env).

add_global_tmp_var(VarId, MZType, IndexRanges, Anns, !Env) :-
    GlobalVarMap0 = !.Env ^ env_globals,
    global_vars.add_global_tmp_var(VarId, MZType, IndexRanges, Anns,
        ConstraintsToAdd, GlobalVarMap0, GlobalVarMap),
    !Env ^ env_globals := GlobalVarMap,
    list.foldl(add_constraint_to_add, ConstraintsToAdd, !Env).

%-----------------------------------------------------------------------------%

Env ^ var_is_tmp(VarId) = Result :-
    ( if map.search(Env ^ env_globals, VarId, VarInfo) then
        VarIsTemp = VarInfo ^ vi_kind,
        (
            VarIsTemp = var_is_temporary,
            Result = yes
        ;
            VarIsTemp = var_is_permanent,
            Result = no
        )
    else
        trace [compiletime(flag("check_var_rep"))] (
            ( if semidet_succeed then
                minizinc_internal_error([] : error_context, $pred,
                    "var_is_tmp lookup on local\n")
            else
                true
            )
        ),
        Result = no
    ).

%-----------------------------------------------------------------------------%

Env ^ var_is_var(VarId) = Result :-
    ( if map.search(Env ^ env_globals, VarId, VarInfo) then
        VarInst = VarInfo ^ vi_inst,
        (
            VarInst = var_is_var,
            Result = yes
        ;
            VarInst = var_is_par,
            Result = no
        )
    else
        trace [compiletime(flag("check_var_rep"))] (
            ( if semidet_succeed then
                minizinc_internal_error([] : error_context, $pred,
                    "var_is_var lookup on local\n")
            else
                true
            )
        ),
        Result = no
    ).

%-----------------------------------------------------------------------------%

Env ^ var_is_local(VarId) =
    ( if map.search(Env ^ env_locals, VarId, _) then
        yes
    else
        no
    ).

%-----------------------------------------------------------------------------%

Env ^ var_index_ranges(VarId) = IndexRanges :-
    GlobalVarMap = Env ^ env_globals,
    ( if map.search(GlobalVarMap, VarId, VarInfo) then
        IndexRanges = VarInfo ^ vi_index_ranges
    else
        % XXX Why can't local vars have nonempty index ranges?
        IndexRanges = []
    ).

(Env0 ^ var_index_ranges(VarId) := IndexRanges) = Env :-
    GlobalVarMap0 = Env0 ^ env_globals,
    map.lookup(GlobalVarMap0, VarId, VarInfo0),
    VarInfo = VarInfo0 ^ vi_index_ranges := IndexRanges,
    map.det_update(VarId, VarInfo, GlobalVarMap0, GlobalVarMap),
    Env = Env0 ^ env_globals := GlobalVarMap.

%-----------------------------------------------------------------------------%

Env ^ var_float_lb(VarId) = LB :-
    LB = global_vars.get_float_lb(Env ^ env_globals, VarId).

Env ^ var_float_ub(VarId) = UB :-
    UB = global_vars.get_float_ub(Env ^ env_globals, VarId).

Env ^ var_int_lb(VarId) = LB :-
    LB = global_vars.get_int_lb(Env ^ env_globals, VarId).

Env ^ var_int_ub(VarId) = UB :-
    UB = global_vars.get_int_ub(Env ^ env_globals, VarId).

Env ^ var_set_ub(VarId) =
    global_vars.get_int_set_bounds(Env ^ env_globals, VarId).

Env ^ var_set_ub_is_contiguous(VarId) =
    var_int_set_bounds_is_contiguous(Env ^ env_globals, VarId).

%-----------------------------------------------------------------------------%

(Env0 ^ var_float_lb(VarId) := LB) = Env :-
    GlobalVarMap0 = Env0 ^ env_globals,
    set_float_lb(VarId, LB, GlobalVarMap0, GlobalVarMap),
    Env = Env0 ^ env_globals := GlobalVarMap.

(Env0 ^ var_float_ub(VarId) := UB) = Env :-
    GlobalVarMap0 = Env0 ^ env_globals,
    set_float_ub(VarId, UB, GlobalVarMap0, GlobalVarMap),
    Env = Env0 ^ env_globals := GlobalVarMap.

(Env0 ^ var_int_lb(VarId) := LB) = Env :-
    GlobalVarMap0 = Env0 ^ env_globals,
    set_int_lb(VarId, LB, GlobalVarMap0, GlobalVarMap),
    Env = Env0 ^ env_globals := GlobalVarMap.

(Env0 ^ var_int_ub(VarId) := UB) = Env :-
    GlobalVarMap0 = Env0 ^ env_globals,
    set_int_ub(VarId, UB, GlobalVarMap0, GlobalVarMap),
    Env = Env0 ^ env_globals := GlobalVarMap.

(Env0 ^ var_set_ub(VarId) := Range) = Env :-
    GlobalVarMap0 = Env0 ^ env_globals,
    set_int_set_bounds(VarId, Range, GlobalVarMap0, GlobalVarMap),
    Env = Env0 ^ env_globals := GlobalVarMap.

%-----------------------------------------------------------------------------%

Env ^ var_value(VarId) = MZ :-
    ( if map.search(Env ^ env_locals, VarId, MZPrime) then
        MZ = MZPrime
      else
        map.lookup(Env ^ env_globals, VarId, VarInfo),
        VarInfo ^ vi_value = yes(MZ)
    ).

(!.Env ^ var_value(VarId) := MZ) = !:Env :-
    LocalVarMap0 = !.Env ^ env_locals,
    ( if map.search(LocalVarMap0, VarId, _) then
        map.det_update(VarId, MZ, LocalVarMap0, LocalVarMap),
        !Env ^ env_locals := LocalVarMap
    else
        % We have to ensure that bool, int, and float globals are in simplified
        % (i.e. FlatZinc) form since these will be output in the FlatZinc
        % model.

        Context = [["In assignment to '", var_name(VarId), "'.\n"]],
        simplify_mzn_expr(Context, MZ, SimpleMZ, !Env),
        GlobalVarMap0 = !.Env ^ env_globals,
        map.lookup(GlobalVarMap0, VarId, VarInfo0),

        % Sanity check: avoid creating self-assignments.
        ( if
            mzn_expr_to_global_var_id(SimpleMZ, SimpleVarId),
            VarId = SimpleVarId
          then
            minizinc_internal_error(Context, $pred,
                "self-assignment to global var detected")
          else
            true
        ),
        VarInfo = VarInfo0 ^ vi_value := yes(SimpleMZ),
        map.det_update(VarId, VarInfo, GlobalVarMap0, GlobalVarMap),
        !Env ^ env_globals := GlobalVarMap
    ).

    % Ensure that a bool, float, or int expression has been simplified
    % prior to assigning it to a global variable.
    %
:- pred simplify_mzn_expr(error_context::in, mzn_expr::in, mzn_expr::out,
    env::in, env::out) is det.

simplify_mzn_expr(Context, MZ0, MZ, !Env) :-
    ( if
        MZ0 = mzn_expr(RawMZ0, Anns),
        (
            RawMZ0 = bool_expr(A),
            simplify_bool(Context, A, SimpleA, !Env),
            RawMZ = bool_expr(SimpleA)
        ;
            RawMZ0 = float_expr(A),
            simplify_float(Context, A, SimpleA, !Env),
            RawMZ = float_expr(SimpleA)
        ;
            RawMZ0 = int_expr(A),
            simplify_int(Context, A, SimpleA, !Env),
            RawMZ = int_expr(SimpleA)
        ;
            RawMZ0 = bool_array_expr(array_items(IndexRanges, As)),
            array.map_foldl(simplify_bool(Context), As, SimpleAs, !Env),
            RawMZ = bool_array_expr(array_items(IndexRanges, SimpleAs))
        ;
            RawMZ0 = float_array_expr(array_items(IndexRanges, As)),
            array.map_foldl(simplify_float(Context), As, SimpleAs, !Env),
            RawMZ = float_array_expr(array_items(IndexRanges, SimpleAs))
        ;
            RawMZ0 = int_array_expr(array_items(IndexRanges, As)),
            array.map_foldl(simplify_int(Context), As, SimpleAs, !Env),
            RawMZ = int_array_expr(array_items(IndexRanges, SimpleAs))
        )
    then
        MZ = mzn_expr(RawMZ, Anns)
    else
        MZ = MZ0
    ).

    % If the expressions is a Boolean, float or int global variable, then
    % return the var id of that global; fail otherwise.
    %
:- pred mzn_expr_to_global_var_id(mzn_expr::in, var_id::out) is semidet.

mzn_expr_to_global_var_id(MZ, VarId) :-
    MZ = mzn_expr(RawMZ, _),
    (
        RawMZ = bool_expr(bool_var(var_no_index(VarId)))
    ;
        RawMZ = float_expr(float_var(var_no_index(VarId)))
    ;
        RawMZ = int_expr(int_var(var_no_index(VarId)))
    ).

%-----------------------------------------------------------------------------%

Env ^ var_type(VarId) = MZType :-
    GlobalVarMap = Env ^ env_globals,
    MZType = get_updated_var_type(GlobalVarMap, VarId).

Env ^ var_inst(VarId) = VarInst :-
    VarInfo = map.lookup(Env ^ env_globals, VarId),
    VarInst = VarInfo ^ vi_inst.

%-----------------------------------------------------------------------------%

:- pred maybe_get_bounds_from_type(mzn_type::in, maybe(var_bounds)::out)
    is det.

maybe_get_bounds_from_type(MZType, MaybeVarBounds) :-
    % Get the bounds, if any, from the type.
    (
        ( MZType = mzn_int(Bounds)
        ; MZType = mzn_int_set(Bounds)
        ; MZType = mzn_int_array(Bounds)
        ; MZType = mzn_int_set_array(Bounds)
        ),
        (
            Bounds = int_range_unbounded,
            MaybeVarBounds = no
        ;
            Bounds = int_range_lb_ub(LB, UB),
            VarBounds = int_bounds(LB, UB),
            MaybeVarBounds = yes(VarBounds)
        ;
            Bounds = int_range_set(Set),
            VarBounds = int_set_bounds(Set),
            MaybeVarBounds = yes(VarBounds)
        )
    ;
        ( MZType = mzn_float(Bounds)
        ; MZType = mzn_float_array(Bounds)
        ),
        (
            Bounds = float_range_unbounded,
            MaybeVarBounds = no
        ;
            Bounds = float_range_lb_ub(LB, UB),
            VarBounds = float_bounds(LB, UB),
            MaybeVarBounds = yes(VarBounds)
        ;
            Bounds = float_range_set(Set),
            Xs = set.to_sorted_list(Set),
            (
                Xs = [LB | _],
                UB = list.det_last(Xs),
                VarBounds = float_bounds(LB, UB),
                MaybeVarBounds = yes(VarBounds)
            ;
                Xs = [],
                % XXX We could return bounds here.
                MaybeVarBounds = no
            )
        )
    ;
        ( MZType = mzn_bool
        ; MZType = mzn_bool_array
        ; MZType = mzn_bool_set
        ; MZType = mzn_bool_set_array
        ; MZType = mzn_float_set(_)
        ; MZType = mzn_float_set_array(_)
        ; MZType = mzn_string
        ; MZType = mzn_string_array
        ; MZType = mzn_ann
        ; MZType = mzn_ann_array
        ; MZType = mzn_bottom
        ; MZType = mzn_bottom_array
        ),
        MaybeVarBounds = no
    ).

%-----------------------------------------------------------------------------%

Env ^ var_anns(VarId) = Anns :-
    GlobalVarMap = Env ^ env_globals,
    map.lookup(GlobalVarMap, VarId, VarInfo),
    Anns = VarInfo ^ vi_anns.

(Env0 ^ var_anns(VarId) := Anns) = Env :-
    GlobalVarMap0 = Env0 ^ env_globals,
    map.lookup(GlobalVarMap0, VarId, VarInfo0),
    VarInfo = VarInfo0 ^ vi_anns := Anns,
    map.det_update(VarId, VarInfo, GlobalVarMap0, GlobalVarMap),
    Env = Env0 ^ env_globals := GlobalVarMap.

%-----------------------------------------------------------------------------%

mark_var_for_output(VarId, !Env) :-
    GlobalVarMap0 = !.Env ^ env_globals,
    ( if
        map.search(GlobalVarMap0, VarId, VarInfo0),
        VarInfo0 ^ vi_inst = var_is_var
    then
        VarInfo = VarInfo0 ^ vi_output := var_is_output,
        map.det_update(VarId, VarInfo, GlobalVarMap0, GlobalVarMap),
        !Env ^ env_globals := GlobalVarMap
    else
        % The variable is either local or a parameter.
        true
    ).

%-----------------------------------------------------------------------------%

impose_constraint(Context, ErrMsg, Z, !Env) :-
    simplify_bool_cv(Context, Z, CVZ, !Env),
    (
        CVZ = boolcv_const(yes)
    ;
        CVZ = boolcv_const(no),
        ( if !.Env ^ reifying = reifying(_ : bool_exprs) then
            !Env ^ reifying := reifying([bool_const(no)])
        else
            model_inconsistency_detected(Context, ErrMsg)
        )
    ;
        CVZ = boolcv_var(MZVar),
        ( if !.Env ^ reifying = reifying(ReifVars) then
            !Env ^ reifying := reifying([bool_var(MZVar) | ReifVars])
        else
            MZTrue = bool_to_mzn_expr(bool_const(yes)),
            ( if MZVar = var_no_index(VarId) then
                !Env ^ var_value(VarId) := MZTrue
            else
                add_constraint(Context, "bool_eq",
                    [bool_to_mzn_expr(bool_var(MZVar)), MZTrue], no_anns, !Env)
            )
        )
    ).

%-----------------------------------------------------------------------------%

:- pred add_int_set_constraint(string::in, mzn_expr::in, set(int)::in,
    env::in, env::out) is det.

add_int_set_constraint(ConstraintName, MZA, Set, !Env) :-
    Context = [],
    Anns = no_anns,
    MZB = int_set_to_mzn_expr(set_items(Set)),
    add_constraint(Context, ConstraintName, [MZA, MZB], Anns, !Env).

%-----------------------------------------------------------------------------%

:- pred add_constraint_to_add(mzn_constraint_to_add::in,
    env::in, env::out) is det.

add_constraint_to_add(ConstraintToAdd, !Env) :-
    ConstraintToAdd =
        mzn_constraint_to_add(Context, ConstraintName, Args, Anns),
    add_constraint(Context, ConstraintName, Args, Anns, !Env).

add_constraint(Context, ConstraintName, Args, Anns0, !Env) :-
    Anns = join_anns(Anns0, !.Env ^ anns),
    ( if
        ProcNo = 1,
        !.Env ^ predicate(ConstraintName, ProcNo) = PredInfo,
        PredInfo = predicate_info(_, _, MaybeBody),
        MaybeBody = yes(_),
        Reifying = !.Env ^ reifying,
        !Env ^ reifying := not_reifying,
        flatten_predicate(Context, ConstraintName, ProcNo, Args, Anns, Z,
            !Env),
        simplify_bool_cv(Context, Z, CVZ, !Env),
        !Env ^ reifying := Reifying
    then
        (
            CVZ = boolcv_const(yes)
        ;
            CVZ = boolcv_const(no),
            unsatisfiable_constraint(Context)
        ;
            CVZ = boolcv_var(_),
            SimpleZ = bool_const_or_var_to_expr(CVZ),
            (
                Reifying = not_reifying,
                ( if
                    flatten_bool_bool_to_bool(Context, Anns,
                        bb2b_eq, SimpleZ, bool_const(yes), EqZ, !Env)
                then
                    ( if EqZ = bool_const(yes) then
                        true
                    else if EqZ = bool_const(no) then
                        unsatisfiable_constraint(Context)
                    else
                        minizinc_internal_error(Context, $pred,
                            "bool_var result.\n")
                    )
                else
                    minizinc_internal_error(Context, $pred,
                        "bool_eq failed!\n")
                )
            ;
                Reifying = reifying(ReifVars : bool_exprs),
                !Env ^ reifying := reifying([SimpleZ | ReifVars])
            )
        )
    else
        Constraint = mzn_constraint(ConstraintName, Args, Anns),
        OldConstraints = !.Env ^ env_constraints,
        mzn_constraint_set_insert(Constraint, OldConstraints, NewConstraints),
        !Env ^ env_constraints := NewConstraints
    ).

%-----------------------------------------------------------------------------%

get_maybe_solve_goal(Env) = Env ^ env_solve_goal.

set_solve_goal(MZSolveGoal, !Env) :-
    (
        !.Env ^ env_solve_goal = no,
        !Env ^ env_solve_goal := yes(MZSolveGoal)
    ;
        !.Env ^ env_solve_goal = yes(_),
        minizinc_user_error([], "Models cannot have multiple solve items.\n")
    ).

update_solve_goal(MZSolveGoal, !Env) :-
    (
        !.Env ^ env_solve_goal = no,
        minizinc_internal_error([], $pred, "solve goal not set")
    ;
        !.Env ^ env_solve_goal = yes(_),
        !Env ^ env_solve_goal := yes(MZSolveGoal)
    ).

%-----------------------------------------------------------------------------%

Env ^ cse_lookup(PartialConstraint) =
    Env ^ env_cse_map ^ elem(PartialConstraint).

%-----------------------------------------------------------------------------%

add_cse_var(PartialConstraint, VarId, !Env) :-
    !Env ^ env_cse_map ^ elem(PartialConstraint) := VarId.

%-----------------------------------------------------------------------------%

diff_constraints_in_envs(InitEnv, FinalEnv, NewConstraints) :-
    InitConstraints = InitEnv ^ env_constraints,
    FinalConstraints = FinalEnv ^ env_constraints,
    mzn_constraint_set_diff(FinalConstraints, InitConstraints, NewConstraints).

construct_env(Reifying, Anns, LocalVarMap, TmpVarCounter, CSEMap, Model,
        Env) :-
    Model = model(PredMap, GlobalVarMap, Constraints, SolveGoal),
    Env = env(LocalVarMap, GlobalVarMap, Reifying, Anns, PredMap, CSEMap,
        Constraints, TmpVarCounter, SolveGoal).

deconstruct_env(Env, Reifying, Anns, LocalVarMap, TmpVarCounter, CSEMap,
        Model) :-
    Env = env(LocalVarMap, GlobalVarMap, Reifying, Anns, PredMap, CSEMap,
        Constraints, TmpVarCounter, SolveGoal),
    Model = model(PredMap, GlobalVarMap, Constraints, SolveGoal).

get_model(Env, Model) :-
    Env = env(_LocalVarMap, GlobalVarMap, _Reifying, _Anns,
        PredMap, _CSEMap, Constraints, _TmpCounter, MaybeSolveGoal),
    Model = model(PredMap, GlobalVarMap, Constraints, MaybeSolveGoal).

set_model(Model, !Env) :-
    Model = model(PredMap, GlobalVarMap, Constraints, MaybeSolveGoal),
    !.Env = env(LocalVarMap, _GlobalVarMap, Reifying, Anns,
        _PredMap, CSEMap, _Constraints, TmpCounter, _MaybeSolveGoal),
    !:Env = env(LocalVarMap, GlobalVarMap, Reifying, Anns,
        PredMap, CSEMap, Constraints, TmpCounter, MaybeSolveGoal).

extend_model_to_env(TmpCounter, Model, Env) :-
    Model = model(PredMap, GlobalVarMap, Constraints, MaybeSolveGoal),
    map.init(LocalVarMap),
    Reifying = not_reifying,
    Anns = no_anns,
    map.init(CSEMap),
    Env = env(LocalVarMap, GlobalVarMap, Reifying, Anns,
        PredMap, CSEMap, Constraints, TmpCounter, MaybeSolveGoal).

%-----------------------------------------------------------------------------%

flatten_ti_expr(Context, TIExpr, VarPar, MZType, IndexRanges, !Env) :-
    TIExpr = ti_expr(RawTIExpr, _TIExprInfo),
    RawTIExpr = raw_ti_expr(VarPar0, BaseTIExprTail),
    (
        BaseTIExprTail = bte_int,
        VarPar = VarPar0,
        MZType = mzn_int(int_range_unbounded),
        IndexRanges = []
    ;
        BaseTIExprTail = bte_range_expr_as_type_expr(LBExpr, UBExpr),
        VarPar = VarPar0,
        flatten_expr(Context, LBExpr, MZLB, !Env),
        flatten_expr(Context, UBExpr, MZUB, !Env),
        ( if
            MZLB = mzn_expr(float_expr(float_const(FLB)), _),
            MZUB = mzn_expr(float_expr(float_const(FUB)), _)
        then
            MZType = mzn_float(float_range_lb_ub(FLB, FUB))
        else if
            MZLB = mzn_expr(int_expr(int_const(ILB)), _),
            MZUB = mzn_expr(int_expr(int_const(IUB)), _)
        then
            MZType = mzn_int(int_range_lb_ub(ILB, IUB))
        else
            minizinc_user_error(Context,
                "Only float and integer '..' ranges are permitted\n")
        ),
        IndexRanges = []
    ;
        BaseTIExprTail = bte_array_of(IndexRangeTIExprs, ElemTIExpr, _),
        list.map_foldl(flatten_index_range_ti_expr(Context),
            IndexRangeTIExprs, IndexRanges, !Env),
        flatten_ti_expr(Context, ElemTIExpr, VarPar, ElemMZType, _, !Env),
        (
            ElemMZType = mzn_bool,
            MZType = mzn_bool_array
        ;
            ElemMZType = mzn_float(FloatRange),
            MZType = mzn_float_array(FloatRange)
        ;
            ElemMZType = mzn_int(IntRange),
            MZType = mzn_int_array(IntRange)
        ;
            ElemMZType = mzn_bool_set,
            MZType = mzn_bool_set_array
        ;
            ElemMZType = mzn_float_set(FloatRange),
            MZType = mzn_float_set_array(FloatRange)
        ;
            ElemMZType = mzn_int_set(IntRange),
            MZType = mzn_int_set_array(IntRange)
        ;
            ElemMZType = mzn_string,
            MZType = mzn_string_array
        ;
            ElemMZType = mzn_ann,
            MZType = mzn_ann_array
        ;
            ElemMZType = mzn_bottom,
            MZType = mzn_bottom_array
        ;
            ( ElemMZType = mzn_bool_array
            ; ElemMZType = mzn_float_array(_)
            ; ElemMZType = mzn_int_array(_)
            ; ElemMZType = mzn_bool_set_array
            ; ElemMZType = mzn_float_set_array(_)
            ; ElemMZType = mzn_int_set_array(_)
            ; ElemMZType = mzn_string_array
            ; ElemMZType = mzn_ann_array
            ; ElemMZType = mzn_bottom_array
            ),
            minizinc_user_error(Context,
                "Minizinc does not support arrays of arrays.\n")
        )
    ;
        BaseTIExprTail = bte_ident(VarId),
        VarPar = VarPar0,
        ( if
            !.Env ^ var_value(VarId) = MZ,
            (
                MZ = mzn_expr(float_set_expr(set_items(FSet)), _),
                MZType0 = mzn_float(float_range_set(FSet))
            ;
                MZ = mzn_expr(int_set_expr(set_items(ISet)), _),
                MZType0 = mzn_int(int_range_set(intset.from_set(ISet)))
            )
        then
            MZType = MZType0
        else
            minizinc_user_error(Context,
                "'" ++ var_name(VarId) ++ "' " ++
                "must be assigned a set of float\n" ++
                "or set of int to be used as a type.\n")
        ),
        IndexRanges = []
    ;
        BaseTIExprTail = bte_bool,
        VarPar = VarPar0,
        MZType = mzn_bool,
        IndexRanges = []
    ;
        BaseTIExprTail = bte_float,
        VarPar = VarPar0,
        MZType = mzn_float(float_range_unbounded),
        IndexRanges = []
    ;
        BaseTIExprTail = bte_set_of(ElemTIExpr),
        flatten_ti_expr(Context, ElemTIExpr, _VarPar, ElemMZType, _, !Env),
        ( if
            (
                ElemMZType = mzn_bool,
                MZType0 = mzn_bool_set
            ;
                ElemMZType = mzn_float(FloatRange),
                MZType0 = mzn_float_set(FloatRange)
            ;
                ElemMZType = mzn_int(IntRange),
                MZType0 = mzn_int_set(IntRange)
            )
        then
            VarPar = VarPar0,
            MZType = MZType0
        else
            minizinc_user_error(Context,
                "MiniZinc only supports set of bool, set of float, " ++
                "and set of int.\n")
        ),
        IndexRanges = []
    ;
        BaseTIExprTail = bte_set_expr_as_type_expr(ItemExprs),
        VarPar = VarPar0,
        list.map_foldl(flatten_expr(Context), ItemExprs, MZs, !Env),
        (
            MZs = [],
            minizinc_user_error(Context,
                "Cannot use an empty set as a type.\n")
        ;
            MZs = [MZ | _],
            ( if
                (
                    MZ = mzn_expr(float_expr(_), _),
                    minizinc_user_error(Context,
                        "'{...}' is not supported as a float type.\n")
                ;
                    MZ = mzn_expr(int_expr(_), _),
                    P = ( pred(mzn_expr(int_expr(int_const(F)), _)::in,
                        F::out) is semidet ),
                    list.map(P, MZs, FXs),
                    FSet = set.from_list(FXs),
                    MZType0 = mzn_int(int_range_set(intset.from_set(FSet)))
                )
            then
                MZType = MZType0
            else
                minizinc_user_error(Context,
                    "Not a well formed literal set of int or " ++
                    "literal set of float.\n")
            )
        ),
        IndexRanges = []
    ;
        BaseTIExprTail = bte_string,
        VarPar = VarPar0,
        MZType = mzn_string,
        IndexRanges = []
    ;
        BaseTIExprTail = bte_ann,
        VarPar = VarPar0,
        MZType = mzn_ann,
        IndexRanges = []
    ;
        ( BaseTIExprTail = bte_typeinst_var(_)
        ; BaseTIExprTail = bte_any_typeinst_var(_)
        ; BaseTIExprTail = bte_tuple_of(_)
        ; BaseTIExprTail = bte_bottom
        ; BaseTIExprTail = bte_error
        ),
        minizinc_internal_error(Context, $pred,
            "expected a MiniZinc type.\n")
    ).

:- pred flatten_index_range_ti_expr(error_context::in, ti_expr::in,
    index_range::out, env::in, env::out) is det.

flatten_index_range_ti_expr(Context, TIExpr, IndexRange, !Env) :-
    flatten_ti_expr(Context, TIExpr, VarPar, MZType, IndexRanges, !Env),
    ( if
        VarPar \= var,
        IndexRanges = [],
        MZType = mzn_int(IntRange)
    then
        (
            IntRange = int_range_unbounded,
            IndexRange = index_implicit
        ;
            IntRange = int_range_lb_ub(LB, UB),
            IndexRange = index_range(LB, UB)
        ;
            IntRange = int_range_set(Set),
            % JJJ FIXME - INTSET REP.
            IndexRange = set_to_index_range(Context, !.Env ^ env_globals,
                set.from_sorted_list(intset.to_sorted_list(Set)))
        )
    else
        minizinc_user_error(Context, "Invalid index range.\n")
    ).

%-----------------------------------------------------------------------------%

replace_implicit_indexes(MZValue, !IndexRanges) :-
    MZValue = mzn_expr(RawExpr, _Anns),
    (
        ( 
            RawExpr = bool_array_expr(BoolArrayExpr),
            ValueIndexRanges = get_index_ranges(BoolArrayExpr)
        ;
            RawExpr = bool_set_array_expr(BoolSetArrayExpr),
            ValueIndexRanges = get_index_ranges(BoolSetArrayExpr)
        ;
            RawExpr = float_array_expr(FloatArrayExpr),
            ValueIndexRanges = get_index_ranges(FloatArrayExpr)
        ;
            RawExpr = float_set_array_expr(FloatSetArrayExpr),
            ValueIndexRanges = get_index_ranges(FloatSetArrayExpr)
        ;
            RawExpr = int_array_expr(IntArrayExpr),
            ValueIndexRanges = get_index_ranges(IntArrayExpr)
        ;
            RawExpr = int_set_array_expr(IntSetArrayExpr),
            ValueIndexRanges = get_index_ranges(IntSetArrayExpr)
        ;
            RawExpr = string_array_expr(StringArrayExpr),
            ValueIndexRanges = get_index_ranges(StringArrayExpr)
        ;
            RawExpr = ann_array_expr(AnnArrayExpr),
            ValueIndexRanges = get_index_ranges(AnnArrayExpr)
        ;
            RawExpr = bottom_array_expr(BottomArrayExpr),
            ValueIndexRanges = get_index_ranges(BottomArrayExpr)
        ),
        !:IndexRanges = list.map_corresponding(replace_implicit_index,
            ValueIndexRanges, !.IndexRanges)
    ;
        ( RawExpr = bool_expr(_)
        ; RawExpr = bool_set_expr(_)
        ; RawExpr = float_expr(_)
        ; RawExpr = float_set_expr(_)
        ; RawExpr = int_expr(_)
        ; RawExpr = int_set_expr(_)
        ; RawExpr = string_expr(_)
        ; RawExpr = ann_expr(_)
        ; RawExpr = bottom_expr(_)
        )
    ).

:- func replace_implicit_index(index_range, index_range) = index_range.

replace_implicit_index(ValueIndex, MaybeImplicitIndex) = ArrayIndex :-
    (
        MaybeImplicitIndex = index_range(_, _),
        ArrayIndex = MaybeImplicitIndex
    ;
        MaybeImplicitIndex = index_implicit,
        (
            ValueIndex = index_implicit,
            unexpected($pred, "inferred implicit array index")
        ;
            ValueIndex = index_range(_, _),
            ArrayIndex = ValueIndex
        )
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

flatten_post_process_vars(!Env) :-
    ensure_var_bounds_are_sensible(!Env),
    condense_tmp_vars(!Env).

%-----------------------------------------------------------------------------%

    % Post-processing step: ensure that each variable's bounds are either +/-
    % infinity or neither are +/- infinity.  Half-open domains are replaced
    % with completely open domains plus an inequality constraint.
    %
:- pred ensure_var_bounds_are_sensible(env::in, env::out) is det.

ensure_var_bounds_are_sensible(!Env) :-
    Globals = !.Env ^ env_globals,
    VarIds = map.keys(Globals),
    list.foldl(ensure_this_var_bounds_are_sensible, VarIds, !Env).

%-----------------------------------------------------------------------------%

    % It is only critical to do this for var int and var set of int
    % variables.
    %
:- pred ensure_this_var_bounds_are_sensible(var_id::in, env::in, env::out)
    is det.

ensure_this_var_bounds_are_sensible(VarId, !Env) :-
    MZType = !.Env ^ var_type(VarId),
    ( if MZType = mzn_int(_) then
        ensure_int_var_bounds_are_sensible(VarId, !Env)
    else if MZType = mzn_int_set(_) then
        ensure_int_set_var_bounds_are_sensible(VarId, !Env)
    else
        true
    ).

%-----------------------------------------------------------------------------%

:- pred ensure_int_var_bounds_are_sensible(var_id::in, env::in, env::out)
    is det.

ensure_int_var_bounds_are_sensible(VarId, !Env) :-
    Context = [["Refining bounds on '", var_name(VarId), "'.\n"]],
    GlobalVarMap0 = !.Env ^ env_globals,
    map.lookup(GlobalVarMap0, VarId, VarInfo0),
    VarBounds0 = VarInfo0 ^ vi_bounds,
    bounds_get_int_lb_ub(VarBounds0, LB, UB),
    ( if LB \= int_minus_infinity then
        ( if UB = int_plus_infinity then
            % Only the LB is present.
            % Convert it into a separate constraint.
            !Env ^ var_int_lb(VarId) := int_minus_infinity,
            add_constraint(Context, "int_le",
                [int_to_mzn_expr(int_const(LB)),
                 int_to_mzn_expr(int_var(var_no_index(VarId)))],
                no_anns, !Env)
        else
            % Both LB and UB are present: no changes needed.
            true
        )
    else if UB \= int_plus_infinity then
        % Only the UB is present.
        % Convert it into a separate constraint.
        !Env ^ var_int_ub(VarId) := int_plus_infinity,
        add_constraint(Context, "int_le",
            [int_to_mzn_expr(int_var(var_no_index(VarId))),
             int_to_mzn_expr(int_const(UB))],
            no_anns, !Env)
    else
        % Neither bound is present.
        % Try to infer bounds from the value (if it has one assigned).
        ( if
            MZ = !.Env ^ var_value(VarId),
            A = mzn_expr_to_int(Context, MZ),
            get_int_expr_lb_ub(Context, GlobalVarMap0, A, ALB, AUB),
            ALB \= int_minus_infinity,
            AUB \= int_plus_infinity
        then
            !Env ^ var_int_lb(VarId) := ALB,
            !Env ^ var_int_ub(VarId) := AUB
        else
            true
        )
    ).

%-----------------------------------------------------------------------------%

:- pred ensure_int_set_var_bounds_are_sensible(var_id::in, env::in, env::out)
    is det.

ensure_int_set_var_bounds_are_sensible(VarId, !Env) :-
    ( if
        !.Env ^ var_set_ub(VarId) = int_range_unbounded,
        MZ = !.Env ^ var_value(VarId),
        Context = [ ["Refining bounds on '", var_name(VarId), "'.\n"] ],
        A = mzn_expr_to_int_set(Context, MZ),
        get_int_set_expr_lb_ub(!.Env ^ env_globals, A, LB, UB),
        LB \= int_minus_infinity,
        UB \= int_plus_infinity
    then
        !Env ^ var_set_ub(VarId) := int_range_lb_ub(LB, UB)
    else
        true
    ).

%-----------------------------------------------------------------------------%

    % Condense groups of tmp vars with the same domain into arrays.
    % This reduces the size of the resulting FlatZinc model.
    %
:- pred condense_tmp_vars(env::in, env::out) is det.

condense_tmp_vars(!Env) :-
    true.   % XXX FILL THIS IN.

%-----------------------------------------------------------------------------%

:- pred debug_look_for_this(T::in) is semidet.

debug_look_for_this(_) :-
    semidet_true.

%-----------------------------------------------------------------------------%
:- end_module flatten.env.
%-----------------------------------------------------------------------------%
