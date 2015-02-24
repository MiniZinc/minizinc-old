%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2009 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Ralph Becket <rafe@csse.unimelb.edu.au>
%
% Output .fzn and .ozn files.
%
%-----------------------------------------------------------------------------%

:- module flatten.output.
:- interface.

:- import_module flatten.env.

:- import_module zinc_ast.
:- import_module zinc_frontend2.

:- import_module bool.
:- import_module io.

%-----------------------------------------------------------------------------%

    % Write out the FlatZinc model as represented in the env structure.
    %
:- pred write_fzn_model(io.output_stream::in, string::in, bool::in, env::in,
    io::di, io::uo) is det.

    % Write out a shell MiniZinc model containing only
    % - parameter declarations and values.
    % - variable declarations (with no assignments) for variables
    %   (except for annotation variables which are omitted entirely.)
    % appearing in the output item;
    % - the output item;
    % This file can be processed by the standalone 'minizinc' application
    % to provide formatted output.  This must be done in conjunction with
    % the solution stream produced from the evaluation of the FlatZinc
    % instance.
    %
:- pred write_ozn_model(output_destination::in, env::in, sast::in,
    io::di, io::uo) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module common_format.
%:- import_module convert_to_tfzn.
:- import_module errors.
:- import_module global_vars.
%:- import_module output_tfzn.
:- import_module types.
:- import_module utilities.

:- import_module builtins.
:- import_module types_and_insts.
:- import_module zinc_common.
:- import_module zinc_pprint.

:- import_module array.
:- import_module exception.
:- import_module list.
:- import_module map.
:- import_module maybe.
:- import_module pair.
:- import_module pprint.
:- import_module require.
:- import_module set.
:- import_module set_tree234.
:- import_module solutions.
:- import_module string.

%-----------------------------------------------------------------------------%

    % Some solvers can take advantage of the fact that a variable is a
    % function of some other variables. Such a variable, X, has its
    % declaration annotated with ':: is_defined_var' and the corresponding
    % constraint annotated with ':: defines_var(X)'.
    %
    % Some optimisations can render these annotations redundant by
    % removing variables entirely or by making them aliases of other variables.
    %
    % This pass removes any such redundant annotations.
    %
    % NOTE that this should only be called *after* topsorted_vars because
    % topsorted_vars breaks equality cycles. Calling this beforehand will
    % result in corruption of the is_defined_var annotations.
    %
:- pred prune_redundant_is_defined_var_anns(
    global_var_map::in, global_var_map::out,
    mzn_constraint_set::in, mzn_constraint_set::out) is det.

prune_redundant_is_defined_var_anns(!GlobalVarMap, !Constraints) :-
    % Prune redundant is_defined_var anns.
    map.map_values_only(prune_redundant_is_defined_var_ann, !GlobalVarMap),

    % Prune redundant defines_var anns.
    mzn_constraint_set_map(prune_redundant_defines_var_ann(!.GlobalVarMap),
        !Constraints).

    % Remove an 'is_defined_var' annotation from any var with a value.
    %
:- pred prune_redundant_is_defined_var_ann(var_info::in, var_info::out) is det.

prune_redundant_is_defined_var_ann(!VarInfo) :-
    ( if
        !.VarInfo ^ vi_value = yes(_),
        !.VarInfo ^ vi_anns = VarAnns0,
        set.contains(VarAnns0, is_defined_var)
    then
        set.delete(is_defined_var, VarAnns0, VarAnns),
        !VarInfo ^ vi_anns := VarAnns
    else
        true
    ).

    % Remove a 'defines_var(X)' annotation from any constraint that
    % doesn't mention X or where X is a variable with an assigned value.
    %
:- pred prune_redundant_defines_var_ann(global_var_map::in,
    mzn_constraint::in, mzn_constraint::out) is det.

prune_redundant_defines_var_ann(GlobalVarMap, Constraint0, Constraint) :-
    Constraint0 = mzn_constraint(Name, Args, Anns0),
    VarSet = set.union_list(list.map(vars_in_mzn_expr, Args)),
    promise_equivalent_solutions [Constraint] (
        ( if
            set.member(RedundantAnn, Anns0),
            RedundantAnn = mzn_ann("defines_var", [AnnArg]),
            set.is_singleton(vars_in_mzn_expr(AnnArg), VarId),
            (
                not set.contains(VarSet, VarId)
            ;
                map.search(GlobalVarMap, VarId, VarInfo),
                VarInfo ^ vi_value = yes(_)
            )
        then
            Anns1 = set.delete(Anns0, RedundantAnn),
            Constraint1 = mzn_constraint(Name, Args, Anns1),
            % This isn't efficient, but it should be rarely needed in practice.
            prune_redundant_defines_var_ann(GlobalVarMap,
                Constraint1, Constraint)
        else
            Constraint = Constraint0
        )
    ).

%-----------------------------------------------------------------------------%

    % Provide a topologically sorted list of the variable names in the model
    % such that if the value assigned to Y depends upon X, then Y appears
    % further down the list than X. This will update the global var map
    % to break any cyclic dependencies.
    %
:- pred topsorted_vars(var_ids::out, global_var_map::in, global_var_map::out)
    is det.

topsorted_vars(VarIds, !GlobalVarMap) :-
    InitDeps = map.init,
    map.foldl2(topsort_var, !.GlobalVarMap, InitDeps, LoopDeps,
        [], RevVarIds0),
    % It is possible for flattening to introduce cycles.
    % We need to break them here.
    % XXX zs: Updating !GlobalVarMap while iterating on it seems hinky.
    map.foldl3(break_loop_dep, !.GlobalVarMap, LoopDeps, _,
        RevVarIds0, RevVarIds, !GlobalVarMap),
    % Reverse the list of var names to get the right order.
    VarIds = list.reverse(RevVarIds).

%-----------------------------------------------------------------------------%

    % Vars that have been sorted into order have no dependents.
    % A var that is waiting to be sorted is
    % (a) on the list of a (single) var it depends on that has not been
    % sorted yet and
    % (b) has its own (possible empty) list of dependents.
    %
    % As a var is sorted, its dependents are reconsidered.  They may either
    % now take their place in the order or they may be moved on to the
    % dependents lists of other variables.
    %
:- type dependency_map == map(var_id, dependents).

:- type dependents == list(dependent).
    % An empty list indicates this var has been sorted into place.

:- type dependent
    --->    dependent(var_id, var_ids).
            % This var is waiting on the vars in the list to be topsorted.

%-----------------------------------------------------------------------------%

:- pred break_loop_dep(var_id::in, var_info::in,
    dependency_map::in, dependency_map::out, var_ids::in, var_ids::out,
    global_var_map::in, global_var_map::out) is det.

break_loop_dep(VarId, _VarInfo, !Deps, !RevVarIds, !GlobalVarMap) :-
    ( if
        map.search(!.Deps, VarId, Dependents),
        Dependents = [_ | _]
    then
        % This var is part of a cycle.
        % We need to remove its value from the environment.
        map.lookup(!.GlobalVarMap, VarId, VarInfo0),
        VarInfo = VarInfo0 ^ vi_value := no,
        map.det_update(VarId, VarInfo, !GlobalVarMap),
        !:RevVarIds = [VarId | !.RevVarIds],
        map.det_update(VarId, [], !Deps),
        list.foldl2(topsort_reconsider_var, Dependents, !Deps, !RevVarIds)
    else
        % This var has already been sorted.
        true
    ).

%-----------------------------------------------------------------------------%

:- pred topsort_var(var_id::in, var_info::in,
    dependency_map::in, dependency_map::out, var_ids::in, var_ids::out) is det.

topsort_var(VarId, VarInfo, !Deps, !RevVarIds) :-
    ( if
        VarInfo ^ vi_inst = var_is_var,
        VarInfo ^ vi_value = yes(MZ)
    then
        DepVars = mzn_expr_vars(MZ)
    else
        DepVars = []
    ),
    topsort_consider_var(VarId, DepVars, !Deps, !RevVarIds).

%-----------------------------------------------------------------------------%

:- pred topsort_consider_var(var_id::in, var_ids::in,
    dependency_map::in, dependency_map::out, var_ids::in, var_ids::out) is det.

topsort_consider_var(VarId, [], !Deps, !RevVarIds) :-
    % This var has no remaining dependencies: add it to !RevVarIds and
    % reconsider all vars waiting on this one.
    !:RevVarIds = [VarId | !.RevVarIds],
    ( if map.search(!.Deps, VarId, Dependents) then
        map.det_update(VarId, [], !Deps),
        list.foldl2(topsort_reconsider_var, Dependents, !Deps, !RevVarIds)
    else
        % There are no dependents for this var.
        map.det_insert(VarId, [], !Deps)
    ).
topsort_consider_var(VarId, [DepVar | DepVars], !Deps, !RevVarIds) :-
    % Search for a DepVar that hasn't been topsorted and add VarId
    % to its dependency_map entry.
    ( if DepVar = VarId then
        topsort_consider_var(VarId, DepVars, !Deps, !RevVarIds)
    else if map.search(!.Deps, DepVar, DepVarDependents) then
        (
            DepVarDependents = [],
            topsort_consider_var(VarId, DepVars, !Deps, !RevVarIds)
        ;
            DepVarDependents = [_ | _],
            map.set(DepVar, [dependent(VarId, DepVars) | DepVarDependents],
                !Deps)
        )
    else
        map.det_insert(DepVar, [dependent(VarId, DepVars)], !Deps)
    ).

%-----------------------------------------------------------------------------%

:- pred topsort_reconsider_var(dependent::in,
    dependency_map::in, dependency_map::out, var_ids::in, var_ids::out) is det.

topsort_reconsider_var(dependent(VarId, DepVars), !Deps, !RevVarIds) :-
    ( if map.search(!.Deps, VarId, []) then
        % This variable was part of a cycle and has already been sorted.
        true
    else
        topsort_consider_var(VarId, DepVars, !Deps, !RevVarIds)
    ).

%-----------------------------------------------------------------------------%

    % Return the list of variable names in a simplified (FlatZinc) value.
    %
:- func mzn_expr_vars(mzn_expr) = list(var_id).

mzn_expr_vars(Expr) = SortedVarIds :-
    accumulate_mzn_expr_vars(Expr, [], VarIds),
    list.sort_and_remove_dups(VarIds, SortedVarIds).

:- pred accumulate_mzn_expr_vars(mzn_expr::in,
    list(var_id)::in, list(var_id)::out) is det.

accumulate_mzn_expr_vars(mzn_expr(RawMZ, Anns), !VarIds) :-
    (
        RawMZ = bool_expr(BoolExpr),
        ( if BoolExpr = bool_var(MZVar) then
            !:VarIds = [mzn_var_id(MZVar) | !.VarIds]
        else
            true
        )
    ;
        RawMZ = float_expr(FloatExpr),
        ( if FloatExpr = float_var(MZVar) then
            !:VarIds = [mzn_var_id(MZVar) | !.VarIds]
        else
            true
        )
    ;
        RawMZ = int_expr(IntExpr),
        ( if IntExpr = int_var(MZVar) then
            !:VarIds = [mzn_var_id(MZVar) | !.VarIds]
        else
            true
        )
    ;
        RawMZ = int_set_expr(IntSetExpr),
        ( if IntSetExpr = set_var(MZVar) then
            !:VarIds = [mzn_var_id(MZVar) | !.VarIds]
        else
            true
        )
    ;
        RawMZ = bool_array_expr(BoolArrayExpr),
        (
            BoolArrayExpr = array_var(_, VarId),
            !:VarIds = [VarId | !.VarIds]
        ;
            BoolArrayExpr = array_items(_, Items),
            array.foldl(accumulate_bool_var_ids, Items, !VarIds)
        )
    ;
        RawMZ = int_array_expr(IntArrayExpr),
        (
            IntArrayExpr = array_var(_, VarId),
            !:VarIds = [VarId | !.VarIds]
        ;
            IntArrayExpr = array_items(_, Items),
            array.foldl(accumulate_int_var_ids, Items, !VarIds)
        )
    ;
        RawMZ = int_set_array_expr(IntSetArrayExpr),
        (
            IntSetArrayExpr = array_var(_, VarId),
            !:VarIds = [VarId | !.VarIds]
        ;
            IntSetArrayExpr = array_items(_, Items),
            array.foldl(accumulate_int_set_var_ids, Items, !VarIds)
        )
    ;
        RawMZ = float_array_expr(FloatArrayExpr),
        (
            FloatArrayExpr = array_var(_, VarId),
            !:VarIds = [VarId | !.VarIds]
        ;
            FloatArrayExpr = array_items(_, Items),
            array.foldl(accumulate_float_var_ids, Items, !VarIds)
        )
    ;
        ( RawMZ = ann_expr(_)
        ; RawMZ = ann_array_expr(_)
        ; RawMZ = bool_set_expr(_)
        ; RawMZ = bool_set_array_expr(_)
        ; RawMZ = bottom_expr(_)
        ; RawMZ = bottom_array_expr(_)
        ; RawMZ = float_set_expr(_)
        ; RawMZ = float_set_array_expr(_)
        ; RawMZ = string_expr(_)
        ; RawMZ = string_array_expr(_)
        )
    ),
    set.fold(accumulate_mzn_expr_vars_in_ann, Anns, !VarIds).

:- pred accumulate_mzn_expr_vars_in_ann(mzn_ann::in,
    list(var_id)::in, list(var_id)::out) is det.

accumulate_mzn_expr_vars_in_ann(Ann, !VarIds) :-
    (
        Ann = mzn_ann(_AnnName, AnnMZs),
        list.foldl(accumulate_mzn_expr_vars, AnnMZs, !VarIds)
    ;
        Ann = mzn_ann_var(_)
    ).

:- pred accumulate_bool_var_ids(bool_expr::in,
    list(var_id)::in, list(var_id)::out) is det.

accumulate_bool_var_ids(BoolExpr, !VarIds) :-
    ( if BoolExpr = bool_var(MZVar) then
        !:VarIds = [mzn_var_id(MZVar) | !.VarIds]
    else
        true
    ).

:- pred accumulate_int_var_ids(int_expr::in,
    list(var_id)::in, list(var_id)::out) is det.

accumulate_int_var_ids(IntExpr, !VarIds) :-
    ( if IntExpr = int_var(MZVar) then
        !:VarIds = [mzn_var_id(MZVar) | !.VarIds]
    else
        true
    ).

:- pred accumulate_int_set_var_ids(int_set_expr::in,
    list(var_id)::in, list(var_id)::out) is det.

accumulate_int_set_var_ids(IntSetExpr, !VarIds) :-
    ( if IntSetExpr = set_var(MZVar) then
        !:VarIds = [mzn_var_id(MZVar) | !.VarIds]
    else
        true
    ).

:- pred accumulate_float_var_ids(float_expr::in,
    list(var_id)::in, list(var_id)::out) is det.

accumulate_float_var_ids(FloatExpr, !VarIds) :-
    ( if FloatExpr = float_var(MZVar) then
        !:VarIds = [mzn_var_id(MZVar) | !.VarIds]
    else
        true
    ).

%-----------------------------------------------------------------------------%

write_fzn_model(OutputStream, _ModelFileName, _Informal, Env0, !IO) :-
    get_model(Env0, Model0),
    Model0 = model(PredMap, GlobalVarMap0, Constraints0, MaybeMZSolveGoal),
    topsorted_vars(VarIds, GlobalVarMap0, GlobalVarMap1),
    prune_redundant_is_defined_var_anns(GlobalVarMap1, GlobalVarMap,
        Constraints0, Constraints),
    Model = model(PredMap, GlobalVarMap, Constraints, MaybeMZSolveGoal),
    set_model(Model, Env0, Env),

    % XXX We should not need to create and use Env, but some of the predicates
    % that write the model flatten type_inst expressions, and the predicate
    % that does that, flatten_ti_expr, needs an environment, even though
    % it shouldn't.
    (
        MaybeMZSolveGoal = yes(MZSolveGoal),
% This call can be used to check whether we can convert all the FlatZinc
% models produced by mzn2fzn to the typed representation. We can.
%       convert_model_to_tfzn(ModelFileName, PredMap, GlobalVarMap, VarIds,
%           set_tree234.to_sorted_list(Constraints), MZSolveGoal, TFzn, !IO),
%       io.open_output(ModelFileName ++ ".tfzn", Res, !IO),
%       ( if Res = ok(OS) then
%           output_tfzn(output_tfzn_opts(Informal, 5), OS, TFzn, !IO),
%           io.close_output(OS, !IO)
%       else
%           true
%       ),

        % Write out the bodyless predicate signatures to allow type checking
        % of the FlatZinc model.
        map.foldl(write_fzn_pred_decl_item(OutputStream, Env), PredMap, !IO),

        % Write out the parameter declarations.
        list.foldl(write_fzn_parameter(OutputStream, GlobalVarMap),
            VarIds, !IO),

        % Write out the variable declarations.
        list.foldl(write_fzn_variable(OutputStream, GlobalVarMap),
            VarIds, !IO),

        % Write out the constraints.
        set_tree234.fold(write_fzn_constraint_item(OutputStream),
            Constraints, !IO),

        write_fzn_solve_item(OutputStream, MZSolveGoal, !IO)
    ;
        MaybeMZSolveGoal = no,
        minizinc_user_error([], "This model needs a solve item.\n")
    ).

%-----------------------------------------------------------------------------%

    % Write out bodyless predicates to allow type checking of the FlatZinc
    % model output.
    %
:- pred write_fzn_pred_decl_item(io.output_stream::in, env::in,
    pred_proc_id::in, predicate_info::in, io::di, io::uo) is det.

write_fzn_pred_decl_item(OutputStream, Env, pred_proc_id(PredName, _ProcNo),
        PredInfo, !IO) :-
    ( if
        PredInfo = predicate_info(TIExprsAndIds, _Anns, MaybeBody),
        MaybeBody = no,
        not is_builtin_fzn_operation(PredName)
    then
        io.write_strings(OutputStream, [
            "predicate ",
            PredName,
            format_param_sigs(Env, TIExprsAndIds),
            ";\n"
        ], !IO)
      else
        true
    ).

%-----------------------------------------------------------------------------%

:- func format_param_sigs(env, ti_exprs_and_ids) = string.

format_param_sigs(Env, ParamSigs) =
    format_list(format_param_sig(Env), "(", ")", ParamSigs).

:- func format_param_sig(env, pair(ti_expr, id)) = string.

format_param_sig(Env, TI - Id) = Str :-
    Context = [],
    flatten_ti_expr(Context, TI, VarPar, MZType, IndexRanges, Env, _),
    ParamName = Id ^ id_name,
    Str = string.append_list([
        format_mzn_type(IndexRanges, VarPar, MZType),
        ": ",
        ParamName
    ]).

%-----------------------------------------------------------------------------%

:- pred write_fzn_parameter(io.text_output_stream::in, global_var_map::in,
    var_id::in, io::di, io::uo) is det.

write_fzn_parameter(OutputStream, GlobalVarMap, VarId, !IO) :-
    map.lookup(GlobalVarMap, VarId, VarInfo),
    MZType = var_get_updated_var_type(VarInfo),
    (
        % We do not emit scalar parameters in FlatZinc.
        % XXX mzn2fzn currently inlines all uses of set of int parameters.
        % I think this a bad idea - juliensf.
        ( MZType = mzn_bool
        ; MZType = mzn_float(_)
        ; MZType = mzn_int(_)
        ; MZType = mzn_int_set(_)
        )
    ;
        ( MZType = mzn_bool_array
        ; MZType = mzn_float_array(_)
        ; MZType = mzn_int_array(_)
        ; MZType = mzn_int_set_array(_)
        ),
        VarInst = VarInfo ^ vi_inst,
        (
            VarInst = var_is_var
        ;
            VarInst = var_is_par,
            IndexRanges0 = VarInfo ^ vi_index_ranges,
            (
                IndexRanges0 = [],
                IndexRanges = IndexRanges0
            ;
                IndexRanges0 = [_ | _],
                N = index_ranges_to_size(IndexRanges0),
                IndexRanges = [index_range(1, N)]
            ),
            % The call to format_fzn_par_type/3 will eliminate constrained
            % type-insts, which is what FlatZinc requires for parameters.
            TypeStr = format_fzn_par_type(IndexRanges, MZType),
            NameStr = var_name(VarId),
            MaybeVarValue = VarInfo ^ vi_value,
            (
                MaybeVarValue = yes(MZ0),
                % (Workaround bug #236 - see comments below for details.)
                deref_array_param_assignment(GlobalVarMap, MZ0, MZ),
                AssignStrs = [" = ", format_mzn_expr(MZ), ";\n"]
            ;
                MaybeVarValue = no,
                unexpected($pred, "FlatZinc parameter with no assignment")
            ),
            io.write_strings(OutputStream,
                [TypeStr, ": ", NameStr | AssignStrs], !IO)
        )
    ;
        MZType = mzn_string
    ;
        % Parameters of these types do not exist in FlatZinc.
        ( MZType = mzn_float_set(_)
        ; MZType = mzn_bool_set
        ; MZType = mzn_bool_set_array
        ; MZType = mzn_float_set_array(_)
        ; MZType = mzn_string_array
        ; MZType = mzn_ann
        ; MZType = mzn_ann_array
        ; MZType = mzn_bottom
        ; MZType = mzn_bottom_array
        )
        % unexpected($pred, "non-flatzinc type")
    ).

    % XXX Workaround for bug #236: the flattener does not eliminate aliases
    % between array parameters.  Since FlatZinc does not support parameter
    % (i.e. par as opposed to var) aliasing we have to eliminate it here.
    % This is not ideal since it means we may end up duplicating array literals
    % in the FlatZinc we emit -- it would be better to eliminate the aliased
    % parameters as a whole rather than do this.
    %
:- pred deref_array_param_assignment(global_var_map::in,
    mzn_expr::in, mzn_expr::out) is det.

deref_array_param_assignment(GlobalVarMap, !Expr) :-
    !.Expr = mzn_expr(RawExpr, _),
    (
        ( RawExpr = bool_expr(_)
        ; RawExpr = float_expr(_)
        ; RawExpr = int_expr(_)
        ; RawExpr = int_set_expr(_)
        ),
        unexpected($pred, "scalar parameter assignment")
    ;
        RawExpr = bool_array_expr(BoolArrayExpr),
        deref_array_param_assignment_2(GlobalVarMap, BoolArrayExpr, !Expr)
    ;
        RawExpr = int_array_expr(IntArrayExpr),
        deref_array_param_assignment_2(GlobalVarMap, IntArrayExpr, !Expr)
    ;
        RawExpr = float_array_expr(FloatArrayExpr),
        deref_array_param_assignment_2(GlobalVarMap, FloatArrayExpr, !Expr)
    ;
        RawExpr = int_set_array_expr(IntSetArrayExpr),
        deref_array_param_assignment_2(GlobalVarMap, IntSetArrayExpr, !Expr)
    ;
        ( RawExpr = bool_set_expr(_)
        ; RawExpr = bool_set_array_expr(_)
        ; RawExpr = float_set_expr(_)
        ; RawExpr = float_set_array_expr(_)
        ; RawExpr = string_expr(_)
        ; RawExpr = string_array_expr(_)
        ; RawExpr = bottom_expr(_)
        ; RawExpr = bottom_array_expr(_)
        ; RawExpr = ann_expr(_)
        ; RawExpr = ann_array_expr(_)
        ),
        unexpected($pred, "non-FlatZinc parameter assignment")
    ). 

:- pred deref_array_param_assignment_2(global_var_map::in,
    array_expr(T)::in, mzn_expr::in, mzn_expr::out) is det.

deref_array_param_assignment_2(GlobalVarMap, ArrayExpr, !Expr) :-
    (
        ArrayExpr = array_items(_, _)
    ;
        ArrayExpr = array_var(_, VarId),
        map.lookup(GlobalVarMap, VarId, VarInfo),
        MaybeVarValue = VarInfo ^ vi_value,
        (
            MaybeVarValue = yes(!:Expr)
        ;
            MaybeVarValue = no,
            unexpected($pred, "FlatZinc parameter with no assignment")
        )
    ).

%-----------------------------------------------------------------------------%

:- pred write_fzn_variable(io.text_output_stream::in, global_var_map::in,
    var_id::in, io::di, io::uo) is det.

write_fzn_variable(OutputStream, GlobalVarMap, VarId, !IO) :-
    map.lookup(GlobalVarMap, VarId, VarInfo),
    VarInst = VarInfo ^ vi_inst,
    (
        VarInst = var_is_par
    ;
        VarInst = var_is_var,
        IndexRanges0 = VarInfo ^ vi_index_ranges,
        (
            IndexRanges0 = [],
            IndexRanges = IndexRanges0
        ;
            IndexRanges0 = [_ | _],
            N = index_ranges_to_size(IndexRanges0),
            IndexRanges = [index_range(1, N)]
        ),
        MZType = var_get_updated_var_type(VarInfo),
        ( if
            ( MZType = mzn_string
            ; MZType = mzn_string_array
            ; MZType = mzn_ann
            ; MZType = mzn_ann_array
            )
        then
            % These types do not exist in FlatZinc.
            true
        else if
            VarInfo ^ vi_value = yes(MZ),
            MZ = mzn_expr(RawMZ, _),
            ( RawMZ = bool_array_expr(array_var(_, _))
            ; RawMZ = bool_set_array_expr(array_var(_, _))
            ; RawMZ = float_array_expr(array_var(_, _))
            ; RawMZ = float_set_array_expr(array_var(_, _))
            ; RawMZ = int_array_expr(array_var(_, _))
            ; RawMZ = int_set_array_expr(array_var(_, _))
            )
        then
            % Aliases of arrays won't appear elsewhere in the model.
            true
        else
            get_var_output_anns(VarInfo, Anns),
            Strs = [
                format_mzn_type(IndexRanges, var, MZType),
                ": ",
                var_name(VarId),
                format_mzn_anns(Anns)
            |   ( if VarInfo ^ vi_value = yes(MZ) then
                    [ " = ", format_mzn_expr(MZ), ";\n" ]
                  else
                    [ ";\n" ]
                )
            ],
            io.write_strings(OutputStream, Strs, !IO)
        )
    ).

%-----------------------------------------------------------------------------%

:- pred write_fzn_constraint_item(io.output_stream::in, mzn_constraint::in,
    io::di, io::uo) is det.

write_fzn_constraint_item(OutputStream, Constraint, !IO) :-
    Constraint = mzn_constraint(PredName0, MZs0, Anns),
    % Replace any occurrence of int_minus/3 with int_plus/3
    % with the arguments suitably permuted.
    ( if
        ( PredName0 = "int_minus", PredName1 = "int_plus"
        ; PredName0 = "float_minus", PredName1 = "float_plus"
        ),
        MZs0 = [A, B, C]
    then
        PredName = PredName1,
        MZs = [C, B, A]
    else if
        PredName0 = "float_negate",
        MZs0 = [A, B]
    then
        PredName = "float_plus",
        MZs = [A, B, mzn_expr(float_expr(float_const(0.0)), set.init)]
    else
        PredName = PredName0,
        MZs = MZs0
    ),
    io.write_strings(OutputStream, [
        "constraint ",
        PredName,
        format_list(format_mzn_expr, "(", ")", MZs),
        format_mzn_anns(Anns),
        ";\n"
    ], !IO).

%-----------------------------------------------------------------------------%

:- pred write_fzn_solve_item(io.output_stream::in, mzn_solve_goal::in,
    io::di, io::uo) is det.

write_fzn_solve_item(OutputStream, Solve0, !IO) :-
    Solve0 = mzn_solve_goal(Anns, Kind0),
    ( if
        ( Kind0 = mzn_solve_minimize(MZObjFn0)
        ; Kind0 = mzn_solve_maximize(MZObjFn0)
        ),
        MZObjFn0 = mzn_expr(RawMZ0, _),
        ( RawMZ0 = bool_expr(bool_const(_))
        ; RawMZ0 = float_expr(float_const(_))
        ; RawMZ0 = int_expr(int_const(_))
        ; RawMZ0 = int_set_expr(set_items(_))
        )
    then
        % This shouldn't happen: Boolean and set-of-int objectives shouldn't
        % make it past the type-checker.  Integer and float objectives must not
        % be integer or float literals since FlatZinc does not support that
        % and we should have introduced a dummy objective variable for them
        % in the finalise_solve_goal pass if they did occur.
        unexpected($pred, "invalid objective expression")
    else
        Kind = Kind0
    ),

    io.write_string(OutputStream, "solve ", !IO),
    AnnsStr = format_mzn_anns(Anns),
    ( if AnnsStr = "" then
        true
    else
        io.write_string(OutputStream, AnnsStr, !IO),
        io.write_string(OutputStream, " ", !IO)
    ),
    (
        Kind = mzn_solve_satisfy,
        io.write_string(OutputStream, "satisfy", !IO)
    ;
        Kind = mzn_solve_minimize(MZObjFn),
        io.write_string(OutputStream, "minimize ", !IO),
        io.write_string(OutputStream, format_mzn_expr(MZObjFn), !IO)
    ;
        Kind = mzn_solve_maximize(MZObjFn),
        io.write_string(OutputStream, "maximize ", !IO),
        io.write_string(OutputStream, format_mzn_expr(MZObjFn), !IO)
    ),
    io.write_string(OutputStream, ";\n", !IO).

%-----------------------------------------------------------------------------%

write_ozn_model(OutputDest, Env, AST, !IO) :-
    AST = sast(MznItems, _SolveItem, MaybeOutputItem),
    (
        OutputDest = output_to_file(FileName),
        io.open_output(FileName, OpenResult, !IO),
        (
            OpenResult = error(IO_Error),
            throw(IO_Error)
        ;
            OpenResult = ok(File)
        )
    ;
        OutputDest = output_to_stdout,
        io.stdout_stream(File, !IO)
    ),
    (
        MaybeOutputItem = yes(OutputItem),
        OutputItem = item(RawOutputItem, _),
        ( if RawOutputItem = output_item(OutputExpr0)
        then OutputExpr = OutputExpr0
        else unexpected($pred, "item is not output item")
        )
    ;
        MaybeOutputItem = no,
        % If the model lacks an output item then create an empty one.
        OutputExpr = expr(
            lit_simple_array([]),
            [],
            expr_info(unknown, ti_array(ti_par_int, ti_par_string))
        )
    ),
    OZNModel = generate_ozn_model(Env, MznItems, OutputExpr),
    do_write_ozn_model(File, OZNModel, !IO),
    (
        OutputDest = output_to_file(_),
        io.close_output(File, !IO)
    ;
        OutputDest = output_to_stdout
    ).

%-----------------------------------------------------------------------------%

:- type ozn_model
    --->    ozn_model(
                ozn_model_tests :: list(ozn_test_decl),
                ozn_model_pars  :: list(ozn_par_decl),
                ozn_model_vars  :: list(ozn_var_decl),
                ozn_model_expr  :: ozn_output_expr
            ).

:- type ozn_test_decl
    --->    ozn_test_decl(
                ozn_test_decl_name   :: zinc_name,
                ozn_test_decl_pn     :: int,
                ozn_test_decl_params :: ti_exprs_and_ids,
                ozn_test_decl_body   :: expr
            ).

:- type ozn_test_decls == list(ozn_test_decl).

:- type ozn_par_decl
    --->    ozn_par_decl(
                ozn_par_decl_type  :: ti_expr,
                ozn_par_decl_name  :: zinc_name,
                ozn_par_decl_value :: expr
            ).

:- type ozn_par_decls == list(ozn_par_decl).

:- type ozn_var_decl
    --->    ozn_var_decl(
                ozn_var_decl_type  :: ti_expr,
                ozn_var_decl_name  :: zinc_name
            ).

:- type ozn_var_decls == list(ozn_var_decl).

:- type ozn_output_expr == expr.

:- type scalar_param_value
    --->    scalar_param_bool(bool)
    ;       scalar_param_int(int)
    ;       scalar_param_float(float)
    ;       scalar_param_string(string).

:- type scalar_param_map == map(zinc_name, scalar_param_value).

%-----------------------------------------------------------------------------%

:- func generate_ozn_model(env, ast, expr) = ozn_model.

generate_ozn_model(Env, AST, OutputExpr0) = OZN :-
    map.init(ScalarParams0),
    list.foldl4(process_item_for_ozn(Env), AST, [], RevTestDecls,
        [], RevParDecls, [], RevVarDecls, ScalarParams0, ScalarParams),
    OutputExpr = subst_scalar_params_in_expr(ScalarParams, OutputExpr0),
    OZN0 = ozn_model(
        RevTestDecls,
        RevParDecls,
        RevVarDecls,
        OutputExpr
    ),
    OZN = eliminate_unused_ozn_items(OZN0).

:- pred process_item_for_ozn(env::in, item::in,
    ozn_test_decls::in, ozn_test_decls::out,
    ozn_par_decls::in, ozn_par_decls::out,
    ozn_var_decls::in, ozn_var_decls::out,
    scalar_param_map::in, scalar_param_map::out) is det.

process_item_for_ozn(Env, Item, !Tests, !Pars, !Vars, !ScalarMap) :-
    Item = item(RawItem, _SrcLocn),
    (
        ( RawItem = constraint_item(_)
        ; RawItem = annotation_item(_, _)
        )
        % Ignore these items -- they should not appear in ozn files.
    ;
        RawItem = var_decl_item(TIExpr, VarId, _Anns, MaybeValue),
        process_var_decl_for_ozn(Env, TIExpr, VarId, MaybeValue,
            !Pars, !Vars, !ScalarMap)
    ;
        RawItem = predfunc_item(RetType, ProcName, ProcN, Params,
            _Anns, MaybeBody),
        process_predfunc_decl_for_ozn(Env, RetType, ProcName, ProcN,
            Params, MaybeBody, !.ScalarMap, !Tests)
    ;
        ( RawItem = assign_item(_, _)
        ; RawItem = solve_item(_, _)
        ; RawItem = output_item(_)
        ),
        unexpected($pred, "invalid item type")
    ).

%-----------------------------------------------------------------------------%

:- pred process_var_decl_for_ozn(env::in, ti_expr::in,
    zinc_name::in, var_decl_assignment::in,
    ozn_par_decls::in, ozn_par_decls::out,
    ozn_var_decls::in, ozn_var_decls::out,
    scalar_param_map::in, scalar_param_map::out) is det.

process_var_decl_for_ozn(Env, !.TIExpr, Name, Assignment, !Pars, !Vars,
        !ScalarMap) :-
    !.TIExpr = ti_expr(RawTIExpr, ExprInfo),
    RawTIExpr = raw_ti_expr(RawTIVarPar, BaseTIExprTail),
    ( if bte_contains_ann(BaseTIExprTail) then
        true    % Ignore (arrays of) annotation variables.
    else
        % For arrays, we are interested in the inst of the elements.
        ( if
            BaseTIExprTail = bte_array_of(_IndexTIExprs, ElemTIExpr, IsList)
        then
            % Replace implicit array indexes since solns2out does not support
            % them.  We take the opportunity to replace non-implicit array
            % indexes with their flat form since this may allow us to eliminate
            % more parameter computation from the ozn file.
            %
            FlatIndexTIExprs = get_flat_index_ti_exprs(Env, Name),
            BaseTIExprTailPrime = bte_array_of(FlatIndexTIExprs, ElemTIExpr,
                IsList),
            RawTIExprPrime = raw_ti_expr(RawTIVarPar, BaseTIExprTailPrime),
            !:TIExpr = subst_scalar_params_in_ti_expr(!.ScalarMap,
                ti_expr(RawTIExprPrime, ExprInfo)),
            VarPar = ElemTIExpr ^ raw_ti_expr ^ var_par
        else
            VarPar = RawTIExpr ^ var_par,
            !:TIExpr = subst_scalar_params_in_ti_expr(!.ScalarMap, !.TIExpr)
        ),
        % We remove constrained flat type-insts from the output schema since
        % floating point wobble in the solution stream can somtimes cause
        % these constraints to "fail".  The user may have already accounted
        % for such wobble, via the use of show_float etc, but if we enforce
        % these constraints then the output item won't be processed.
        !:TIExpr = remove_constrained_float_ti_expr(!.TIExpr),
        (
            VarPar = var,
            OZNVar = ozn_var_decl(!.TIExpr, Name),
            !:Vars = [OZNVar | !.Vars]
        ;
            VarPar = par,
            (
                Assignment = no_assignment,
                unexpected($pred, "missing parameter assignment")
            ;
                ( Assignment = rhs_assignment(AssignExpr0)
                ; Assignment = separate_assignment(_, AssignExpr0)
                )
            ),
            ( if bte_is_scalar_param(BaseTIExprTail) then
                add_to_scalar_param_map(Env, Name, !ScalarMap) 
            else
                AssignExpr = subst_scalar_params_in_expr(!.ScalarMap,
                    AssignExpr0),
                OZNPar = ozn_par_decl(!.TIExpr, Name, AssignExpr),
                !:Pars = [OZNPar | !.Pars]
            )
        )
    ).

:- func remove_constrained_float_ti_expr(ti_expr) = ti_expr.

remove_constrained_float_ti_expr(!.TIExpr) = !:TIExpr :-
    !.TIExpr = ti_expr(RawTIExpr0, ExprInfo),
    RawTIExpr0 = raw_ti_expr(VarPar, BaseTIExprTail0),
    TI = ExprInfo ^ expr_type_inst,
    ( if
        ( TI = ti_par_float ; TI = ti_var_float)
    then
        RawTIExpr = raw_ti_expr(VarPar, bte_float)
    else if
        TI = ti_array(_IndexTI, ElemTI),
        ( ElemTI = ti_par_float ; ElemTI = ti_var_float),
        BaseTIExprTail0 = bte_array_of(IndexTIExprs, ElemTIExpr0, IsList),
        ElemTIExpr0 = ti_expr(RawElemTIExpr0, ElemExprInfo),
        RawElemTIExpr0 = raw_ti_expr(ElemVarPar, _)
    then
        RawElemTIExpr = raw_ti_expr(ElemVarPar, bte_float),
        ElemTIExpr = ti_expr(RawElemTIExpr, ElemExprInfo),
        BaseTIExprTail = bte_array_of(IndexTIExprs, ElemTIExpr, IsList),
        RawTIExpr = raw_ti_expr(VarPar, BaseTIExprTail)
    else
        RawTIExpr = RawTIExpr0
    ),
    !:TIExpr = ti_expr(RawTIExpr, ExprInfo).

:- pred bte_contains_ann(base_ti_expr_tail::in) is semidet.

bte_contains_ann(BaseTIExprTail) :-
    (
        BaseTIExprTail = bte_ann
    ;
        BaseTIExprTail = bte_array_of(_, ElemTIExpr, _),
        ElemTIExpr ^ raw_ti_expr ^ base_ti_expr_tail = bte_ann
    ).

:- pred bte_is_scalar_param(base_ti_expr_tail::in) is semidet.

bte_is_scalar_param(BaseTIExprTail) :-
    ( BaseTIExprTail = bte_bool
    ; BaseTIExprTail = bte_int
    ; BaseTIExprTail = bte_float
    ; BaseTIExprTail = bte_string
    ).

:- func get_flat_index_ti_exprs(env, zinc_name) = ti_exprs.

get_flat_index_ti_exprs(Env, VarName) = IndexTIExprs :-
    VarId = id_global(VarName),
    IndexRanges = Env ^ var_index_ranges(VarId),
    IndexTIExprs = list.map(index_range_to_ti_expr, IndexRanges).

:- func index_range_to_ti_expr(index_range)= ti_expr.

index_range_to_ti_expr(IndexRange) = TIExpr :-
    (
        IndexRange = index_range(LB, UB),
        DummyExprInfo = expr_info(unknown, ti_par_int),
        LBExpr = expr(lit(int(LB)), [], DummyExprInfo),
        UBExpr = expr(lit(int(UB)), [], DummyExprInfo),
        BaseTIExpr = bte_range_expr_as_type_expr(LBExpr, UBExpr),
        RawTIExpr = raw_ti_expr(par, BaseTIExpr),
        TIExpr = ti_expr(RawTIExpr, DummyExprInfo)
    ;
        IndexRange = index_implicit,
        unexpected($pred, "implicit index in flattened model")
    ).

:- pred add_to_scalar_param_map(env::in, zinc_name::in,
    scalar_param_map::in, scalar_param_map::out) is det.                

add_to_scalar_param_map(Env, Name, !ScalarMap) :-
    VarId = id_global(Name),
    ( if FlatValue = Env ^ var_value(VarId) then
        FlatValue = mzn_expr(RawExpr, _),
        ( if RawExpr = bool_expr(bool_const(Bool)) then
            Value = scalar_param_bool(Bool)
        else if RawExpr = int_expr(int_const(Int)) then
            Value = scalar_param_int(Int)
        else if RawExpr = string_expr(StringExpr) then
            String = format_string_expr_unquoted(StringExpr),
            Value = scalar_param_string(String)
        else if RawExpr = float_expr(float_const(Float)) then
            Value = scalar_param_float(Float)
        else
            unexpected($pred, "non-scalar or non-constant expr")
        ),
        map.det_insert(Name, Value, !ScalarMap)
    else
        unexpected($pred, "parameter with no flat")
    ).

:- func subst_scalar_params_in_expr(scalar_param_map, expr) = expr.

subst_scalar_params_in_expr(Map, !.Expr) = !:Expr :-
    !.Expr = expr(RawExpr0, Anns, ExprInfo),
    RawExpr = subst_scalar_params_in_raw_expr(Map, RawExpr0),
    % Ignore the annotations: we do not include them in the ozn file
    % anyway.
    !:Expr = expr(RawExpr, Anns, ExprInfo).

:- func subst_scalar_params_in_exprs(scalar_param_map, exprs) = exprs.

subst_scalar_params_in_exprs(Map, Exprs) =
    list.map(subst_scalar_params_in_expr(Map), Exprs).

:- func subst_scalar_params_in_raw_expr(scalar_param_map, raw_expr)
    = raw_expr.

subst_scalar_params_in_raw_expr(Map, !.RawExpr) = !:RawExpr :-
    (
        ( !.RawExpr = lit(_)
        ; !.RawExpr = lit_ann(_, _)
        ; !.RawExpr = anon_var
        )
    ;
        !.RawExpr = ident(Id),
        ( if
            Id = id_global(Name),
            map.search(Map, Name, Value)
        then
            (
                Value = scalar_param_bool(Bool),
                !:RawExpr = lit(bool(Bool))
            ;
                Value = scalar_param_int(Int),
                !:RawExpr = lit(int(Int))
            ;
                Value = scalar_param_string(String),
                !:RawExpr = lit(string(String))
            ; 
                Value = scalar_param_float(Float),
                !:RawExpr = lit(floatstr(float_to_string(Float)))
            )
        else
            true
        )
    ;
        !.RawExpr = app(Id, ProcN, Kind, Args0),
        Args = subst_scalar_params_in_exprs(Map, Args0),
        !:RawExpr = app(Id, ProcN, Kind, Args)
    ;
        !.RawExpr = array_access(ArrayExpr0, IndexExprs0),
        ArrayExpr = subst_scalar_params_in_expr(Map, ArrayExpr0),
        IndexExprs = subst_scalar_params_in_exprs(Map, IndexExprs0),
        !:RawExpr = array_access(ArrayExpr, IndexExprs)
    ;
        !.RawExpr = lit_set(ElemExprs0),
        ElemExprs = subst_scalar_params_in_exprs(Map, ElemExprs0),
        !:RawExpr = lit_set(ElemExprs)
    ;
        !.RawExpr = lit_simple_array(ElemExprs0),
        ElemExprs = subst_scalar_params_in_exprs(Map, ElemExprs0),
        !:RawExpr = lit_simple_array(ElemExprs)
    ;
        !.RawExpr = comprehension(Kind0, Gens0, MaybeWhere0),
        Kind = subst_scalar_params_in_comp_kind(Map, Kind0),
        Gens = subst_scalar_params_in_generators(Map, Gens0),
        MaybeWhere = map_maybe(subst_scalar_params_in_expr(Map), MaybeWhere0),
        !:RawExpr = comprehension(Kind, Gens, MaybeWhere)
    ; 
        !.RawExpr = if_then_else(IfExpr0, ThenExpr0, ElseExpr0),
        IfExpr = subst_scalar_params_in_expr(Map, IfExpr0),
        ThenExpr = subst_scalar_params_in_expr(Map, ThenExpr0),
        ElseExpr = subst_scalar_params_in_expr(Map, ElseExpr0),
        !:RawExpr = if_then_else(IfExpr, ThenExpr, ElseExpr)
    ;
        !.RawExpr = let(LocalVars0, LetExpr0),
        LocalVars = subst_scalar_params_in_local_vars(Map, LocalVars0),
        LetExpr = subst_scalar_params_in_expr(Map, LetExpr0),
        !:RawExpr = let(LocalVars, LetExpr)
    ;
        !.RawExpr = coerce(To, From, CoercedExpr0),
        CoercedExpr = subst_scalar_params_in_expr(Map, CoercedExpr0),
        !:RawExpr = coerce(To, From, CoercedExpr)
    ;
        !.RawExpr = lit_tuple(_),
        unexpected($pred, "not a MiniZinc expression")
    ).

:- func subst_scalar_params_in_comp_kind(scalar_param_map, comprehension_kind) = 
    comprehension_kind.

subst_scalar_params_in_comp_kind(Map, !.Kind) = !:Kind :-
    (
        !.Kind = set_comp(Expr0),
        Expr = subst_scalar_params_in_expr(Map, Expr0),
        !:Kind = set_comp(Expr)
    ;
        !.Kind = simple_array_comp(Expr0),
        Expr = subst_scalar_params_in_expr(Map, Expr0),
        !:Kind = simple_array_comp(Expr)
    ).

:- func subst_scalar_params_in_generators(scalar_param_map, generators) = 
    generators.

subst_scalar_params_in_generators(Map, Gens) = 
    list.map(subst_scalar_params_in_generator(Map), Gens).

:- func subst_scalar_params_in_generator(scalar_param_map, generator) = 
    generator.

subst_scalar_params_in_generator(Map, !.Gen) = !:Gen :-
    !.Gen = generator(Ids, Expr0),
    Expr = subst_scalar_params_in_expr(Map, Expr0),
    !:Gen = generator(Ids, Expr).

:- func subst_scalar_params_in_local_vars(scalar_param_map, local_vars) = 
    local_vars.

subst_scalar_params_in_local_vars(Map, LocalVars) = 
    list.map(subst_scalar_params_in_local_var(Map), LocalVars).       

:- func subst_scalar_params_in_local_var(scalar_param_map, local_var) = 
    local_var.

subst_scalar_params_in_local_var(Map, !.LocalVar) = !:LocalVar :-
    !.LocalVar = local_var(TIExpr0, Id, Exprs0, MaybeExpr0),
    TIExpr = subst_scalar_params_in_ti_expr(Map, TIExpr0),
    Exprs = subst_scalar_params_in_exprs(Map, Exprs0),
    MaybeExpr = map_maybe(subst_scalar_params_in_expr(Map), MaybeExpr0),
    !:LocalVar = local_var(TIExpr, Id, Exprs, MaybeExpr).

%-----------------------------------------------------------------------------%

:- func subst_scalar_params_in_ti_expr(scalar_param_map, ti_expr) = ti_expr.

subst_scalar_params_in_ti_expr(Map, !.TIExpr) = !:TIExpr :-
    !.TIExpr = ti_expr(RawTIExpr0, ExprInfo),
    RawTIExpr0 = raw_ti_expr(VarPar, BaseTIExprTail0),
    BaseTIExprTail = subst_scalar_params_in_bte(Map, BaseTIExprTail0),
    RawTIExpr = raw_ti_expr(VarPar, BaseTIExprTail),
    !:TIExpr = ti_expr(RawTIExpr, ExprInfo).

:- func subst_scalar_params_in_ti_exprs(scalar_param_map, ti_exprs) = ti_exprs.

subst_scalar_params_in_ti_exprs(Map, TIExprs) = 
    list.map(subst_scalar_params_in_ti_expr(Map), TIExprs).

:- func subst_scalar_params_in_bte(scalar_param_map, base_ti_expr_tail)
    = base_ti_expr_tail.

subst_scalar_params_in_bte(Map, !.BTE) = !:BTE :-
    (
        ( !.BTE = bte_int
        ; !.BTE = bte_ident(_)
        ; !.BTE = bte_bool
        ; !.BTE = bte_float
        ; !.BTE = bte_ann
        ; !.BTE = bte_bottom
        ; !.BTE = bte_string
        ) 
    ;
        !.BTE = bte_range_expr_as_type_expr(LBExpr0, UBExpr0),
        LBExpr = subst_scalar_params_in_expr(Map, LBExpr0),
        UBExpr = subst_scalar_params_in_expr(Map, UBExpr0),
        !:BTE = bte_range_expr_as_type_expr(LBExpr, UBExpr)
    ;
        !.BTE = bte_array_of(IndexTIExprs0, ElemTIExpr0, IsList),
        IndexTIExprs = subst_scalar_params_in_ti_exprs(Map, IndexTIExprs0),
        ElemTIExpr = subst_scalar_params_in_ti_expr(Map, ElemTIExpr0),
        !:BTE = bte_array_of(IndexTIExprs, ElemTIExpr, IsList)
    ;   
        !.BTE = bte_set_of(ElemTIExpr0),
        ElemTIExpr = subst_scalar_params_in_ti_expr(Map, ElemTIExpr0),
        !:BTE = bte_set_of(ElemTIExpr)
    ;
        !.BTE = bte_set_expr_as_type_expr(ElemExprs0),
        ElemExprs = subst_scalar_params_in_exprs(Map, ElemExprs0),
        !:BTE = bte_set_expr_as_type_expr(ElemExprs)
    ;
        ( !.BTE = bte_typeinst_var(_)
        ; !.BTE = bte_any_typeinst_var(_)
        ; !.BTE = bte_tuple_of(_)
        ; !.BTE = bte_error
        ),
        unexpected($pred, "not a MiniZinc base type-inst")
    ).

:- func subst_scalar_params_in_ti_exprs_and_ids(scalar_param_map,
    ti_exprs_and_ids) = ti_exprs_and_ids.

subst_scalar_params_in_ti_exprs_and_ids(Map, TIExprsAndIds) = 
    list.map(subst_scalar_params_in_ti_expr_and_id(Map), TIExprsAndIds).

:- func subst_scalar_params_in_ti_expr_and_id(scalar_param_map,
    ti_expr_and_id) = ti_expr_and_id.

subst_scalar_params_in_ti_expr_and_id(Map, !.TIExprAndId) = !:TIExprAndId :-
    !.TIExprAndId = TIExpr0 - Id,
    TIExpr = subst_scalar_params_in_ti_expr(Map, TIExpr0),
    !:TIExprAndId = TIExpr - Id.
    
%-----------------------------------------------------------------------------%

:- pred process_predfunc_decl_for_ozn(env::in, predfunc_ret::in,
    zinc_name::in, int::in, ti_exprs_and_ids::in, maybe(expr)::in,
    scalar_param_map::in, ozn_test_decls::in, ozn_test_decls::out) is det.

process_predfunc_decl_for_ozn(_Env, RetType, Name, ProcN, Params0, MaybeBody,
        ScalarMap, !Tests) :-
    (
        RetType = test_ret,
        (
            MaybeBody = no
        ;
            % Any test item that is used in an output expression *must* have
            % a body.
            MaybeBody = yes(Body0),
            Params = subst_scalar_params_in_ti_exprs_and_ids(ScalarMap,
                Params0),
            Body = subst_scalar_params_in_expr(ScalarMap, Body0),
            TestDecl = ozn_test_decl(Name, ProcN, Params, Body),
            !:Tests = [TestDecl | !.Tests]
        )
    ;
        ( RetType = pred_ret
        ; RetType = func_ret(_)
        )
        % Ignore these - they should not appear in ozn files.
    ).

%-----------------------------------------------------------------------------%
%
% Unused item elimination for ozn files.
%

:- type ozn_item_id
    --->    oii_var(zinc_name)
    ;       oii_test(zinc_name, int).

:- func eliminate_unused_ozn_items(ozn_model) = ozn_model.

eliminate_unused_ozn_items(!.OZN) = !:OZN :-
    OutputExpr = !.OZN ^ ozn_model_expr,
    ozn_item_ids_in_expr(OutputExpr, set.init, ItemsToExamine),
    set.init(UsedItems0),
    set.init(NextItems), 
    gather_items_in_use(!.OZN, ItemsToExamine, UsedItems0, UsedItems,
        NextItems),
    do_eliminate_unused_items(UsedItems, !OZN).

:- pred gather_items_in_use(ozn_model::in, set(ozn_item_id)::in,
    set(ozn_item_id)::in, set(ozn_item_id)::out,
    set(ozn_item_id)::in) is det.

gather_items_in_use(OZN, ItemsToExamine, !UsedItems, !.NextItems) :-
    ( if set.is_empty(ItemsToExamine) then
        true
    else
        OZN = ozn_model(TestDecls, ParDecls, VarDecls, _),
        set.union(ItemsToExamine, !UsedItems),
        list.foldl2(gather_test_in_use(ItemsToExamine), TestDecls, !UsedItems,
            !NextItems),
        list.foldl2(gather_par_in_use(ItemsToExamine), ParDecls, !UsedItems,
            !NextItems),
        list.foldl2(gather_var_in_use(ItemsToExamine), VarDecls, !UsedItems,
            !NextItems),
        gather_items_in_use(OZN, !.NextItems, !UsedItems, set.init)
    ).

:- pred gather_test_in_use(set(ozn_item_id)::in, ozn_test_decl::in,
    set(ozn_item_id)::in, set(ozn_item_id)::out,
    set(ozn_item_id)::in, set(ozn_item_id)::out) is det.

gather_test_in_use(ItemsToExamine, Test, !UsedItems, !NextItems) :-
    Test = ozn_test_decl(Name, ProcN, Params, Body),
    TestId = oii_test(Name, ProcN),
    ( if set.contains(ItemsToExamine, TestId) then
        some [!Uses] (
            set.init(!:Uses),
            list.foldl(ozn_item_ids_in_ti_expr_and_id, Params, !Uses),
            ozn_item_ids_in_expr(Body, !Uses),
            set.fold(update_next_items(!.UsedItems), !.Uses, !NextItems)
        )
    else
        true
    ).

:- pred gather_par_in_use(set(ozn_item_id)::in, ozn_par_decl::in,
    set(ozn_item_id)::in, set(ozn_item_id)::out,
    set(ozn_item_id)::in, set(ozn_item_id)::out) is det.

gather_par_in_use(ItemsToExamine, Par, !UsedItems, !NextItems) :-
    Par = ozn_par_decl(TIExpr, Name, ValueExpr),
    ParId = oii_var(Name),
    ( if set.contains(ItemsToExamine, ParId) then
        some [!Uses] (
            set.init(!:Uses),
            ozn_item_ids_in_ti_expr(TIExpr, !Uses),
            ozn_item_ids_in_expr(ValueExpr, !Uses),
            set.fold(update_next_items(!.UsedItems), !.Uses, !NextItems)
        )
    else
        true
    ).

:- pred gather_var_in_use(set(ozn_item_id)::in, ozn_var_decl::in,
    set(ozn_item_id)::in, set(ozn_item_id)::out,
    set(ozn_item_id)::in, set(ozn_item_id)::out) is det.

gather_var_in_use(ItemsToExamine, Var, !UsedItems, !NextItems) :-
    Var = ozn_var_decl(TIExpr, Name),
    ParId = oii_var(Name),
    ( if set.contains(ItemsToExamine, ParId) then
        some [!Uses] (
            set.init(!:Uses),
            ozn_item_ids_in_ti_expr(TIExpr, !Uses),
            set.fold(update_next_items(!.UsedItems), !.Uses, !NextItems)
        )
    else
        true
    ).

:- pred update_next_items(set(ozn_item_id)::in, ozn_item_id::in,
    set(ozn_item_id)::in, set(ozn_item_id)::out) is det.

update_next_items(UsedItems, Item, !NextItems) :-
    ( if set.contains(UsedItems, Item)
    then true
    else set.insert(Item, !NextItems)
    ).

:- pred do_eliminate_unused_items(set(ozn_item_id)::in,
    ozn_model::in, ozn_model::out) is det.

do_eliminate_unused_items(ItemsUsed, !OZN) :-
    !.OZN = ozn_model(Tests0, Pars0, Vars0, OutputExpr),
    list.filter(test_in_use(ItemsUsed), Tests0, Tests),
    list.filter(par_in_use(ItemsUsed), Pars0, Pars),
    list.filter(var_in_use(ItemsUsed), Vars0, Vars),
    !:OZN = ozn_model(Tests, Pars, Vars, OutputExpr).

:- pred test_in_use(set(ozn_item_id)::in, ozn_test_decl::in) is semidet.

test_in_use(ItemsUsed, Test) :-
    Test = ozn_test_decl(Name, ProcN, _, _),
    TestId = oii_test(Name, ProcN),
    set.member(TestId, ItemsUsed).

:- pred par_in_use(set(ozn_item_id)::in, ozn_par_decl::in) is semidet.

par_in_use(ItemsUsed, Par) :-
    Par = ozn_par_decl(_, Name, _),
    ParId = oii_var(Name),
    set.member(ParId, ItemsUsed).

:- pred var_in_use(set(ozn_item_id)::in, ozn_var_decl::in) is semidet.

var_in_use(ItemsUsed, Var) :-
    Var = ozn_var_decl(_, Name),
    VarId = oii_var(Name),
    set.member(VarId, ItemsUsed).

%-----------------------------------------------------------------------------%

:- pred ozn_item_ids_in_expr(expr::in,
    set(ozn_item_id)::in, set(ozn_item_id)::out) is det.

ozn_item_ids_in_expr(Expr, !Set) :-
    RawExpr = Expr ^ raw_expr,
    (
        RawExpr = ident(Id),
        ( if Id = id_global(VarName)
        then set.insert(oii_var(VarName), !Set)
        else true
        )
    ;
        ( RawExpr = lit(_)
        ; RawExpr = anon_var
        )
    ;
        RawExpr = app(Id, ProcN, _Kind, ArgExprs),
        ( 
            Id = id_global(AppName),
            set.insert(oii_test(AppName, ProcN), !Set)
        ;
            ( Id = id_unset(_)
            ; Id = id_scoped(_, _)
            ),
            unexpected($pred, "non-global proc id")
        ),
        list.foldl(ozn_item_ids_in_expr, ArgExprs, !Set)
    ;
        RawExpr = array_access(ArrayExpr, IndexExprs),
        ozn_item_ids_in_expr(ArrayExpr, !Set),
        list.foldl(ozn_item_ids_in_expr, IndexExprs, !Set)
    ;
        RawExpr = lit_set(ElemExprs),
        list.foldl(ozn_item_ids_in_expr, ElemExprs, !Set)
    ;
        RawExpr = lit_simple_array(ElemExprs),
        list.foldl(ozn_item_ids_in_expr, ElemExprs, !Set)
    ;
        RawExpr = comprehension(CompKind, Gens, MaybeWhereExpr),
        (
            ( CompKind = set_comp(HeadExpr)
            ; CompKind = simple_array_comp(HeadExpr)
            ),
            ozn_item_ids_in_expr(HeadExpr, !Set)
        ),
        list.foldl(ozn_item_ids_in_gen, Gens, !Set),
        fold_maybe(ozn_item_ids_in_expr, MaybeWhereExpr, !Set)
    ;
        RawExpr = if_then_else(IfExpr, ThenExpr, ElseExpr),
        ozn_item_ids_in_expr(IfExpr, !Set),
        ozn_item_ids_in_expr(ThenExpr, !Set),
        ozn_item_ids_in_expr(ElseExpr, !Set)
    ;
        RawExpr = let(LocalVars, LetExpr),
        list.foldl(ozn_item_ids_in_local_var, LocalVars, !Set), 
        ozn_item_ids_in_expr(LetExpr, !Set)
    ;
        RawExpr = coerce(_, _, CoercedExpr),
        ozn_item_ids_in_expr(CoercedExpr, !Set)
    ;
        ( RawExpr = lit_tuple(_)
        ; RawExpr = lit_ann(_, _)
        ),
        unexpected($pred, "not a MiniZinc expression")
    ).

:- pred ozn_item_ids_in_gen(generator::in,
    set(ozn_item_id)::in, set(ozn_item_id)::out) is det.

ozn_item_ids_in_gen(Generator, !Set) :-
    Generator = generator(_, Expr),
    ozn_item_ids_in_expr(Expr, !Set).

:- pred ozn_item_ids_in_local_var(local_var::in,
    set(ozn_item_id)::in, set(ozn_item_id)::out) is det.

ozn_item_ids_in_local_var(LocalVar, !Set) :-
    LocalVar = local_var(TIExpr, _, Exprs, MaybeExpr),
    ozn_item_ids_in_ti_expr(TIExpr, !Set),
    list.foldl(ozn_item_ids_in_expr, Exprs, !Set),
    fold_maybe(ozn_item_ids_in_expr, MaybeExpr, !Set).

:- pred ozn_item_ids_in_ti_expr(ti_expr::in,
    set(ozn_item_id)::in, set(ozn_item_id)::out) is det.

ozn_item_ids_in_ti_expr(TIExpr, !Set) :-
    RawTIExpr = TIExpr ^ raw_ti_expr,
    RawTIExpr = raw_ti_expr(_, BaseTIExprTail),
    (
        BaseTIExprTail = bte_range_expr_as_type_expr(LBExpr, UBExpr),
        ozn_item_ids_in_expr(LBExpr, !Set),
        ozn_item_ids_in_expr(UBExpr, !Set)
    ;
        BaseTIExprTail = bte_array_of(IndexTIExprs, ArrayTIExpr, _),
        list.foldl(ozn_item_ids_in_ti_expr, IndexTIExprs, !Set),
        ozn_item_ids_in_ti_expr(ArrayTIExpr, !Set)
    ;
        BaseTIExprTail = bte_ident(Id),
        ( if Id = id_global(Name)
        then set.insert(oii_var(Name), !Set)
        else true
        )
    ;
        BaseTIExprTail = bte_set_of(ElemTIExprs),
        ozn_item_ids_in_ti_expr(ElemTIExprs, !Set)
    ;
        BaseTIExprTail = bte_set_expr_as_type_expr(ElemExprs),
        list.foldl(ozn_item_ids_in_expr, ElemExprs, !Set)
    ;
        ( BaseTIExprTail = bte_int
        ; BaseTIExprTail = bte_bool
        ; BaseTIExprTail = bte_float
        ; BaseTIExprTail = bte_string
        ; BaseTIExprTail = bte_ann
        )
    ;
        ( BaseTIExprTail = bte_typeinst_var(_)
        ; BaseTIExprTail = bte_any_typeinst_var(_)
        ; BaseTIExprTail = bte_tuple_of(_)
        ; BaseTIExprTail = bte_bottom
        ; BaseTIExprTail = bte_error
        ),
        unexpected($pred, "non-MiniZinc expression")
    ).

:- pred ozn_item_ids_in_ti_expr_and_id(ti_expr_and_id::in,
    set(ozn_item_id)::in, set(ozn_item_id)::out) is det.

ozn_item_ids_in_ti_expr_and_id(TIExprAndId, !Uses) :-
    TIExprAndId = TIExpr - _Id,
    ozn_item_ids_in_ti_expr(TIExpr, !Uses). 

%-----------------------------------------------------------------------------%

:- pred do_write_ozn_model(io.text_output_stream::in,
    ozn_model::in, io::di, io::uo) is det.

do_write_ozn_model(File, Model, !IO) :-
    Model = ozn_model(Tests, Pars, Vars, OutputExpr),
    list.foldl(write_ozn_test_item(File), Tests, !IO),
    list.foldl(write_ozn_par_item(File), Pars, !IO),
    list.foldl(write_ozn_var_item(File), Vars, !IO),
    write_ozn_output_expr(File, OutputExpr, !IO).

:- pred write_ozn_test_item(io.text_output_stream::in,
    ozn_test_decl::in, io::di, io::uo) is det.

write_ozn_test_item(File, Test, !IO) :-
    Test = ozn_test_decl(Name, ProcN, Params, Body),
    RawItem = predfunc_item(test_ret, Name, ProcN, Params, [], yes(Body)),
    pprint_ozn_item(File, RawItem, !IO).

:- pred write_ozn_par_item(io.text_output_stream::in,
    ozn_par_decl::in, io::di, io::uo) is det.

write_ozn_par_item(File, Par, !IO) :-
    Par = ozn_par_decl(TIExpr, Name, Value),
    RawItem = var_decl_item(TIExpr, Name, [], rhs_assignment(Value)),
    pprint_ozn_item(File, RawItem, !IO).

:- pred write_ozn_var_item(io.text_output_stream::in,
    ozn_var_decl::in, io::di, io::uo) is det.

write_ozn_var_item(File, Par, !IO) :-
    Par = ozn_var_decl(TIExpr, Name),
    RawItem = var_decl_item(TIExpr, Name, [], no_assignment),
    pprint_ozn_item(File, RawItem, !IO).

:- pred write_ozn_output_expr(io.text_output_stream::in,
    ozn_output_expr::in, io::di, io::uo) is det.

write_ozn_output_expr(File, OutputExpr, !IO) :-
    RawItem = output_item(OutputExpr),
    pprint_ozn_item(File, RawItem, !IO).

:- pred pprint_ozn_item(io.text_output_stream::in, raw_item::in,
    io::di, io::uo) is det.

pprint_ozn_item(File, RawItem, !IO) :-
    PPLang = pp_lang_minizinc(dont_print_coercions),
    Doc = doc_raw_item(PPLang, RawItem) ++ semic,
    pprint.write(File, 76, Doc, !IO),
    io.nl(File, !IO).

%-----------------------------------------------------------------------------%

:- pred is_builtin_fzn_operation(zinc_name::in) is semidet.
   
is_builtin_fzn_operation("..").
 
    % Integer comparisons
is_builtin_fzn_operation("int_eq").
is_builtin_fzn_operation("int_ne").
is_builtin_fzn_operation("int_le").
is_builtin_fzn_operation("int_lt").

is_builtin_fzn_operation("int_eq_reif").
is_builtin_fzn_operation("int_ne_reif").
is_builtin_fzn_operation("int_le_reif").
is_builtin_fzn_operation("int_lt_reif").

    % Float comparisons
is_builtin_fzn_operation("float_eq").
is_builtin_fzn_operation("float_ne").
is_builtin_fzn_operation("float_le").
is_builtin_fzn_operation("float_lt").

is_builtin_fzn_operation("float_eq_reif").
is_builtin_fzn_operation("float_ne_reif").
is_builtin_fzn_operation("float_le_reif").
is_builtin_fzn_operation("float_lt_reif").

    % Boolean comparisons
is_builtin_fzn_operation("bool_eq").
is_builtin_fzn_operation("bool_le").
is_builtin_fzn_operation("bool_lt").

is_builtin_fzn_operation("bool_eq_reif").
is_builtin_fzn_operation("bool_le_reif").
is_builtin_fzn_operation("bool_lt_reif").

    % Pseudo-boolean linear equalities and inequalities
is_builtin_fzn_operation("bool_lin_eq").
is_builtin_fzn_operation("bool_lin_le").

    % set-of-int comparisons
is_builtin_fzn_operation("set_eq").
is_builtin_fzn_operation("set_ne").
is_builtin_fzn_operation("set_le").
is_builtin_fzn_operation("set_lt").

is_builtin_fzn_operation("set_eq_reif").
is_builtin_fzn_operation("set_ne_reif").
is_builtin_fzn_operation("set_le_reif").
is_builtin_fzn_operation("set_lt_reif").

    % Integer linear equalities and inequalities
is_builtin_fzn_operation("int_lin_ne").
is_builtin_fzn_operation("int_lin_eq").
is_builtin_fzn_operation("int_lin_le").

is_builtin_fzn_operation("int_lin_ne_reif").
is_builtin_fzn_operation("int_lin_eq_reif").
is_builtin_fzn_operation("int_lin_le_reif").

    % Floating-point linear equalities and inequalities
is_builtin_fzn_operation("float_lin_ne").
is_builtin_fzn_operation("float_lin_eq").
is_builtin_fzn_operation("float_lin_le").
is_builtin_fzn_operation("float_lin_lt").

is_builtin_fzn_operation("float_lin_ne_reif").
is_builtin_fzn_operation("float_lin_eq_reif").
is_builtin_fzn_operation("float_lin_le_reif").
is_builtin_fzn_operation("float_lin_lt_reif").

    % Integer arithmetic
is_builtin_fzn_operation("int_plus").
is_builtin_fzn_operation("int_times").
is_builtin_fzn_operation("int_mod").
is_builtin_fzn_operation("int_div").
is_builtin_fzn_operation("int_max").
is_builtin_fzn_operation("int_min").
is_builtin_fzn_operation("int_abs").

    % Floating-point arithmetic
is_builtin_fzn_operation("float_acos").
is_builtin_fzn_operation("float_asin").
is_builtin_fzn_operation("float_atan").
is_builtin_fzn_operation("float_cos").
is_builtin_fzn_operation("float_cosh").
is_builtin_fzn_operation("float_exp").
is_builtin_fzn_operation("float_ln").
is_builtin_fzn_operation("float_log10").
is_builtin_fzn_operation("float_log2").
is_builtin_fzn_operation("float_sqrt").
is_builtin_fzn_operation("float_sin").
is_builtin_fzn_operation("float_sinh").
is_builtin_fzn_operation("float_tan").
is_builtin_fzn_operation("float_tanh").
is_builtin_fzn_operation("float_plus").
is_builtin_fzn_operation("float_times").
is_builtin_fzn_operation("float_div").
is_builtin_fzn_operation("float_max").
is_builtin_fzn_operation("float_min").
is_builtin_fzn_operation("float_abs").

    % Logical constraints
is_builtin_fzn_operation("bool_or").
is_builtin_fzn_operation("bool_and").
is_builtin_fzn_operation("bool_xor").
is_builtin_fzn_operation("bool_not").
is_builtin_fzn_operation("array_bool_and").
is_builtin_fzn_operation("array_bool_or").
is_builtin_fzn_operation("array_bool_xor").
is_builtin_fzn_operation("bool_clause").

    % Set constraints
is_builtin_fzn_operation("set_union").
is_builtin_fzn_operation("set_intersect").
is_builtin_fzn_operation("set_diff").
is_builtin_fzn_operation("set_symdiff").
is_builtin_fzn_operation("set_subset").
is_builtin_fzn_operation("set_card").
is_builtin_fzn_operation("set_in").
is_builtin_fzn_operation("set_subset_reif").
is_builtin_fzn_operation("set_in_reif").

    % Element
is_builtin_fzn_operation("array_bool_element").
is_builtin_fzn_operation("array_var_bool_element").
is_builtin_fzn_operation("array_int_element").
is_builtin_fzn_operation("array_var_int_element").
is_builtin_fzn_operation("array_float_element").
is_builtin_fzn_operation("array_var_float_element").
is_builtin_fzn_operation("array_set_element").
is_builtin_fzn_operation("array_var_set_element").

    % Coercions
is_builtin_fzn_operation("int2float").
is_builtin_fzn_operation("bool2int").

%-----------------------------------------------------------------------------%
:- end_module flatten.output.
%-----------------------------------------------------------------------------%
