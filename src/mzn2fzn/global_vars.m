%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Authors:
% Ralph Becket <rafe@csse.unimelb.edu.au>
% Zoltan Somogyi <zs@csse.unimelb.edu.au>
%
% Operations on global variables.
%
%-----------------------------------------------------------------------------%

:- module global_vars.
:- interface.

:- import_module errors.
:- import_module types.

:- import_module bool.
:- import_module list.

%-----------------------------------------------------------------------------%

    % This type contains a context and the information in an mzn_constraint.
:- type mzn_constraint_to_add
    --->    mzn_constraint_to_add(
                mcta_context    ::  error_context,
                mcta_predname   ::  string,
                mcta_args       ::  list(mzn_expr),
                mcta_anns       ::  mzn_anns
            ).

:- func mcta_to_mzn_constraint(mzn_constraint_to_add) = mzn_constraint.

    % Initialise local and global variables.
    % N.B.: a "tmp" var is an intermediate variable introduced by flattening.
    %
:- pred add_global_par(var_id::in, mzn_type::in, index_ranges::in,
    global_var_map::in, global_var_map::out) is det.
:- pred add_global_permanent_var(var_id::in, mzn_type::in, index_ranges::in,
    mzn_anns::in, list(mzn_constraint_to_add)::out,
    global_var_map::in, global_var_map::out) is det.
:- pred add_global_tmp_var(var_id::in, mzn_type::in, index_ranges::in,
    mzn_anns::in, list(mzn_constraint_to_add)::out,
    global_var_map::in, global_var_map::out) is det.

%-----------------------------------------------------------------------------%

    % Array variable index ranges.
    %
:- func get_var_index_ranges(global_var_map, var_id) = index_ranges.
:- pred set_var_index_ranges(var_id::in, index_ranges::in,
    global_var_map::in, global_var_map::out) is det.

%-----------------------------------------------------------------------------%

    % Operations to look up and return variable bounds.

:- func bounds_get_float_lb(var_bounds) = float.
:- func get_float_lb(global_var_map, var_id) = float.
:- pred set_float_lb(var_id::in, float::in,
    global_var_map::in, global_var_map::out) is det.

:- func bounds_get_float_ub(var_bounds) = float.
:- func get_float_ub(global_var_map, var_id) = float.
:- pred set_float_ub(var_id::in, float::in,
    global_var_map::in, global_var_map::out) is det.

:- pred bounds_get_float_lb_ub(var_bounds::in, float::out, float::out) is det.
:- pred get_float_lb_ub(global_var_map::in, var_id::in,
    float::out, float::out) is det.
:- pred set_float_lb_ub(var_id::in, float::in, float::in,
    global_var_map::in, global_var_map::out) is det.

:- func bounds_get_int_lb(var_bounds) = int.
:- func get_int_lb(global_var_map, var_id) = int.
:- pred set_int_lb(var_id::in, int::in,
    global_var_map::in, global_var_map::out) is det.

:- func bounds_get_int_ub(var_bounds) = int.
:- func get_int_ub(global_var_map, var_id) = int.
:- pred set_int_ub(var_id::in, int::in,
    global_var_map::in, global_var_map::out) is det.

:- pred bounds_get_int_lb_ub(var_bounds::in, int::out, int::out) is det.
:- pred get_int_lb_ub(global_var_map::in, var_id::in,
    int::out, int::out) is det.
:- pred set_int_lb_ub(var_id::in, int::in, int::in,
    global_var_map::in, global_var_map::out) is det.

:- func bounds_get_int_set_bounds(var_bounds, mzn_type) = int_range.
:- func get_int_set_bounds(global_var_map, var_id) = int_range.
:- pred set_int_set_bounds(var_id::in, int_range::in,
    global_var_map::in, global_var_map::out) is det.

:- func var_int_set_bounds_is_contiguous(global_var_map, var_id) = bool.

%-----------------------------------------------------------------------------%

:- func var_get_updated_var_type(var_info) = mzn_type.
:- func get_updated_var_type(global_var_map, var_id) = mzn_type.

%-----------------------------------------------------------------------------%

    % Variable annotations.
    %
:- func get_var_anns(global_var_map, var_id) = mzn_anns.
:- pred set_var_anns(var_id::in, mzn_anns::in,
    global_var_map::in, global_var_map::out) is det.

%-----------------------------------------------------------------------------%

    % Marks the given variable as an output, provided it is a global var,
    % and not local or a parameter.
    %
:- pred mark_var_for_output(var_id::in,
    global_var_map::in, global_var_map::out) is det.

:- pred get_var_output_anns(var_info::in, mzn_anns::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module intset.
:- import_module zinc_common.

:- import_module array.
:- import_module float.
:- import_module int.
:- import_module map.
:- import_module maybe.
:- import_module require.
:- import_module set.
:- import_module string.

%-----------------------------------------------------------------------------%

mcta_to_mzn_constraint(mzn_constraint_to_add(_, Name, Args, Anns)) =
    mzn_constraint(Name, Args, Anns).

%-----------------------------------------------------------------------------%

add_global_par(VarId, MZType, IndexRanges, !GlobalVarMap) :-
    VarInfo = var_info(MZType, IndexRanges, no,
        var_is_permanent, var_is_par, var_is_not_output, no_bounds, set.init),
    map.det_insert(VarId, VarInfo, !GlobalVarMap).

%-----------------------------------------------------------------------------%

add_global_permanent_var(VarId, MZType, IndexRanges, Anns,
        ConstraintsToAdd, !GlobalVarMap) :-
    add_global_var(VarId, MZType, IndexRanges, var_is_permanent, Anns,
        ConstraintsToAdd, !GlobalVarMap).

add_global_tmp_var(VarId, MZType, IndexRanges, Anns,
        ConstraintsToAdd, !GlobalVarMap) :-
    add_global_var(VarId, MZType, IndexRanges, var_is_temporary, Anns,
        ConstraintsToAdd, !GlobalVarMap).

:- pred add_global_var(var_id::in, mzn_type::in, index_ranges::in,
    var_kind::in, mzn_anns::in, list(mzn_constraint_to_add)::out,
    global_var_map::in, global_var_map::out) is det.

add_global_var(VarId, MZType, IndexRanges, Kind, Anns, ConstraintsToAdd,
        !GlobalVarMap) :-
    maybe_get_bounds_from_type(MZType, MaybeVarBounds),
    (
        MaybeVarBounds = yes(VarBounds)
    ;
        MaybeVarBounds = no,
        VarBounds = no_bounds
    ),
    VarInfo = var_info(MZType, IndexRanges, no,
        Kind, var_is_var, var_is_not_output, VarBounds, Anns),
    map.det_insert(VarId, VarInfo, !GlobalVarMap),

    % Handle any discontiguous set constraints.
    ( if
        MZType = mzn_int(int_range_set(Set)),
        not is_contiguous(Set, _, _)
    then
        ConstraintName = "set_in",
        MZA = int_to_mzn_expr(int_var(var_no_index(VarId))),
        Context = [],
        PAnns = no_anns,
        % JJJ FIXME - SET REP.
        MZB = int_set_to_mzn_expr(
            set_items(set.from_sorted_list(intset.to_sorted_list(Set)))),
        ConstraintsToAdd =
            [mzn_constraint_to_add(Context, ConstraintName, [MZA, MZB], PAnns)]
    else if
        MZType = mzn_int_array(int_range_set(Set)),
        not is_contiguous(Set, _, _)
    then
        ConstraintName = "set_in",
        Context = [],
        PAnns = no_anns,
        % JJJ FIXME - SET REP.
        MZB = int_set_to_mzn_expr(
            set_items(set.from_sorted_list(intset.to_sorted_list(Set)))),
        P = ( pred(I::in, CTA::out) is det :-
            MZA = int_to_mzn_expr(int_var(var_index(VarId, I))),
            CTA = mzn_constraint_to_add(Context, ConstraintName, [MZA, MZB],
                PAnns)
        ),
        N = index_ranges_to_size(IndexRanges),
        list.map(P, 1 .. N, ConstraintsToAdd)
    else
        ConstraintsToAdd = []
    ).

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

get_var_index_ranges(GlobalVarMap, VarId) = IndexRanges :-
    map.lookup(GlobalVarMap, VarId, VarInfo),
    IndexRanges = VarInfo ^ vi_index_ranges.

set_var_index_ranges(VarId, IndexRanges, !GlobalVarMap) :-
    map.lookup(!.GlobalVarMap, VarId, VarInfo0),
    VarInfo = VarInfo0 ^ vi_index_ranges := IndexRanges,
    map.det_update(VarId, VarInfo, !GlobalVarMap).

%-----------------------------------------------------------------------------%

get_float_lb(GlobalVarMap, VarId) = LB :-
    map.lookup(GlobalVarMap, VarId, VarInfo),
    VarBounds = VarInfo ^ vi_bounds,
    LB = bounds_get_float_lb(VarBounds).

get_float_ub(GlobalVarMap, VarId) = UB :-
    map.lookup(GlobalVarMap, VarId, VarInfo),
    VarBounds = VarInfo ^ vi_bounds,
    UB = bounds_get_float_ub(VarBounds).

get_float_lb_ub(GlobalVarMap, VarId, LB, UB) :-
    map.lookup(GlobalVarMap, VarId, VarInfo),
    VarBounds = VarInfo ^ vi_bounds,
    bounds_get_float_lb_ub(VarBounds, LB, UB).

get_int_lb(GlobalVarMap, VarId) = LB :-
    map.lookup(GlobalVarMap, VarId, VarInfo),
    VarBounds = VarInfo ^ vi_bounds,
    LB = bounds_get_int_lb(VarBounds).

get_int_ub(GlobalVarMap, VarId) = UB :-
    map.lookup(GlobalVarMap, VarId, VarInfo),
    VarBounds = VarInfo ^ vi_bounds,
    UB = bounds_get_int_ub(VarBounds).

get_int_lb_ub(GlobalVarMap, VarId, LB, UB) :-
    map.lookup(GlobalVarMap, VarId, VarInfo),
    VarBounds = VarInfo ^ vi_bounds,
    bounds_get_int_lb_ub(VarBounds, LB, UB).

get_int_set_bounds(GlobalVarMap, VarId) = Range :-
    map.lookup(GlobalVarMap, VarId, VarInfo),
    VarBounds = VarInfo ^ vi_bounds,
    VarType = VarInfo ^ vi_type,
    Range = bounds_get_int_set_bounds(VarBounds, VarType).

%-----------------------------------------------------------------------------%

bounds_get_float_lb(VarBounds) = LB :-
    (
        VarBounds = no_bounds,
        LB = float_minus_infinity
    ;
        VarBounds = float_bounds(LB, _)
    ;
        ( VarBounds = int_bounds(_, _)
        ; VarBounds = int_set_bounds(_)
        ),
        minizinc_internal_error([] : error_context, $pred,
            "Looking up float bounds of var with int bounds")
    ).

bounds_get_float_ub(VarBounds) = UB :-
    (
        VarBounds = no_bounds,
        UB = float_plus_infinity
    ;
        VarBounds = float_bounds(_, UB)
    ;
        ( VarBounds = int_bounds(_, _)
        ; VarBounds = int_set_bounds(_)
        ),
        minizinc_internal_error([] : error_context, $pred,
            "Looking up float bounds of var with int bounds")
    ).

bounds_get_float_lb_ub(VarBounds, LB, UB) :-
    (
        VarBounds = no_bounds,
        LB = float_minus_infinity,
        UB = float_plus_infinity
    ;
        VarBounds = float_bounds(LB, UB)
    ;
        ( VarBounds = int_bounds(_, _)
        ; VarBounds = int_set_bounds(_)
        ),
        minizinc_internal_error([] : error_context, $pred,
            "Looking up float bounds of var with int bounds")
    ).

bounds_get_int_lb(VarBounds) = LB :-
    (
        VarBounds = no_bounds,
        LB = int_minus_infinity
    ;
        VarBounds = float_bounds(_, _),
        minizinc_internal_error([] : error_context, $pred,
            "Looking up int bounds of var with float bounds")
    ;
        VarBounds = int_bounds(LB, _)
    ;
        VarBounds = int_set_bounds(IntSet),
        ( if least(IntSet, Least) then
            LB = Least
        else
            minizinc_internal_error([] : error_context, $pred,
                "var_int_lb lookup on empty int_set_bounds")
        )
    ).

bounds_get_int_ub(VarBounds) = UB :-
    (
        VarBounds = no_bounds,
        UB = int_plus_infinity
    ;
        VarBounds = float_bounds(_, _),
        minizinc_internal_error([] : error_context, $pred,
            "Looking up int bounds of var with float bounds")
    ;
        VarBounds = int_bounds(_, UB)
    ;
        VarBounds = int_set_bounds(IntSet),
        ( if greatest(IntSet, Greatest) then
            UB = Greatest
        else
            minizinc_internal_error([] : error_context, $pred,
                "var_int_ub lookup on empty int_set_bounds")
        )
    ).

bounds_get_int_lb_ub(VarBounds, LB, UB) :-
    (
        VarBounds = no_bounds,
        LB = int_minus_infinity,
        UB = int_plus_infinity
    ;
        VarBounds = float_bounds(_, _),
        minizinc_internal_error([] : error_context, $pred,
            "Looking up int bounds of var with float bounds")
    ;
        VarBounds = int_bounds(LB, UB)
    ;
        VarBounds = int_set_bounds(IntSet),
        ( if
            least(IntSet, Least),
            greatest(IntSet, Greatest)
        then
            LB = Least,
            UB = Greatest
        else
            minizinc_internal_error([] : error_context, $pred,
                "var_int_lb_ub lookup on empty int_set_bounds")
        )
    ).

bounds_get_int_set_bounds(VarBounds, VarType) = Range :-
    % XXX Should be a switch.
    ( if
        VarBounds = int_set_bounds(IntSet)
    then
        Range = int_range_set(IntSet)
    else if
        VarBounds = int_bounds(Min, Max),
        Min \= int_minus_infinity,
        Max \= int_plus_infinity
    then
        Range = int_range_lb_ub(Min, Max)
    else if
        VarType = mzn_int_set(Range0),
        Range0 \= int_range_unbounded
    then
        Range = Range0
    else if
        VarType = mzn_int_set_array(Range0)
    then
        Range = Range0
    else
        trace [compiletime(flag("check_var_rep"))] (
            ( if VarBounds = float_bounds(_, _) then
                minizinc_internal_error([] : error_context, $pred,
                    "get_int_set_bounds lookup on float_bounds\n")
            else
                true
            )
        ),
        Range = int_range_unbounded
    ).

%-----------------------------------------------------------------------------%

set_float_lb(VarId, LB, !GlobalVarMap) :-
    map.lookup(!.GlobalVarMap, VarId, VarInfo0),
    VarBounds0 = VarInfo0 ^ vi_bounds,
    (
        VarBounds0 = no_bounds,
        VarBounds = float_bounds(LB, float_plus_infinity)
    ;
        VarBounds0 = float_bounds(OldLB, UB),
        trace [compiletime(flag("check_bounds_tightening"))] (
            ( if LB >= OldLB then
                true
            else
                minizinc_internal_error([] : error_context, $pred,
                    "new float LB is not greater than old float LB")
            )
        ),
        VarBounds = float_bounds(LB, UB)
    ;
        ( VarBounds0 = int_bounds(_, _)
        ; VarBounds0 = int_set_bounds(_)
        ),
        minizinc_internal_error([] : error_context, $pred,
            "Setting up new float bounds of var with old int bounds " ++
            var_name(VarId) ++ "\n")
    ),
    VarInfo = VarInfo0 ^ vi_bounds := VarBounds,
    map.det_update(VarId, VarInfo, !GlobalVarMap).

set_float_ub(VarId, UB, !GlobalVarMap) :-
    map.lookup(!.GlobalVarMap, VarId, VarInfo0),
    VarBounds0 = VarInfo0 ^ vi_bounds,
    (
        VarBounds0 = no_bounds,
        VarBounds = float_bounds(float_minus_infinity, UB)
    ;
        VarBounds0 = float_bounds(LB, OldUB),
        trace [compiletime(flag("check_bounds_tightening"))] (
            ( if UB =< OldUB then
                true
            else
                minizinc_internal_error([] : error_context, $pred,
                    "new float UB is not smaller than old float UB")
            )
        ),
        VarBounds = float_bounds(LB, UB)
    ;
        ( VarBounds0 = int_bounds(_, _)
        ; VarBounds0 = int_set_bounds(_)
        ),
        minizinc_internal_error([] : error_context, $pred,
            "Setting up new float bounds of var with old int bounds " ++
            var_name(VarId) ++ "\n")
    ),
    VarInfo = VarInfo0 ^ vi_bounds := VarBounds,
    map.det_update(VarId, VarInfo, !GlobalVarMap).

set_float_lb_ub(VarId, LB, UB, !GlobalVarMap) :-
    map.lookup(!.GlobalVarMap, VarId, VarInfo0),
    VarBounds0 = VarInfo0 ^ vi_bounds,
    (
        VarBounds0 = no_bounds,
        VarBounds = float_bounds(float_minus_infinity, UB)
    ;
        VarBounds0 = float_bounds(OldLB, OldUB),
        trace [compiletime(flag("check_bounds_tightening"))] (
            ( if LB >= OldLB then
                true
            else
                minizinc_internal_error([] : error_context, $pred,
                    "new float LB is not greater than old float LB")
            ),
            ( if UB < OldUB then
                true
            else
                minizinc_internal_error([] : error_context, $pred,
                    "new float UB is not smaller than old float UB")
            )
        ),
        VarBounds = float_bounds(LB, UB)
    ;
        ( VarBounds0 = int_bounds(_, _)
        ; VarBounds0 = int_set_bounds(_)
        ),
        minizinc_internal_error([] : error_context, $pred,
            "Setting up new float bounds of var with old int bounds " ++
            var_name(VarId) ++ "\n")
    ),
    VarInfo = VarInfo0 ^ vi_bounds := VarBounds,
    map.det_update(VarId, VarInfo, !GlobalVarMap).

set_int_lb(VarId, LB, !GlobalVarMap) :-
    map.lookup(!.GlobalVarMap, VarId, VarInfo0),
    VarBounds0 = VarInfo0 ^ vi_bounds,
    (
        VarBounds0 = no_bounds,
        VarBounds = int_bounds(LB, int_plus_infinity)
    ;
        VarBounds0 = float_bounds(_, _),
        minizinc_internal_error([] : error_context, $pred,
            "Setting up new int bounds of var with old float bounds " ++
            var_name(VarId) ++ "\n")
    ;
        VarBounds0 = int_bounds(OldLB, UB),
        trace [compiletime(flag("check_bounds_tightening"))] (
            ( if LB >= OldLB then
                true
            else
                minizinc_internal_error([] : error_context, $pred,
                    "new int LB is not greater than old int LB")
            )
        ),
        VarBounds = int_bounds(LB, UB)
    ;
        VarBounds0 = int_set_bounds(IntBounds0),
        IntBounds = restrict_min(LB, IntBounds0),
        ( is_contiguous(IntBounds, Min, Max) ->
            VarBounds = int_bounds(Min, Max)
        ;
            VarBounds = int_set_bounds(IntBounds)
        )
    ),
    VarInfo = VarInfo0 ^ vi_bounds := VarBounds,
    map.det_update(VarId, VarInfo, !GlobalVarMap).

set_int_ub(VarId, UB, !GlobalVarMap) :-
    map.lookup(!.GlobalVarMap, VarId, VarInfo0),
    VarBounds0 = VarInfo0 ^ vi_bounds,
    (
        VarBounds0 = no_bounds,
        VarBounds = int_bounds(int_minus_infinity, UB)
    ;
        VarBounds0 = float_bounds(_, _),
        minizinc_internal_error([] : error_context, $pred,
            "Setting up new int bounds of var with old float bounds " ++
            var_name(VarId) ++ "\n")
    ;
        VarBounds0 = int_bounds(LB, OldUB),
        trace [compiletime(flag("check_bounds_tightening"))] (
            ( if UB =< OldUB then
                true
            else
                minizinc_internal_error([] : error_context, $pred,
                    "new int UB is not smaller than old int UB")
            )
        ),
        VarBounds = int_bounds(LB, UB)
    ;
        VarBounds0 = int_set_bounds(IntBounds0),
        IntBounds = restrict_max(UB, IntBounds0),
        ( is_contiguous(IntBounds, Min, Max) ->
            VarBounds = int_bounds(Min, Max)
        ;
            VarBounds = int_set_bounds(IntBounds)
        )
    ),
    VarInfo = VarInfo0 ^ vi_bounds := VarBounds,
    map.det_update(VarId, VarInfo, !GlobalVarMap).

set_int_lb_ub(VarId, LB, UB, !GlobalVarMap) :-
    map.lookup(!.GlobalVarMap, VarId, VarInfo0),
    VarBounds0 = VarInfo0 ^ vi_bounds,
    (
        VarBounds0 = no_bounds,
        VarBounds = int_bounds(int_minus_infinity, UB)
    ;
        VarBounds0 = float_bounds(_, _),
        minizinc_internal_error([] : error_context, $pred,
            "Setting up new int bounds of var with old float bounds " ++
            var_name(VarId) ++ "\n")
    ;
        VarBounds0 = int_bounds(OldLB, OldUB),
        trace [compiletime(flag("check_bounds_tightening"))] (
            ( if LB >= OldLB then
                true
            else
                minizinc_internal_error([] : error_context, $pred,
                    "new int LB is not greater than old int LB")
            ),
            ( if UB =< OldUB then
                true
            else
                minizinc_internal_error([] : error_context, $pred,
                    "new int UB is not smaller than old int UB")
            )
        ),
        VarBounds = int_bounds(LB, UB)
    ;
        VarBounds0 = int_set_bounds(IntBounds0),
        IntBounds1 = restrict_min(LB, IntBounds0),
        IntBounds =  restrict_max(UB, IntBounds1),
        ( is_contiguous(IntBounds, Min, Max) ->
            VarBounds = int_bounds(Min, Max)
        ;
            VarBounds = int_set_bounds(IntBounds)
        )
    ),
    VarInfo = VarInfo0 ^ vi_bounds := VarBounds,
    map.det_update(VarId, VarInfo, !GlobalVarMap).

set_int_set_bounds(VarId, Range, !GlobalVarMap) :-
    % If the set is contiguous, only store it as a range.
    (
        Range = int_range_unbounded
    ;
        Range = int_range_lb_ub(LB, UB),
        map.lookup(!.GlobalVarMap, VarId, VarInfo0),
        VarBounds0 = VarInfo0 ^ vi_bounds,
        (
            VarBounds0 = no_bounds,
            VarBounds = int_bounds(LB, UB)
        ;
            VarBounds0 = float_bounds(_, _),
            minizinc_internal_error([] : error_context, $pred,
                "Setting up new int bounds of var with old float bounds " ++
                var_name(VarId) ++ "\n")
        ;
            VarBounds0 = int_bounds(OldLB, OldUB),
            trace [compiletime(flag("check_bounds_tightening"))] (
                ( if LB >= OldLB then
                    true
                else
                    minizinc_internal_error([] : error_context, $pred,
                        "new int LB is not greater than old int LB")
                ),
                ( if UB =< OldUB then
                    true
                else
                    minizinc_internal_error([] : error_context, $pred,
                        "new int UB is not smaller than old int UB")
                )
            ),
            VarBounds = int_bounds(LB, UB)
        ;
            VarBounds0 = int_set_bounds(IntBounds0),
            IntBounds1 = restrict_min(LB, IntBounds0),
            IntBounds = restrict_max(UB, IntBounds1),
            ( is_contiguous(IntBounds, Min, Max) ->
                VarBounds = int_bounds(Min, Max)
            ;
                VarBounds = int_set_bounds(IntBounds)
            )
        ),
        VarInfo1 = VarInfo0 ^ vi_bounds := VarBounds,

        Type1 = VarInfo1 ^ vi_type,
        ( if Type1 = mzn_int_set_array(_) then
            Type = mzn_int_set_array(Range),
            VarInfo = VarInfo1 ^ vi_type := Type
        else if Type1 = mzn_int_set(_) then
            Type = mzn_int_set(Range),
            VarInfo = VarInfo1 ^ vi_type := Type
        else
            minizinc_internal_error([] : error_context, $pred,
                "var_set_ub is trying to variable's type")
        ),
        map.det_update(VarId, VarInfo, !GlobalVarMap)
    ;
        Range = int_range_set(Set),
        map.lookup(!.GlobalVarMap, VarId, VarInfo0),
        VarBounds0 = VarInfo0 ^ vi_bounds,

        Xs = intset.to_sorted_list(Set),
        % JJJ FIXME - SET REP - simplify the switch below.
        (
            Xs = [],
            LB = 1,
            UB = 0
        ;
            Xs = [LB | _],
            UB = list.det_last(Xs)
        ),
        ( if
            list.length(Xs) = 1 + UB - LB
          then
            (
                VarBounds0 = no_bounds,
                VarBounds = int_bounds(LB, UB)
            ;
                VarBounds0 = float_bounds(_, _),
                minizinc_internal_error([] : error_context, $pred,
                    "Setting up new int bounds of var with old float bounds " ++
                    var_name(VarId) ++ "\n")
            ;
                VarBounds0 = int_bounds(OldLB, OldUB),
                trace [compiletime(flag("check_bounds_tightening"))] (
                    ( if LB < OldLB, LB =< UB then
                        minizinc_internal_error([] : error_context, $pred,
                            "new int LB is less than than old int LB")
                    else
                        true
                    ),
                    ( if UB > OldUB, LB =< UB then
                        minizinc_internal_error([] : error_context, $pred,
                            "new int UB is greater than old int UB")
                    else
                        true
                    )
                ),
                VarBounds = int_bounds(LB, UB)
            ;
                VarBounds0 = int_set_bounds(IntBounds0),
                IntBounds1 = restrict_min(LB, IntBounds0),
                IntBounds = restrict_max(UB, IntBounds1),
                ( is_contiguous(IntBounds, Min, Max) ->
                    VarBounds = int_bounds(Min, Max)
                ;
                    VarBounds = int_set_bounds(IntBounds)
                )
            )
          else
            (
                VarBounds0 = no_bounds,
                VarBounds = int_set_bounds(Set)
            ;
                VarBounds0 = float_bounds(_, _),
                minizinc_internal_error([] : error_context, $pred,
                    "Setting up new int bounds of var with old float bounds " ++
                    var_name(VarId) ++ "\n")
            ;
                VarBounds0 = int_bounds(OldLB, OldUB),
                trace [compiletime(flag("check_bounds_tightening"))] (
                    ( if least(Set, Min), Min < OldLB then
                        minizinc_internal_error([] : error_context, $pred,
                            "new int LB is not greater than old int LB")
                    else
                        true
                    ),
                    ( if greatest(Set, Max), Max > OldUB then
                        minizinc_internal_error([] : error_context, $pred,
                            "new int UB is not smaller than old int UB")
                    else
                        true
                    )
                ),
                VarBounds = int_bounds(LB, UB)
            ;
                VarBounds0 = int_set_bounds(OldSet),
                trace [compiletime(flag("check_bounds_tightening"))] (
                    ( if subset(Set, OldSet) then
                        true
                    else
                        minizinc_internal_error([] : error_context, $pred,
                            "new int set is not subset of old int set")
                    ),
                    ( if is_contiguous(Set, _, _) then
                        minizinc_internal_error([] : error_context, $pred,
                            "contiguity test failed in var_set_ub")
                    else
                        true
                    )
                ),
                VarBounds = int_set_bounds(Set)
            )
        ),
        VarInfo1 = VarInfo0 ^ vi_bounds := VarBounds,

        Type1 = VarInfo1 ^ vi_type,
        ( if Type1 = mzn_int_set_array(_) then
            Type = mzn_int_set_array(Range),
            VarInfo = VarInfo1 ^ vi_type := Type
        else if Type1 = mzn_int_set(_) then
            Type = mzn_int_set(Range),
            VarInfo = VarInfo1 ^ vi_type := Type
        else
            minizinc_internal_error([] : error_context, $pred,
                "var_set_ub is trying to variable's type")
        ),
        map.det_update(VarId, VarInfo, !GlobalVarMap)
    ).

%-----------------------------------------------------------------------------%

var_int_set_bounds_is_contiguous(GlobalVarMap, VarId) = Result :-
    map.lookup(GlobalVarMap, VarId, VarInfo),
    VarBounds = VarInfo ^ vi_bounds,
    (
        VarBounds = no_bounds,
        Result = yes
    ;
        VarBounds = int_bounds(_, _),
        Result = yes
    ;
        VarBounds = int_set_bounds(IntSet),
        % If IntSet is contiguous, we should have replaced the bounds
        % with int_bounds(_, _).
        % XXX Is that a wise design decision? Surely we update the range
        % more often than we care abouts is contiguity, so checking contiguity
        % only when we care about has to be more efficient.
        trace [compiletime(flag("check_var_rep"))] (
            ( if is_contiguous(IntSet, _, _) then
                true
            else
                minizinc_internal_error([] : error_context, $pred,
                    "int_set_bounds on contiguous set\n")
            )
        ),
        Result = no
    ;
        VarBounds = float_bounds(_, _),
        minizinc_internal_error([] : error_context, $pred,
            "is_var_int_set_bounds_contiguous lookup on float_bounds\n")
    ).

%-----------------------------------------------------------------------------%

var_get_updated_var_type(VarInfo) = MZType :-
    MZType0 = VarInfo ^ vi_type,
    VarInst = VarInfo ^ vi_inst,

    % If this is an int or float or int set type, then we should take the
    % bounds from the bounds field rather than the original type, since
    % bounds fields are updated as constraints are added.
    ( if
        VarInst = var_is_var,
        VarBounds = VarInfo ^ vi_bounds,
        (
            MZType0 = mzn_int(_),
            bounds_get_int_lb_ub(VarBounds, ILB, IUB),
            IBounds = int_range_lb_ub(ILB, IUB),
            MZType1 = mzn_int(IBounds)
        ;
            MZType0 = mzn_int_array(_),
            bounds_get_int_lb_ub(VarBounds, ILB, IUB),
            IBounds = int_range_lb_ub(ILB, IUB),
            MZType1 = mzn_int_array(IBounds)
        ;
            MZType0 = mzn_float(_),
            bounds_get_float_lb_ub(VarBounds, FLB, FUB),
            FBounds = float_range_lb_ub(FLB, FUB),
            MZType1 = mzn_float(FBounds)
        ;
            MZType0 = mzn_float_array(_),
            bounds_get_float_lb_ub(VarBounds, FLB, FUB),
            FBounds = float_range_lb_ub(FLB, FUB),
            MZType1 = mzn_float_array(FBounds)
        ;
            MZType0 = mzn_int_set(_),
            SBounds = bounds_get_int_set_bounds(VarBounds, MZType0),
            MZType1 = mzn_int_set(SBounds)
        ;
            MZType0 = mzn_int_set_array(_),
            SBounds = bounds_get_int_set_bounds(VarBounds, MZType0),
            MZType1 = mzn_int_set_array(SBounds)
        )
      then
        MZType = MZType1
      else
        MZType = MZType0
    ).

get_updated_var_type(GlobalVarMap, VarId) = MZType :-
    map.lookup(GlobalVarMap, VarId, VarInfo),
    MZType = var_get_updated_var_type(VarInfo).

%-----------------------------------------------------------------------------%

get_var_anns(GlobalVarMap, VarId) = Anns :-
    map.lookup(GlobalVarMap, VarId, VarInfo),
    Anns = VarInfo ^ vi_anns.

set_var_anns(VarId, Anns, !GlobalVarMap) :-
    map.lookup(!.GlobalVarMap, VarId, VarInfo0),
    VarInfo = VarInfo0 ^ vi_anns := Anns,
    map.det_update(VarId, VarInfo, !GlobalVarMap).

%-----------------------------------------------------------------------------%

mark_var_for_output(VarId, !GlobalVarMap) :-
    ( if
        map.search(!.GlobalVarMap, VarId, VarInfo0),
        VarInfo0 ^ vi_inst = var_is_var
    then
        VarInfo = VarInfo0 ^ vi_output := var_is_output,
        map.det_update(VarId, VarInfo, !GlobalVarMap)
    else
        % The variable is either local or a parameter.
        true
    ).

get_var_output_anns(VarInfo, Anns) :-
    Anns0 = VarInfo ^ vi_anns,
    Kind = VarInfo ^ vi_kind,
    (
        Kind = var_is_permanent,
        Anns1 = Anns0
    ;
        Kind = var_is_temporary,
        Anns1 = join_anns(just_var_is_introduced, Anns0)
    ),
    VarOutput = VarInfo ^ vi_output,
    (
        % A variable can be marked as output by mark_var_for_output above,
        % or (in test cases at least) it can have the is_output annotation
        % put on it explicitly in the .mzn source file.
        VarOutput = var_is_output,
        IndexRanges = VarInfo ^ vi_index_ranges,
        (
            IndexRanges = [],
            Ann = mzn_ann("output_var", []),
            Anns = set.insert(Anns1, Ann)
        ;
            IndexRanges = [_ | _],
            F = (func(IR) = Set :-
                (
                    IR = index_range(LB, UB),
                    Set = set_items(set.from_sorted_list(LB..UB))
                ;
                    IR = index_implicit,
                    unexpected($pred, "implicit index")
                )
            ),
            MZRanges = array(list.map(F, IndexRanges)),
            AnnArg = int_set_array_to_mzn_expr(array_items([], MZRanges)),
            Ann = mzn_ann("output_array", [AnnArg]),
            Anns = set.insert(Anns1, Ann)
        )
    ;
        VarOutput = var_is_not_output,
        Anns = Anns1
    ).

%-----------------------------------------------------------------------------%
:- end_module global_vars.
%-----------------------------------------------------------------------------%
