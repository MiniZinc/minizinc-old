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

:- module translate.info.
:- interface.

:- import_module error_util.
:- import_module tfzn_ast.
:- import_module tmzn_ast.
:- import_module translate.vars.

:- import_module list.
:- import_module map.
:- import_module maybe.

%-----------------------------------------------------------------------------%

    % Half reification generates implications of the form
    %   true -> constraint
    %   var  -> constraint
    % Full reification generates implications of the form
    %   var <-> constraint
    %
    % This type (implication lhs) represents the left hand side
    % of the implication.
:- type ilhs
    --->    ilhs_true
            % The constraint is asserted to be true.
    ;       ilhs_var(tfzn_bool_var)
            % The constraint is asserted to be true IF the given
            % variable is true.
    ;       ilhs_reif(tfzn_bool_var).
            % The constraint is asserted to have the same truth value
            % as the given variable.

:- func dump_ilhs(ilhs) = string.

    % XXX document why this is useful
    % we can replace the ->s with <-> in the indicated constraints,
    % because the bools on the right hand side are used just once.
    % XXX justify this
    %
    % We can translate the constraint
    %
    %   bool2int(x =< y or z =< u) >= u
    %
    % into
    %
    %   v >= u
    %   v = bool2int(b)
    %   b -> b1 or b2       <->
    %   b1 -> x =< y
    %   b2 -> z =< u
    %
    % We can translate
    %
    %   a >= 0 -> (x =< y and (u =< v or w >= 0))
    %
    % into
    %
    %   b1 or b2
    %   b1 -> a < 0
    %   b2 -> x =< y
    %   b2 -> b3 or b4      <->
    %   b3 -> u =< v
    %   b4 -> w >= 0
    %
:- type ilhs_uniqueness
    --->    lhs_not_used_only_here
    ;       lhs_used_only_here.

:- func ilhs_to_tfzn_reification(ilhs) = tfzn_reification.

%-----------------------------------------------------------------------------%

:- type asserted_truth
    --->    asserted_false
    ;       asserted_true.

    % Convert the asserted truth of `not A' (if there is such an assertion)
    % into an assertions on A.
    %
:- pred asserted_truth_not(maybe(asserted_truth)::in,
    maybe(asserted_truth)::out) is det.

    % Convert the asserted truth of `A and B' (if there is such an assertion)
    % into assertions on A and B.
    %
:- pred asserted_truth_and(maybe(asserted_truth)::in,
    maybe(asserted_truth)::out, maybe(asserted_truth)::out) is det.

    % Convert the asserted truth of `A or B' (if there is such an assertion)
    % into assertions on A and B.
    %
:- pred asserted_truth_or(maybe(asserted_truth)::in,
    maybe(asserted_truth)::out, maybe(asserted_truth)::out) is det.

    % Convert the asserted truth of `A < B' (if there is such an assertion)
    % into assertions on A and B.
    %
:- pred asserted_truth_lt(maybe(asserted_truth)::in,
    maybe(asserted_truth)::out, maybe(asserted_truth)::out) is det.

    % Convert the asserted truth of `A <= B' (if there is such an assertion)
    % into assertions on A and B.
    %
:- pred asserted_truth_le(maybe(asserted_truth)::in,
    maybe(asserted_truth)::out, maybe(asserted_truth)::out) is det.

%-----------------------------------------------------------------------------%

:- type maybe_known_truth
    --->    unknown_truth
    ;       known_truth(known_truth).

:- type known_truth
    --->    known_false
    ;       known_true.

:- func maybe_known_truth_not(maybe_known_truth) = maybe_known_truth.
:- func maybe_known_truth_and(maybe_known_truth, maybe_known_truth)
    = maybe_known_truth.
:- func maybe_known_truth_or(maybe_known_truth, maybe_known_truth)
    = maybe_known_truth.
:- func maybe_known_truth_eq(maybe_known_truth, maybe_known_truth)
    = maybe_known_truth.

%-----------------------------------------------------------------------------%

:- type optimize_result(M, F)
    --->    opt_flattening_required(M)
    ;       opt_all_done(F, tfzn_constraint_set).

:- type optimize_result_bool ==
    optimize_result(tmzn_bool_expr, maybe_known_truth).
:- type optimize_result_int ==
    optimize_result(tmzn_int_expr, tfzn_int_term).
:- type optimize_result_float ==
    optimize_result(tmzn_float_expr, tfzn_float_term).
:- type optimize_result_string ==
    optimize_result(tmzn_string_expr, tfzn_string_term).

%-----------------------------------------------------------------------------%

:- type tfzn_constraint_set.

:- func no_tfzn_constraints = tfzn_constraint_set.

:- pred add_tfzn_constraint(tfzn_item_constraint::in,
    tfzn_constraint_set::in, tfzn_constraint_set::out) is det.

:- func one_tfzn_constraint(tfzn_item_constraint) = tfzn_constraint_set.

:- func '++'(tfzn_constraint_set, tfzn_constraint_set) = tfzn_constraint_set.

:- func condense_tfzn_constraint_sets(list(tfzn_constraint_set)) =
    tfzn_constraint_set.

:- func tfzn_constraint_set_to_list(tfzn_constraint_set) =
    list(tfzn_item_constraint).

%-----------------------------------------------------------------------------%

:- pred add_tmp_var_bool(var_info_bool::in, tfzn_bool_var::out,
    tr_info::in, tr_info::out) is det.

:- pred add_tmp_var_int(var_info_int::in, tfzn_int_var::out,
    tr_info::in, tr_info::out) is det.

:- pred add_tmp_var_int_array(var_info_int_array::in, tfzn_int_array_var::out,
    tr_info::in, tr_info::out) is det.

:- pred add_tmp_var_float(var_info_float::in, tfzn_float_var::out,
    tr_info::in, tr_info::out) is det.

%-----------------------------------------------------------------------------%

    % The data structure we use to detect repeated constraints.
    % It contains a map for each kind of constraint we can generate
    % that computes a new value. Each map maps the input parameters
    % of the constraint to both a variable representing the result,
    % and the constraint itself.
:- type cse_maps.

:- type csemap_i2i ==
    map({tfzn_int_arith_unop, tfzn_int_term},
        {tfzn_int_var, tfzn_item_constraint}).
:- type csemap_ii2i ==
    map({tfzn_int_arith_binop, tfzn_int_term, tfzn_int_term},
        {tfzn_int_var, tfzn_item_constraint}).
:- type csemap_int_lin_eq ==
    map({list(int), list(tfzn_int_var), int},
        {tfzn_int_var, tfzn_item_constraint}).

:- type csemap_i2f ==
    map({tfzn_int_to_float_op, tfzn_int_term},
        {tfzn_float_var, tfzn_item_constraint}).

:- type csemap_f2f ==
    map({tfzn_float_arith_unop, tfzn_float_term},
        {tfzn_float_var, tfzn_item_constraint}).
:- type csemap_ff2f ==
    map({tfzn_float_arith_binop, tfzn_float_term, tfzn_float_term},
        {tfzn_float_var, tfzn_item_constraint}).
:- type csemap_float_lin_eq ==
    map({list(float), list(tfzn_float_var), float},
        {tfzn_float_var, tfzn_item_constraint}).

:- pred get_cse_map_i2i(cse_maps::in, csemap_i2i::out) is det.
:- pred get_cse_map_ii2i(cse_maps::in, csemap_ii2i::out) is det.
:- pred get_cse_map_int_lin_eq(cse_maps::in, csemap_int_lin_eq::out) is det.

:- pred get_cse_map_i2f(cse_maps::in, csemap_i2f::out) is det.

:- pred get_cse_map_f2f(cse_maps::in, csemap_f2f::out) is det.
:- pred get_cse_map_ff2f(cse_maps::in, csemap_ff2f::out) is det.
:- pred get_cse_map_float_lin_eq(cse_maps::in, csemap_float_lin_eq::out) is det.

:- pred set_cse_map_i2i(csemap_i2i::in,
    cse_maps::in, cse_maps::out) is det.
:- pred set_cse_map_ii2i(csemap_ii2i::in,
    cse_maps::in, cse_maps::out) is det.
:- pred set_cse_map_int_lin_eq(csemap_int_lin_eq::in,
    cse_maps::in, cse_maps::out) is det.

:- pred set_cse_map_i2f(csemap_i2f::in,
    cse_maps::in, cse_maps::out) is det.

:- pred set_cse_map_f2f(csemap_f2f::in,
    cse_maps::in, cse_maps::out) is det.
:- pred set_cse_map_ff2f(csemap_ff2f::in,
    cse_maps::in, cse_maps::out) is det.
:- pred set_cse_map_float_lin_eq(csemap_float_lin_eq::in,
    cse_maps::in, cse_maps::out) is det.

%-----------------------------------------------------------------------------%

:- pred add_error(error_spec::in,
    tr_info::in, tr_info::out) is det.

:- pred add_errors(list(error_spec)::in,
    tr_info::in, tr_info::out) is det.

    % add_overflow_error_info(Pred, Phase, SrcPos, !Info)
    % XXX Should we print the expression that overflowed?
    %
:- pred add_overflow_error_info(string::in, error_phase::in, src_pos::in,
    tr_info::in, tr_info::out) is det.

    % add_internal_error_info(Pred, Phase, SrcPos, What, !Info)
    %
:- pred add_internal_error_info(string::in, error_phase::in, src_pos::in,
    string::in, tr_info::in, tr_info::out) is det.

    % add_user_error_info(Pred, Phase, SrcPos, What, !Info)
    %
:- pred add_user_error_info(string::in, error_phase::in, src_pos::in,
    string::in, tr_info::in, tr_info::out) is det.

    % add_nyi_error_info(Pred, Phase, SrcPos, What, !Info)
    %
:- pred add_nyi_error_info(string::in, error_phase::in, src_pos::in,
    string::in, tr_info::in, tr_info::out) is det.

%-----------------------------------------------------------------------------%

    % The translation environment.
:- type tr_info.

:- pred init_tr_info(tr_info::out) is det.

:- pred tr_info_get_tmp_counters(tr_info::in, tmp_counters::out) is det.
:- pred tr_info_get_cse_maps(tr_info::in, cse_maps::out) is det.
:- pred tr_info_get_var_info_maps(tr_info::in, var_info_maps::out) is det.
:- pred tr_info_get_constraints(tr_info::in, tfzn_constraint_set::out) is det.
:- pred tr_info_get_errors(tr_info::in, list(error_spec)::out) is det.

:- pred tr_info_set_tmp_counters(tmp_counters::in,
    tr_info::in, tr_info::out) is det.
:- pred tr_info_set_cse_maps(cse_maps::in,
    tr_info::in, tr_info::out) is det.
:- pred tr_info_set_var_info_maps(var_info_maps::in,
    tr_info::in, tr_info::out) is det.
:- pred tr_info_set_constraints(tfzn_constraint_set::in,
    tr_info::in, tr_info::out) is det.
:- pred tr_info_set_errors(list(error_spec)::in,
    tr_info::in, tr_info::out) is det.

%-----------------------------------------------------------------------------%

:- func find_int_var_bounds(tr_info, tfzn_int_var) = bounds_int.
:- func find_float_var_bounds(tr_info, tfzn_float_var) = bounds_float.

:- func find_int_term_bounds(tr_info, tfzn_int_term) = bounds_int.
:- func find_float_term_bounds(tr_info, tfzn_float_term) = bounds_float.

:- pred update_int_var_bounds(tfzn_int_var::in, bounds_int::in,
    tr_info::in, tr_info::out) is det.
:- pred update_float_var_bounds(tfzn_float_var::in, bounds_float::in,
    tr_info::in, tr_info::out) is det.

:- pred update_int_term_bounds(tfzn_int_term::in, bounds_int::in,
    tr_info::in, tr_info::out) is det.
:- pred update_float_term_bounds(tfzn_float_term::in, bounds_float::in,
    tr_info::in, tr_info::out) is det.

%-----------------------------------------------------------------------------%

    % Post-process vars after the model has been constructed.
    %
    % - Ensure all var bounds are sensible, which means that either both of
    %   a variable's bounds are +/-infinity, or neither is. If only one bound
    %   is +/- infinity, we update the other bound to be infinity as well,
    %   and add a new constraint to enforce the old other bound.
    %
    % - Accumulate groups of tmp vars with the same domain into arrays, since
    %   this can substantially reduce the number of variable declarations in
    %   the FlatZinc model. This requires applying a substitution over the
    %   tmp vars in the model.
    %
:- pred tr_post_process_vars(tfzn_constraint_set::out,
    tr_info::in, tr_info::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module output_common.
:- import_module output_tfzn.
:- import_module types.

:- import_module bool.
:- import_module cord.
:- import_module counter.
:- import_module int.
:- import_module set.
:- import_module string.

%-----------------------------------------------------------------------------%

dump_ilhs(ILHS) = Str :-
    (
        ILHS = ilhs_true,
        Str = "ilhs_true"
    ;
        ILHS = ilhs_var(Var),
        Opts = output_opts(yes, 2),
        Str = bool_var_to_str(Opts, Var) ++ " ->"
    ;
        ILHS = ilhs_reif(Var),
        Opts = output_opts(yes, 2),
        Str = bool_var_to_str(Opts, Var) ++ " <->"
    ).

ilhs_to_tfzn_reification(ilhs_true) = not_reified.
ilhs_to_tfzn_reification(ilhs_var(BoolVar)) =
    half_reified(tfzn_bool_term_var(BoolVar)).
ilhs_to_tfzn_reification(ilhs_reif(BoolVar)) =
    fully_reified(tfzn_bool_term_var(BoolVar)).

%-----------------------------------------------------------------------------%

asserted_truth_not(no, no).
asserted_truth_not(yes(asserted_false), yes(asserted_true)).
asserted_truth_not(yes(asserted_true), yes(asserted_false)).

asserted_truth_and(no, no, no).
asserted_truth_and(yes(asserted_false), no, no).
asserted_truth_and(yes(asserted_true), yes(asserted_true), yes(asserted_true)).

asserted_truth_or(no, no, no).
asserted_truth_or(yes(asserted_true), no, no).
asserted_truth_or(yes(asserted_false),
    yes(asserted_false), yes(asserted_false)).

asserted_truth_lt(no, no, no).
asserted_truth_lt(yes(asserted_true), yes(asserted_false), yes(asserted_true)).
asserted_truth_lt(yes(asserted_false), no, no).

asserted_truth_le(no, no, no).
asserted_truth_le(yes(asserted_true), no, no).
asserted_truth_le(yes(asserted_false),
    yes(asserted_true), yes(asserted_false)).

%-----------------------------------------------------------------------------%

maybe_known_truth_not(MaybeKnownTruthA) = MaybeKnownTruth :-
    (
        MaybeKnownTruthA = known_truth(known_true),
        MaybeKnownTruth  = known_truth(known_false)
    ;
        MaybeKnownTruthA = known_truth(known_false),
        MaybeKnownTruth  = known_truth(known_true)
    ;
        MaybeKnownTruthA = unknown_truth,
        MaybeKnownTruth  = unknown_truth
    ).

maybe_known_truth_and(MaybeKnownTruthA, MaybeKnownTruthB) = MaybeKnownTruth :-
    (
        MaybeKnownTruthA = known_truth(known_true),
        MaybeKnownTruthB = known_truth(known_true),
        MaybeKnownTruth  = known_truth(known_true)
    ;
        MaybeKnownTruthA = known_truth(known_true),
        MaybeKnownTruthB = known_truth(known_false),
        MaybeKnownTruth  = known_truth(known_false)
    ;
        MaybeKnownTruthA = known_truth(known_true),
        MaybeKnownTruthB = unknown_truth,
        MaybeKnownTruth  = unknown_truth
    ;
        MaybeKnownTruthA = known_truth(known_false),
        MaybeKnownTruthB = known_truth(known_true),
        MaybeKnownTruth  = known_truth(known_false)
    ;
        MaybeKnownTruthA = known_truth(known_false),
        MaybeKnownTruthB = known_truth(known_false),
        MaybeKnownTruth  = known_truth(known_false)
    ;
        MaybeKnownTruthA = known_truth(known_false),
        MaybeKnownTruthB = unknown_truth,
        MaybeKnownTruth  = known_truth(known_false)
    ;
        MaybeKnownTruthA = unknown_truth,
        MaybeKnownTruthB = known_truth(known_true),
        MaybeKnownTruth  = unknown_truth
    ;
        MaybeKnownTruthA = unknown_truth,
        MaybeKnownTruthB = known_truth(known_false),
        MaybeKnownTruth  = known_truth(known_false)
    ;
        MaybeKnownTruthA = unknown_truth,
        MaybeKnownTruthB = unknown_truth,
        MaybeKnownTruth  = unknown_truth
    ).

maybe_known_truth_or(MaybeKnownTruthA, MaybeKnownTruthB) = MaybeKnownTruth :-
    (
        MaybeKnownTruthA = known_truth(known_true),
        MaybeKnownTruthB = known_truth(known_true),
        MaybeKnownTruth  = known_truth(known_true)
    ;
        MaybeKnownTruthA = known_truth(known_true),
        MaybeKnownTruthB = known_truth(known_false),
        MaybeKnownTruth  = known_truth(known_true)
    ;
        MaybeKnownTruthA = known_truth(known_true),
        MaybeKnownTruthB = unknown_truth,
        MaybeKnownTruth  = known_truth(known_true)
    ;
        MaybeKnownTruthA = known_truth(known_false),
        MaybeKnownTruthB = known_truth(known_true),
        MaybeKnownTruth  = known_truth(known_true)
    ;
        MaybeKnownTruthA = known_truth(known_false),
        MaybeKnownTruthB = known_truth(known_false),
        MaybeKnownTruth  = known_truth(known_false)
    ;
        MaybeKnownTruthA = known_truth(known_false),
        MaybeKnownTruthB = unknown_truth,
        MaybeKnownTruth  = unknown_truth
    ;
        MaybeKnownTruthA = unknown_truth,
        MaybeKnownTruthB = known_truth(known_true),
        MaybeKnownTruth  = known_truth(known_true)
    ;
        MaybeKnownTruthA = unknown_truth,
        MaybeKnownTruthB = known_truth(known_false),
        MaybeKnownTruth  = unknown_truth
    ;
        MaybeKnownTruthA = unknown_truth,
        MaybeKnownTruthB = unknown_truth,
        MaybeKnownTruth  = unknown_truth
    ).

maybe_known_truth_eq(MaybeKnownTruthA, MaybeKnownTruthB) = MaybeKnownTruth :-
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
            KnownTruth = known_false
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
    ).

%-----------------------------------------------------------------------------%

    % Using set_tree234 limits the maximum amount of the memory needed
    % to store a constraint set, but makes insertion and union slow.
    %
    % Using cords make insertion and union very fast, but allows duplicates
    % to greatly increase peak memory requirements. It also generates
    % data structures that are easier to read in the debugger :-(
    %
    % XXX We should consider using cords vs using set_tree234.

% :- type tfzn_constraint_set == set_tree234(tfzn_item_constraint).
% 
% no_tfzn_constraints = set_tree234.init.
% 
% add_tfzn_constraint(Item, !Set) :-
%     set_tree234.insert(Item, !Set).
% 
% one_tfzn_constraint(Item) = set_tree234.make_singleton_set(Item).
% 
% '++'(SetA, SetB) = SetAB :-
%     set_tree234.union(SetA, SetB, SetAB).
% 
% condense_tfzn_constraint_sets(Sets) = set_tree234.union_list(Sets).
% 
% tfzn_constraint_set_to_list(Set) = set_tree234.to_sorted_list(Set).

:- type tfzn_constraint_set == cord(tfzn_item_constraint).

no_tfzn_constraints = cord.init.

add_tfzn_constraint(Item, !Set) :-
    !:Set = cord.snoc(!.Set, Item).

one_tfzn_constraint(Item) = cord.singleton(Item).

'++'(SetA, SetB) = cord.'++'(SetA, SetB).

condense_tfzn_constraint_sets(Sets) = cord_list_to_cord(Sets).

tfzn_constraint_set_to_list(Set) = cord.list(Set).

%-----------------------------------------------------------------------------%

:- type cse_maps
    --->    cse_maps(
                % XXX many more fields to come
                csemap_i2i                      :: csemap_i2i,
                csemap_ii2i                     :: csemap_ii2i,
                csemap_int_lin_eq               :: csemap_int_lin_eq,

                csemap_i2f                      :: csemap_i2f,

                csemap_f2f                      :: csemap_f2f,
                csemap_ff2f                     :: csemap_ff2f,
                csemap_float_lin_eq             :: csemap_float_lin_eq
            ).

get_cse_map_i2i(CSEMaps, Map) :-
    Map = CSEMaps ^ csemap_i2i.
get_cse_map_ii2i(CSEMaps, Map) :-
    Map = CSEMaps ^ csemap_ii2i.
get_cse_map_int_lin_eq(CSEMaps, Map) :-
    Map = CSEMaps ^ csemap_int_lin_eq.

get_cse_map_i2f(CSEMaps, Map) :-
    Map = CSEMaps ^ csemap_i2f.

get_cse_map_f2f(CSEMaps, Map) :-
    Map = CSEMaps ^ csemap_f2f.
get_cse_map_ff2f(CSEMaps, Map) :-
    Map = CSEMaps ^ csemap_ff2f.
get_cse_map_float_lin_eq(CSEMaps, Map) :-
    Map = CSEMaps ^ csemap_float_lin_eq.

set_cse_map_i2i(Map, !CSEMaps) :-
    !CSEMaps ^ csemap_i2i := Map.
set_cse_map_ii2i(Map, !CSEMaps) :-
    !CSEMaps ^ csemap_ii2i := Map.
set_cse_map_int_lin_eq(Map, !CSEMaps) :-
    !CSEMaps ^ csemap_int_lin_eq := Map.

set_cse_map_i2f(Map, !CSEMaps) :-
    !CSEMaps ^ csemap_i2f := Map.

set_cse_map_f2f(Map, !CSEMaps) :-
    !CSEMaps ^ csemap_f2f := Map.
set_cse_map_ff2f(Map, !CSEMaps) :-
    !CSEMaps ^ csemap_ff2f := Map.
set_cse_map_float_lin_eq(Map, !CSEMaps) :-
    !CSEMaps ^ csemap_float_lin_eq := Map.

%-----------------------------------------------------------------------------%

add_error(Spec, !Info) :-
    tr_info_get_errors(!.Info, Specs0),
    Specs = [Spec | Specs0],
    tr_info_set_errors(Specs, !Info).

add_errors(NewSpecs, !Info) :-
    (
        NewSpecs = []
    ;
        NewSpecs = [_ | _],
        tr_info_get_errors(!.Info, Specs0),
        Specs = NewSpecs ++ Specs0,
        tr_info_set_errors(Specs, !Info)
    ).

add_overflow_error_info(Pred, Phase, SrcPos, !Info) :-
    make_overflow_error(Pred, Phase, SrcPos, Spec),
    add_error(Spec, !Info).

add_user_error_info(Pred, Phase, SrcPos, What, !Info) :-
    make_user_error(Pred, Phase, SrcPos, What, Spec),
    add_error(Spec, !Info).

add_internal_error_info(Pred, Phase, SrcPos, What, !Info) :-
    make_internal_error(Pred, Phase, SrcPos, What, Spec),
    add_error(Spec, !Info).

add_nyi_error_info(Pred, Phase, SrcPos, What, !Info) :-
    make_nyi_error(Pred, Phase, SrcPos, What, Spec),
    add_error(Spec, !Info).

%-----------------------------------------------------------------------------%

    % Missing:
    % predicate_map (not yet implemented)
    % local_var_map (should be extra parameter)
    % global_var_map (need type-specific version)
    % solve goal (should not be needed when translating the rest of the input)
:- type tr_info
    --->    tr_info(
                % Used to allocate new temporary global variables.
                tri_tmp_counters            :: tmp_counters,

                % Common subexpression elimination maps.
                tri_cse_maps                :: cse_maps,

                % Information about the global variables.
                tri_var_info_maps           :: var_info_maps,

                % XXX Do we need this? We plan to return the constraint set
                % resulting from the flattening of an expression as a result
                % from the predicate that does the flattening.
                tri_constraints             :: tfzn_constraint_set,

                tri_errors                  :: list(error_spec)
            ).

init_tr_info(Info) :-
    counter.init(1, TmpBoolCounter),
    counter.init(1, TmpIntCounter),
    counter.init(1, TmpFloatCounter),
    counter.init(1, TmpStrCounter),
    TmpCounters = tmp_counters(TmpBoolCounter, TmpIntCounter,
        TmpFloatCounter, TmpStrCounter),

    map.init(CSEMapI2I),
    map.init(CSEMapII2I),
    map.init(CSEMapIntLinEq),

    map.init(CSEMapI2F),

    map.init(CSEMapF2F),
    map.init(CSEMapFF2F),
    map.init(CSEMapFloatLinEq),

    CSEMaps = cse_maps(
        CSEMapI2I, CSEMapII2I, CSEMapIntLinEq,
        CSEMapI2F,
        CSEMapF2F, CSEMapFF2F, CSEMapFloatLinEq),

    VarInfoMaps = init_var_info_maps,
    ConstraintSet = no_tfzn_constraints,
    ErrorSpecs = [],

    Info = tr_info(TmpCounters, CSEMaps, VarInfoMaps, ConstraintSet,
        ErrorSpecs).

%-----------------------------------------------------------------------------%

tr_info_get_tmp_counters(Info, TmpVarCounters) :-
    TmpVarCounters = Info ^ tri_tmp_counters.
tr_info_get_cse_maps(Info, CSEMaps) :-
    CSEMaps = Info ^ tri_cse_maps.
tr_info_get_var_info_maps(Info, VarInfoMaps) :-
    VarInfoMaps = Info ^ tri_var_info_maps.
tr_info_get_constraints(Info, Constraints) :-
    Constraints = Info ^ tri_constraints.
tr_info_get_errors(Info, Specs) :-
    Specs = Info ^ tri_errors.

tr_info_set_tmp_counters(TmpVarCounters, !Info) :-
    !Info ^ tri_tmp_counters := TmpVarCounters.
tr_info_set_cse_maps(CSEMaps, !Info) :-
    !Info ^ tri_cse_maps := CSEMaps.
tr_info_set_var_info_maps(VarInfoMaps, !Info) :-
    !Info ^ tri_var_info_maps := VarInfoMaps.
tr_info_set_constraints(Constraints, !Info) :-
    !Info ^ tri_constraints := Constraints.
tr_info_set_errors(Specs, !Info) :-
    !Info ^ tri_errors := Specs.

%-----------------------------------------------------------------------------%

add_tmp_var_bool(TmpVarInfo, TmpVar, !Info) :-
    alloc_bool_tmp_var_num(N, !Info),
    TmpVar = tfzn_bool_var_tmp(N),
    tr_info_get_var_info_maps(!.Info, VarInfoMaps0),
    vim_get_bool_map(VarInfoMaps0, BoolMap0),
    map.det_insert(TmpVar, TmpVarInfo, BoolMap0, BoolMap),
    vim_set_bool_map(BoolMap, VarInfoMaps0, VarInfoMaps),
    tr_info_set_var_info_maps(VarInfoMaps, !Info).

add_tmp_var_int(TmpVarInfo, TmpVar, !Info) :-
    alloc_int_tmp_var_num(N, !Info),
    TmpVar = tfzn_int_var_tmp(N),
    tr_info_get_var_info_maps(!.Info, VarInfoMaps0),
    vim_get_int_map(VarInfoMaps0, IntMap0),
    map.det_insert(TmpVar, TmpVarInfo, IntMap0, IntMap),
    vim_set_int_map(IntMap, VarInfoMaps0, VarInfoMaps),
    tr_info_set_var_info_maps(VarInfoMaps, !Info).

add_tmp_var_int_array(TmpVarInfo, TmpVar, !Info) :-
    alloc_int_tmp_var_num(N, !Info),
    TmpVar = tfzn_int_array_var_tmp(N),
    tr_info_get_var_info_maps(!.Info, VarInfoMaps0),
    vim_get_int_array_map(VarInfoMaps0, IntArrayMap0),
    map.det_insert(TmpVar, TmpVarInfo, IntArrayMap0, IntArrayMap),
    vim_set_int_array_map(IntArrayMap, VarInfoMaps0, VarInfoMaps),
    tr_info_set_var_info_maps(VarInfoMaps, !Info).

add_tmp_var_float(TmpVarInfo, TmpVar, !Info) :-
    alloc_float_tmp_var_num(N, !Info),
    TmpVar = tfzn_float_var_tmp(N),
    tr_info_get_var_info_maps(!.Info, VarInfoMaps0),
    vim_get_float_map(VarInfoMaps0, FloatMap0),
    map.det_insert(TmpVar, TmpVarInfo, FloatMap0, FloatMap),
    vim_set_float_map(FloatMap, VarInfoMaps0, VarInfoMaps),
    tr_info_set_var_info_maps(VarInfoMaps, !Info).

%-----------------------------------------------------------------------------%

:- type tmp_counters
    --->    tmp_counters(
                % Could have separate ones for each array and set type as well.
                tmpcnt_bool                 :: counter,
                tmpcnt_int                  :: counter,
                tmpcnt_float                :: counter,
                tmpcnt_string               :: counter
            ).

:- pred alloc_bool_tmp_var_num(int::out, tr_info::in, tr_info::out) is det.
:- pred alloc_int_tmp_var_num(int::out, tr_info::in, tr_info::out) is det.
:- pred alloc_float_tmp_var_num(int::out, tr_info::in, tr_info::out) is det.
:- pred alloc_string_tmp_var_num(int::out, tr_info::in, tr_info::out) is det.

alloc_bool_tmp_var_num(N, !Info) :-
    tr_info_get_tmp_counters(!.Info, TmpCounters0),
    Counter0 = TmpCounters0 ^ tmpcnt_bool,
    counter.allocate(N, Counter0, Counter),
    TmpCounters = TmpCounters0 ^ tmpcnt_bool := Counter,
    tr_info_set_tmp_counters(TmpCounters, !Info).

alloc_int_tmp_var_num(N, !Info) :-
    tr_info_get_tmp_counters(!.Info, TmpCounters0),
    Counter0 = TmpCounters0 ^ tmpcnt_int,
    counter.allocate(N, Counter0, Counter),
    TmpCounters = TmpCounters0 ^ tmpcnt_int := Counter,
    tr_info_set_tmp_counters(TmpCounters, !Info).

alloc_float_tmp_var_num(N, !Info) :-
    tr_info_get_tmp_counters(!.Info, TmpCounters0),
    Counter0 = TmpCounters0 ^ tmpcnt_float,
    counter.allocate(N, Counter0, Counter),
    TmpCounters = TmpCounters0 ^ tmpcnt_float := Counter,
    tr_info_set_tmp_counters(TmpCounters, !Info).

alloc_string_tmp_var_num(N, !Info) :-
    tr_info_get_tmp_counters(!.Info, TmpCounters0),
    Counter0 = TmpCounters0 ^ tmpcnt_string,
    counter.allocate(N, Counter0, Counter),
    TmpCounters = TmpCounters0 ^ tmpcnt_string := Counter,
    tr_info_set_tmp_counters(TmpCounters, !Info).

%-----------------------------------------------------------------------------%

find_int_var_bounds(Info, IntVar) = Bounds :-
    tr_info_get_var_info_maps(Info, VarInfoMaps),
    vim_get_int_map(VarInfoMaps, IntMap),
    map.lookup(IntMap, IntVar, IntVarInfo),
    Bounds = IntVarInfo ^ vii_bounds.

find_float_var_bounds(Info, FloatVar) = Bounds :-
    tr_info_get_var_info_maps(Info, VarInfoMaps),
    vim_get_float_map(VarInfoMaps, FloatMap),
    map.lookup(FloatMap, FloatVar, FloatVarInfo),
    Bounds = FloatVarInfo ^ vif_bounds.

find_int_term_bounds(Info, IntTerm) = Bounds :-
    (
        IntTerm = tfzn_int_term_const(Int),
        Bounds = int_bounds_range(Int, Int)
    ;
        IntTerm = tfzn_int_term_var(IntVar),
        Bounds = find_int_var_bounds(Info, IntVar)
    ).

find_float_term_bounds(Info, FloatTerm) = Bounds :-
    (
        FloatTerm = tfzn_float_term_const(Float),
        Bounds = float_bounds_range(Float, Float)
    ;
        FloatTerm = tfzn_float_term_var(FloatVar),
        Bounds = find_float_var_bounds(Info, FloatVar)
    ).

update_int_var_bounds(IntVar, Bounds, !Info) :-
    tr_info_get_var_info_maps(!.Info, VarInfoMaps0),
    vim_get_int_map(VarInfoMaps0, IntMap0),
    map.lookup(IntMap0, IntVar, IntVarInfo0),
    IntVarInfo = IntVarInfo0 ^ vii_bounds := Bounds,
    map.det_update(IntVar, IntVarInfo, IntMap0, IntMap),
    vim_set_int_map(IntMap, VarInfoMaps0, VarInfoMaps),
    tr_info_set_var_info_maps(VarInfoMaps, !Info).

update_float_var_bounds(FloatVar, Bounds, !Info) :-
    tr_info_get_var_info_maps(!.Info, VarInfoMaps0),
    vim_get_float_map(VarInfoMaps0, FloatMap0),
    map.lookup(FloatMap0, FloatVar, FloatVarInfo0),
    FloatVarInfo = FloatVarInfo0 ^ vif_bounds := Bounds,
    map.det_update(FloatVar, FloatVarInfo, FloatMap0, FloatMap),
    vim_set_float_map(FloatMap, VarInfoMaps0, VarInfoMaps),
    tr_info_set_var_info_maps(VarInfoMaps, !Info).

update_int_term_bounds(IntTerm, Bounds, !Info) :-
    (
        IntTerm = tfzn_int_term_const(_Int)
    ;
        IntTerm = tfzn_int_term_var(IntVar),
        update_int_var_bounds(IntVar, Bounds, !Info)
    ).

update_float_term_bounds(FloatTerm, Bounds, !Info) :-
    (
        FloatTerm = tfzn_float_term_const(_Float)
    ;
        FloatTerm = tfzn_float_term_var(FloatVar),
        update_float_var_bounds(FloatVar, Bounds, !Info)
    ).

%-----------------------------------------------------------------------------%

tr_post_process_vars(!:Constraints, !Info) :-
    tr_info_get_var_info_maps(!.Info, VarInfoMaps0),
    vim_get_int_map(VarInfoMaps0, IntMap0),
    vim_get_float_map(VarInfoMaps0, FloatMap0),
    !:Constraints = no_tfzn_constraints,
    map.map_foldl(handle_half_open_bounds_int, IntMap0, IntMap,
        !Constraints),
    map.map_foldl(handle_half_open_bounds_float, FloatMap0, FloatMap,
        !Constraints),
    vim_set_int_map(IntMap, VarInfoMaps0, VarInfoMaps1),
    vim_set_float_map(FloatMap, VarInfoMaps1, VarInfoMaps),
    tr_info_set_var_info_maps(VarInfoMaps, !Info).

:- pred handle_half_open_bounds_int(tfzn_int_var::in,
    var_info_int::in, var_info_int::out,
    tfzn_constraint_set::in, tfzn_constraint_set::out) is det.

handle_half_open_bounds_int(Var, VarInfo0, VarInfo, !Constraints) :-
    int_bounds_range(LB, UB) = VarInfo0 ^ vii_bounds,
    ( if LB = int_minus_infinity, UB \= int_plus_infinity then
        VarInfo = VarInfo0 ^ vii_bounds :=
            int_bounds_range(int_minus_infinity, int_plus_infinity),
        Constraint = tfzn_constr_int_compare(int_le,
            tfzn_int_term_var(Var), tfzn_int_term_const(UB), not_reified),
        % XXX Anns
        set.init(Anns),
        ConstraintItem = tfzn_item_constraint(Constraint, Anns),
        add_tfzn_constraint(ConstraintItem, !Constraints)
    else if LB \= int_minus_infinity, UB = int_plus_infinity then
        VarInfo = VarInfo0 ^ vii_bounds :=
            int_bounds_range(int_minus_infinity, int_plus_infinity),
        Constraint = tfzn_constr_int_compare(int_le,
            tfzn_int_term_const(LB), tfzn_int_term_var(Var), not_reified),
        % XXX Anns
        set.init(Anns),
        ConstraintItem = tfzn_item_constraint(Constraint, Anns),
        add_tfzn_constraint(ConstraintItem, !Constraints)
    else
        VarInfo = VarInfo0
    ).

:- pred handle_half_open_bounds_float(tfzn_float_var::in,
    var_info_float::in, var_info_float::out,
    tfzn_constraint_set::in, tfzn_constraint_set::out) is det.

handle_half_open_bounds_float(Var, VarInfo0, VarInfo, !Constraints) :-
    float_bounds_range(LB, UB) = VarInfo0 ^ vif_bounds,
    ( if LB = float_minus_infinity, UB \= float_plus_infinity then
        VarInfo = VarInfo0 ^ vif_bounds :=
            float_bounds_range(float_minus_infinity, float_plus_infinity),
        Constraint = tfzn_constr_float_compare(float_le,
            tfzn_float_term_var(Var), tfzn_float_term_const(UB), not_reified),
        % XXX Anns
        set.init(Anns),
        ConstraintItem = tfzn_item_constraint(Constraint, Anns),
        add_tfzn_constraint(ConstraintItem, !Constraints)
    else if LB \= float_minus_infinity, UB = float_plus_infinity then
        VarInfo = VarInfo0 ^ vif_bounds :=
            float_bounds_range(float_minus_infinity, float_plus_infinity),
        Constraint = tfzn_constr_float_compare(float_le,
            tfzn_float_term_const(LB), tfzn_float_term_var(Var), not_reified),
        % XXX Anns
        set.init(Anns),
        ConstraintItem = tfzn_item_constraint(Constraint, Anns),
        add_tfzn_constraint(ConstraintItem, !Constraints)
    else
        VarInfo = VarInfo0
    ).

%-----------------------------------------------------------------------------%
:- end_module translate.info.
%-----------------------------------------------------------------------------%
