%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2009-2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Ralph Becket <rafe@csse.unimelb.edu.au>
%
% A representation of MiniZinc types and values.
%
%-----------------------------------------------------------------------------%

:- module types.
:- interface.

:- import_module errors.

:- import_module intset.
:- import_module types_and_insts.
:- import_module zinc_ast.
:- import_module zinc_common.

:- import_module array.
:- import_module bool.
:- import_module list.
:- import_module map.
:- import_module maybe.
:- import_module set.
:- import_module set_tree234.

%-----------------------------------------------------------------------------%

:- type model
    --->    model(
                model_pred_map      :: predicate_map,
                model_globals       :: global_var_map,
                model_constraints   :: mzn_constraint_set,
                model_solve_goal    :: maybe(mzn_solve_goal)
            ).

:- func empty_model = model.

:- type pred_name == string.
:- type proc_no == int.
:- type pred_proc_id
    --->    pred_proc_id(pred_name, proc_no).

    % Lookup and record predicate details.
    %
:- type predicate_map == map(pred_proc_id, predicate_info).

:- type predicate_info
    --->    predicate_info(
                % Parameter types and names, annotations, optional body.
                pred_params     :: ti_exprs_and_ids,
                pred_anns       :: exprs,
                pred_body       :: maybe(expr)
            ).

:- type var_kind
    --->    var_is_permanent
    ;       var_is_temporary.

:- type var_inst
    --->    var_is_par
    ;       var_is_var.

:- type var_output
    --->    var_is_not_output
    ;       var_is_output.

:- type var_bounds
    --->    no_bounds
    ;       float_bounds(
                fb_lower    :: float,       % may be float_minus_infinity
                fb_upper    :: float        % may be float_plus_infinity
            )
    ;       int_bounds(
                ib_lower    :: int,         % may be int_minus_infinity
                ib_upper    :: int          % may be int_plus_infinity
            )
    ;       int_set_bounds(
                isb_set     ::  intset      % Only used for discontiguous sets
            ).

:- type var_info
    --->    var_info(
                % The type of the variable. Any bounds information in the type
                % is superseded by the contents of the vi_bounds field.
                vi_type         :: mzn_type,

                % The index ranges of the various dimentions of the array
                % the variable represents. The number of elements in the list
                % must correspond to the type of the variable; it should be
                % zero unless the variable is of an array type.
                vi_index_ranges :: list(index_range),   % [] unless array type

                % If the variable is defined to be equal to an expression,
                % this is the expression.
                vi_value        :: maybe(mzn_expr),

                % Is the variable temporary or not? Is it a parameter or not?
                vi_kind         :: var_kind,
                vi_inst         :: var_inst,

                % Does the variable appear in an output item?
                % Note that for now, a variable can be made output not only
                % by appearing in an output item, but also by having an
                % is_output annotation on it. We record the latter in the
                % annotations field, together with all other annotations.
                vi_output       :: var_output,

                % Information we have deduced about the bounds on the variable.
                % The bounds information must be compatible with the type of
                % the variable (e.g. an int variable cannot have float bounds).
                % This field is initialized from any ranges in the type of the
                % variable, but can be (and typically is) updated  later when
                % constraints are added.
                vi_bounds       :: var_bounds,

                % The annotations on the variable.
                vi_anns         :: mzn_anns
            ).

:- type global_var_map == map(var_id, var_info).

    % Locals map *only* to values.
    % Bounds and other info is attached to the *value* of the local,
    % not the local itself.
    %
:- type local_var_map == map(var_id, mzn_expr).

:- type cse_map == map(mzn_constraint, var_id).

:- type mzn_constraint_set == set_tree234(mzn_constraint).

:- pred mzn_constraint_set_empty(mzn_constraint_set::out) is det.
:- pred mzn_constraint_set_is_empty(mzn_constraint_set::in) is semidet.
:- pred mzn_constraint_set_singleton(mzn_constraint::in,
    mzn_constraint_set::out) is det.
:- pred mzn_constraint_set_from_list(list(mzn_constraint)::in,
    mzn_constraint_set::out) is det.
:- pred mzn_constraint_set_insert(mzn_constraint::in,
    mzn_constraint_set::in, mzn_constraint_set::out) is det.
:- pred mzn_constraint_set_insert_list(list(mzn_constraint)::in,
    mzn_constraint_set::in, mzn_constraint_set::out) is det.
:- pred mzn_constraint_set_union(mzn_constraint_set::in,
    mzn_constraint_set::in, mzn_constraint_set::out) is det.
:- pred mzn_constraint_set_union_list(list(mzn_constraint_set)::in,
    mzn_constraint_set::out) is det.
:- pred mzn_constraint_set_union_mixed_list(list(mzn_constraint)::in,
    list(mzn_constraint_set)::in, mzn_constraint_set::out) is det.
:- pred mzn_constraint_set_diff(mzn_constraint_set::in,
    mzn_constraint_set::in, mzn_constraint_set::out) is det.
:- pred mzn_constraint_set_map(
    pred(mzn_constraint, mzn_constraint)::in(pred(in, out) is det),
    mzn_constraint_set::in, mzn_constraint_set::out) is det.

:- type mzn_solve_goal
    --->    mzn_solve_goal(mzn_anns, mzn_solve_kind).

    % For minimize and maximize, the mzn_expr is the objective function.
:- type mzn_solve_kind
    --->    mzn_solve_satisfy
    ;       mzn_solve_minimize(mzn_expr)
    ;       mzn_solve_maximize(mzn_expr).

%-----------------------------------------------------------------------------%

:- type mzn_constraint
    --->    mzn_constraint(string, list(mzn_expr), mzn_anns).

:- type mzn_constraints == list(mzn_constraint).

%-----------------------------------------------------------------------------%

:- type mzn_expr
    --->    mzn_expr(mzn_raw_expr, mzn_anns).

:- type mzn_exprs == list(mzn_expr).

:- type mzn_expr_array == array(mzn_expr).

:- type mzn_raw_expr
    --->    bool_expr(bool_expr)
    ;       bool_set_expr(bool_set_expr)
    ;       bool_array_expr(bool_array_expr)
    ;       bool_set_array_expr(bool_set_array_expr)

    ;       float_expr(float_expr)
    ;       float_set_expr(float_set_expr)
    ;       float_array_expr(float_array_expr)
    ;       float_set_array_expr(float_set_array_expr)

    ;       int_expr(int_expr)
    ;       int_set_expr(int_set_expr)
    ;       int_array_expr(int_array_expr)
    ;       int_set_array_expr(int_set_array_expr)

    ;       string_expr(string_expr)
    ;       string_array_expr(string_array_expr)

    ;       ann_expr(mzn_ann)
    ;       ann_array_expr(ann_array_expr)

    ;       bottom_expr(bottom_expr)
    ;       bottom_array_expr(bottom_array_expr).

%-----------------------------------------------------------------------------%

:- type bool_expr
    --->    bool_const(bool)
    ;       bool_var(mzn_var)
    ;       bool_conj(list(bool_expr))       % May only contain bool_vars.
    ;       bool_disj(list(bool_expr)).      % May only contain bool_vars.

:- type bool_exprs == list(bool_expr).

:- type bool_const_or_var
    --->    boolcv_const(bool)
    ;       boolcv_var(mzn_var).

:- func bool_const_or_var_to_expr(bool_const_or_var) = bool_expr.

%-----------------------------------------------------------------------------%

:- type float_expr
    --->    float_const(float)
    ;       float_var(mzn_var)
    ;       float_expr + float_expr
    ;       float * float_expr.

:- type float_exprs == array(float_expr).

:- type float_range
    --->    float_range_unbounded
    ;       float_range_lb_ub(float, float)
    ;       float_range_set(set(float)).

    % Decide whether an float_expr is simple (i.e. is in FlatZinc form).
    % This matters because we have "simple" constraints, such as "float_le",
    % and "linear" constraints, such as "float_lin_le", depending upon whether
    % the float_exprs are simple or not.
    %
:- pred float_expr_is_simple(float_expr::in) is semidet.

%-----------------------------------------------------------------------------%

:- type int_expr
    --->    int_const(int)
    ;       int_var(mzn_var)
    ;       int_expr + int_expr
    ;       int * int_expr.

:- type int_exprs == array(int_expr).

:- type int_range
    --->    int_range_unbounded
    ;       int_range_lb_ub(int, int)
    ;       int_range_set(intset).

    % Decide whether an int_expr is simple (i.e., is in FlatZinc form).
    %
:- pred int_expr_is_simple(int_expr::in) is semidet.

%-----------------------------------------------------------------------------%

:- type string_expr
    --->    string_const(string)
    ;       string_show(mzn_expr)
    ;       string_expr ++ string_expr
    ;       string_concat(string_exprs)
    ;       string_join(string_expr, string_exprs).

:- type string_exprs == list(string_expr).

:- type string_array_expr == array_expr(string_expr).

%-----------------------------------------------------------------------------%

:- type set_expr(T)
    --->    set_items(set(T))
    ;       set_var(mzn_var).

:- type bool_set_expr == set_expr(bool).
:- type float_set_expr == set_expr(float).
:- type int_set_expr == set_expr(int).

:- type bool_set_exprs == array(bool_set_expr).
:- type float_set_exprs == array(float_set_expr).
:- type int_set_exprs == array(int_set_expr).

:- func list_to_set_expr(list(T)) = set_expr(T).

%-----------------------------------------------------------------------------%

:- type array_expr(T)
    --->    array_items(index_ranges, array(T))
    ;       array_var(index_ranges, var_id).

:- type bool_array_expr == array_expr(bool_expr).
:- type float_array_expr == array_expr(float_expr).
:- type int_array_expr == array_expr(int_expr).

:- type bottom_expr
    --->    bottom_expr.

:- type bottom_array_expr == array_expr(bottom_expr).

:- type bool_set_array_expr == array_expr(bool_set_expr).
:- type float_set_array_expr == array_expr(float_set_expr).
:- type int_set_array_expr == array_expr(int_set_expr).

:- type index_range
    --->    index_range(
                ir_lb   ::  int,
                ir_ub   ::  int
            )
   
    ;       index_implicit.

:- type index_ranges == list(index_range).

%-----------------------------------------------------------------------------%

:- type mzn_ann
    --->    mzn_ann(string, list(mzn_expr))
    ;       mzn_ann_var(mzn_var).

:- type mzn_anns == set(mzn_ann).

:- type ann_array_expr == array_expr(mzn_ann).

%-----------------------------------------------------------------------------%

:- type mzn_relop
    --->    relop_eq
    ;       relop_ne
    ;       relop_ge
    ;       relop_gt
    ;       relop_le
    ;       relop_lt.

%-----------------------------------------------------------------------------%

:- type mzn_type
    --->    mzn_bool
    ;       mzn_float(float_range)
    ;       mzn_int(int_range)

    ;       mzn_bool_set
    ;       mzn_float_set(float_range)
    ;       mzn_int_set(int_range)

    ;       mzn_bool_array
    ;       mzn_float_array(float_range)
    ;       mzn_int_array(int_range)

    ;       mzn_bool_set_array
    ;       mzn_float_set_array(float_range)
    ;       mzn_int_set_array(int_range)

    ;       mzn_string
    ;       mzn_string_array

    ;       mzn_ann
    ;       mzn_ann_array

    ;       mzn_bottom
    ;       mzn_bottom_array.

%-----------------------------------------------------------------------------%

:- type mzn_var
    --->    var_no_index(var_id)            % An unsubscripted var.
    ;       var_index(var_id, int).         % A subscripted var.

:- type var_id == zinc_common.id.
:- type var_ids == list(var_id).

:- func mzn_var_id(mzn_var) = var_id.

:- func var_name(var_id) = string.
:- func name_to_global_var(string) = var_id.

%-----------------------------------------------------------------------------%

:- func float_minus_infinity = float.
:- func float_plus_infinity = float.

:- func int_minus_infinity = int.
:- func int_plus_infinity = int.

:- pred get_float_bounds(var_bounds::in, float::out, float::out) is det.
:- pred get_int_bounds(var_bounds::in, int::out, int::out) is det.

%-----------------------------------------------------------------------------%

    % FlatZinc arrays are one dimensional and are 1-based.
    %
:- func index_ranges_to_fzn_form(array_expr(ElemT)) = array_expr(ElemT).

:- func index_ranges_to_size(index_ranges) = int.

:- func array_size(array_expr(T)) = int.

:- func replace_index_ranges(index_ranges, array_expr(T)) = array_expr(T).

:- func get_index_ranges(array_expr(T)) = index_ranges.

%-----------------------------------------------------------------------------%

:- func mzn_expr_to_bool(error_context, mzn_expr) = bool_expr.
:- func mzn_expr_to_int(error_context, mzn_expr) = int_expr.
:- func mzn_expr_to_float(error_context, mzn_expr) = float_expr.
:- func mzn_expr_to_string(error_context, mzn_expr) = string_expr.
:- func mzn_expr_to_ann(error_context, mzn_expr) = mzn_ann.
:- func mzn_expr_to_bool_set(error_context, mzn_expr) = bool_set_expr.
:- func mzn_expr_to_int_set(error_context, mzn_expr) = int_set_expr.
:- func mzn_expr_to_float_set(error_context, mzn_expr) = float_set_expr.
:- func mzn_expr_to_bool_array(error_context, mzn_expr) = bool_array_expr.
:- func mzn_expr_to_float_array(error_context, mzn_expr) = float_array_expr.
:- func mzn_expr_to_int_array(error_context, mzn_expr) = int_array_expr.
:- func mzn_expr_to_bool_set_array(error_context, mzn_expr) =
    bool_set_array_expr.
:- func mzn_expr_to_float_set_array(error_context, mzn_expr) =
    float_set_array_expr.
:- func mzn_expr_to_int_set_array(error_context, mzn_expr) =
    int_set_array_expr.
:- func mzn_expr_to_string_array(error_context, mzn_expr) = string_array_expr.
:- func mzn_expr_to_ann_array(error_context, mzn_expr) = ann_array_expr.

:- pred mzn_expr_to_bool_acc(error_context::in, mzn_expr::in,
    list(bool_expr)::in, list(bool_expr)::out) is det.
:- pred mzn_expr_to_int_acc(error_context::in, mzn_expr::in,
    list(int_expr)::in, list(int_expr)::out) is det.
:- pred mzn_expr_to_float_acc(error_context::in, mzn_expr::in,
    list(float_expr)::in, list(float_expr)::out) is det.
:- pred mzn_expr_to_ann_acc(error_context::in, mzn_expr::in,
    list(mzn_ann)::in, list(mzn_ann)::out) is det.
:- pred mzn_expr_to_string_acc(error_context::in, mzn_expr::in,
    list(string_expr)::in, list(string_expr)::out) is det.
:- pred mzn_expr_to_bool_set_acc(error_context::in, mzn_expr::in,
    list(bool_set_expr)::in, list(bool_set_expr)::out) is det.
:- pred mzn_expr_to_int_set_acc(error_context::in, mzn_expr::in,
    list(int_set_expr)::in, list(int_set_expr)::out) is det.
:- pred mzn_expr_to_float_set_acc(error_context::in, mzn_expr::in,
    list(float_set_expr)::in, list(float_set_expr)::out) is det.

:- func mzn_expr_to_bool_const(error_context, mzn_expr) = bool.
:- func mzn_expr_to_int_const(error_context, mzn_expr) = int.
:- func mzn_expr_to_float_const(error_context, mzn_expr) = float.

%-----------------------------------------------------------------------------%

:- func ann_to_mzn_expr(mzn_ann) = mzn_expr.
:- func bool_to_mzn_expr(bool_expr) = mzn_expr.
:- func float_to_mzn_expr(float_expr) = mzn_expr.
:- func int_to_mzn_expr(int_expr) = mzn_expr.
:- func string_to_mzn_expr(string_expr) = mzn_expr.
:- func bottom_to_mzn_expr(bottom_expr) = mzn_expr.

:- func bool_set_to_mzn_expr(bool_set_expr) = mzn_expr.
:- func float_set_to_mzn_expr(float_set_expr) = mzn_expr.
:- func int_set_to_mzn_expr(int_set_expr) = mzn_expr.

:- func bool_array_to_mzn_expr(bool_array_expr) = mzn_expr.
:- func float_array_to_mzn_expr(float_array_expr) = mzn_expr.
:- func int_array_to_mzn_expr(int_array_expr) = mzn_expr.
:- func string_array_to_mzn_expr(string_array_expr) = mzn_expr.

:- func ann_array_to_mzn_expr(ann_array_expr) = mzn_expr.
:- func bool_set_array_to_mzn_expr(bool_set_array_expr) = mzn_expr.
:- func float_set_array_to_mzn_expr(float_set_array_expr) = mzn_expr.
:- func int_set_array_to_mzn_expr(int_set_array_expr) = mzn_expr.
:- func bottom_array_to_mzn_expr(bottom_array_expr) = mzn_expr.

%-----------------------------------------------------------------------------%

:- pred ann_is_par(mzn_ann::in) is semidet.
:- pred bool_is_par(bool_expr::in) is semidet.
:- pred float_is_par(float_expr::in) is semidet.
:- pred int_is_par(int_expr::in) is semidet.
:- pred string_is_par(string_expr::in) is semidet.

:- pred bool_set_is_par(bool_set_expr::in) is semidet.
:- pred float_set_is_par(float_set_expr::in) is semidet.
:- pred int_set_is_par(int_set_expr::in) is semidet.

%-----------------------------------------------------------------------------%

:- func null_ann = mzn_ann.
:- func no_anns = mzn_anns.
:- func add_ann(mzn_ann, mzn_anns) = mzn_anns.
:- func join_anns(mzn_anns, mzn_anns) = mzn_anns.

:- func domain = mzn_ann.
:- func var_is_introduced = mzn_ann.
:- func is_defined_var = mzn_ann.
:- func defines_var(mzn_expr) = mzn_ann.

:- func just_domain = mzn_anns.
:- func just_var_is_introduced = mzn_anns.
:- func just_is_defined_var = mzn_anns.
:- func just_defines_var(mzn_expr) = mzn_anns.

%-----------------------------------------------------------------------------%

:- pred type_inst_to_mzn_type(error_context::in, type_inst::in,
    var_par::out, mzn_type::out) is det.

%-----------------------------------------------------------------------------%

:- func make_var_mzn_expr(index_ranges, mzn_type, var_id) = mzn_expr.

%-----------------------------------------------------------------------------%

:- type constraint_name_suffix_kind
    --->    cns_none
    ;       cns_reif
    ;       cns_half.

:- func cns_kind_to_string(constraint_name_suffix_kind) = string.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module float.
:- import_module int.
:- import_module require.

%-----------------------------------------------------------------------------%

empty_model = model(map.init, map.init, set_tree234.init, no).

%-----------------------------------------------------------------------------%

mzn_constraint_set_empty(ConstraintSet) :-
    ConstraintSet = set_tree234.init.

mzn_constraint_set_is_empty(ConstraintSet) :-
    set_tree234.empty(ConstraintSet).

mzn_constraint_set_singleton(Constraint, ConstraintSet) :-
    set_tree234.singleton_set(Constraint, ConstraintSet).

mzn_constraint_set_from_list(Constraints, ConstraintSet) :-
    ConstraintSet = set_tree234.list_to_set(Constraints).

mzn_constraint_set_insert(Constraint, !ConstraintSet) :-
    set_tree234.insert(Constraint, !ConstraintSet).

mzn_constraint_set_insert_list(Constraints, !ConstraintSet) :-
    set_tree234.insert_list(Constraints, !ConstraintSet).

mzn_constraint_set_union(ConstraintSetA, ConstraintSetB, ConstraintSetAB) :-
    set_tree234.union(ConstraintSetA, ConstraintSetB, ConstraintSetAB).

mzn_constraint_set_union_list(ConstraintSets, ConstraintSet) :-
    set_tree234.union_list(ConstraintSets, ConstraintSet).

mzn_constraint_set_union_mixed_list(Constraints, ConstraintSets,
        ConstraintSet) :-
    set_tree234.union_list(ConstraintSets, ConstraintSet0),
    set_tree234.insert_list(Constraints, ConstraintSet0, ConstraintSet).

mzn_constraint_set_diff(ConstraintSetA, ConstraintSetB, ConstraintSetAmB) :-
    set_tree234.difference(ConstraintSetA, ConstraintSetB, ConstraintSetAmB).

mzn_constraint_set_map(Pred, !ConstraintSet) :-
    set_tree234.map(Pred, !ConstraintSet).

%-----------------------------------------------------------------------------%

bool_const_or_var_to_expr(boolcv_const(BoolConst)) = bool_const(BoolConst).
bool_const_or_var_to_expr(boolcv_var(BoolVar)) = bool_var(BoolVar).

%-----------------------------------------------------------------------------%

float_expr_is_simple(float_const(_)).
float_expr_is_simple(float_var(_)).

%-----------------------------------------------------------------------------%

int_expr_is_simple(int_const(_)).
int_expr_is_simple(int_var(_)).

%-----------------------------------------------------------------------------%

list_to_set_expr(Xs) =
    set_items(set.from_list(Xs)).

%-----------------------------------------------------------------------------%

mzn_var_id(var_no_index(VarId)) = VarId.
mzn_var_id(var_index(VarId, _Index)) = VarId.

var_name(VarId) = zinc_common.id_name(VarId).

name_to_global_var(VarId) = id_global(VarId).

%-----------------------------------------------------------------------------%

float_minus_infinity = -float_plus_infinity.
float_plus_infinity = float.max.
int_minus_infinity = -int_plus_infinity.
int_plus_infinity = int.max_int.

get_float_bounds(VarBounds, LB, UB) :-
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
        trace [compiletime(flag("check_var_rep"))] (
            ( if semidet_succeed then
                minizinc_internal_error([] : error_context, $pred,
                    "int bound on float\n")
            else
                true
            )
        ),
        LB = float_minus_infinity,
        UB = float_plus_infinity
    ).

get_int_bounds(VarBounds, LB, UB) :-
    (
        VarBounds = no_bounds,
        LB = int_minus_infinity,
        UB = int_plus_infinity
    ;
        VarBounds = float_bounds(_, _),
        trace [compiletime(flag("check_var_rep"))] (
            ( if semidet_succeed then
                minizinc_internal_error([] : error_context, $pred,
                    "float bound on int\n")
            else
                true
            )
        ),
        LB = int_minus_infinity,
        UB = int_plus_infinity
    ;
        VarBounds = int_bounds(LB, UB)
    ;
        VarBounds = int_set_bounds(Set),
        ( if least(Set, LB0) then
            LB = LB0
        else
            LB = int_minus_infinity
        ),
        ( if greatest(Set, UB0) then
            UB = UB0
        else
            UB = int_plus_infinity
        )
    ).

%-----------------------------------------------------------------------------%

index_ranges_to_fzn_form(A0) = A :-
    (
        A0 = array_items(IndexRanges0, As),
        ( if IndexRanges0 = [index_range(1, _)] then
            A = A0
          else
            Size = index_ranges_to_size(IndexRanges0),
            A = array_items([index_range(1, Size)], As)
        )
    ;
        A0 = array_var(IndexRanges0, V),
        ( if IndexRanges0 = [index_range(1, _)] then
            A = A0
          else
            Size = index_ranges_to_size(IndexRanges0),
            A = array_var([index_range(1, Size)], V)
        )
    ).

index_ranges_to_size(IndexRanges) = Size :-
    Size = list.foldl(index_ranges_to_size_2, IndexRanges, 1).

:- func index_ranges_to_size_2(index_range, int) = int.

index_ranges_to_size_2(IndexRange, Size0) = Size :-
    (
        IndexRange = index_range(LB, UB),
        Size = (1 + UB - LB) * Size0
    ;
        IndexRange = index_implicit,
        unexpected($pred, "implicit index")
    ).

array_size(Array) = Size :-
    ( Array = array_items(IndexRanges, _)
    ; Array = array_var(IndexRanges, _)
    ),
    Size = index_ranges_to_size(IndexRanges).

replace_index_ranges(IndexRanges, array_items(_, Items)) =
    array_items(IndexRanges, Items).
replace_index_ranges(IndexRanges, array_var(_, VarId)) =
    array_var(IndexRanges, VarId).

get_index_ranges(ArrayExpr) = IndexRanges:-
    (
        ArrayExpr = array_items(IndexRanges, _)
    ;
        ArrayExpr = array_var(IndexRanges, _)
    ).

%-----------------------------------------------------------------------------%

mzn_expr_to_bool(Context, mzn_expr(RawMZ, _)) = Expr :-
    ( if RawMZ = bool_expr(Expr0) then
        Expr = Expr0
    else
        minizinc_user_error(Context, "Expected bool_expr.\n")
    ).

mzn_expr_to_int(Context, MZ) = Expr :-
    ( if MZ = mzn_expr(int_expr(Expr0), _) then
        Expr = Expr0
    else
        minizinc_internal_error(Context, $pred, "Expected int_expr.\n")
    ).

mzn_expr_to_float(Context, MZ) = Expr :-
    ( if MZ = mzn_expr(float_expr(Expr0), _) then
        Expr = Expr0
    else
        minizinc_internal_error(Context, $pred, "Expected float_expr.\n")
    ).

mzn_expr_to_string(Context, MZ) = Expr :-
    ( if MZ = mzn_expr(string_expr(Expr0), _) then
        Expr = Expr0
    else
        minizinc_internal_error(Context, $pred, "Expected string_expr.\n")
    ).

mzn_expr_to_ann(Context, MZ) = Expr :-
    ( if MZ = mzn_expr(ann_expr(Expr0), _) then
        Expr = Expr0
      else
        minizinc_internal_error(Context, $pred, "Expected mzn_ann.\n")
    ).

mzn_expr_to_bool_set(Context, MZ) = Expr :-
    ( if MZ = mzn_expr(bool_set_expr(Expr0), _) then
        Expr = Expr0
    else
        minizinc_internal_error(Context, $pred, "Expected bool_set_expr.\n")
    ).

mzn_expr_to_int_set(Context, MZ) = Expr :-
    ( if MZ = mzn_expr(int_set_expr(Expr0), _) then
        Expr = Expr0
    else
        minizinc_internal_error(Context, $pred, "Expected int_set_expr.\n")
    ).

mzn_expr_to_float_set(Context, MZ) = Expr :-
    ( if MZ = mzn_expr(float_set_expr(Expr0), _) then
        Expr = Expr0
    else
        minizinc_internal_error(Context, $pred, "Expected float_set_expr.\n")
    ).

mzn_expr_to_bool_array(Context, mzn_expr(RawMZ, _)) = Expr :-
    ( if RawMZ = bool_array_expr(Expr0) then
        Expr = Expr0
    else
        minizinc_internal_error(Context, $pred, "Expected bool_array_expr.\n")
    ).

mzn_expr_to_float_array(Context, mzn_expr(RawMZ, _)) = Expr :-
    ( if RawMZ = float_array_expr(Expr0) then
        Expr = Expr0
    else
        minizinc_internal_error(Context, $pred, "Expected float_array_expr.\n")
    ).

mzn_expr_to_int_array(Context, mzn_expr(RawMZ, _)) = Expr :-
    ( if RawMZ = int_array_expr(Expr0) then
        Expr = Expr0
    else
        minizinc_internal_error(Context, $pred, "Expected int_array_expr.\n")
    ).

mzn_expr_to_bool_set_array(Context, mzn_expr(RawMZ, _)) = Expr :-
    ( if RawMZ = bool_set_array_expr(Expr0) then
        Expr = Expr0
    else
        minizinc_internal_error(Context, $pred,
            "Expected bool_set_array_expr.\n")
    ).

mzn_expr_to_float_set_array(Context, mzn_expr(RawMZ, _)) = Expr :-
    ( if RawMZ = float_set_array_expr(Expr0) then
        Expr = Expr0
    else
        minizinc_internal_error(Context, $pred,
            "Expected float_set_array_expr.\n")
    ).

mzn_expr_to_int_set_array(Context, mzn_expr(RawMZ, _)) = Expr :-
    ( if RawMZ = int_set_array_expr(Expr0) then
        Expr = Expr0
    else
        minizinc_internal_error(Context, $pred,
            "Expected int_set_array_expr.\n")
    ).

mzn_expr_to_string_array(Context, mzn_expr(RawMZ, _)) = Expr :-
    ( if RawMZ = string_array_expr(Expr0) then
        Expr = Expr0
    else
        minizinc_internal_error(Context, $pred,
            "Expected string_array_expr.\n")
    ).

mzn_expr_to_ann_array(Context, mzn_expr(RawMZ, _)) = Expr :-
    ( if RawMZ = ann_array_expr(Expr0) then
        Expr = Expr0
    else
        minizinc_internal_error(Context, $pred,
            "Expected ann_array_expr.\n")
    ).

%-----------------------------------------------------------------------------%

mzn_expr_to_bool_acc(Context, Mzn, !Exprs) :-
    Expr = mzn_expr_to_bool(Context, Mzn),
    !:Exprs = [Expr | !.Exprs].

mzn_expr_to_int_acc(Context, MZ, !Exprs) :-
    Expr = mzn_expr_to_int(Context, MZ),
    !:Exprs = [Expr | !.Exprs].

mzn_expr_to_float_acc(Context, MZ, !Exprs) :-
    Expr = mzn_expr_to_float(Context, MZ),
    !:Exprs = [Expr | !.Exprs].

mzn_expr_to_string_acc(Context, MZ, !Exprs) :-
    Expr = mzn_expr_to_string(Context, MZ),
    !:Exprs = [Expr | !.Exprs].

mzn_expr_to_ann_acc(Context, MZ, !Exprs) :-
    Expr = mzn_expr_to_ann(Context, MZ),
    !:Exprs = [Expr | !.Exprs].

mzn_expr_to_bool_set_acc(Context, MZ, !Exprs) :-
    Expr = mzn_expr_to_bool_set(Context, MZ),
    !:Exprs = [Expr | !.Exprs].

mzn_expr_to_int_set_acc(Context, MZ, !Exprs) :-
    Expr = mzn_expr_to_int_set(Context, MZ),
    !:Exprs = [Expr | !.Exprs].

mzn_expr_to_float_set_acc(Context, MZ, !Exprs) :-
    Expr = mzn_expr_to_float_set(Context, MZ),
    !:Exprs = [Expr | !.Exprs].

%-----------------------------------------------------------------------------%

mzn_expr_to_bool_const(Context, MZ) = B :-
    ( if mzn_expr_to_bool(Context, MZ) = bool_const(B0) then
        B = B0
    else
        minizinc_user_error(Context, "Expected a bool constant.\n")
    ).

mzn_expr_to_int_const(Context, MZ) = I :-
    ( if mzn_expr_to_int(Context, MZ) = int_const(I0) then
        I = I0
    else
        minizinc_user_error(Context, "Expected an int constant.\n")
    ).

mzn_expr_to_float_const(Context, MZ) = F :-
    ( if mzn_expr_to_float(Context, MZ) = float_const(F0) then
        F = F0
    else
        minizinc_user_error(Context, "Expected a float constant.\n")
    ).

%-----------------------------------------------------------------------------%

ann_to_mzn_expr(Ann) = mzn_expr(ann_expr(Ann), no_anns).
bool_to_mzn_expr(BoolExpr) = mzn_expr(bool_expr(BoolExpr), no_anns).
float_to_mzn_expr(FloatExpr) = mzn_expr(float_expr(FloatExpr), no_anns).
int_to_mzn_expr(IntExpr) = mzn_expr(int_expr(IntExpr), no_anns).
string_to_mzn_expr(StringExpr) = mzn_expr(string_expr(StringExpr), no_anns).
bottom_to_mzn_expr(BottomExpr) = mzn_expr(bottom_expr(BottomExpr), no_anns).

bool_set_to_mzn_expr(A) = mzn_expr(bool_set_expr(A), no_anns).
float_set_to_mzn_expr(A) = mzn_expr(float_set_expr(A), no_anns).
int_set_to_mzn_expr(A) = mzn_expr(int_set_expr(A), no_anns).

% When converting back to mzn_exprs, we want to ensure that array values
% go out with FlatZinc 1-based 1-dimensional index sets, not arbitrary
% MiniZinc index sets.

bool_array_to_mzn_expr(ArrayExpr) =
    mzn_expr(bool_array_expr(index_ranges_to_fzn_form(ArrayExpr)), no_anns).
float_array_to_mzn_expr(ArrayExpr) =
    mzn_expr(float_array_expr(index_ranges_to_fzn_form(ArrayExpr)), no_anns).
string_array_to_mzn_expr(ArrayExpr) =
    mzn_expr(string_array_expr(index_ranges_to_fzn_form(ArrayExpr)), no_anns).
ann_array_to_mzn_expr(ArrayExpr) =
    mzn_expr(ann_array_expr(index_ranges_to_fzn_form(ArrayExpr)), no_anns).

int_array_to_mzn_expr(ArrayExpr) =
    mzn_expr(int_array_expr(index_ranges_to_fzn_form(ArrayExpr)), no_anns).
bool_set_array_to_mzn_expr(ArrayExpr) =
    mzn_expr(bool_set_array_expr(index_ranges_to_fzn_form(ArrayExpr)), no_anns).
float_set_array_to_mzn_expr(ArrayExpr) =
    mzn_expr(float_set_array_expr(index_ranges_to_fzn_form(ArrayExpr)),
        no_anns).
int_set_array_to_mzn_expr(ArrayExpr) =
    mzn_expr(int_set_array_expr(index_ranges_to_fzn_form(ArrayExpr)), no_anns).
bottom_array_to_mzn_expr(ArrayExpr) =
    mzn_expr(bottom_array_expr(index_ranges_to_fzn_form(ArrayExpr)), no_anns).

%-----------------------------------------------------------------------------%

ann_is_par(_) :-
    semidet_true.
bool_is_par(bool_const(_)).
float_is_par(float_const(_)).
int_is_par(int_const(_)).

bool_set_is_par(set_items(_)).
float_set_is_par(set_items(_)).
int_set_is_par(set_items(_)).
string_is_par(string_const(_)).

%-----------------------------------------------------------------------------%

null_ann = mzn_ann("null", []).
no_anns = set.init.
add_ann(A, Bs) = set.insert(Bs, A).
join_anns(As, Bs) = set.union(As, Bs).

domain = mzn_ann("domain", []).
var_is_introduced = mzn_ann("var_is_introduced", []).
is_defined_var = mzn_ann("is_defined_var", []).
defines_var(MZ) = mzn_ann("defines_var", [MZ]).

just_domain = set.make_singleton_set(domain).
just_var_is_introduced = set.make_singleton_set(var_is_introduced).
just_is_defined_var = set.make_singleton_set(is_defined_var).
just_defines_var(MZ) = set.make_singleton_set(defines_var(MZ)).

%-----------------------------------------------------------------------------%

type_inst_to_mzn_type(Context, TI, VarPar, MZType) :-
    ( if
        (
            TI = ti_par_bool,
            VarPar0 = par,
            MZType0 = mzn_bool
        ;
            TI = ti_var_bool,
            VarPar0 = var,
            MZType0 = mzn_bool
        ;
            TI = ti_par_float,
            VarPar0 = par,
            MZType0 = mzn_float(float_range_unbounded)
        ;
            TI = ti_var_float,
            VarPar0 = var,
            MZType0 = mzn_float(float_range_unbounded)
        ;
            TI = ti_par_int,
            VarPar0 = par,
            MZType0 = mzn_int(int_range_unbounded)
        ;
            TI = ti_var_int,
            VarPar0 = var,
            MZType0 = mzn_int(int_range_unbounded)
        ;
            TI = ti_ann,
            VarPar0 = par,
            MZType0 = mzn_ann
        ;
            TI = ti_par_string,
            VarPar0 = par,
            MZType0 = mzn_string
        ;
            TI = ti_par_set(ti_par_bool),
            VarPar0 = par,
            MZType0 = mzn_bool_set
        ;
            TI = ti_var_set(ti_par_bool),
            VarPar0 = var,
            MZType0 = mzn_bool_set
        ;
            TI = ti_par_set(ti_par_float),
            VarPar0 = par,
            MZType0 = mzn_float_set(float_range_unbounded)
        ;
            TI = ti_var_set(ti_par_float),
            VarPar0 = var,
            MZType0 = mzn_float_set(float_range_unbounded)
        ;
            TI = ti_par_set(ti_par_int),
            VarPar0 = par,
            MZType0 = mzn_int_set(int_range_unbounded)
        ;
            TI = ti_var_set(ti_par_int),
            VarPar0 = var,
            MZType0 = mzn_int_set(int_range_unbounded)
        ;
            % This happens because the broken type inference algorithm
            % doesn't assign types to empty sets inside par-to-var
            % coercions.  The only such sets can be int sets.
            %
            TI = ti_par_set(ti_par_bottom),
            VarPar0 = par,
            MZType0 = mzn_int_set(int_range_unbounded)
        ;
            TI = ti_array(_, ti_par_bool),
            VarPar0 = par,
            MZType0 = mzn_bool_array
        ;
            TI = ti_array(_, ti_var_bool),
            VarPar0 = var,
            MZType0 = mzn_bool_array
        ;
            TI = ti_array(_, ti_par_float),
            VarPar0 = par,
            MZType0 = mzn_float_array(float_range_unbounded)
        ;
            TI = ti_array(_, ti_var_float),
            VarPar0 = var,
            MZType0 = mzn_float_array(float_range_unbounded)
        ;
            TI = ti_array(_, ti_par_int),
            VarPar0 = par,
            MZType0 = mzn_int_array(int_range_unbounded)
        ;
            TI = ti_array(_, ti_var_int),
            VarPar0 = var,
            MZType0 = mzn_int_array(int_range_unbounded)
        ;
            TI = ti_array(_, ti_ann),
            VarPar0 = par,
            MZType0 = mzn_ann_array
        ;
            TI = ti_array(_, ti_par_string),
            VarPar0 = par,
            MZType0 = mzn_string_array
        ;
            TI = ti_array(_, ti_par_set(ti_par_bool)),
            VarPar0 = par,
            MZType0 = mzn_bool_set_array
        ;
            TI = ti_array(_, ti_var_set(ti_par_bool)),
            VarPar0 = var,
            MZType0 = mzn_bool_set_array
        ;
            TI = ti_array(_, ti_par_set(ti_par_float)),
            VarPar0 = par,
            MZType0 = mzn_float_set_array(float_range_unbounded)
        ;
            TI = ti_array(_, ti_var_set(ti_par_float)),
            VarPar0 = var,
            MZType0 = mzn_float_set_array(float_range_unbounded)
        ;
            TI = ti_array(_, ti_par_set(ti_par_int)),
            VarPar0 = par,
            MZType0 = mzn_int_set_array(int_range_unbounded)
        ;
            TI = ti_array(_, ti_var_set(ti_par_int)),
            VarPar0 = var,
            MZType0 = mzn_int_set_array(int_range_unbounded)
        ;
            % XXX This can occur if we have an expression like: [{}, {}, {}].
            TI = ti_array(_, ti_par_set(ti_par_bottom)),
            VarPar0 = par,
            MZType0 = mzn_int_set_array(int_range_set(intset(1, 0)))
        ;
            TI = ti_array(_, ti_par_bottom),
            VarPar0 = par,
            MZType0 = mzn_bottom_array
        ;
            TI = ti_var_bottom,
            VarPar0 = var,
            MZType0 = mzn_bottom
        )
      then
        VarPar = VarPar0,
        MZType = MZType0
      else
        minizinc_user_error(Context,
            "This is not a valid MiniZinc type.\n")
    ).

%-----------------------------------------------------------------------------%

make_var_mzn_expr(IndexRanges, MZType, VarId) = MZ :-
    MZVar = var_no_index(VarId),
    (
        MZType = mzn_bool,
        RawMZ = bool_expr(bool_var(MZVar))
    ;
        MZType = mzn_float(_),
        RawMZ = float_expr(float_var(MZVar))
    ;
        MZType = mzn_int(_),
        RawMZ = int_expr(int_var(MZVar))
    ;
        MZType = mzn_bool_set,
        RawMZ = bool_set_expr(set_var(MZVar))
    ;
        MZType = mzn_float_set(_),
        RawMZ = float_set_expr(set_var(MZVar))
    ;
        MZType = mzn_int_set(_),
        RawMZ = int_set_expr(set_var(MZVar))
    ;
        MZType = mzn_bool_array,
        RawMZ = bool_array_expr(array_var(IndexRanges, VarId))
    ;
        MZType = mzn_float_array(_),
        RawMZ = float_array_expr(array_var(IndexRanges, VarId))
    ;
        MZType = mzn_int_array(_),
        RawMZ = int_array_expr(array_var(IndexRanges, VarId))
    ;
        MZType = mzn_bool_set_array,
        RawMZ = bool_set_array_expr(array_var(IndexRanges, VarId))
    ;
        MZType = mzn_float_set_array(_),
        RawMZ = float_set_array_expr(array_var(IndexRanges, VarId))
    ;
        MZType = mzn_int_set_array(_),
        RawMZ = int_set_array_expr(array_var(IndexRanges, VarId))
    ;
        MZType = mzn_ann,
        RawMZ = ann_expr(mzn_ann_var(var_no_index(VarId)))
    ;
        MZType = mzn_ann_array,
        RawMZ = ann_array_expr(array_var(IndexRanges, VarId))
    ;
        % This is a dummy placeholder: there are no string
        % variables in MiniZinc.
        MZType = mzn_string,
        RawMZ = string_expr(string_const(""))
    ;
        MZType = mzn_string_array,
        RawMZ = string_array_expr(array_var(IndexRanges, VarId))
    ;
        MZType = mzn_bottom,
        unexpected($pred, "mzn_bottom")
    ;
        MZType = mzn_bottom_array,
        unexpected($pred, "mzn_bottom_array")
    ),
    MZ = mzn_expr(RawMZ, no_anns).

%-----------------------------------------------------------------------------%

cns_kind_to_string(SuffixKind) = Suffix :-
    ( SuffixKind = cns_none, Suffix = ""
    ; SuffixKind = cns_reif, Suffix = "_reif"
    ; SuffixKind = cns_half, Suffix = "_halfreif"
    ).

%-----------------------------------------------------------------------------%
:- end_module types.
%-----------------------------------------------------------------------------%
