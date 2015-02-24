%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Ralph Becket <rafe@csse.unimelb.edu.au>
%
% Functions to convert parts of MiniZinc and FlatZinc representations
% to strings.
%
%-----------------------------------------------------------------------------%

:- module common_format.
:- interface.

:- import_module types.

:- import_module zinc_ast.

:- import_module list.

%-----------------------------------------------------------------------------%

:- func format_string_expr(string_expr) = string.

:- func format_string_expr_unquoted(string_expr) = string.

%-----------------------------------------------------------------------------%

:- func format_mzn_expr(mzn_expr) = string.

    % Format a list of mzn_exprs as a comma-separated list in brackets.
    %
:- func format_mzn_exprs(mzn_exprs) = string.

:- func format_mzn_var(mzn_var) = string.

:- func format_mzn_type(index_ranges, var_par, mzn_type) = string.

:- func format_fzn_par_type(index_ranges, mzn_type) = string.

:- func format_mzn_anns(mzn_anns) = string.

    % format_list(F. LPar, RPar, List):
    %
    % Convert a list into a comma separated string representation
    % with the given bracketing characters.
    %
:- func format_list(func(T) = string, string, string, list(T)) = string.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module intset.

:- import_module array.
:- import_module bool.
:- import_module int.
:- import_module require.
:- import_module set.
:- import_module string.

%-----------------------------------------------------------------------------%

format_string_expr(A) = Str :-
    do_format_string_expr_acc(A, ["\""], Strs),
    Str = string.append_list(["\"" | Strs]).

format_string_expr_unquoted(A) = Str :-
    do_format_string_expr_acc(A, [], Strs),
    Str = string.append_list(Strs).

:- pred do_format_string_expr_acc(string_expr::in,
    list(string)::in, list(string)::out) is det.

do_format_string_expr_acc(Expr, !Strs) :-
    require_complete_switch [Expr] (
        Expr = string_const(Str),
        !:Strs = [Str | !.Strs]
    ;
        % show/1 is handled specially in flatten.expr.m.
        Expr = string_show(_),
        unexpected($pred, "show/1 encountered")
    ;
        Expr = SA ++ SB, 
        do_format_string_expr_acc(SB, !Strs),
        do_format_string_expr_acc(SA, !Strs)
    ;
        Expr = string_concat(ConcatExprs),
        !:Strs = list.map(format_string_expr_unquoted, ConcatExprs) ++ !.Strs
    ;
        Expr = string_join(SepExpr, JoinExprs),
        SepStr = format_string_expr_unquoted(SepExpr),
        JoinStrs = list.map(format_string_expr_unquoted, JoinExprs),
        Str = string.join_list(SepStr, JoinStrs),
        !:Strs = [Str | !.Strs] 
    ).

%-----------------------------------------------------------------------------%

format_mzn_expr(mzn_expr(RawMZ, Anns)) =
    string.(format_mzn_raw_expr(RawMZ) ++ format_mzn_anns(Anns)).

format_mzn_exprs(MZs) = format_list(format_mzn_expr, "(", ")", MZs).

%-----------------------------------------------------------------------------%

:- func format_mzn_raw_expr(mzn_raw_expr) = string.

format_mzn_raw_expr(RawMZ) = Str :-
    (    
        RawMZ = bool_expr(A),
        (
            A = bool_const(no),
            Str = "false"
        ;
            A = bool_const(yes),
            Str = "true"
        ;
            A = bool_var(Var),
            Str = format_mzn_var(Var)
        ;
            ( A = bool_conj(_)
            ; A = bool_disj(_)
            ),
            unexpected($pred, "Not a FlatZinc expression.")
        )
    ;
        RawMZ = float_expr(A),
        (
            A = float_const(F),
            Str = float_to_string(F)
        ;
            A = float_var(Var),
            Str = format_mzn_var(Var)
        ;
            ( A = _ + _
            ; A = _ * _
            ), 
            unexpected($pred, "Not a FlatZinc expression.")
        )
    ;
        RawMZ = int_expr(A),
        (
            A = int_const(F),
            Str = int_to_string(F)
        ;
            A = int_var(Var),
            Str = format_mzn_var(Var)
        ;
            ( A = _ + _
            ; A = _ * _
            ),
            unexpected($pred, "Not a FlatZinc expression.")
        )
    ;
        RawMZ = int_set_expr(A),
        ( A = set_items(IntSet),  Str = format_int_set_items(IntSet)
        ; A = set_var(Var),       Str = format_mzn_var(Var)
        )
    ;
        RawMZ = bool_array_expr(A),
        (
            A = array_var(_, VarId),
            Str = var_name(VarId)
        ;
            A = array_items(_, As),
            Str = format_array_items(bool_to_mzn_expr, As)
        )
    ;
        RawMZ = float_array_expr(A),
        (
            A = array_var(_, VarId),
            Str = var_name(VarId)
        ;
            A = array_items(_, As),
            Str = format_array_items(float_to_mzn_expr, As)
        )
    ;
        RawMZ = int_array_expr(A),
        (
            A = array_var(_, VarId),
            Str = var_name(VarId)
        ;
            A = array_items(_, As),
            Str = format_array_items(int_to_mzn_expr, As)
        )
    ;
        RawMZ = int_set_array_expr(A),
        (
            A = array_var(_, VarId),
            Str = var_name(VarId)
        ;
            A = array_items(_, As),
            Str = format_array_items(int_set_to_mzn_expr, As)
        )
    ;
        RawMZ = string_expr(A),
        Str = format_string_expr(A)
    ;
        RawMZ = ann_expr(A),
        Str = format_mzn_ann_term(A)
    ;
        RawMZ = string_array_expr(A),
        (
            A = array_var(_, VarId),
            Str = var_name(VarId)
        ;
            A = array_items(_, As),
            Str = format_array_items(string_to_mzn_expr, As)
        )
    ;
        RawMZ = ann_array_expr(A),
        (
            A = array_var(_, VarId),
            Str = var_name(VarId)
        ;
            A = array_items(_, As),
            Str = format_array_items(ann_to_mzn_expr, As)
        )
    ;
        RawMZ = bottom_expr(_),
        Str = "_"
    ;
        RawMZ = bottom_array_expr(A),
        (
            A = array_var(_, _),
            unexpected($pred, "Not a FlatZinc expression.")
        ;
            A = array_items(_, As),
            Str = format_array_items(bottom_to_mzn_expr, As)
        )
    ;
        ( RawMZ = bool_set_array_expr(_)
        ; RawMZ = bool_set_expr(_)
        ; RawMZ = float_set_array_expr(_)
        ; RawMZ = float_set_expr(_)
        ),
        unexpected($pred, "Not a FlatZinc expression.")
    ).

%-----------------------------------------------------------------------------%

:- func format_int_set_items(set(int)) = string.

format_int_set_items(Set) = Str :-
    ( if
        Xs = set.to_sorted_list(Set),
        Xs = [Min | _],
        list.last(Xs, Max)
    then
% Don't simplify singleton sets to {x} since this routine is used to
% output array index ranges in output_array(...) annotations.
%         ( if Min = Max then
%             Str = string.append_list(["{", int_to_string(Min), "}"])
%           else
        ( if 1 + Max - Min = list.length(Xs) then
            Str = string.append_list([int_to_string(Min), "..",
                int_to_string(Max)])
        else
            Str = format_list(int_to_string, "{", "}", Xs)
        )
    else
        Str = "{}"
    ).

%-----------------------------------------------------------------------------%

:- func format_array_items(func(T) = mzn_expr, array(T)) = string.

format_array_items(F, Xs) = ArrayStr :-
    MZExprs = array_map_to_list(F, Xs),
    ArrayStr = format_list(format_mzn_expr, "[", "]", MZExprs).

:- func array_map_to_list((func(T) = mzn_expr), array(T)) = mzn_exprs.

array_map_to_list(F, Xs) = Elems :-
    % The Mercury stdlib doesn't currently (as of 10.04) have a predicate
    % version of array.foldr.
    DoF = (func(X, !.Exprs) = !:Exprs :-
        Expr = F(X),
        !:Exprs = [Expr | !.Exprs]
    ),
    Elems = array.foldr(DoF, Xs, []).

%-----------------------------------------------------------------------------%

format_mzn_var(var_no_index(VarId)) = var_name(VarId).
format_mzn_var(var_index(VarId, Index)) =
    string.append_list([var_name(VarId), "[", int_to_string(Index), "]"]).

%-----------------------------------------------------------------------------%

format_mzn_type(IndexRanges, VarPar, MZType) = Str :-
    VarParStr = ( if VarPar = var then "var " else "" ),
    (
        IndexRanges = [],
        Str = string.(VarParStr ++ format_mzn_type_2(MZType))
    ;
        IndexRanges = [_ | _],
        Str = string.append_list([
            "array ",
            format_list(format_index_range, "[", "]", IndexRanges),
            " of ",
            VarParStr,
            format_mzn_type_2(MZType)
        ])
    ).

%-----------------------------------------------------------------------------%

    % The array part of the type (if any) has already been handled by
    % format_mzn_type.
    %
:- func format_mzn_type_2(mzn_type) = string.

format_mzn_type_2(mzn_bool) = "bool".
format_mzn_type_2(mzn_float(float_range_unbounded)) = "float".
format_mzn_type_2(mzn_float(float_range_lb_ub(LB, UB))) =
    ( if LB = float_minus_infinity, UB = float_plus_infinity then
        "float"
    else
        string.append_list([float_to_string(LB), "..", float_to_string(UB)])
    ).
format_mzn_type_2(mzn_float(float_range_set(Set))) =
    format_list(float_to_string, "{", "}", set.to_sorted_list(Set)).
format_mzn_type_2(mzn_int(int_range_unbounded)) = "int".
format_mzn_type_2(mzn_int(int_range_lb_ub(Min, Max))) =
    ( if Min = int_minus_infinity, Max = int_plus_infinity then
        "int"
    else
        string.append_list([int_to_string(Min), "..", int_to_string(Max)])
    ).
format_mzn_type_2(mzn_int(int_range_set(Set))) =
    ( if
        % JJJ - INTSET
        Xs = intset.to_sorted_list(Set),
        Xs = [Min | _],
        list.last(Xs, Max),
        intset.size(Set) = 1 + Max - Min
    then
        format_mzn_type_2(mzn_int(int_range_lb_ub(Min, Max)))
    else
        format_list(int_to_string, "{", "}", intset.to_sorted_list(Set))
    ).
format_mzn_type_2(mzn_bool_set) = "set of bool".
format_mzn_type_2(mzn_float_set(Bounds)) =
    string.("set of " ++ format_mzn_type_2(mzn_float(Bounds))).
format_mzn_type_2(mzn_int_set(Bounds)) =
    string.("set of " ++ format_mzn_type_2(mzn_int(Bounds))).
format_mzn_type_2(mzn_bool_array) = format_mzn_type_2(mzn_bool).
format_mzn_type_2(mzn_float_array(Bounds)) =
    format_mzn_type_2(mzn_float(Bounds)).
format_mzn_type_2(mzn_int_array(Bounds)) =
    format_mzn_type_2(mzn_int(Bounds)).
format_mzn_type_2(mzn_bool_set_array) = format_mzn_type_2(mzn_bool_set).
format_mzn_type_2(mzn_float_set_array(Bounds)) =
    format_mzn_type_2(mzn_float_set(Bounds)).
format_mzn_type_2(mzn_int_set_array(Bounds)) =
    format_mzn_type_2(mzn_int_set(Bounds)).
format_mzn_type_2(mzn_string) = "string".
format_mzn_type_2(mzn_string_array) = "string".
format_mzn_type_2(mzn_ann) = "ann".
format_mzn_type_2(mzn_ann_array) = "ann".
format_mzn_type_2(mzn_bottom) = _ :-
    unexpected($pred, "bottom").
format_mzn_type_2(mzn_bottom_array) = _ :-
    unexpected($pred, "array of bottom").

%-----------------------------------------------------------------------------%

format_fzn_par_type(IndexRanges, MZType) = Str :-
    (
        IndexRanges = [],
        Str = format_fzn_par_type_2(MZType)
    ;
        IndexRanges = [_ | _],
        Str = string.append_list([
            "array ",
            format_list(format_index_range, "[", "]", IndexRanges),
            " of ",
            format_fzn_par_type_2(MZType)
        ])
    ).

:- func format_fzn_par_type_2(mzn_type) = string.

format_fzn_par_type_2(Type) = Str :-
    (
        ( Type = mzn_bool
        ; Type = mzn_bool_array
        ),
        Str = "bool"
    ;
        ( Type = mzn_float(_)
        ; Type = mzn_float_array(_)
        ),
        Str = "float"
    ;
        ( Type = mzn_int(_)
        ; Type = mzn_int_array(_)
        ),
        Str = "int"
    ;
        ( Type = mzn_int_set(_)
        ; Type = mzn_int_set_array(_)
        ),
        Str = "set of int"
    ;
        ( Type = mzn_bool_set
        ; Type = mzn_float_set(_)
        ; Type = mzn_bool_set_array
        ; Type = mzn_float_set_array(_)
        ; Type = mzn_string
        ; Type = mzn_string_array
        ; Type = mzn_ann
        ; Type = mzn_ann_array
        ; Type = mzn_bottom
        ; Type = mzn_bottom_array
        ),
        unexpected($module, $pred, "not a FlatZinc parameter type")
    ).

%-----------------------------------------------------------------------------%

:- func format_index_range(index_range) = string.

format_index_range(index_implicit) = "int".
format_index_range(index_range(LB, UB)) =
    string.append_list([int_to_string(LB), "..", int_to_string(UB)]).

%-----------------------------------------------------------------------------%

format_mzn_anns(Anns) =
    ( if set.empty(Anns) then
        ""
    else
        string.append_list(list.map(format_mzn_ann, set.to_sorted_list(Anns)))
    ).

%-----------------------------------------------------------------------------%

:- func format_mzn_ann(mzn_ann) = string.

format_mzn_ann(Ann) = " :: " ++ format_mzn_ann_term(Ann).

%-----------------------------------------------------------------------------%

:- func format_mzn_ann_term(mzn_ann) = string.

format_mzn_ann_term(mzn_ann(AnnName, [])) = AnnName.
format_mzn_ann_term(mzn_ann(AnnName, AnnArgs @ [_ | _])) =
    AnnName ++ format_mzn_exprs(AnnArgs).
format_mzn_ann_term(mzn_ann_var(MZVar)) = format_mzn_var(MZVar).

%-----------------------------------------------------------------------------%

format_list(_F, LPar, RPar, []) = string.(LPar ++ RPar).
format_list(F, LPar, RPar, [MZ | MZs]) =
    string.append_list([LPar, F(MZ) | format_list_2(F, RPar, MZs)]).

:- func format_list_2(func(T) = string, string, list(T)) = list(string).

format_list_2(_F, RPar, []) = [RPar].
format_list_2(F, RPar, [MZ | MZs]) =
    [", ", F(MZ) | format_list_2(F, RPar, MZs)].

%-----------------------------------------------------------------------------%
:- end_module common_format.
%-----------------------------------------------------------------------------%
