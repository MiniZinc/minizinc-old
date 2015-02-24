%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
% A representation of MiniZinc strings.
%
%-----------------------------------------------------------------------------%

:- module hr.string.
:- interface.

:- import_module errors.
:- import_module hr.info.
:- import_module types.
:- import_module mzn_ops.

:- import_module bool.

%-----------------------------------------------------------------------------%

:- pred hr_flatten_show_to_string(error_context::in, mzn_anns::in,
    ilhs::in, mzn_expr::in, string_expr::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

:- pred hr_flatten_string_string_to_string(error_context::in, mzn_anns::in,
    string_string_to_string_op::in, string_expr::in, string_expr::in,
    string_expr::out) is det.

:- pred hr_flatten_string_string_to_bool(error_context::in, mzn_anns::in,
    string_string_to_bool_op::in, string_expr::in, string_expr::in,
    bool::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module common_format.
:- import_module hr.array.
:- import_module hr.convert.
:- import_module hr.int.
:- import_module list.
:- import_module string.

%-----------------------------------------------------------------------------%

hr_flatten_show_to_string(Context, Anns, ILHS, MZ0, Z, AllConstraints,
        !Info, !Model) :-
    % If we are showing a scalar, we need to ensure it is simplified.
    % If we are showing an array, we need to ensure it is fully dereferenced.
    MZ0 = mzn_expr(RawMZ0, Anns0),
    (
        RawMZ0 = bool_expr(A0),
        hr_simplify_bool_cv(Context, Anns, ILHS, A0, CVA, AllConstraints,
            !Info, !Model),
        A = bool_const_or_var_to_expr(CVA),
        RawMZ = bool_expr(A)
    ;
        RawMZ0 = bool_set_expr(_),
        mzn_constraint_set_empty(AllConstraints),
        RawMZ = RawMZ0
    ;
        RawMZ0 = bool_array_expr(A0),
        A = hr_fully_deref_bool_array(!.Info, !.Model, Context, A0),
        mzn_constraint_set_empty(AllConstraints),
        RawMZ = bool_array_expr(A)
    ;
        RawMZ0 = bool_set_array_expr(A0),
        A = hr_fully_deref_bool_set_array(!.Info, !.Model, Context, A0),
        mzn_constraint_set_empty(AllConstraints),
        RawMZ = bool_set_array_expr(A)
    ;
        RawMZ0 = float_expr(A0),
        hr_simplify_float(Context, Anns, ILHS, A0, A, AllConstraints,
            !Info, !Model),
        RawMZ = float_expr(A)
    ;
        RawMZ0 = float_set_expr(_),
        mzn_constraint_set_empty(AllConstraints),
        RawMZ = RawMZ0
    ;
        RawMZ0 = float_array_expr(A0),
        A = hr_fully_deref_float_array(!.Info, !.Model, Context, A0),
        mzn_constraint_set_empty(AllConstraints),
        RawMZ = float_array_expr(A)
    ;
        RawMZ0 = float_set_array_expr(A0),
        A = hr_fully_deref_float_set_array(!.Info, !.Model, Context, A0),
        mzn_constraint_set_empty(AllConstraints),
        RawMZ = float_set_array_expr(A)
    ;
        RawMZ0 = int_expr(A0),
        hr_simplify_int(Context, Anns, ILHS, A0, A, AllConstraints,
            !Info, !Model),
        RawMZ = int_expr(A)
    ;
        RawMZ0 = int_set_expr(_),
        mzn_constraint_set_empty(AllConstraints),
        RawMZ = RawMZ0
    ;
        RawMZ0 = int_array_expr(A0),
        A = hr_fully_deref_int_array(!.Info, !.Model, Context, A0),
        mzn_constraint_set_empty(AllConstraints),
        RawMZ = int_array_expr(A)
    ;
        RawMZ0 = int_set_array_expr(A0),
        A = hr_fully_deref_int_set_array(!.Info, !.Model, Context, A0),
        mzn_constraint_set_empty(AllConstraints),
        RawMZ = int_set_array_expr(A)
    ;
        RawMZ0 = ann_expr(_),
        mzn_constraint_set_empty(AllConstraints),
        RawMZ = RawMZ0
    ;
        RawMZ0 = ann_array_expr(A0),
        A = hr_fully_deref_ann_array(!.Info, !.Model, Context, A0),
        mzn_constraint_set_empty(AllConstraints),
        RawMZ = ann_array_expr(A)
    ;
        RawMZ0 = string_expr(_),
        mzn_constraint_set_empty(AllConstraints),
        RawMZ = RawMZ0
    ;
        RawMZ0 = string_array_expr(A0),
        A = hr_fully_deref_string_array(!.Info, !.Model, Context, A0),
        mzn_constraint_set_empty(AllConstraints),
        RawMZ = string_array_expr(A)
    ;
        RawMZ0 = bottom_expr(_),
        mzn_constraint_set_empty(AllConstraints),
        RawMZ = RawMZ0
    ;
        % It is not possible to express aliasing in MiniZinc for this case.
        RawMZ0 = bottom_array_expr(_),
        mzn_constraint_set_empty(AllConstraints),
        RawMZ = RawMZ0
    ),
    ( if
        RawMZ = string_expr(A1),
        Z0 = string_const(format_string_expr_unquoted(A1))
    then
        Z = Z0
    else
        MZ = mzn_expr(RawMZ, Anns0),
        Z = string_const(format_mzn_expr(MZ))
    ).

%-----------------------------------------------------------------------------%

hr_flatten_string_string_to_string(_Context, _Anns, Op, A, B, Z) :-
    (
        Op = ss2s_append,
        Z = A ++ B
    ).

%-----------------------------------------------------------------------------%

hr_flatten_string_string_to_bool(_Context, _Anns, Op, A, B, BoolZ) :-
    StrA = format_string_expr(A),
    StrB = format_string_expr(B),
    compare(CmpRes, StrA, StrB),
    ( Op = ss2b_eq, BoolZ = ( if CmpRes = (=) then yes else no )
    ; Op = ss2b_ee, BoolZ = ( if CmpRes = (=) then yes else no )
    ; Op = ss2b_ne, BoolZ = ( if CmpRes \= (=) then yes else no )
    ; Op = ss2b_lt, BoolZ = ( if CmpRes = (<) then yes else no )
    ; Op = ss2b_le, BoolZ = ( if CmpRes \= (>) then yes else no )
    ; Op = ss2b_gt, BoolZ = ( if CmpRes = (>) then yes else no )
    ; Op = ss2b_ge, BoolZ = ( if CmpRes \= (<) then yes else no )
    ).

%-----------------------------------------------------------------------------%
:- end_module hr.string.
%-----------------------------------------------------------------------------%
