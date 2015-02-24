%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2009 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Ralph Becket <rafe@csse.unimelb.edu.au>
%
% A representation of MiniZinc strings.
%
%-----------------------------------------------------------------------------%

:- module flatten.string.
:- interface.

:- import_module errors.
:- import_module flatten.env.
:- import_module mzn_ops.
:- import_module types.

:- import_module bool.

%-----------------------------------------------------------------------------%

:- pred flatten_show_to_string(error_context::in,
    mzn_expr::in, string::out, env::in, env::out) is det.

:- pred flatten_show_int_to_string(error_context::in,
    mzn_expr::in, mzn_expr::in, string::out, env::in, env::out) is det.

:- pred flatten_show_float_to_string(error_context::in, mzn_expr::in,
    mzn_expr::in, mzn_expr::in, string::out, env::in, env::out) is det.        

:- pred flatten_string_string_to_string(error_context::in, mzn_anns::in,
    string_string_to_string_op::in, string_expr::in, string_expr::in,
    string_expr::out, env::in, env::out) is det.

:- pred flatten_string_string_to_bool(error_context::in, mzn_anns::in,
    string_string_to_bool_op::in, string_expr::in, string_expr::in,
    bool::out, env::in, env::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module common_format.
:- import_module flatten.array.
:- import_module flatten.bool.
:- import_module flatten.float.
:- import_module flatten.int.

:- import_module int.
:- import_module list.
:- import_module set.
:- import_module string.

%-----------------------------------------------------------------------------%

flatten_show_to_string(Context, MZ0, Z, !Env) :-
    % If we are showing a scalar, we need to ensure it is simplified.
    % If we are showing an array, we need to ensure it is fully dereferenced.
    MZ0 = mzn_expr(RawMZ0, Anns0),
    (
        RawMZ0 = bool_expr(A0),
        simplify_bool(Context, A0, A, !Env),
        RawMZ = bool_expr(A)
    ;
        RawMZ0 = bool_set_expr(_),
        RawMZ = RawMZ0
    ;
        RawMZ0 = bool_array_expr(A0),
        A = fully_deref_bool_array(Context, A0, !.Env),
        RawMZ = bool_array_expr(A)
    ;
        RawMZ0 = bool_set_array_expr(A0),
        A = fully_deref_bool_set_array(Context, A0, !.Env),
        RawMZ = bool_set_array_expr(A)
    ;
        RawMZ0 = float_expr(A0),
        simplify_float(Context, A0, A, !Env),
        RawMZ = float_expr(A)
    ;
        RawMZ0 = float_set_expr(_),
        RawMZ = RawMZ0
    ;
        RawMZ0 = float_array_expr(A0),
        A = fully_deref_float_array(Context, A0, !.Env),
        RawMZ = float_array_expr(A)
    ;
        RawMZ0 = float_set_array_expr(A0),
        A = fully_deref_float_set_array(Context, A0, !.Env),
        RawMZ = float_set_array_expr(A)
    ;
        RawMZ0 = int_expr(A0),
        simplify_int(Context, A0, A, !Env),
        RawMZ = int_expr(A)
    ;
        RawMZ0 = int_set_expr(_),
        RawMZ = RawMZ0
    ;
        RawMZ0 = int_array_expr(A0),
        A = fully_deref_int_array(Context, A0, !.Env),
        RawMZ = int_array_expr(A)
    ;
        RawMZ0 = int_set_array_expr(A0),
        A = fully_deref_int_set_array(Context, A0, !.Env),
        RawMZ = int_set_array_expr(A)
    ;
        RawMZ0 = ann_expr(_),
        RawMZ = RawMZ0
    ;
        RawMZ0 = ann_array_expr(A0),
        A = fully_deref_ann_array(Context, A0, !.Env),
        RawMZ = ann_array_expr(A)
    ;
        RawMZ0 = string_expr(_),
        RawMZ = RawMZ0
    ;
        RawMZ0 = string_array_expr(A0),
        A = fully_deref_string_array(Context, A0, !.Env),
        RawMZ = string_array_expr(A)
    ;
        RawMZ0 = bottom_expr(_),
        RawMZ = RawMZ0
    ;
        % It's not possible to express aliasing in MiniZinc for this case.
        RawMZ0 = bottom_array_expr(_),
        RawMZ = RawMZ0
    ),
    ( if
        RawMZ = string_expr(A1),
        Z0 = format_string_expr_unquoted(A1)
    then
        Z = Z0
    else
        MZ = mzn_expr(RawMZ, Anns0),
        Z = format_mzn_expr(MZ)
    ).

%-----------------------------------------------------------------------------%

flatten_show_int_to_string(Context, MZWidth, MZInt, Z, !Env) :-
    MZWidth = mzn_expr(RawMZWidth, _),
    ( if
        RawMZWidth = int_expr(WidthExpr0),
        simplify_int(Context, WidthExpr0, WidthExpr, !Env),
        WidthExpr = int_const(Width0)
      then
        Width = Width0
      else
        minizinc_user_error(Context,
            "Cannot evaluate width expression.\n")
    ),
    MZInt = mzn_expr(RawMZInt, _),
    ( if
        RawMZInt = int_expr(IntExpr0),
        simplify_int(Context, IntExpr0, IntExpr, !Env)
      then
        (
            IntExpr = int_const(Int),
            Z = string.format("%*d", [i(Width), i(Int)])
        ;
            IntExpr = int_var(Var),
            Z = format_mzn_var(Var)
        ;
            ( IntExpr =  _ + _
            ; IntExpr = _ * _
            ),
            minizinc_internal_error(Context, $pred,
            "unevaluated integer expression for show_int")
        )
      else
        minizinc_internal_error(Context, $pred,
            "unsimplified integer expression for show_int")
    ).

%-----------------------------------------------------------------------------%

flatten_show_float_to_string(Context, MZWidth, MZPrec, MZFloat, Z, !Env) :-
    MZWidth = mzn_expr(RawMZWidth, _),
    ( if
        RawMZWidth = int_expr(WidthExpr0),
        simplify_int(Context, WidthExpr0, WidthExpr, !Env),
        WidthExpr = int_const(Width0)
      then
        Width = Width0
      else
        minizinc_user_error(Context, "Cannot evaluate width expression.\n")
    ),
    MZPrec = mzn_expr(RawMZPrec, _),
    ( if
        RawMZPrec = int_expr(PrecExpr0),
        simplify_int(Context, PrecExpr0, PrecExpr, !Env),
        PrecExpr = int_const(Prec0)
      then
        Prec = Prec0
      else
        minizinc_user_error(Context, "Cannot evaluate precision expression.\n")
    ),
    ( if Prec < 0 then
        minizinc_user_error(Context, "Precision must be non-negative.\n")
      else
        true
    ),
    MZFloat = mzn_expr(RawMZFloat, _),
    ( if
        RawMZFloat = float_expr(FloatExpr0),
        simplify_float(Context, FloatExpr0, FloatExpr, !Env) 
      then
        (
            FloatExpr = float_const(Float),
            Z = string.format("%*.*f", [i(Width), i(Prec), f(Float)])
        ;
            FloatExpr = float_var(Var),
            Z = format_mzn_var(Var) 
        ;
            ( FloatExpr = _ + _
            ; FloatExpr = _ * _
            ),
            minizinc_internal_error(Context, $pred,
                "unevaluated float expression")
        )
      else
        minizinc_internal_error(Context, $pred,
            "unsimplified float expression")
    ).

%-----------------------------------------------------------------------------%

flatten_string_string_to_string(_Context, _Anns, Op, A, B, Z, !Env) :-
    (
        Op = ss2s_append,
        Z = A ++ B
    ).

%-----------------------------------------------------------------------------%

flatten_string_string_to_bool(_Context, _Anns, Op, A, B, BoolZ, !Env) :-
    StrA = format_string_expr(A),
    StrB = format_string_expr(B),
    compare(Result, StrA, StrB),
    ( Op = ss2b_eq, BoolZ = ( if Result = (=)  then yes else no )
    ; Op = ss2b_ee, BoolZ = ( if Result = (=)  then yes else no )
    ; Op = ss2b_ne, BoolZ = ( if Result \= (=) then yes else no )
    ; Op = ss2b_lt, BoolZ = ( if Result = (<)  then yes else no )
    ; Op = ss2b_le, BoolZ = ( if Result \= (>) then yes else no )
    ; Op = ss2b_gt, BoolZ = ( if Result = (>)  then yes else no )
    ; Op = ss2b_ge, BoolZ = ( if Result \= (<) then yes else no )
    ).

%-----------------------------------------------------------------------------%
:- end_module flatten.string.
%-----------------------------------------------------------------------------%
