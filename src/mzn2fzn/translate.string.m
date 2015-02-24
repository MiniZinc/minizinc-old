%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
%-----------------------------------------------------------------------------%

:- module translate.string.
:- interface.

:- import_module error_util.
:- import_module tmzn_ast.
:- import_module translate.info.

:- import_module list.
:- import_module maybe.

:- pred is_string_const_expr(tr_info::in, tmzn_string_expr::in,
    maybe(string)::out,
    list(error_spec)::in, list(error_spec)::out) is det.

%-----------------------------------------------------------------------------%

:- implementation.

:- import_module translate.bool.
:- import_module mzn_ops.

:- import_module bool.
:- import_module string.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

is_string_const_expr(Info, TMznStrExpr, MaybeStrConst, !Specs) :-
    % XXX should switch on TMznStrExpr
    (
        TMznStrExpr = tmzn_string_expr_const(_SL, StrConst),
        MaybeStrConst = yes(StrConst)
    ;
        TMznStrExpr = tmzn_string_expr_var(_SL, _),
        % XXX Constraints may have already determined the value
        % of the variable.
        MaybeStrConst = no
    ;
        TMznStrExpr = tmzn_string_expr_ss2s(_SL, SS2SOp, TMznStrA, TMznStrB),
        is_string_const_expr(Info, TMznStrA, MaybeStrConstA, !Specs),
        is_string_const_expr(Info, TMznStrB, MaybeStrConstB, !Specs),
        ( if
            MaybeStrConstA = yes(StrConstA),
            MaybeStrConstB = yes(StrConstB)
        then
            translate_par_string_par_string_to_string(SS2SOp,
                StrConstA, StrConstB, StrConst),
            MaybeStrConst = yes(StrConst)
        else
            MaybeStrConst = no
        )
    ;
        ( TMznStrExpr = tmzn_string_expr_x2s(_, _, _)
        ; TMznStrExpr = tmzn_string_expr_ii2s(_, _, _, _)
        ; TMznStrExpr = tmzn_string_expr_iif2s(_, _, _, _, _)
        ; TMznStrExpr = tmzn_string_expr_sa2s(_, _, _)
        ; TMznStrExpr = tmzn_string_expr_ssa2s(_, _, _, _)
        ),
        % XXX Can we do better?
        MaybeStrConst = no
    ;
        TMznStrExpr = tmzn_string_expr_ite(_SL, TMznCondExpr,
            TMznThenExpr, TMznElseExpr),
        is_bool_const_expr(Info, TMznCondExpr, MaybeCondConst, !Specs),
        ( if
            MaybeCondConst = yes(CondConst)
        then
            (
                CondConst = yes,
                is_string_const_expr(Info, TMznThenExpr, MaybeThenConst,
                    !Specs),
                MaybeStrConst = MaybeThenConst
            ;
                CondConst = no,
                is_string_const_expr(Info, TMznElseExpr, MaybeElseConst,
                    !Specs),
                MaybeStrConst = MaybeElseConst
            )
        else
            MaybeStrConst = no
        )
    ).

:- pred translate_par_string_par_string_to_string(
    string_string_to_string_op::in, string::in, string::in, string::out)
    is det.

translate_par_string_par_string_to_string(SS2SOp, StrA, StrB, Str) :-
    (
        SS2SOp = ss2s_append,
        Str = StrA ++ StrB
    ).

%-----------------------------------------------------------------------------%
:- end_module translate.string.
%-----------------------------------------------------------------------------%
