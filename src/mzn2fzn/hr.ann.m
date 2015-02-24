%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
% A representation of MiniZinc annotations.
%
%-----------------------------------------------------------------------------%

:- module hr.ann.
:- interface.

:- import_module errors.
:- import_module hr.info.
:- import_module types.

% :- import_module zinc_ast.

:- import_module list.
:- import_module unit.

%-----------------------------------------------------------------------------%

    % NB This predicate will remove any 'null' annotations in the set.
    %
% :- pred hr_flatten_anns(error_context::in, list(expr)::in, mzn_anns::out,
%     env::in, env::out) is det.

    % XXX Need to support assignment for anns!
    % XXX HR: outside annotations are assumed to be no_anns.
    %
:- pred hr_flatten_ann_ann_to_bool_not_reified(error_context::in,
    string::in, mzn_anns::in, mzn_ann::in, mzn_ann::in, bool_expr::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

    % This just throws an exception.
    %
:- pred hr_add_tmp_ann_var(error_context::in, unit::in,
    string::in, list(mzn_expr)::in, mzn_anns::in, mzn_ann::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

% XXX :- import_module flatten.expr.

:- import_module zinc_common.

:- import_module array.
:- import_module bool.
:- import_module maybe.
:- import_module set.

%-----------------------------------------------------------------------------%

% hr_flatten_anns(_Context, [], Anns, !Info, !Model) :-
%     Anns = no_anns.
% hr_flatten_anns(Context, AnnExprs @ [_ | _], Anns, !Info, !Model) :-
%     list.map_foldl2(hr_flatten_expr(Context), AnnExprs, MZs, !Info, !Model),
%     Anns0 = set.from_list(list.map(mzn_expr_to_ann(Context), MZs)),
%     Anns1 = set.union_list(list.map(mzn_expr_anns, MZs)),
%     Anns2 = join_anns(Anns0, Anns1),
%     Anns  = set.delete(Anns2, null_ann).

% :- func mzn_expr_anns(mzn_expr) = mzn_anns.

% mzn_expr_anns(mzn_expr(_, Anns)) = Anns.

%-----------------------------------------------------------------------------%

hr_flatten_ann_ann_to_bool_not_reified(Context, Op, _Anns, A, B, Z,
        !Info, !Model) :-
    ( if
        ( Op = "="
        ; Op = "=="
        )
    then
        (
            A = mzn_ann(_, _),
            B = mzn_ann(_, _),
            minizinc_user_error(Context,
                "Comparison of annotations is not supported.\n")
        ;
            A = mzn_ann(_, _),
            B = mzn_ann_var(MZVarB),
            VarIdB = mzn_var_id(MZVarB),
            MaybeValueB = hr_get_var_value(!.Info, !.Model, VarIdB),
            (
                MaybeValueB = yes(_),
                minizinc_user_error(Context,
                    "Comparison of annotations is not supported.\n")
            ;
                MaybeValueB = no,
                LHS = VarIdB,
                RHS = A
            )
        ;
            A = mzn_ann_var(MZVarA),
            B = mzn_ann(_, _),
            VarIdA = mzn_var_id(MZVarA),
            MaybeValueA = hr_get_var_value(!.Info, !.Model, VarIdA),
            (
                MaybeValueA = yes(_),
                minizinc_user_error(Context,
                    "Comparison of annotations is not supported.\n")
            ;
                MaybeValueA = no,
                LHS = VarIdA,
                RHS = B
            )
        ;
            A = mzn_ann_var(MZVarA),
            B = mzn_ann_var(MZVarB),
            VarIdA = mzn_var_id(MZVarA),
            VarIdB = mzn_var_id(MZVarB),
            MaybeValueA = hr_get_var_value(!.Info, !.Model, VarIdA),
            MaybeValueB = hr_get_var_value(!.Info, !.Model, VarIdB),
            (
                MaybeValueA = no,
                MaybeValueB = no,
                minizinc_user_error(Context,
                    "Comparison of annotations is not supported.\n")
            ;
                MaybeValueA = no,
                MaybeValueB = yes(ValueB),
                LHS = VarIdA,
                RHS = mzn_expr_to_ann(Context, ValueB)
            ;
                MaybeValueA = yes(ValueA),
                MaybeValueB = no,
                LHS = VarIdA,
                RHS = mzn_expr_to_ann(Context, ValueA)
            ;
                MaybeValueA = yes(_),
                MaybeValueB = yes(_),
                minizinc_user_error(Context,
                    "Comparison of annotations is not supported.\n")
            )
        ),
        hr_set_var_value(LHS, ann_to_mzn_expr(RHS), !Info, !Model),
        Z = bool_const(yes)
    else
        minizinc_user_error(Context,
            "Assignment is the only supported annotation operation.\n")
    ).

%-----------------------------------------------------------------------------%

hr_add_tmp_ann_var(Context, _, _, _, _, Z, !Info, !Model) :-
    ( if semidet_succeed then
        minizinc_internal_error(Context, $pred, "invoked")
      else
        Z = mzn_ann("dummy", [])
    ).

%-----------------------------------------------------------------------------%
:- end_module hr.ann.
%-----------------------------------------------------------------------------%
