%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2009,2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Ralph Becket <rafe@csse.unimelb.edu.au>
%
% A representation of MiniZinc annotations.
%
%-----------------------------------------------------------------------------%

:- module flatten.ann.
:- interface.

:- import_module errors.
:- import_module flatten.env.
:- import_module types.

:- import_module zinc_ast.

%-----------------------------------------------------------------------------%

    % NB This predicate will remove any 'null' annotations in the set.
    %
:- pred flatten_anns(error_context::in, exprs::in, mzn_anns::out,
    env::in, env::out) is det.

    % XXX Need to support assignment for anns!
    %
:- pred flatten_ann_ann_to_bool(error_context::in, mzn_anns::in,
    string::in, mzn_ann::in, mzn_ann::in,
    bool_expr::out, env::in, env::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module flatten.expr.

:- import_module zinc_common.

:- import_module bool.
:- import_module list.
:- import_module set.

%-----------------------------------------------------------------------------%

flatten_anns(_Context, [], Anns, !Env) :-
    Anns = no_anns.
flatten_anns(Context, AnnExprs @ [_ | _], Anns, !Env) :-
    list.map_foldl(flatten_expr(Context), AnnExprs, MZs, !Env),
    Anns0 = set.from_list(list.map(mzn_expr_to_ann(Context), MZs)),
    Anns1 = set.union_list(list.map(mzn_expr_anns, MZs)),
    Anns2 = join_anns(Anns0, Anns1),
    Anns  = set.delete(Anns2, null_ann).

:- func mzn_expr_anns(mzn_expr) = mzn_anns.

mzn_expr_anns(mzn_expr(_, Anns)) = Anns.

%-----------------------------------------------------------------------------%

flatten_ann_ann_to_bool(Context, _Anns, Op, A, B, bool_const(yes), !Env) :-
    ( if
        ( Op = "="
        ; Op = "=="
        )
    then
        (
            A = mzn_ann(_, _),
            B = mzn_ann(_, _),
            VarId = id_global("Dummy"),
            C = A, % Dummy
            Okay = no
        ;
            A = mzn_ann(_, _),
            B = mzn_ann_var(MZVarA),
            VarId = mzn_var_id(MZVarA),
            C = A,
            Okay = ( if !.Env ^ var_value(VarId) = _ then no else yes )
        ;
            A = mzn_ann_var(MZVarA),
            B = mzn_ann(_, _),
            VarId = mzn_var_id(MZVarA),
            C = B,
            Okay = ( if !.Env ^ var_value(VarId) = _ then no else yes )
        ;
            A = mzn_ann_var(MZVarA),
            B = mzn_ann_var(MZVarB),
            VarIdA = mzn_var_id(MZVarA),
            VarIdB = mzn_var_id(MZVarB),
            ( if
                not !.Env ^ var_value(VarIdA) = _,
                !.Env ^ var_value(VarIdB) = C0
            then
                VarId = VarIdA,
                C = mzn_expr_to_ann(Context, C0),
                Okay = yes
            else if
                !.Env ^ var_value(VarIdA) = C0,
                not !.Env ^ var_value(VarIdB) = _
            then
                VarId = VarIdB,
                C = mzn_expr_to_ann(Context, C0),
                Okay = yes
            else
                VarId = id_global("Dummy"),
                C = A, % Dummy
                Okay = no
            )
        ),
        (
            Okay = no,
            minizinc_user_error(Context,
                "Comparison of annotations is not supported.\n")
        ;
            Okay = yes,
            !Env ^ var_value(VarId) := ann_to_mzn_expr(C)
        )
    else
        minizinc_user_error(Context,
            "Assignment is the only supported annotation operation.\n")
    ).

%-----------------------------------------------------------------------------%
:- end_module flatten.ann.
%-----------------------------------------------------------------------------%
