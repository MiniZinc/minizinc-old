
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs
%
% Code to convert to and from the data structures used by the flatten package.
%
%-----------------------------------------------------------------------------%

:- module hr.convert.
:- interface.

:- import_module errors.
:- import_module types.
:- import_module hr.info.
:- import_module mzn_ops.

:- import_module types_and_insts.
:- import_module zinc_ast.

:- import_module list.

%-----------------------------------------------------------------------------%
% flatten.ann.m.

:- pred hr_flatten_anns(error_context::in, mzn_anns::in, ilhs::in,
    exprs::in, mzn_anns::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

%-----------------------------------------------------------------------------%
% flatten.app.m.

:- pred hr_flatten_predicate(error_context::in, mzn_anns::in, ilhs::in,
    string::in, int::in, list(mzn_expr)::in, mzn_anns::in, bool_expr::out,
    mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

%-----------------------------------------------------------------------------%
% flatten.bool.m.

:- pred hr_simplify_bool_cv(error_context::in, mzn_anns::in, ilhs::in,
    bool_expr::in, bool_const_or_var::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

:- pred hr_flatten_bool_bool_to_bool(error_context::in, mzn_anns::in, ilhs::in,
    bool_bool_to_bool_op::in, bool_expr::in, bool_expr::in, bool_expr::out,
    mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is semidet.

%-----------------------------------------------------------------------------%
% flatten.env.m.

:- pred hr_flatten_ti_expr(error_context::in, mzn_anns::in, ilhs::in,
    ti_expr::in, var_par::out, mzn_type::out, index_ranges::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

%-----------------------------------------------------------------------------%
% flatten.expr.m.

:- pred hr_flatten_expr(error_context::in, mzn_anns::in, ilhs::in,
    expr::in, mzn_expr::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

:- pred hr_flatten_expr_must_reify(error_context::in, mzn_anns::in,
    expr::in, mzn_expr::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

:- pred hr_flatten_builtin(error_context::in, mzn_anns::in, ilhs::in,
    string::in, list(mzn_expr)::in, mzn_expr::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is semidet.

:- pred hr_flatten_coerce(error_context::in, mzn_anns::in, ilhs::in,
    type_inst::in, type_inst::in, expr::in, mzn_expr::out,
    mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

%-----------------------------------------------------------------------------%
% flatten.float.m.

:- pred hr_simplify_float(error_context::in, mzn_anns::in, ilhs::in,
    float_expr::in, float_expr::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

%-----------------------------------------------------------------------------%
% flatten.int.m.

% :- pred hr_simplify_int(error_context::in, mzn_anns::in, ilhs::in,
%     int_expr::in, int_expr::out, mzn_constraint_set::out,
%     hr_info::in, hr_info::out, model::in, model::out) is det.

%-----------------------------------------------------------------------------%
% flatten.let.m.

:- pred hr_flatten_let_expr(error_context::in, mzn_anns::in, ilhs::in,
    local_vars::in, expr::in, mzn_expr::out, mzn_constraint_set::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

%-----------------------------------------------------------------------------%

:- implementation.

:- import_module flatten.
:- import_module flatten.ann.
:- import_module flatten.app.
:- import_module flatten.bool.
:- import_module flatten.env.
:- import_module flatten.expr.
:- import_module flatten.float.
:- import_module flatten.int.
:- import_module flatten.let.
:- import_module flatten.string.
:- import_module global_vars.

:- import_module bool.
:- import_module counter.
:- import_module map.
:- import_module maybe.
:- import_module string.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
%
% Forwarding predicates to the flatten package.
%

%-----------------------------------------------------------------------------%
% flatten.ann.m.

hr_flatten_anns(Context, OutsideAnns, ILHS, VarAnnExprs, Anns,
        !Info, !Model) :-
    (
        ILHS = ilhs_true,
        hr_info_model_to_env_not_reified(OutsideAnns, !.Info, !.Model, Env0),
        flatten_anns(Context, VarAnnExprs, Anns, Env0, Env),
        env_to_hr_info_model_not_reified(Env, OutsideAnns, !:Info, !:Model)
    ;
        ILHS = ilhs_var(_),
        hr_info_model_to_env_reified(OutsideAnns, !.Info, !.Model, Env0),
        flatten_anns(Context, VarAnnExprs, Anns, Env0, Env),
        env_to_hr_info_model_reified(Env, OutsideAnns, !:Info, !:Model,
            MaybeReifVar),
        (
            MaybeReifVar = no
        ;
            MaybeReifVar = yes(_),
            minizinc_internal_error([], $pred, "MaybeReifVar = yes.\n")
        )
    ).

%-----------------------------------------------------------------------------%
% flatten.app.m.

hr_flatten_predicate(Context, OutsideAnns, ILHS, PredName, ProcNum,
        Args, PredAnns, Z, AllConstraints, !Info, !Model) :-
    (
        ILHS = ilhs_true,
        hr_info_model_to_env_not_reified(OutsideAnns, !.Info, !.Model, Env0),
        flatten_predicate(Context, PredName, ProcNum, Args, PredAnns, Z,
            Env0, Env),
        env_to_hr_info_model_not_reified(Env, OutsideAnns, !:Info, !:Model),
        diff_constraints_in_envs(Env0, Env, AllConstraints)
    ;
        ILHS = ilhs_var(_),
        minizinc_internal_error([], $pred, "ilhs_var NYI.\n")
    ).

%-----------------------------------------------------------------------------%
% flatten.bool.m.

hr_simplify_bool_cv(Context, OutsideAnns, ILHS, Z, CVZ, AllConstraints,
        !Info, !Model) :-
    (
        ILHS = ilhs_true,
        hr_info_model_to_env_not_reified(OutsideAnns, !.Info, !.Model, Env0),
        simplify_bool_cv(Context, Z, CVZ, Env0, Env),
        env_to_hr_info_model_not_reified(Env, OutsideAnns, !:Info, !:Model),
        diff_constraints_in_envs(Env0, Env, AllConstraints)
    ;
        ILHS = ilhs_var(_),
        minizinc_internal_error([], $pred, "ilhs_var NYI.\n")
    ).

hr_flatten_bool_bool_to_bool(Context, Anns, ILHS, Op, A, B, Z, AllConstraints,
        !Info, !Model) :-
    % XXX flatten_bool_bool_to_bool has anns both as explicit args
    % and inside Env0.
    (
        ILHS = ilhs_true,
        hr_info_model_to_env_not_reified(Anns, !.Info, !.Model, Env0),
        flatten_bool_bool_to_bool(Context, Anns, Op, A, B, Z, Env0, Env),
        env_to_hr_info_model_not_reified(Env, Anns, !:Info, !:Model),
        diff_constraints_in_envs(Env0, Env, AllConstraints)
    ;
        ILHS = ilhs_var(_),
        minizinc_internal_error([], $pred, "ilhs_var NYI.\n")
    ).

%-----------------------------------------------------------------------------%
% flatten.env.m.

hr_flatten_ti_expr(Context, OutsideAnns, ILHS, TIExpr,
        VarPar, MZType, IndexRanges, !Info, !Model) :-
    (
        ILHS = ilhs_true,
        hr_info_model_to_env_not_reified(OutsideAnns, !.Info, !.Model, Env0),
        flatten_ti_expr(Context, TIExpr, VarPar, MZType, IndexRanges,
            Env0, Env),
        env_to_hr_info_model_not_reified(Env, OutsideAnns, !:Info, !:Model),
        diff_constraints_in_envs(Env0, Env, AllConstraints),
        minizinc_require(Context, mzn_constraint_set_is_empty(AllConstraints),
            $pred, "constraint set not empty")
    ;
        ILHS = ilhs_var(_),
        minizinc_internal_error([], $pred, "ilhs_var NYI")
    ).

%-----------------------------------------------------------------------------%
% flatten.expr.m.

hr_flatten_expr(Context, OutsideAnns, ILHS, Expr, MZExpr, AllConstraints,
        !Info, !Model) :-
    (
        ILHS = ilhs_true,
        hr_info_model_to_env_not_reified(OutsideAnns, !.Info, !.Model, Env0),
        flatten_expr(Context, Expr, MZExpr, Env0, Env),
        env_to_hr_info_model_not_reified(Env, OutsideAnns, !:Info, !:Model),
        diff_constraints_in_envs(Env0, Env, AllConstraints)
    ;
        ILHS = ilhs_var(_),
        minizinc_internal_error([], $pred, "ilhs_var NYI")
    ).

hr_flatten_expr_must_reify(Context, OutsideAnns, Expr, MZExpr, AllConstraints,
        !Info, !Model) :-
    % XXX The code in flatten.expr.m conjoins MZExpr with the current list of
    % reifying expressions. In the hr package, this task is up to the caller.
    hr_info_model_to_env_not_reified(OutsideAnns, !.Info, !.Model, Env0),
    flatten_expr_must_reify(Context, Expr, MZExpr, Env0, Env),
    env_to_hr_info_model_not_reified(Env, OutsideAnns, !:Info, !:Model),
    diff_constraints_in_envs(Env0, Env, AllConstraints).

hr_flatten_builtin(Context, OutsideAnns, ILHS, Op, Args, MZ, AllConstraints,
        !Info, !Model) :-
    (
        ILHS = ilhs_true,
        hr_info_model_to_env_not_reified(OutsideAnns, !.Info, !.Model, Env0),
        flatten_builtin(Context, Op, Args, MZ, Env0, Env),
        env_to_hr_info_model_not_reified(Env, OutsideAnns, !:Info, !:Model),
        diff_constraints_in_envs(Env0, Env, AllConstraints)
    ;
        ILHS = ilhs_var(_),
        minizinc_internal_error([], $pred, "ilhs_var NYI")
    ).

hr_flatten_coerce(Context, OutsideAnns, ILHS, TIFrom, TITo, Expr, MZ,
        AllConstraints, !Info, !Model) :-
    (
        ILHS = ilhs_true,
        hr_info_model_to_env_not_reified(OutsideAnns, !.Info, !.Model, Env0),
        flatten_coerce(Context, TIFrom, TITo, Expr, MZ, Env0, Env),
        env_to_hr_info_model_not_reified(Env, OutsideAnns, !:Info, !:Model),
        diff_constraints_in_envs(Env0, Env, AllConstraints)
    ;
        ILHS = ilhs_var(_),
        minizinc_internal_error([], $pred, "ilhs_var NYI")
    ).

%-----------------------------------------------------------------------------%
% flatten.float.m.

hr_simplify_float(Context, OutsideAnns, ILHS, A, Z, AllConstraints,
        !Info, !Model) :-
    (
        ILHS = ilhs_true,
        hr_info_model_to_env_not_reified(OutsideAnns, !.Info, !.Model, Env0),
        simplify_float(Context, A, Z, Env0, Env),
        env_to_hr_info_model_not_reified(Env, OutsideAnns, !:Info, !:Model),
        diff_constraints_in_envs(Env0, Env, AllConstraints)
    ;
        ILHS = ilhs_var(_),
        minizinc_internal_error([], $pred, "ilhs_var NYI")
    ).

%-----------------------------------------------------------------------------%
% flatten.int.m.

% hr_simplify_int(Context, OutsideAnns, ILHS, A, Z, AllConstraints,
%         !Info, !Model) :-
%     (
%         ILHS = ilhs_true,
%         hr_info_model_to_env_not_reified(OutsideAnns, !.Info, !.Model, Env0),
%         simplify_int(Context, A, Z, Env0, Env),
%         env_to_hr_info_model_not_reified(Env, OutsideAnns, !:Info, !:Model),
%         diff_constraints_in_envs(Env0, Env, AllConstraints)
%     ;
%         ILHS = ilhs_var(_),
%         minizinc_internal_error([], $pred, "ilhs_var NYI")
%     ).

%-----------------------------------------------------------------------------%
% flatten.let.m.

hr_flatten_let_expr(Context, OutsideAnns, ILHS, LetVars, LetExpr, MZ,
        AllConstraints, !Info, !Model) :-
    (
        ILHS = ilhs_true,
        hr_info_model_to_env_not_reified(OutsideAnns, !.Info, !.Model, Env0),
        flatten_let_expr(Context, LetVars, LetExpr, MZ, Env0, Env),
        env_to_hr_info_model_not_reified(Env, OutsideAnns, !:Info, !:Model),
        diff_constraints_in_envs(Env0, Env, AllConstraints)
    ;
        ILHS = ilhs_var(_),
        minizinc_internal_error([], $pred, "ilhs_var NYI")
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
%
% Construct a hr_info and a model from an env.
% This sets up for a forwarding call.
%

:- pred hr_info_model_to_env_not_reified(mzn_anns::in, hr_info::in, model::in,
    env::out) is det.

hr_info_model_to_env_not_reified(Anns, Info, Model, Env) :-
    deconstruct_hr_info(Info, LocalVarMap, TmpVarCounter, CSEMap),
    construct_env(not_reifying, Anns, LocalVarMap, TmpVarCounter, CSEMap,
        Model, Env).

:- pred hr_info_model_to_env_reified(mzn_anns::in, hr_info::in,
    model::in, env::out) is det.

hr_info_model_to_env_reified(Anns, Info, Model, Env) :-
    deconstruct_hr_info(Info, LocalVarMap, TmpVarCounter, CSEMap),
    construct_env(reifying([]), Anns, LocalVarMap, TmpVarCounter, CSEMap,
        Model, Env).

%-----------------------------------------------------------------------------%
%
% Construct an env from a hr_info and a model.
% This processes the result of a forwarding call.
%

:- pred env_to_hr_info_model_not_reified(env::in, mzn_anns::in,
    hr_info::out, model::out) is det.

env_to_hr_info_model_not_reified(Env, Anns, Info, Model) :-
    deconstruct_env(Env, EnvReifying, EnvAnns, LocalVarMap, TmpVarCounter,
        CSEMap, Model),
    (
        EnvReifying = not_reifying,
        ( if Anns = EnvAnns then
            construct_hr_info(LocalVarMap, TmpVarCounter, CSEMap, Info)
        else
            minizinc_internal_error([], $pred,
                "env has different annotations.\n")
        )
    ;
        EnvReifying = reifying(_ : bool_exprs),
        minizinc_internal_error([], $pred,
            "env has reifying.\n")
    ).

:- pred env_to_hr_info_model_reified(env::in, mzn_anns::in,
    hr_info::out, model::out, maybe(mzn_var)::out) is det.

env_to_hr_info_model_reified(Env, Anns, Info, Model, MaybeReifVar) :-
    deconstruct_env(Env, EnvReifying, EnvAnns, LocalVarMap, TmpVarCounter,
        CSEMap, Model),
    (
        EnvReifying = not_reifying,
        minizinc_internal_error([], $pred,
            "env has not_reifying.\n")
    ;
        EnvReifying = reifying(ReifExprs),
        ( if Anns = EnvAnns then
            construct_hr_info(LocalVarMap, TmpVarCounter, CSEMap, Info),
            (
                ReifExprs = [],
                minizinc_internal_error([], $pred,
                    "no reification expression.\n")
            ;
                ReifExprs = [ReifExpr],
                ( if ReifExpr = bool_var(ReifVar) then
                    MaybeReifVar = yes(ReifVar)
                else if ReifExpr = bool_const(no) then
                    MaybeReifVar = no
                else
                    minizinc_internal_error([], $pred,
                        "reification expression of unexpected form.\n")
                )
            ;
                ReifExprs = [_, _ | _],
                minizinc_internal_error([], $pred,
                    "more than one reification expression.\n")
            )
        else
            minizinc_internal_error([], $pred,
                "env has different annotations.\n")
        )
    ).

%-----------------------------------------------------------------------------%
:- end_module hr.convert.
%-----------------------------------------------------------------------------%
