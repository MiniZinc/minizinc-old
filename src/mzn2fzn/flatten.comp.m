%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2009 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Ralph Becket <rafe@csse.unimelb.edu.au>
%
% Flattening comprehensions.
%
%-----------------------------------------------------------------------------%

:- module flatten.comp.
:- interface.

:- import_module errors.
:- import_module flatten.env.
:- import_module types.

:- import_module types_and_insts.
:- import_module zinc_ast.

:- import_module maybe.

%-----------------------------------------------------------------------------%

    % Flatten a comprehension into a list of mzn_exprs.
    %
:- pred flatten_comp(error_context::in, type_inst::in,
    comprehension_kind::in, generators::in, maybe(expr)::in, mzn_expr::out,
    env::in, env::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module common_array.
:- import_module flatten.array.
:- import_module flatten.expr.

:- import_module array.
:- import_module bool.
:- import_module list.
:- import_module string.

%-----------------------------------------------------------------------------%

flatten_comp(Context, TI, CompKind, Generators, MaybeCondExpr, MZ, !Env) :-
    % Each generator variable is a local. We need to restore the state
    % of the locals after evaluating the comprehension. We evaluate
    % the comprehension in reverse order, then reverse the resulting
    % list of mzn_exprs.

    CompContext = [["In comprehension.\n"] | Context],
    OldLocals = !.Env ^ locals,
    type_inst_to_mzn_type(CompContext, TI, _VarPar, MZType),
    (
        CompKind = simple_array_comp(HeadExpr),
        ( if
            % In these switches, we can't just construct higher order
            % values for the "unpacking" and "packing" functions and
            % then call them in one place after the switch, since
            % each disjunct would then produce an output with a different
            % type.
            (
                MZType = mzn_bool_array,
                flatten_generators(CompContext, Generators, MaybeCondExpr,
                    HeadExpr, [], RevMZs, !Env),
                list.reverse(RevMZs, MZs),
                list.foldl(mzn_expr_to_bool_acc(CompContext), MZs, [], RevYs),
                list.reverse(RevYs, Ys),
                MZ0 = bool_array_to_mzn_expr(list_to_array_expr(Ys))
            ;
                MZType = mzn_float_array(_),
                flatten_generators(CompContext, Generators, MaybeCondExpr,
                    HeadExpr, [], RevMZs, !Env),
                list.reverse(RevMZs, MZs),
                list.foldl(mzn_expr_to_float_acc(CompContext), MZs, [], RevYs),
                list.reverse(RevYs, Ys),
                MZ0 = float_array_to_mzn_expr(list_to_array_expr(Ys))
            ;
                MZType = mzn_int_array(_),
                flatten_generators(CompContext, Generators, MaybeCondExpr,
                    HeadExpr, [], RevMZs, !Env),
                list.reverse(RevMZs, MZs),
                list.foldl(mzn_expr_to_int_acc(CompContext), MZs, [], RevYs),
                list.reverse(RevYs, Ys),
                MZ0 = int_array_to_mzn_expr(list_to_array_expr(Ys))
            ;
                MZType = mzn_bool_set_array,
                flatten_generators(CompContext, Generators, MaybeCondExpr,
                    HeadExpr, [], RevMZs, !Env),
                list.reverse(RevMZs, MZs),
                list.foldl(mzn_expr_to_bool_set_acc(CompContext), MZs,
                    [], RevYs),
                list.reverse(RevYs, Ys),
                MZ0 = bool_set_array_to_mzn_expr(list_to_array_expr(Ys))
            ;
                MZType = mzn_float_set_array(_),
                flatten_generators(CompContext, Generators, MaybeCondExpr,
                    HeadExpr, [], RevMZs, !Env),
                list.reverse(RevMZs, MZs),
                list.foldl(mzn_expr_to_float_set_acc(CompContext), MZs,
                    [], RevYs),
                list.reverse(RevYs, Ys),
                MZ0 = float_set_array_to_mzn_expr(list_to_array_expr(Ys))
            ;
                MZType = mzn_int_set_array(_),
                flatten_generators(CompContext, Generators, MaybeCondExpr,
                    HeadExpr, [], RevMZs, !Env),
                list.reverse(RevMZs, MZs),
                list.foldl(mzn_expr_to_int_set_acc(CompContext), MZs,
                    [], RevYs),
                list.reverse(RevYs, Ys),
                MZ0 = int_set_array_to_mzn_expr(list_to_array_expr(Ys))
            ;
                MZType = mzn_string_array,
                flatten_generators(CompContext, Generators, MaybeCondExpr,
                    HeadExpr, [], RevMZs, !Env),
                list.reverse(RevMZs, MZs),
                list.foldl(mzn_expr_to_string_acc(CompContext), MZs,
                    [], RevYs),
                list.reverse(RevYs, Ys),
                MZ0 = string_array_to_mzn_expr(list_to_array_expr(Ys))
            ;
                MZType = mzn_ann_array,
                flatten_generators(CompContext, Generators, MaybeCondExpr,
                    HeadExpr, [], RevMZs, !Env),
                list.reverse(RevMZs, MZs),
                list.foldl(mzn_expr_to_ann_acc(CompContext), MZs, [], RevYs),
                list.reverse(RevYs, Ys),
                MZ0 = ann_array_to_mzn_expr(list_to_array_expr(Ys))
            )
        then
            MZ = MZ0
        else
            minizinc_user_error(CompContext, "Invalid array type.\n")
        )
    ;
        CompKind = set_comp(HeadExpr),
        ( if
            (
                MZType = mzn_bool_array,
                flatten_generators(CompContext, Generators, MaybeCondExpr,
                    HeadExpr, [], RevMZs, !Env),
                Ys = list.map(mzn_expr_to_bool_const(CompContext), RevMZs),
                MZ0 = bool_set_to_mzn_expr(list_to_set_expr(Ys))
            ;
                MZType = mzn_float_set(_),
                flatten_generators(CompContext, Generators, MaybeCondExpr,
                    HeadExpr, [], RevMZs, !Env),
                Ys = list.map(mzn_expr_to_float_const(CompContext), RevMZs),
                MZ0 = float_set_to_mzn_expr(list_to_set_expr(Ys))
            ;
                MZType = mzn_int_set(_),
                flatten_generators(CompContext, Generators, MaybeCondExpr,
                    HeadExpr, [], RevMZs, !Env),
                Ys = list.map(mzn_expr_to_int_const(CompContext), RevMZs),
                MZ0 = int_set_to_mzn_expr(list_to_set_expr(Ys))
            )
        then
            MZ = MZ0
        else
            minizinc_user_error(CompContext,
                "Invalid set type.\n")
        )
    ),
    % Restore the locals to those of the enclosing scope.
    !Env ^ locals := OldLocals.

%-----------------------------------------------------------------------------%

    % Each generator is a list of generator variables and an array or set
    % expression.
    %
    % If we are at the end of the generators, we can test the condition
    %
:- pred flatten_generators(error_context::in, generators::in,
    maybe(expr)::in, expr::in, mzn_exprs::in, mzn_exprs::out,
    env::in, env::out) is det.

flatten_generators(Context, [], MaybeCondExpr, HeadExpr, !RevMZs, !Env) :-
    ( if
        (
            MaybeCondExpr = no
        ;
            MaybeCondExpr = yes(CondExpr),
            CondContext = [["In comprehension condition.\n"] | Context],
            flatten_expr_must_reify(CondContext, CondExpr, CondMZ, !Env),
            Cond = mzn_expr_to_bool(CondContext, CondMZ),
            ( if Cond = bool_const(BCond) then
                BCond = yes
            else
                minizinc_user_error(CondContext,
                    "Condition is variable, not fixed.\n")
            )
        )
    then
        HeadExprContext = [["In comprehension head.\n"] | Context],
        flatten_expr(HeadExprContext, HeadExpr, HeadMZ, !Env),
        list.cons(HeadMZ, !RevMZs)
    else
        true
    ).
flatten_generators(Context, [Generator | Generators], MaybeCondExpr,
        HeadExpr, !RevMZs, !Env) :-
    Generator = generator(Vars, GenExpr),
    flatten_expr(Context, GenExpr, GenMZ, !Env),
    GenMZ = mzn_expr(RawGenMZ, _GenAnns),
    (
        RawGenMZ = bool_array_expr(A0),
        A = fully_deref_bool_array(Context, A0, !.Env),
        MZArray = array_items_to_mzn_exprs(Context, bool_to_mzn_expr, A)
    ;
        RawGenMZ = float_array_expr(A0),
        A = fully_deref_float_array(Context, A0, !.Env),
        MZArray = array_items_to_mzn_exprs(Context, float_to_mzn_expr, A)
    ;
        RawGenMZ = int_array_expr(A0),
        A = fully_deref_int_array(Context, A0, !.Env),
        MZArray = array_items_to_mzn_exprs(Context, int_to_mzn_expr, A)
    ;
        RawGenMZ = string_array_expr(A0),
        A = fully_deref_string_array(Context, A0, !.Env),
        MZArray = array_items_to_mzn_exprs(Context, string_to_mzn_expr, A) 
    ;
        RawGenMZ = bool_set_array_expr(A0),
        A = fully_deref_bool_set_array(Context, A0, !.Env),
        MZArray = array_items_to_mzn_exprs(Context, bool_set_to_mzn_expr, A)
    ;
        RawGenMZ = float_set_array_expr(A0),
        A = fully_deref_float_set_array(Context, A0, !.Env),
        MZArray = array_items_to_mzn_exprs(Context, float_set_to_mzn_expr, A)
    ;
        RawGenMZ = int_set_array_expr(A0),
        A = fully_deref_int_set_array(Context, A0, !.Env),
        MZArray = array_items_to_mzn_exprs(Context, int_set_to_mzn_expr, A)
    ;
        ( RawGenMZ = bool_expr(_)
        ; RawGenMZ = float_expr(_)
        ; RawGenMZ = int_expr(_)
        ; RawGenMZ = bool_set_expr(_)
        ; RawGenMZ = float_set_expr(_)
        ; RawGenMZ = int_set_expr(_)
        ; RawGenMZ = string_expr(_)
        ; RawGenMZ = ann_expr(_)
        ; RawGenMZ = ann_array_expr(_)
        ; RawGenMZ = bottom_expr(_)
        ; RawGenMZ = bottom_array_expr(_)
        ),
        minizinc_user_error(Context,
            "Generator expression of this type is not valid MiniZinc.\n")
    ),
    MZs = array.to_list(MZArray),
    flatten_generator_vars(Context, Vars, MZs, Generators, MaybeCondExpr,
        HeadExpr, !RevMZs, !Env).

%-----------------------------------------------------------------------------%

:- pred flatten_generator_vars(error_context::in, list(var_id)::in,
    mzn_exprs::in, generators::in, maybe(expr)::in, expr::in,
    mzn_exprs::in, mzn_exprs::out, env::in, env::out) is det.

flatten_generator_vars(Context, [], _MZs, Generators, MaybeCondExpr, HeadExpr,
        !RevMZs, !Env) :-
    flatten_generators(Context, Generators, MaybeCondExpr, HeadExpr,
        !RevMZs, !Env).
flatten_generator_vars(Context, [Var | Vars], MZs, Generators, MaybeCondExpr,
        HeadExpr, !RevMZs, !Env) :-
    flatten_generator_var(Context, Var, MZs, Vars, MZs, Generators,
        MaybeCondExpr, HeadExpr, !RevMZs, !Env).

%-----------------------------------------------------------------------------%

:- pred flatten_generator_var(error_context::in, var_id::in, mzn_exprs::in,
    list(var_id)::in, mzn_exprs::in, generators::in, maybe(expr)::in,
    expr::in, mzn_exprs::in, mzn_exprs::out, env::in, env::out) is det.

flatten_generator_var(_Context, _VarId, [], _VarIds, _MZs, _Generators,
        _MaybeCondExpr, _HeadExpr, !RevMZs, !Env).
flatten_generator_var(Context, VarId, [VarMZ | VarMZs], VarIds, MZs,
        Generators, MaybeCondExpr, HeadExpr, !RevMZs, !Env) :-
    add_local_var(VarId, VarMZ, !Env),
    ( if VarMZ = mzn_expr(int_expr(int_const(I)), _) then
        % It is useful to include integer generator variables in the error
        % context, since these are often used as array indices.
        VarName = var_name(VarId),
        VarContext =
            [[VarName, " = ", string.int_to_string(I), "\n"] | Context]
    else
        VarContext = Context
    ),
    flatten_generator_vars(VarContext, VarIds, MZs, Generators,
        MaybeCondExpr, HeadExpr, !RevMZs, !Env),
    flatten_generator_var(Context, VarId, VarMZs, VarIds, MZs, Generators,
        MaybeCondExpr, HeadExpr, !RevMZs, !Env).

%-----------------------------------------------------------------------------%
:- end_module flatten.comp.
%-----------------------------------------------------------------------------%
