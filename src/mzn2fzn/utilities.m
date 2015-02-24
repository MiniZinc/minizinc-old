%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Ralph Becket <rafe@csse.unimelb.edu.au>
%
% Utility predicates.
%
%-----------------------------------------------------------------------------%

:- module utilities.
:- interface.

:- import_module types.

:- import_module zinc_ast.

:- import_module set.

%-----------------------------------------------------------------------------%

    % Extract the set of global variables reachable from an output expression.
    % The resulting set is used to annotate variables in the generated FlatZinc
    % with output_var/0 or output_array/1 annotations.
    %
:- func global_vars_in_output_expr(model, expr) = set(var_id).

    % Extract the set of global variables in an mzn_expr.
    %
:- func vars_in_mzn_expr(mzn_expr) = set(var_id).

%-----------------------------------------------------------------------------%

:- implementation.

:- import_module errors.
:- import_module zinc_common.

:- import_module array.
:- import_module list.
:- import_module map.
:- import_module maybe.

%-----------------------------------------------------------------------------%

global_vars_in_output_expr(Model, Expr) = !:VarSet :-
    set.init(!:VarSet),
    global_vars_in_output_expr(Model, Expr, !VarSet).

vars_in_mzn_expr(MZ) = !:VarSet :-
    set.init(!:VarSet),
    add_vars_in_mzn_expr(MZ, !VarSet).

%-----------------------------------------------------------------------------%

:- pred global_vars_in_output_expr(model::in, expr::in,
    set(var_id)::in, set(var_id)::out) is det.

global_vars_in_output_expr(Model, Expr, !VarSet) :-
    Expr = expr(RawExpr, _Anns, _ExprInfo),
    global_vars_in_raw_expr(Model, RawExpr, !VarSet).

:- pred global_vars_in_output_exprs(model::in, list(expr)::in,
    set(var_id)::in, set(var_id)::out) is det.

global_vars_in_output_exprs(_Model, [], !VarSet).
global_vars_in_output_exprs(Model, [Expr | Exprs], !VarSet) :-
    global_vars_in_output_expr(Model, Expr, !VarSet),
    global_vars_in_output_exprs(Model, Exprs, !VarSet).

%-----------------------------------------------------------------------------%

:- pred global_vars_in_raw_expr(model::in, raw_expr::in,
    set(var_id)::in, set(var_id)::out) is det.

global_vars_in_raw_expr(Model, RawExpr, !VarSet) :-
    (
        RawExpr = ident(VarId),
        ( if
            GlobalVarMap = Model ^ model_globals,
            map.search(GlobalVarMap, VarId, VarInfo),
            VarInfo ^ vi_inst = var_is_var
        then
            set.insert(VarId, !VarSet)
        else
            true
        )
    ;
        ( RawExpr = lit(_)
        ; RawExpr = lit_ann(_, _)
        ; RawExpr = anon_var
        )
    ;
        RawExpr = app(AppId, AppProcN, AppKind, AppArgExprs),
        global_vars_in_output_exprs(Model, AppArgExprs, !VarSet),
        (
            ( AppKind = gen_call_app
            ; AppKind = array2d_literal
            ; AppKind = operator_app
            )
        ;
            AppKind = predfunc_app,
            PredInfos = Model ^ model_pred_map,
            PPId = pred_proc_id(AppId ^ id_name, AppProcN),
            ( if map.search(PredInfos, PPId, PredInfo) then
                PredInfo = predicate_info(_Params, _Anns, MaybeBody),
                (
                    MaybeBody = no
                    % XXX this should probably be an error, but the frontned
                    % should check for it; as it is solns2out will abort if
                    % encounters a bodyless predicate / test in the output
                    % item.
                ;
                    MaybeBody = yes(BodyExpr),
                    global_vars_in_output_expr(Model, BodyExpr, !VarSet)
                )
              else
                % If the operation was not in the predicate map then it's
                % a built-in.
                true
            )
        )
    ;
        ( RawExpr = lit_set(Exprs)
        ; RawExpr = lit_simple_array(Exprs)
        ),
        global_vars_in_output_exprs(Model, Exprs, !VarSet)
    ;
        RawExpr = array_access(ArrayExpr, IndexExprs),
        global_vars_in_output_expr(Model, ArrayExpr, !VarSet),
        global_vars_in_output_exprs(Model, IndexExprs, !VarSet)
    ;
        RawExpr = lit_tuple(_),
        minizinc_internal_error([["In output item.\n"]], $pred,
            "non-MiniZinc expression.")
    ;
        RawExpr = comprehension(CompKind, Generators, MaybeWhereExpr),
        ( CompKind = set_comp(Expr)
        ; CompKind = simple_array_comp(Expr)
        ),
        global_vars_in_output_expr(Model, Expr, !VarSet),
        (
            MaybeWhereExpr = yes(WhereExpr),
            global_vars_in_output_expr(Model, WhereExpr, !VarSet)
        ;
            MaybeWhereExpr = no
        ),
        F = (func(generator(_Id, GeneratorExpr)) = GeneratorExpr),
        GeneratorExprs = list.map(F, Generators),
        global_vars_in_output_exprs(Model, GeneratorExprs, !VarSet)
    ;
        RawExpr = if_then_else(CondExpr, ThenExpr, ElseExpr),
        global_vars_in_output_expr(Model, CondExpr, !VarSet),
        global_vars_in_output_expr(Model, ThenExpr, !VarSet),
        global_vars_in_output_expr(Model, ElseExpr, !VarSet)
    ;
        RawExpr = let(LetVars, Expr),
        list.foldl(global_vars_in_local_var(Model), LetVars, !VarSet),
        global_vars_in_output_expr(Model, Expr, !VarSet)
    ;
        RawExpr = coerce(_, _, Expr),
        global_vars_in_output_expr(Model, Expr, !VarSet)
    ).

:- pred global_vars_in_local_var(model::in, local_var::in,
    set(var_id)::in, set(var_id)::out) is det.

global_vars_in_local_var(Model, LocalVar, !VarSet) :-
    % Let variables have local scope so we don't need to consider them
    % directly.  If assigned, then their assignments may contain references to
    % global variables however, so we need to examine them.
    LocalVar = local_var(_TIExpr, _Id, _AnnEs, MaybeInit),
    (
        MaybeInit = yes(Expr),
        global_vars_in_output_expr(Model, Expr, !VarSet)
    ;
        MaybeInit = no
    ).

%-----------------------------------------------------------------------------%
%
% Accumulate vars in MiniZinc expressions.
%

:- pred add_vars_in_mzn_expr(mzn_expr::in, set(var_id)::in, set(var_id)::out)
    is det.

add_vars_in_mzn_expr(mzn_expr(RawMZ, Anns), !VarSet) :-
    add_vars_in_mzn_raw_expr(RawMZ, !VarSet),
    set.fold(add_vars_in_ann_expr, Anns, !VarSet).

:- pred add_vars_in_mzn_raw_expr(mzn_raw_expr::in,
    set(var_id)::in, set(var_id)::out) is det.

add_vars_in_mzn_raw_expr(Expr, !VarSet) :-
    (
        Expr = bool_expr(BoolExpr),
        add_vars_in_bool_expr(BoolExpr, !VarSet)
    ;
        Expr = bool_set_expr(BoolSetExpr),
        add_vars_in_bool_set_expr(BoolSetExpr, !VarSet)
    ;
        Expr = bool_array_expr(BoolArrayExpr),
        add_vars_in_bool_array_expr(BoolArrayExpr, !VarSet)
    ;
        Expr = bool_set_array_expr(BoolSetArrayExpr),
        add_vars_in_bool_set_array_expr(BoolSetArrayExpr, !VarSet)
    ;
        Expr = float_expr(FloatExpr),
        add_vars_in_float_expr(FloatExpr, !VarSet)
    ;
        Expr = float_set_expr(FloatSetExpr),
        add_vars_in_float_set_expr(FloatSetExpr, !VarSet)
    ;
        Expr = float_array_expr(FloatArrayExpr),
        add_vars_in_float_array_expr(FloatArrayExpr, !VarSet)
    ;
        Expr = float_set_array_expr(FloatSetArrayExpr),
        add_vars_in_float_set_array_expr(FloatSetArrayExpr, !VarSet)
    ;
        Expr = int_expr(IntExpr),
        add_vars_in_int_expr(IntExpr, !VarSet)
    ;
        Expr = int_set_expr(IntSetExpr),
        add_vars_in_int_set_expr(IntSetExpr, !VarSet)
    ;
        Expr = int_array_expr(IntArrayExpr),
        add_vars_in_int_array_expr(IntArrayExpr, !VarSet)
    ;
        Expr = int_set_array_expr(IntSetArrayExpr),
        add_vars_in_int_set_array_expr(IntSetArrayExpr, !VarSet)
    ;
        Expr = string_expr(StringExpr),
        add_vars_in_string_expr(StringExpr, !VarSet)
    ;
        Expr = string_array_expr(StringArrayExpr),
        add_vars_in_string_array_expr(StringArrayExpr, !VarSet)
    ;
        Expr = ann_expr(AnnExpr),
        add_vars_in_ann_expr(AnnExpr, !VarSet)
    ;
        Expr = ann_array_expr(AnnArrayExpr),
        add_vars_in_ann_array_expr(AnnArrayExpr, !VarSet)
    ;
        ( Expr = bottom_expr(_)
        ; Expr = bottom_array_expr(_)
        )
    ).

%-----------------------------------------------------------------------------%
%
% Accumulate vars in basic expressions.
%

:- pred add_vars_in_bool_expr(bool_expr::in,
    set(var_id)::in, set(var_id)::out) is det.

add_vars_in_bool_expr(BoolExpr, !VarSet) :-
    (
        BoolExpr = bool_const(_)
    ;
        BoolExpr = bool_var(MZVar),
        VarId = mzn_var_id(MZVar),
        set.insert(VarId, !VarSet)
    ;
        ( BoolExpr = bool_conj(SubExprs)
        ; BoolExpr = bool_disj(SubExprs)
        ),
        add_vars_in_bool_exprs(SubExprs, !VarSet)
    ).

:- pred add_vars_in_float_expr(float_expr::in,
    set(var_id)::in, set(var_id)::out) is det.

add_vars_in_float_expr(FloatExpr, !VarSet) :-
    (
        FloatExpr = float_const(_)
    ;
        FloatExpr = float_var(MZVar),
        VarId = mzn_var_id(MZVar),
        set.insert(VarId, !VarSet)
    ;
        FloatExpr = A + B,
        add_vars_in_float_expr(A, !VarSet),
        add_vars_in_float_expr(B, !VarSet)
    ;
        FloatExpr = _K * A,
        add_vars_in_float_expr(A, !VarSet)
    ).

:- pred add_vars_in_int_expr(int_expr::in,
    set(var_id)::in, set(var_id)::out) is det.

add_vars_in_int_expr(IntExpr, !VarSet) :-
    (
        IntExpr = int_const(_)
    ;
        IntExpr = int_var(MZVar),
        VarId = mzn_var_id(MZVar),
        set.insert(VarId, !VarSet)
    ;
        IntExpr = A + B,
        add_vars_in_int_expr(A, !VarSet),
        add_vars_in_int_expr(B, !VarSet)
    ;
        IntExpr = _K * A,
        add_vars_in_int_expr(A, !VarSet)
    ).

:- pred add_vars_in_string_expr(string_expr::in,
    set(var_id)::in, set(var_id)::out) is det.

add_vars_in_string_expr(_StringExpr, !VarSet).
    % XXX string_show contains mzn_expr

:- pred add_vars_in_ann_expr(mzn_ann::in,
    set(var_id)::in, set(var_id)::out) is det.

add_vars_in_ann_expr(AnnExpr, !VarSet) :-
    (
        AnnExpr = mzn_ann(_Name, Args),
        add_vars_in_mzn_exprs(Args, !VarSet)
    ;
        AnnExpr = mzn_ann_var(MZVar),
        VarId = mzn_var_id(MZVar),
        set.insert(VarId, !VarSet)
    ).

%-----------------------------------------------------------------------------%
%
% Accumulate vars in set expressions.
%

:- pred add_vars_in_bool_set_expr(bool_set_expr::in,
    set(var_id)::in, set(var_id)::out) is det.

add_vars_in_bool_set_expr(BoolSetEXpr, !VarSet) :-
    (
        BoolSetEXpr = set_items(_)
    ;
        BoolSetEXpr = set_var(MZVar),
        VarId = mzn_var_id(MZVar),
        set.insert(VarId, !VarSet)
    ).

:- pred add_vars_in_float_set_expr(float_set_expr::in,
    set(var_id)::in, set(var_id)::out) is det.

add_vars_in_float_set_expr(FloatSetExpr, !VarSet) :-
    (
        FloatSetExpr = set_items(_)
    ;
        FloatSetExpr = set_var(MZVar),
        VarId = mzn_var_id(MZVar),
        set.insert(VarId, !VarSet)
    ).

:- pred add_vars_in_int_set_expr(int_set_expr::in,
    set(var_id)::in, set(var_id)::out) is det.

add_vars_in_int_set_expr(IntSetExpr, !VarSet) :-
    (
        IntSetExpr = set_items(_)
    ;
        IntSetExpr = set_var(MZVar),
        VarId = mzn_var_id(MZVar),
        set.insert(VarId, !VarSet)
    ).

%-----------------------------------------------------------------------------%
%
% Accumulate vars in array expressions.
%

:- pred add_vars_in_bool_array_expr(bool_array_expr::in,
    set(var_id)::in, set(var_id)::out) is det.

add_vars_in_bool_array_expr(BoolArrayExpr, !VarSet) :-
    (
        BoolArrayExpr = array_items(_, As),
        array.foldl(add_vars_in_bool_expr, As, !VarSet)
    ;
        BoolArrayExpr = array_var(_, VarId),
        set.insert(VarId, !VarSet)
    ).

:- pred add_vars_in_float_array_expr(float_array_expr::in,
    set(var_id)::in, set(var_id)::out) is det.

add_vars_in_float_array_expr(FloatArrayExpr, !VarSet) :-
    (
        FloatArrayExpr = array_items(_, As),
        array.foldl(add_vars_in_float_expr, As, !VarSet)
    ;
        FloatArrayExpr = array_var(_, VarId),
        set.insert(VarId, !VarSet)
    ).

:- pred add_vars_in_int_array_expr(int_array_expr::in,
    set(var_id)::in, set(var_id)::out) is det.

add_vars_in_int_array_expr(IntArrayExpr, !VarSet) :-
    (
        IntArrayExpr = array_items(_, As),
        array.foldl(add_vars_in_int_expr, As, !VarSet)
    ;
        IntArrayExpr = array_var(_, VarId),
        set.insert(VarId, !VarSet)
    ).

:- pred add_vars_in_string_array_expr(string_array_expr::in,
    set(var_id)::in, set(var_id)::out) is det.

add_vars_in_string_array_expr(StringArrayExpr, !VarSet) :-
    (
        StringArrayExpr = array_items(_, As),
        array.foldl(add_vars_in_string_expr, As, !VarSet)
    ;
        StringArrayExpr = array_var(_, VarId),
        set.insert(VarId, !VarSet)
    ).

:- pred add_vars_in_ann_array_expr(ann_array_expr::in,
    set(var_id)::in, set(var_id)::out) is det.

add_vars_in_ann_array_expr(AnnArrayExpr, !VarSet) :-
    (
        AnnArrayExpr = array_items(_, As),
        array.foldl(add_vars_in_ann_expr, As, !VarSet)
    ;
        AnnArrayExpr = array_var(_, VarId),
        set.insert(VarId, !VarSet)
    ).

%-----------------------------------------------------------------------------%
%
% Accumulate vars in set array expressions.
%

:- pred add_vars_in_bool_set_array_expr(bool_set_array_expr::in,
    set(var_id)::in, set(var_id)::out) is det.

add_vars_in_bool_set_array_expr(BoolSetArrayExpr, !VarSet) :-
    (
        BoolSetArrayExpr = array_items(_, As),
        array.foldl(add_vars_in_bool_set_expr, As, !VarSet)
    ;
        BoolSetArrayExpr = array_var(_, VarId),
        set.insert(VarId, !VarSet)
    ).

:- pred add_vars_in_float_set_array_expr(float_set_array_expr::in,
    set(var_id)::in, set(var_id)::out) is det.

add_vars_in_float_set_array_expr(FloatSetArrayExpr, !VarSet) :-
    (
        FloatSetArrayExpr = array_items(_, As),
        array.foldl(add_vars_in_float_set_expr, As, !VarSet)
    ;
        FloatSetArrayExpr = array_var(_, VarId),
        set.insert(VarId, !VarSet)
    ).

:- pred add_vars_in_int_set_array_expr(int_set_array_expr::in,
    set(var_id)::in, set(var_id)::out) is det.

add_vars_in_int_set_array_expr(IntSetArrayExpr, !VarSet) :-
    (
        IntSetArrayExpr = array_items(_, As),
        array.foldl(add_vars_in_int_set_expr, As, !VarSet)
    ;
        IntSetArrayExpr = array_var(_, VarId),
        set.insert(VarId, !VarSet)
    ).

%-----------------------------------------------------------------------------%
%
% Accumulate vars in lists of expressions.
%

:- pred add_vars_in_mzn_exprs(list(mzn_expr)::in,
    set(var_id)::in, set(var_id)::out) is det.

add_vars_in_mzn_exprs([], !VarSet).
add_vars_in_mzn_exprs([Expr | Exprs], !VarSet) :-
    add_vars_in_mzn_expr(Expr, !VarSet),
    add_vars_in_mzn_exprs(Exprs, !VarSet).

:- pred add_vars_in_bool_exprs(list(bool_expr)::in,
    set(var_id)::in, set(var_id)::out) is det.

add_vars_in_bool_exprs([], !VarSet).
add_vars_in_bool_exprs([Expr | Exprs], !VarSet) :-
    add_vars_in_bool_expr(Expr, !VarSet),
    add_vars_in_bool_exprs(Exprs, !VarSet).

%-----------------------------------------------------------------------------%
:- end_module utilities.
%-----------------------------------------------------------------------------%
