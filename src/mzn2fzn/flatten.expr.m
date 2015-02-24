%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2009-2010 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Ralph Becket <rafe@csse.unimelb.edu.au>
%
% Flatten a Zinc AST expr into an mzn_expr.
%
%-----------------------------------------------------------------------------%

:- module flatten.expr.
:- interface.

:- import_module errors.
:- import_module flatten.env.
:- import_module types.

:- import_module types_and_insts.
:- import_module zinc_ast.

:- import_module list.

%-----------------------------------------------------------------------------%

    % Flatten an arbitrary MiniZinc expression.
    %
:- pred flatten_expr(error_context::in, expr::in, mzn_expr::out,
    env::in, env::out) is det.

:- pred flatten_expr_acc(error_context::in, expr::in,
    list(mzn_expr)::in, list(mzn_expr)::out, env::in, env::out) is det.

    % Some logical operators (such as disjunction) require us to flatten their
    % arguments in a reified form.
    %
:- pred flatten_expr_must_reify(error_context::in, expr::in, mzn_expr::out,
    env::in, env::out) is det.

:- pred flatten_expr_must_reify_acc(error_context::in, expr::in,
    list(mzn_expr)::in, list(mzn_expr)::out, env::in, env::out) is det.

    % Exported for hr.convert.m only.
    %
:- pred flatten_coerce(error_context::in, type_inst::in, type_inst::in,
    expr::in, mzn_expr::out, env::in, env::out) is det.

    % Flatten a MiniZinc application.  An application can be one of two things:
    % (1) an application of a predicate;
    % (2) an application of a built-in operator.
    % Built-in logical operators (such as disjuntion, "\/") need special
    % treatment since their arguments must be evaluated in a reifying context.
    %
:- pred flatten_app(error_context::in, string::in, int::in, list(expr)::in,
    mzn_expr::out, env::in, env::out) is det.

    % Flatten a builtin operator application.
    %
:- pred flatten_builtin(error_context::in, string::in, list(mzn_expr)::in,
    mzn_expr::out, env::in, env::out) is semidet.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module common_format.
:- import_module flatten.ann.
:- import_module flatten.app.
:- import_module flatten.array.
:- import_module flatten.bool.
:- import_module flatten.comp.
:- import_module flatten.float.
:- import_module flatten.int.
:- import_module flatten.let.
:- import_module flatten.set.
:- import_module flatten.string.
:- import_module mzn_ops.

:- import_module zinc_common.

:- import_module array.
:- import_module bool.
:- import_module float.
:- import_module int.
:- import_module io.
:- import_module set.
:- import_module string.

%-----------------------------------------------------------------------------%

flatten_expr(Context, Expr, MZ, !Env) :-
    Expr = expr(RawExpr, AnnExprs, ExprInfo),
    ExprInfo = expr_info(_SrcLocn, TI),
    flatten_anns(Context, AnnExprs, Anns, !Env),
    OldAnns = !.Env ^ anns,
    ( if Anns = no_anns then
        true
    else
        !Env ^ anns := join_anns(Anns, OldAnns)
    ),
    (
        RawExpr = ident(VarId),
        flatten_ident(Context, VarId, MZ, !Env)
    ;
        RawExpr = lit(Literal),
        flatten_literal(Context, Literal, MZ, !Env)
    ;
        RawExpr = app(PredId, ProcNo, _AppKind, ArgExprs),
        PredName = id_name(PredId),
        flatten_app(Context, PredName, ProcNo, ArgExprs, MZ, !Env)
    ;
        RawExpr = array_access(ArrayExpr, IndexExprs),
        flatten_expr(Context, ArrayExpr, MZA, !Env),
        list.map_foldl(flatten_expr(Context), IndexExprs, MZIndices, !Env),
        flatten_array_access(Context, TI, MZA, MZIndices, MZ, !Env)
    ;
        RawExpr = lit_set(ItemExprs),
        flatten_lit_set(Context, TI, ItemExprs, MZ, !Env)
    ;
        RawExpr = lit_simple_array(ItemExprs),
        flatten_lit_array(Context, TI, ItemExprs, MZ, !Env)
    ;
        RawExpr = lit_ann(Id, ArgExprs),
        AnnName = Id ^ id_name,
        flatten_ann(Context, AnnName, ArgExprs, MZ0, !Env),
        MZ0 = mzn_expr(RawMZ, AnnAnns),
        MZ = mzn_expr(RawMZ, join_anns(Anns, AnnAnns))
    ;
        RawExpr = comprehension(CompKind, Generators, MaybeCondExpr),
        flatten_comp(Context, TI, CompKind, Generators, MaybeCondExpr, MZ,
            !Env)
    ;
        RawExpr = anon_var,
        flatten_anon_var(Context, TI, MZ, !Env)
    ;
        RawExpr = if_then_else(CondExpr, ThenExpr, ElseExpr),
        flatten_if_then_else(Context, CondExpr, ThenExpr, ElseExpr, MZ, !Env)
    ;
        RawExpr = let(LetVars, LetExpr),
        flatten_let_expr(Context, LetVars, LetExpr, MZ, !Env)
    ;
        RawExpr = coerce(FromTI, ToTI, CoerceExpr),
        flatten_coerce(Context, FromTI, ToTI, CoerceExpr, MZ, !Env)
    ;
        RawExpr = lit_tuple(_),
        minizinc_internal_error(Context, $pred, "Non-MiniZinc syntax item.\n")
    ),
    ( if Anns = no_anns then
        true
    else
        !Env ^ anns := OldAnns
    ).

flatten_expr_acc(Context, Expr, !MZExprs, !Env) :-
    flatten_expr(Context, Expr, MZ, !Env),
    !:MZExprs = [MZ | !.MZExprs].

%-----------------------------------------------------------------------------%

    % Obtain the value of a variable.
    %
    % If the variable value has no value, then just provide a representation
    % of the variable.
    %
    % If the variable value is an array literal and the variable is not a
    % local, just provide a representation of the variable (use
    % fully_deref_xxx_array to obtain the literal value).
    %
    % We do this to prevent duplicating literal array values in the model.
    %
:- pred flatten_ident(error_context::in, var_id::in, mzn_expr::out,
    env::in, env::out) is det.

flatten_ident(_Context, Var, MZ, !Env) :-
    ( if !.Env ^ var_value(Var) = MZ0 then
        MZ0 = mzn_expr(RawMZ0, Anns),
        ( if
            !.Env ^ var_is_local(Var) = no,
            (
                RawMZ0 = bool_array_expr(array_items(IndexRanges, _)),
                RawMZ  = bool_array_expr(array_var(IndexRanges, Var))
            ;
                RawMZ0 = float_array_expr(array_items(IndexRanges, _)),
                RawMZ  = float_array_expr(array_var(IndexRanges, Var))
            ;
                RawMZ0 = int_array_expr(array_items(IndexRanges, _)),
                RawMZ  = int_array_expr(array_var(IndexRanges, Var))
            ;
                RawMZ0 = bool_set_array_expr(array_items(IndexRanges, _)),
                RawMZ  = bool_set_array_expr(array_var(IndexRanges, Var))
            ;
                RawMZ0 = float_set_array_expr(array_items(IndexRanges, _)),
                RawMZ  = float_set_array_expr(array_var(IndexRanges, Var))
            ;
                RawMZ0 = int_set_array_expr(array_items(IndexRanges, _)),
                RawMZ  = int_set_array_expr(array_var(IndexRanges, Var))
            )
        then
            MZ = mzn_expr(RawMZ, Anns)
        else
            MZ = MZ0
        )
    else
        IndexRanges = !.Env ^ var_index_ranges(Var),
        MZType = !.Env ^ var_type(Var),
        MZ = make_var_mzn_expr(IndexRanges, MZType, Var)
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_literal(error_context::in, literal::in, mzn_expr::out,
    env::in, env::out) is det.

flatten_literal(_Context, Literal, MZ, !Env) :-
    (
        Literal = bool(B),
        MZ = bool_to_mzn_expr(bool_const(B))
    ;
        Literal = floatstr(FS),
        MZ = float_to_mzn_expr(float_const(string.det_to_float(FS)))
    ;
        Literal = int(I),
        MZ = int_to_mzn_expr(int_const(I))
    ;
        Literal = string(S),
        MZ = string_to_mzn_expr(string_const(S))
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_lit_set(error_context::in, type_inst::in, list(expr)::in,
    mzn_expr::out, env::in, env::out) is det.

flatten_lit_set(Context, TI, ItemExprs, MZ, !Env) :-
    (
        ItemExprs = [],
        ( if
            TI = ti_par_set(ElemTI),
            (
                ElemTI = ti_par_bool,
                MZ0 = bool_set_to_mzn_expr(set_items(set.init))
            ;
                ElemTI = ti_par_float,
                MZ0 = float_set_to_mzn_expr(set_items(set.init))
            ;
                ElemTI = ti_par_int,
                MZ0 = int_set_to_mzn_expr(set_items(set.init))
            ;
                % This happens because the broken type inference algorithm
                % doesn't assign types to empty sets inside par-to-var
                % coercions.  The only such sets can be int sets.
                %
                ElemTI = ti_par_bottom,
                MZ0 = int_set_to_mzn_expr(set_items(set.init))
            )
        then
            MZ = MZ0
        else
            minizinc_user_error(Context,
                "This is not a valid MiniZinc set type.\n")
        )
    ;
        ItemExprs = [_ | _],
        list.foldl2(flatten_expr_acc(Context), ItemExprs, [], ItemMZs, !Env),
        ( if
            TI = ti_par_set(ElemTI),
            (
                ElemTI = ti_par_bool,
                AddToBoolSet = (pred(ItemMZ::in, !.S::in, !:S::out) is det :-
                    BoolConst = mzn_expr_to_bool_const(Context, ItemMZ),
                    set.insert(BoolConst, !S)
                ),
                list.foldl(AddToBoolSet, ItemMZs, set.init, Set),
                MZ0 = bool_set_to_mzn_expr(set_items(Set))
            ;
                ElemTI = ti_par_float,
                AddToFloatSet = (pred(ItemMZ::in, !.S::in, !:S::out) is det :-
                    FloatConst = mzn_expr_to_float_const(Context, ItemMZ),
                    set.insert(FloatConst, !S)
                ),
                list.foldl(AddToFloatSet, ItemMZs, set.init, Set),
                MZ0 = float_set_to_mzn_expr(set_items(Set))
            ;
                ElemTI = ti_par_int,
                AddToIntSet = (pred(ItemMZ::in, !.S::in, !:S::out) is det :-
                    IntConst = mzn_expr_to_int_const(Context, ItemMZ),
                    set.insert(IntConst, !S)
                ),
                list.foldl(AddToIntSet, ItemMZs, set.init, Set),
                MZ0 = int_set_to_mzn_expr(set_items(Set))
            )
          then
            MZ = MZ0
          else
            minizinc_user_error(Context,
                "This is not a valid MiniZinc set type.\n")
        )
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_lit_array(error_context::in, type_inst::in, list(expr)::in,
    mzn_expr::out, env::in, env::out) is det.

flatten_lit_array(Context, TI, ItemExprs, MZ, !Env) :-
    (
        ItemExprs = [],
        IndexRanges = [index_range(1, 0)],
        ( if
            TI = ti_array(_, ElemTI),
            (
                ( ElemTI = ti_par_bool
                ; ElemTI = ti_var_bool
                ),
                Empty = array.make_empty_array,
                MZ0 = bool_array_to_mzn_expr(array_items(IndexRanges,
                    Empty))
            ;
                ( ElemTI = ti_par_float
                ; ElemTI = ti_var_float
                ),
                Empty = array.make_empty_array,
                MZ0 = float_array_to_mzn_expr(array_items(IndexRanges,
                    Empty))
            ;
                ( ElemTI = ti_par_int
                ; ElemTI = ti_var_int
                ),
                Empty = array.make_empty_array,
                MZ0 = int_array_to_mzn_expr(array_items(IndexRanges, Empty))
            ;
                ElemTI = ti_par_set(ti_par_bool),
                Empty = array.make_empty_array,
                MZ0 = bool_set_array_to_mzn_expr(array_items(IndexRanges,
                    Empty))
            ;
                ElemTI = ti_par_set(ti_par_float),
                Empty = array.make_empty_array,
                MZ0 = float_set_array_to_mzn_expr(array_items(IndexRanges,
                    Empty))
            ;
                ( ElemTI = ti_var_set(ti_par_int)
                ; ElemTI = ti_par_set(ti_par_int)
                ),
                Empty = array.make_empty_array,
                MZ0 = int_set_array_to_mzn_expr(array_items(IndexRanges,
                    Empty))
            ;
                ElemTI = ti_par_string,
                Empty = array.make_empty_array,
                MZ0 = string_array_to_mzn_expr(array_items(IndexRanges,
                    Empty))
            ;
                ElemTI = ti_ann,
                Empty = array.make_empty_array,
                MZ0 = ann_array_to_mzn_expr(array_items(IndexRanges,
                    Empty))
            ;
                ElemTI = ti_par_bottom,
                Empty = array.make_empty_array,
                MZ0 = bottom_array_to_mzn_expr(array_items(IndexRanges,
                    Empty))
            )
        then
            MZ = MZ0
        else
            minizinc_user_error(Context,
                "This is not a valid MiniZinc array type.\n")
        )
    ;
        ItemExprs = [_ | _],
        N = list.length(ItemExprs),
        IndexRanges = [index_range(1, N)],
        ( if TI = ti_array(_, ti_var_bool) then
            list.foldl2(flatten_expr_must_reify_acc(Context), ItemExprs,
                [], RevItemMZs, !Env)
        else
            list.foldl2(flatten_expr_acc(Context), ItemExprs,
                [], RevItemMZs, !Env)
        ),
        ( if
            TI = ti_array(_, ElemTI),
            (
                ( ElemTI = ti_par_bool
                ; ElemTI = ti_var_bool
                ),
                list.foldl(mzn_expr_to_bool_acc(Context), RevItemMZs,
                    [], BoolExprs),
                Xs = array(BoolExprs),
                MZ0 = bool_array_to_mzn_expr(array_items(IndexRanges, Xs))
            ;
                ( ElemTI = ti_par_float
                ; ElemTI = ti_var_float
                ),
                list.foldl(mzn_expr_to_float_acc(Context), RevItemMZs,
                    [], FloatExprs),
                Xs = array(FloatExprs),
                MZ0 = float_array_to_mzn_expr(array_items(IndexRanges, Xs))
            ;
                ( ElemTI = ti_par_int
                ; ElemTI = ti_var_int
                ),
                list.foldl(mzn_expr_to_int_acc(Context), RevItemMZs,
                    [], IntExprs),
                Xs = array(IntExprs),
                MZ0 = int_array_to_mzn_expr(array_items(IndexRanges, Xs))
            ;
                ElemTI = ti_par_set(ti_par_bool),
                list.foldl(mzn_expr_to_bool_set_acc(Context), RevItemMZs,
                    [], SetBoolExprs),
                Xs = array(SetBoolExprs),
                MZ0 = bool_set_array_to_mzn_expr(array_items(IndexRanges, Xs))
            ;
                ElemTI = ti_par_set(ti_par_float),
                list.foldl(mzn_expr_to_float_set_acc(Context), RevItemMZs,
                    [], SetFloatExprs),
                Xs = array(SetFloatExprs),
                MZ0 = float_set_array_to_mzn_expr(array_items(IndexRanges, Xs))
            ;
                ( ElemTI = ti_par_set(ti_par_int)
                ; ElemTI = ti_var_set(ti_par_int)
                ; ElemTI = ti_par_set(ti_par_bottom)
                ),
                list.foldl(mzn_expr_to_int_set_acc(Context), RevItemMZs,
                    [], SetIntExprs),
                Xs = array(SetIntExprs),
                MZ0 = int_set_array_to_mzn_expr(array_items(IndexRanges, Xs))
            ;
                ElemTI = ti_par_string,
                list.foldl(mzn_expr_to_string_acc(Context), RevItemMZs,
                    [], StringExprs),
                Xs = array(StringExprs),
                MZ0 = string_array_to_mzn_expr(array_items(IndexRanges, Xs))
            ;
                ElemTI = ti_ann,
                list.foldl(mzn_expr_to_ann_acc(Context), RevItemMZs,
                    [], AnnExprs),
                Xs = array(AnnExprs),
                MZ0 = ann_array_to_mzn_expr(array_items(IndexRanges, Xs))
            ;
                ( ElemTI = ti_par_bottom
                ; ElemTI = ti_var_bottom
                ),
                list.length(RevItemMZs, NumItems),
                array.init(NumItems, bottom_expr, Xs),
                MZ0 = bottom_array_to_mzn_expr(array_items(IndexRanges, Xs))
            )
        then
            MZ = MZ0
        else
            minizinc_user_error(Context,
                "This is not a valid MiniZinc array type.\n")
        )
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_ann(error_context::in,
    string::in, list(expr)::in, mzn_expr::out,
    env::in, env::out) is det.

flatten_ann(Context, AnnName, ArgExprs, MZ, !Env) :-
    list.map_foldl(flatten_expr(Context), ArgExprs, ArgMZs, !Env),
    MZ = mzn_expr(ann_expr(mzn_ann(AnnName, ArgMZs)), no_anns).

%-----------------------------------------------------------------------------%

:- pred flatten_anon_var(error_context::in, type_inst::in, mzn_expr::out,
    env::in, env::out) is det.

flatten_anon_var(Context, TI, MZ, !Env) :-
    type_inst_to_mzn_type(Context, TI, VarPar, MZType),
    ( if MZType = mzn_bottom then
        MZ = mzn_expr(bottom_expr(bottom_expr), no_anns)
    else
        create_new_var(Context, "X", VarPar, MZType, [], no_anns, _Var, MZ,
            !Env)
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_if_then_else(error_context::in, expr::in, expr::in, expr::in,
    mzn_expr::out, env::in, env::out) is det.

flatten_if_then_else(Context, CondExpr, ThenExpr, ElseExpr, MZ, !Env) :-
    CondContext = [["In if-then-else condition.\n"] | Context],
    flatten_expr_must_reify(CondContext, CondExpr, CondMZ, !Env),
    A = mzn_expr_to_bool(CondContext, CondMZ),
    ( if A = bool_const(BoolA) then
        (
            BoolA = yes,
            ThenContext =
                [["In if-then-else 'then' expression.\n"] | Context],
            flatten_expr(ThenContext, ThenExpr, MZ, !Env)
        ;
            BoolA = no,
            ElseContext =
                [["In if-then-else 'else' expression.\n"] | Context],
            flatten_expr(ElseContext, ElseExpr, MZ, !Env)
        )
    else
        minizinc_user_error(CondContext,
            "Condition must be fixed, not variable.\n")
    ).

%-----------------------------------------------------------------------------%

flatten_coerce(Context, TIFrom, TITo, Expr, MZ, !Env) :-
    CoerceContext = [["In coercion.\n"] | Context],
    flatten_expr(CoerceContext, Expr, MZ0, !Env),
    type_inst_to_mzn_type(CoerceContext, TIFrom, VarParFrom, _MZTypeFrom),
    type_inst_to_mzn_type(CoerceContext, TITo, VarParTo, MZTypeTo),
    ( if
        VarParFrom = par,
        VarParTo = var
    then
        % This is a par to var coercion.
        MZ = MZ0
    else if
        (
            MZTypeTo = mzn_int(_),
            A = mzn_expr_to_bool(CoerceContext, MZ0),
            flatten_bool_to_int(CoerceContext, no_anns, b2i_bool2int,
                A, Z, !Env),
            MZ1 = int_to_mzn_expr(Z)
        ;
            MZTypeTo = mzn_float(_),
            A = mzn_expr_to_int(CoerceContext, MZ0),
            flatten_int_to_float(CoerceContext, no_anns, i2f_int2float,
                A, Z, !Env),
            MZ1 = float_to_mzn_expr(Z)
        ;
            MZTypeTo = mzn_int_array(_),
            (
                MZ0 = mzn_expr(bool_array_expr(A), _),
                flatten_coerce_array(CoerceContext,
                    flatten_bool_to_int_semidet(CoerceContext, no_anns,
                        b2i_bool2int),
                    ( func(V, I) = bool_var(var_index(V, I)) ),
                    A, Z, !Env),
                MZ1 = int_array_to_mzn_expr(Z)
            ;
                MZ0 = mzn_expr(int_set_expr(A), _),
                F = ( func(I) = int_const(I) ),
                flatten_coerce_set_to_array(CoerceContext, F, A, Z, !Env),
                MZ1 = int_array_to_mzn_expr(Z)
            )
        ;
            MZTypeTo = mzn_float_array(_),
            (
                MZ0 = mzn_expr(int_array_expr(A), _),
                flatten_coerce_array(CoerceContext,
                    flatten_int_to_float_semidet(CoerceContext, no_anns,
                        i2f_int2float),
                    ( func(V, I) = int_var(var_index(V, I)) ),
                    A, Z, !Env),
                MZ1 = float_array_to_mzn_expr(Z)
            ;
                MZ0 = mzn_expr(int_set_expr(A), _),
                F = ( func(I) = float_const(float(I)) ),
                flatten_coerce_set_to_array(CoerceContext, F, A, Z, !Env),
                MZ1 = float_array_to_mzn_expr(Z)
            )
        )
    then
        MZ = MZ1
    else
        minizinc_user_error(CoerceContext, "Coercion is invalid.\n")
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_coerce_array(error_context::in,
    pred(T1, T2, env, env)::in(pred(in, out, in, out) is semidet),
    (func(var_id, int) = T1)::in,
    array_expr(T1)::in, array_expr(T2)::out, env::in, env::out) is semidet.

flatten_coerce_array(_Context, P, F, ArrayExpr0, ArrayExpr, !Env) :-
    (
        ArrayExpr0 = array_items(IndexRanges0, As0),
        N = index_ranges_to_size(IndexRanges0),
        IndexRanges = [index_range(1, N)]
    ;
        ArrayExpr0 = array_var(IndexRanges0, V),
        N = index_ranges_to_size(IndexRanges0),
        IndexRanges = [index_range(1, N)],
        As0 = array(int.fold_down(func(I, Ls) = [F(V, I) | Ls], 1, N, []))
    ),
    array.map_foldl(P, As0, As, !Env),
    ArrayExpr = array_items(IndexRanges, As).

%-----------------------------------------------------------------------------%

:- pred flatten_coerce_set_to_array(error_context::in,
    (func(T1) = T2)::in, set_expr(T1)::in, array_expr(T2)::out,
    env::in, env::out) is det.

flatten_coerce_set_to_array(Context, F, SetExpr, ArrayExpr, !Env) :-
    (
        SetExpr = set_var(_),
        minizinc_user_error(Context, "Set variables cannot be coerced.\n")
    ;
        SetExpr = set_items(Xs),
        coerce_elems(F, set.to_sorted_list(Xs), [], RevAs),
        As = array(list.reverse(RevAs)),
        N = array.size(As),
        IndexRanges = [index_range(1, N)],
        ArrayExpr = array_items(IndexRanges, As)
    ).

    % There's nothing in the stdlib that we allows us to do this without
    % nesting closures.
    %
:- pred coerce_elems((func(T1) = T2)::in, list(T1)::in,
    list(T2)::in, list(T2)::out) is det.

coerce_elems(_, [], !Acc).
coerce_elems(F, [H0 | T], !Acc) :-
    H = F(H0),
    !:Acc = [H | !.Acc],
    coerce_elems(F, T, !Acc).

%-----------------------------------------------------------------------------%

flatten_app(Context, Op, ProcNo, ArgExprs, MZ, !Env) :-
    AppContext = [["In '", Op, "' expression.\n"] | Context],
    Arity = list.length(ArgExprs),
    ( if
        Op = "assert",
        ArgExprs = [ArgExpr1, ArgExpr2 | OptArgExpr]
    then
        % We need to handle assertions specially.
        Reifying = !.Env ^ reifying,
        !Env ^ reifying := reifying([]),
        flatten_expr(AppContext, ArgExpr1, MZ1, !Env),
        !Env ^ reifying := Reifying,
        B1 = mzn_expr_to_bool(AppContext, MZ1),
        ( if B1 = bool_const(no) then
            flatten_expr(AppContext, ArgExpr2, MZ2, !Env),
            S2 = mzn_expr_to_string(AppContext, MZ2),
            Str = format_string_expr(S2),
            minizinc_user_error(AppContext, "Assertion failure: " ++ Str)
        else
            (
                OptArgExpr = [],
                MZ = bool_to_mzn_expr(bool_const(yes))
            ;
                OptArgExpr = [ArgExpr3],
                flatten_expr(AppContext, ArgExpr3, MZ, !Env)
            ;
                OptArgExpr = [_, _ | _],
                minizinc_internal_error(AppContext, $pred, "arg count error")
            )
        )
    else if
        Op = "abort",
        ArgExprs = [AbortStrExpr]
    then
        flatten_expr(AppContext, AbortStrExpr, MZAbortStr, !Env),
        StrExpr = mzn_expr_to_string(AppContext, MZAbortStr),
        Str = format_string_expr(StrExpr),
        minizinc_user_error(AppContext, "Abort: " ++ Str)
    else if
        Op = "trace",
        ArgExprs = [TraceStrExpr, TraceArgExpr]
    then
        flatten_expr(AppContext, TraceStrExpr, MZTraceStr, !Env),
        StrExpr = mzn_expr_to_string(AppContext, MZTraceStr),
        Str = format_string_expr_unquoted(StrExpr),
        trace [io(!IO)] (
            io.write_string(Str, !IO),
            io.flush_output(!IO)
        ),
        flatten_expr(AppContext, TraceArgExpr, MZ, !Env)
    else if
        Op = "is_fixed",
        ArgExprs = [ArgExpr1]
    then
        flatten_expr(Context, ArgExpr1, MZ1, !Env),
        Z = ( if flatten_is_fixed(!.Env, MZ1) then yes else no),
        MZ = bool_to_mzn_expr(bool_const(Z))
    else if
        Op = "show",
        ArgExprs = [ArgExpr1]
    then
        % We need to handle 'show' expressions specially.
        flatten_expr(Context, ArgExpr1, MZ1, !Env),
        flatten_show_to_string(AppContext, MZ1, StringZ, !Env),
        MZ = string_to_mzn_expr(string_const(StringZ))
    else if
        Op = "show_int",
        ArgExprs = [WidthExpr, ValueExpr]
    then
        flatten_expr(Context, WidthExpr, MZWidth, !Env),
        flatten_expr(Context, ValueExpr, MZValue, !Env),
        flatten_show_int_to_string(AppContext, MZWidth, MZValue, StringZ, !Env),
        MZ = string_to_mzn_expr(string_const(StringZ)) 
    else if
        Op = "show_float",
        ArgExprs = [WidthExpr, PrecExpr, ValueExpr]
    then
        flatten_expr(Context, WidthExpr, MZWidth, !Env),
        flatten_expr(Context, PrecExpr, MZPrec, !Env),
        flatten_expr(Context, ValueExpr, MZValue, !Env),
        flatten_show_float_to_string(AppContext, MZWidth, MZPrec, MZValue,
            StringZ, !Env),
        MZ = string_to_mzn_expr(string_const(StringZ))
    else if
        Op = "fix",
        ArgExprs = [ArgExpr1]
    then
        flatten_app_fix(Context, AppContext, ArgExpr1, MZ, !Env)
    else if
        is_builtin_op(Op, Arity, IsLogicalOp, NeedToReifyArgs, _OpType)
    then
        % Flatten the arguments. Annotations in the enclosing scope
        % are not propagated unless this is a logical op. Some logical
        % operators may need their arguments to be flattened in a reified
        % form (e.g., disjunction).
        OldReifying = !.Env ^ reifying,
        (
            IsLogicalOp = yes,
            (
                NeedToReifyArgs = no,
                list.map_foldl(flatten_expr(AppContext),
                    ArgExprs, ArgMZs, !Env)
            ;
                NeedToReifyArgs = yes,
                list.map_foldl(flatten_expr_must_reify(AppContext),
                    ArgExprs, ArgMZs, !Env)
            )
        ;
            IsLogicalOp = no,
            OuterAnns = !.Env ^ anns,
            !Env ^ anns := no_anns,
            list.map_foldl(flatten_expr(AppContext), ArgExprs, ArgMZs, !Env),
            !Env ^ anns := OuterAnns
        ),
        ( if flatten_builtin(AppContext, Op, ArgMZs, MZ0, !Env) then
            % If this is a logical operator and there are residual
            % reification variables (e.g., in an equality with a
            % partial function application) then we may need to conjoin
            % the reification variables with the result.
            (
                IsLogicalOp = no,
                MZ = MZ0
            ;
                IsLogicalOp = yes,
                (
                    OldReifying = not_reifying,
                    CurReifying = !.Env ^ reifying,
                    (
                        CurReifying = not_reifying,
                        MZ = MZ0
                    ;
                        CurReifying = reifying(Bs0 : bool_exprs),
                        % We need to conjoin the reification vars
                        % with the result.
                        B0 = mzn_expr_to_bool(AppContext, MZ0),
                        (
                            Bs0 = [],
                            B = B0
                        ;
                            Bs0 = [B1],
                            conjoin(AppContext, B0, B1, B, !Env)
                        ;
                            Bs0 = [_, _ | _],
                            conjoin(AppContext, B0, bool_conj(Bs0), B, !Env)
                        ),
                        % Restore the old reification status.
                        !Env ^ reifying := not_reifying,
                        MZ = bool_to_mzn_expr(B)
                    )
                ;
                    OldReifying = reifying(_ : bool_exprs),
                    % In this case we don't need to do anything.  We can
                    % let the reification vars "bubble up".
                    MZ = MZ0
                )
            )
        else
            minizinc_user_error(AppContext,
                "Invalid builtin operator application.\n")
        )
    else 
        % This must be a user-defined predicate application.  Arguments are
        % flattened without annotations from the enclosing scope.
        OuterAnns = !.Env ^ anns,
        !Env ^ anns := no_anns,
        OldReifying = !.Env ^ reifying,
        list.map_foldl(flatten_expr_must_reify(AppContext), ArgExprs, ArgMZs,
            !Env),
        !Env ^ anns := OuterAnns,
        !Env ^ reifying := OldReifying,
        flatten_predicate(AppContext, Op, ProcNo, ArgMZs, no_anns, B, !Env),
        MZ = mzn_expr(bool_expr(B), no_anns)
    ).

%-----------------------------------------------------------------------------%

flatten_expr_must_reify(Context, Expr, MZ, !Env) :-
    OldReifying = !.Env ^ reifying,
    !Env ^ reifying := reifying([] : bool_exprs),
    flatten_expr(Context, Expr, MZ0, !Env),
    Reifying = !.Env ^ reifying,
    (
        Reifying = not_reifying,
        minizinc_internal_error(Context, $pred,
            "Should be reifying, but found not_reifying.\n")
    ;
        Reifying = reifying([] : bool_exprs),   % Light optimisation.
        NewReifying = OldReifying,
        MZ = MZ0
    ;
        Reifying = reifying(Bs @ [_ | _] : bool_exprs),
        ( if
            % If this is a boolean expression, then conjoin the
            % new reification vars with the result.
            MZ0 = mzn_expr(bool_expr(B0), _)
        then
            (
                Bs = [],
                B = B0
            ;
                Bs = [B1],
                conjoin(Context, B0, B1, B, !Env)
            ;
                Bs = [_, _ | _],
                conjoin(Context, B0, bool_conj(Bs), B, !Env)
            ),
            NewReifying = OldReifying,
            MZ = bool_to_mzn_expr(B)
        else
            % This isn't a boolean expression, so we need to preserve
            % the new reification vars.
            (
                OldReifying = not_reifying,
                NewReifying = reifying(Bs)
            ;
                OldReifying = reifying(Bs0),
                NewReifying = reifying(Bs0 ++ Bs)
            ),
            MZ = MZ0
        )
    ),
    !Env ^ reifying := NewReifying.

flatten_expr_must_reify_acc(Context, Expr, !MZs, !Env) :-
    flatten_expr_must_reify(Context, Expr, MZ, !Env),
    !:MZs = [MZ | !.MZs].

%-----------------------------------------------------------------------------%

flatten_builtin(Context, Op, ArgMZs, MZ, !Env) :-
    Anns = no_anns,
    (
        ArgMZs = [MZA],
        MZA = mzn_expr(RawMZA, _),
        flatten_builtin_arity_1(Context, Anns, Op, RawMZA, RawMZ, !Env)
    ;
        ArgMZs = [MZA, MZB],
        MZA = mzn_expr(RawMZA, _),
        MZB = mzn_expr(RawMZB, _),
        flatten_builtin_arity_2(Context, Anns, Op, MZA, MZB, RawMZA, RawMZB,
            RawMZ, !Env)
    ;
        ArgMZs = [MZA, MZB, MZC],
        MZA = mzn_expr(RawMZA, _),
        MZB = mzn_expr(RawMZB, _),
        MZC = mzn_expr(RawMZC, _),
        flatten_builtin_arity_3(Context, Anns, Op, RawMZA, RawMZB, RawMZC,
            RawMZ, !Env)
    ;
        ArgMZs = [MZA, MZB, MZC, MZD],
        MZA = mzn_expr(RawMZA, _),
        MZB = mzn_expr(RawMZB, _),
        MZC = mzn_expr(RawMZC, _),
        MZD = mzn_expr(RawMZD, _),
        flatten_builtin_arity_4(Context, Anns, Op, RawMZA, RawMZB, RawMZC,
            RawMZD, RawMZ, !Env)
    ;
        ArgMZs = [MZA, MZB, MZC, MZD, MZE],
        MZA = mzn_expr(RawMZA, _),
        MZB = mzn_expr(RawMZB, _),
        MZC = mzn_expr(RawMZC, _),
        MZD = mzn_expr(RawMZD, _),
        MZE = mzn_expr(RawMZE, _),
        flatten_builtin_arity_5(Context, Anns, Op, RawMZA, RawMZB, RawMZC,
            RawMZD, RawMZE, RawMZ, !Env)
    ;
        ArgMZs = [MZA, MZB, MZC, MZD, MZE, MZF],
        MZA = mzn_expr(RawMZA, _),
        MZB = mzn_expr(RawMZB, _),
        MZC = mzn_expr(RawMZC, _),
        MZD = mzn_expr(RawMZD, _),
        MZE = mzn_expr(RawMZE, _),
        MZF = mzn_expr(RawMZF, _),
        flatten_builtin_arity_6(Context, Anns, Op, RawMZA, RawMZB, RawMZC,
            RawMZD, RawMZE, RawMZF, RawMZ, !Env)
    ;
        ArgMZs = [MZA, MZB, MZC, MZD, MZE, MZF, MZG],
        MZA = mzn_expr(RawMZA, _),
        MZB = mzn_expr(RawMZB, _),
        MZC = mzn_expr(RawMZC, _),
        MZD = mzn_expr(RawMZD, _),
        MZE = mzn_expr(RawMZE, _),
        MZF = mzn_expr(RawMZF, _),
        MZG = mzn_expr(RawMZG, _),
        flatten_builtin_arity_7(Context, Anns, Op, RawMZA, RawMZB, RawMZC,
            RawMZD, RawMZE, RawMZF, RawMZG, RawMZ, !Env)
    ),
    MZ = mzn_expr(RawMZ, Anns).

:- pred flatten_builtin_arity_1(error_context::in, mzn_anns::in, string::in,
    mzn_raw_expr::in,
    mzn_raw_expr::out, env::in, env::out) is semidet.

flatten_builtin_arity_1(Context, Anns, OpStr, RawMZA, RawMZ, !Env) :-
    (
        RawMZA = bool_expr(A),
        ( if
            is_bool_to_bool_op(OpStr, Op),
            flatten_bool_to_bool(Context, Anns, Op, A, Z, !Env)
        then
            RawMZ = bool_expr(Z)
        else if
            is_bool_to_int_op(OpStr, Op),
            flatten_bool_to_int(Context, Anns, Op, A, Z, !Env)
        then
            RawMZ = int_expr(Z)
        else
            fail
        )
    ;
        RawMZA = float_expr(A),
        ( if
            is_float_to_float_op(OpStr, Op),
            flatten_float_to_float(Context, Anns, Op, A, Z, !Env)
        then
            RawMZ = float_expr(Z)
        else if
            is_float_to_int_op(OpStr, Op),
            flatten_float_to_int(Context, Anns, Op, A, Z, !Env)
        then
            RawMZ = int_expr(Z)
        else if
            is_float_to_float_set_op(OpStr, Op),
            flatten_float_to_float_set(Context, Anns, Op, A, Z, !Env)
        then
            RawMZ = float_set_expr(Z)
        else
            fail
        )
    ;
        RawMZA = int_expr(A),
        ( if
            is_int_to_float_op(OpStr, Op),
            flatten_int_to_float(Context, Anns, Op, A, Z, !Env)
        then
            RawMZ = float_expr(Z)
        else if
            is_int_to_int_op(OpStr, Op),
            flatten_int_to_int(Context, Anns, Op, A, Z, !Env)
        then
            RawMZ = int_expr(Z)
        else if
            is_int_to_int_set_op(OpStr, Op),
            flatten_int_to_int_set(Context, Anns, Op, A, Z, !Env)
        then
            RawMZ = int_set_expr(Z)
        else
            fail
        )
    ;
        RawMZA = bool_set_expr(A),
        ( if
            is_set_to_int_op(OpStr, Op),
            flatten_set_to_int(Context, Anns, Op, A, Z, !Env)
        then
            RawMZ = int_expr(Z)
        else
            fail
        )
    ;
        RawMZA = float_set_expr(A),
        ( if
            is_set_to_int_op(OpStr, Op),
            flatten_set_to_int(Context, Anns, Op, A, Z, !Env)
        then
            RawMZ = int_expr(Z)
        else
            fail
        )
    ;
        RawMZA = int_set_expr(A),
        ( if
            is_set_to_int_op(OpStr, Op),
            flatten_set_to_int(Context, Anns, Op, A, Z, !Env)
        then
            RawMZ = int_expr(Z)
        else if
            is_int_set_to_int_op(OpStr, Op),
            flatten_int_set_to_int(Context, Anns, Op, A, Z, !Env)
        then
            RawMZ = int_expr(Z)
        else if
            is_int_set_to_int_set_op(OpStr, Op),
            flatten_int_set_to_int_set(Context, Anns, Op, A, Z, !Env)
        then
            RawMZ = int_set_expr(Z)
        else if
            is_set_to_array_op(OpStr, Op),
            flatten_int_set_to_array(Context, Anns, Op, A, Z, !Env)
        then
            RawMZ = int_array_expr(Z)
        else
            fail
        )
    ;
        RawMZA = bool_array_expr(A),
        ( if
            is_bool_array_to_bool_op(OpStr, Op),
            flatten_bool_array_to_bool(Context, Anns, Op, A, Z, !Env)
        then
            RawMZ = bool_expr(Z)
        else if
            flatten_arbitrary_array_to_int(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_expr(Z)
        else if
            flatten_array_to_int_set(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_set_expr(Z)
        else
            fail
        )
    ;
        RawMZA = float_array_expr(A),
        ( if
            flatten_float_array_to_float(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = float_expr(Z)
        else if
            flatten_arbitrary_array_to_int(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_expr(Z)
        else if
            flatten_array_to_int_set(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_set_expr(Z)
        else
            fail
        )
    ;
        RawMZA = int_array_expr(A),
        ( if
            flatten_int_array_to_int(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_expr(Z)
        else if
            flatten_arbitrary_array_to_int(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_expr(Z)
        else if
            flatten_array_to_int_set(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_set_expr(Z)
        else
            fail
        )
    ;
        RawMZA = bool_set_array_expr(A),
        ( if
            flatten_array_to_int_set(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_set_expr(Z)
        else if
            flatten_arbitrary_array_to_int(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_expr(Z)
        else if
            flatten_bool_set_array_to_set(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = bool_set_expr(Z)
        else
            fail
        )
    ;
        RawMZA = float_set_array_expr(A),
        ( if
            flatten_array_to_int_set(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_set_expr(Z)
        else if
            flatten_arbitrary_array_to_int(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_expr(Z)
        else if
            flatten_float_set_array_to_set(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = float_set_expr(Z)
        else
            fail
        )
    ;
        RawMZA = int_set_array_expr(A),
        ( if
            flatten_array_to_int_set(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_set_expr(Z)
        else if
            flatten_arbitrary_array_to_int(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_expr(Z)
        else if
            flatten_int_set_array_to_set(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_set_expr(Z)
        else
            fail
        )
    ;
        RawMZA = ann_array_expr(A),
        ( if
            flatten_array_to_int_set(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_set_expr(Z)
        else if
            flatten_arbitrary_array_to_int(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_expr(Z)
        else
            fail
        )
    ;
        RawMZA = string_array_expr(A),
        ( if
            flatten_array_to_int_set(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_set_expr(Z)
        else if
            flatten_string_array_to_string(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = string_expr(Z)
        else if
            flatten_arbitrary_array_to_int(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_expr(Z)
        else
            fail
        )
    ;
        RawMZA = bottom_array_expr(A),
        ( if
            flatten_array_to_int_set(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_set_expr(Z)
        else if
            flatten_arbitrary_array_to_int(Context, Anns, OpStr, A, Z, !Env)
        then
            RawMZ = int_expr(Z)
        else
            fail
        )
    ).

:- pred flatten_builtin_arity_2(error_context::in, mzn_anns::in, string::in,
    mzn_expr::in, mzn_expr::in,
    mzn_raw_expr::in, mzn_raw_expr::in,
    mzn_raw_expr::out, env::in, env::out) is semidet.

flatten_builtin_arity_2(Context, Anns, OpStr, MZA, MZB, RawMZA, RawMZB, RawMZ,
        !Env) :-
    (
        RawMZA = bool_expr(A),
        RawMZB = bool_expr(B),
        ( if
            is_bool_bool_to_bool_op(OpStr, Op),
            flatten_bool_bool_to_bool(Context, Anns, Op, A, B, Z, !Env)
        then
            RawMZ = bool_expr(Z)
        else
            fail
        )
    ;
        RawMZA = float_expr(A),
        RawMZB = float_expr(B),
        ( if
            is_float_float_to_float_op(OpStr, Op),
            flatten_float_float_to_float(Context, Anns, Op, A, B, Z, !Env)
        then
            RawMZ = float_expr(Z)
        else if
            is_float_float_to_float_set_op(OpStr, Op),
            flatten_float_float_to_float_set(Context, Anns, Op, A, B, Z, !Env)
        then
            RawMZ = float_set_expr(Z)
        else if
            is_float_float_to_bool_op(OpStr, Op),
            flatten_float_float_to_bool(Context, Anns, Op, A, B, CVZ, !Env)
        then
            RawMZ = bool_expr(bool_const_or_var_to_expr(CVZ))
        else
            fail
        )
    ;
        RawMZA = float_expr(A),
        RawMZB = float_set_expr(B),
        ( if
            is_float_float_set_to_bool_op(OpStr, Op),
            flatten_float_float_set_to_bool(Context, Anns, Op, A, B, BoolZ,
                !Env)
        then
            RawMZ = bool_expr(bool_const(BoolZ))
        else
            fail
        )
    ;
        RawMZA = int_expr(A),
        RawMZB = int_expr(B),
        ( if
            is_int_int_to_int_op(OpStr, Op),
            flatten_int_int_to_int(Context, Anns, Op, A, B, Z, !Env)
        then
            RawMZ = int_expr(Z)
        else if
            is_int_int_to_int_set_op(OpStr, Op),
            flatten_int_int_to_int_set(Context, Anns, Op, A, B, Z, !Env)
        then
            RawMZ = int_set_expr(Z)
        else if
            is_int_int_to_bool_op(OpStr, Op),
            flatten_int_int_to_bool(Context, Anns, Op, A, B, CVZ, !Env)
        then
            RawMZ = bool_expr(bool_const_or_var_to_expr(CVZ))
        else
            fail
        )
    ;
        RawMZA = int_expr(A),
        RawMZB = int_set_expr(B),
        ( if
            is_int_int_set_to_bool_op(OpStr, Op),
            flatten_int_int_set_to_bool(Context, Anns, Op, A, B, CVZ, !Env)
        then
            RawMZ = bool_expr(bool_const_or_var_to_expr(CVZ))
        else
            fail
        )
    ;
        RawMZA = bool_set_expr(A),
        RawMZB = bool_set_expr(B),
        ( if
            is_set_set_to_bool_op(OpStr, Op),
            flatten_set_set_to_bool(Context, Anns, Op, A, B, CVZ, !Env)
        then
            RawMZ = bool_expr(bool_const_or_var_to_expr(CVZ))
        else
            fail
        )
    ;
        RawMZA = float_set_expr(A),
        RawMZB = float_set_expr(B),
        ( if
            is_set_set_to_bool_op(OpStr, Op),
            flatten_set_set_to_bool(Context, Anns, Op, A, B, CVZ, !Env)
        then
            RawMZ = bool_expr(bool_const_or_var_to_expr(CVZ))
        else
            fail
        )
    ;
        RawMZA = bool_array_expr(A),
        RawMZB = bool_array_expr(B),
        ( if
            flatten_array_array_to_bool(fully_deref_bool_array,
                bool_to_mzn_expr,
                Context, Anns, OpStr, MZA, MZB, A, B, Z, !Env)
        then
            RawMZ = bool_expr(Z)
        else if
            flatten_array_array_to_array(fully_deref_bool_array,
                ( func(V) = bool_var(V) ),
                Context, Anns, OpStr, A, B, Z, !Env)
        then
            RawMZ = bool_array_expr(Z)
        else
            fail
        )
    ;
        RawMZA = bool_set_array_expr(A),
        RawMZB = bool_set_array_expr(B),
        ( if
            flatten_array_array_to_bool(fully_deref_bool_set_array,
                bool_set_to_mzn_expr,
                Context, Anns, OpStr, MZA, MZB, A, B, Z, !Env)
        then
            RawMZ = bool_expr(Z)
        else if
            flatten_array_array_to_array(fully_deref_bool_set_array,
                ( func(V) = set_var(V) ),
                Context, Anns, OpStr, A, B, Z, !Env)
        then
            RawMZ = bool_set_array_expr(Z)
        else
            fail
        )
    ;
        RawMZA = float_array_expr(A),
        RawMZB = float_array_expr(B),
        ( if
            flatten_array_array_to_bool(fully_deref_float_array,
                float_to_mzn_expr,
                Context, Anns, OpStr, MZA, MZB, A, B, Z, !Env)
        then
            RawMZ = bool_expr(Z)
        else if
            flatten_array_array_to_array(fully_deref_float_array,
                ( func(V) = float_var(V) ),
                Context, Anns, OpStr, A, B, Z, !Env)
        then
            RawMZ = float_array_expr(Z)
        else
            fail
        )
    ;
        RawMZA = float_set_array_expr(A),
        RawMZB = float_set_array_expr(B),
        ( if
            flatten_array_array_to_bool(fully_deref_float_set_array,
                float_set_to_mzn_expr,
                Context, Anns, OpStr, MZA, MZB, A, B, Z, !Env)
        then
            RawMZ = bool_expr(Z)
        else if
            flatten_array_array_to_array(fully_deref_float_set_array,
                ( func(V) = set_var(V) ),
                Context, Anns, OpStr, A, B, Z, !Env)
        then
            RawMZ = float_set_array_expr(Z)
        else
            fail
        )
    ;
        RawMZA = int_array_expr(A),
        RawMZB = int_array_expr(B),
        ( if
            flatten_array_array_to_bool(fully_deref_int_array,
                int_to_mzn_expr,
                Context, Anns, OpStr, MZA, MZB, A, B, Z, !Env)
        then
            RawMZ = bool_expr(Z)
        else if
            flatten_array_array_to_array(fully_deref_int_array,
                ( func(V) = int_var(V) ),
                Context, Anns, OpStr, A, B, Z, !Env)
        then
            RawMZ = int_array_expr(Z)
        else
            fail
        )
    ;
        RawMZA = int_set_array_expr(A),
        RawMZB = int_set_array_expr(B),
        ( if
            flatten_array_array_to_bool(fully_deref_int_set_array,
                int_set_to_mzn_expr,
                Context, Anns, OpStr, MZA, MZB, A, B, Z, !Env)
        then
            RawMZ = bool_expr(Z)
        else if
            flatten_array_array_to_array(fully_deref_int_set_array,
                ( func(V) = set_var(V) ),
                Context, Anns, OpStr, A, B, Z, !Env)
        then
            RawMZ = int_set_array_expr(Z)
        else
            fail
        )
    ;
        RawMZA = string_array_expr(A),
        RawMZB = string_array_expr(B),
        ( if
            flatten_array_array_to_bool(fully_deref_string_array,
                string_to_mzn_expr,
                Context, Anns, OpStr, MZA, MZB, A, B, Z, !Env)
        then
            RawMZ = bool_expr(Z)
        else if
            flatten_array_array_to_array(fully_deref_string_array,
                ( func(_) = _ :-
                    minizinc_internal_error(Context, $pred, "gadzooks!")
                ),
                Context, Anns, OpStr, A, B, Z, !Env)
        then
            RawMZ = string_array_expr(Z)
        else
            fail
        )
    ;
        RawMZA = ann_expr(A),
        RawMZB = ann_expr(B),
        flatten_ann_ann_to_bool(Context, Anns, OpStr, A, B, Z, !Env),
        RawMZ = bool_expr(Z)
    ;
        RawMZA = ann_array_expr(A),
        RawMZB = ann_array_expr(B),
        ( if
            flatten_array_array_to_bool(fully_deref_ann_array,
                ann_to_mzn_expr,
                Context, Anns, OpStr, MZA, MZB, A, B, Z, !Env)
        then
            RawMZ = bool_expr(Z)
        else if
            flatten_array_array_to_array(fully_deref_ann_array,
                ( func(_) = _ :-
                    minizinc_internal_error(Context, $pred, "gadzooks!")
                ),
                Context, Anns, OpStr, A, B, Z, !Env)
        then
            RawMZ = ann_array_expr(Z)
        else
            fail
        )
    ;
        RawMZA = string_expr(A),
        RawMZB = string_expr(B),
        ( if
            is_string_string_to_string_op(OpStr, Op),
            flatten_string_string_to_string(Context, Anns, Op, A, B, Z, !Env)
        then
            RawMZ = string_expr(Z)
        else if
            is_string_string_to_bool_op(OpStr, Op),
            flatten_string_string_to_bool(Context, Anns, Op, A, B, BoolZ,
                !Env)
        then
            RawMZ = bool_expr(bool_const(BoolZ))
        else
            fail
        )
    ;
        RawMZA = string_expr(A),
        RawMZB = string_array_expr(B),
        ( if
            flatten_string_string_array_to_string(Context, Anns, OpStr,
                A, B, Z, !Env)
        then
            RawMZ = string_expr(Z)
        else
            fail
        )
    ;
        RawMZA = int_set_expr(A),
        (
            RawMZB = bool_array_expr(B),
            flatten_array_redim(Context, Anns, OpStr, [A], B, Z, !Env),
            RawMZ = bool_array_expr(Z)
        ;
            RawMZB = float_array_expr(B),
            flatten_array_redim(Context, Anns, OpStr, [A], B, Z, !Env),
            RawMZ = float_array_expr(Z)
        ;
            RawMZB = int_array_expr(B),
            flatten_array_redim(Context, Anns, OpStr, [A], B, Z, !Env),
            RawMZ = int_array_expr(Z)
        ;
            RawMZB = string_array_expr(B),
            flatten_array_redim(Context, Anns, OpStr, [A], B, Z, !Env),
            RawMZ = string_array_expr(Z)
        ;
            RawMZB = bool_set_array_expr(B),
            flatten_array_redim(Context, Anns, OpStr, [A], B, Z, !Env),
            RawMZ = bool_set_array_expr(Z)
        ;
            RawMZB = float_set_array_expr(B),
            flatten_array_redim(Context, Anns, OpStr, [A], B, Z, !Env),
            RawMZ = float_set_array_expr(Z)
        ;
            RawMZB = int_set_array_expr(B),
            flatten_array_redim(Context, Anns, OpStr, [A], B, Z, !Env),
            RawMZ = int_set_array_expr(Z)
        ;
            RawMZB = bottom_array_expr(B),
            flatten_array_redim(Context, Anns, OpStr, [A], B, Z, !Env),
            RawMZ = bottom_array_expr(Z)
        ;
            RawMZB = int_set_expr(B),
            ( if
                is_set_set_to_bool_op(OpStr, Op),
                flatten_set_set_to_bool(Context, Anns, Op, A, B, CVZ, !Env)
            then
                RawMZ = bool_expr(bool_const_or_var_to_expr(CVZ))
            else if
                is_set_set_to_set_op(OpStr, Op),
                flatten_set_set_to_set(Context, Anns, Op, A, B, Z, !Env)
            then
                RawMZ = int_set_expr(Z)
            else
                fail
            )
        )
    ).

:- pred flatten_builtin_arity_3(error_context::in, mzn_anns::in, string::in,
    mzn_raw_expr::in, mzn_raw_expr::in, mzn_raw_expr::in,
    mzn_raw_expr::out, env::in, env::out) is semidet.

flatten_builtin_arity_3(Context, Anns, Op, RawMZA, RawMZB, RawMZC, RawMZ,
        !Env) :-
    RawMZA = int_set_expr(A),
    RawMZB = int_set_expr(B),
    (
        RawMZC = bool_array_expr(C),
        flatten_array_redim(Context, Anns, Op, [A, B], C, Z, !Env),
        RawMZ = bool_array_expr(Z)
    ;
        RawMZC = float_array_expr(C),
        flatten_array_redim(Context, Anns, Op, [A, B], C, Z, !Env),
        RawMZ = float_array_expr(Z)
    ;
        RawMZC = int_array_expr(C),
        flatten_array_redim(Context, Anns, Op, [A, B], C, Z, !Env),
        RawMZ = int_array_expr(Z)
    ;
        RawMZC = string_array_expr(C),
        flatten_array_redim(Context, Anns, Op, [A, B], C, Z, !Env),
        RawMZ = string_array_expr(Z)
    ;
        RawMZC = bool_set_array_expr(C),
        flatten_array_redim(Context, Anns, Op, [A, B], C, Z, !Env),
        RawMZ = bool_set_array_expr(Z)
    ;
        RawMZC = float_set_array_expr(C),
        flatten_array_redim(Context, Anns, Op, [A, B], C, Z, !Env),
        RawMZ = float_set_array_expr(Z)
    ;
        RawMZC = int_set_array_expr(C),
        flatten_array_redim(Context, Anns, Op, [A, B], C, Z, !Env),
        RawMZ = int_set_array_expr(Z)
    ;
        RawMZC = bottom_array_expr(C),
        flatten_array_redim(Context, Anns, Op, [A, B], C, Z, !Env),
        RawMZ = bottom_array_expr(Z)
    ).

:- pred flatten_builtin_arity_4(error_context::in, mzn_anns::in, string::in,
    mzn_raw_expr::in, mzn_raw_expr::in, mzn_raw_expr::in,
    mzn_raw_expr::in,
    mzn_raw_expr::out, env::in, env::out) is semidet.

flatten_builtin_arity_4(Context, Anns, Op, RawMZA, RawMZB, RawMZC, RawMZD,
        RawMZ, !Env) :-
    RawMZA = int_set_expr(A),
    RawMZB = int_set_expr(B),
    RawMZC = int_set_expr(C),
    (
        RawMZD = bool_array_expr(D),
        flatten_array_redim(Context, Anns, Op, [A, B, C], D, Z, !Env),
        RawMZ = bool_array_expr(Z)
    ;
        RawMZD = float_array_expr(D),
        flatten_array_redim(Context, Anns, Op, [A, B, C], D, Z, !Env),
        RawMZ = float_array_expr(Z)
    ;
        RawMZD = int_array_expr(D),
        flatten_array_redim(Context, Anns, Op, [A, B, C], D, Z, !Env),
        RawMZ = int_array_expr(Z)
    ;
        RawMZD = string_array_expr(D),
        flatten_array_redim(Context, Anns, Op, [A, B, C], D, Z, !Env),
        RawMZ = string_array_expr(Z)
    ;
        RawMZD = bool_set_array_expr(D),
        flatten_array_redim(Context, Anns, Op, [A, B, C], D, Z, !Env),
        RawMZ = bool_set_array_expr(Z)
    ;
        RawMZD = float_set_array_expr(D),
        flatten_array_redim(Context, Anns, Op, [A, B, C], D, Z, !Env),
        RawMZ = float_set_array_expr(Z)
    ;
        RawMZD = int_set_array_expr(D),
        flatten_array_redim(Context, Anns, Op, [A, B, C], D, Z, !Env),
        RawMZ = int_set_array_expr(Z)
    ;
        RawMZD = bottom_array_expr(D),
        flatten_array_redim(Context, Anns, Op, [A, B, C], D, Z, !Env),
        RawMZ = bottom_array_expr(Z)
    ).

:- pred flatten_builtin_arity_5(error_context::in, mzn_anns::in, string::in,
    mzn_raw_expr::in, mzn_raw_expr::in, mzn_raw_expr::in,
    mzn_raw_expr::in, mzn_raw_expr::in,
    mzn_raw_expr::out, env::in, env::out) is semidet.

flatten_builtin_arity_5(Context, Anns, Op, RawMZA, RawMZB, RawMZC,
        RawMZD, RawMZE, RawMZ, !Env) :-
    RawMZA = int_set_expr(A),
    RawMZB = int_set_expr(B),
    RawMZC = int_set_expr(C),
    RawMZD = int_set_expr(D),
    (
        RawMZE = bool_array_expr(E),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D], E, Z, !Env),
        RawMZ = bool_array_expr(Z)
    ;
        RawMZE = float_array_expr(E),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D], E, Z, !Env),
        RawMZ = float_array_expr(Z)
    ;
        RawMZE = int_array_expr(E),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D], E, Z, !Env),
        RawMZ = int_array_expr(Z)
    ;
        RawMZE = string_array_expr(E),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D], E, Z, !Env),
        RawMZ = string_array_expr(Z)
    ;
        RawMZE = bool_set_array_expr(E),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D], E, Z, !Env),
        RawMZ = bool_set_array_expr(Z)
    ;
        RawMZE = float_set_array_expr(E),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D], E, Z, !Env),
        RawMZ = float_set_array_expr(Z)
    ;
        RawMZE = int_set_array_expr(E),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D], E, Z, !Env),
        RawMZ = int_set_array_expr(Z)
    ;
        RawMZE = bottom_array_expr(E),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D], E, Z, !Env),
        RawMZ = bottom_array_expr(Z)
    ).

:- pred flatten_builtin_arity_6(error_context::in, mzn_anns::in, string::in,
    mzn_raw_expr::in, mzn_raw_expr::in, mzn_raw_expr::in,
    mzn_raw_expr::in, mzn_raw_expr::in, mzn_raw_expr::in,
    mzn_raw_expr::out, env::in, env::out) is semidet.

flatten_builtin_arity_6(Context, Anns, Op, RawMZA, RawMZB, RawMZC,
        RawMZD, RawMZE, RawMZF, RawMZ, !Env) :-
    RawMZA = int_set_expr(A),
    RawMZB = int_set_expr(B),
    RawMZC = int_set_expr(C),
    RawMZD = int_set_expr(D),
    RawMZE = int_set_expr(E),
    (
        RawMZF = bool_array_expr(F),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D, E], F, Z, !Env),
        RawMZ = bool_array_expr(Z)
    ;
        RawMZF = float_array_expr(F),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D, E], F, Z, !Env),
        RawMZ = float_array_expr(Z)
    ;
        RawMZF = int_array_expr(F),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D, E], F, Z, !Env),
        RawMZ = int_array_expr(Z)
    ;
        RawMZF = string_array_expr(F),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D, E], F, Z, !Env),
        RawMZ = string_array_expr(Z)
    ;
        RawMZF = bool_set_array_expr(F),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D, E], F, Z, !Env),
        RawMZ = bool_set_array_expr(Z)
    ;
        RawMZF = float_set_array_expr(F),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D, E], F, Z, !Env),
        RawMZ = float_set_array_expr(Z)
    ;
        RawMZF = int_set_array_expr(F),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D, E], F, Z, !Env),
        RawMZ = int_set_array_expr(Z)
    ;
        RawMZF = bottom_array_expr(F),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D, E], F, Z, !Env),
        RawMZ = bottom_array_expr(Z)
    ).

:- pred flatten_builtin_arity_7(error_context::in, mzn_anns::in, string::in,
    mzn_raw_expr::in, mzn_raw_expr::in, mzn_raw_expr::in,
    mzn_raw_expr::in, mzn_raw_expr::in, mzn_raw_expr::in, mzn_raw_expr::in,
    mzn_raw_expr::out, env::in, env::out) is semidet.

flatten_builtin_arity_7(Context, Anns, Op, RawMZA, RawMZB, RawMZC,
        RawMZD, RawMZE, RawMZF, RawMZG, RawMZ, !Env) :-
    RawMZA = int_set_expr(A),
    RawMZB = int_set_expr(B),
    RawMZC = int_set_expr(C),
    RawMZD = int_set_expr(D),
    RawMZE = int_set_expr(E),
    RawMZF = int_set_expr(F),
    (
        RawMZG = bool_array_expr(G),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D, E, F], G, Z, !Env),
        RawMZ = bool_array_expr(Z)
    ;
        RawMZG = float_array_expr(G),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D, E, F], G, Z, !Env),
        RawMZ = float_array_expr(Z)
    ;
        RawMZG = int_array_expr(G),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D, E, F], G, Z, !Env),
        RawMZ = int_array_expr(Z)
    ;
        RawMZG = string_array_expr(G),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D, E, F], G, Z, !Env),
        RawMZ = string_array_expr(Z)
    ;
        RawMZG = bool_set_array_expr(G),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D, E, F], G, Z, !Env),
        RawMZ = bool_set_array_expr(Z)
    ;
        RawMZG = float_set_array_expr(G),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D, E, F], G, Z, !Env),
        RawMZ = float_set_array_expr(Z)
    ;
        RawMZG = int_set_array_expr(G),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D, E, F], G, Z, !Env),
        RawMZ = int_set_array_expr(Z)
    ;
        RawMZG = bottom_array_expr(G),
        flatten_array_redim(Context, Anns, Op, [A, B, C, D, E, F], G, Z, !Env),
        RawMZ = bottom_array_expr(Z)
    ).

%-----------------------------------------------------------------------------%
%
% Flattening of fix/1 applications.
%

:- pred flatten_app_fix(error_context::in, error_context::in, expr::in,
    mzn_expr::out, env::in, env::out) is det.

flatten_app_fix(Context, AppContext, ArgExpr, MZ, !Env) :-
    % We need to handle 'fix' expressions specially.
    flatten_expr(Context, ArgExpr, MZ0, !Env),
    ( if flatten_is_fixed(!.Env, MZ0)
    then true
    else minizinc_user_error(AppContext, "Argument is not fixed.")
    ),
    %
    % If we have ``array[int] of var X: foo'' and have just flattened the
    % expression ``fix(foo)'' we *cannot* simply return foo, as the declared
    % inst.  This is because the FlatZinc we generate may not be inst-correct.
    % Instead we need to introduce a new temporary array parameter whose value
    % is the same as the fixed value of the original expression.
    % We do not need to do this for scalars since the will be substituted
    % directly.
    %
    MZ0 = mzn_expr(RawMZ0, Anns0),
    (
        RawMZ0 = bool_array_expr(BoolArrayExpr0),
        post_fix_array_expr(Context, BoolArrayExpr0, BoolArrayExpr,
            Anns0, Anns, !Env),
        RawMZ = bool_array_expr(BoolArrayExpr)
    ;
        RawMZ0 = float_array_expr(FloatArrayExpr0),
        post_fix_array_expr(Context, FloatArrayExpr0, FloatArrayExpr,
            Anns0, Anns, !Env),
        RawMZ = float_array_expr(FloatArrayExpr)
    ;
        RawMZ0 = int_array_expr(IntArrayExpr0),
        post_fix_array_expr(Context, IntArrayExpr0, IntArrayExpr,
            Anns0, Anns, !Env),
        RawMZ = int_array_expr(IntArrayExpr)
    ;
        RawMZ0 = int_set_array_expr(IntSetArrayExpr0),
        post_fix_array_expr(Context, IntSetArrayExpr0, IntSetArrayExpr,
            Anns0, Anns, !Env),
        RawMZ = int_set_array_expr(IntSetArrayExpr)
    ;
        ( RawMZ0 = bool_expr(_)
        ; RawMZ0 = bool_set_expr(_)
        ; RawMZ0 = bool_set_array_expr(_)   % Always par in MiniZinc.
        ; RawMZ0 = float_expr(_)
        ; RawMZ0 = float_set_expr(_)
        ; RawMZ0 = float_set_array_expr(_)  % Always par in MiniZinc.
        ; RawMZ0 = int_expr(_)
        ; RawMZ0 = int_set_expr(_)
        ; RawMZ0 = string_expr(_)
        ; RawMZ0 = string_array_expr(_)
        ; RawMZ0 = ann_expr(_)
        ; RawMZ0 = ann_array_expr(_)
        ; RawMZ0 = bottom_expr(_)
        ; RawMZ0 = bottom_array_expr(_)    %  Cannot fix this.
        ),
        RawMZ = RawMZ0,
        Anns = Anns0
    ),
    MZ = mzn_expr(RawMZ, Anns).

:- pred post_fix_array_expr(error_context::in,
    array_expr(T)::in, array_expr(T)::out,
    mzn_anns::in, mzn_anns::out, env::in, env::out) is det.

post_fix_array_expr(Context, !ArrayExpr, !Anns, !Env) :-
    (
        !.ArrayExpr = array_items(_, _)
    ;
        !.ArrayExpr = array_var(IndexRanges, VarId),
        Inst = !.Env ^ var_inst(VarId), 
        (
            Inst = var_is_var,
            Type = !.Env ^ var_type(VarId),
            new_tmp_var_id("FIX", TmpVarId, !Env),
            add_global_par(TmpVarId, Type, IndexRanges, !Env),
            ( if Value = !.Env ^ var_value(VarId) then
                !Env ^ var_value(TmpVarId) := Value,
                !:ArrayExpr = array_var(IndexRanges, TmpVarId),
                % The new temporary parameter should no inherit the
                % annotations from the original expression.
                set.init(!:Anns)
            else
                % We should never get here because fix/1 should abort
                % if the variable has no assignment and we have already
                % checked for that.
                minizinc_internal_error(Context, $pred,
                    "fix/1 did not abort but no assignment?.\n")
            )    
        ;
            Inst = var_is_par
            % Do nothing if it is a parameter.
        )       
    ).

%-----------------------------------------------------------------------------%
%
% Implementation of is_fixed/1.
%

% XXX should be func returning bool
:- pred flatten_is_fixed(env::in, mzn_expr::in) is semidet.

flatten_is_fixed(Env, Expr) :-
    Expr = mzn_expr(RawExpr, _),
    require_complete_switch [RawExpr] (
        RawExpr = bool_expr(BoolExpr),
        bool_expr_is_fixed(Env, BoolExpr)
    ; 
        RawExpr = bool_array_expr(BoolArrayExpr),
        array_expr_is_fixed(bool_expr_is_fixed(Env), Env, BoolArrayExpr)
    ;
        RawExpr = float_expr(FloatExpr),
        float_expr_is_fixed(Env, FloatExpr)
    ;
        RawExpr = float_array_expr(FloatArrayExpr),
        array_expr_is_fixed(float_expr_is_fixed(Env), Env, FloatArrayExpr)
    ;
        RawExpr = int_expr(IntExpr),
        int_expr_is_fixed(Env, IntExpr)
    ;
        RawExpr = int_set_expr(IntSetExpr),
        int_set_expr_is_fixed(Env, IntSetExpr)
    ;
        RawExpr = int_array_expr(IntArrayExpr),
        array_expr_is_fixed(int_expr_is_fixed(Env), Env, IntArrayExpr)
    ;
        RawExpr = int_set_array_expr(IntSetArrayExpr),
        array_expr_is_fixed(int_set_expr_is_fixed(Env), Env, IntSetArrayExpr)
    ;
        % The following may only be par values in MiniZinc.
        ( RawExpr = bool_set_array_expr(_)
        ; RawExpr = bool_set_expr(_)
        ; RawExpr = float_set_expr(_)
        ; RawExpr = float_set_array_expr(_)
        ; RawExpr = string_expr(_)
        ; RawExpr = string_array_expr(_)
        )
    ; 
        % XXX Should annotations be an error instead?
        ( RawExpr = ann_expr(_) 
        ; RawExpr = ann_array_expr(_)
        ; RawExpr = bottom_expr(_)
        ),
        false
    ;
        RawExpr = bottom_array_expr(BottomArrayExpr),
        % Corner case: is_fixed([]) should flatten to true.
        BottomArrayExpr = array_items(_, Array),
        array.size(Array, 0)
    ).      

:- pred bool_expr_is_fixed(env::in, bool_expr::in) is semidet.

bool_expr_is_fixed(Env, Expr) :-
    require_complete_switch [Expr] (
        Expr = bool_const(_)
    ;
        Expr = bool_var(MznVar),
        mzn_var_is_fixed(Env, MznVar)
    ;
        ( Expr = bool_conj(BoolExprs)   
        ; Expr = bool_disj(BoolExprs)
        ),
        list.all_true(bool_expr_is_fixed(Env), BoolExprs)
    ).

:- pred float_expr_is_fixed(env::in, float_expr::in) is semidet.

float_expr_is_fixed(Env, Expr) :-
    require_complete_switch [Expr] (
        (
            Expr = float_const(_)
        ;
            Expr = float_var(MznVar),
            mzn_var_is_fixed(Env, MznVar)
        ;
            Expr = X + Y,
            float_expr_is_fixed(Env, X),
            float_expr_is_fixed(Env, Y)
        ;
            Expr = _Const * ExprPrime,
            float_expr_is_fixed(Env, ExprPrime)
        )
    ).    

:- pred int_expr_is_fixed(env::in, int_expr::in) is semidet.

int_expr_is_fixed(Env, Expr) :-
    require_complete_switch [Expr] (
        (
            Expr = int_const(_)
        ;
            Expr = int_var(MznVar),
            mzn_var_is_fixed(Env, MznVar)
        ;
            Expr = X + Y,
            int_expr_is_fixed(Env, X),
            int_expr_is_fixed(Env, Y)
        ;
            Expr = _Const * ExprPrime,
            int_expr_is_fixed(Env, ExprPrime)
        )
    ).

:- pred int_set_expr_is_fixed(env::in, int_set_expr::in) is semidet.

int_set_expr_is_fixed(Env, Expr) :-
    require_complete_switch [Expr] (
        Expr = set_items(_)
    ;
        Expr = set_var(MznVar),
        mzn_var_is_fixed(Env, MznVar)
    ).

:- pred mzn_var_is_fixed(env::in, mzn_var::in) is semidet.

mzn_var_is_fixed(Env, Var) :-
    require_complete_switch [Var] (
        Var = var_no_index(VarId),
        Value = Env ^ var_value(VarId),
        flatten_is_fixed(Env, Value) 
    ;
        Var = var_index(_, _),
        false
    ).

:- pred array_expr_is_fixed(pred(T)::in(pred(in) is semidet),
    env::in, array_expr(T)::in) is semidet.

array_expr_is_fixed(IsElemFixed, Env, Expr) :-
    require_complete_switch [Expr] (
        Expr = array_items(_, ElemArray),
        % XXX We need array.all_true in stdlib.
        Exprs = array.to_list(ElemArray),
        list.all_true(IsElemFixed, Exprs)
    ;
        Expr = array_var(_, VarId),
        Value = Env ^ var_value(VarId),
        flatten_is_fixed(Env, Value)
    ).

%-----------------------------------------------------------------------------%
:- end_module flatten.expr.
%-----------------------------------------------------------------------------%
