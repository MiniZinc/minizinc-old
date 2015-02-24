%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
% Flatten a Zinc AST expr into an mzn_expr.
%
%-----------------------------------------------------------------------------%

:- module hr.expr.
:- interface.

:- import_module errors.
:- import_module hr.info.
:- import_module types.

:- import_module zinc_ast.

%-----------------------------------------------------------------------------%

    % Flatten an expression representing a MiniZinc constraint.
    %
:- pred halfreify_constraint(error_context::in, mzn_anns::in, ilhs::in,
    expr::in, mzn_expr::out, mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

    % Flatten an expression representing a MiniZinc term.
    %
:- pred halfreify_term(error_context::in, mzn_anns::in, ilhs::in,
    expr::in, mzn_expr::out, mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

    % Flatten an arbitrary expression which may represent a constraint
    % or a term, but the caller does not know which.
    %
:- pred halfreify_expr(error_context::in, mzn_anns::in, ilhs::in,
    expr::in, mzn_expr::out, mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module common_array.
:- import_module common_format.
:- import_module global_vars.
:- import_module hr.array.
:- import_module hr.convert.
:- import_module hr.string.
:- import_module utilities.
% :- import_module flatten.ann.
% :- import_module flatten.app.
% :- import_module flatten.array.
% :- import_module flatten.bool.
% :- import_module flatten.comp.
% :- import_module flatten.float.
% :- import_module flatten.int.
% :- import_module flatten.let.
% :- import_module flatten.set.

:- import_module types_and_insts.
:- import_module zinc_common.

:- import_module array.
:- import_module bool.
:- import_module float.
:- import_module io.
:- import_module list.
:- import_module map.
:- import_module maybe.
:- import_module set.
:- import_module string.

%-----------------------------------------------------------------------------%

halfreify_constraint(Context, OutsideAnns, ILHS, Expr, MZ,
        AllConstraints, KnownFalse, !Info, !Model) :-
    halfreify_any_expr(expr_is_constraint, Context, OutsideAnns,
        ILHS, Expr, MZ, AllConstraints, KnownFalse, !Info, !Model).

halfreify_term(Context, OutsideAnns, ILHS, Expr, MZ,
        AllConstraints, KnownFalse, !Info, !Model) :-
    halfreify_any_expr(expr_is_term, Context, OutsideAnns,
        ILHS, Expr, MZ, AllConstraints, KnownFalse, !Info, !Model).

halfreify_expr(Context, OutsideAnns, ILHS, Expr, MZ,
        AllConstraints, KnownFalse, !Info, !Model) :-
    halfreify_any_expr(expr_kind_unknown, Context, OutsideAnns,
        ILHS, Expr, MZ, AllConstraints, KnownFalse, !Info, !Model).

%-----------------------------------------------------------------------------%

:- type constr_or_term
    --->    expr_is_constraint
    ;       expr_is_term
    ;       expr_kind_unknown.

    % This predicate does the job of both halfreify_constraint and
    % halfreify_term from the half-reification paper. The reason why
    % it does the job of both is that some Zinc syntactic constructs
    % can stand for constraints in some contexts (e.g. a bool var that
    % is constrainted to be true) and for terms in other contexts (e.g.
    % any non-bool var), and the Zinc AST does not cleanly distinguish
    % between the two. (It should, but it doesn't.)
    %
:- pred halfreify_any_expr(constr_or_term::in, error_context::in, mzn_anns::in,
    ilhs::in, expr::in, mzn_expr::out,
    mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

halfreify_any_expr(ConstrOrTerm, Context, OutsideAnns, ILHS, Expr, MZ,
        AllConstraints, KnownFalse, !Info, !Model) :-
    Expr = expr(RawExpr, AnnExprs, ExprInfo),
    ExprInfo = expr_info(_SrcLocn, TI),
    hr_flatten_anns(Context, OutsideAnns, ILHS, AnnExprs, ExprAnns,
        !Info, !Model),
    InsideAnns = join_anns(ExprAnns, OutsideAnns),

    (
        % ConstrOrTerm does not need to have any particular value here.
        RawExpr = ident(VarId),
        hr_lookup_ident(!.Info, !.Model, VarId, MZ),
        mzn_constraint_set_empty(AllConstraints),
        KnownFalse = not_known_to_be_false
    ;
        % halfreify_term
        RawExpr = lit(Literal),
        hr_lookup_literal(Literal, MZ),
        mzn_constraint_set_empty(AllConstraints),
        KnownFalse = not_known_to_be_false
    ;
        % halfreify_cons
        RawExpr = app(_AppId, _ProcNo, _AppKind, _ArgExprs),
        minizinc_internal_error(Context, $pred,
            "app NYI\n")
        % _PredName = id_name(AppId),
        % hr_flatten_app(Context, PredName, ProcNo, ArgExprs, MZ,
        %   ALlConstraints, KnownFalse, !Info, !Model)
    ;
        RawExpr = array_access(ArrayExpr, IndexExprs),
        minizinc_require_match(Context, ConstrOrTerm,
            [expr_is_term, expr_kind_unknown],
            $pred, "array access treated as constraint"),
        % XXX Can an access to an array of bools be a constraint?

        halfreify_term(Context, InsideAnns, ILHS, ArrayExpr, MZA,
            ArrayConstraints, ArrayKnownFalse, !Info, !Model),
        % XXX paper says flatten_term for the subscript expressions.
        % XXX What if a subscript contains an array access as well?
        % XXX similarly for the arguments of arithmetic operations.
        list.map3_foldl2(halfreify_term(Context, InsideAnns, ILHS),
            IndexExprs, IndexMZs, ArgConstraintSets, ArgKnownFalses,
            !Info, !Model),
        halfreify_array_access(Context, InsideAnns, ILHS, TI,
            MZA, IndexMZs, MZ, AccessConstraints, AccessKnownFalse,
            !Info, !Model),
        % AccessConstraints = set_tree234.init,
        % MZ = mzn_expr(bool_expr(bool_const(yes)), set.init),
        mzn_constraint_set_union_list(
            [ArrayConstraints, AccessConstraints | ArgConstraintSets],
            AllConstraints),
        KnownFalse = combine_known_to_be_false_list(
            [ArrayKnownFalse, AccessKnownFalse | ArgKnownFalses])
    ;
        % halfreify_term
        RawExpr = lit_set(_ItemExprs),
        minizinc_internal_error(Context, $pred,
            "lit_set NYI\n")
        % hr_flatten_lit_set(Context, InsideAnns, TI, ItemExprs, MZ,
        %     !Info, !Model)
    ;
        % halfreify_term
        RawExpr = lit_simple_array(_ItemExprs),
        minizinc_internal_error(Context, $pred,
            "lit_simple_array NYI\n")
        % hr_flatten_lit_array(Context, InsideAnns, TI, ItemExprs, MZ,
        %     !Info, !Model)
    ;
        % halfreify_term
        RawExpr = lit_ann(AnnId, ArgExprs),
        AnnName = AnnId ^ id_name,
        halfreify_ann(Context, InsideAnns, ILHS, AnnName, ArgExprs, MZ0,
            AllConstraints, KnownFalse, !Info, !Model),
        MZ0 = mzn_expr(RawMZ, AnnAnns),
        MZ = mzn_expr(RawMZ, join_anns(ExprAnns, AnnAnns))
    ;
        % halfreify_cons
        RawExpr = comprehension(_CompKind, _Generators, _MaybeCondExpr),
        minizinc_internal_error(Context, $pred,
            "comprehension NYI\n")
        % hr_flatten_comp_not_reified(Context, InsideAnns, TI, CompKind,
        %     Generators, MaybeCondExpr, MZ, !Info, !Model)
    ;
        % halfreify_term
        RawExpr = anon_var,
        minizinc_internal_error(Context, $pred,
            "anon_var NYI\n")
        % hr_flatten_anon_var_not_reified(Context, InsideAnns, TI, MZ,
        %     !Info, !Model)
    ;
        % halfreify_cons
        RawExpr = if_then_else(_CondExpr, _ThenExpr, _ElseExpr),
        minizinc_internal_error(Context, $pred,
            "if_then_else NYI\n")
        % hr_flatten_if_then_else_not_reified(Context, InsideAnns,
        %     CondExpr, ThenExpr, ElseExpr, MZ, !Info, !Model)
    ;
        % halfreify_cons
        RawExpr = let(_LetVars, _LetExpr),
        minizinc_internal_error(Context, $pred,
            "let NYI\n")
        % hr_flatten_let_expr_not_reified(Context, InsideAnns,
        %     LetVars, LetExpr, MZ, !Info, !Model)
    ;
        % halfreify_cons
        RawExpr = coerce(_FromTI, _ToTI, _CoerceExpr),
        minizinc_internal_error(Context, $pred,
            "coerce NYI\n")
        % hr_flatten_coerce_not_reified(Context, InsideAnns,
        %     FromTI, ToTI, CoerceExpr, MZ, !Info, !Model)
    ;
        RawExpr = lit_tuple(_),
        minizinc_internal_error(Context, $pred,
            "Non-MiniZinc syntax item.\n")
    ).

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
:- pred hr_lookup_ident(hr_info::in, model::in, var_id::in, mzn_expr::out)
    is det.

hr_lookup_ident(Info, Model, VarId, MZ) :-
    LocalVarMap = hr_info_get_local_var_map(Info),
    ( if map.search(LocalVarMap, VarId, MZ0) then
        MZ = MZ0
    else
        GlobalVarMap = Model ^ model_globals,
        map.lookup(GlobalVarMap, VarId, VarInfo),
        MaybeVarValue = VarInfo ^ vi_value,
        (
            MaybeVarValue = yes(MZ0),
            MZ0 = mzn_expr(RawMZ0, Anns),
            ( if
                (
                    RawMZ0 = bool_array_expr(array_items(IndexRanges, _)),
                    RawMZ  = bool_array_expr(array_var(IndexRanges, VarId))
                ;
                    RawMZ0 = float_array_expr(array_items(IndexRanges, _)),
                    RawMZ  = float_array_expr(array_var(IndexRanges, VarId))
                ;
                    RawMZ0 = int_array_expr(array_items(IndexRanges, _)),
                    RawMZ  = int_array_expr(array_var(IndexRanges, VarId))
                ;
                    RawMZ0 = bool_set_array_expr(array_items(IndexRanges, _)),
                    RawMZ  = bool_set_array_expr(array_var(IndexRanges, VarId))
                ;
                    RawMZ0 = float_set_array_expr(array_items(IndexRanges, _)),
                    RawMZ  = float_set_array_expr(array_var(IndexRanges, VarId))
                ;
                    RawMZ0 = int_set_array_expr(array_items(IndexRanges, _)),
                    RawMZ  = int_set_array_expr(array_var(IndexRanges, VarId))
                )
              then
                MZ = mzn_expr(RawMZ, Anns)
              else
                MZ = MZ0
            )
        ;
            MaybeVarValue = no,
            IndexRanges = VarInfo ^ vi_index_ranges,
            MZType = var_get_updated_var_type(VarInfo),
            MZ = make_var_mzn_expr(IndexRanges, MZType, VarId)
        )
    ).

%-----------------------------------------------------------------------------%

:- pred hr_lookup_literal(literal::in, mzn_expr::out) is det.

hr_lookup_literal(Literal, MZ) :-
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

% :- pred hr_flatten_lit_set(error_context::in, mzn_anns::in,
%     type_inst::in, exprs::in, mzn_expr::out,
%     hr_info::in, hr_info::out, model::in, model::in) is det.
% 
% hr_flatten_lit_set(Context, Anns, TI, ItemExprs, MZ, !Info, !Model) :-
%     (
%         ItemExprs = [],
%         ( if
%             TI = ti_par_set(ElemTI),
%             (
%                 ElemTI = ti_par_bool,
%                 MZ0 = bool_set_to_mzn_expr(set_items(set.init))
%             ;
%                 ElemTI = ti_par_float,
%                 MZ0 = float_set_to_mzn_expr(set_items(set.init))
%             ;
%                 ElemTI = ti_par_int,
%                 MZ0 = int_set_to_mzn_expr(set_items(set.init))
%             ;
%                 % This happens because the broken type inference algorithm
%                 % doesn't assign types to empty sets inside par-to-var
%                 % coercions. The only such sets can be int sets.
%                 %
%                 ElemTI = ti_par_bottom,
%                 MZ0 = int_set_to_mzn_expr(set_items(set.init))
%             )
%           then
%             MZ = MZ0
%           else
%             minizinc_user_error(Context,
%                 "This is not a valid MiniZinc set type.\n")
%         )
%     ;
%         ItemExprs = [_ | _],
%         list.map_foldl2(hr_flatten_expr(Context, Anns), ItemExprs, ItemMZs,
%             !Info, !Model),
%         ( if
%             TI = ti_par_set(ElemTI),
%             (
%                 ElemTI = ti_par_bool,
%                 Xs = list.map(mzn_expr_to_bool_const(Context), ItemMZs),
%                 Set = set.from_list(Xs),
%                 MZ0 = bool_set_to_mzn_expr(set_items(Set))
%             ;
%                 ElemTI = ti_par_float,
%                 Xs = list.map(mzn_expr_to_float_const(Context), ItemMZs),
%                 Set = set.from_list(Xs),
%                 MZ0 = float_set_to_mzn_expr(set_items(Set))
%             ;
%                 ElemTI = ti_par_int,
%                 Xs = list.map(mzn_expr_to_int_const(Context), ItemMZs),
%                 Set = set.from_list(Xs),
%                 MZ0 = int_set_to_mzn_expr(set_items(Set))
%             )
%           then
%             MZ = MZ0
%           else
%             minizinc_user_error(Context,
%                 "This is not a valid MiniZinc set type.\n")
%         )
%     ).

%-----------------------------------------------------------------------------%

% :- pred hr_flatten_lit_array(error_context::in,
%     type_inst::in, exprs::in, mzn_expr::out,
%     hr_info::in, hr_info::out, model::in, model::in) is det.
% 
% hr_flatten_lit_array(Context, TI, ItemExprs, MZ, !Info, !Model) :-
%     (
%         ItemExprs = [],
%         IndexRanges = [index_range(1, 0)],
%         ( if
%             TI = ti_array(_, ElemTI),
%             (
%                 ( ElemTI = ti_par_bool
%                 ; ElemTI = ti_var_bool
%                 ),
%                 Empty = array.make_empty_array,
%                 MZ0 = bool_array_to_mzn_expr(array_items(IndexRanges,
%                     Empty))
%             ;
%                 ( ElemTI = ti_par_float
%                 ; ElemTI = ti_var_float
%                 ),
%                 Empty = array.make_empty_array,
%                 MZ0 = float_array_to_mzn_expr(array_items(IndexRanges,
%                     Empty))
%             ;
%                 ( ElemTI = ti_par_int
%                 ; ElemTI = ti_var_int
%                 ),
%                 Empty = array.make_empty_array,
%                 MZ0 = int_array_to_mzn_expr(array_items(IndexRanges,
%                     Empty))
%             ;
%                 ElemTI = ti_par_set(ti_par_bool),
%                 Empty = array.make_empty_array,
%                 MZ0 = bool_set_array_to_mzn_expr(array_items(IndexRanges,
%                     Empty))
%             ;
%                 ElemTI = ti_par_set(ti_par_float),
%                 Empty = array.make_empty_array,
%                 MZ0 = float_set_array_to_mzn_expr(array_items(IndexRanges,
%                     Empty))
%             ;
%                 ( ElemTI = ti_var_set(ti_par_int)
%                 ; ElemTI = ti_par_set(ti_par_int)
%                 ),
%                 Empty = array.make_empty_array,
%                 MZ0 = int_set_array_to_mzn_expr(array_items(IndexRanges,
%                     Empty))
%             ;
%                 ElemTI = ti_par_string,
%                 Empty = array.make_empty_array,
%                 MZ0 = string_array_to_mzn_expr(array_items(IndexRanges,
%                     Empty))
%             ;
%                 ElemTI = ti_ann,
%                 Empty = array.make_empty_array,
%                 MZ0 = ann_array_to_mzn_expr(array_items(IndexRanges,
%                     Empty))
%             ;
%                 ElemTI = ti_par_bottom,
%                 Empty = array.make_empty_array,
%                 MZ0 = bottom_array_to_mzn_expr(array_items(IndexRanges,
%                     Empty))
%             )
%           then
%             MZ = MZ0
%           else
%             minizinc_user_error(Context,
%                 "This is not a valid MiniZinc array type.\n")
%         )
%     ;
%         ItemExprs = [_ | _],
%         N = list.length(ItemExprs),
%         IndexRanges = [index_range(1, N)],
%         % XXX HR
%         ( if TI = ti_array(_, ti_var_bool) then
%             list.foldl3(hr_flatten_expr_reified_acc(Context, Anns), ItemExprs,
%                 [], RevItemMZs, !Info, !Model)
%           else
%             list.foldl3(hr_flatten_expr_acc(Context), ItemExprs,
%                 [], RevItemMZs, !Info, !Model)
%         ),
%         ( if
%             TI = ti_array(_, ElemTI),
%             (
%                 ( ElemTI = ti_par_bool
%                 ; ElemTI = ti_var_bool
%                 ),
%                 list.foldl(mzn_expr_to_bool_acc(Context), RevItemMZs,
%                     [], BoolExprs),
%                 Xs = array(BoolExprs),
%                 MZ0 = bool_array_to_mzn_expr(array_items(IndexRanges, Xs))
%             ;
%                 ( ElemTI = ti_par_float
%                 ; ElemTI = ti_var_float
%                 ),
%                 list.foldl(mzn_expr_to_float_acc(Context), RevItemMZs,
%                     [], FloatExprs),
%                 Xs = array(FloatExprs),
%                 MZ0 = float_array_to_mzn_expr(array_items(IndexRanges, Xs))
%             ;
%                 ( ElemTI = ti_par_int
%                 ; ElemTI = ti_var_int
%                 ),
%                 list.foldl(mzn_expr_to_int_acc(Context), RevItemMZs,
%                     [], IntExprs),
%                 Xs = array(IntExprs),
%                 MZ0 = int_array_to_mzn_expr(array_items(IndexRanges, Xs))
%             ;
%                 ElemTI = ti_par_set(ti_par_bool),
%                 list.foldl(mzn_expr_to_bool_set_acc(Context), RevItemMZs,
%                     [], SetBoolExprs),
%                 Xs = array(SetBoolExprs),
%                 MZ0 = bool_set_array_to_mzn_expr(array_items(IndexRanges, Xs))
%             ;
%                 ElemTI = ti_par_set(ti_par_float),
%                 list.foldl(mzn_expr_to_float_set_acc(Context), RevItemMZs,
%                     [], SetFloatExprs),
%                 Xs = array(SetFloatExprs),
%                 MZ0 = float_set_array_to_mzn_expr(array_items(IndexRanges, Xs))
%             ;
%                 ( ElemTI = ti_par_set(ti_par_int)
%                 ; ElemTI = ti_var_set(ti_par_int)
%                 ),
%                 list.foldl(mzn_expr_to_int_set_acc(Context), RevItemMZs,
%                     [], SetIntExprs),
%                 Xs = array(SetIntExprs),
%                 MZ0 = int_set_array_to_mzn_expr(array_items(IndexRanges, Xs))
%             ;
%                 ElemTI = ti_par_string,
%                 list.foldl(mzn_expr_to_string_acc(Context), RevItemMZs,
%                     [], StringExprs),
%                 Xs = array(StringExprs),
%                 MZ0 = string_array_to_mzn_expr(array_items(IndexRanges, Xs))
%             ;
%                 ElemTI = ti_ann,
%                 list.foldl(mzn_expr_to_ann_acc(Context), RevItemMZs,
%                     [], AnnExprs),
%                 Xs = array(AnnExprs),
%                 MZ0 = ann_array_to_mzn_expr(array_items(IndexRanges, Xs))
%             ;
%                 ( ElemTI = ti_par_bottom
%                 ; ElemTI = ti_var_bottom
%                 ),
%                 list.length(RevItemMZs, NumItems),
%                 array.init(NumItems, bottom_expr, Xs),
%                 MZ0 = bottom_array_to_mzn_expr(array_items(IndexRanges, Xs))
%             )
%           then
%             MZ = MZ0
%           else
%             minizinc_user_error(Context,
%                 "This is not a valid MiniZinc array type.\n")
%         )
%     ).

%-----------------------------------------------------------------------------%

:- pred halfreify_ann(error_context::in, mzn_anns::in, ilhs::in,
    string::in, exprs::in, mzn_expr::out,
    mzn_constraint_set::out, known_to_be_false::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

halfreify_ann(Context, Anns, ILHS, AnnName, ArgExprs, MZ,
        AllConstraints, KnownFalse, !Info, !Model) :-
    list.map3_foldl2(halfreify_expr(Context, Anns, ILHS), ArgExprs, ArgMZs,
        ConstraintSets, KnownFalses, !Info, !Model),
    MZ = mzn_expr(ann_expr(mzn_ann(AnnName, ArgMZs)), no_anns),
    mzn_constraint_set_union_list(ConstraintSets, AllConstraints),
    KnownFalse = combine_known_to_be_false_list(KnownFalses).

%-----------------------------------------------------------------------------%
:- end_module hr.expr.
%-----------------------------------------------------------------------------%
