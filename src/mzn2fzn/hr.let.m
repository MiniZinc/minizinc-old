%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
% Flattening let expressions.
%
%-----------------------------------------------------------------------------%

:- module hr.let.
:- interface.

:- import_module errors.
:- import_module hr.info.
:- import_module types.

:- import_module zinc_ast.

%-----------------------------------------------------------------------------%

% :- pred flatten_let_expr(error_context::in, local_vars::in, expr::in,
%     mzn_expr::out, env::in, env::out) is det.

:- pred hr_create_new_var(error_context::in, string::in, var_par::in,
    mzn_type::in, index_ranges::in, mzn_anns::in,
    var_id::out, mzn_expr::out,
    hr_info::in, hr_info::out, model::in, model::out) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

% :- import_module flatten.ann.
% :- import_module flatten.app.
% :- import_module flatten.expr.

:- import_module list.
:- import_module maybe.
:- import_module require.
:- import_module string.

%-----------------------------------------------------------------------------%

% flatten_let_expr(Context, LetVars, Expr, MZ, !Env) :-
%     OldLocals = !.Env ^ locals,
%     list.foldl(flatten_let_var(Context), LetVars, !Env),
%     flatten_expr(Context, Expr, MZ, !Env),
%     !Env ^ locals := OldLocals.
%
%     % XXX Handle the AnnExprs below.
%     %
% :- pred flatten_let_var(error_context::in, local_var::in, env::in, env::out)
%     is det.
%
% flatten_let_var(Context, LocalVar, !Env) :-
%     LocalVar = local_var(TIExpr, VarId, AnnExprs, MaybeExpr),
%     VarName = var_name(VarId),
%     VarContext = [["In let-variable '", VarName, "'.\n"] | Context],
%     flatten_ti_expr(VarContext, TIExpr, VarPar, MZType, IndexRanges, !Env),
%     (
%         MaybeExpr = yes(ValueExpr),
%         % If this is a var bool or array of var bool then we want to
%         % reify the value (e.g., we don't want to do any assignments
%         % when processing, say, x = [y = 1, y = 2, y = 3]).
%         ( if
%             VarPar = var,
%             ( MZType = mzn_bool
%             ; MZType = mzn_bool_array
%             )
%           then
%             flatten_expr_reified(VarContext, ValueExpr, MZ, !Env)
%           else
%             flatten_expr(VarContext, ValueExpr, MZ, !Env)
%         ),
%         ( if index_ranges_are_compatible(VarContext, IndexRanges, MZ) then
%             true
%           else
%             minizinc_user_error(VarContext,
%                 "Array index ranges do not match.\n")
%         )
%     ;
%         MaybeExpr = no,
%         Reifying = !.Env ^ reifying,
%         (
%             Reifying = not_reifying,
%             flatten_anns(Context, AnnExprs, Anns, !Env),
%             create_new_var(VarContext, VarName, VarPar, MZType, IndexRanges,
%                 Anns, _NewVar, MZ, !Env)
%         ;
%             Reifying = reifying(_ : bool_exprs),
%             minizinc_user_error(VarContext,
%                 "Let-variables with no definitions cannot appear in " ++
%                 "reified contexts.\n")
%         )
%     ),
%     bind_local(VarContext, MZType, VarId, MZ, !Env).
%
% :- pred index_ranges_are_compatible(error_context::in, index_ranges::in,
%     mzn_expr::in) is semidet.
%
% index_ranges_are_compatible(Context, IndexRanges, MZ) :-
%     (
%         % Variable is not an array.
%         %
%         IndexRanges = []
%     ;
%         IndexRanges = [_ | _],
%         MZ = mzn_expr(RawExpr, _),
%         require_complete_switch [RawExpr] (
%             ( RawExpr = bool_expr(_)
%             ; RawExpr = bool_set_expr(_)
%             ; RawExpr = float_expr(_)
%             ; RawExpr = float_set_expr(_)
%             ; RawExpr = int_expr(_)
%             ; RawExpr = int_set_expr(_)
%             ; RawExpr = string_expr(_)
%             ; RawExpr = ann_expr(_)
%             ; RawExpr = bottom_expr(_)
%             ),
%             minizinc_internal_error(Context, $pred,
%                 "type mistmatch in local array decl.")
%         ;
%             (
%                 RawExpr = bool_array_expr(ArrayExpr),
%                 IndexRanges = array_expr_to_index_ranges(ArrayExpr)
%             ;
%                 RawExpr = bool_set_array_expr(ArrayExpr),
%                 IndexRanges = array_expr_to_index_ranges(ArrayExpr)
%             ;
%                 RawExpr = float_array_expr(ArrayExpr),
%                 IndexRanges = array_expr_to_index_ranges(ArrayExpr)
%             ;
%                 RawExpr = float_set_array_expr(ArrayExpr),
%                 IndexRanges = array_expr_to_index_ranges(ArrayExpr)
%             ;
%                 RawExpr = int_array_expr(ArrayExpr),
%                 IndexRanges = array_expr_to_index_ranges(ArrayExpr)
%             ;
%                 RawExpr = int_set_array_expr(ArrayExpr),
%                 IndexRanges = array_expr_to_index_ranges(ArrayExpr)
%             ;
%                 RawExpr = bottom_array_expr(ArrayExpr),
%                 IndexRanges = array_expr_to_index_ranges(ArrayExpr)
%             )
%         ;
%             ( RawExpr = string_array_expr(_)
%             ; RawExpr = ann_array_expr(_)
%             ),
%             minizinc_internal_error(Context, $pred,
%                 "Unexpected string or annotation type.\n")
%         )
%     ).
%
% :- func array_expr_to_index_ranges(array_expr(_)) = index_ranges.
%
% array_expr_to_index_ranges(array_items(I, _)) = I.
% array_expr_to_index_ranges(array_var(I, _)) = I.

%-----------------------------------------------------------------------------%

hr_create_new_var(_Context, VarName, _VarPar, _MZType, _IndexRanges, _Anns,
        VarId, MZ, !Info, !Model) :-
    ( if semidet_succeed then
        unexpected($pred, "NYI")
    else
        hr_new_tmp_var_id(VarName, VarId, !Info),
        % XXX dummy
        MZ = mzn_expr(bool_expr(bool_var(var_no_index(VarId))), no_anns)
    ).
%     hr_new_tmp_var_id(VarName, VarId, !Info),
%     ( if VarPar = var then
%         hr_add_global_permanent_var(VarId, MZType, IndexRanges, Anns,
%             ConstraintsToAdd, !Model)
%       else
%         hr_add_global_par(VarId, MZType, IndexRanges, !Model)
%     ),
%     MZVar = var_no_index(VarId),
%     (
%         MZType = mzn_bool,
%         A = bool_var(MZVar),
%         RawMZ = bool_expr(A)
%     ;
%         MZType = mzn_bool_array,
%         A = array_var(IndexRanges, VarId),
%         RawMZ = bool_array_expr(A)
%     ;
%         MZType = mzn_bool_set,
%         A = set_var(MZVar),
%         RawMZ = bool_set_expr(A)
%     ;
%         MZType = mzn_bool_set_array,
%         A = array_var(IndexRanges, VarId),
%         RawMZ = bool_set_array_expr(A)
%     ;
%         MZType = mzn_float(Bounds),
%         A = float_var(MZVar),
%         RawMZ = float_expr(A),
%         hr_impose_float_bounds(Context, Bounds, A, !Info, !Model)
%     ;
%         MZType = mzn_float_array(Bounds),
%         A = array_var(IndexRanges, VarId),
%         RawMZ = float_array_expr(A),
%         hr_impose_float_array_bounds(Context, Bounds, A, !Info, !Model)
%     ;
%         MZType = mzn_float_set(Bounds),
%         A = set_var(MZVar),
%         RawMZ = float_set_expr(A),
%         hr_impose_float_set_bounds(Context, Bounds, A, !Env)
%     ;
%         MZType = mzn_float_set_array(Bounds),
%         A = array_var(IndexRanges, VarId),
%         RawMZ = float_set_array_expr(A),
%         hr_impose_float_set_array_bounds(Context, Bounds, A, !Env)
%     ;
%         MZType = mzn_int(Bounds),
%         A = int_var(MZVar),
%         RawMZ = int_expr(A),
%         hr_impose_int_bounds(Context, Bounds, A, !Env)
%     ;
%         MZType = mzn_int_array(Bounds),
%         A = array_var(IndexRanges, VarId),
%         RawMZ = int_array_expr(A),
%         hr_impose_int_array_bounds(Context, Bounds, A, !Env)
%     ;
%         MZType = mzn_int_set(Bounds),
%         A = set_var(MZVar),
%         RawMZ = int_set_expr(A),
%         hr_impose_int_set_bounds(Context, Bounds, A, !Env)
%     ;
%         MZType = mzn_int_set_array(Bounds),
%         A = array_var(IndexRanges, VarId),
%         RawMZ = int_set_array_expr(A),
%         hr_impose_int_set_array_bounds(Context, Bounds, A, !Env)
%     ;
%         MZType = mzn_bottom,
%         RawMZ = bottom_expr(bottom_expr)
%     ;
%         MZType= mzn_bottom_array,
%         unexpected($pred, "array bottom")
%     ;
%         (   MZType = mzn_string
%         ;   MZType = mzn_string_array
%         ;   MZType = mzn_ann
%         ;   MZType = mzn_ann_array
%         ),
%         minizinc_internal_error(Context, $pred,
%             "Unexpected string or annotation type.\n")
%     ),
%     MZ = mzn_expr(RawMZ, no_anns).

%-----------------------------------------------------------------------------%
:- end_module hr.let.
%-----------------------------------------------------------------------------%
