%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Ralph Becket <rafe@csse.unimelb.edu.au>
%
%-----------------------------------------------------------------------------%

:- module common_array.
:- interface.

:- import_module errors.
:- import_module types.

:- import_module array.
:- import_module list.

%-----------------------------------------------------------------------------%

    % XXX Add support for array equality and comparison etc.
:- func list_to_array_expr(list(T)) = array_expr(T).

:- func array_to_array_expr(array(T)) = array_expr(T).

    % Turn an array of items into mzn_exprs.
    % The array must be fully dereferenced before calling this function.
    %
:- func array_items_to_mzn_exprs(error_context, func(T) = mzn_expr,
    array_expr(T)) = mzn_expr_array.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

%-----------------------------------------------------------------------------%

list_to_array_expr(Xs) = array_to_array_expr(array(Xs)).

array_to_array_expr(As) = ArrayExpr :-
    IndexExprs = [index_range(1, array.size(As))],
    ArrayExpr = array_items(IndexExprs, As).

array_items_to_mzn_exprs(Context, F, ArrayExpr) = MznExprArray :-
    (
        ArrayExpr = array_var(_, _),
        minizinc_user_error(Context,
            "This is not an array literal.\n")
    ;
        ArrayExpr = array_items(_, Items),
        MznExprArray = array.map(F, Items)
    ).

%-----------------------------------------------------------------------------%
:- end_module common_array.
%-----------------------------------------------------------------------------%
