%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2012 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
% Dump the typed MiniZinc representation in a format suitable for debugging
% messages.
%
%-----------------------------------------------------------------------------%

:- module output_tmzn.
:- interface.

:- import_module output_common.
:- import_module tmzn_ast.

%-----------------------------------------------------------------------------%
%
% These functions should generate output that is in standard Zinc syntax.
% XXX They do not yet do so.
%

:- func bool_expr_to_str(output_opts, tmzn_bool_expr) = string.
:- func int_expr_to_str(output_opts, tmzn_int_expr) = string.
:- func int_set_expr_to_str(output_opts, tmzn_int_set_expr) = string.
:- func float_expr_to_str(output_opts, tmzn_float_expr) = string.

%-----------------------------------------------------------------------------%
%
% These functions for debugging generate easy-to-read output that is NOT
% in standard Zinc syntax.
%

:- func dump_tmzn_constraint_item(tmzn_constraint_item) = string.

:- type parens
    --->    no_parens
    ;       parens.

:- func dump_tmzn_bool_expr(parens, tmzn_bool_expr) = string.
:- func dump_tmzn_bool_array_expr(parens, tmzn_bool_array_expr) = string.
:- func dump_tmzn_int_expr(parens, tmzn_int_expr) = string.
:- func dump_tmzn_int_array_expr(parens, tmzn_int_array_expr) = string.
:- func dump_tmzn_int_set_expr(parens, tmzn_int_set_expr) = string.
:- func dump_tmzn_int_set_array_expr(parens, tmzn_int_set_array_expr) = string.
:- func dump_tmzn_float_expr(parens, tmzn_float_expr) = string.
:- func dump_tmzn_float_array_expr(parens, tmzn_float_array_expr) = string.
:- func dump_tmzn_float_set_expr(parens, tmzn_float_set_expr) = string.
:- func dump_tmzn_string_expr(parens, tmzn_string_expr) = string.
:- func dump_tmzn_string_array_expr(parens, tmzn_string_array_expr) = string.
:- func dump_tmzn_general_expr(parens, tmzn_general_expr) = string.

:- func dump_tmzn_bool_var(tmzn_bool_var) = string.
:- func dump_tmzn_bool_array_var(tmzn_bool_array_var) = string.
:- func dump_tmzn_int_var(tmzn_int_var) = string.
:- func dump_tmzn_int_array_var(tmzn_int_array_var) = string.
:- func dump_tmzn_int_set_var(tmzn_int_set_var) = string.
:- func dump_tmzn_int_set_array_var(tmzn_int_set_array_var) = string.
:- func dump_tmzn_float_var(tmzn_float_var) = string.
:- func dump_tmzn_float_array_var(tmzn_float_array_var) = string.
:- func dump_tmzn_float_set_var(tmzn_float_set_var) = string.
:- func dump_tmzn_string_var(tmzn_string_var) = string.
:- func dump_tmzn_string_array_var(tmzn_string_array_var) = string.

%-----------------------------------------------------------------------------%

:- implementation.

:- import_module mzn_ops.
:- import_module types.

:- import_module bool.
:- import_module list.
:- import_module maybe.
:- import_module set.
:- import_module string.
:- import_module term_io.

%-----------------------------------------------------------------------------%

% XXX These should be reimplemented to generate output in Zinc syntax.
bool_expr_to_str(_Opts, BoolExpr) =
    dump_tmzn_bool_expr(no_parens, BoolExpr).
int_expr_to_str(_Opts, IntExpr) =
    dump_tmzn_int_expr(no_parens, IntExpr).
int_set_expr_to_str(_Opts, IntSetExpr) =
    dump_tmzn_int_set_expr(no_parens, IntSetExpr).
float_expr_to_str(_Opts, FloatExpr) =
    dump_tmzn_float_expr(no_parens, FloatExpr).

%-----------------------------------------------------------------------------%

dump_tmzn_constraint_item(ConstraintItem) = Str :-
    ConstraintItem = tmzn_constraint_item(_SrcPos, Constraint, _Anns),
    Str = dump_tmzn_constraint(Constraint).

:- func dump_tmzn_constraint(tmzn_constraint) = string.

dump_tmzn_constraint(Constraint) = Str :-
    Constraint = tmzn_constr_bool_expr(BoolExpr),
    Str = dump_tmzn_bool_expr(no_parens, BoolExpr) ++ "\n".

%-----------------------------------------------------------------------------%

dump_tmzn_bool_expr(Parens, BoolExpr) = Str :-
    (
        BoolExpr = tmzn_bool_expr_const(_SrcPos, BoolConst),
        (
            BoolConst = no,
            Str = "no"
        ;
            BoolConst = yes,
            Str = "yes"
        )
    ;
        BoolExpr = tmzn_bool_expr_var(_SrcPos, BoolVar),
        Str = dump_tmzn_bool_var(BoolVar)
    ;
        BoolExpr = tmzn_bool_expr_b2b(_SrcPos, B2BOp, BoolExprA),
        is_bool_to_bool_op(B2BOpStr, B2BOp),
        Str =
            maybe_paren_open(Parens) ++
            B2BOpStr ++ " " ++
            dump_tmzn_bool_expr(parens, BoolExprA) ++
            maybe_paren_close(Parens)
    ;
        BoolExpr = tmzn_bool_expr_bb2b(_SrcPos, BB2BOp, BoolExprA, BoolExprB),
        is_bool_bool_to_bool_op(BB2BOpStr, BB2BOp),
        Str =
            maybe_paren_open(Parens) ++
            dump_tmzn_bool_expr(parens, BoolExprA) ++
            " " ++ BB2BOpStr ++ " " ++
            dump_tmzn_bool_expr(parens, BoolExprB) ++
            maybe_paren_close(Parens)
    ;
        BoolExpr = tmzn_bool_expr_ba2b(_SrcPos, BA2BOp, BoolArrayExprA),
        is_bool_array_to_bool_op(BA2BOpStr, BA2BOp),
        Str =
            maybe_paren_open(Parens) ++
            BA2BOpStr ++ " " ++
            dump_tmzn_bool_array_expr(parens, BoolArrayExprA) ++
            maybe_paren_close(Parens)
    ;
        BoolExpr = tmzn_bool_expr_ii2b(_SrcPos, II2BOp, IntExprA, IntExprB),
        is_int_int_to_bool_op(II2BOpStr, II2BOp),
        Str =
            maybe_paren_open(Parens) ++
            dump_tmzn_int_expr(parens, IntExprA) ++
            " " ++
            II2BOpStr ++
            " " ++
            dump_tmzn_int_expr(parens, IntExprB) ++
            maybe_paren_close(Parens)
    ;
        BoolExpr = tmzn_bool_expr_iis2b(_SrcPos, IIS2BOp,
            IntExprA, IntSetExprB),
        is_int_int_set_to_bool_op(IIS2BOpStr, IIS2BOp),
        Str =
            maybe_paren_open(Parens) ++
            dump_tmzn_int_expr(parens, IntExprA) ++
            " " ++ IIS2BOpStr ++ " " ++
            dump_tmzn_int_set_expr(parens, IntSetExprB) ++
            maybe_paren_close(Parens)
    ;
        BoolExpr = tmzn_bool_expr_isis2b(_SrcPos, ISIS2BOp,
            IntSetExprA, IntSetExprB),
        is_set_set_to_bool_op(ISIS2BOpStr, ISIS2BOp),
        Str =
            maybe_paren_open(Parens) ++
            dump_tmzn_int_set_expr(parens, IntSetExprA) ++
            " " ++ ISIS2BOpStr ++ " " ++
            dump_tmzn_int_set_expr(parens, IntSetExprB) ++
            maybe_paren_close(Parens)
    ;
        BoolExpr = tmzn_bool_expr_ff2b(_SrcPos, FF2BOp,
            FloatExprA, FloatExprB),
        is_float_float_to_bool_op(FF2BOpStr, FF2BOp),
        Str =
            maybe_paren_open(Parens) ++
            dump_tmzn_float_expr(parens, FloatExprA) ++
            " " ++ FF2BOpStr ++ " " ++
            dump_tmzn_float_expr(parens, FloatExprB) ++
            maybe_paren_close(Parens)
    ;
        BoolExpr = tmzn_bool_expr_ffs2b(_SrcPos, FFS2BOp,
            FloatExprA, FloatSetExprB),
        is_float_float_set_to_bool_op(FFS2BOpStr, FFS2BOp),
        Str =
            maybe_paren_open(Parens) ++
            dump_tmzn_float_expr(parens, FloatExprA) ++
            " " ++ FFS2BOpStr ++ " " ++
            dump_tmzn_float_set_expr(parens, FloatSetExprB) ++
            maybe_paren_close(Parens)
    ;
        BoolExpr = tmzn_bool_expr_fsfs2b(_SrcPos, FSFS2BOp,
            FloatSetExprA, FloatSetExprB),
        is_set_set_to_bool_op(FSFS2BOpStr, FSFS2BOp),
        Str =
            maybe_paren_open(Parens) ++
            dump_tmzn_float_set_expr(parens, FloatSetExprA) ++
            " " ++ FSFS2BOpStr ++ " " ++
            dump_tmzn_float_set_expr(parens, FloatSetExprB) ++
            maybe_paren_close(Parens)
    ;
        BoolExpr = tmzn_bool_expr_ss2b(_SrcPos, SS2BOp,
            StringExprA, StringExprB),
        is_string_string_to_bool_op(SS2BOpStr, SS2BOp),
        Str =
            maybe_paren_open(Parens) ++
            dump_tmzn_string_expr(parens, StringExprA) ++
            " " ++ SS2BOpStr ++ " " ++
            dump_tmzn_string_expr(parens, StringExprB) ++
            maybe_paren_close(Parens)
    ;
        BoolExpr = tmzn_bool_expr_ite(_SrcPos, CondExpr, ThenExpr, ElseExpr),
        Str =
            maybe_paren_open(Parens) ++
            "if " ++
            dump_tmzn_bool_expr(parens, CondExpr) ++
            " then " ++
            dump_tmzn_bool_expr(parens, ThenExpr) ++
            " else " ++
            dump_tmzn_bool_expr(parens, ElseExpr) ++
            maybe_paren_close(Parens)
    ;
        BoolExpr = tmzn_bool_expr_is_fixed(_SrcPos, GeneralExpr),
        Str = "is_fixed(" ++
            dump_tmzn_general_expr(no_parens, GeneralExpr) ++
            ")"
    ;
        BoolExpr = tmzn_bool_expr_general(_SrcPos, PredName, GeneralExprs),
        Str = "apply_pred(" ++
            PredName ++ ", " ++
            dump_list(dump_tmzn_general_expr(no_parens), GeneralExprs) ++
            ")"
    ).

dump_tmzn_bool_array_expr(_Parens, BoolArrayExpr) = Str :-
    (
        BoolArrayExpr = tmzn_bool_array_expr_consts(_SrcPos,
            IndexRanges, Bools),
        Str = "bool_array_consts(" ++
            dump_list(dump_index_range, IndexRanges) ++ ", " ++
            dump_list(dump_bool, Bools) ++ ")"
    ;
        BoolArrayExpr = tmzn_bool_array_expr_vars(_SrcPos,
            IndexRanges, BoolVars),
        Str = "bool_array_consts(" ++
            dump_list(dump_index_range, IndexRanges) ++ ", " ++
            dump_list(dump_tmzn_bool_var, BoolVars) ++ ")"
    ;
        BoolArrayExpr = tmzn_bool_array_expr_exprs(_SrcPos,
            IndexRanges, BoolExprs),
        Str = "bool_array_consts(" ++
            dump_list(dump_index_range, IndexRanges) ++ ", " ++
            dump_list(dump_tmzn_bool_expr(no_parens), BoolExprs) ++ ")"
    ;
        BoolArrayExpr = tmzn_bool_array_expr_var(_SrcPos, BoolArrayVar),
        Str = dump_tmzn_bool_array_var(BoolArrayVar)
    ;
        BoolArrayExpr = tmzn_bool_array_expr_comprehension(_SrcPos,
            HeadBoolExpr, Generators, MaybeCondExpr),
        Str = "comprehension(" ++
            dump_tmzn_bool_expr(no_parens, HeadBoolExpr) ++ ", " ++
            dump_list(dump_tmzn_generator, Generators) ++ ", " ++
            dump_maybe_tmzn_bool_expr(MaybeCondExpr) ++
            ")"
    ).

dump_tmzn_int_expr(Parens, IntExpr) = Str :-
    (
        IntExpr = tmzn_int_expr_const(_SrcPos, IntConst),
        string.int_to_string(IntConst, Str)
    ;
        IntExpr = tmzn_int_expr_var(_SrcPos, IntVar),
        Str = dump_tmzn_int_var(IntVar)
    ;
        IntExpr = tmzn_int_expr_b2i(_SrcPos, B2IOp, BoolExprA),
        is_bool_to_int_op(B2IOpStr, B2IOp),
        Str =
            maybe_paren_open(Parens) ++
            B2IOpStr ++ " " ++
            dump_tmzn_bool_expr(parens, BoolExprA) ++
            maybe_paren_close(Parens)
    ;
        IntExpr = tmzn_int_expr_i2i(_SrcPos, I2IOp, IntExprA),
        is_int_to_int_op(I2IOpStr, I2IOp),
        Str =
            maybe_paren_open(Parens) ++
            I2IOpStr ++ " " ++
            dump_tmzn_int_expr(parens, IntExprA) ++
            maybe_paren_close(Parens)
    ;
        IntExpr = tmzn_int_expr_ii2i(_SrcPos, II2IOp, IntExprA, IntExprB),
        is_int_int_to_int_op(II2IOpStr, II2IOp),
        Str =
            maybe_paren_open(Parens) ++
            dump_tmzn_int_expr(parens, IntExprA) ++
            " " ++ II2IOpStr ++ " " ++
            dump_tmzn_int_expr(parens, IntExprB) ++
            maybe_paren_close(Parens)
    ;
        IntExpr = tmzn_int_expr_is2i(_SrcPos, IS2IOp, IntSetExprA),
        is_int_set_to_int_op(IS2IOpStr, IS2IOp),
        Str =
            maybe_paren_open(Parens) ++
            IS2IOpStr ++ " " ++
            dump_tmzn_int_set_expr(parens, IntSetExprA) ++
            maybe_paren_close(Parens)
    ;
        IntExpr = tmzn_int_expr_ia2i(_SrcPos, IA2IOp, IntArrayExprA),
        is_int_array_to_int_op(IA2IOpStr, IA2IOp),
        Str =
            maybe_paren_open(Parens) ++
            IA2IOpStr ++ " " ++
            dump_tmzn_int_array_expr(parens, IntArrayExprA) ++
            maybe_paren_close(Parens)
    ;
        IntExpr = tmzn_int_expr_xs2i(_SrcPos, XS2IOp, IntSetExprA),
        is_set_to_int_op(XS2IOpStr, XS2IOp),
        Str =
            maybe_paren_open(Parens) ++
            XS2IOpStr ++ " " ++
            dump_tmzn_int_set_expr(parens, IntSetExprA) ++
            maybe_paren_close(Parens)
    ;
        IntExpr = tmzn_int_expr_ite(_SrcPos, CondExpr, ThenExpr, ElseExpr),
        Str =
            maybe_paren_open(Parens) ++
            "if " ++
            dump_tmzn_bool_expr(parens, CondExpr) ++
            " then " ++
            dump_tmzn_int_expr(parens, ThenExpr) ++
            " else " ++
            dump_tmzn_int_expr(parens, ElseExpr) ++
            maybe_paren_close(Parens)
    ).

dump_tmzn_int_array_expr(_Parens, IntArrayExpr) = Str :-
    (
        IntArrayExpr = tmzn_int_array_expr_consts(_SrcPos,
            IndexRanges, Ints),
        Str = "int_array_consts(" ++
            dump_list(dump_index_range, IndexRanges) ++ ", " ++
            dump_list(dump_int, Ints) ++ ")"
    ;
        IntArrayExpr = tmzn_int_array_expr_vars(_SrcPos,
            IndexRanges, IntVars),
        Str = "int_array_consts(" ++
            dump_list(dump_index_range, IndexRanges) ++ ", " ++
            dump_list(dump_tmzn_int_var, IntVars) ++ ")"
    ;
        IntArrayExpr = tmzn_int_array_expr_exprs(_SrcPos,
            IndexRanges, IntExprs),
        Str = "int_array_consts(" ++
            dump_list(dump_index_range, IndexRanges) ++ ", " ++
            dump_list(dump_tmzn_int_expr(no_parens), IntExprs) ++ ")"
    ;
        IntArrayExpr = tmzn_int_array_expr_var(_SrcPos, IntArrayVar),
        Str = dump_tmzn_int_array_var(IntArrayVar)
    ;
        IntArrayExpr = tmzn_int_array_expr_comprehension(_SrcPos,
            HeadIntExpr, Generators, MaybeCondExpr),
        Str = "comprehension(" ++
            dump_tmzn_int_expr(no_parens, HeadIntExpr) ++ ", " ++
            dump_list(dump_tmzn_generator, Generators) ++ ", " ++
            dump_maybe_tmzn_bool_expr(MaybeCondExpr) ++
            ")"
    ;
        IntArrayExpr = tmzn_int_array_expr_from_set(_SrcPos, IntSetExprA),
        Str = "int_array_from_set(" ++
            dump_tmzn_int_set_expr(no_parens, IntSetExprA) ++
            ")"
    ).

dump_tmzn_int_set_expr(Parens, IntSetExpr) = Str :-
    (
        IntSetExpr = tmzn_int_set_expr_const(_SrcPos, IntSet),
        set.to_sorted_list(IntSet, Ints),
        Str = "set(" ++ dump_list(dump_int, Ints) ++ ")"
    ;
        IntSetExpr = tmzn_int_set_expr_exprs(_SrcPos, IntExprSet),
        set.to_sorted_list(IntExprSet, IntExprs),
        Str = "set(" ++ dump_list(dump_tmzn_int_expr(Parens), IntExprs) ++ ")"
    ;
        IntSetExpr = tmzn_int_set_expr_var(_SrcPos, IntSetVar),
        Str = dump_tmzn_int_set_var(IntSetVar)
    ;
        IntSetExpr = tmzn_int_set_expr_i2is(_SrcPos, I2ISOp, IntExprA),
        is_int_to_int_set_op(I2ISOpStr, I2ISOp),
        Str =
            maybe_paren_open(Parens) ++
            I2ISOpStr ++ " " ++
            dump_tmzn_int_expr(parens, IntExprA) ++
            maybe_paren_close(Parens)
    ;
        IntSetExpr = tmzn_int_set_expr_ii2is(_SrcPos, II2ISOp,
            IntExprA, IntExprB),
        is_int_int_to_int_set_op(II2ISOpStr, II2ISOp),
        Str =
            maybe_paren_open(Parens) ++
            dump_tmzn_int_expr(parens, IntExprA) ++
            II2ISOpStr ++ " " ++
            dump_tmzn_int_expr(parens, IntExprB) ++
            maybe_paren_close(Parens)
    ;
        IntSetExpr = tmzn_int_set_expr_isis2is(_SrcPos, ISIS2ISOp,
            IntSetExprA, IntSetExprB),
        is_set_set_to_set_op(ISIS2ISOpStr, ISIS2ISOp),
        Str =
            maybe_paren_open(Parens) ++
            dump_tmzn_int_set_expr(parens, IntSetExprA) ++
            " " ++ ISIS2ISOpStr ++ " " ++
            dump_tmzn_int_set_expr(parens, IntSetExprB) ++
            maybe_paren_close(Parens)
    ;
        IntSetExpr = tmzn_int_set_expr_comprehension(_SrcPos,
            HeadIntExpr, Generators, MaybeCondExpr),
        Str = "int_set_comprehension(" ++
            dump_tmzn_int_expr(no_parens, HeadIntExpr) ++ ", " ++
            dump_list(dump_tmzn_generator, Generators) ++ ", " ++
            dump_maybe_tmzn_bool_expr(MaybeCondExpr) ++
            ")"
    ).

dump_tmzn_int_set_array_expr(_Parens, IntSetArrayExpr) = Str :-
    (
        IntSetArrayExpr = tmzn_int_set_array_expr_consts(_SrcPos,
            IndexRanges, IntSets),
        Str = "int_set_array_consts(" ++
            dump_list(dump_index_range, IndexRanges) ++ ", " ++
            dump_list(dump_int_set, IntSets) ++ ")"
    ;
        IntSetArrayExpr = tmzn_int_set_array_expr_vars(_SrcPos,
            IndexRanges, IntSetVars),
        Str = "int_set_array_consts(" ++
            dump_list(dump_index_range, IndexRanges) ++ ", " ++
            dump_list(dump_tmzn_int_set_var, IntSetVars) ++ ")"
    ;
        IntSetArrayExpr = tmzn_int_set_array_expr_exprs(_SrcPos,
            IndexRanges, IntSetExprs),
        Str = "int_set_array_consts(" ++
            dump_list(dump_index_range, IndexRanges) ++ ", " ++
            dump_list(dump_tmzn_int_set_expr(no_parens), IntSetExprs) ++ ")"
    ;
        IntSetArrayExpr = tmzn_int_set_array_expr_var(_SrcPos, FloatArrayVar),
        Str = dump_tmzn_int_set_array_var(FloatArrayVar)
    ;
        IntSetArrayExpr = tmzn_int_set_array_expr_comprehension(_SrcPos,
            HeadIntSetExpr, Generators, MaybeCondExpr),
        Str = "int_set_array_comprehension(" ++
            dump_tmzn_int_set_expr(no_parens, HeadIntSetExpr) ++ ", " ++
            dump_list(dump_tmzn_generator, Generators) ++ ", " ++
            dump_maybe_tmzn_bool_expr(MaybeCondExpr) ++
            ")"
    ).

dump_tmzn_float_expr(Parens, FloatExpr) = Str :-
    (
        FloatExpr = tmzn_float_expr_const(_SrcPos, FloatConst),
        string.float_to_string(FloatConst, Str)
    ;
        FloatExpr = tmzn_float_expr_var(_SrcPos, FloatVar),
        Str = dump_tmzn_float_var(FloatVar)
    ;
        FloatExpr = tmzn_float_expr_i2f(_SrcPos, I2FOp, IntExprA),
        is_int_to_float_op(I2FOpStr, I2FOp),
        Str =
            maybe_paren_open(Parens) ++
            I2FOpStr ++ " " ++
            dump_tmzn_int_expr(parens, IntExprA) ++
            maybe_paren_close(Parens)
    ;
        FloatExpr = tmzn_float_expr_f2f(_SrcPos, F2FOp, FloatExprA),
        is_float_to_float_op(F2FOpStr, F2FOp),
        Str =
            maybe_paren_open(Parens) ++
            F2FOpStr ++ " " ++
            dump_tmzn_float_expr(parens, FloatExprA) ++
            maybe_paren_close(Parens)
    ;
        FloatExpr = tmzn_float_expr_ff2f(_SrcPos, FF2FOp,
            FloatExprA, FloatExprB),
        is_float_float_to_float_op(FF2FOpStr, FF2FOp),
        Str =
            maybe_paren_open(Parens) ++
            dump_tmzn_float_expr(parens, FloatExprA) ++
            " " ++ FF2FOpStr ++ " " ++
            dump_tmzn_float_expr(parens, FloatExprB) ++
            maybe_paren_close(Parens)
    ;
        FloatExpr = tmzn_float_expr_ite(_SrcPos, CondExpr, ThenExpr, ElseExpr),
        Str =
            maybe_paren_open(Parens) ++
            "if " ++
            dump_tmzn_bool_expr(parens, CondExpr) ++
            " then " ++
            dump_tmzn_float_expr(parens, ThenExpr) ++
            " else " ++
            dump_tmzn_float_expr(parens, ElseExpr) ++
            maybe_paren_close(Parens)
    ).

dump_tmzn_float_array_expr(_Parens, FloatArrayExpr) = Str :-
    (
        FloatArrayExpr = tmzn_float_array_expr_consts(_SrcPos,
            IndexRanges, Floats),
        Str = "float_array_consts(" ++
            dump_list(dump_index_range, IndexRanges) ++ ", " ++
            dump_list(dump_float, Floats) ++ ")"
    ;
        FloatArrayExpr = tmzn_float_array_expr_vars(_SrcPos,
            IndexRanges, FloatVars),
        Str = "float_array_consts(" ++
            dump_list(dump_index_range, IndexRanges) ++ ", " ++
            dump_list(dump_tmzn_float_var, FloatVars) ++ ")"
    ;
        FloatArrayExpr = tmzn_float_array_expr_exprs(_SrcPos,
            IndexRanges, FloatExprs),
        Str = "float_array_consts(" ++
            dump_list(dump_index_range, IndexRanges) ++ ", " ++
            dump_list(dump_tmzn_float_expr(no_parens), FloatExprs) ++ ")"
    ;
        FloatArrayExpr = tmzn_float_array_expr_var(_SrcPos, FloatArrayVar),
        Str = dump_tmzn_float_array_var(FloatArrayVar)
    ;
        FloatArrayExpr = tmzn_float_array_expr_comprehension(_SrcPos,
            HeadFloatExpr, Generators, MaybeCondExpr),
        Str = "float_array_comprehension(" ++
            dump_tmzn_float_expr(no_parens, HeadFloatExpr) ++ ", " ++
            dump_list(dump_tmzn_generator, Generators) ++ ", " ++
            dump_maybe_tmzn_bool_expr(MaybeCondExpr) ++
            ")"
    ).

dump_tmzn_float_set_expr(_Parens, FloatSetExpr) = Str :-
    (
        FloatSetExpr = tmzn_float_set_expr_const(_SrcPos, FloatSet),
        set.to_sorted_list(FloatSet, Floats),
        Str = "set(" ++ dump_list(dump_float, Floats) ++ ")"
    ;
        FloatSetExpr = tmzn_float_set_expr_var(_SrcPos, FloatSetVar),
        Str = dump_tmzn_float_set_var(FloatSetVar)
    ).

dump_tmzn_string_expr(Parens, StringExpr) = Str :-
    (
        StringExpr = tmzn_string_expr_const(_SrcPos, StringConst),
        Str = StringConst
    ;
        StringExpr = tmzn_string_expr_var(_SrcPos, StringVar),
        Str = dump_tmzn_string_var(StringVar)
    ;
        StringExpr = tmzn_string_expr_ss2s(_SrcPos, SS2SOp,
            StringExprA, StringExprB),
        is_string_string_to_string_op(SS2SOpStr, SS2SOp),
        Str =
            maybe_paren_open(Parens) ++
            dump_tmzn_string_expr(parens, StringExprA) ++
            " " ++ SS2SOpStr ++ " " ++
            dump_tmzn_string_expr(parens, StringExprB) ++
            maybe_paren_close(Parens)
    ;
        StringExpr = tmzn_string_expr_sa2s(_SrcPos, SA2SOp,
            StringArrayExprA),
        is_string_array_to_string_op(SA2SOpStr, SA2SOp),
        Str = 
            maybe_paren_open(Parens) ++
            SA2SOpStr ++ " " ++
            dump_tmzn_string_array_expr(parens, StringArrayExprA) ++
            maybe_paren_close(Parens)
    ;
        StringExpr = tmzn_string_expr_ssa2s(_SrcPos, SSA2SOp,
            StringExprA, StringArrayExprB),
        is_string_string_array_to_string_op(SSA2SOpStr, SSA2SOp),
        Str = 
            maybe_paren_open(Parens) ++
            SSA2SOpStr ++ " " ++
            dump_tmzn_string_expr(parens, StringExprA) ++
            dump_tmzn_string_array_expr(parens, StringArrayExprB) ++
            maybe_paren_close(Parens)
    ;
        StringExpr = tmzn_string_expr_x2s(_SrcPos, X2SOp, SubExprA),
        is_general_to_string_op(X2SOpStr, X2SOp),
        Str =
            maybe_paren_open(Parens) ++
            X2SOpStr ++ " " ++
            dump_tmzn_general_expr(parens, SubExprA) ++
            maybe_paren_close(Parens)
    ;
        StringExpr = tmzn_string_expr_ii2s(_SrcPos, II2SOp, SubExprA, SubExprB),
        is_int_int_to_string_op(II2SOpStr, II2SOp),
        Str =
            maybe_paren_open(Parens) ++
            II2SOpStr ++ " " ++
            dump_tmzn_int_expr(parens, SubExprA) ++
            dump_tmzn_int_expr(parens, SubExprB) ++
            maybe_paren_close(Parens)
    ;
        StringExpr = tmzn_string_expr_iif2s(_SrcPos, IIF2SOp, SubExprA,
            SubExprB, SubExprC),
        is_int_int_float_to_string_op(IIF2SOpStr, IIF2SOp),
        Str = 
            maybe_paren_open(Parens) ++
            IIF2SOpStr ++ " " ++
            dump_tmzn_int_expr(parens, SubExprA) ++
            dump_tmzn_int_expr(parens, SubExprB) ++
            dump_tmzn_float_expr(parens, SubExprC) ++
            maybe_paren_close(Parens)
    ;
        StringExpr = tmzn_string_expr_ite(_SrcPos, CondExpr,
            ThenExpr, ElseExpr),
        Str =
            maybe_paren_open(Parens) ++
            "if " ++
            dump_tmzn_bool_expr(parens, CondExpr) ++
            " then " ++
            dump_tmzn_string_expr(parens, ThenExpr) ++
            " else " ++
            dump_tmzn_string_expr(parens, ElseExpr) ++
            maybe_paren_close(Parens)
    ).

dump_tmzn_string_array_expr(Parens, StringArrayExpr) = Str :-
    (
        StringArrayExpr = tmzn_string_array_expr_consts(_SrcPos,
            IndexRanges, Strings),
        Str = "string_array_consts(" ++
            dump_list(dump_index_range, IndexRanges) ++ ", " ++
            dump_list(dump_string, Strings) ++ ")"
    ;
        StringArrayExpr = tmzn_string_array_expr_exprs(_SrcPos,
            IndexRanges, StringExprs),
        Str = "string_array_consts(" ++
            dump_list(dump_index_range, IndexRanges) ++ ", " ++
            dump_list(dump_tmzn_string_expr(no_parens), StringExprs) ++ ")"
    ;
        StringArrayExpr = tmzn_string_array_expr_var(_SrcPos, StringArrayVar),
        Str = dump_tmzn_string_array_var(StringArrayVar)
    ;
        StringArrayExpr = tmzn_string_array_expr_sasa2sa(_SrcPos, SASA2SAOp,
            StringArrayExprA, StringArrayExprB),
        is_array_array_to_array_op(SASA2SAOpStr, SASA2SAOp),
        Str =
            maybe_paren_open(Parens) ++
            dump_tmzn_string_array_expr(parens, StringArrayExprA) ++
            " " ++ SASA2SAOpStr ++ " " ++
            dump_tmzn_string_array_expr(parens, StringArrayExprB) ++
            maybe_paren_close(Parens)
    ;
        StringArrayExpr = tmzn_string_array_expr_comprehension(_SrcPos,
            HeadStringExpr, Generators, MaybeCondExpr),
        Str = "string_array_comprehension(" ++
            dump_tmzn_string_expr(no_parens, HeadStringExpr) ++ ", " ++
            dump_list(dump_tmzn_generator, Generators) ++ ", " ++
            dump_maybe_tmzn_bool_expr(MaybeCondExpr) ++
            ")"
    ).

dump_tmzn_general_expr(Parens, Expr) = Str :-
    (
        Expr = tmzn_gen_expr_bool(BoolExpr),
        Str = "bool(" ++ dump_tmzn_bool_expr(Parens, BoolExpr) ++ ")"
    ;
        Expr = tmzn_gen_expr_bool_array(BoolArrayExpr),
        Str = "bool_array(" ++
            dump_tmzn_bool_array_expr(Parens, BoolArrayExpr) ++ ")"
    ;
        Expr = tmzn_gen_expr_int(IntExpr),
        Str = "int(" ++ dump_tmzn_int_expr(Parens, IntExpr) ++ ")"
    ;
        Expr = tmzn_gen_expr_int_array(IntArrayExpr),
        Str = "int_array(" ++
            dump_tmzn_int_array_expr(Parens, IntArrayExpr) ++ ")"
    ;
        Expr = tmzn_gen_expr_int_set(IntSetExpr),
        Str = "int_set(" ++ dump_tmzn_int_set_expr(Parens, IntSetExpr) ++ ")"
    ;
        Expr = tmzn_gen_expr_int_set_array(IntSetArrayExpr),
        Str = "int_set_array("
            ++ dump_tmzn_int_set_array_expr(Parens, IntSetArrayExpr) ++ ")"
    ;
        Expr = tmzn_gen_expr_float(FloatExpr),
        Str = "float(" ++ dump_tmzn_float_expr(Parens, FloatExpr) ++ ")"
    ;
        Expr = tmzn_gen_expr_float_array(FloatArrayExpr),
        Str = "float_array(" ++
            dump_tmzn_float_array_expr(Parens, FloatArrayExpr) ++ ")"
    ;
        Expr = tmzn_gen_expr_float_set(FloatSetExpr),
        Str = "float_set(" ++
            dump_tmzn_float_set_expr(Parens, FloatSetExpr) ++ ")"
    ;
        Expr = tmzn_gen_expr_string(StringExpr),
        Str = "string(" ++ dump_tmzn_string_expr(Parens, StringExpr) ++ ")"
    ;
        Expr = tmzn_gen_expr_string_array(StringArrayExpr),
        Str = "string_array(" ++
            dump_tmzn_string_array_expr(Parens, StringArrayExpr) ++ ")"
    ).

%-----------------------------------------------------------------------------%

:- func dump_tmzn_generator(tmzn_generator) = string.

dump_tmzn_generator(tmzn_generator(Strings, GeneralExpr)) =
    "generator(" ++
        dump_list(dump_string, Strings) ++ ", " ++
        dump_tmzn_general_expr(no_parens, GeneralExpr) ++
    ")".

%-----------------------------------------------------------------------------%

:- func dump_maybe_tmzn_bool_expr(maybe(tmzn_bool_expr)) = string.

dump_maybe_tmzn_bool_expr(no) = "no".
dump_maybe_tmzn_bool_expr(yes(BoolExpr)) =
    "yes(" ++ dump_tmzn_bool_expr(no_parens, BoolExpr) ++ ")".

%-----------------------------------------------------------------------------%

dump_tmzn_bool_var(BoolVar) = Str :-
    (
        BoolVar = tmzn_bool_var_named(Name),
        Str = Name
    ;
        BoolVar = tmzn_bool_var_anon,
        Str = "anon_bool_var"
    ;
        BoolVar = tmzn_bool_var_array_slot(BoolArrayExpr, Indexes),
        Str =
            dump_tmzn_bool_array_expr(no_parens, BoolArrayExpr) ++
            dump_tmzn_array_indexes_in_brackets(Indexes)
    ).

dump_tmzn_bool_array_var(BoolArrayVar) = Str :-
    (
        BoolArrayVar = tmzn_bool_array_var_named(Name),
        Str = Name
    ;
        BoolArrayVar = tmzn_bool_array_var_anon,
        Str = "anon_bool_array_var"
    ).

dump_tmzn_int_var(IntVar) = Str :-
    (
        IntVar = tmzn_int_var_named(Name),
        Str = Name
    ;
        IntVar = tmzn_int_var_anon,
        Str = "anon_int_var"
    ;
        IntVar = tmzn_int_var_array_slot(IntArrayExpr, Indexes),
        Str =
            dump_tmzn_int_array_expr(no_parens, IntArrayExpr) ++
            dump_tmzn_array_indexes_in_brackets(Indexes)
    ).

dump_tmzn_int_array_var(IntArrayVar) = Str :-
    (
        IntArrayVar = tmzn_int_array_var_named(Name),
        Str = Name
    ;
        IntArrayVar = tmzn_int_array_var_anon,
        Str = "anon_int_array_var"
    ).

dump_tmzn_int_set_var(IntSetVar) = Str :-
    (
        IntSetVar = tmzn_int_set_var_named(Name),
        Str = Name
    ;
        IntSetVar = tmzn_int_set_var_anon,
        Str = "anon_int_set_var"
    ;
        IntSetVar = tmzn_int_set_var_array_slot(IntSetArrayExpr, Indexes),
        Str =
            dump_tmzn_int_set_array_expr(no_parens, IntSetArrayExpr) ++
            dump_tmzn_array_indexes_in_brackets(Indexes)
    ).

dump_tmzn_int_set_array_var(IntSetArrayVar) = Str :-
    (
        IntSetArrayVar = tmzn_int_set_array_var_named(Name),
        Str = Name
    ;
        IntSetArrayVar = tmzn_int_set_array_var_anon,
        Str = "anon_int_set_array_var"
    ).

dump_tmzn_float_var(FloatVar) = Str :-
    (
        FloatVar = tmzn_float_var_named(Name),
        Str = Name
    ;
        FloatVar = tmzn_float_var_anon,
        Str = "anon_float_var"
    ;
        FloatVar = tmzn_float_var_array_slot(FloatArrayExpr, Indexes),
        Str =
            dump_tmzn_float_array_expr(no_parens, FloatArrayExpr) ++
            dump_tmzn_array_indexes_in_brackets(Indexes)
    ).

dump_tmzn_float_array_var(FloatArrayVar) = Str :-
    (
        FloatArrayVar = tmzn_float_array_var_named(Name),
        Str = Name
    ;
        FloatArrayVar = tmzn_float_array_var_anon,
        Str = "anon_float_array_var"
    ).

dump_tmzn_float_set_var(FloatSetVar) = Str :-
    (
        FloatSetVar = tmzn_float_set_var_named(Name),
        Str = Name
    ;
        FloatSetVar = tmzn_float_set_var_anon,
        Str = "anon_float_set_var"
    ).

dump_tmzn_string_var(StringVar) = Str :-
    (
        StringVar = tmzn_string_var_named(Name),
        Str = Name
    ;
        StringVar = tmzn_string_var_anon,
        Str = "anon_string_var"
    ;
        StringVar = tmzn_string_var_array_slot(StringArrayExpr, Indexes),
        Str =
            dump_tmzn_string_array_expr(no_parens, StringArrayExpr) ++
            dump_tmzn_array_indexes_in_brackets(Indexes)
    ).

dump_tmzn_string_array_var(StringArrayVar) = Str :-
    (
        StringArrayVar = tmzn_string_array_var_named(Name),
        Str = Name
    ).

%-----------------------------------------------------------------------------%

:- func dump_tmzn_array_indexes_in_brackets(indexes) = string.

dump_tmzn_array_indexes_in_brackets(Indexes) =
    "[" ++ dump_tmzn_array_indexes("", Indexes) ++ "]".

:- func dump_tmzn_array_indexes(string, indexes) = string.

dump_tmzn_array_indexes(_, []) = "".
dump_tmzn_array_indexes(Prefix, [Index | Indexes]) =
    Prefix ++
        dump_tmzn_int_expr(no_parens, Index) ++
        dump_tmzn_array_indexes(", ", Indexes).

%-----------------------------------------------------------------------------%

:- func dump_list(func(T) = string, list(T)) = string.

dump_list(_DumpFunc, []) = "".
dump_list(DumpFunc, [Head | Tail]) =
    DumpFunc(Head) ++ dump_list_2(DumpFunc, Tail).

:- func dump_list_2(func(T) = string, list(T)) = string.

dump_list_2(_DumpFunc, []) = "".
dump_list_2(DumpFunc, [Head | Tail]) =
    ", " ++ DumpFunc(Head) ++ dump_list_2(DumpFunc, Tail).

%-----------------------------------------------------------------------------%

:- func dump_index_range(index_range) = string.

dump_index_range(index_implicit) = "int".
dump_index_range(index_range(LB, UB)) =
    dump_int(LB) ++ " to " ++ dump_int(UB).

:- func dump_bool(bool) = string.

dump_bool(no) = "no".
dump_bool(yes) = "yes".

:- func dump_int(int) = string.

dump_int(Int) = string.int_to_string(Int).

:- func dump_int_set(set(int)) = string.

dump_int_set(IntSet) = dump_list(dump_int, set.to_sorted_list(IntSet)).

:- func dump_float(float) = string.

dump_float(Float) = string.float_to_string(Float).

:- func dump_string(string) = string.

dump_string(String) = term_io.quoted_string(String).

%-----------------------------------------------------------------------------%

:- func maybe_paren_open(parens) = string.

maybe_paren_open(Parens) = Str :-
    (
        Parens = no_parens,
        Str = ""
    ;
        Parens = parens,
        Str = "("
    ).

:- func maybe_paren_close(parens) = string.

maybe_paren_close(Parens) = Str :-
    (
        Parens = no_parens,
        Str = ""
    ;
        Parens = parens,
        Str = ")"
    ).

%-----------------------------------------------------------------------------%
:- end_module output_tmzn.
%-----------------------------------------------------------------------------%
