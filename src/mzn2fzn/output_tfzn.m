%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
% Output the typed FlatZinc representation, at the caller's option either
% in the format needed for .fzn files, or in a shorter, informal format
% that is easier to read.
%
%-----------------------------------------------------------------------------%

:- module output_tfzn.
:- interface.

:- import_module output_common.
:- import_module tfzn_ast.

:- import_module io.

:- pred output_tfzn(output_opts::in, io.output_stream::in, tfzn::in,
    io::di, io::uo) is det.

:- pred output_tfzn_constraint_item(output_opts::in, io.output_stream::in,
    tfzn_item_constraint::in, io::di, io::uo) is det.

:- func bool_term_to_str(output_opts, tfzn_bool_term) = string.
:- func bool_var_to_str(output_opts, tfzn_bool_var) = string.
:- func bool_array_term_to_str(output_opts, tfzn_bool_array_term) = string.
:- func bool_array_var_to_str(output_opts, tfzn_bool_array_var) = string.

:- func int_term_to_str(output_opts, tfzn_int_term) = string.
:- func int_var_to_str(output_opts, tfzn_int_var) = string.
:- func int_array_term_to_str(output_opts, tfzn_int_array_term) = string.
:- func int_array_var_to_str(output_opts, tfzn_int_array_var) = string.

:- func int_set_term_to_str(output_opts, tfzn_int_set_term) = string.
:- func int_set_var_to_str(output_opts, tfzn_int_set_var) = string.
:- func int_set_array_term_to_str(output_opts, tfzn_int_set_array_term)
    = string.
:- func int_set_array_var_to_str(output_opts, tfzn_int_set_array_var)
    = string.

:- func float_term_to_str(output_opts, tfzn_float_term) = string.
:- func float_var_to_str(output_opts, tfzn_float_var) = string.
:- func float_array_term_to_str(output_opts, tfzn_float_array_term) = string.
:- func float_array_var_to_str(output_opts, tfzn_float_array_var) = string.

:- func float_set_term_to_str(output_opts, tfzn_float_set_term) = string.
:- func float_set_var_to_str(output_opts, tfzn_float_set_var) = string.

:- func string_term_to_str(output_opts, tfzn_string_term) = string.
:- func string_var_to_str(output_opts, tfzn_string_var) = string.

:- func general_term_to_str(output_opts, tfzn_general_term) = string.

%-----------------------------------------------------------------------------%

:- implementation.

:- import_module intset.
:- import_module output_tmzn.
:- import_module types.

:- import_module assoc_list.
:- import_module bool.
:- import_module list.
:- import_module maybe.
:- import_module pair.
:- import_module require.
:- import_module set.
:- import_module string.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

output_tfzn(Opts, OutStream, TFzn, !IO) :-
    % XXX _PredDeclItems
    TFzn = tfzn(_PredDeclItems, ParDeclItems, VarDeclItems,
        ConstraintItems, SolveItem),

    list.foldl(output_tfzn_par_decl_item(Opts, OutStream), ParDeclItems, !IO),
    list.foldl(output_tfzn_var_decl_item(Opts, OutStream), VarDeclItems, !IO),
    list.foldl(output_tfzn_constraint_item(Opts, OutStream), ConstraintItems,
        !IO),
    output_tfzn_solve_item(Opts, OutStream, SolveItem, !IO).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred output_tfzn_par_decl_item(output_opts::in, io.output_stream::in,
    tfzn_item_par_decl::in, io::di, io::uo) is det.

output_tfzn_par_decl_item(Opts, OS, ParDeclItem, !IO) :-
    ParDeclItem = tfzn_item_par_decl(TypeValue),
    (
        TypeValue = tpv_bool(Var, Bool),
        Name = bool_var_to_str(Opts, Var),
        BoolStr = bool_to_str(Bool),
        io.format(OS, "bool: %s = %s;\n", [s(Name), s(BoolStr)], !IO)
    ;
        TypeValue = tpv_bool_array(Var, Bools),
        Name = bool_array_var_to_str(Opts, Var),
        list.length(Bools, NumBools),
        BoolStrs = list.map(bool_to_str, Bools),
        BoolsStr = "[" ++ string.join_list(", ", BoolStrs) ++ "]",
        io.format(OS, "array [1..%d] of bool: %s = %s;\n",
            [i(NumBools), s(Name), s(BoolsStr)], !IO)
    ;
        TypeValue = tpv_int(Var, Int),
        Name = int_var_to_str(Opts, Var),
        IntStr = string.int_to_string(Int),
        io.format(OS, "int: %s = %s;\n", [s(Name), s(IntStr)], !IO)
    ;
        TypeValue = tpv_int_array(Var, Ints),
        Name = int_array_var_to_str(Opts, Var),
        list.length(Ints, NumInts),
        IntStrs = list.map(string.int_to_string, Ints),
        IntsStr = "[" ++ string.join_list(", ", IntStrs) ++ "]",
        io.format(OS, "array [1..%d] of int: %s = %s;\n",
            [i(NumInts), s(Name), s(IntsStr)], !IO)
    ;
        TypeValue = tpv_int_set(Var, IntSet),
        Name = int_set_var_to_str(Opts, Var),
        IntSetStr = int_set_to_str(IntSet),
        io.format(OS, "set of int: %s = %s;\n", [s(Name), s(IntSetStr)], !IO)
    ;
        TypeValue = tpv_int_set_array(Var, IntSets),
        Name = int_set_array_var_to_str(Opts, Var),
        list.length(IntSets, NumIntSets),
        IntSetStrs = list.map(int_set_to_str, IntSets),
        IntSetsStr = "[" ++ string.join_list(", ", IntSetStrs) ++ "]",
        io.format(OS, "array [1..%d] of int: %s = %s;\n",
            [i(NumIntSets), s(Name), s(IntSetsStr)], !IO)
    ;
        TypeValue = tpv_float(Var, Float),
        Name = float_var_to_str(Opts, Var),
        FloatStr = string.float_to_string(Float),
        io.format(OS, "float: %s = %s;\n", [s(Name), s(FloatStr)], !IO)
    ;
        TypeValue = tpv_float_array(Var, Floats),
        Name = float_array_var_to_str(Opts, Var),
        list.length(Floats, NumFloats),
        FloatStrs = list.map(string.float_to_string, Floats),
        FloatsStr = "[" ++ string.join_list(", ", FloatStrs) ++ "]",
        io.format(OS, "array [1..%d] of float: %s = %s;\n",
            [i(NumFloats), s(Name), s(FloatsStr)], !IO)
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred output_tfzn_var_decl_item(output_opts::in, io.output_stream::in,
    tfzn_item_var_decl::in, io::di, io::uo) is det.

output_tfzn_var_decl_item(Opts, OS, VarDeclItem, !IO) :-
    VarDeclItem = tfzn_item_var_decl(TypeMaybeValue, Anns),
    AnnsStr = var_decl_anns_to_str(Anns),
    (
        TypeMaybeValue = tftmv_bool(Var, MaybeBoolExpr),
        Name = bool_var_to_str(Opts, Var),
        io.format(OS, "var bool: %s", [s(Name)], !IO),
        (
            MaybeBoolExpr = no,
            io.format(OS, "%s;\n", [s(AnnsStr)], !IO)
        ;
            MaybeBoolExpr = yes(BoolExpr),
            BoolStr = bool_expr_to_str(Opts, BoolExpr),
            io.format(OS, " = %s%s;\n", [s(BoolStr), s(AnnsStr)], !IO)
        )
    ;
        TypeMaybeValue = tftmv_bool_array(Var, Size, MaybeBoolArrayExpr),
        Name = bool_array_var_to_str(Opts, Var),
        io.format(OS, "var array [1..%d] of bool: %s",
            [i(Size), s(Name)], !IO),
        (
            MaybeBoolArrayExpr = no,
            io.format(OS, "%s;\n", [s(AnnsStr)], !IO)
        ;
            MaybeBoolArrayExpr = yes(BoolExprs),
            BoolStrs = list.map(bool_expr_to_str(Opts), BoolExprs),
            BoolsStr = "[" ++ string.join_list(", ", BoolStrs) ++ "]",
            io.format(OS, " = %s%s;\n", [s(BoolsStr), s(AnnsStr)], !IO)
        )
    ;
        TypeMaybeValue = tftmv_int(Var, IntRange, MaybeIntExpr),
        Name = int_var_to_str(Opts, Var),
        TypeName = int_range_type_to_str(IntRange),
        io.format(OS, "var %s: %s", [s(TypeName), s(Name)], !IO),
        (
            MaybeIntExpr = no,
            io.format(OS, "%s;\n", [s(AnnsStr)], !IO)
        ;
            MaybeIntExpr = yes(IntExpr),
            IntStr = int_expr_to_str(Opts, IntExpr),
            io.format(OS, " = %s%s;\n", [s(IntStr), s(AnnsStr)], !IO)
        )
    ;
        TypeMaybeValue = tftmv_int_array(Var, IntRange, Size, MaybeIntExprs),
        Name = int_array_var_to_str(Opts, Var),
        TypeName = int_range_type_to_str(IntRange),
        io.format(OS, "array [1..%d] of var %s: %s",
            [i(Size), s(TypeName), s(Name)], !IO),
        (
            MaybeIntExprs = no,
            io.format(OS, "%s;\n", [s(AnnsStr)], !IO)
        ;
            MaybeIntExprs = yes(IntExprs),
            IntExprStrs = list.map(int_expr_to_str(Opts), IntExprs),
            IntExprsStr = "[" ++ string.join_list(", ", IntExprStrs) ++ "]",
            io.format(OS, " = %s%s;\n", [s(IntExprsStr), s(AnnsStr)], !IO)
        )
    ;
        TypeMaybeValue = tftmv_int_set(Var, IntRange, MaybeIntSetExpr),
        Name = int_set_var_to_str(Opts, Var),
        TypeName = int_range_type_to_str(IntRange),
        io.format(OS, "var set of %s: %s", [s(TypeName), s(Name)], !IO),
        (
            MaybeIntSetExpr = no,
            io.format(OS, "%s;\n", [s(AnnsStr)], !IO)
        ;
            MaybeIntSetExpr = yes(IntSetExpr),
            IntSetStr = int_set_expr_to_str(Opts, IntSetExpr),
            io.format(OS, " = %s%s;\n", [s(IntSetStr), s(AnnsStr)], !IO)
        )
    ;
        TypeMaybeValue = tftmv_int_set_array(Var, IntRange, Size,
            MaybeIntSetExprs),
        Name = int_set_array_var_to_str(Opts, Var),
        TypeName = int_range_type_to_str(IntRange),
        io.format(OS, "array [1..%d] var set of %s: %s",
            [i(Size), s(TypeName), s(Name)], !IO),
        (
            MaybeIntSetExprs = no,
            io.format(OS, "%s;\n", [s(AnnsStr)], !IO)
        ;
            MaybeIntSetExprs = yes(IntSetExprs),
            IntSetStrs = list.map(int_set_expr_to_str(Opts), IntSetExprs),
            IntSetsStr = "[" ++ string.join_list(", ", IntSetStrs) ++ "]",
            io.format(OS, " = %s%s;\n", [s(IntSetsStr), s(AnnsStr)], !IO)
        )
    ;
        TypeMaybeValue = tftmv_float(Var, FloatRange, MaybeFloatExpr),
        Name = float_var_to_str(Opts, Var),
        TypeName = float_range_type_to_str(FloatRange),
        io.format(OS, "var %s: %s", [s(TypeName), s(Name)], !IO),
        (
            MaybeFloatExpr = no,
            io.format(OS, "%s;\n", [s(AnnsStr)], !IO)
        ;
            MaybeFloatExpr = yes(FloatExpr),
            FloatStr = float_expr_to_str(Opts, FloatExpr),
            io.format(OS, " = %s%s;\n", [s(FloatStr), s(AnnsStr)], !IO)
        )
    ;
        TypeMaybeValue = tftmv_float_array(Var, FloatRange, Size,
            MaybeFloatExprs),
        Name = float_array_var_to_str(Opts, Var),
        TypeName = float_range_type_to_str(FloatRange),
        io.format(OS, "array [1..%d] of var %s: %s",
            [i(Size), s(TypeName), s(Name)], !IO),
        (
            MaybeFloatExprs = no,
            io.format(OS, "%s;\n", [s(AnnsStr)], !IO)
        ;
            MaybeFloatExprs = yes(FloatExprs),
            FloatExprStrs = list.map(float_expr_to_str(Opts), FloatExprs),
            FloatExprsStr = "[" ++ string.join_list(", ", FloatExprStrs) ++ "]",
            io.format(OS, " = %s%s;\n", [s(FloatExprsStr), s(AnnsStr)], !IO)
        )
    ).

%-----------------------------------------------------------------------------%

:- func var_decl_anns_to_str(list(tfzn_var_ann)) = string.

var_decl_anns_to_str(Anns) =
    string.append_list(list.map(var_decl_ann_to_str, Anns)).

:- func var_decl_ann_to_str(tfzn_var_ann) = string.

var_decl_ann_to_str(Ann) = Str :-
    % The implementation of this function is the converse of
    % convert_builtin_var_decl_ann in convert_to_tfzn.m.
    (
        Ann = var_ann_is_defined_var,
        BaseStr = "is_defined_var"
    ;
        Ann = var_ann_is_defined_var_eqv(_),
        unexpected($module, $pred, "var_ann_is_defined_var_eqv")
    ;
        Ann = var_ann_var_is_introduced,
        BaseStr = "var_is_introduced"
    ;
        Ann = var_ann_output_var,
        BaseStr = "output_var"
    ;
        Ann = var_ann_output_array(_),
        unexpected($module, $pred, "var_ann_output_array")
    ;
        Ann = var_ann_general(_, _),
        unexpected($module, $pred, "var_ann_general")
    ),
    Str = " :: " ++ BaseStr.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

output_tfzn_constraint_item(Opts, OS, ConstraintItem, !IO) :-
    ConstraintItem = tfzn_item_constraint(Constraint, _Anns),
    % XXX _Anns
    AnnsStr = "",
    Informal = Opts ^ oo_informal_syntax,
    (
        Informal = no,
        io.write_string(OS, "constraint ", !IO)
    ;
        Informal = yes
    ),
    (
        Constraint = tfzn_constr_array_bool(ArrayBoolOp, BoolArrayTerm,
            BoolTerm),
        (
            ArrayBoolOp = array_bool_and,
            PredName = "array_bool_and"
        ;
            ArrayBoolOp = array_bool_or,
            PredName = "array_bool_or"
        ),
        ArrayStr = bool_array_term_to_str(Opts, BoolArrayTerm),
        EltStr = bool_term_to_str(Opts, BoolTerm),
        io.format(OS, "%s(%s, %s)%s;\n",
            [s(PredName), s(ArrayStr), s(EltStr), s(AnnsStr)], !IO)
    ;
        Constraint = tfzn_constr_array_bool_element(ArrayEltOp, IndexTerm,
            BoolArrayTerm, BoolTerm, HalfReification),
        (
            ArrayEltOp = array_bool_element,
            PredName = "array_bool_element"
        ;
            ArrayEltOp = array_var_bool_element,
            PredName = "array_var_bool_element"
        ),
        IndexStr = int_term_to_str(Opts, IndexTerm),
        ArrayStr = bool_array_term_to_str(Opts, BoolArrayTerm),
        EltStr = bool_term_to_str(Opts, BoolTerm),
        half_reification_to_suffix_prefix(Opts, HalfReification,
            PredNameSuffix, ArgsSuffix, ConstrPrefix),
        (
            Informal = no,
            io.format(OS, "%s%s(%s, %s, %s%s)%s;\n",
                [s(PredName), s(PredNameSuffix), s(IndexStr), s(ArrayStr),
                s(EltStr), s(ArgsSuffix), s(AnnsStr)],
                !IO)
        ;
            Informal = yes,
            io.format(OS, "%s%s[%s] = %s%s;\n",
                [s(ConstrPrefix), s(ArrayStr), s(IndexStr), s(EltStr),
                s(AnnsStr)], !IO)
        )
    ;
        Constraint = tfzn_constr_array_int_element(ArrayEltOp, IndexTerm,
            IntArrayTerm, IntTerm, HalfReification),
        (
            ArrayEltOp = array_int_element,
            PredName = "array_int_element"
        ;
            ArrayEltOp = array_var_int_element,
            PredName = "array_var_int_element"
        ),
        IndexStr = int_term_to_str(Opts, IndexTerm),
        ArrayStr = int_array_term_to_str(Opts, IntArrayTerm),
        EltStr = int_term_to_str(Opts, IntTerm),
        half_reification_to_suffix_prefix(Opts, HalfReification,
            PredNameSuffix, ArgsSuffix, ConstrPrefix),
        (
            Informal = no,
            io.format(OS, "%s%s(%s, %s, %s%s)%s;\n",
                [s(PredName), s(PredNameSuffix), s(IndexStr), s(ArrayStr),
                s(EltStr), s(ArgsSuffix), s(AnnsStr)], !IO)
        ;
            Informal = yes,
            io.format(OS, "%s%s[%s] = %s%s;\n",
                [s(ConstrPrefix), s(ArrayStr), s(IndexStr), s(EltStr),
                s(AnnsStr)], !IO)
        )
    ;
        Constraint = tfzn_constr_array_float_element(ArrayEltOp, IndexTerm,
            FloatArrayTerm, FloatTerm, HalfReification),
        (
            ArrayEltOp = array_float_element,
            PredName = "array_float_element"
        ;
            ArrayEltOp = array_var_float_element,
            PredName = "array_var_float_element"
        ),
        IndexStr = int_term_to_str(Opts, IndexTerm),
        ArrayStr = float_array_term_to_str(Opts, FloatArrayTerm),
        EltStr = float_term_to_str(Opts, FloatTerm),
        half_reification_to_suffix_prefix(Opts, HalfReification,
            PredNameSuffix, ArgsSuffix, ConstrPrefix),
        (
            Informal = no,
            io.format(OS, "%s%s(%s, %s, %s%s)%s;\n",
                [s(PredName), s(PredNameSuffix), s(IndexStr), s(ArrayStr),
                s(EltStr), s(ArgsSuffix), s(AnnsStr)], !IO)
        ;
            Informal = yes,
            io.format(OS, "%s%s[%s] = %s%s;\n",
                [s(ConstrPrefix), s(ArrayStr), s(IndexStr), s(EltStr),
                s(AnnsStr)], !IO)
        )
    ;
        Constraint = tfzn_constr_array_int_set_element(ArrayEltOp, IndexTerm,
            IntSetArrayTerm, IntSetTerm, HalfReification),
        (
            ArrayEltOp = array_int_set_element,
            PredName = "array_set_element"
        ;
            ArrayEltOp = array_var_int_set_element,
            PredName = "array_var_set_element"
        ),
        IndexStr = int_term_to_str(Opts, IndexTerm),
        ArrayStr = int_set_array_term_to_str(Opts, IntSetArrayTerm),
        EltStr = int_set_term_to_str(Opts, IntSetTerm),
        half_reification_to_suffix_prefix(Opts, HalfReification,
            PredNameSuffix, ArgsSuffix, ConstrPrefix),
        (
            Informal = no,
            io.format(OS, "%s%s(%s, %s, %s%s)%s;\n",
                [s(PredName), s(PredNameSuffix), s(IndexStr), s(ArrayStr),
                s(EltStr), s(ArgsSuffix), s(AnnsStr)], !IO)
        ;
            Informal = yes,
            io.format(OS, "%s%s[%s] = %s%s;\n",
                [s(ConstrPrefix), s(ArrayStr), s(IndexStr), s(EltStr),
                s(AnnsStr)], !IO)
        )
    ;
        Constraint = tfzn_constr_bool_to_int(B2IOp, BoolTerm, IntVar),
        (
            B2IOp = bool_to_int,
            PredName = "bool2int"
        ),
        BoolStr = bool_term_to_str(Opts, BoolTerm),
        IntStr = int_var_to_str(Opts, IntVar),
        (
            Informal = no,
            io.format(OS, "%s(%s, %s)%s;\n",
                [s(PredName), s(BoolStr), s(IntStr), s(AnnsStr)], !IO)
        ;
            Informal = yes,
            io.format(OS, "%s = %s(%s)%s;\n",
                [s(IntStr), s(PredName), s(BoolStr), s(AnnsStr)], !IO)
        )
    ;
        Constraint = tfzn_constr_int_to_float(I2FOp, IntTerm, FloatVar),
        (
            I2FOp = int_to_float,
            PredName = "int2float"
        ),
        IntStr = int_term_to_str(Opts, IntTerm),
        FloatStr = float_var_to_str(Opts, FloatVar),
        (
            Informal = no,
            io.format(OS, "%s(%s, %s)%s;\n",
                [s(PredName), s(IntStr), s(FloatStr), s(AnnsStr)], !IO)
        ;
            Informal = yes,
            io.format(OS, "%s = %s(%s)%s;\n",
                [s(FloatStr), s(PredName), s(IntStr), s(AnnsStr)], !IO)
        )
    ;
        Constraint = tfzn_constr_bool_arith_unop(B2BOp, Arg1Term, ResultTerm),
        (
            B2BOp = bool_not,
            PredName = "bool_not",
            OpName = "not"
        ),
        Arg1Str = bool_term_to_str(Opts, Arg1Term),
        ResultStr = bool_term_to_str(Opts, ResultTerm),
        (
            Informal = no,
            io.format(OS, "%s(%s, %s)%s;\n",
                [s(PredName), s(Arg1Str), s(ResultStr), s(AnnsStr)], !IO)
        ;
            Informal = yes,
            io.format(OS, "%s = %s(%s)%s;\n",
                [s(ResultStr), s(OpName), s(Arg1Str), s(AnnsStr)], !IO)
        )
    ;
        Constraint = tfzn_constr_bool_arith_binop(BB2BOp, Arg1Term, Arg2Term,
            ResultTerm),
        (
            BB2BOp = bool_and,
            PredName = "bool_and",
            OpName = "and"
        ;
            BB2BOp = bool_or,
            PredName = "bool_or",
            OpName = "or"
        ;
            BB2BOp = bool_xor,
            PredName = "bool_xor",
            OpName = "xor"
        ),
        Arg1Str = bool_term_to_str(Opts, Arg1Term),
        Arg2Str = bool_term_to_str(Opts, Arg2Term),
        ResultStr = bool_term_to_str(Opts, ResultTerm),
        (
            Informal = no,
            io.format(OS, "%s(%s, %s, %s)%s;\n",
                [s(PredName), s(Arg1Str), s(Arg2Str), s(ResultStr),
                s(AnnsStr)], !IO)
        ;
            Informal = yes,
            io.format(OS, "%s = %s(%s, %s)%s;\n",
                [s(ResultStr), s(OpName), s(Arg1Str), s(Arg2Str), s(AnnsStr)],
                !IO)
        )
    ;
        Constraint = tfzn_constr_int_arith_unop(I2IOp, Arg1Term, ResultTerm),
        (
            I2IOp = int_abs,
            PredName = "int_abs",
            OpName = "abs"
        ;
            I2IOp = int_negate,
            PredName = "int_negate",
            OpName = "-"
        ),
        Arg1Str = int_term_to_str(Opts, Arg1Term),
        ResultStr = int_term_to_str(Opts, ResultTerm),
        (
            Informal = no,
            io.format(OS, "%s(%s, %s)%s;\n",
                [s(PredName), s(Arg1Str), s(ResultStr), s(AnnsStr)], !IO)
        ;
            Informal = yes,
            io.format(OS, "%s = %s %s %s;\n",
                [s(ResultStr), s(OpName), s(Arg1Str), s(AnnsStr)], !IO)
        )
    ;
        Constraint = tfzn_constr_int_arith_binop(BB2BOp, Arg1Term, Arg2Term,
            ResultTerm),
        (
            BB2BOp = int_plus,
            PredName = "int_plus",
            OpName = "+"
        ;
            BB2BOp = int_minus,
            PredName = "int_minus",
            OpName = "-"
        ;
            BB2BOp = int_times,
            PredName = "int_times",
            OpName = "*"
        ;
            BB2BOp = int_div,
            PredName = "int_div",
            OpName = "div"
        ;
            BB2BOp = int_mod,
            PredName = "int_mod",
            OpName = "mod"
        ;
            BB2BOp = int_min,
            PredName = "int_min",
            OpName = "min"
        ;
            BB2BOp = int_max,
            PredName = "int_max",
            OpName = "max"
        ),
        Arg1Str = int_term_to_str(Opts, Arg1Term),
        Arg2Str = int_term_to_str(Opts, Arg2Term),
        ResultStr = int_term_to_str(Opts, ResultTerm),
        (
            Informal = no,
            io.format(OS, "%s(%s, %s, %s)%s;\n",
                [s(PredName), s(Arg1Str), s(Arg2Str), s(ResultStr),
                s(AnnsStr)], !IO)
        ;
            Informal = yes,
            io.format(OS, "%s = %s %s %s%s;\n",
                [s(ResultStr), s(Arg1Str), s(OpName), s(Arg2Str), s(AnnsStr)],
                !IO)
        )
    ;
        Constraint = tfzn_constr_float_arith_unop(I2IOp, Arg1Term, ResultTerm),
        (
            I2IOp = float_abs,
            PredName = "float_abs",
            OpName = "abs"
        ;
            I2IOp = float_negate,
            PredName = "float_negate",
            OpName = "-"
        ;
            I2IOp = float_exp,
            PredName = "float_exp",
            OpName = "exp"
        ;
            I2IOp = float_sin,
            PredName = "float_sin",
            OpName = "sin"
        ;
            I2IOp = float_cos,
            PredName = "float_cos",
            OpName = "cos"
        ),
        Arg1Str = float_term_to_str(Opts, Arg1Term),
        ResultStr = float_term_to_str(Opts, ResultTerm),
        (
            Informal = no,
            io.format(OS, "%s(%s, %s)%s;\n",
                [s(PredName), s(Arg1Str), s(ResultStr), s(AnnsStr)], !IO)
        ;
            Informal = yes,
            io.format(OS, "%s = %s %s%s;\n",
                [s(ResultStr), s(OpName), s(Arg1Str), s(AnnsStr)], !IO)
        )
    ;
        Constraint = tfzn_constr_float_arith_binop(BB2BOp, Arg1Term, Arg2Term,
            ResultTerm),
        (
            BB2BOp = float_plus,
            PredName = "float_plus",
            OpName = "+"
        ;
            BB2BOp = float_minus,
            PredName = "float_minus",
            OpName = "-"
        ;
            BB2BOp = float_times,
            PredName = "float_times",
            OpName = "*"
        ;
            BB2BOp = float_div,
            PredName = "float_div",
            OpName = "/"
        ;
            BB2BOp = float_min,
            PredName = "float_min",
            OpName = "min"
        ;
            BB2BOp = float_max,
            PredName = "float_max",
            OpName = "max"
        ),
        Arg1Str = float_term_to_str(Opts, Arg1Term),
        Arg2Str = float_term_to_str(Opts, Arg2Term),
        ResultStr = float_term_to_str(Opts, ResultTerm),
        (
            Informal = no,
            io.format(OS, "%s(%s, %s, %s)%s;\n",
                [s(PredName), s(Arg1Str), s(Arg2Str), s(ResultStr),
                s(AnnsStr)], !IO)
        ;
            Informal = yes,
            io.format(OS, "%s = %s %s %s%s;\n",
                [s(ResultStr), s(Arg1Str), s(OpName), s(Arg2Str), s(AnnsStr)],
                !IO)
        )
    ;
        Constraint = tfzn_constr_bool_compare(CompareOp, Arg1Term, Arg2Term,
            Reification),
        reification_to_suffix_prefix(Opts, Reification,
            PredNameSuffix, ArgsSuffix, ConstrPrefix),
        (
            CompareOp = bool_eq,
            PredName = "bool_eq",
            OpName = "="
        ;
            CompareOp = bool_le,
            PredName = "bool_le",
            OpName = "->"
        ),
        Arg1Str = bool_term_to_str(Opts, Arg1Term),
        Arg2Str = bool_term_to_str(Opts, Arg2Term),
        (
            Informal = no,
            io.format(OS, "%s%s(%s, %s%s)%s;\n",
                [s(PredName), s(PredNameSuffix), s(Arg1Str), s(Arg2Str),
                s(ArgsSuffix), s(AnnsStr)], !IO)
        ;
            Informal = yes,
            io.format(OS, "%s%s %s %s%s;\n",
                [s(ConstrPrefix), s(Arg1Str), s(OpName), s(Arg2Str),
                s(AnnsStr)], !IO)
        )
    ;
        Constraint = tfzn_constr_int_compare(CompareOp, Arg1Term, Arg2Term,
            Reification),
        reification_to_suffix_prefix(Opts, Reification,
            PredNameSuffix, ArgsSuffix, ConstrPrefix),
        (
            CompareOp = int_eq,
            PredName = "int_eq",
            OpName = "="
        ;
            CompareOp = int_ne,
            PredName = "int_ne",
            OpName = "!="
        ;
            CompareOp = int_lt,
            PredName = "int_lt",
            OpName = "<"
        ;
            CompareOp = int_le,
            PredName = "int_le",
            OpName = "=<"
        ),
        Arg1Str = int_term_to_str(Opts, Arg1Term),
        Arg2Str = int_term_to_str(Opts, Arg2Term),
        (
            Informal = no,
            io.format(OS, "%s%s(%s, %s%s)%s;\n",
                [s(PredName), s(PredNameSuffix), s(Arg1Str), s(Arg2Str),
                s(ArgsSuffix), s(AnnsStr)], !IO)
        ;
            Informal = yes,
            io.format(OS, "%s%s %s %s%s;\n",
                [s(ConstrPrefix), s(Arg1Str), s(OpName), s(Arg2Str),
                s(AnnsStr)], !IO)
        )
    ;
        Constraint = tfzn_constr_int_set_compare(CompareOp, Arg1Term,
            Arg2Term),
        (
            CompareOp = set_eq,
            PredName = "set_eq",
            OpName = "="
        ;
            CompareOp = set_ne,
            PredName = "set_ne",
            OpName = "!="
        ;
            CompareOp = set_le,
            PredName = "set_le",
            OpName = "=<"
        ),
        Arg1Str = int_set_term_to_str(Opts, Arg1Term),
        Arg2Str = int_set_term_to_str(Opts, Arg2Term),
        (
            Informal = no,
            io.format(OS, "%s(%s, %s)%s;\n",
                [s(PredName), s(Arg1Str), s(Arg2Str), s(AnnsStr)], !IO)
        ;
            Informal = yes,
            io.format(OS, "%s %s %s%s;\n",
                [s(Arg1Str), s(OpName), s(Arg2Str), s(AnnsStr)], !IO)
        )
    ;
        Constraint = tfzn_constr_float_compare(CompareOp, Arg1Term, Arg2Term,
            Reification),
        reification_to_suffix_prefix(Opts, Reification,
            PredNameSuffix, ArgsSuffix, ConstrPrefix),
        (
            CompareOp = float_eq,
            PredName = "float_eq",
            OpName = "="
        ;
            CompareOp = float_ne,
            PredName = "float_ne",
            OpName = "!="
        ;
            CompareOp = float_lt,
            PredName = "float_lt",
            OpName = "<"
        ;
            CompareOp = float_le,
            PredName = "float_le",
            OpName = "=<"
        ),
        Arg1Str = float_term_to_str(Opts, Arg1Term),
        Arg2Str = float_term_to_str(Opts, Arg2Term),
        (
            Informal = no,
            io.format(OS, "%s%s(%s, %s%s)%s;\n",
                [s(PredName), s(PredNameSuffix), s(Arg1Str), s(Arg2Str),
                s(ArgsSuffix), s(AnnsStr)], !IO)
        ;
            Informal = yes,
            io.format(OS, "%s%s %s %s%s;\n",
                [s(ConstrPrefix), s(Arg1Str), s(OpName), s(Arg2Str),
                s(AnnsStr)], !IO)
        )
    ;
        Constraint = tfzn_constr_int_linear(LinearOp, CoeffsTerm, XsTerm,
            ValueTerm, Reification),
        reification_to_suffix_prefix(Opts, Reification,
            PredNameSuffix, ArgsSuffix, ConstrPrefix),
        (
            LinearOp = int_lin_eq,
            PredName = "int_lin_eq",
            OpName = "="
        ;
            LinearOp = int_lin_ne,
            PredName = "int_lin_ne",
            OpName = "!="
        ;
            LinearOp = int_lin_le,
            PredName = "int_lin_le",
            OpName = "=<"
        ),
        ValueStr = int_term_to_str(Opts, ValueTerm),
        CoeffsStr = int_array_term_to_str(Opts, CoeffsTerm),
        XsStr = int_array_term_to_str(Opts, XsTerm),
        (
            Informal = no,
            io.format(OS, "%s%s(%s, %s, %s%s)%s;\n",
                [s(PredName), s(PredNameSuffix), s(CoeffsStr), s(XsStr),
                s(ValueStr), s(ArgsSuffix), s(AnnsStr)], !IO)
        ;
            Informal = yes,
            ( if
                CoeffsTerm = tfzn_int_array_term_consts(Coeffs),
                XsTerm = tfzn_int_array_term_vars(Xs)
            then
                assoc_list.from_corresponding_lists(Coeffs, Xs, CoeffsXs),
                LinearExprStr = int_coeffs_xs_to_str(Opts, CoeffsXs),
                io.format(OS, "%s%s %s %s%s;\n",
                    [s(ConstrPrefix), s(LinearExprStr), s(OpName), s(ValueStr),
                    s(AnnsStr)], !IO)
            else
                io.format(OS, "%s%s(%s, %s, %s%s)%s;\n",
                    [s(PredName), s(PredNameSuffix), s(CoeffsStr), s(XsStr),
                    s(ValueStr), s(ArgsSuffix), s(AnnsStr)], !IO)
            )
        )
    ;
        Constraint = tfzn_constr_float_linear(LinearOp, CoeffsTerm, XsTerm,
            ValueTerm, Reification),
        reification_to_suffix_prefix(Opts, Reification,
            PredNameSuffix, ArgsSuffix, ConstrPrefix),
        (
            LinearOp = float_lin_eq,
            PredName = "float_lin_eq",
            OpName = "="
        ;
            LinearOp = float_lin_ne,
            PredName = "float_lin_ne",
            OpName = "!="
        ;
            LinearOp = float_lin_le,
            PredName = "float_lin_le",
            OpName = "=<"
        ),
        ValueStr = float_term_to_str(Opts, ValueTerm),
        CoeffsStr = float_array_term_to_str(Opts, CoeffsTerm),
        XsStr = float_array_term_to_str(Opts, XsTerm),
        (
            Informal = no,
            io.format(OS, "%s%s(%s, %s, %s%s)%s;\n",
                [s(PredName), s(PredNameSuffix), s(CoeffsStr), s(XsStr),
                s(ValueStr), s(ArgsSuffix), s(AnnsStr)], !IO)
        ;
            Informal = yes,
            ( if
                CoeffsTerm = tfzn_float_array_term_consts(Coeffs),
                XsTerm = tfzn_float_array_term_vars(Xs)
            then
                assoc_list.from_corresponding_lists(Coeffs, Xs, CoeffsXs),
                LinearExprStr = float_coeffs_xs_to_str(Opts, CoeffsXs),
                io.format(OS, "%s%s %s %s%s;\n",
                    [s(ConstrPrefix), s(LinearExprStr), s(OpName), s(ValueStr),
                    s(AnnsStr)], !IO)
            else
                io.format(OS, "%s%s(%s, %s, %s%s)%s;\n",
                    [s(PredName), s(PredNameSuffix), s(CoeffsStr), s(XsStr),
                    s(ValueStr), s(ArgsSuffix), s(AnnsStr)], !IO)
            )
        )
    ;
        Constraint = tfzn_constr_int_set_in(InOp, EltTerm, SetTerm,
            Reification),
        reification_to_suffix_prefix(Opts, Reification,
            PredNameSuffix, ArgsSuffix, ConstrPrefix),
        (
            InOp = set_in,
            PredName = "set_in",
            OpName = "in"
        ),
        EltStr = int_term_to_str(Opts, EltTerm),
        SetStr = int_set_term_to_str(Opts, SetTerm),
        (
            Informal = no,
            io.format(OS, "%s%s(%s, %s%s)%s;\n",
                [s(PredName), s(PredNameSuffix), s(EltStr), s(SetStr),
                s(ArgsSuffix), s(AnnsStr)], !IO)
        ;
            Informal = yes,
            io.format(OS, "%s%s %s %s%s;\n",
                [s(ConstrPrefix), s(EltStr), s(OpName), s(SetStr),
                s(AnnsStr)], !IO)
        )
    ;
        Constraint = tfzn_constr_int_set_card(CardOp, SetTerm, CardTerm),
        (
            CardOp = set_card,
            PredName = "set_card"
        ),
        SetStr = int_set_term_to_str(Opts, SetTerm),
        CardStr = int_term_to_str(Opts, CardTerm),
        io.format(OS, "%s(%s, %s)%s;\n",
            [s(PredName), s(SetStr), s(CardStr), s(AnnsStr)], !IO)
    ;
        Constraint = tfzn_constr_int_set_subset(SubsetOp, Arg1Term, Arg2Term,
            Reification),
        reification_to_suffix_prefix(Opts, Reification,
            PredNameSuffix, ArgsSuffix, ConstrPrefix),
        (
            SubsetOp = set_subset,
            PredName = "set_subset",
            OpName = "is_subset_of"
        ),
        Arg1Str = int_set_term_to_str(Opts, Arg1Term),
        Arg2Str = int_set_term_to_str(Opts, Arg2Term),
        (
            Informal = no,
            io.format(OS, "%s%s(%s, %s%s)%s;\n",
                [s(PredName), s(PredNameSuffix), s(Arg1Str), s(Arg2Str),
                s(ArgsSuffix), s(AnnsStr)], !IO)
        ;
            Informal = yes,
            io.format(OS, "%s%s %s %s%s;\n",
                [s(ConstrPrefix), s(Arg1Str), s(OpName), s(Arg2Str),
                s(AnnsStr)], !IO)
        )
    ;
        Constraint = tfzn_constr_int_set_set_op(SetSetOp, Arg1Term, Arg2Term,
            ResultTerm),
        (
            SetSetOp = set_intersect,
            PredName = "set_intersect",
            OpName = "intersect"
        ;
            SetSetOp = set_union,
            PredName = "set_union",
            OpName = "union"
        ;
            SetSetOp = set_diff,
            PredName = "set_diff",
            OpName = "diff"
        ),
        Arg1Str = int_set_term_to_str(Opts, Arg1Term),
        Arg2Str = int_set_term_to_str(Opts, Arg2Term),
        ResultStr = int_set_term_to_str(Opts, ResultTerm),
        (
            Informal = no,
            io.format(OS, "%s(%s, %s, %s)%s;\n",
                [s(PredName), s(Arg1Str), s(Arg2Str), s(ResultStr),
                s(AnnsStr)], !IO)
        ;
            Informal = yes,
            io.format(OS, "%s = %s %s %s%s;\n",
                [s(ResultStr), s(Arg1Str), s(OpName), s(Arg2Str),
                s(AnnsStr)], !IO)
        )
    ;
        Constraint = tfzn_constr_user(PredName, ArgTerms),
        ArgStrs = list.map(general_term_to_str(Opts), ArgTerms),
        ArgsStr = string.join_list(", ", ArgStrs),
        io.format(OS, "%s(%s)%s;\n",
            [s(PredName), s(ArgsStr), s(AnnsStr)], !IO)
    ).

:- pred reification_to_suffix_prefix(output_opts::in, tfzn_reification::in,
    string::out, string::out, string::out) is det.

reification_to_suffix_prefix(Opts, Reification, PredNameSuffix, ArgsSuffix,
        ConstrPrefix) :-
    (
        Reification = not_reified,
        PredNameSuffix = "",
        ArgsSuffix = "",
        ConstrPrefix = ""
    ;
        Reification = half_reified(BoolTerm),
        (
            BoolTerm = tfzn_bool_term_var(BoolVar),
            BoolStr = bool_var_to_str(Opts, BoolVar),
            PredNameSuffix = "_halfreif",
            ArgsSuffix = ", " ++ BoolStr,
            ConstrPrefix = BoolStr ++ " -> "
        ;
            BoolTerm = tfzn_bool_term_const(no),
            PredNameSuffix = "_halfreif",
            ArgsSuffix = ", false",
            ConstrPrefix = "false -> "
        ;
            BoolTerm = tfzn_bool_term_const(yes),
            PredNameSuffix = "",
            ArgsSuffix = "",
            ConstrPrefix = ""
        )
    ;
        Reification = fully_reified(BoolTerm),
        (
            BoolTerm = tfzn_bool_term_var(BoolVar),
            BoolStr = bool_var_to_str(Opts, BoolVar),
            PredNameSuffix = "_reif",
            ArgsSuffix = ", " ++ BoolStr,
            ConstrPrefix = BoolStr ++ " <-> "
        ;
            BoolTerm = tfzn_bool_term_const(no),
            PredNameSuffix = "_reif",
            ArgsSuffix = ", false",
            ConstrPrefix = "false <-> "
        ;
            BoolTerm = tfzn_bool_term_const(yes),
            PredNameSuffix = "",
            ArgsSuffix = "",
            ConstrPrefix = ""
        )
    ).

:- pred half_reification_to_suffix_prefix(output_opts::in,
    tfzn_half_reification::in, string::out, string::out, string::out) is det.

half_reification_to_suffix_prefix(Opts, HalfReification,
        PredNameSuffix, ArgsSuffix, ConstrPrefix) :-
    (
        HalfReification = hr_not_reified,
        PredNameSuffix = "",
        ArgsSuffix = "",
        ConstrPrefix = ""
    ;
        HalfReification = hr_half_reified(BoolVar),
        BoolStr = bool_var_to_str(Opts, BoolVar),
        PredNameSuffix = "_halfreif",
        ArgsSuffix = ", " ++ BoolStr,
        ConstrPrefix = BoolStr ++ " -> "
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred output_tfzn_solve_item(output_opts::in, io.output_stream::in,
    tfzn_item_solve::in, io::di, io::uo) is det.

output_tfzn_solve_item(Opts, OS, SolveItem, !IO) :-
    SolveItem = tfzn_item_solve(SolveKind, _Anns),
    % XXX _Anns
    (
        SolveKind = tfzn_sk_satisfy,
        io.format(OS, "solve satisfy;\n", [], !IO)
    ;
        SolveKind = tfzn_sk_minimize_int(IntTerm),
        IntStr = int_term_to_str(Opts, IntTerm),
        io.format(OS, "solve minimize %s;\n", [s(IntStr)], !IO)
    ;
        SolveKind = tfzn_sk_maximize_int(IntTerm),
        IntStr = int_term_to_str(Opts, IntTerm),
        io.format(OS, "solve maximize %s;\n", [s(IntStr)], !IO)
    ;
        SolveKind = tfzn_sk_minimize_float(FloatTerm),
        FloatStr = float_term_to_str(Opts, FloatTerm),
        io.format(OS, "solve minimize %s;\n", [s(FloatStr)], !IO)
    ;
        SolveKind = tfzn_sk_maximize_float(FloatTerm),
        FloatStr = float_term_to_str(Opts, FloatTerm),
        io.format(OS, "solve maximize %s;\n", [s(FloatStr)], !IO)
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

bool_term_to_str(_, tfzn_bool_term_const(Bool)) = bool_to_str(Bool).
bool_term_to_str(Opts, tfzn_bool_term_var(BoolVar)) =
    bool_var_to_str(Opts, BoolVar).

bool_var_to_str(_, tfzn_bool_var_named(Name)) = Name.
bool_var_to_str(Opts, tfzn_bool_var_tmp(N)) = Name :-
    Informal = Opts ^ oo_informal_syntax,
    NStr = string.int_to_string(N),
    (
        Informal = no,
        Name = "BOOL____" ++ string.pad_left(NStr, '0', Opts ^ oo_pad_length)
    ;
        Informal = yes,
        Name = "b" ++ NStr
    ).
bool_var_to_str(Opts, tfzn_bool_var_array_slot(ArrayVar, N)) =
    bool_array_var_to_str(Opts, ArrayVar) ++
        "[" ++ string.int_to_string(N) ++ "]".

bool_array_term_to_str(Opts, BoolArrayTerm) = Str :-
    (
        BoolArrayTerm = tfzn_bool_array_term_consts(Bools),
        BoolStrs = list.map(bool_to_str, Bools),
        Str = "[" ++ string.join_list(", ", BoolStrs) ++ "]"
    ;
        BoolArrayTerm = tfzn_bool_array_term_vars(BoolVars),
        BoolStrs = list.map(bool_var_to_str(Opts), BoolVars),
        Str = "[" ++ string.join_list(", ", BoolStrs) ++ "]"
    ;
        BoolArrayTerm = tfzn_bool_array_term_terms(BoolTerms),
        BoolStrs = list.map(bool_term_to_str(Opts), BoolTerms),
        Str = "[" ++ string.join_list(", ", BoolStrs) ++ "]"
    ;
        BoolArrayTerm = tfzn_bool_array_term_var(BoolArrayVar),
        Str = bool_array_var_to_str(Opts, BoolArrayVar)
    ).

bool_array_var_to_str(_, tfzn_bool_array_var_named(Name)) = Name.
bool_array_var_to_str(Opts, tfzn_bool_array_var_tmp(N)) = Name :-
    Informal = Opts ^ oo_informal_syntax,
    NStr = string.int_to_string(N),
    (
        Informal = no,
        Name = "BOOL_ARRAY____" ++
            string.pad_left(NStr, '0', Opts ^ oo_pad_length)
    ;
        Informal = yes,
        Name = "ba" ++ NStr
    ).

%-----------------------------------------------------------------------------%

int_term_to_str(_, tfzn_int_term_const(Int)) = string.int_to_string(Int).
int_term_to_str(Opts, tfzn_int_term_var(IntVar)) =
    int_var_to_str(Opts, IntVar).

int_var_to_str(_, tfzn_int_var_named(Name)) = Name.
int_var_to_str(Opts, tfzn_int_var_tmp(N)) = Name :-
    Informal = Opts ^ oo_informal_syntax,
    NStr = string.int_to_string(N),
    (
        Informal = no,
        Name = "INT____" ++ string.pad_left(NStr, '0', Opts ^ oo_pad_length)
    ;
        Informal = yes,
        Name = "i" ++ NStr
    ).
int_var_to_str(Opts, tfzn_int_var_array_slot(ArrayVar, N)) =
    int_array_var_to_str(Opts, ArrayVar) ++
        "[" ++ string.int_to_string(N) ++ "]".

int_array_term_to_str(Opts, IntArrayTerm) = Str :-
    (
        IntArrayTerm = tfzn_int_array_term_consts(Ints),
        IntStrs = list.map(string.int_to_string, Ints),
        Str = "[" ++ string.join_list(", ", IntStrs) ++ "]"
    ;
        IntArrayTerm = tfzn_int_array_term_vars(IntVars),
        IntStrs = list.map(int_var_to_str(Opts), IntVars),
        Str = "[" ++ string.join_list(", ", IntStrs) ++ "]"
    ;
        IntArrayTerm = tfzn_int_array_term_terms(IntTerms),
        IntStrs = list.map(int_term_to_str(Opts), IntTerms),
        Str = "[" ++ string.join_list(", ", IntStrs) ++ "]"
    ;
        IntArrayTerm = tfzn_int_array_term_var(IntArrayVar),
        Str = int_array_var_to_str(Opts, IntArrayVar)
    ).

int_array_var_to_str(_, tfzn_int_array_var_named(Name)) = Name.
int_array_var_to_str(Opts, tfzn_int_array_var_tmp(N)) = Name :-
    Informal = Opts ^ oo_informal_syntax,
    NStr = string.int_to_string(N),
    (
        Informal = no,
        Name = "INT_ARRAY____" ++
            string.pad_left(NStr, '0', Opts ^ oo_pad_length)
    ;
        Informal = yes,
        Name = "ia" ++ NStr
    ).

%-----------------------------------------------------------------------------%

int_set_term_to_str(_, tfzn_int_set_term_const(IntSet)) =
    int_set_to_str(IntSet).
int_set_term_to_str(Opts, tfzn_int_set_term_var(IntSetVar)) =
    int_set_var_to_str(Opts, IntSetVar).

int_set_var_to_str(_, tfzn_int_set_var_named(Name)) = Name.
int_set_var_to_str(Opts, tfzn_int_set_var_tmp(N)) = Name :-
    Informal = Opts ^ oo_informal_syntax,
    NStr = string.int_to_string(N),
    (
        Informal = no,
        Name = "INT_SET____" ++
            string.pad_left(NStr, '0', Opts ^ oo_pad_length)
    ;
        Informal = yes,
        Name = "is" ++ NStr
    ).
int_set_var_to_str(Opts, tfzn_int_set_var_array_slot(ArrayVar, N)) =
    int_set_array_var_to_str(Opts, ArrayVar) ++
        "[" ++ string.int_to_string(N) ++ "]".

int_set_array_term_to_str(Opts, IntSetArrayTerm) = Str :-
    (
        IntSetArrayTerm = tfzn_int_set_array_term_consts(IntSets),
        IntSetStrs = list.map(int_set_to_str, IntSets),
        Str = "[" ++ string.join_list(", ", IntSetStrs) ++ "]"
    ;
        IntSetArrayTerm = tfzn_int_set_array_term_vars(IntSetVars),
        IntSetStrs = list.map(int_set_var_to_str(Opts), IntSetVars),
        Str = "[" ++ string.join_list(", ", IntSetStrs) ++ "]"
    ;
        IntSetArrayTerm = tfzn_int_set_array_term_terms(IntSetTerms),
        IntSetStrs = list.map(int_set_term_to_str(Opts), IntSetTerms),
        Str = "[" ++ string.join_list(", ", IntSetStrs) ++ "]"
    ;
        IntSetArrayTerm = tfzn_int_set_array_term_var(IntSetArrayVar),
        Str = int_set_array_var_to_str(Opts, IntSetArrayVar)
    ).

int_set_array_var_to_str(_, tfzn_int_set_array_var_named(Name)) = Name.
int_set_array_var_to_str(Opts, tfzn_int_set_array_var_tmp(N)) = Name :-
    Informal = Opts ^ oo_informal_syntax,
    NStr = string.int_to_string(N),
    (
        Informal = no,
        Name = "INT_SET_ARRAY____" ++
            string.pad_left(NStr, '0', Opts ^ oo_pad_length)
    ;
        Informal = yes,
        Name = "isa" ++ NStr
    ).

%-----------------------------------------------------------------------------%

float_term_to_str(_, tfzn_float_term_const(Int)) = string.float_to_string(Int).
float_term_to_str(Opts, tfzn_float_term_var(IntVar)) =
    float_var_to_str(Opts, IntVar).

float_var_to_str(_, tfzn_float_var_named(Name)) = Name.
float_var_to_str(Opts, tfzn_float_var_tmp(N)) = Name :-
    Informal = Opts ^ oo_informal_syntax,
    NStr = string.int_to_string(N),
    (
        Informal = no,
        Name = "FLOAT____" ++ string.pad_left(NStr, '0', Opts ^ oo_pad_length)
    ;
        Informal = yes,
        Name = "f" ++ NStr
    ).
float_var_to_str(Opts, tfzn_float_var_array_slot(ArrayVar, N)) =
    float_array_var_to_str(Opts, ArrayVar) ++
        "[" ++ string.int_to_string(N) ++ "]".

float_array_term_to_str(Opts, FloatArrayTerm) = Str :-
    (
        FloatArrayTerm = tfzn_float_array_term_consts(Floats),
        FloatStrs = list.map(string.float_to_string, Floats),
        Str = "[" ++ string.join_list(", ", FloatStrs) ++ "]"
    ;
        FloatArrayTerm = tfzn_float_array_term_vars(FloatVars),
        FloatStrs = list.map(float_var_to_str(Opts), FloatVars),
        Str = "[" ++ string.join_list(", ", FloatStrs) ++ "]"
    ;
        FloatArrayTerm = tfzn_float_array_term_terms(FloatTerms),
        FloatStrs = list.map(float_term_to_str(Opts), FloatTerms),
        Str = "[" ++ string.join_list(", ", FloatStrs) ++ "]"
    ;
        FloatArrayTerm = tfzn_float_array_term_var(FloatArrayVar),
        Str = float_array_var_to_str(Opts, FloatArrayVar)
    ).

float_array_var_to_str(_, tfzn_float_array_var_named(Name)) = Name.
float_array_var_to_str(Opts, tfzn_float_array_var_tmp(N)) = Name :-
    Informal = Opts ^ oo_informal_syntax,
    NStr = string.int_to_string(N),
    (
        Informal = no,
        Name = "FLOAT_ARRAY____" ++
            string.pad_left(NStr, '0', Opts ^ oo_pad_length)
    ;
        Informal = yes,
        Name = "fa" ++ NStr
    ).

%-----------------------------------------------------------------------------%

float_set_term_to_str(_, tfzn_float_set_term_const(FloatSet)) =
    float_set_to_str(FloatSet).
float_set_term_to_str(Opts, tfzn_float_set_term_var(FloatSetVar)) =
    float_set_var_to_str(Opts, FloatSetVar).

float_set_var_to_str(_, tfzn_float_set_var_named(Name)) = Name.
float_set_var_to_str(Opts, tfzn_float_set_var_tmp(N)) = Name :-
    Informal = Opts ^ oo_informal_syntax,
    NStr = string.int_to_string(N),
    (
        Informal = no,
        Name = "FLOAT_SET____" ++
            string.pad_left(NStr, '0', Opts ^ oo_pad_length)
    ;
        Informal = yes,
        Name = "fs" ++ NStr
    ).

%-----------------------------------------------------------------------------%

string_term_to_str(_, tfzn_string_term_const(Str)) = Str.
string_term_to_str(Opts, tfzn_string_term_var(StrVar)) =
    string_var_to_str(Opts, StrVar).

string_var_to_str(_, tfzn_string_var_named(Name)) = Name.
string_var_to_str(Opts, tfzn_string_var_tmp(N)) = Name :-
    Informal = Opts ^ oo_informal_syntax,
    NStr = string.int_to_string(N),
    (
        Informal = no,
        Name = "String____" ++
            string.pad_left(NStr, '0', Opts ^ oo_pad_length)
    ;
        Informal = yes,
        Name = "s" ++ NStr
    ).

%-----------------------------------------------------------------------------%

general_term_to_str(Opts, GenTerm) = Str :-
    (
        GenTerm = tfzn_gen_term_bool(BoolTerm),
        Str = bool_term_to_str(Opts, BoolTerm)
    ;
        GenTerm = tfzn_gen_term_bool_array(BoolArrayTerm),
        Str = bool_array_term_to_str(Opts, BoolArrayTerm)
    ;
        GenTerm = tfzn_gen_term_int(IntTerm),
        Str = int_term_to_str(Opts, IntTerm)
    ;
        GenTerm = tfzn_gen_term_int_array(IntArrayTerm),
        Str = int_array_term_to_str(Opts, IntArrayTerm)
    ;
        GenTerm = tfzn_gen_term_int_set(IntSetTerm),
        Str = int_set_term_to_str(Opts, IntSetTerm)
    ;
        GenTerm = tfzn_gen_term_int_set_array(IntSetArrayTerm),
        Str = int_set_array_term_to_str(Opts, IntSetArrayTerm)
    ;
        GenTerm = tfzn_gen_term_float(FloatTerm),
        Str = float_term_to_str(Opts, FloatTerm)
    ;
        GenTerm = tfzn_gen_term_float_set(FloatSetTerm),
        Str = float_set_term_to_str(Opts, FloatSetTerm)
    ;
        GenTerm = tfzn_gen_term_float_array(FloatArrayTerm),
        Str = float_array_term_to_str(Opts, FloatArrayTerm)
    ;
        GenTerm = tfzn_gen_term_string(StrTerm),
        Str = string_term_to_str(Opts, StrTerm)
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- func int_coeffs_xs_to_str(output_opts,
    assoc_list(int, tfzn_int_var)) = string.

int_coeffs_xs_to_str(Opts, CoeffsXs) =
    string.join_list(" + ", list.map(int_coeff_x_to_str(Opts), CoeffsXs)).

:- func int_coeff_x_to_str(output_opts,
    pair(int, tfzn_int_var)) = string.

int_coeff_x_to_str(Opts, Coeff - X) =
    string.int_to_string(Coeff) ++ "*" ++ int_var_to_str(Opts, X).

:- func float_coeffs_xs_to_str(output_opts,
    assoc_list(float, tfzn_float_var)) = string.

float_coeffs_xs_to_str(Opts, CoeffsXs) =
    string.join_list(" + ", list.map(float_coeff_x_to_str(Opts), CoeffsXs)).

:- func float_coeff_x_to_str(output_opts,
    pair(float, tfzn_float_var)) = string.

float_coeff_x_to_str(Opts, Coeff - X) =
    string.float_to_string(Coeff) ++ "*" ++ float_var_to_str(Opts, X).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
