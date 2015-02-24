%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Zoltan Somogyi
%
% Operations on global variables.
%
%-----------------------------------------------------------------------------%

:- module translate.vars.
:- interface.

:- import_module tfzn_ast.
:- import_module tmzn_ast.
:- import_module types.

:- import_module bool.
:- import_module list.
:- import_module map.
:- import_module maybe.

%-----------------------------------------------------------------------------%

:- type var_info_maps.

:- type var_info_map_bool
    == map(tfzn_bool_var, var_info_bool).
:- type var_info_map_bool_array
    == map(tfzn_bool_array_var, var_info_bool_array).
:- type var_info_map_int
    == map(tfzn_int_var, var_info_int).
:- type var_info_map_int_array
    == map(tfzn_int_array_var, var_info_int_array).
:- type var_info_map_float
    == map(tfzn_float_var, var_info_float).
:- type var_info_map_float_array
    == map(tfzn_float_array_var, var_info_float_array).

:- type var_info_bool
    --->    var_info_bool(
                vib_inst            :: var_inst,
                vib_output          :: var_output,
                vib_is_known        :: maybe(bool), % simplified bounds
                vib_maybe_expr      :: maybe(tmzn_bool_expr)
            ).

:- type var_info_bool_array
    --->    var_info_bool_array(
                viba_inst           :: var_inst,
                viba_output         :: var_output,
                viba_index_ranges   :: index_ranges,
                viba_maybe_expr     :: maybe(list(tmzn_bool_expr))
            ).

:- type var_info_int
    --->    var_info_int(
                vii_inst            :: var_inst,
                vii_output          :: var_output,
                vii_bounds          :: bounds_int,
                vii_maybe_expr      :: maybe(tmzn_int_expr)
            ).

:- type var_info_int_array
    --->    var_info_int_array(
                viia_inst           :: var_inst,
                viia_output         :: var_output,
                viia_bounds         :: bounds_int,
                viia_index_ranges   :: index_ranges,
                viia_maybe_expr     :: maybe(list(tmzn_int_expr))
            ).

:- type var_info_float
    --->    var_info_float(
                vif_inst            :: var_inst,
                vif_output          :: var_output,
                vif_bounds          :: bounds_float,
                vif_maybe_expr      :: maybe(tmzn_float_expr)
            ).

:- type var_info_float_array
    --->    var_info_float_array(
                vifa_inst           :: var_inst,
                vifa_output         :: var_output,
                vifa_bounds         :: bounds_float,
                vifa_index_ranges   :: index_ranges,
                vifa_maybe_expr     :: maybe(list(tmzn_float_expr))
            ).

%-----------------------------------------------------------------------------%

:- type bounds_int
    --->    int_bounds_range(
                ibr_lower           :: int,
                ibr_upper           :: int
            ).

:- type bounds_float
    --->    float_bounds_range(
                fbr_lower           :: float,
                fbr_upper           :: float
            ).

%-----------------------------------------------------------------------------%

:- func init_var_info_maps = var_info_maps.

%-----------------------------------------------------------------------------%

:- pred vim_get_par_var_decls(var_info_maps::in,
    list(tfzn_item_par_decl)::out, list(tfzn_item_var_decl)::out) is det.

%-----------------------------------------------------------------------------%

:- pred vim_get_bool_map(var_info_maps::in,
    var_info_map_bool::out) is det.
:- pred vim_get_bool_array_map(var_info_maps::in,
    var_info_map_bool_array::out) is det.
:- pred vim_get_int_map(var_info_maps::in,
    var_info_map_int::out) is det.
:- pred vim_get_int_array_map(var_info_maps::in,
    var_info_map_int_array::out) is det.
:- pred vim_get_float_map(var_info_maps::in,
    var_info_map_float::out) is det.
:- pred vim_get_float_array_map(var_info_maps::in,
    var_info_map_float_array::out) is det.

:- pred vim_set_bool_map(var_info_map_bool::in,
    var_info_maps::in, var_info_maps::out) is det.
:- pred vim_set_bool_array_map(var_info_map_bool_array::in,
    var_info_maps::in, var_info_maps::out) is det.
:- pred vim_set_int_map(var_info_map_int::in,
    var_info_maps::in, var_info_maps::out) is det.
:- pred vim_set_int_array_map(var_info_map_int_array::in,
    var_info_maps::in, var_info_maps::out) is det.
:- pred vim_set_float_map(var_info_map_float::in,
    var_info_maps::in, var_info_maps::out) is det.
:- pred vim_set_float_array_map(var_info_map_float_array::in,
    var_info_maps::in, var_info_maps::out) is det.

%-----------------------------------------------------------------------------%

:- implementation.

:- import_module pair.
:- import_module require.

:- type var_info_maps
    --->    var_info_maps(
                % XXX More to come.
                vim_bool            :: var_info_map_bool,
                vim_bool_array      :: var_info_map_bool_array,
                vim_int             :: var_info_map_int,
                vim_int_array       :: var_info_map_int_array,
                vim_float           :: var_info_map_float,
                vim_float_array     :: var_info_map_float_array
            ).

init_var_info_maps = VarInfoMaps :-
    map.init(BoolMap),
    map.init(BoolArrayMap),
    map.init(IntMap),
    map.init(IntArrayMap),
    map.init(FloatMap),
    map.init(FloatArrayMap),
    VarInfoMaps = var_info_maps(
        BoolMap, BoolArrayMap,
        IntMap, IntArrayMap,
        FloatMap, FloatArrayMap).

%-----------------------------------------------------------------------------%

vim_get_par_var_decls(VarInfoMaps, ParDecls, VarDecls) :-
    % XXX implement the equivalent of topsorted_vars
    % XXX implement the equivalent of prune_redundant_is_defined_var_anns
    % XXX implement the equivalent of prune_redundant_defines_var_ann

    VarInfoMaps = var_info_maps(
        BoolMap, BoolArrayMap,
        IntMap, IntArrayMap,
        FloatMap, FloatArrayMap),
    map.to_assoc_list(BoolMap, BoolPairs),
    map.to_assoc_list(BoolArrayMap, BoolArrayPairs),
    map.to_assoc_list(IntMap, IntPairs),
    map.to_assoc_list(IntArrayMap, IntArrayPairs),
    map.to_assoc_list(FloatMap, FloatPairs),
    map.to_assoc_list(FloatArrayMap, FloatArrayPairs),
    some [!RevParDecls, !RevVarDecls] (
        !:RevParDecls = [],
        !:RevVarDecls = [],
        list.foldl2(vim_get_par_var_decl_bool, BoolPairs,
            !RevParDecls, !RevVarDecls),
        list.foldl2(vim_get_par_var_decl_bool_array, BoolArrayPairs,
            !RevParDecls, !RevVarDecls),
        list.foldl2(vim_get_par_var_decl_int, IntPairs,
            !RevParDecls, !RevVarDecls),
        list.foldl2(vim_get_par_var_decl_int_array, IntArrayPairs,
            !RevParDecls, !RevVarDecls),
        list.foldl2(vim_get_par_var_decl_float, FloatPairs,
            !RevParDecls, !RevVarDecls),
        list.foldl2(vim_get_par_var_decl_float_array, FloatArrayPairs,
            !RevParDecls, !RevVarDecls),
        list.reverse(!.RevParDecls, ParDecls),
        list.reverse(!.RevVarDecls, VarDecls)
    ).

:- pred vim_get_par_var_decl_bool(
    pair(tfzn_bool_var, var_info_bool)::in,
    list(tfzn_item_par_decl)::in, list(tfzn_item_par_decl)::out,
    list(tfzn_item_var_decl)::in, list(tfzn_item_var_decl)::out) is det.

vim_get_par_var_decl_bool(Var - VarInfo, !RevParDecls, !RevVarDecls) :-
    VarInfo = var_info_bool(VarInst, VarOutput, IsKnown, MaybeExpr),
    (
        IsKnown = yes(KnownValue),
        % It is ok for VarInst to be either var_is_par or var_is_var.
        TypeValue = tpv_bool(Var, KnownValue),
        ParDecl = tfzn_item_par_decl(TypeValue),
        !:RevParDecls = [ParDecl | !.RevParDecls]
    ;
        IsKnown = no,
        expect(unify(VarInst, var_is_var), $module, $pred,
            "bool var with unknown value is not var_is_var"),
        TypeMaybeValue = tftmv_bool(Var, MaybeExpr),
        (
            VarOutput = var_is_not_output,
            OutputAnns = []
        ;
            VarOutput = var_is_output,
            OutputAnns = [var_ann_output_var]
        ),
        (
            ( Var = tfzn_bool_var_named(_)
            ; Var = tfzn_bool_var_array_slot(_, _)
            ),
            IntroducedAnns = []
        ;
            Var = tfzn_bool_var_tmp(_),
            IntroducedAnns = [var_ann_var_is_introduced]
        ),
        % XXX Anns any more? is_defined_var?
        Anns = OutputAnns ++ IntroducedAnns,
        VarDecl = tfzn_item_var_decl(TypeMaybeValue, Anns),
        !:RevVarDecls = [VarDecl | !.RevVarDecls]
    ).

:- pred vim_get_par_var_decl_bool_array(
    pair(tfzn_bool_array_var, var_info_bool_array)::in,
    list(tfzn_item_par_decl)::in, list(tfzn_item_par_decl)::out,
    list(tfzn_item_var_decl)::in, list(tfzn_item_var_decl)::out) is det.

vim_get_par_var_decl_bool_array(Var - VarInfo, !RevParDecls, !RevVarDecls) :-
    VarInfo = var_info_bool_array(VarInst, VarOutput, IndexRanges,
        MaybeBoolExprs),
    ( if
        MaybeBoolExprs = yes(BoolExprs),
        list.map(try_project_bool_expr_to_const, BoolExprs, Bools)
    then
        % It is ok for VarInst to be either var_is_par or var_is_var.
        TypeValue = tpv_bool_array(Var, Bools),
        ParDecl = tfzn_item_par_decl(TypeValue),
        !:RevParDecls = [ParDecl | !.RevParDecls]
    else
        expect(unify(VarInst, var_is_var), $module, $pred,
            "bool array var with unknown value is not var_is_var"),
        Size = index_ranges_to_size(IndexRanges),
        TypeMaybeValue = tftmv_bool_array(Var, Size, MaybeBoolExprs),
        (
            VarOutput = var_is_not_output,
            OutputAnns = []
        ;
            VarOutput = var_is_output,
            OutputAnns = [var_ann_output_array(IndexRanges)]
        ),
        (
            Var = tfzn_bool_array_var_named(_),
            IntroducedAnns = []
        ;
            Var = tfzn_bool_array_var_tmp(_),
            IntroducedAnns = [var_ann_var_is_introduced]
        ),
        % XXX Anns any more? is_defined_var?
        Anns = OutputAnns ++ IntroducedAnns,
        VarDecl = tfzn_item_var_decl(TypeMaybeValue, Anns),
        !:RevVarDecls = [VarDecl | !.RevVarDecls]
    ).

:- pred vim_get_par_var_decl_int(
    pair(tfzn_int_var, var_info_int)::in,
    list(tfzn_item_par_decl)::in, list(tfzn_item_par_decl)::out,
    list(tfzn_item_var_decl)::in, list(tfzn_item_var_decl)::out) is det.

vim_get_par_var_decl_int(Var - VarInfo, !RevParDecls, !RevVarDecls) :-
    VarInfo = var_info_int(VarInst, VarOutput, Bounds, MaybeExpr),
    Bounds = int_bounds_range(LB, UB),
    ( if LB = UB then
        % It is ok for VarInst to be either var_is_par or var_is_var.
        TypeValue = tpv_int(Var, LB),
        ParDecl = tfzn_item_par_decl(TypeValue),
        !:RevParDecls = [ParDecl | !.RevParDecls]
    else
        expect(unify(VarInst, var_is_var), $module, $pred,
            "int var with unknown value is not var_is_var"),
        ( if ( LB = int_minus_infinity ; UB = int_plus_infinity ) then
            IntRange = int_range_unbounded
        else
            IntRange = int_range_lb_ub(LB, UB)
        ),
        TypeMaybeValue = tftmv_int(Var, IntRange, MaybeExpr),
        (
            VarOutput = var_is_not_output,
            OutputAnns = []
        ;
            VarOutput = var_is_output,
            OutputAnns = [var_ann_output_var]
        ),
        (
            ( Var = tfzn_int_var_named(_)
            ; Var = tfzn_int_var_array_slot(_, _)
            ),
            IntroducedAnns = []
        ;
            Var = tfzn_int_var_tmp(_),
            IntroducedAnns = [var_ann_var_is_introduced]
        ),
        % XXX Anns any more? is_defined_var?
        Anns = OutputAnns ++ IntroducedAnns,
        VarDecl = tfzn_item_var_decl(TypeMaybeValue, Anns),
        !:RevVarDecls = [VarDecl | !.RevVarDecls]
    ).

:- pred vim_get_par_var_decl_int_array(
    pair(tfzn_int_array_var, var_info_int_array)::in,
    list(tfzn_item_par_decl)::in, list(tfzn_item_par_decl)::out,
    list(tfzn_item_var_decl)::in, list(tfzn_item_var_decl)::out) is det.

vim_get_par_var_decl_int_array(Var - VarInfo, !RevParDecls, !RevVarDecls) :-
    VarInfo = var_info_int_array(VarInst, VarOutput, Bounds, IndexRanges,
        MaybeIntExprs),
    ( if
        MaybeIntExprs = yes(IntExprs),
        list.map(try_project_int_expr_to_const, IntExprs, Ints)
    then
        % It is ok for VarInst to be either var_is_par or var_is_var.
        TypeValue = tpv_int_array(Var, Ints),
        ParDecl = tfzn_item_par_decl(TypeValue),
        !:RevParDecls = [ParDecl | !.RevParDecls]
    else
        expect(unify(VarInst, var_is_var), $module, $pred,
            "int array var with unknown value is not var_is_var"),
        Bounds = int_bounds_range(LB, UB),
        ( if ( LB = int_minus_infinity ; UB = int_plus_infinity ) then
            IntRange = int_range_unbounded
        else
            IntRange = int_range_lb_ub(LB, UB)
        ),
        Size = index_ranges_to_size(IndexRanges),
        TypeMaybeValue = tftmv_int_array(Var, IntRange, Size, MaybeIntExprs),
        (
            VarOutput = var_is_not_output,
            OutputAnns = []
        ;
            VarOutput = var_is_output,
            OutputAnns = [var_ann_output_array(IndexRanges)]
        ),
        (
            Var = tfzn_int_array_var_named(_),
            IntroducedAnns = []
        ;
            Var = tfzn_int_array_var_tmp(_),
            IntroducedAnns = [var_ann_var_is_introduced]
        ),
        % XXX Anns any more? is_defined_var?
        Anns = OutputAnns ++ IntroducedAnns,
        VarDecl = tfzn_item_var_decl(TypeMaybeValue, Anns),
        !:RevVarDecls = [VarDecl | !.RevVarDecls]
    ).

:- pred vim_get_par_var_decl_float(
    pair(tfzn_float_var, var_info_float)::in,
    list(tfzn_item_par_decl)::in, list(tfzn_item_par_decl)::out,
    list(tfzn_item_var_decl)::in, list(tfzn_item_var_decl)::out) is det.

vim_get_par_var_decl_float(Var - VarInfo, !RevParDecls, !RevVarDecls) :-
    VarInfo = var_info_float(VarInst, VarOutput, Bounds, MaybeExpr),
    Bounds = float_bounds_range(LB, UB),
    ( if LB = UB then
        % It is ok for VarInst to be either var_is_par or var_is_var.
        TypeValue = tpv_float(Var, LB),
        ParDecl = tfzn_item_par_decl(TypeValue),
        !:RevParDecls = [ParDecl | !.RevParDecls]
    else
        expect(unify(VarInst, var_is_var), $module, $pred,
            "float var with unknown value is not var_is_var"),
        ( if ( LB = float_minus_infinity ; UB = float_plus_infinity ) then
            IntRange = float_range_unbounded
        else
            IntRange = float_range_lb_ub(LB, UB)
        ),
        TypeMaybeValue = tftmv_float(Var, IntRange, MaybeExpr),
        (
            VarOutput = var_is_not_output,
            OutputAnns = []
        ;
            VarOutput = var_is_output,
            OutputAnns = [var_ann_output_var]
        ),
        (
            ( Var = tfzn_float_var_named(_)
            ; Var = tfzn_float_var_array_slot(_, _)
            ),
            IntroducedAnns = []
        ;
            Var = tfzn_float_var_tmp(_),
            IntroducedAnns = [var_ann_var_is_introduced]
        ),
        % XXX Anns any more? is_defined_var?
        Anns = OutputAnns ++ IntroducedAnns,
        VarDecl = tfzn_item_var_decl(TypeMaybeValue, Anns),
        !:RevVarDecls = [VarDecl | !.RevVarDecls]
    ).

:- pred vim_get_par_var_decl_float_array(
    pair(tfzn_float_array_var, var_info_float_array)::in,
    list(tfzn_item_par_decl)::in, list(tfzn_item_par_decl)::out,
    list(tfzn_item_var_decl)::in, list(tfzn_item_var_decl)::out) is det.

vim_get_par_var_decl_float_array(Var - VarInfo, !RevParDecls, !RevVarDecls) :-
    VarInfo = var_info_float_array(VarInst, VarOutput, Bounds, IndexRanges,
        MaybeFloatExprs),
    ( if
        MaybeFloatExprs = yes(FloatExprs),
        list.map(try_project_float_expr_to_const, FloatExprs, Floats)
    then
        % It is ok for VarInst to be either var_is_par or var_is_var.
        TypeValue = tpv_float_array(Var, Floats),
        ParDecl = tfzn_item_par_decl(TypeValue),
        !:RevParDecls = [ParDecl | !.RevParDecls]
    else
        expect(unify(VarInst, var_is_var), $module, $pred,
            "float array var with unknown value is not var_is_var"),
        Bounds = float_bounds_range(LB, UB),
        ( if ( LB = float_minus_infinity ; UB = float_plus_infinity ) then
            FloatRange = float_range_unbounded
        else
            FloatRange = float_range_lb_ub(LB, UB)
        ),
        Size = index_ranges_to_size(IndexRanges),
        TypeMaybeValue = tftmv_float_array(Var, FloatRange, Size,
            MaybeFloatExprs),
        (
            VarOutput = var_is_not_output,
            OutputAnns = []
        ;
            VarOutput = var_is_output,
            OutputAnns = [var_ann_output_array(IndexRanges)]
        ),
        (
            Var = tfzn_float_array_var_named(_),
            IntroducedAnns = []
        ;
            Var = tfzn_float_array_var_tmp(_),
            IntroducedAnns = [var_ann_var_is_introduced]
        ),
        % XXX Anns any more? is_defined_var?
        Anns = OutputAnns ++ IntroducedAnns,
        VarDecl = tfzn_item_var_decl(TypeMaybeValue, Anns),
        !:RevVarDecls = [VarDecl | !.RevVarDecls]
    ).

%-----------------------------------------------------------------------------%

vim_get_bool_map(VarInfoMaps, BoolMap) :-
    BoolMap = VarInfoMaps ^ vim_bool.
vim_get_bool_array_map(VarInfoMaps, BoolArrayMap) :-
    BoolArrayMap = VarInfoMaps ^ vim_bool_array.
vim_get_int_map(VarInfoMaps, IntMap) :-
    IntMap = VarInfoMaps ^ vim_int.
vim_get_int_array_map(VarInfoMaps, IntArrayMap) :-
    IntArrayMap = VarInfoMaps ^ vim_int_array.
vim_get_float_map(VarInfoMaps, FloatMap) :-
    FloatMap = VarInfoMaps ^ vim_float.
vim_get_float_array_map(VarInfoMaps, FloatArrayMap) :-
    FloatArrayMap = VarInfoMaps ^ vim_float_array.

vim_set_bool_map(BoolMap, !VarInfoMaps) :-
    !VarInfoMaps ^ vim_bool := BoolMap.
vim_set_bool_array_map(BoolArrayMap, !VarInfoMaps) :-
    !VarInfoMaps ^ vim_bool_array := BoolArrayMap.
vim_set_int_map(IntMap, !VarInfoMaps) :-
    !VarInfoMaps ^ vim_int := IntMap.
vim_set_int_array_map(IntArrayMap, !VarInfoMaps) :-
    !VarInfoMaps ^ vim_int_array := IntArrayMap.
vim_set_float_map(FloatMap, !VarInfoMaps) :-
    !VarInfoMaps ^ vim_float := FloatMap.
vim_set_float_array_map(FloatArrayMap, !VarInfoMaps) :-
    !VarInfoMaps ^ vim_float_array := FloatArrayMap.

%-----------------------------------------------------------------------------%
:- end_module translate.vars.
%-----------------------------------------------------------------------------%
