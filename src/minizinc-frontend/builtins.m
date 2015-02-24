%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2006-2012 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Authors: Nicholas Nethercote <njn@csse.unimelb.edu.au>
%
% Type-inst signatures for Zinc's built-in operations:  operators, predicates
% and functions.
%-----------------------------------------------------------------------------%

:- module builtins.
:- interface.

%---------------------------------------------------------------------------%

:- import_module types_and_insts.
:- import_module zinc_common.

:- import_module list.
:- import_module pair.

%---------------------------------------------------------------------------%

    % All built-in preds/funcs/ops.
    %
:- pred is_builtin_operation(lang::in, zinc_name::in) is semidet.

    % All the built-in operators.
    %
:- pred is_operator(lang::in, zinc_name::in) is semidet.

    % All built-in annotations.
    %
:- pred is_builtin_annotation(Ctrl::in, lang::in, zinc_name::in) is semidet
    <= frontend_control(Ctrl).

    % Lists of the above and their type-inst sigs.  The type-sigs can be
    % determined from these.  There are no names repeated in the lists (ie.
    % all the sigs for each name are in the one place).
    %
:- func all_operator_ti_sigs(lang)     = list(pair(zinc_name, type_inst_sigs)).
:- func all_builtin_func_ti_sigs(lang) = list(pair(zinc_name, type_inst_sigs)).
:- func all_builtin_pred_ti_sigs(lang) = list(pair(zinc_name, type_inst_sigs)).

    % Similar, but for annotations.
    %
:- func all_builtin_ann_ti_sigs(Ctrl, lang) = list(pair(zinc_name, type_insts))
    <= frontend_control(Ctrl).

%---------------------------------------------------------------------------%
%---------------------------------------------------------------------------%

:- implementation.

:- import_module bool.
:- import_module maybe.
:- import_module solutions.

%-----------------------------------------------------------------------------%
%
% Types and Insts
%

:- func pb      = type_inst.    pb = ti_par_bool.
:- func vb      = type_inst.    vb = ti_var_bool.
:- func pi      = type_inst.    pi = ti_par_int.
:- func vi      = type_inst.    vi = ti_var_int.
:- func pf      = type_inst.    pf = ti_par_float.
:- func vf      = type_inst.    vf = ti_var_float.
:- func ps      = type_inst.    ps = ti_par_string.
:- func ann     = type_inst.    ann = ti_ann.

:- func ptv     = type_inst.    ptv  = ti_par_variable("T",no).
:- func ptv1    = type_inst.    ptv1 = ti_par_variable("T1",no).
:- func ptv2    = type_inst.    ptv2 = ti_par_variable("T2",no).
:- func ptv3    = type_inst.    ptv3 = ti_par_variable("T3",no).
:- func ptv4    = type_inst.    ptv4 = ti_par_variable("T4",no).
:- func ptv5    = type_inst.    ptv5 = ti_par_variable("T5",no).
:- func ptv6    = type_inst.    ptv6 = ti_par_variable("T6",no).
:- func ptv12   = type_inst.    ptv12  = ti_tuple([ptv1, ptv2]).
:- func ptv123  = type_inst.    ptv123 = ti_tuple([ptv1, ptv2, ptv3]).
:- func ptv1234 = type_inst.    ptv1234 = ti_tuple([ptv1, ptv2, ptv3, ptv4]).
:- func ptv12345= type_inst.    ptv12345 = ti_tuple([ptv1, ptv2, ptv3, ptv4,
                                                     ptv5]).
:- func ptv123456= type_inst.   ptv123456 = ti_tuple([ptv1, ptv2, ptv3, ptv4,
                                                      ptv5, ptv6]).
:- func puv     = type_inst.    puv  = ti_par_variable("U",no).
:- func pvv     = type_inst.    pvv  = ti_par_variable("V",no).
:- func atv     = type_inst.    atv  = ti_any_variable("T",no).
:- func auv     = type_inst.    auv  = ti_any_variable("U",no).

:- func pset_i  = type_inst.     pset_i   = ti_par_set(pi).
:- func vset_i  = type_inst.     vset_i   = ti_var_set(pi).
:- func pset_f  = type_inst.     pset_f   = ti_par_set(pf).
:- func pset_b  = type_inst.     pset_b   = ti_par_set(pb).
:- func pset_tv = type_inst.     pset_tv  = ti_par_set(ptv).
:- func vset_tv = type_inst.     vset_tv  = ti_var_set(ptv).
:- func pset_tv1 = type_inst.    pset_tv1 = ti_par_set(ptv1).
:- func pset_tv2 = type_inst.    pset_tv2 = ti_par_set(ptv2).
:- func pset_tv3 = type_inst.    pset_tv3 = ti_par_set(ptv3).
:- func pset_tv4 = type_inst.    pset_tv4 = ti_par_set(ptv4).
:- func pset_tv5 = type_inst.    pset_tv5 = ti_par_set(ptv5).
:- func pset_tv6 = type_inst.    pset_tv6 = ti_par_set(ptv6).
:- func pset_tv12 = type_inst.   pset_tv12= ti_par_set(ptv12).
:- func pset_tv123 = type_inst.  pset_tv123 = ti_par_set(ptv123).
:- func pset_tv1234 = type_inst.
pset_tv1234 = ti_par_set(ptv1234).
:- func pset_tv12345 = type_inst.
pset_tv12345 = ti_par_set(ptv12345).
:- func pset_tv123456 = type_inst.
pset_tv123456 = ti_par_set(ptv123456).
:- func pset_set_tv = type_inst. pset_set_tv = ti_par_set(ti_par_set(ptv)).

:- func arr_ann   = type_inst.  arr_ann = ti_array(pi, ann).

:- func arr_i_pi  = type_inst.  arr_i_pi = ti_array(pi, pi).
:- func arr_i_vi  = type_inst.  arr_i_vi = ti_array(pi, vi).
:- func arr_i_pf  = type_inst.  arr_i_pf = ti_array(pi, pf).
:- func arr_i_vf  = type_inst.  arr_i_vf = ti_array(pi, vf).
:- func arr_i_pb  = type_inst.  arr_i_pb = ti_array(pi, pb).
:- func arr_i_vb  = type_inst.  arr_i_vb = ti_array(pi, vb).
:- func arr_i_ps  = type_inst.  arr_i_ps = ti_array(pi, ps).

:- func arr_i_ptv = type_inst.  arr_i_ptv = ti_array(pi, ptv).
:- func arr_i_atv = type_inst.  arr_i_atv = ti_array(pi, atv).

:- func arr_i_pset_i = type_inst.   arr_i_pset_i = ti_array(pi, pset_i).
:- func arr_i_pset_f = type_inst.   arr_i_pset_f = ti_array(pi, pset_f).
:- func arr_i_pset_b = type_inst.   arr_i_pset_b = ti_array(pi, pset_b).
:- func arr_i_vset_i = type_inst.   arr_i_vset_i = ti_array(pi, vset_i).

:- func arr_tv_pb  = type_inst. arr_tv_pb  = ti_array(ptv, pb).
:- func arr_tv_pi  = type_inst. arr_tv_pi  = ti_array(ptv, pi).
:- func arr_tv_pf  = type_inst. arr_tv_pf  = ti_array(ptv, pf).
:- func arr_tv_vb  = type_inst. arr_tv_vb  = ti_array(ptv, vb).
:- func arr_tv_ps  = type_inst. arr_tv_ps  = ti_array(ptv, ps).
:- func arr_tv_vi  = type_inst. arr_tv_vi  = ti_array(ptv, vi).
:- func arr_tv_vf  = type_inst. arr_tv_vf  = ti_array(ptv, vf).
:- func arr_tv_puv = type_inst. arr_tv_puv = ti_array(ptv, puv).
:- func arr_tv_auv = type_inst. arr_tv_auv = ti_array(ptv, auv).
:- func arr_tv_vset_i = type_inst. arr_tv_vset_i = ti_array(ptv, vset_i).

:- func arr_tv1_auv   = type_inst. arr_tv1_auv   = ti_array(ptv1,   auv).
:- func arr_tv12_auv  = type_inst. arr_tv12_auv  = ti_array(ptv12,  auv).
:- func arr_tv123_auv = type_inst. arr_tv123_auv = ti_array(ptv123, auv).
:- func arr_tv1234_auv = type_inst. arr_tv1234_auv = ti_array(ptv1234, auv).
:- func arr_tv12345_auv = type_inst. arr_tv12345_auv = ti_array(ptv12345, auv).

:- func arr_tv123456_auv = type_inst.

arr_tv123456_auv = ti_array(ptv123456, auv).

:- func arr_vv_auv = type_inst. arr_vv_auv = ti_array(pvv, auv).

%-----------------------------------------------------------------------------%

:- func f7(type_inst, type_inst, type_inst, type_inst, type_inst, type_inst,
           type_inst, type_inst)                       = type_inst_sig.
:- func f6(type_inst, type_inst, type_inst, type_inst, type_inst, type_inst,
           type_inst)                                  = type_inst_sig.
:- func f5(type_inst, type_inst, type_inst, type_inst, type_inst, type_inst)
                                                       = type_inst_sig.
:- func f4(type_inst, type_inst, type_inst, type_inst, type_inst)
                                                       = type_inst_sig.
:- func f3(type_inst, type_inst, type_inst, type_inst) = type_inst_sig.
:- func f2(type_inst, type_inst,            type_inst) = type_inst_sig.
:- func f1(type_inst,                       type_inst) = type_inst_sig.
f7(TI1, TI2, TI3, TI4, TI5, TI6, TI7, RetTI) =
                           [TI1, TI2, TI3, TI4, TI5, TI6, TI7] - RetTI.
f6(TI1, TI2, TI3, TI4, TI5, TI6, RetTI) =
                                [TI1, TI2, TI3, TI4, TI5, TI6] - RetTI.
f5(TI1, TI2, TI3, TI4, TI5, RetTI) = [TI1, TI2, TI3, TI4, TI5] - RetTI.
f4(TI1, TI2, TI3, TI4,      RetTI) = [TI1, TI2, TI3, TI4     ] - RetTI.
f3(TI1, TI2, TI3,           RetTI) = [TI1, TI2, TI3          ] - RetTI.
f2(TI1, TI2,                RetTI) = [TI1, TI2               ] - RetTI.
f1(TI1,                     RetTI) = [TI1                    ] - RetTI.

:- func p4(type_inst, type_inst, type_inst, type_inst) = type_inst_sig.
:- func p3(type_inst, type_inst, type_inst           ) = type_inst_sig.
:- func p2(type_inst, type_inst                      ) = type_inst_sig.
:- func p1(type_inst                                 ) = type_inst_sig.
p4(TI1, TI2, TI3, TI4) = [TI1, TI2, TI3, TI4] - vb.
p3(TI1, TI2, TI3     ) = [TI1, TI2, TI3     ] - vb.
p2(TI1, TI2          ) = [TI1, TI2          ] - vb.
p1(TI1               ) = [TI1               ] - vb.

:- func a5(type_inst, type_inst, type_inst, type_inst, type_inst) = type_insts.
:- func a4(type_inst, type_inst, type_inst, type_inst           ) = type_insts.
:- func a3(type_inst, type_inst, type_inst                      ) = type_insts.
:- func a2(type_inst, type_inst                                 ) = type_insts.
:- func a1(type_inst                                            ) = type_insts.
:- func a0                                                        = type_insts.
a5(TI1, TI2, TI3, TI4, TI5) = [TI1, TI2, TI3, TI4, TI5].
a4(TI1, TI2, TI3, TI4     ) = [TI1, TI2, TI3, TI4     ].
a3(TI1, TI2, TI3          ) = [TI1, TI2, TI3          ].
a2(TI1, TI2               ) = [TI1, TI2               ].
a1(TI1                    ) = [TI1                    ].
a0                          = [                       ].


%-----------------------------------------------------------------------------%
% Operators and built-in functions
%-----------------------------------------------------------------------------%

is_builtin_operation(Lang, Name) :-
    ( builtin_op(Lang, Name, _)
    ; builtin_func(Lang, Name, _)
    ; builtin_pred(Lang, Name, _)
    ).

is_builtin_annotation(Ctrl, Lang, Name) :-
    ( builtin_ann(Lang, Name, _)
    ; extra_builtin_annotation(Ctrl, Lang, Name, _)
    ).

is_operator(Lang, Name) :-
    builtin_op(Lang, Name, _).

%-----------------------------------------------------------------------------%

    % Signatures of Built-in Operators

    % Nb: overloadings must be ordered from lowest to highest on the lattice.
:- func num_op     = type_inst_sigs.
:- func un_num_op  = type_inst_sigs.
:- func int_op     = type_inst_sigs.
:- func float_op   = type_inst_sigs.
:- func cmp_op_zinc = type_inst_sigs.
:- func cmp_op_minizinc = type_inst_sigs.
:- func range_op   = type_inst_sigs.
:- func in_op_z    = type_inst_sigs.
:- func in_op_m    = type_inst_sigs.
:- func set_op     = type_inst_sigs.
:- func boolset_op = type_inst_sigs.
:- func bool_op    = type_inst_sigs.
:- func not_op     = type_inst_sigs.
:- func concat_op  = type_inst_sigs.

num_op     = [f2(pi,pi,pi), f2(vi,vi,vi), f2(pf,pf,pf), f2(vf,vf,vf)].
un_num_op  = [f1(pi,pi), f1(vi,vi), f1(pf,pf), f1(vf,vf)].
int_op     = [f2(pi,pi,pi),   f2(vi,vi,vi)].
float_op   = [f2(pf,pf,pf),   f2(vf,vf,vf)].
cmp_op_zinc = [f2(ptv,ptv,pb), f2(atv,atv,vb)].

% MiniZinc only allows comparison on scalar types - not arrays.
% (See appendix E.3 of the Zinc specification.)
%
cmp_op_minizinc = [
    f2(pi, pi, pb),   % (int,        int)                -> bool
    f2(vi, vi, vb),   % (var int,    var int)            -> var bool
    f2(pf, pf, pb),   % (float,      float)              -> bool
    f2(vf, vf, vb),   % (var float,  var float)          -> var bool
    f2(pb, pb, pb),   % (bool,       bool)               -> bool
    f2(vb, vb, vb),   % (var bool,   var bool)           -> var bool
    f2(ps, ps, pb),   % (string, string)                 -> bool
    f2(pset_i, pset_i, pb), % (set of int, set of int)         -> bool
    f2(pset_b, pset_b, pb), % (set of bool, set of bool)       -> bool
    f2(pset_f, pset_f, pb), % (set of float, set of float)     -> bool
    f2(vset_i, vset_i, vb)  % (var set of int, var set of int) -> var bool
].

range_op   = [f2(pi,pi,pset_i)].
in_op_z    = [f2(ptv,pset_tv,pb), f2(atv,vset_tv,vb)].
in_op_m    = [f2(pi,pset_i,pb), f2(pb,pset_b,pb), f2(pf,pset_f,pb),
              f2(vi,vset_i,vb)].
set_op     = [f2(pset_tv, pset_tv, pset_tv), f2(vset_tv, vset_tv, vset_tv)].
boolset_op = [f2(pset_tv,pset_tv,pb), f2(vset_tv,vset_tv,vb)].
bool_op    = [f2(pb,pb,pb), f2(vb,vb,vb)].
not_op     = [f1(pb,pb), f1(vb,vb)].
concat_op  = [f2(ps,ps,ps),                         % string concat
              f2(arr_i_atv,arr_i_atv,arr_i_atv)].   % array concat

%-----------------------------------------------------------------------------%

:- pred builtin_op(lang, zinc_name, type_inst_sigs).
:- mode builtin_op(in, in,  out) is semidet.
:- mode builtin_op(in, out, out) is multi.

    % Binary-only operators (ie. excluding '+' and '-').
builtin_op(Lang,    "<->",      bool_op     ) :- zm(Lang).

builtin_op(Lang,    "<-",       bool_op     ) :- zm(Lang).
builtin_op(Lang,    "->",       bool_op     ) :- zm(Lang).

builtin_op(Lang,    "\\/",      bool_op     ) :- zm(Lang).
builtin_op(Lang,    "xor",      bool_op     ) :- zm(Lang).

builtin_op(Lang,    "/\\",      bool_op     ) :- zm(Lang).

builtin_op(lang_minizinc, CmpOpStr, TI_Sigs) :-
    ( CmpOpStr = "=="
    ; CmpOpStr = "="
    ; CmpOpStr = "!="
    ; CmpOpStr = "<"
    ; CmpOpStr = "<="
    ; CmpOpStr = ">="
    ; CmpOpStr = ">"
    ),
    TI_Sigs = cmp_op_minizinc.

builtin_op(lang_minizinc,"in",       in_op_m     ).
builtin_op(Lang,    "subset",   boolset_op  ) :- zm(Lang).
builtin_op(Lang,    "superset", boolset_op  ) :- zm(Lang).

builtin_op(Lang,    "union",    set_op      ) :- zm(Lang).
builtin_op(Lang,    "diff",     set_op      ) :- zm(Lang).
builtin_op(Lang,    "symdiff",  set_op      ) :- zm(Lang).

    % We need '..' for FlatZinc, because it's how 1..2 set literals are
    % represented internally.
builtin_op(Lang,    "..",       range_op    ) :- zmf(Lang).

builtin_op(Lang,    "+",        num_op ++ un_num_op ) :- zm(Lang).
builtin_op(Lang,    "-",        num_op ++ un_num_op ) :- zm(Lang).

builtin_op(Lang,    "*",        num_op      ) :- zm(Lang).
builtin_op(Lang,    "/",        float_op    ) :- zm(Lang).
builtin_op(Lang,    "div",      int_op      ) :- zm(Lang).
builtin_op(Lang,    "mod",      int_op      ) :- zm(Lang).
builtin_op(Lang,    "intersect",set_op      ) :- zm(Lang).

builtin_op(Lang,    "++",       concat_op   ) :- zm(Lang).

builtin_op(Lang,    "not",      not_op      ) :- zm(Lang).

%-----------------------------------------------------------------------------%

:- pred builtin_func(lang, zinc_name, type_inst_sigs).
:- mode builtin_func(in,   in,   out) is semidet.
:- mode builtin_func(in,   out,  out) is multi.

% String operations.

builtin_func(Lang, "show",        [f1(atv, ps)]) :- zm(Lang).
builtin_func(Lang, "show_int",    [f2(pi, vi, ps)]) :- zm(Lang).
builtin_func(Lang, "show_float",  [f3(pi, pi, vf, ps)]) :- zm(Lang).

% Zinc: stdlib.zinc.
builtin_func(lang_minizinc, "concat",      [f1(arr_tv_ps, ps)]).
builtin_func(lang_minizinc, "join",        [f2(ps, arr_tv_ps, ps)]).

builtin_func(Lang,  "ceil",        [f1(pf,pi)]) :- zm(Lang).
builtin_func(Lang,  "floor",       [f1(pf,pi)]) :- zm(Lang).
builtin_func(Lang,  "round",       [f1(pf,pi)]) :- zm(Lang).

    % index_set      :: (array[T1             ] of any U) -> set of T1
    % index_set_1of2 :: (array[tuple(T1,T2   )] of any U) -> set of T1
    % index_set_1of2 :: (array[tuple(T1,T2   )] of any U) -> set of T2
    % index_set_1of3 :: (array[tuple(T1,T2,T3)] of any U) -> set of T1
    % index_set_2of3 :: (array[tuple(T1,T2,T3)] of any U) -> set of T2
    % index_set_3of3 :: (array[tuple(T1,T2,T3)] of any U) -> set of T3
    % index_set_1of4 :: (array[tuple(T1,T2,T3,T4)] of any U) -> set of T1
    %
    % ... etc etc ...
    %
:- func index1arr_ati = type_inst.

index1arr_ati = ti_array(ptv1, auv).

:- func index2arr_ati = type_inst.

index2arr_ati = ti_array(ti_tuple([ptv1,ptv2]), auv).

:- func index3arr_ati = type_inst.

index3arr_ati = ti_array(ti_tuple([ptv1,ptv2,ptv3]), auv).

:- func index4arr_ati = type_inst.

index4arr_ati = ti_array(ti_tuple([ptv1,ptv2,ptv3,ptv4]), auv).

:- func index5arr_ati = type_inst.

index5arr_ati = ti_array(ti_tuple([ptv1,ptv2,ptv3,ptv4,ptv5]), auv).

builtin_func(lang_minizinc, "index_set", [f1(ti_array(pi,auv),pset_i)]).

builtin_func(Lang,  "index_set_1of2",
                    [f1(index2arr_ati,ti_par_set(ptv1))]) :- zm(Lang).
builtin_func(Lang,  "index_set_2of2",
                    [f1(index2arr_ati,ti_par_set(ptv2))]) :- zm(Lang).
builtin_func(Lang,  "index_set_1of3",
                    [f1(index3arr_ati,ti_par_set(ptv1))]) :- zm(Lang).
builtin_func(Lang,  "index_set_2of3",
                    [f1(index3arr_ati,ti_par_set(ptv2))]) :- zm(Lang).
builtin_func(Lang,  "index_set_3of3",
                    [f1(index3arr_ati,ti_par_set(ptv3))]) :- zm(Lang).

builtin_func(Lang,  "card", [f1(pset_tv,pi),  f1(vset_tv,vi)]) :- zm(Lang).


% Bound operations.

builtin_func(lang_minizinc, "lb",  [
    f1(vi,pi),                  % var int -> int.
    f1(vf,pf),                  % var float -> float
    f1(vset_i,pset_i)           % var set of int  -> set of int
]).

builtin_func(lang_minizinc, "ub", [
    f1(vi,pi),
    f1(vf,pf),
    f1(vset_i,pset_i)
]).

builtin_func(Lang,      "lb_array", [f1(arr_tv_vi,pi),
                                     f1(arr_tv_vf,pf),
                                     f1(arr_tv_vset_i,pset_i)
                                    ]) :- zm(Lang).

builtin_func(Lang,      "ub_array", [f1(arr_tv_vi,pi),
                                     f1(arr_tv_vf,pf),
                                     f1(arr_tv_vset_i,pset_i)
                                    ]) :- zm(Lang).

builtin_func(lang_minizinc, "dom",  [f1(vi,pset_i)]).

builtin_func(Lang,          "dom_array", [f1(arr_tv_vi,pset_i)]) :-
                                        zm(Lang).
builtin_func(lang_minizinc,  "dom_size",  [f1(vi,pi)]).

:- func max_fn_z = type_inst_sigs.
    % Nb: procedure 2 subsumes procedure 1, and procedure 5 subsumes procedure
    % 4.  In both cases we have both procedures because the back-end handles
    % them differently.
max_fn_z = [f2(ptv,ptv,ptv),
            f2(atv,atv,atv),
            f1(pset_tv,ptv),
            f1(arr_tv_puv,puv),
            f1(arr_tv_auv,auv)].

:- func max_fn_m = type_inst_sigs.

max_fn_m = [f2(pi,pi,pi), f2(vi,vi,vi),
            f2(pf,pf,pf), f2(vf,vf,vf),
            f1(pset_i,pi),   f1(pset_f,pf),
            f1(arr_i_pi,pi), f1(arr_i_pf,pf),
            f1(arr_i_vi,vi), f1(arr_i_vf,vf)].
builtin_func(lang_minizinc,  "min",      max_fn_m).
builtin_func(lang_minizinc,  "max",      max_fn_m).

builtin_func(Lang, "abs", un_num_op) :- zm(Lang).

builtin_func(lang_minizinc, "sum", sum_arr_fn).
builtin_func(lang_minizinc,  "product",  sum_arr_fn).  % Zinc: in stdlib.zinc

builtin_func(Lang, "pow",   [f2(pi,pi,pi), f2(pf,pf,pf)]) :- zm(Lang).
builtin_func(Lang, "sqrt",  [f1(pf,pf), f1(vf,vf)]) :- zm(Lang).
builtin_func(Lang, "ln",    [f1(pf,pf), f1(vf,vf)]) :- zm(Lang).
builtin_func(Lang, "log10", [f1(pf,pf), f1(vf,vf)]) :- zm(Lang).
builtin_func(Lang, "log2",  [f1(pf,pf),f1(vf,vf)])  :- zm(Lang).
builtin_func(Lang, "log",   [f2(pf,pf,pf)]) :- zm(Lang).
builtin_func(Lang, "exp",   [f1(pf,pf), f1(vf,vf)]) :- zm(Lang).

builtin_func(Lang, "sin",   [f1(pf,pf), f1(vf,vf)]) :- zm(Lang).
builtin_func(Lang, "cos",   [f1(pf,pf), f1(vf,vf)]) :- zm(Lang).
builtin_func(Lang, "tan",   [f1(pf,pf), f1(vf,vf)]) :- zm(Lang).
builtin_func(Lang, "asin",  [f1(pf,pf), f1(vf,vf)]) :- zm(Lang).
builtin_func(Lang, "acos",  [f1(pf,pf), f1(vf,vf)]) :- zm(Lang).
builtin_func(Lang, "atan",  [f1(pf,pf), f1(vf,vf)]) :- zm(Lang).
builtin_func(Lang, "sinh",  [f1(pf,pf), f1(vf,vf)]) :- zm(Lang).
builtin_func(Lang, "cosh",  [f1(pf,pf), f1(vf,vf)]) :- zm(Lang).
builtin_func(Lang, "tanh",  [f1(pf,pf), f1(vf,vf)]) :- zm(Lang).

builtin_func(Lang,      "length",   [f1(arr_tv_auv,pi)]) :- zm(Lang).

builtin_func(lang_minizinc,  "array_union",     arr_set_fn_m).% Zinc: in stdlib.zinc
builtin_func(lang_minizinc,  "array_intersect", arr_set_fn_m).% Zinc: in stdlib.zinc

builtin_func(Lang,      "bool2int",     [f1(pb,pi), f1(vb,vi)]) :- zm(Lang).
builtin_func(Lang,      "int2float",    [f1(pi,pf), f1(vi,vf)]) :- zm(Lang).
builtin_func(Lang,      "set2array",    [f1(pset_tv,arr_i_ptv)]) :- zm(Lang).

builtin_func(Lang,      "assert",       [f3(pb, ps, atv, atv),
                                         f2(pb, ps, pb)]) :- zm(Lang).

builtin_func(lang_minizinc, "trace",    [f2(ps, atv, atv)]).

builtin_func(Lang,      "abort",        [f1(ps, ti_par_bottom)]) :- zm(Lang).

builtin_func(Lang,   "array1d",
                     [f2(pset_tv1, arr_vv_auv,
                            arr_tv1_auv)]) :- zm(Lang).
builtin_func(Lang,   "array2d",
                     [f3(pset_tv1, pset_tv2, arr_vv_auv,
                            arr_tv12_auv)]) :- zm(Lang).
builtin_func(Lang,   "array3d",
                     [f4(pset_tv1, pset_tv2, pset_tv3, arr_vv_auv,
                            arr_tv123_auv)]) :- zm(Lang).
builtin_func(Lang,  "array4d",
                     [f5(pset_tv1, pset_tv2, pset_tv3, pset_tv4, arr_vv_auv,
                            arr_tv1234_auv)]) :- zm(Lang).
builtin_func(Lang,  "array5d",
                    [f6(pset_tv1, pset_tv2, pset_tv3, pset_tv4, pset_tv5,
                            arr_vv_auv, arr_tv12345_auv)]) :- zm(Lang).
builtin_func(Lang,  "array6d",
                    [f7(pset_tv1, pset_tv2, pset_tv3, pset_tv4, pset_tv5,
                            pset_tv6, arr_vv_auv, arr_tv123456_auv)]) :- zm(Lang).

builtin_func(Lang, "fix", [f1(atv, ptv)]) :- zm(Lang).
builtin_func(Lang, "is_fixed", [f1(atv, pb)]) :- zm(Lang).

:- func sum_arr_fn = type_inst_sigs.

sum_arr_fn = [
    f1(arr_tv_pi,pi),
    f1(arr_tv_vi,vi),
    f1(arr_tv_pf,pf),
    f1(arr_tv_vf,vf)
].

:- func arr_set_fn_m  = type_inst_sigs.

arr_set_fn_m = [
    f1(arr_i_pset_i,pset_i),
    f1(arr_i_pset_f,pset_f),
    f1(arr_i_pset_b,pset_b),
    f1(arr_i_vset_i,vset_i)
].

%-----------------------------------------------------------------------------%

:- pred builtin_pred(lang, zinc_name, type_inst_sigs).
:- mode builtin_pred(in,   in,   out) is semidet.
:- mode builtin_pred(in,   out,  out) is multi.

:- func forall_pred = type_inst_sigs.

forall_pred = [f1(arr_tv_pb, pb), f1(arr_tv_vb, vb)].

% MiniZinc predicates.

builtin_pred(lang_minizinc,  "exists", forall_pred).
builtin_pred(lang_minizinc,  "forall", forall_pred).
builtin_pred(lang_minizinc,  "iffall", forall_pred).   % Zinc: in stdlib.zinc
builtin_pred(lang_minizinc,  "xorall", forall_pred).   % Zinc: in stdlib.zinc

%-----------------------------------------------------------------------------%

:- pred builtin_ann(lang, zinc_name, type_insts).
:- mode builtin_ann(in,   in,   out) is semidet.
:- mode builtin_ann(in,   out,  out) is nondet.

    % General annotations
builtin_ann(Lang,   "null",         a0) :- zm(Lang).

    % Monitoring annotations
builtin_ann(Lang,   "watch",        a0) :- mf(Lang).
builtin_ann(Lang,   "label",        a1(ps)) :- zmf(Lang).

    % Visualization annotations
builtin_ann(Lang,   "viz",          a1(arr_ann))            :- mf(Lang).
builtin_ann(Lang,   "viztype",      a1(ps))                 :- mf(Lang).
builtin_ann(Lang,   "vizdisplay",   a1(ps))                 :- mf(Lang).
builtin_ann(Lang,   "vizpos",       a2(pi, pi))             :- mf(Lang).
builtin_ann(Lang,   "vizwidth",     a1(pi))                 :- mf(Lang).
builtin_ann(Lang,   "vizheight",    a1(pi))                 :- mf(Lang).
builtin_ann(Lang,   "vizrange",     a2(pi, pi))             :- mf(Lang).

    % Constraint annotations
builtin_ann(Lang,   "bounds",       a0)           :- zmf(Lang).
builtin_ann(Lang,   "boundsZ",      a0)           :- zmf(Lang).
builtin_ann(Lang,   "boundsR",      a0)           :- zmf(Lang).
builtin_ann(Lang,   "boundsD",      a0)           :- zmf(Lang).
builtin_ann(Lang,   "domain",       a0)           :- zmf(Lang).
builtin_ann(Lang,   "priority",     a1(pi))       :- zmf(Lang).
builtin_ann(Lang,   "multiple",     a1(arr_i_ps)) :- zmf(Lang).
builtin_ann(Lang,   "staged",       a1(arr_i_ps)) :- zmf(Lang).

    % Variable annotations
    % Nb: "bounds" is listed above -- it's both a variable annotation and a
    % constraint annotation.
builtin_ann(Lang,   "bitmap",       a2(pi,pi))      :- zmf(Lang).
builtin_ann(Lang,   "cardinality",  a0)             :- zmf(Lang).
    % Used to identify variables introduced by a source-to-source
    % transformation, such as flattening MiniZinc.
builtin_ann(Lang,   "var_is_introduced", a0)        :- zmf(Lang).
    % Used to identify "view" variables that are defined functionally in
    % terms of other variables.
builtin_ann(Lang,   "is_defined_var",  a0)          :- zmf(Lang).
builtin_ann(Lang,   "defines_var",  a1(atv))        :- zmf(Lang).

%-----------------------------------------------------------------------------%

all_operator_ti_sigs(Lang) = OperatorsList :-
    Operators = (pred(Nm-Sigs::out) is nondet :- builtin_op(Lang, Nm, Sigs)),
    solutions(Operators, OperatorsList).

all_builtin_func_ti_sigs(Lang) = NameSigsList :-
    NameSigs = (pred(Nm-Sigs::out) is nondet :- builtin_func(Lang, Nm, Sigs) ),
    solutions(NameSigs, NameSigsList).

all_builtin_pred_ti_sigs(Lang) = NameSigsList :-
    NameSigs = (pred(Nm-Sigs::out) is nondet :- builtin_pred(Lang, Nm, Sigs) ),
    solutions(NameSigs, NameSigsList).

all_builtin_ann_ti_sigs(Ctrl, Lang) = NameSigList :-
    NameSig = (pred(Nm-Sig::out) is nondet :-
        ( builtin_ann(Lang, Nm, Sig)
        ; extra_builtin_annotation(Ctrl, Lang, Nm, Sig)
        )
    ),
    solutions(NameSig, NameSigList).

%-----------------------------------------------------------------------------%
:- end_module builtins.
%-----------------------------------------------------------------------------%
