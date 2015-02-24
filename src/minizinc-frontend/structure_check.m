%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2006-2007 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Nicholas Nethercote <njn@csse.unimelb.edu.au>
%
% This module does some structural checking of items that doesn't require the
% symbol table, eg. that there's exactly one solve item, and no more than one
% output item.  It also checks, if the model is MiniZinc, that it doesn't
% contain any Zinc-only items.  It doesn't change the AST at all.
%-----------------------------------------------------------------------------%

:- module structure_check.
:- interface.
%-----------------------------------------------------------------------------%

:- import_module compiler_common.
:- import_module zinc_ast.

%-----------------------------------------------------------------------------%

:- pred structure_check_ast : stage(ast, sast) `with_inst` stage.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module zinc_common.
:- import_module zinc_error.

:- import_module list.
:- import_module maybe.
:- import_module require.
:- import_module string.

%-----------------------------------------------------------------------------%

    % This type is used only to reduce the number of args passed around.
    %
:- type sc_state
    --->    sc_state(
                scs_lang :: lang,
                
                scs_items :: items,        
                % Non-solve and -output items in reverse order.

                scs_solve_items  :: items,
                % Any solve items in the model.
                
                scs_output_items :: items,
                % Any output items in the model.
                
                scs_errors       :: zinc_errors
                % Accumulated errors.
            ).

%-----------------------------------------------------------------------------%

structure_check_ast(Lang, Items0, AST, Errs, /*Warns*/[]) :-
    some [!S] (
        !:S = sc_state(Lang, [], [], [], []),
        list.foldl(sc_item, Items0, !S),
        SolveItems = !.S ^ scs_solve_items,
        (
            SolveItems = [],
            structure_error([words("no solve item")], unknown, !S),
            SolveItem = sast_solve_item(satisfy, [], unknown)    % Dummy value.
        ;
            SolveItems = [SolveItem0],
            SolveItem0 = item(RawSolveItem, SolveSrcLocn),
            ( if RawSolveItem = solve_item(SolveKind, SolveAnns) then
                SolveItem = sast_solve_item(SolveKind, SolveAnns, SolveSrcLocn)
              else
                unexpected($pred, ": not a solve item")
            )
        ;
            SolveItems = [FirstSolveItem | RestSolveItems @ [_ | _]],
            RestSolveParts = list_to_parts(
                (func(I) = src_locn(I ^ item_src_locn)),
                RestSolveItems),
            MultipleSolveItemMsg = [
                words("multiple solve items."),  nl, 
                words("Other solve items are at:")
            ] ++ RestSolveParts,
            structure_error(MultipleSolveItemMsg,
                FirstSolveItem ^ item_src_locn, !S),
            FirstSolveItem = item(RawSolveItem, SolveSrcLocn),
            ( if RawSolveItem = solve_item(SolveKind, SolveAnns) then
                SolveItem = sast_solve_item(SolveKind, SolveAnns, SolveSrcLocn)
              else
                unexpected($pred, ": not a solve item")
            )
        ),
        OutputItems = !.S ^ scs_output_items,
        (
            OutputItems = [],
            MaybeOutputItem = no
        ;
            OutputItems = [OutputItem],
            MaybeOutputItem = yes(OutputItem)
        ;
            OutputItems = [FirstOutputItem | RestOutputItems @ [_ | _]],
            RestOutputParts = list_to_parts(
                (func(I) = src_locn(I ^ item_src_locn)),
                RestOutputItems),
            MultipleOutputItemMsg = [
                words("multiple output items."), nl,
                words("Other output items are at:")
            ] ++ RestOutputParts,
            structure_error(MultipleOutputItemMsg,
                FirstOutputItem ^ item_src_locn, !S),
            MaybeOutputItem = yes(FirstOutputItem)
        ),
        !.S = sc_state(_Lang, RevItems, _SolveItems, _OutputItems, Errs),
        list.reverse(RevItems, Items),
        AST = sast(Items, SolveItem, MaybeOutputItem)
    ).

%-----------------------------------------------------------------------------%
%
% Structure-check items
%

:- pred sc_item(item::in, sc_state::in, sc_state::out) is det.

sc_item(Item, !S) :-
    Item = item(RawItem, Locn),
    (
        ( RawItem = var_decl_item(_, _, _, _)
        ; RawItem = assign_item(_, _)
        ; RawItem = constraint_item(_)
        ),
        !S ^ scs_items := [Item | !.S ^ scs_items]
    ;
        RawItem = annotation_item(_, _),
        !S ^ scs_items := [Item | !.S ^ scs_items]
    ;
        RawItem = predfunc_item(Ret, _, _, _, _, MaybeBody),
        (
            Ret = func_ret(_),
            not_in_lang([lang_minizinc], "function items",
                Locn, !S)
        ;
            Ret = test_ret,
            (
                MaybeBody = no,
                not_in_lang([lang_minizinc], "test items without bodies",
                    Locn, !S)
            ;
                MaybeBody = yes(_)
            )
        ;
            Ret = pred_ret
        ),
        !S ^ scs_items := [Item | !.S ^ scs_items]
    ;
        RawItem = output_item(_),
        !S ^ scs_output_items := [Item | !.S ^ scs_output_items]
    ;
        RawItem = solve_item(_, _),
        !S ^ scs_solve_items := [Item | !.S ^ scs_solve_items]
    ).

%-----------------------------------------------------------------------------%
%
% Errors and warnings
%

:- pred structure_error(error_msg::in, src_locn::in,
    sc_state::in, sc_state::out) is det.

structure_error(ErrMsg0, Locn, S, S ^ scs_errors := Temp) :-
    ErrMsg = [words("structure error:") | ErrMsg0],
    error_at_locn(ErrMsg, Locn, S ^ scs_errors, Temp).

:- pred not_in_lang(list(lang)::in, string::in, src_locn::in,
    sc_state::in, sc_state::out) is det.

not_in_lang([], _, _, !S).
not_in_lang([Lang | Langs], What, Locn, !S) :-
    ( if !.S ^ scs_lang = Lang then
        ErrMsg = [
            words(Lang^show),
            words("does not permit"),
            words(What)
        ],
        structure_error(ErrMsg, Locn, !S)
      else
        true
    ),
    not_in_lang(Langs, What, Locn, !S).

%-----------------------------------------------------------------------------%
:- end_module structure_check.
%-----------------------------------------------------------------------------%
