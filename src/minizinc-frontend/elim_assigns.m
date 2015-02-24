%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2012 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Julien Fischer <juliensf@csse.unimelb.edu.au>
%
% This module eliminates separate assignment items from the model by
% hoisting the assignment into the corresponding variable declaration.
% If there are multiple assignments for a variable then it will emit an
% error message.
%
%-----------------------------------------------------------------------------%


:- module elim_assigns.
:- interface.

:- import_module compiler_common.
:- import_module zinc_ast.

%-----------------------------------------------------------------------------%

:- pred eliminate_assignments : stage(ast, ast) `with_inst` stage.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module zinc_common.
:- import_module zinc_error.

:- import_module list.
:- import_module map.
:- import_module multi_map.
:- import_module require.
:- import_module string.

%-----------------------------------------------------------------------------%

eliminate_assignments(Lang, Items0, Items, !:Errs, Warns) :-
    else_unexpected(is_lang(Lang, [lang_minizinc]),
        $pred ++ ": unexpected language " ++ Lang ^ string),
    some [!AssignMap] (
        multi_map.init(!:AssignMap),
        list.foldl2(gather_assignment, Items0, !AssignMap, [], NonAssignItems0),
        list.foldl3(hoist_assignment, NonAssignItems0, !AssignMap,
            [], NonAssignItems, [], !:Errs),
        %
        % At this point it is possible for there to some assignments remaining
        % in the assignment map, e.g. because a variable declaration is 
        % missing from the model, put any such residual assignments back into
        % the AST - symbol checking will emit an appropriate error for them.
        %
        map.foldl(restore_residual_assignment, !.AssignMap, NonAssignItems,
            Items)
    ),
    Warns = [].

% Items, Errs, HoistedAssigns
% delete keys that were used.

%-----------------------------------------------------------------------------%

:- type assign_info
    --->    assign_info(
                assign_info_value :: expr,
                assign_info_locn  :: src_locn
            ).

:- type assign_map == multi_map(zinc_name, assign_info).

:- pred gather_assignment(item::in, assign_map::in, assign_map::out,
    items::in, items::out) is det.

gather_assignment(Item, !AssignMap, !NonAssignItems) :-
    Item = item(RawItem, SrcLocn),
    (
        ( RawItem = constraint_item(_)
        ; RawItem = var_decl_item(_, _, _, _)
        ; RawItem = predfunc_item(_, _, _, _, _, _)
        ; RawItem = annotation_item(_, _)
        ; RawItem = solve_item(_, _)
        ; RawItem = output_item(_)
        ),
        !:NonAssignItems = [Item | !.NonAssignItems]
    ;
        RawItem = assign_item(Name, Value),
        AssignInfo = assign_info(Value, SrcLocn),
        multi_map.add(Name, AssignInfo, !AssignMap)
    ).        

%-----------------------------------------------------------------------------%

:- pred hoist_assignment(item::in, assign_map::in, assign_map::out,
    items::in, items::out, zinc_errors::in, zinc_errors::out) is det.

hoist_assignment(Item0, !AssignMap, !Items, !Errs) :-
    Item0 = item(RawItem0, SrcLocn),
    (
        RawItem0 = var_decl_item(TIE, Name, Anns, VarDeclAssign0),
        ( if multi_map.search(!.AssignMap, Name, Assigns) then
            (
                Assigns = [],
                unexpected($pred, "missing assignment values")
            ;
                Assigns = [AssignInfo],
                (
                    VarDeclAssign0 = no_assignment,
                    AssignInfo = assign_info(Value, AssignSrcLocn),
                    VarDeclAssign = separate_assignment(AssignSrcLocn, Value),
                    RawItem =  var_decl_item(TIE, Name, Anns, VarDeclAssign),
                    Item = item(RawItem, SrcLocn),
                    !:Items = [Item | !.Items],
                    multi_map.delete(Name, !AssignMap)
                ;
                    VarDeclAssign0 = rhs_assignment(RHSValue),
                    AllAssigns = [assign_info(RHSValue, SrcLocn) | Assigns],
                    report_multiple_assignment_error(SrcLocn, Name, AllAssigns,
                        !Errs)
                ;
                    VarDeclAssign0 = separate_assignment(_, _),
                    unexpected($pred,
                        "separate assignment during elim_assigns")
                )
            ;
                Assigns = [_, _ | _],
                ( 
                    VarDeclAssign0 = no_assignment,
                    AllAssigns = Assigns
                ;
                    VarDeclAssign0 = rhs_assignment(RHSValue),
                    AllAssigns = [assign_info(RHSValue, SrcLocn) | Assigns]
                ;
                    VarDeclAssign0 = separate_assignment(_, _),
                    unexpected($pred,
                        "separate assignment during elim_assigns")
                ),
                report_multiple_assignment_error(SrcLocn, Name, AllAssigns,
                    !Errs)
            )
        else
            !:Items = [Item0 | !.Items]
        )
    ;
        ( RawItem0 = constraint_item(_)
        ; RawItem0 = predfunc_item(_, _, _, _, _, _)
        ; RawItem0 = annotation_item(_, _)
        ; RawItem0 = solve_item(_, _)
        ; RawItem0 = output_item(_)
        ),
        !:Items = [Item0 | !.Items]
    ;
        RawItem0 = assign_item(_, _),
        unexpected($pred, "assign item outside of assign_map")
    ). 

%-----------------------------------------------------------------------------%
                    
:- pred report_multiple_assignment_error(src_locn::in, zinc_name::in,
    list(assign_info)::in(non_empty_list),
    zinc_errors::in, zinc_errors::out) is det.

report_multiple_assignment_error(VarSrcLocn, Name, Assigns, !Errs) :-
    ErrMsgHead = [
        words("error: multiple assignments for global variable"),
            suffix(quote(Name), "."),
        nl,
        words("The assignments occur at: "), nl
    ],
    AssignLocns0 = list.map(get_src_locn, Assigns),
    list.sort(AssignLocns0, AssignLocns),
    ErrMsgAssigns = make_locn_descs(AssignLocns),
    ErrMsgParts = [ErrMsgHead | ErrMsgAssigns],
    list.condense(ErrMsgParts, ErrMsg),    
    error_at_locn(ErrMsg, VarSrcLocn, !Errs).

:- func get_src_locn(assign_info) = src_locn.

get_src_locn(I) = I ^ assign_info_locn.

:- func make_locn_descs(list(src_locn)) = list(error_msg).

make_locn_descs(Locns) = MsgParts :-
    (
        Locns = [],
        unexpected($pred, "empty list of locations")
    ;
        Locns = [Locn],
        MsgParts = [[fixed("  "), src_locn(Locn)]]
    ;
        Locns = [Locn | LocnsPrime @ [_ | _]],
        MsgParts0 = make_locn_descs(LocnsPrime),
        MsgPart = [fixed("  "), src_locn(Locn), nl],
        MsgParts = [MsgPart | MsgParts0]
    ).

%-----------------------------------------------------------------------------%

:- pred restore_residual_assignment(zinc_name::in, list(assign_info)::in,
    items::in, items::out) is det.

restore_residual_assignment(Name, Infos, !Items) :-
    (
        Infos = [],
        unexpected($pred, "missing assignment values")
    ;
        Infos = [Info | _OtherInfos],
        % NOTE: we deliberately ignore OtherInfos here even if it is
        % non-empty.  The important error to report at this point is that
        % the name on the lhs of the assignment is undeclared.
        % By throwing away any assignments in OtherInfos we ensure that
        % this happens.
        %
        Info = assign_info(Value, SrcLocn),
        RawItem = assign_item(Name, Value),
        Item = item(RawItem, SrcLocn),
        !:Items = [Item | !.Items]
    ).

%-----------------------------------------------------------------------------%
:- end_module elim_assigns.
%-----------------------------------------------------------------------------%
