%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2006-2009 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Nicholas Nethercote <njn@csse.unimelb.edu.au>
%
% This module topologically sorts the items in the AST so that all names are
% declared before use, where possible.  It also ensures that variables are
% defined before use, where possible.  It reports any cycles that it finds.
% The algorithm is given in top_sort_ast below.
%
%-----------------------------------------------------------------------------%

:- module top_sort.
:- interface.

%-----------------------------------------------------------------------------%

:- import_module compiler_common.
:- import_module zinc_ast.
:- import_module zinc_common.

:- import_module pair.

%-----------------------------------------------------------------------------%

:- type top_sort_graph.

    % Topologically sort the AST.
    % We output the top-sort-graph purely so it can be printed,
    % for debugging purposes.
    %
:- pred top_sort_ast : stage(ast, pair(ast, top_sort_graph)) `with_inst` stage.

    % "FlatZinc sort" the AST.  That is, ensure all pred declarations
    % precede all variable declarations, which precede all constraints, which
    % precede the solve item.  Aborts if any other kind of item is present in
    % the AST.  Important:  the sort is *stable*.
    %
:- func flatzinc_sort_ast(ast) = ast.

:- pred pprint_top_sort_graph : writer2(top_sort_graph) `with_inst` writer2.
:- pred dump_top_sort_graph : writer( top_sort_graph) `with_inst` writer.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module zinc_error.

:- import_module assoc_list.
:- import_module digraph.
:- import_module exception.
:- import_module io.
:- import_module list.
:- import_module maybe.
:- import_module multi_map.
:- import_module require.
:- import_module set.
:- import_module set_tree234.
:- import_module string.

%-----------------------------------------------------------------------------%

    % This is the (abstractly) exported one.
:- type top_sort_graph == assoc_list(item).

    % This is the real graph we use internally.
:- type graph == digraph(item).

:- type def_mmap == multi_map(zinc_name, item).

%-----------------------------------------------------------------------------%

top_sort_ast(Lang, Items, ATSortedItems - !:GraphAssocList, !:Errs, Warns) :-
    else_unexpected(is_lang(Lang, [lang_minizinc]),
        $pred ++ ": unexpected language " ++ Lang ^ string),
    % data:
    % - DefMMap = multi_map(zinc_name, item)
    % - Graph = graph(item)
    %
    some [!Graph] (
        % for each item I
        %     add I to Graph
        %     for each name Name def'd by I
        %         record in DefMMap the fact that I defined Name
        list.foldl2(do_defs, Items, multi_map.init, DefMMap, digraph.init,
            !:Graph),

        % for each item I
        %     for each name Name used by I
        %         for each item IDef that defines Name
        %             add IDef->I edge to Graph
        %
        % (Nb: we ignore any uses of undef'd names -- they will be caught and
        % complained about by a subsequent phase.)
        list.foldl(do_uses(DefMMap), Items, !Graph),

        % Because assignments are considered to both def and use their LHS
        % variable (see defs_in_raw_item), they get marked as cycles above.  We
        % now remove these cycles from the graph, because they're not genuine
        % cycles (except when they are... eg. "x = x" or "x = f(x)").
        digraph.to_assoc_list(!.Graph, !:GraphAssocList),
        IsNotAssignmentWithFakeCycle = (pred((DefItem - UseItem)::in)
                is semidet :-
            ( if
                DefItem = UseItem,
                DefItem = item(assign_item(Name, E), _),
                not set.member(Name, uses_in_expr(E))
            then
                false   % Assignment with fake cycle
            else
                true
            )
        ),
        list.filter(IsNotAssignmentWithFakeCycle, !GraphAssocList),

        % Check if any item has a Def-Use chain to itself (eg. "int: x = x").
        CheckIfItemIsCyclic = (pred((DefItem - UseItem)::in,
                !.CycleErrs::in, !:CycleErrs::out) is det :-
            ( if DefItem = UseItem
            then cyclic_defn_error(DefItem, !CycleErrs)
            else true
            )
        ),
        list.foldl(CheckIfItemIsCyclic, !.GraphAssocList, [], !:Errs),

        % Do an approximate topological sort of the graph (ie. a topological
        % sort with cycles collected into sets), recording any cycles between
        % multiple items.  (We already did intra-item cycles above).
        digraph.atsort(!.Graph, ATSortedGraph),
        flatten_atsorted_graph(ATSortedGraph, ATSortedItems, !Errs)
    ),
    Warns = [].         % This stage doesn't produce any warnings.

%-----------------------------------------------------------------------------%

:- pred do_defs(item::in, def_mmap::in, def_mmap::out, graph::in, graph::out)
        is det.

do_defs(Item @ item(RawItem, _Locn), !DefMMap, !Graph) :-
    digraph.add_vertex(Item, _Key, !Graph),
    DefdNames = defs_in_raw_item(RawItem),
    AddDefdNameAndItem = (pred(Name::in, !.DefMMap::in, !:DefMMap::out)
            is det :-
        multi_map.add(Name, Item, !DefMMap)
    ),
    set.fold(AddDefdNameAndItem, DefdNames, !DefMMap).

%-----------------------------------------------------------------------------%

:- pred do_uses(def_mmap::in, item::in, graph::in, graph::out) is det.

do_uses(DefMMap, Item @ item(RawItem, _Locn), !Graph) :-
    UseNames = uses_in_raw_item(RawItem),
    set.fold(add_def_use_edges(DefMMap, Item), UseNames, !Graph).

:- pred add_def_use_edges(def_mmap::in, item::in, zinc_name::in,
    graph::in, graph::out) is det.

add_def_use_edges(DefMMap, UseItem, UseName, !Graph) :-
    AddDefUseEdge = (
        pred(DefItem::in, !.Graph::in, !:Graph::out) is det :-
            digraph.add_vertices_and_edge(DefItem, UseItem, !Graph)
    ),
    ( if multi_map.search(DefMMap, UseName, DefItems) then
        foldl(AddDefUseEdge, DefItems, !Graph)
    else
        % Undef'd name used!  Ignore, a later phase will complain about it.
        true
    ).

%-----------------------------------------------------------------------------%

:- pred flatten_atsorted_graph(list(set(item))::in, items::out,
    zinc_errors::in, zinc_errors::out) is det.

flatten_atsorted_graph([], [], !Errs).
flatten_atsorted_graph([S | Ss], FlatS ++ FlatSs, !Errs) :-
    ( if is_singleton(S, Elem) then
        FlatS = [Elem]
    else
        FlatS = set.to_sorted_list(S),
        foldl(cyclic_defn_error, FlatS, !Errs)
    ),
    flatten_atsorted_graph(Ss, FlatSs, !Errs).

:- pred cyclic_defn_error(item::in,
    zinc_errors::in, zinc_errors::out) is det.

cyclic_defn_error(item(RawItem, Locn), !Errs) :-
    Defs = defs_in_raw_item(RawItem),
     ( if is_singleton(Defs, Def)
    then CyclicName = Def
    else unexpected($file, $pred, "something went wrong")
    ),
    ErrMsg = [words("cycle error: cycle in definition of"), quote(CyclicName)],
    error_at_locn(ErrMsg, Locn, !Errs).

%-----------------------------------------------------------------------------%
% Defs
%-----------------------------------------------------------------------------%

    % First list is the global def'd names (types, funcs/preds), second is the
    % top-level def'd names (variables)
:- func defs_in_raw_item(raw_item) = set(zinc_name).

defs_in_raw_item(RawItem) = Defs :-
    ( RawItem = output_item(_)
    ; RawItem = constraint_item(_)
    ; RawItem = solve_item(_,_)
    ),
    Defs = set.init.

defs_in_raw_item(RawItem) = Defs :-
    % Assignments are considered both defs and vars of their LHS variable.
    % This ensures they come after the var declaration, but before any var
    % uses.
    ( RawItem = assign_item(Name,_)
    ; RawItem = predfunc_item(_,Name,_,_,_,_)
    ; RawItem = var_decl_item(_,Name,_,_)
    ; RawItem = annotation_item(Name,_)
    ),
    Defs = make_singleton_set(Name).

%-----------------------------------------------------------------------------%
% Uses
%-----------------------------------------------------------------------------%

:- func uses_in_raw_item(raw_item) = set(zinc_name).

uses_in_raw_item(annotation_item(_, Params)) = Uses :-
    ParamsTIs = assoc_list.keys(Params),
    Uses = uses_in_Xs(uses_in_ti_expr, ParamsTIs).

uses_in_raw_item(output_item(E))        = uses_in_expr(E).
uses_in_raw_item(constraint_item(E))    = uses_in_expr(E).

uses_in_raw_item(solve_item(SolveKind, AnnEs)) = Uses :-
    (
        SolveKind = satisfy,
        UsesInSolveKind = set.init
    ;
        SolveKind = minimize(E),
        UsesInSolveKind = uses_in_expr(E)
    ;   
        SolveKind = maximize(E),
        UsesInSolveKind = uses_in_expr(E)
    ),
    Uses = UsesInSolveKind `union` uses_in_Xs(uses_in_expr, AnnEs).

    % See comment in defs_in_raw_item about assignments.
uses_in_raw_item(assign_item(Name, E)) =
    make_singleton_set(Name) `union` uses_in_expr(E).

uses_in_raw_item(var_decl_item(TIE, _Name, AnnEs, MaybeE)) = Uses :-
    (
        MaybeE = no_assignment,
        set.init(UsesInAssign)
    ;
        ( MaybeE = rhs_assignment(AssignE)
        ; MaybeE = separate_assignment(_, AssignE)
        ),
        UsesInAssign = uses_in_expr(AssignE)
    ),
    Uses = uses_in_ti_expr(TIE) `union`
        uses_in_Xs(uses_in_expr, AnnEs) `union` UsesInAssign.

uses_in_raw_item(RawItem) = Uses :-
    RawItem = predfunc_item(PredFuncRet, _Name, _ProcN, Params, AnnEs,
        MaybeBodyE),
    % Nb: any parameters used in the body should be removed from the body's
    % uses list.
    (
        PredFuncRet = func_ret(RetTIE),
        RetUses = uses_in_ti_expr(RetTIE)
    ;
        ( PredFuncRet = test_ret
        ; PredFuncRet = pred_ret
        ),
        RetUses = set.init
    ),
    assoc_list.keys_and_values(Params, ParamTIs, ParamIds),
    Uses = RetUses `union` 
        uses_in_Xs(uses_in_ti_expr, ParamTIs) `union` 
        uses_in_Xs(uses_in_expr, AnnEs) `union` 
        ( uses_in_maybe_X(uses_in_expr, MaybeBodyE) `difference` 
            uses_in_Xs(uses_in_id, ParamIds)).

%-----------------------------------------------------------------------------%

:- func uses_in_expr(expr) = set(zinc_name).

uses_in_expr(expr(RawE, AnnEs, _EInfo)) =
    uses_in_raw_expr(RawE) `union` uses_in_Xs(uses_in_expr, AnnEs).

:- func uses_in_raw_expr(raw_expr) = set(zinc_name).

uses_in_raw_expr(RawE) = Uses :-
    (
        RawE = ident(Id),
        Uses = uses_in_id(Id)
    ;
        RawE = anon_var,
        Uses = set.init
    ;
        RawE = lit(_Lit),
        Uses = set.init
    ;
        ( RawE = lit_set(Es)
        ; RawE = lit_simple_array(Es)
        ; RawE = lit_tuple(Es)
        ),
        Uses = uses_in_Xs(uses_in_expr, Es)
    ;
        RawE = comprehension(Kind, Generators, MaybeWhereE),
        VarsAndUsesInGenerator = (
            pred(generator(VarIds, GenE)::in, AllVars::in, NAllVars::out,
                    AllUses::in, NAllUses::out) is det:-
            % Careful:  add all uses from this E, except for those of generator
            % vars (not including this one!) we've seen so far.
            NAllVars = AllVars `union` uses_in_Xs(uses_in_id, VarIds),
            NAllUses = AllUses `union` 
                (uses_in_expr(GenE) `difference` AllVars)
        ),
        list.foldl2(VarsAndUsesInGenerator, Generators, set.init, GenVars,
            set.init, GenUses),
        % Be careful to remove the generator variables from the uses of the
        % head expression(s) and the where expression.
        WhereUses = uses_in_maybe_X(uses_in_expr, MaybeWhereE) `difference`
            GenVars,
        ( Kind = set_comp(E)
        ; Kind = simple_array_comp(E)
        ),
        HeadUses = uses_in_expr(E) `difference` GenVars,
        Uses = HeadUses `union` GenUses `union` WhereUses
    ;
        RawE = array_access(ArrayE, IndexEs),
        Uses = uses_in_expr(ArrayE) `union` uses_in_Xs(uses_in_expr, IndexEs)
    ;
        RawE = if_then_else(IfE, ThenE, ElseE),
        Uses = uses_in_Xs(uses_in_expr, [IfE, ThenE, ElseE])
    ;
        RawE = app(Id, _ProcN, _AppKind, ArgEs),
        Uses = make_singleton_set(Id ^ id_name) `union` 
            uses_in_Xs(uses_in_expr, ArgEs)
    ;
        % Nb: must exclude local vars from Uses
        RawE = let(LocalVarDefns, E),
        VarsAndUsesInLetLocalVars = (
            pred(local_var(TIE, Id, AnnEs, MaybeInitE)::in, AllVars::in,
                    NAllVars::out, AllUses::in, NAllUses::out) is det:-
            % Careful:  add all uses from this local var definition, except
            % for those of local vars (not including this one!) we've seen so
            % far.
            NAllVars = AllVars `union` uses_in_id(Id),
            UsesInLocalVar = uses_in_ti_expr(TIE) `union`
                uses_in_Xs(uses_in_expr, AnnEs) `union`
                uses_in_maybe_X(uses_in_expr, MaybeInitE),
            NAllUses = AllUses `union` (UsesInLocalVar `difference` AllVars)
        ),
        list.foldl2(VarsAndUsesInLetLocalVars, LocalVarDefns,
            set.init, LocalVars, set.init, LocalUses),
        % Be careful to remove the let-local variables from the uses of the
        % let-defined expression.
        Uses = LocalUses `union` (uses_in_expr(E) `difference` LocalVars)
    ;
        % This doesn't appear after parsing, but it can be present when
        % top-sorting after MiniZinc flattening.
        RawE = coerce(_T1, _T2, E),
        Uses = uses_in_expr(E)
    ;
        % This doesn't appear after parsing, but it can be present when
        % top-sorting after MiniZinc flattening.
        RawE = lit_ann(_Id, Es),
        Uses = uses_in_Xs(uses_in_expr, Es)
    ).

%-----------------------------------------------------------------------------

:- func uses_in_ti_expr(ti_expr) = set(zinc_name).

uses_in_ti_expr(ti_expr(RawTIE, _TIEInfo)) =
    uses_in_raw_ti_expr(RawTIE).

:- func uses_in_raw_ti_expr(raw_ti_expr) = set(zinc_name).

uses_in_raw_ti_expr(raw_ti_expr(_VarPar, BaseTIETail)) = Uses :-
    (
        % These should only appear after type-inst checking.
        ( BaseTIETail = bte_bottom
        ; BaseTIETail = bte_error
        ),
        unexpected($pred, BaseTIETail ^ string)
    ;
        ( BaseTIETail = bte_bool
        ; BaseTIETail = bte_int
        ; BaseTIETail = bte_float
        ; BaseTIETail = bte_string
        ; BaseTIETail = bte_ann
        ; BaseTIETail = bte_typeinst_var(_)
        ; BaseTIETail = bte_any_typeinst_var(_)
        ),
        Uses = set.init
    ;
        BaseTIETail = bte_ident(Id),
        Uses = uses_in_id(Id)
    ;
        BaseTIETail = bte_set_of(TIE),
        Uses = uses_in_ti_expr(TIE)
    ;
        BaseTIETail = bte_array_of(TIEs, TIE,_),
        Uses = uses_in_Xs(uses_in_ti_expr, TIEs) `set.union`
            uses_in_ti_expr(TIE)
    ;
        BaseTIETail = bte_tuple_of(TIEs),
        Uses = uses_in_Xs(uses_in_ti_expr, TIEs)
    ;
        BaseTIETail = bte_set_expr_as_type_expr(Es),
        Uses = uses_in_Xs(uses_in_expr, Es)
    ;
        BaseTIETail = bte_range_expr_as_type_expr(E1, E2),
        Uses = uses_in_expr(E1) `union` uses_in_expr(E2)
    ).

%-----------------------------------------------------------------------------%

:- func uses_in_id(id) = set(zinc_name).

uses_in_id(Id) = make_singleton_set(Id ^ id_name).

:- func uses_in_Xs(func(X) = set(zinc_name), list(X)) = set(zinc_name).

uses_in_Xs(UsesInXFunc, Xs) = UsesInXs :-
    list.foldl(uses_in_x_acc(UsesInXFunc), Xs, set.init, UsesInXs).

:- pred uses_in_x_acc((func(X) = set(zinc_name))::in,
    X::in, set(zinc_name)::in, set(zinc_name)::out) is det.

uses_in_x_acc(Func, X, !Uses) :-
    UsesInX = Func(X),
    set.union(!.Uses, UsesInX, !:Uses).

:- func uses_in_maybe_X(func(X) = set(zinc_name), maybe(X)) = set(zinc_name).

uses_in_maybe_X(_, no) = set.init.
uses_in_maybe_X(UsesInX, yes(E)) = UsesInX(E).

%-----------------------------------------------------------------------------%
% Printing
%-----------------------------------------------------------------------------%

pprint_top_sort_graph(TopSortGraph, IgnoredFiles, !IO) :-
    io.write_string("-- topological sort graph --\n  ", !IO),
    WritePair = (pred((Item1 - Item2)::in, !.IO::di, !:IO::uo) is det :-
        io.write_string(Item1 ^ item_src_locn^show, !IO),
        io.write_string(" < ", !IO),
        io.write_string(Item2 ^ item_src_locn^show, !IO)
    ),
    ItemsNotInIgnoredFiles = (pred((Item1 - Item2)::in) is semidet :-
        Item1 = item(_, SrcLocn1),
        Item2 = item(_, SrcLocn2),
        not ( list.member(SrcLocn1 ^ filename, IgnoredFiles)
            ; list.member(SrcLocn2 ^ filename, IgnoredFiles)
            )
    ),
    TopSortGraph2 = list.filter(ItemsNotInIgnoredFiles, TopSortGraph),
    io.write_list(TopSortGraph2, "\n  ", WritePair, !IO),
    io.nl(!IO).

dump_top_sort_graph(TopSortGraph, !IO) :-
    % Don't ignore any files.
    pprint_top_sort_graph(TopSortGraph, [], !IO).

%-----------------------------------------------------------------------------%

flatzinc_sort_ast(AST) = SortedAST :-
    list.foldl5(categorise_item, AST, [], Preds,
        [], Vars0, [], Constraints, [], Solves, [], Outputs),
    Vars = sort_var_decls(Vars0, set_tree234.init, []),
    SortedAST = list.foldl(rev_append,
        [Outputs, Solves, Constraints, Vars, Preds], []).

%-----------------------------------------------------------------------------%

:- func rev_append(list(T), list(T)) = list(T).

rev_append([], Ys) = Ys.
rev_append([X | Xs], Ys) = rev_append(Xs, [X | Ys]).

%-----------------------------------------------------------------------------%

:- pred categorise_item(item::in,
        items::in, items::out,
        items::in, items::out,
        items::in, items::out,
        items::in, items::out,
        items::in, items::out) is det.

categorise_item(Item, !Preds, !Vars, !Constraints, !Solves, !Outputs) :-
    Item = item(RawItem, _),
    (
        RawItem = predfunc_item(_, _, _, _, _, _),
        list.cons(Item, !Preds)
    ;
        RawItem = var_decl_item(_, _, _, _),
        list.cons(Item, !Vars)
    ;
        RawItem = constraint_item(_),
        list.cons(Item, !Constraints)
    ;
        RawItem = solve_item(_, _),
        list.cons(Item, !Solves)
    ;
        RawItem = output_item(_),
        list.cons(Item, !Outputs)
    ;
        ( RawItem = annotation_item(_, _)
        ; RawItem = assign_item(_, _)
        ),
        unexpected($pred, "unexpected item kind")
    ).

%-----------------------------------------------------------------------------%

    % This is quadratic in theory, but you'd have to work pretty hard to
    % generate a pathological case in practice.
    %
    % N.b.: we use set_tree234(zinc_name) rather than plain set(zinc_name)
    % because the former has O(log n) rather than O(n) access time.  This is a
    % significant improvement for some models.
    %
:- func sort_var_decls(items, set_tree234(zinc_name), items) = items.

sort_var_decls(UnsortedVars0, Names0, SortedVars0) = Vars :-
    list.foldl3(sort_var_decl, UnsortedVars0, Names0, Names,
        [], UnsortedVars, SortedVars0, SortedVars),
    (
        UnsortedVars = [],
        Vars = SortedVars
    ;
        UnsortedVars = [_ | _],
        Vars = sort_var_decls(UnsortedVars, Names, SortedVars)
    ).

%-----------------------------------------------------------------------------%

:- pred sort_var_decl(item::in,
    set_tree234(zinc_name)::in, set_tree234(zinc_name)::out,
    items::in, items::out,
    items::in, items::out) is det.

sort_var_decl(Item, !Names, !UnsortedVars, !SortedVars) :-
    Item = item(RawItem, _),
    ( if RawItem = var_decl_item(_, Name, _, MaybeExpr) then
        (
            MaybeExpr = no_assignment,
            !:Names = set_tree234.insert(Name, !.Names),
            list.cons(Item, !SortedVars)
        ;
            ( MaybeExpr = rhs_assignment(Expr)
            ; MaybeExpr = separate_assignment(_, Expr)
            ),
                ( if flatzinc_expr_names_in_set(Expr, !.Names) then
                    !:Names = set_tree234.insert(Name, !.Names),
                    list.cons(Item, !SortedVars)
                else
                    list.cons(Item, !UnsortedVars)
                )
            )
    else
        unexpected($pred, "unexpected item")
    ).

%-----------------------------------------------------------------------------%

:- pred flatzinc_expr_names_in_set(expr::in, set_tree234(zinc_name)::in)
    is semidet.

flatzinc_expr_names_in_set(Expr, Names) :-
    RawExpr = Expr ^ raw_expr,
    ( if RawExpr = ident(Id) then
        set_tree234.contains(Names, Id ^ id_name)
    else if RawExpr = lit_simple_array(SubExprs) then
        all [SubExpr] (
            list.member(SubExpr, SubExprs)
        =>
            flatzinc_expr_names_in_set(SubExpr, Names)
        )
    else if RawExpr = array_access(SubExpr, _) then
        flatzinc_expr_names_in_set(SubExpr, Names)
    else
        % Anything else either can't contain id(_) subexpressions or
        % shouldn't appear at all in FlatZinc var decls.
        true
    ).

%---------------------------------------------------------------------------%
:- end_module top_sort.
%---------------------------------------------------------------------------%
