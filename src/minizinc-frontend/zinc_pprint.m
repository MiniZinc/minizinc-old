%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2006-2007 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Nicholas Nethercote <njn@csse.unimelb.edu.au>
%
% A Zinc AST pretty-printer.  Also contains a predicate that just dumps the
% full AST without any formatting.
%
%-----------------------------------------------------------------------------%

:- module zinc_pprint.
:- interface.

%-----------------------------------------------------------------------------%

:- import_module types_and_insts.
:- import_module zinc_ast.
:- import_module zinc_common.
:- import_module zinc_error.

:- import_module bool.
:- import_module io.
:- import_module pprint.

%-----------------------------------------------------------------------------%

    % The frontend introduces terms making type coercions explicit.
    % These coercions are not part of the language and should be
    % printed out only for debugging.  We attach this information
    % to the language flag for convenience.
    %
:- type pp_lang
    --->    pp_lang_zinc(print_coercions)
    ;       pp_lang_minizinc(print_coercions)
    ;       pp_lang_flatzinc(print_coercions).

:- type print_coercions
    --->    print_coercions
    ;       dont_print_coercions.

:- pred pprint_ast(pp_lang::in)
    : writer2(ast) `with_inst` writer2.
:- pred pprint_ast_sorted_by_locn(pp_lang::in)
    : writer2(ast) `with_inst` writer2.
:- pred pprint_ast_with_locns(pp_lang::in)
    : writer2(ast) `with_inst` writer2.

:- pred dump_ast : writer(ast) `with_inst` writer.

:- pred pprint_sast(pp_lang::in)
    : writer2(sast) `with_inst` writer2.
:- pred pprint_sast_sorted_by_locn(pp_lang::in)
    : writer2(sast) `with_inst` writer2.

:- pred dump_sast : writer(sast) `with_inst` writer.

:- pred pprint_item(pp_lang::in, item::in, io::di, io::uo) is det.
:- pred dump_item(item::in, io::di, io::uo) is det.

    % Pretty-prints all errors.  For each error, it prefaces each line with the
    % location, and indents the 2nd and subsequent lines.
:- pred pprint_zinc_errors(pp_lang::in, string::in, zinc_errors::in,
    io::di, io::uo) is det.

    % For use by fzn2xml and zinc.
    %
:- func doc_raw_item(pp_lang, raw_item) = doc.
:- func doc_raw_expr(pp_lang, bool, raw_expr) = doc.

    % For use by the Zinc runtime driver.
    %
:- func doc_type_inst(pp_lang, type_inst) = doc.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module builtins.

:- import_module assoc_list.
:- import_module char.
:- import_module list.
:- import_module maybe.
:- import_module pair.
:- import_module std_util.
:- import_module require.
:- import_module string.

:- type docs == list(doc).

%-----------------------------------------------------------------------------%
%
% Pretty-printer
%

pprint_ast_sorted_by_locn(Lang, Items, IgnoredFiles, !IO) :-
    % Filter before sorting, to minimise the work done by the sort.
    % Then pass an empty IgnoredFiles list to pprint_ast to avoid duplicating
    % the filtering.
    filter_ignored_items(IgnoredFiles, Items, Items2),
    pprint_ast(Lang, sort_ast_by_locn(Items2), [], !IO).

pprint_sast_sorted_by_locn(Lang, SAST, IgnoredFiles, !IO) :-
    SAST = sast(Items, SolveItem0, MaybeOutputItem),
    SolveItem0 = sast_solve_item(SolveKind, SolveAnns, SolveSrcLocn),
    SolveItem = item(solve_item(SolveKind, SolveAnns), SolveSrcLocn),
    (
        MaybeOutputItem = yes(OutputItem),
        AST = [OutputItem, SolveItem | Items]
    ;
        MaybeOutputItem = no,
        AST = [SolveItem | Items]
    ),
    pprint_ast_sorted_by_locn(Lang, AST, IgnoredFiles, !IO).

pprint_ast(Lang, Items, IgnoredFiles, !IO) :-
    filter_ignored_items(IgnoredFiles, Items, Items2),
    io.write_list(Items2, "\n\n", pprint_item(Lang), !IO),
    io.nl(!IO).

pprint_sast(Lang, SAST, IgnoredFiles, !IO) :-
    SAST = sast(Items, SolveItem0, MaybeOutputItem),
    filter_ignored_items(IgnoredFiles, Items, FilteredItems),
    io.write_list(FilteredItems, "\n\n", pprint_item(Lang), !IO),
    SolveItem0 = sast_solve_item(SolveKind, SolveAnns, SolveSrcLocn),
    SolveItem = item(solve_item(SolveKind, SolveAnns), SolveSrcLocn),
    (
        MaybeOutputItem = yes(OutputItem),
        OtherItems0 = [SolveItem, OutputItem]
    ;
        MaybeOutputItem = no,
        OtherItems0 = [SolveItem]
    ),
    filter_ignored_items(IgnoredFiles, OtherItems0, OtherItems),
    io.write_list(OtherItems, "\n\n", pprint_item(Lang), !IO),
    io.nl(!IO).

pprint_ast_with_locns(Lang, Items, IgnoredFiles, !IO) :-
    filter_ignored_items(IgnoredFiles, Items, Items2),
    io.write_list(Items2, "\n\n", pprint_item_with_locn(Lang), !IO),
    io.nl(!IO).

:- pred pprint_item_with_locn(pp_lang::in, item::in,
    io::di, io::uo) is det.

pprint_item_with_locn(Lang, Item, !IO) :-
    pprint_item(Lang, Item, !IO),
    io.write_string("    % " ++ Item^item_src_locn^show, !IO).

pprint_item(Lang, Item, !IO) :-
    pprint.write(76, item_to_doc(Lang, Item), !IO).

    % We use this predicate rather that list.filter/2 since this is
    % guranteed to only use a constant amount of stack.
    %
:- pred filter_ignored_items(list(string)::in,
    list(item)::in, list(item)::out) is det.

filter_ignored_items([], !Items).
filter_ignored_items(IgnoredFiles @ [_ | _], !Items) :-
    filter_ignored_items_2(IgnoredFiles, !.Items, [], !:Items),
    list.reverse(!Items).

:- pred filter_ignored_items_2(list(string)::in,
    list(item)::in, list(item)::in, list(item)::out) is det.

filter_ignored_items_2(_, [], !ItemAcc).
filter_ignored_items_2(IgnoredFiles, [ Item | Items], !ItemAcc) :-
    ( if    item_from_ignored_file(IgnoredFiles, Item)
      then  true
      else  !:ItemAcc = [Item | !.ItemAcc]
    ),
    filter_ignored_items_2(IgnoredFiles, Items, !ItemAcc).

:- pred item_from_ignored_file(list(string)::in, item::in) is semidet.

item_from_ignored_file(IgnoredFiles, Item) :-
    Item = item(_RawItem, src_locn(FileName, _LineNum)),
    list.member(FileName, IgnoredFiles).

%-----------------------------------------------------------------------------%
%
% Dumper
%

% In all code below the comments show the layout in the cases with the most
% possible linebreaks.
dump_ast(Items, !IO) :-
    io.write_list(Items, "\n\n", dump_item, !IO),
    io.nl(!IO).

dump_sast(AST, !IO) :-
    AST = sast(Items, SolveItem0, MaybeOutputItem),
    io.write_list(Items, "\n\n", dump_item, !IO),
    SolveItem0 = sast_solve_item(SolveKind, SolveAnns, SolveSrcLocn),
    SolveItem = item(solve_item(SolveKind, SolveAnns), SolveSrcLocn),
    dump_item(SolveItem, !IO),
    (
        MaybeOutputItem = yes(OutputItem),
        dump_item(OutputItem, !IO)
    ;
        MaybeOutputItem = no
    ).

%-----------------------------------------------------------------------------%
% Other things
%-----------------------------------------------------------------------------%

dump_item(Item, !IO) :-
    pprint.write(76, pprint.to_doc(Item), !IO).

%-----------------------------------------------------------------------------%

pprint_zinc_errors(Lang, ProgramName, Errs, !IO) :-
    SortedErrs = list.sort(zinc_error.error_compare, Errs),
    list.foldl(pprint_zinc_error(Lang, ProgramName), SortedErrs, !IO).

:- pred pprint_zinc_error(pp_lang::in, string::in)
    : writer(zinc_error) `with_inst` writer.

pprint_zinc_error(Lang, ProgramName, zinc_error(ErrLocn, ErrMsg), !IO) :-
    (
        ErrLocn = file_line_column(FileName, Line, Column),
        LocnStr = FileName ++ ":" ++ Line^string ++ ":" ++ Column^string
    ;
        ErrLocn = file_line(FileName, Line),
        LocnStr = FileName ++ ":" ++ Line^string
    ;
        ErrLocn = non_specific,
        LocnStr = ProgramName
    ;
        ErrLocn = builtin,
        LocnStr = "(builtin)"
    ),
    Docs = error_msg_to_docs(Lang, ErrMsg),
    PrefixStr = LocnStr ++ ":\n  ",
    io.write_string(io.stderr_stream, PrefixStr, !IO),
    ErrDoc = nest(2, my_packed(yes, Docs)),
    % Using 80 here seems to give a maximum line length of 79, not sure
    % why... --njn
    pprint.write(io.stderr_stream, 80, ErrDoc, !IO),
    io.nl(io.stderr_stream, !IO).

    % The result consists of as many small docs as possible, rather than
    % aggregations of them.  This subsequently allows us full aggregation
    % flexibility.
:- func error_msg_to_docs(pp_lang, error_msg) = list(doc).

error_msg_to_docs(_,[]) = [].
error_msg_to_docs(Lang, [Part | Parts]) =
    error_msg_part_to_docs(Lang, Part) ++ error_msg_to_docs(Lang, Parts).

:- func error_msg_part_to_docs(pp_lang, error_msg_part) = list(doc).

error_msg_part_to_docs(Lang, Part) = Docs :-
    (
        Part = fixed(Str),
        Docs = [doc(Str)]
    ;
        Part = words(WordsStr),
        Strs = string.words_separator(char.is_whitespace, WordsStr),
        Docs = map(doc, Strs)
    ;
        Part = type_inst(TI),
        Docs = ["`" ++ doc_type_inst(Lang, TI) ++ "'"]
    ;
        Part = type_inst_sig_args(TIs),
        DocX = ( func(Doc) = nest(2, doc_type_inst(Lang, Doc)) ),
        Docs = ["`" ++
                parentheses( doc_Xs(DocX, TIs) ) ++
                "'"]
    ;
        Part = suffix(Part2, SuffixStr),
        Docs2 = error_msg_part_to_docs(Lang, Part2),
        list.det_split_last(Docs2, FrontDocs2, LastDoc2),
        Docs = FrontDocs2 ++ [LastDoc2 ++ SuffixStr]
    ;
        Part = quote(Str),
        Docs = ["`" ++ doc(Str) ++ "'"]
    ;
        Part = nl,
        Docs = [line]
    ;
        Part = src_locn(SrcLocn),
        (
            SrcLocn = src_locn(FileName, LineNum),
            string.format("%s:%d", [s(FileName), i(LineNum)], ContextStr),
            Docs = [doc(ContextStr)]
        ;
            SrcLocn = builtin,
            Docs = [doc("(builtin)")]
        ;
            SrcLocn = unknown,
            Docs = [doc("(unknown)")]
        )
    ;
        Part = empty,
        Docs = []
    ).

    % This is like pprint.packed(space), but with the exception that any 'line'
    % docs are not grouped, which ensures that they are always printed as line
    % breaks.
:- func my_packed(bool, list(doc)) = doc.

my_packed(_,[]) = nil.
my_packed(AddLine, [Doc]) =
    ( if Doc = line then line else group(maybe_line(AddLine) ++ Doc) ).
my_packed(AddLine, [Doc1, Doc2 | Docs]) =
    ( if Doc1 = line then
        line ++ my_packed(no, [Doc2 | Docs])
      else
        group(maybe_line(AddLine) ++ Doc1 ++ space) ++
            my_packed(yes, [Doc2 | Docs])
    ).

:- func maybe_line(bool) = doc.

maybe_line(yes) = line.
maybe_line(no)  = nil.

%-----------------------------------------------------------------------------%
% Items
%-----------------------------------------------------------------------------%

:- func item_to_doc(pp_lang, item)   = doc.

item_to_doc(Lang, item(RawItem, _SrcLocn)) =
    doc_raw_item(Lang, RawItem) ++ semic.

% In all code below this point the comments show the layout in the cases with
% the most possible linebreaks.

    % <TypedName>
    %   <AnnEs> =
    %     <E>
    %
    % <TypedName> =
    %   <E>
doc_raw_item(Lang, var_decl_item(TIE, Name, AnnEs, MaybeE)) = Doc :-
    (
        AnnEs = [],
        AssignDoc = eq_mline_doc_var_decl_assignment(Lang, MaybeE)
    ;
        AnnEs = [_ | _],
        AssignDoc = mline(
            doc_annotations(Lang, AnnEs) ++
            eq_mline_doc_var_decl_assignment(Lang, MaybeE)
        )
    ),
    Doc = doc_ti_expr_and_name(Lang, TIE - Name) ++ AssignDoc.

    % <Name> =
    %   <E>
doc_raw_item(Lang, assign_item(Name, E)) =
    doc_name(Name) ++ " = " ++
        mline(doc_expr(Lang, no, E)).

    % output
    %   <E>
doc_raw_item(Lang, output_item(E)) =
    "output " ++
        mline(doc_expr(Lang, no, E)).

    % constraint
    %   <E>
doc_raw_item(Lang, constraint_item(E)) =
    "constraint " ++
        mline(doc_expr(Lang, no, E)).

    % solve
    %   <AnnEs>
    %   satisfy
    %
    % solve
    %   <AnnEs>
    %   {min,max}imize
    %     <E>
doc_raw_item(Lang, solve_item(SolveKind, AnnEs)) = Doc :-
    (
        SolveKind = satisfy,
        SubDoc = doc("satisfy")
    ;
        SolveKind = minimize(E),
        SubDoc = doc("minimize ") ++ mline(doc_expr(Lang, no, E))
    ;
        SolveKind = maximize(E),
        SubDoc = doc("maximize ") ++ mline(doc_expr(Lang, no, E))
    ),
    (
        AnnEs = [],
        Doc = "solve " ++
                mline(SubDoc)
    ;
        AnnEs = [_ | _],
        Doc = "solve " ++
                mline(doc_annotations(Lang, AnnEs) ++ doc(" ") ++
                nline(SubDoc))
    ).

    % test
    %   <Name>(
    %     <Params>)<Anns> =
    %   <Body>
    %
doc_raw_item(Lang, predfunc_item(test_ret, Name, _ProcN, Params, Anns, MaybeBody)) =
    "test " ++
        mline(doc_name(Name) ++ doc_maybe_enclosed_Xs_nl(parentheses, nil,
                doc_ti_expr_and_id(Lang), Params) ++
            mline(doc_annotations(Lang, Anns)) ++
            eq_mline_doc_maybe_defn(doc_expr(Lang, no), MaybeBody)
        ).

    % predicate
    %   <Name>(
    %     <Params>)<Anns> =
    %   <Body>
    %
doc_raw_item(Lang, predfunc_item(pred_ret, Name, _ProcN, Params, Anns, MaybeBody))
        = Doc :-
    Doc = "predicate " ++
        mline(doc_name(Name) ++ doc_maybe_enclosed_Xs_nl(parentheses, nil,
                doc_ti_expr_and_id(Lang), Params) ++
            mline(doc_annotations(Lang, Anns)) ++
            eq_mline_doc_maybe_defn(doc_expr(Lang, no), MaybeBody)
        ).

    % function
    %   <RetTIE>:
    %     <Name>(
    %       <Params>)<Anns> =
    %     <Body>
    %
doc_raw_item(Lang,
        predfunc_item(func_ret(RetTIE), Name, _ProcN, Params, Anns, MaybeBody)) = Doc :-
    Doc = "function " ++
        mline(doc_ti_expr(Lang, RetTIE) ++ ": " ++
            mline(doc_name(Name) ++ doc_maybe_enclosed_Xs_nl(parentheses, nil,
                    doc_ti_expr_and_id(Lang), Params)
            ) ++ mline(doc_annotations(Lang, Anns)) ++
            eq_mline_doc_maybe_defn(doc_expr(Lang, no), MaybeBody)
        ).

    % annotation
    %   <Name>(
    %     <Params>)
doc_raw_item(Lang, annotation_item(Name, Params)) =
    "annotation " ++
        mline(doc_name(Name) ++ doc_maybe_enclosed_Xs_nl(parentheses, nil,
                doc_ti_expr_and_id(Lang), Params)
        ).

%-----------------------------------------------------------------------------%

    % =
    %   <X>
:- func eq_mline_doc_maybe_defn(func(X) = doc, maybe(X)) = doc.

eq_mline_doc_maybe_defn(_D_X, no)        = nil.
eq_mline_doc_maybe_defn( D_X, yes(Defn)) = " = " ++ mline(D_X(Defn)).

    % =
    %   <X>
:- func eq_mline_doc_var_decl_assignment(pp_lang, var_decl_assignment) = doc.

eq_mline_doc_var_decl_assignment(Lang, MaybeAssign) = Doc :-
    (
        MaybeAssign = no_assignment,
        Doc = nil
    ;
        ( MaybeAssign = rhs_assignment(Expr)
        ; MaybeAssign = separate_assignment(_, Expr)
        ),
        Doc = " = " ++ mline(doc_expr(Lang, no, Expr))
    ).

%-----------------------------------------------------------------------------%
% Type-inst expressions
%-----------------------------------------------------------------------------%

:- func doc_var_par(pp_lang, var_par) = doc.

    % FlatZinc doesn't allow 'par', so we ignore it if present.
doc_var_par(_, par) = nil.
doc_var_par(_,    var) = doc("var ").

    % <VarPar> <BaseTIETail>
    %
    % ( <TIE>:
    %     <Name>
    %   where
    %     <E>
    % )
    %
:- func doc_ti_expr(pp_lang, ti_expr) = doc.

doc_ti_expr(Lang, ti_expr(RawTIE, _Locn)) =
    doc_raw_ti_expr(Lang, RawTIE).

:- func doc_raw_ti_expr(pp_lang, raw_ti_expr) = doc.

doc_raw_ti_expr(Lang, raw_ti_expr(VarPar, BaseTIETail)) = Doc :-
    Doc = doc_var_par(Lang, VarPar) ++ doc_base_ti_expr_tail(Lang, BaseTIETail).

%-----------------------------------------------------------------------------%

:- func doc_base_ti_expr_tail(pp_lang, base_ti_expr_tail) = doc.

    % This can occur because ti_{par,var}_bottom can be lifted to a ti_expr.
doc_base_ti_expr_tail(_,bte_bottom) = doc("_").
doc_base_ti_expr_tail(_,bte_error)  = doc("<type_inst_error>").

doc_base_ti_expr_tail(_,bte_bool)   = doc("bool"  ).
doc_base_ti_expr_tail(_,bte_int)    = doc("int"   ).
doc_base_ti_expr_tail(_,bte_float)  = doc("float" ).
doc_base_ti_expr_tail(_,bte_string) = doc("string").
doc_base_ti_expr_tail(_,bte_ann)    = doc("ann"   ).

doc_base_ti_expr_tail(_,bte_ident(Id)) = doc_id(Id).

doc_base_ti_expr_tail(_,bte_typeinst_var(TV)) = doc("$") ++ doc(TV).
doc_base_ti_expr_tail(_,bte_any_typeinst_var(TV)) =
    doc("any ") ++ doc("$") ++ doc(TV).

    % set of
    %   <TIE>
doc_base_ti_expr_tail(Lang, bte_set_of(TIE)) =
    "set of " ++
        mline(doc_ti_expr(Lang, TIE)).

    % array[
    %   <TIE1>,
    %   <TIE2>,
    %   <TIE3>] of
    %   <TIE>
doc_base_ti_expr_tail(Lang, bte_array_of(IndexTIEs, TIE, IsListSyntax)) = Doc :-
    % Nb: For multi-dimensional array declarations, we always use the
    % "array[A,B]" sugar if possible instead of "array[tuple(A,B)]".  This is
    % because when converting a multi-dimensional array to Cadmium and back,
    % we always end up with a single tuple index, but that's not valid in
    % MiniZinc.  Using the sugar always produces something that is valid
    % MiniZinc.
    (   IsListSyntax = no,
        TIEs = ( if IndexTIEs =
                    [ti_expr(raw_ti_expr(par, bte_tuple_of(TIEs0)),_)]
                 then TIEs0 else IndexTIEs ),
        ThingDoc = doc("array") ++
            doc_enclosed_Xs_nl(brackets, nil, doc_ti_expr(Lang), TIEs)
    ;
        IsListSyntax = yes,
        ( if
            ( Lang = pp_lang_zinc(_) ; Lang = pp_lang_minizinc(_) ),
            IndexTIEs = [ti_expr(raw_ti_expr(par, bte_int),_)]
          then
            ThingDoc = doc("list")
          else
            unexpected($pred, ": problem with 'list' form of array")
        )
    ),
    Doc = ThingDoc ++ " of " ++
        mline(doc_ti_expr(Lang, TIE)).

    % tuple(
    %   <E1>,
    %   <E2>,
    %   <E3>)
doc_base_ti_expr_tail(Lang, bte_tuple_of(TIEs)) =
    doc("tuple") ++
        doc_enclosed_Xs_nl(parentheses, nil, doc_ti_expr(Lang), TIEs).

    % (Treat just like a literal set.)
doc_base_ti_expr_tail(Lang, bte_set_expr_as_type_expr(Es)) =
    doc_raw_expr(Lang, no, lit_set(Es)).

    %   <E1> ..
    %     <E2>
    %
    % Nb: no parentheses around it -- if it's preceded by 'var' or 'par' that
    % would give "var (1..2)" which is a syntax error.  But we do need to put
    % parentheses around any operators or lets within the expressions.
    %
doc_base_ti_expr_tail(Lang, bte_range_expr_as_type_expr(E1, E2)) =
    doc_expr(Lang, yes, E1) ++ space ++ doc_opname("..") ++ space ++
        mline(doc_expr(Lang, no, E2)).

%-----------------------------------------------------------------------------%
% Type-insts
%-----------------------------------------------------------------------------%

    % For these ones, it's much easier to just lift the TI to a TIE and print
    % that.
    % And it guarantees consistent results.
    %
doc_type_inst(Lang, TI) = Doc :-
    Doc = doc_ti_expr(Lang, lift_type_inst_to_ti_expr(unknown, TI)).

%-----------------------------------------------------------------------------%
% Expressions
%-----------------------------------------------------------------------------%

    % <E>
    %   <AnnEs>
    %
    % doc_expr(Lang, NeedsParensIfOpAppOrLet, Expr)
    %
:- func doc_expr(pp_lang, bool, expr) = doc.

doc_expr(Lang, NeedsParensIfOpAppOrLet, expr(RawE, AnnEs, _EInfo)) = Doc :-
    % If this expression is an op application and it is annotated, it needs
    % parentheses around it.
    HasAnns = ( if AnnEs = [] then no else yes ),
    NeedsParensIfOpAppOrLet2 = NeedsParensIfOpAppOrLet `or` HasAnns,
    Doc = doc_raw_expr(Lang, NeedsParensIfOpAppOrLet2, RawE) ++
            mline(doc_annotations(Lang, AnnEs)).

doc_raw_expr(_,_,ident(Id)) = doc_id(Id).
doc_raw_expr(_,_,anon_var)  = doc("_").

doc_raw_expr(_,_,lit(bool(B))) = doc( if B = yes then "true" else "false" ).
doc_raw_expr(_,_,lit(int(I)))       = doc(I).
doc_raw_expr(_,_,lit(floatstr(S)))  = doc(S).
doc_raw_expr(_,_,lit(string(S)))    = doc(S^string).

    % { <E1>,
    %   <E2>,
    %   <E3> }
doc_raw_expr(Lang,_,lit_set(Es)) =
    doc_enclosed_Xs(braces, space, doc_expr(Lang, no), Es).

    % [ <E1>,
    %   <E2>,
    %   <E3> ]
doc_raw_expr(Lang,_,lit_simple_array(Es)) =
    doc_enclosed_Xs(brackets, space, doc_expr(Lang, no), Es).

    % (<E1>,
    %   <E2>,
    %   <E3>)
doc_raw_expr(Lang,_,lit_tuple(Es)) =
    doc_enclosed_Xs(parentheses, nil, doc_expr(Lang, no), Es).

    % <Name>(
    %   <E1>,
    %   <E2>,
    %   <E3>)
doc_raw_expr(Lang,_,lit_ann(Id, Es)) =
    doc_id(Id) ++
        doc_maybe_enclosed_Xs_nl(parentheses, nil, doc_expr(Lang, no), Es).

    % { <E> |
    %   <Gens>
    %   where
    %     <E> }
doc_raw_expr(Lang,_,comprehension(set_comp(E), Gens, MaybeWhereE)) =
    doc_comprehension(Lang, braces, doc_expr(Lang, no), E, Gens, MaybeWhereE).

    % [ <E> |
    %   <Gens>
    %   where
    %     <E> ]
doc_raw_expr(Lang,_,comprehension(simple_array_comp(E), Gens, MaybeWhereE)) =
    doc_comprehension(Lang, brackets, doc_expr(Lang, no), E, Gens, MaybeWhereE).

    % <ArrayE>[
    %   <IndexE1>,
    %   <IndexE2>,
    %   <IndexE2>]
doc_raw_expr(Lang, _, RawExpr) = Doc :-
    RawExpr = array_access(ArrayE, IndexEs),
    % Nb: For multi-dimensional array accesses, we always use the "A[B,C]"
    % sugar if possible, rather than "A[(B,C)]".  See the comment for
    % 'array_of' for why.
    Es = ( if IndexEs = [expr(lit_tuple(Es0), [], _)] then Es0 else IndexEs ),

    % If the array expression is an operator application then we need
    % to parenthesize it, e.g.
    %
    %   (1 .. 20)[4] is valid, but
    %    1 .. 20[4] is not
    %
    ParenArrayExpr = yes,

    % If the array expression is annotated then we need to parenthesize
    % the *annotated* array expression as a whole, e.g.
    %
    % (a::b)[4] is valid, but
    % a::b[4] is not
    %
    ( if
         ArrayE = expr(_, ArrayEAnns, _),
         ArrayEAnns = [_ | _]
      then
        Parentheses = parentheses
      else
        Parentheses = id
    ),
    Doc = Parentheses(doc_expr(Lang, ParenArrayExpr, ArrayE)) ++
        doc_enclosed_Xs_nl(brackets, nil, doc_expr(Lang, no), Es).

    % if
    %   <IfE>
    % then
    %   <ThenE>
    % else
    %   <ElseE>
    % endif
doc_raw_expr(Lang,_,if_then_else(IfE, ThenE, ElseE)) =
    "if " ++
        mline(doc_expr(Lang, no, IfE) ++ space) ++
    nline("then " ++
        mline(doc_expr(Lang, no, ThenE) ++ space)) ++
    nline("else " ++
        mline(doc_expr(Lang, no, ElseE) ++ space)) ++
    nline(doc("endif")).

    % Function/predicate calls:
    %   <Name>(         OR      <Name>
    %     <E1>,
    %     <E2>,
    %     <E3>)
    %
    % Generator calls (unless coercions have been added, in which case we print
    % it like a normal call because we can't print it as a generator call):
    %   <Name>(
    %     GensAndWhere)
    %     (<E>)
    %
    % Binary operators:
    %   (<E1> <Name>    OR      <E1> <Name>
    %   <E2>)                   <E2>
    %
    % Unary operators:
    %   (<Name> <E>)    OR      <Name> <E>
    %
doc_raw_expr(Lang, NeedsParensIfOpAppOrLet, RawExpr) = Doc :-
    RawExpr = app(Id, ProcN, AppKind, Es),
    Name = Id ^ id_name,
    % XXX: this can be used if we want to print the ProcN in the pretty-printed
    % output...
    ( if ProcN = unset_proc_number then
        ProcNDoc = nil
      else
        ProcNDoc = nil %doc(("<" ++ ProcN^string ++ ">"):string)
    ),
    (   ( AppKind = predfunc_app
          % XXX: could print 2d literals explicitly here.
        ; AppKind = array2d_literal
        ),
        Doc = doc_name(Name) ++ ProcNDoc
                ++ doc_maybe_enclosed_Xs_nl(parentheses, nil,
                                            doc_expr(Lang, no), Es)
    ;
        AppKind = gen_call_app,
        ( if Es = [expr(comprehension(simple_array_comp(E), Gens, MaybeWhereE),
                AnnEs, _EInfo)] then
            % The comprehension should never have annotations within it.
            else_unexpected(unify(AnnEs, []), "doc_raw_expr: non-empty AnnEs"),
            Doc = doc_name(Name) ++ ProcNDoc ++ parentheses(
                doc_generators_and_where(Lang, Gens, MaybeWhereE) ) ++ space ++
                mline(parentheses( doc_expr(Lang, no, E) ))
          else
            % Not in the simplest form -- a coercion must have been added, so
            % print it like a normal func/pred call.
            Doc = doc_raw_expr(Lang, no, app(Id, ProcN, predfunc_app, Es))
        )
    ;
        % We print parentheses around an operator application if it is a
        % sub-expression of another operator application.  Eg. a + (b + c),
        % -(a + b), a + (-b), -(-1).
        AppKind = operator_app,
        (   NeedsParensIfOpAppOrLet = yes, Parentheses = parentheses
        ;   NeedsParensIfOpAppOrLet = no,  Parentheses = id
        ),
        ( if Es = [E1, E2] then
            % Nb: using 'nline' here instead of 'mline' is deliberate -- we
            % don't want the second operand to be indented if it's on a new
            % line.  This can make a big difference;  one large model with
            % very long chains of binary operator applications was 2.2GB of
            % text (mostly whitespace) with the indentation, and 13MB without!
            Doc = Parentheses(doc_expr(Lang, yes, E1) ++ space
                    ++ doc_opname(Name)
                    ++ ProcNDoc ++ space ++
                nline(doc_expr(Lang, yes, E2)))
          else if Es = [E] then
            Doc = Parentheses( doc_opname(Name) ++ ProcNDoc ++
                    space ++ doc_expr(Lang, yes, E)
            )
          else
            unexpected("doc_raw_expr: operator_app with not 1 or 2 arguments")
        )
    ).

    % let {                     (let {
    %   <LocalVar1>,              <LocalVar1>,
    %   <LocalVar2>,     OR       <LocalVar2>,
    %   <LocalVar3> }             <LocalVar3> }
    % in                        in
    %   <E>                       <E>)
    %
doc_raw_expr(Lang, NeedsParensIfOpAppOrLet, let(LocalVars, InE)) = Doc :-
    % We print parentheses around a let expression if it is a sub-expression
    % of an operator application.  Eg. "(let { int: x = 3 } in x) + x" -- we
    % shouldn't print that as "let { int: x = 3 } in x + x".
    (   NeedsParensIfOpAppOrLet = yes, Parentheses = parentheses
    ;   NeedsParensIfOpAppOrLet = no,  Parentheses = id
    ),
    Doc = Parentheses(
        "let "
        ++ doc_enclosed_Xs_nl(braces, space, doc_local_var(Lang), LocalVars)
        ++ space ++
    nline("in " ++
        mline(doc_expr(Lang, no, InE))
    )).

    % Coercions are introduced by the frontend and should not form
    % part of a .zinc, .mzn, or .fzn file unless requested.
    %
    % coerce(
    %   <T1>,
    %   <T2>,
    %   <E>)
doc_raw_expr(Lang, NeedsParensIfOpAppOrLet, coerce(T1, T2, E)) =
    ( if
        (   Lang = pp_lang_zinc(print_coercions)
        ;   Lang = pp_lang_minizinc(print_coercions)
        ;   Lang = pp_lang_flatzinc(print_coercions)
        )
      then
        doc("coerce") ++ doc_enclosed_Xs_nl(parentheses, nil, id,
            [to_doc(T1), to_doc(T2), doc_expr(Lang, no, E)])
      else
        doc_expr(Lang, NeedsParensIfOpAppOrLet, E)
    ).

%-----------------------------------------------------------------------------%

    %   ::Ann1
    %   ::Ann2
    %   ::Ann3
    %
:- func doc_annotations(pp_lang, exprs) = doc.

doc_annotations(_,[]) = nil.
doc_annotations(Lang, [AnnE | AnnEs]) =
    doc_annotation(Lang, AnnE) ++ nline(doc_annotations(Lang, AnnEs)).

    %   ::<E>
    %
:- func doc_annotation(pp_lang, expr) = doc.

doc_annotation(Lang, E) =
    doc("::") ++ doc_expr(Lang, no, E).

%-----------------------------------------------------------------------------%

    % <L> <X> |
    %   <Gens>
    %   where
    %     <E> <R>
:- func doc_comprehension(pp_lang, func(doc) = doc, func(X) = doc, X, generators,
        maybe(expr)) = doc.

doc_comprehension(Lang, Parens, DocX, X, Gens, MaybeWhereE) =
    Parens(
        space ++ DocX(X) ++ " | " ++
        doc_generators_and_where(Lang, Gens, MaybeWhereE) ++ space
    ).

    % <Gens>
    %   where
    %   <E>
:- func doc_generators_and_where(pp_lang, generators, maybe(expr)) = doc.

doc_generators_and_where(Lang, Gens, MaybeWhereE) =
    mline(doc_Xs(doc_generator(Lang), Gens)) ++
    mline_doc_maybe_expr(Lang, "where", MaybeWhereE).

    % i,
    % j in
    %   <E>
:- func doc_generator(pp_lang, generator) = doc.

doc_generator(Lang, generator(Vars, E)) =
    doc_Xs(doc_id, Vars) ++ doc(" in ") ++
        mline(doc_expr(Lang, no, E)).

%-----------------------------------------------------------------------------%

    % <Keyword>
    %   <E>
:- func mline_doc_maybe_expr(pp_lang, string, maybe(expr)) = doc.

mline_doc_maybe_expr(_,_,no) = nil.
mline_doc_maybe_expr(Lang, Keyword, yes(E)) =
    space ++ mline(Keyword ++ space ++
        mline(doc_expr(Lang, no, E))).

%-----------------------------------------------------------------------------%

:- func doc_id_expr(pp_lang, id_expr) = doc.

doc_id_expr(Lang, Id - Expr) =
    doc_id(Id) ++ doc(": ") ++ doc_expr(Lang, no, Expr).

%-----------------------------------------------------------------------------%
% Small things
%-----------------------------------------------------------------------------%

    % <TIE>:
    %   <Name>
:- func doc_ti_expr_and_name(pp_lang, ti_expr_and_name) = doc.

doc_ti_expr_and_name(Lang, TIE - Name) =
    doc_ti_expr(Lang, TIE) ++ ": " ++
        mline(doc_name(Name)).

    % (Same as doc_ti_expr_and_name)
:- func doc_ti_expr_and_id(pp_lang, ti_expr_and_id) = doc.

doc_ti_expr_and_id(Lang, TIE - Id) = Doc :-
    Name = Id ^ id_name,
    Doc = doc_ti_expr_and_name(Lang, TIE - Name).

    % <Name>:
    %   <E>
:- func doc_named_expr(pp_lang, named_expr) = doc.

doc_named_expr(Lang, Name - E) =
    doc_name(Name) ++ ": " ++
        mline(doc_expr(Lang, no, E)).

    % <E>:
    %   <E>
:- func doc_index_expr(pp_lang, index_expr) = doc.

doc_index_expr(Lang, E1 - E2) =
    doc_expr(Lang, no, E1) ++ ": " ++
        mline(doc_expr(Lang, no, E2)).

    % <Name> -->
    %   <E>
:- func doc_case_option(pp_lang, id_expr) = doc.

doc_case_option(Lang, Id - E) =
    doc_id(Id) ++ " --> " ++
        mline(doc_expr(Lang, no, E)).

    % Same as a var_decl_item.
    %
:- func doc_local_var(pp_lang, local_var) = doc.

doc_local_var(Lang, local_var(TIE, Id, AnnEs, MaybeInitE0)) = Doc :-
    (
        MaybeInitE0 = no,
        MaybeInitE = no_assignment
    ;
        MaybeInitE0 = yes(AssignE),
        MaybeInitE = rhs_assignment(AssignE)
    ), 
    Doc = doc_raw_item(Lang,
        var_decl_item(TIE, Id ^ id_name, AnnEs, MaybeInitE)).

%-----------------------------------------------------------------------------%

:- func doc_id(id) = doc.

doc_id(Id) =
    doc_name(Id ^ id_name).

:- func doc_name(zinc_name) = doc.

doc_name(Name) =
    doc( if is_operator(lang_minizinc, Name) then "'" ++ Name ++ "'" else Name ).

:- func doc_opname(zinc_name) = doc.

doc_opname(Name) =
    doc( if is_operator(lang_minizinc, Name) then Name else "`" ++ Name ++ "`" ).

%-----------------------------------------------------------------------------%
% Combinators
%-----------------------------------------------------------------------------%

    % <L>
    %   <X1>,
    %   <X2>,       OR      <L><R>
    %   <X3> <R>
:- func doc_enclosed_Xs_nl(func(doc) = doc, doc, func(X) = doc, list(X)) = doc.

doc_enclosed_Xs_nl(Enclose, Bookend, DocX, Xs) =
    doc_enclosed_Xs_2(Enclose, Bookend, mline, DocX, Xs).

    % <L>
    %   <X1>,
    %   <X2>,       OR      nil
    %   <X3> <R>
:- func doc_maybe_enclosed_Xs_nl(func(doc) = doc, doc, func(X) = doc, list(X))
        = doc.

doc_maybe_enclosed_Xs_nl(Enclose, Bookend, DocX, Xs) =
    ( if   Xs = []
      then nil
      else doc_enclosed_Xs_2(Enclose, Bookend, mline, DocX, Xs)
    ).

    % <L> <X1>,
    %   <X2>,       OR      <L><R>
    %   <X3> <R>
:- func doc_enclosed_Xs(func(doc) = doc, doc, func(X) = doc, list(X)) = doc.

doc_enclosed_Xs(Enclose, Bookend, DocX, Xs) =
    doc_enclosed_Xs_2(Enclose, Bookend, ( func(Doc) = nest(2, Doc) ), DocX, Xs).

:- func doc_enclosed_Xs_2(func(doc) = doc, doc, func(doc) = doc,
        func(X) = doc, list(X)) = doc.

doc_enclosed_Xs_2(Enclose, Bookend, XLine, DocX, Xs) =
    ( if Xs = [] then
        Enclose(nil)
      else
        Enclose( Bookend ++
            XLine(doc_Xs(DocX, Xs)) ++ Bookend
        )
    ).

%-----------------------------------------------------------------------------%

    % <X1>,
    % <X2>,
    % <X3>
    %
    % Implemented as:
    %   <X1> ++ ", " ++ nline(<X2>) ++ ", " ++ nline(<X3>)
 :- func doc_Xs(func(X) = doc, list(X)) = doc.

doc_Xs(_DocX, [])       = nil.
doc_Xs( DocX, [X | Xs]) = DocX(X) ++ doc_Xs_2(DocX, Xs).

:- func doc_Xs_2(func(X) = doc, list(X)) = doc.

doc_Xs_2(DocX, Xs) = Doc :-
    list.foldl(doc_Xs_2_acc(DocX), Xs, [], Docs),
    list.foldl(join_docs, Docs, nil, Doc).

:- pred doc_Xs_2_acc((func(X) = doc)::in, X::in, list(doc)::in, list(doc)::out)
    is det.

doc_Xs_2_acc(DocX, X, !Docs) :-
    Doc = ", " ++ nline(DocX(X)),
    !:Docs = [Doc | !.Docs].

:- pred join_docs(doc::in, doc::in, doc::out) is det.

join_docs(Doc, !Docs) :-
    !:Docs = Doc ++ !.Docs.

:- func doc_maybe_X(func(X) = doc, maybe(X)) = doc.

doc_maybe_X(_DocX, no)     = nil.
doc_maybe_X( DocX, yes(X)) = DocX(X).

%-----------------------------------------------------------------------------%
% Line-breaking combinators
%-----------------------------------------------------------------------------%

    % Insert an optional line-break with indentation.
:- func mline(doc) = doc.

mline(Doc) = group(nest(2, line ++ Doc)).

    % Insert an optional line-break without indentation.
:- func nline(doc) = doc.

nline(Doc) = group(line ++ Doc).
