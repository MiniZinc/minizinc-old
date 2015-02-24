%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2006-2007 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Nicholas Nethercote <njn@csse.unimelb.edu.au>
% Ralph Becket <rafe@cs.mu.oz.au>
%
% More code that is common to various Zinc tools, but not all of them.  Most
% notably, this code is not used by the Zinc run-time;  if it were, the Zinc
% run-time would have to include top_sort.m and structure_check.m even though
% it wouldn't use them.  If you import this module, you'll probably have to
% import zinc_frontend as well.
%
%-----------------------------------------------------------------------------%

:- module zinc_frontend2.
:- interface.

:- import_module symbol_table.
:- import_module top_sort.
:- import_module zinc_ast.
:- import_module zinc_common.
:- import_module zinc_frontend.
:- import_module zinc_pprint.

:- import_module maybe.
:- import_module pair.
:- import_module list.
:- import_module io.

%-----------------------------------------------------------------------------%
    
    % do_analysis_stages(ErrorControl, ProgramName, StageNames, Lang,
    %   Checking, StageNameSuffix, DebugSpec, MaybeItems,
    %   MaybeItemsAndSymTbl, !IO):
    %
    % The StageNameSuffix allows different invocations of these stages to be
    % given different names, and thus individually printed/dumped from the
    % command line.
    %
:- pred do_analysis_stages(Ctrl::in, string::in, list(string)::in,
    lang::in, checking::in, string::in, debug_spec::in, maybe(ast)::in,
    maybe({sast, symbol_table})::out, io::di, io::uo) is det
    <= frontend_control(Ctrl).

%-----------------------------------------------------------------------------%

    % Output can go to a file or to stdout.
    %
:- type output_destination
    --->    output_to_file(string)
    ;       output_to_stdout.

    % Print the AST (if present) to the given destination -- a file, or stdout.
    %
:- pred maybe_pprint_ast_to_destination(pp_lang::in, maybe(items)::in,
    string::in, output_destination::in, io::di, io::uo) is det.

%-----------------------------------------------------------------------------%

    % Pretty-print the AST (with item ordered by source location) and the
    % top-sort graph.
    %
:- pred pprint_ast_and_top_sort_graph(pair(ast, top_sort_graph)::in,
    list(string)::in, io::di, io::uo) is det.

:- pred dump_ast_and_top_sort_graph(pair(ast, top_sort_graph)::in,
    io::di, io::uo) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module compiler_common.
:- import_module elim_assigns.
:- import_module structure_check.
:- import_module type_inst_check.
:- import_module zinc_pprint.

:- import_module exception.
:- import_module pair.
:- import_module string.
:- import_module unit.
:- import_module univ.

%-----------------------------------------------------------------------------%

do_analysis_stages(Ctrl, ProgramName, StageNames, Lang, Checking,
        StageNameSuffix, DebugSpec, MaybeItems0, MaybeItemsSymTbl4, !IO) :-
    PPLang = pp_lang_minizinc(print_coercions),
    
    % Assignment elimination.
    %
    do_stage(ProgramName, StageNames,
        "assignment-elimination" ++ StageNameSuffix, Lang, DebugSpec,
        eliminate_assignments,
        pprint_ast(PPLang), dump_ast,
        pprint_ast(PPLang), dump_ast,
        MaybeItems0, MaybeItems1, !IO),

    % Topological sorting.
    %
    do_stage(ProgramName, StageNames,
        "top-sorting" ++ StageNameSuffix, Lang, DebugSpec,
        top_sort_ast,
        pprint_ast(PPLang), dump_ast,
        pprint_ast_and_top_sort_graph, dump_ast_and_top_sort_graph,
        MaybeItems1, MaybeItemsAndTopSortGraph2, !IO),
    MaybeItems2 = map_maybe(pair.fst, MaybeItemsAndTopSortGraph2),

    % Structure checking.
    %
    do_stage(ProgramName, StageNames,
        "structure-checking" ++ StageNameSuffix, Lang, DebugSpec,
        structure_check_ast,
        pprint_ast_sorted_by_locn(PPLang), dump_ast,
        pprint_sast_sorted_by_locn(PPLang), dump_sast,
        MaybeItems2, MaybeItems3, !IO),

    % Type-inst checking.
    %
    (
        MaybeItems3 = yes(Items3),
        MaybeCheckingItemsSymTbl3 = yes({Checking, Items3, symbol_table.init})
    ;
        MaybeItems3 = no,
        MaybeCheckingItemsSymTbl3 = no
    ),
    do_stage(ProgramName, StageNames,
        "type-inst-checking" ++ StageNameSuffix, Lang, DebugSpec,
        type_inst_check_sast(Ctrl),
        pprint_pre_type_inst_check(PPLang), dump_pre_type_inst_check,
        pprint_post_type_inst_check(PPLang), dump_post_type_inst_check,
        MaybeCheckingItemsSymTbl3, MaybeItemsSymTbl4, !IO).

%-----------------------------------------------------------------------------%

maybe_pprint_ast_to_destination(_,no,_,_,!IO) :-
    trace [io(!TIO)] (
        verbose("Printing no code", !TIO)
    ).

maybe_pprint_ast_to_destination(PPLang, yes(AST), _ProgramName,
        output_to_stdout, !IO) :-
    trace [io(!TIO)] (
        verbose("Printing code to stdout", !TIO)
    ),
    pprint_ast(PPLang, AST, [], !IO).

maybe_pprint_ast_to_destination(PPLang, yes(AST), ProgramName,
        output_to_file(FileName), !IO) :-
    trace [io(!TIO)] ( 
        verbose("Printing code to file `" ++ FileName ++ "'", !TIO)
    ),
    io.tell(FileName, TellResult, !IO),
    (   
        TellResult = ok,
        pprint_ast(PPLang, AST, [], !IO),
        ResetStdout = (pred(unit::out, !.IO::di, !:IO::uo) is det :-
            io.told(!IO)
        ),
        promise_equivalent_solutions [!:IO] (
            try_io(ResetStdout, ResetStdoutResult, !IO),
            (
                ResetStdoutResult = succeeded(_)
            ;
                ResetStdoutResult = exception(ResetStdoutException),
                % If the exception that was raised is an io_error,
                % then something went wrong when we tried to close the
                % file.  Print the error message.
                ( if ResetStdoutException = univ(IO_Error) then
                    io.stderr_stream(Stderr, !IO),
                    IO_ErrorMsg = io.error_message(IO_Error),
                    io.format(Stderr, "%s: %s\n",
                        [s(ProgramName), s(IO_ErrorMsg)], !IO),
                    get_error_exit_status(ErrorExitStatus, !IO),
                    io.set_exit_status(ErrorExitStatus, !IO)
                  else 
                    % If it's something else then there's nothing
                    % we can do about it here so just rethrow the
                    % exception.
                    rethrow(ResetStdoutResult)
                )
            )
        )
    ;
        TellResult = error(IO_Error),
        io.stderr_stream(Stderr, !IO),
        IO_ErrorMsg = io.error_message(IO_Error),
        io.format(Stderr, "%s: %s\n",
            [s(ProgramName), s(IO_ErrorMsg)], !IO),
        get_error_exit_status(ErrorExitStatus, !IO),
        io.set_exit_status(ErrorExitStatus, !IO)
    ).

pprint_ast_and_top_sort_graph(AST - TopSortGraph, IgnoredFiles, !IO) :-
    SortedAST = sort_ast_by_locn(AST),
    % XXX why is the language hardcoded to Zinc here?  - juliensf.
    pprint_ast_with_locns(pp_lang_zinc(print_coercions), SortedAST,
        IgnoredFiles, !IO),
    pprint_top_sort_graph(TopSortGraph, IgnoredFiles, !IO).

dump_ast_and_top_sort_graph(AST - TopSortGraph, !IO) :-
    dump_ast(AST, !IO),
    dump_top_sort_graph(TopSortGraph, !IO).

:- pred pprint_pre_type_inst_check(pp_lang::in,
    {checking, sast, symbol_table}::in, list(string)::in, io::di, io::uo)
    is det.

pprint_pre_type_inst_check(PPLang, {_Checking, AST, _SymTbl}, IgnoredFiles, !IO) :-
    pprint_sast_sorted_by_locn(PPLang, AST, IgnoredFiles, !IO).

:- pred dump_pre_type_inst_check({checking, sast, symbol_table}::in,
    io::di, io::uo) is det.

dump_pre_type_inst_check({D_Checking, AST, SymTbl}, !IO) :-
    io.write_string("% Checking = " ++ D_Checking^string ++ "\n", !IO),
    dump_sast(AST, !IO),
    dump_symbol_table(SymTbl, !IO).

:- pred pprint_post_type_inst_check(pp_lang::in,
    {sast, symbol_table}::in, list(string)::in, io::di, io::uo) is det.

pprint_post_type_inst_check(PPLang, {AST, _SymTbl}, IgnoredFiles, !IO) :-
    pprint_sast_sorted_by_locn(PPLang, AST, IgnoredFiles, !IO).

:- pred dump_post_type_inst_check({sast, symbol_table}::in,
    io::di, io::uo) is det.

dump_post_type_inst_check({AST, SymTbl}, !IO) :-
    dump_sast(AST, !IO),
    dump_symbol_table(SymTbl, !IO).

%-----------------------------------------------------------------------------%
:- end_module zinc_frontend2.
%-----------------------------------------------------------------------------%
