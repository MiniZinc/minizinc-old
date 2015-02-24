%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2011-2012 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Julien Fischer <juliensf@csse.unimelb.edu.au>
%
% MiniZinc solution printing tool.
%
% A MiniZinc output specification (.ozn file) is generated by mzn2fzn when the
% model instance is flattened.  This program is responsible for combining the
% output specification with the solution stream from a FlatZinc implementation
% and then printing out the solutions in the format given in the specification.
%
% The contents of a model output specification are a subset of of MiniZinc.
% The following  are _not_ allowed in a .ozn file:
%
%   * Include items.
%   * Annotations.
%   * Predicate declarations, except for test declarations.
%   * Solve items.
%   * Assigned variable declarations.
%   * Unassigned parameter declarations.
%   * Assign items.
%   * Implicit array indexes on global variables.
%     (They are ok on let-variables.)
%
% The following can appear in a .ozn file:
%
%   * Assigned parameter declarations.
%   * Unassigned variable declarations.
%   * Test declarations.
%   * An output item.  (Must be present.)
%
%-----------------------------------------------------------------------------%

:- module solns2out.
:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is cc_multi.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module read_soln.
:- import_module solns2out_config.

:- import_module common_format.
:- import_module errors.
:- import_module flatten.
:- import_module flatten.array.
:- import_module flatten.env.
:- import_module flatten.expr.
:- import_module flatten.item.
:- import_module flatten.string.
:- import_module types.

:- import_module compiler_common.
:- import_module parse_stage.
:- import_module symbol_table.
:- import_module top_sort.
:- import_module type_inst_check.
:- import_module types_and_insts.
:- import_module zinc_ast.
:- import_module zinc_common.
:- import_module zinc_error.
:- import_module zinc_frontend.
:- import_module zinc_frontend2.
:- import_module zinc_pprint.

:- import_module array.
:- import_module bool.
:- import_module char.
:- import_module exception.
:- import_module getopt_io.
:- import_module int.
:- import_module list.
:- import_module maybe.
:- import_module pair.
:- import_module string.
:- import_module unit.
:- import_module univ.

%-----------------------------------------------------------------------------%

main(!IO) :-
    ( try [io(!IO)] (
        io.command_line_arguments(Args, !IO),
        OptionOps = option_ops_multi(
            solns2out_short_option,
            solns2out_long_option,
            (pred(O::out, D::out) is multi :- solns2out_option_defaults(O, D))
        ),
        process_options(OptionOps, Args, NonOptionArgs, Result, !IO),
        (
            Result = error(Msg),
            bad_cmdline(solns2out_program, Msg, !IO)
        ;
            Result = ok(OptionTable),

            % Set up the global state for the frontend.
            %
            lookup_bool_option(OptionTable, verbose, Verbose),
            lookup_bool_option(OptionTable, statistics, Statistics),
            VeryVerbose = no,   % Not currently used by solns2out.
            init_frontend_globals(Verbose, VeryVerbose, Statistics, !IO),

            ( if lookup_bool_option(OptionTable, version, yes) then
                io.write_string(solns2out_version, !IO)
              else if lookup_bool_option(OptionTable, help, yes) then
                io.write_string(solns2out_usage, !IO)
              else
                main_2(OptionTable, NonOptionArgs, !IO)
            )
        )
    )
    then
        true
    catch IO_Error ->
        handle_io_error(solns2out_program, IO_Error, !IO)
    catch FlatteningError ->
        FlatteningError = flattening_error(SrcLocn, Msg),
        error_at_locn(Msg, SrcLocn, [], Errors),
        pprint_zinc_errors(pp_lang_minizinc(dont_print_coercions),
            solns2out_program, Errors, !IO),
        io.set_exit_status(1, !IO)
    catch UnsatModel ->
        UnsatModel = unsatisfiable_model(SrcLocn, Context),
        error_at_locn(Context, SrcLocn, [], Errors),
        pprint_zinc_errors(pp_lang_minizinc(dont_print_coercions),
            solns2out_program, Errors, !IO),
        io.set_exit_status(1, !IO)
    catch_any Other ->
        throw(Other)
    ).

%-----------------------------------------------------------------------------%

:- pred main_2(option_table(solns2out_option)::in, list(string)::in,
    io::di, io::uo) is det.

main_2(OptionTable, Args, !IO) :-
    (
        Args = [],
        bad_cmdline(solns2out_program, "no .ozn file specified", !IO)
   ;
        Args = [_ | _],
        list.filter(is_ozn, Args, OznArgs, NonOznArgs),
        (
            OznArgs = [],
            bad_cmdline(solns2out_program, "no .ozn file specified", !IO)
        ;
            OznArgs = [OznFile],
            (
                (
                    NonOznArgs = [],
                    SolnsSrc = solns_src_stdin
                ;
                    NonOznArgs = [SolnsFile],
                    SolnsSrc = solns_src_file(SolnsFile)
                ),
                main_3(OptionTable, OznFile, SolnsSrc, !IO)
            ;
                NonOznArgs = [_, _ | _],
                bad_cmdline(solns2out_program,
                    "multiple solution streams specified", !IO)
            )
        ;
            OznArgs = [_, _ | _],
            bad_cmdline(solns2out_program, "multiple .ozn files specified",
                !IO)
        )
    ).

%-----------------------------------------------------------------------------%

    % What is the source of the FlatZinc solution stream we are processing?
    %
:- type solns_src
    --->    solns_src_file(string)
    ;       solns_src_stdin.

:- pred is_ozn(string::in) is semidet.

is_ozn(FileName) :-
    string.suffix(FileName, ".ozn").

%-----------------------------------------------------------------------------%

:- pred main_3(option_table(solns2out_option)::in, string::in, solns_src::in,
    io::di, io::uo) is det.

main_3(OptionTable, OznFile, SolnSrc, !IO) :-

    % Where are we writing the output to?
    %
    lookup_string_option(OptionTable, output_to_file, OutputFileName),
    ( if    OutputFileName = ""
      then  OutputDest = output_to_stdout
      else  OutputDest = output_to_file(OutputFileName)
    ),

    AllInputs = [zi_model_file(OznFile)],

    % Setup parameter required for the frontend library.
    %
    DebugSpec = make_solns2out_debug_spec(OptionTable),
    Lang = lang_minizinc,
    StageNames = solns2out_stage_names,
    %Checking = model_checking,

    % Parsing.
    % Nb: the pprint-before function will print nothing, because the
    % AST is empty at that point.
    EmptyAST = [],
    SearchDirs = ["."],
    do_io_stage(solns2out_program, StageNames,
        "parsing", Lang, DebugSpec,
        parse_zinc_model(no_includes, AllInputs, SearchDirs),
        pprint_ast(pp_lang_minizinc(print_coercions)), io.write,
        pprint_ast(pp_lang_minizinc(print_coercions)), dump_ast,
        yes(EmptyAST), MaybeItems, !IO),

    do_stage(solns2out_program, StageNames,
        "top-sorting", Lang, DebugSpec,
         top_sort_ast,
         pprint_ast(pp_lang_minizinc(print_coercions)), dump_ast,
         pprint_ast_and_top_sort_graph, dump_ast_and_top_sort_graph,
         MaybeItems, MaybeItemsAndTopSortGraph, !IO),

    MaybeTopSortedItems = map_maybe(pair.fst, MaybeItemsAndTopSortGraph),

    % OZN structure checking.
    do_stage(solns2out_program, StageNames,
        "structure-checking", Lang, DebugSpec,
        ozn_structure_check,
        pprint_ast_sorted_by_locn(pp_lang_minizinc(print_coercions)), dump_ast,
        pprint_oast_sorted_by_locn, dump_oast,
        MaybeTopSortedItems, MaybeOAST, !IO),

    % Type check the OZN.
    Ctrl = solns2out_control,
    do_stage(solns2out_program, StageNames,
        "type-inst-checking", Lang, DebugSpec,
        type_inst_check_oast(Ctrl),
        pprint_oast_sorted_by_locn, dump_oast,
        pprint_oast_post_ti_check, dump_oast_post_ti_check,
        MaybeOAST, MaybeOASTAndSymTbl, !IO),
    (
        MaybeOASTAndSymTbl = no
    ;
        MaybeOASTAndSymTbl = yes({OAST, SymTbl}),
        OP = gather_output_params(OptionTable),
        lookup_int_option(OptionTable, ignore_leading_lines,
            LeadingLinesToIgnore),
        read_and_print_solutions(OP, SolnSrc, OutputDest, OAST, SymTbl,
            LeadingLinesToIgnore, !IO)
    ).

%-----------------------------------------------------------------------------%

:- pred read_and_print_solutions(output_params::in, solns_src::in,
    output_destination::in, oast::in, symbol_table::in, int::in,
    io::di, io::uo) is det.

read_and_print_solutions(OP, SolnsSrc, OutputDest, OAST, SymbolTable,
        NumLeadIgnoreLines, !IO) :-
    (
        SolnsSrc = solns_src_file(InputFileName),
        io.open_input(InputFileName, MaybeInputFile, !IO),
        (
            MaybeInputFile = ok(InputFile)
        ;
            MaybeInputFile = error(OpenInputFileError),
            throw(OpenInputFileError)
        ),
        InputFileCloseNeeded = yes
    ;
        SolnsSrc = solns_src_stdin,
        io.stdin_stream(InputFile, !IO),
        InputFileCloseNeeded = no
    ),
    (
        OutputDest = output_to_file(OutputFileName),
        io.open_output(OutputFileName, MaybeOutputFile, !IO),
        (
            MaybeOutputFile = ok(OutputFile)
        ;
            MaybeOutputFile = error(OpenOutputFileError),
            throw(OpenOutputFileError)
        ),
        OutputFileCloseNeeded = yes
    ;
        OutputDest = output_to_stdout,
        io.stdout_stream(OutputFile, !IO),
        OutputFileCloseNeeded = no
    ),
    discard_leading_lines(NumLeadIgnoreLines, InputFile, !IO),
    read_and_print_solutions_2(OP, InputFile, OutputFile, OAST, SymbolTable,
        !IO),
    (
        InputFileCloseNeeded = no
    ;
        InputFileCloseNeeded = yes,
        io.close_input(InputFile, !IO)
    ),
    (
        OutputFileCloseNeeded = no
    ;
        OutputFileCloseNeeded = yes,
        io.close_output(OutputFile, !IO)
    ).

:- pred read_and_print_solutions_2(output_params::in,
    io.text_input_stream::in, io.text_output_stream::in, oast::in,
    symbol_table::in, io::di, io::uo) is det.

read_and_print_solutions_2(OP, InputFile, OutputFile, OAST, SymbolTable, !IO) :-
    read_solution(InputFile, solns2out_program, ReadSolnResult, !IO),
    (
        (
            ReadSolnResult = result_unknown(Comments),
            io.write_string(OutputFile, OP ^ output_unknown_msg, !IO),
            io.nl(OutputFile, !IO)
        ;
            ReadSolnResult = result_unbounded(Comments),
            io.write_string(OutputFile, OP ^ output_unbounded_msg, !IO),
            io.nl(OutputFile, !IO)
        ;
            ReadSolnResult = result_unsatisfiable(Comments),
            io.write_string(OutputFile, OP ^ output_unsat_msg, !IO),
            io.nl(OutputFile, !IO)
        ;
            ReadSolnResult = result_search_complete(Comments),
            io.write_string(OutputFile, OP ^ output_complete_msg, !IO),
            io.nl(OutputFile, !IO)
        ),
        print_comments(OP ^ output_print_comments, OutputFile, Comments, !IO)
    ;
        ReadSolnResult = result_soln(SolnItems, Comments),
        print_solution(OutputFile, OAST, SymbolTable, SolnItems, Continue, !IO),
        (
            Continue = yes,
            print_comments(OP ^ output_print_comments, OutputFile, Comments,
                !IO),
            io.write_string(OutputFile, OP ^ output_soln_sep, !IO),
            io.nl(OutputFile, !IO),
            io.flush_output(OutputFile, !IO),
            read_and_print_solutions_2(OP, InputFile, OutputFile, OAST,
                SymbolTable, !IO)
        ;
            Continue = no
        )
    ;
        ReadSolnResult = result_parse_error
        % Do nothing; any error messages have already been printed.
    ;
        ReadSolnResult = result_eof(Comments),
        print_comments(OP ^ output_print_comments, OutputFile, Comments, !IO)
    ).

:- pred print_comments(bool::in, io.text_output_stream::in, comments::in,
    io::di, io::uo) is det.

print_comments(PrintComments, OutputFile, Comments, !IO) :-
    (
        PrintComments = no
    ;
        PrintComments = yes,
        io.write_list(OutputFile, Comments, "\n", io.write_string, !IO),
        (
            Comments = []
        ;
            Comments = [_ | _],
            io.nl(OutputFile, !IO)
        )
    ). 

:- pred discard_leading_lines(int::in, io.text_input_stream::in,
    io::di, io::uo) is det.

discard_leading_lines(N, File, !IO) :-
    ( if N > 0 then
        io.read_line_as_string(File, ReadResult, !IO),
        (
            ReadResult = ok(_),
            discard_leading_lines(N - 1, File, !IO)
        ;
            ReadResult = eof
        ;
            ReadResult = error(IO_Error),
            throw(IO_Error)
        )
      else
        true
    ).

%-----------------------------------------------------------------------------%

:- pred print_solution(io.text_output_stream::in, oast::in, symbol_table::in,
    items::in, bool::out, io::di, io::uo) is det.

print_solution(OutputFile, OAST, SymbolTable, !.SolnItems, Continue, !IO) :-
    type_inst_check_mzn_soln(solns2out_control, SymbolTable, _SolnSymbolTable,
        !SolnItems, Errors, _Warnings),
    (
        Errors = [],
        minizinc_ast_to_output(OutputFile, OAST, !.SolnItems, !IO),
        Continue = yes
    ;
        Errors = [_ | _],
        PPLang = pp_lang_minizinc(print_coercions),
        pprint_zinc_errors(PPLang, solns2out_program, Errors, !IO),
        io.set_exit_status(1, !IO),
        Continue = no
    ).

:- pred minizinc_ast_to_output(io.text_output_stream::in,
    oast::in, items::in, io::di, io::uo) is det.

minizinc_ast_to_output(File, OAST, Soln, !IO) :-
    promise_equivalent_solutions [!:IO] (
        flatten_mzn_model_for_output(OAST, Soln, Env),
        process_output_item_for_output(File, OAST, Env, !IO)
    ).

:- pred flatten_mzn_model_for_output(oast::in, items::in, env::out) is det.
 
flatten_mzn_model_for_output(OAST, Soln, !:Env) :-
    !:Env = new_env,
    OAST = oast(MZItems, _),
    trace [io(!IO)] (
        verbose("  Flattening items for output...", !IO)
    ),

    % Flatten test declarations from the .ozn file.
    %
    list.foldl(flatten_process_predfunc_item, MZItems, !Env),
 
    % Next we process variable declarations and assignment items
    % from the .ozn file.
    %
    list.foldl(flatten_process_var_decl_item, MZItems, !Env),
 
    % And now the assignments from the solution.
    %
    list.foldl(flatten_process_var_decl_item, Soln, !Env).

:- pred process_output_item_for_output(io.text_output_stream::in,
    oast::in, env::in, io::di, io::uo) is det.

process_output_item_for_output(File, OAST, Env, !IO) :-
    OAST = oast(_, OutputItem),
    OutputItem = oast_output_item(OutputExpr, SrcLocn),
    Context = [ ["In output item.\n"] | init_context(SrcLocn) ],
    flatten_expr(Context, OutputExpr, MZ, Env, _),
    A0 = mzn_expr_to_string_array(Context, MZ),
    A = fully_deref_string_array(Context, A0, Env),
    (
        A = array_var(_, _),
        minizinc_internal_error(Context, $pred, "expected array_items")
     ;
        A = array_items(_, ItemsA),
        % We need to keep track of whether the final character printed was
        % a newline or not.  If the final character printed was not a newline
        % then we will need to insert one so that the subsequent solutions
        % seperator (or subsequent solution if separators are not being
        % printed) begins on a separate line.
        array.foldl2(process_output_item_for_output_2(File, Context, Env),
            ItemsA, do_not_have_terminating_nl, HaveTerminatingNl, !IO),
        (
            HaveTerminatingNl = have_terminating_nl
        ;
            HaveTerminatingNl = do_not_have_terminating_nl,
            io.nl(File, !IO)
        )
     ).

:- pred process_output_item_for_output_2(io.text_output_stream::in,
    error_context::in, env::in, string_expr::in, 
    have_terminating_nl::in, have_terminating_nl::out,
    io::di, io::uo) is det.

process_output_item_for_output_2(File, Context, Env, StrExpr, !HTN, !IO) :-
    (
        ( 
            StrExpr = string_const(Str)
        ;
            StrExpr = string_show(MZ),
            flatten_show_to_string(Context, MZ, Str, Env, _)
        ),
        update_htn_and_write(File, Str, !HTN, !IO)
    ;
        StrExpr = A ++ B,
        process_output_item_for_output_2(File, Context, Env, A, !HTN, !IO),
        process_output_item_for_output_2(File, Context, Env, B, !HTN, !IO)
    ;
        StrExpr = string_concat(Strs),
        list.foldl2(process_output_item_for_output_2(File, Context, Env), Strs,
            !HTN, !IO)
    ;
        StrExpr = string_join(_, _),
        Str = format_string_expr_unquoted(StrExpr),
        update_htn_and_write(File, Str, !HTN, !IO)
    ).

:- type have_terminating_nl
    --->    have_terminating_nl
    ;       do_not_have_terminating_nl.

:- pred update_htn_and_write(io.text_output_stream::in, string::in,
    have_terminating_nl::in, have_terminating_nl::out, io::di, io::uo) is det.

update_htn_and_write(File, String, !HTN, !IO) :-
    % Empty strings in the output array cannot affect the final character
    % printed.
    ( if String = "" then
        true
      else
        ( if string.suffix(String, "\n") then
            !:HTN = have_terminating_nl
          else
            !:HTN = do_not_have_terminating_nl
        ),
        io.write_string(File, String, !IO)
    ).

%-----------------------------------------------------------------------------%

% XXX Fill these in.

:- pred pprint_oast_sorted_by_locn : writer2(oast) `with_inst` writer2.

pprint_oast_sorted_by_locn(_, _, !IO).

:- pred dump_oast : writer(oast) `with_inst` writer.

dump_oast(_, !IO).

:- pred pprint_oast_post_ti_check : writer2({oast, symbol_table})
    `with_inst` writer2.

pprint_oast_post_ti_check(_, _, !IO).

:- pred dump_oast_post_ti_check : writer({oast, symbol_table})
    `with_inst` writer.

dump_oast_post_ti_check(_, !IO).

%-----------------------------------------------------------------------------%
%
% Structure check ozn files
%

:- pred ozn_structure_check : stage(ast, oast) `with_inst` stage.

ozn_structure_check(_Lang, AST, OAST, Errs, /*Warns*/[]) :-
    list.foldl3(ozn_structure_check_item, AST, [], RevItems, [], OutputItems,
        [], Errs0),
    (
        OutputItems = [],
        NoOutputItemMsg = [
            words("structure error: no output item")
        ],
        error_at_locn(NoOutputItemMsg, unknown, Errs0, Errs),
        OutputItem = dummy_oast_output_item
    ;
        OutputItems = [OutputItem],
        Errs = Errs0
    ;
        OutputItems = [FirstOutputItem | RestOutputItems @ [_ | _]],
        RestOutputParts = list_to_parts(
            (func(I) = src_locn(I ^ oast_out_locn)),
            RestOutputItems),
        MultipleOutputItemMsg = [
            words("structure error: multiple output items."), nl,
            words("Other output items are at:")
        ] ++ RestOutputParts,
        error_at_locn(MultipleOutputItemMsg, FirstOutputItem ^ oast_out_locn,
            Errs0, Errs),
        OutputItem = dummy_oast_output_item
    ),
    list.reverse(RevItems, Items),
    OAST = oast(Items, OutputItem).

:- func dummy_oast_output_item = oast_output_item.

dummy_oast_output_item =
    oast_output_item(expr(anon_var, [],  expr_info(unknown, ti_unknown)),
        unknown).

:- pred ozn_structure_check_item(item::in, items::in, items::out,
    list(oast_output_item)::in, list(oast_output_item)::out,
    zinc_errors::in, zinc_errors::out) is det.

ozn_structure_check_item(Item, !Items, !OutputItems, !Errors) :-
    Item = item(RawItem, Locn),
    (
        ( RawItem = var_decl_item(_, _, _, _)
        ; RawItem = assign_item(_, _)
        ),
        list.cons(Item, !Items)
    ;
        RawItem = output_item(Expr),
        list.cons(oast_output_item(Expr, Locn), !OutputItems)
    ;
        RawItem = predfunc_item(RetType, _, _, _, _, _),
        (
            RetType = test_ret,
            list.cons(Item, !Items)
        ;
            (
                RetType = pred_ret,
                Desc = "predicate declaration items"
            ;
                RetType = func_ret(_),
                Desc = "function declaraation items"
            ),
            report_item_not_allowed(Desc, Locn, !Errors)
        )
    ;
        (
            RawItem = annotation_item(_, _),
            Desc = "annotation items"
        ;
            RawItem = solve_item(_, _),
            Desc = "solve items"
        ;
            RawItem = constraint_item(_),
            Desc = "constraint items"
        ),
        report_item_not_allowed(Desc, Locn, !Errors)
    ).

:- pred report_item_not_allowed(string::in, src_locn::in,
    zinc_errors::in, zinc_errors::out) is det.

report_item_not_allowed(Desc, Locn, !Errors) :-
    BadItemMsg = [
        words("structure error:"), fixed(Desc),
        words("are not allowed in ozn files.")
    ],
    error_at_locn(BadItemMsg, Locn, !Errors).

%-----------------------------------------------------------------------------%
%
% Control
%

:- type solns2out_control ---> solns2out_control.

:- instance frontend_control(solns2out_control) where [
    % XXX maybe this should just throw an exception since it shouldn't
    %     occur?
    ( warn_unknown_fzn_annotations(_) = yes ),
    ( extra_builtin_annotation(_, _, _, _) :- false ),
    ( post_typecheck_var_decl_action(_) = no ),
    ( post_typecheck_constraint_action(_) = no ),
    ( post_typecheck_solve_action(_) = no )
].

%-----------------------------------------------------------------------------%

:- type solns2out_option
    --->    help
    ;       version
    ;       verbose
    ;       output_to_file
    ;       statistics

    % Options that control the formatting of the output.
   
    ;       ignore_leading_lines 
    ;       output_comments
    ;       solution_separator 
    ;       unsatisfiable_msg
    ;       unbounded_msg
    ;       unknown_msg
    ;       search_complete_msg.

:- pred solns2out_short_option(char::in, solns2out_option::out) is semidet.

solns2out_short_option('h', help).
solns2out_short_option('o', output_to_file).
solns2out_short_option('S', statistics).
solns2out_short_option('v', verbose).
solns2out_short_option('i', ignore_leading_lines).

:- pred solns2out_long_option(string::in, solns2out_option::out) is semidet.

solns2out_long_option("help",                 help).
solns2out_long_option("version",              version).
solns2out_long_option("verbose",              verbose).
solns2out_long_option("output-to-file",       output_to_file).
solns2out_long_option("statistics",           statistics).
solns2out_long_option("output-comments",      output_comments).
solns2out_long_option("ignore-lines",         ignore_leading_lines).
solns2out_long_option("ignore-leading-lines", ignore_leading_lines).
solns2out_long_option("soln-sep",             solution_separator).
solns2out_long_option("soln-separator",       solution_separator).
solns2out_long_option("solution-separator",   solution_separator).
solns2out_long_option("unsat-msg",            unsatisfiable_msg).
solns2out_long_option("unsatisfiable-msg",    unsatisfiable_msg).
solns2out_long_option("unbounded-msg",        unbounded_msg).
solns2out_long_option("unknown-msg",          unknown_msg).
solns2out_long_option("search-complete-msg",  search_complete_msg).

:- pred solns2out_option_defaults(solns2out_option, option_data).
:- mode solns2out_option_defaults(out, out) is multi.
:- mode solns2out_option_defaults(in, out) is det.

solns2out_option_defaults(help,                  bool(no)).
solns2out_option_defaults(version,               bool(no)).
solns2out_option_defaults(output_to_file,        string("")).
solns2out_option_defaults(statistics,            bool(no)).
solns2out_option_defaults(verbose,               bool(no)).
solns2out_option_defaults(output_comments,       bool(yes)).
solns2out_option_defaults(ignore_leading_lines,  int(0)).
solns2out_option_defaults(solution_separator,    maybe_string(no)).
solns2out_option_defaults(unsatisfiable_msg,     maybe_string(no)).
solns2out_option_defaults(unbounded_msg,         maybe_string(no)).
solns2out_option_defaults(unknown_msg,           maybe_string(no)).
solns2out_option_defaults(search_complete_msg,   maybe_string(no)).

%-----------------------------------------------------------------------------%

:- type output_params
    --->    output_params(
                output_print_comments :: bool,
                output_soln_sep       :: string,
                output_unsat_msg      :: string,
                output_unbounded_msg  :: string,
                output_unknown_msg    :: string,
                output_complete_msg   :: string
            ).

:- func gather_output_params(option_table(solns2out_option)) = output_params.

gather_output_params(OptionTable) = Params :-
    lookup_bool_option(OptionTable, output_comments, PrintComments),
    lookup_maybe_string_option(OptionTable, solution_separator, MaybeSolnSep),
    (
        MaybeSolnSep = yes(SolnSep)
    ;
        MaybeSolnSep = no,
        SolnSep = "----------"
    ),
    lookup_maybe_string_option(OptionTable, unsatisfiable_msg, MaybeUnsatMsg),
    (
        MaybeUnsatMsg = yes(UnsatMsg)
    ;
        MaybeUnsatMsg = no,
        UnsatMsg = "=====UNSATISFIABLE====="
    ),
    lookup_maybe_string_option(OptionTable, unbounded_msg, MaybeUnboundedMsg),
    (
        MaybeUnboundedMsg = yes(UnboundedMsg)
    ;
        MaybeUnboundedMsg = no,
        UnboundedMsg = "=====UNBOUNDED====="
    ),
    lookup_maybe_string_option(OptionTable, unknown_msg, MaybeUnknownMsg),
    (
        MaybeUnknownMsg = yes(UnknownMsg)
    ;
        MaybeUnknownMsg = no,
        UnknownMsg = "=====UNBOUNDED====="
    ),
    lookup_maybe_string_option(OptionTable, search_complete_msg,
        MaybeCompleteMsg),
    (
        MaybeCompleteMsg = yes(CompleteMsg)
    ;
        MaybeCompleteMsg = no,
        CompleteMsg = "=========="
    ),
    Params = output_params(
        PrintComments,
        SolnSep,
        UnsatMsg,
        UnboundedMsg,
        UnknownMsg,
        CompleteMsg
    ).

%-----------------------------------------------------------------------------%
%
% Usage and version messages
%

    % NOTE: changes here may need to be reflected in:
    %
    %   g12/zinc/man/solns2out.1.in
    %
:- func solns2out_usage = string.

solns2out_usage =
    list.foldr(func(X, Xs) = X ++ "\n" ++ Xs, UsageLines, "") :-
    UsageLines = [
    "Usage: solns2out [<options>] <model>.ozn [<soln>.szn]"
,   "Options:"
,   "    -h, --help"
,   "        Print this message."
,   "    --version"
,   "        Print version information."
,   "    -o <file>, --output-to-file <file>"
,   "        Write output to the specified file rather than to the"
,   "        the standard output."
,   "    --no-output-comments"
,   "        Do not print comments in the FlatZinc solution stream."
,   "    -i <n>, --ignore-lines <n>, --ignore-leading-lines <n>"
,   "        Ignore the first <n> lines in the FlatZinc solution stream."
,   "    --soln-sep <s>, --soln-separator <s>, --solution-separator <s>"
,   "        Specify the string used to separate solutions."
,   "        The default is to use the FlatZinc solution separator,"
,   "        \"----------\"."
,   "    --unsat-msg <msg>, --unsatisfiable-msg <msg>"
,   "        Specify the message to print if the model instance is"
,   "        unsatisfiable."
,   "        The default is to print \"=====UNSATISFIABLE=====\"."
,   "    --unbounded-msg <msg>"
,   "        Specify the message to print if the objective of the"
,   "        model instance is unbounded."
,   "        The default is to print \"=====UNBOUNDED=====\"."
,   "    --unknown-msg <msg>"
,   "        Specify the message to print if search terminates without"
,   "        the entire search space having been explored and no"
,   "        solution has been found."
,   "        The default is to print \"=====UNKNOWN=====\"."
,   "    --search-complete-msg <msg>"
,   "        Specify the message to print if search terminates having"
,   "        explored the entire search space."
,   "        The default is to print \"==========\"."
].

:- func solns2out_version = string.

solns2out_version = VersionMsg :-
    Version = get_solns2out_version,
    VersionMsg =
        "G12 MiniZinc solution printing tool, version " ++ Version ++ "\n"
++      "Copyright (C) 2011-2012 The University of Melbourne and NICTA\n".

%-----------------------------------------------------------------------------%

    % NOTE: if you add or remove stages please update the solns2out man
    % page in g12/zinc/man/solns2out.1.in
    %
:- func solns2out_stage_names = list(string).

solns2out_stage_names = [
    "parsing",
    "top-sorting",
    "structure-checking",
    "type-inst-checking",
    "formatting-output"
].

    % Return the debug spec that is implicit in the option table.
    % This assumes that we have already checked that the stage names are
    % valid.
    %
:- func make_solns2out_debug_spec(option_table(solns2out_option)) = debug_spec.

make_solns2out_debug_spec(_OptionTable) = DebugSpec :-
    %lookup_accumulating_option(OptionTable, pprint_before, PPrintBefore),
    %lookup_accumulating_option(OptionTable, pprint_after,  PPrintAfter),
    %lookup_accumulating_option(OptionTable, pprint_ignore_file,
    %    PPrintIgnoredFiles),
    %lookup_accumulating_option(OptionTable, dump_before,   DumpBefore),
    %lookup_accumulating_option(OptionTable, dump_after,    DumpAfter),
    %lookup_accumulating_option(OptionTable, stop_before,   StopBefore),
    %lookup_accumulating_option(OptionTable, stop_after,    StopAfter),
    %DebugSpec = new_debug_spec(PPrintBefore, PPrintAfter,
    %    PPrintIgnoredFiles, DumpBefore, DumpAfter, StopBefore, StopAfter)
    DebugSpec = new_debug_spec([], [], [], [], [], [], []).

%-----------------------------------------------------------------------------%

:- func solns2out_program = string.

solns2out_program = "solns2out".

%-----------------------------------------------------------------------------%
:- end_module solns2out.
%-----------------------------------------------------------------------------%
