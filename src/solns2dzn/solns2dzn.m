%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2009-2010 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Julien Fischer <juliensf@csse.unimelb.edu.au>
%
% solns2dzn is a tool for processing FlatZinc output.
% It has four modes of operation:
%
% (1) split: output each separate (by default, distinct) solution into a
%     separate file.
%
% (2) canonicalise: sort the solutions in the output, strip comments
%     and (optionally) delete duplicate solutions -- this is the default.
%
% (3) first solution: output the first solution in a FlatZinc solution
%     stream in .dzn format.
%
% (4) last solution: as with (3) but output the last solution in the stream.
%
% XXX: we don't actually canonicalise the solution (other than stripping
% trailing whitespace).  We could use the frontend libs to do this but it
% doesn't seem necessary at the moment.  (And assuming FlatZinc implementations
% actually stick to the spec w.r.t output it shouldn't be necessary.) 
%
%-----------------------------------------------------------------------------%

:- module solns2dzn.
:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is cc_multi.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module solns2dzn_config.

:- import_module bool.
:- import_module char.
:- import_module exception.
:- import_module getopt_io.
:- import_module int.
:- import_module list.
:- import_module maybe.
:- import_module string.
:- import_module univ.
:- import_module unit.

%-----------------------------------------------------------------------------%

:- type bad_input_error
    --->    bad_input_error(string).

%-----------------------------------------------------------------------------%
main(!IO) :-
    try_io(main_2, Result, !IO),
    (
        Result = succeeded(_)
    ;
        Result = exception(Excp),
        ( if univ_to_type(Excp, IO_Error) then
            handle_io_error(IO_Error, !IO)
          else if univ_to_type(Excp, BadInputError) then
            handle_bad_input_error(BadInputError, !IO)
          else 
            rethrow(Result)
        )
    ).

%-----------------------------------------------------------------------------%

:- pred main_2(unit::out, io::di, io::uo) is det.

main_2(unit, !IO) :-
    io.command_line_arguments(Args, !IO),
    OptionOps = option_ops_multi(
        solns2dzn_short_option,
        solns2dzn_long_option,
        (pred(O::out, D::out) is multi :- solns2dzn_option_defaults(O, D))
    ),
    process_options(OptionOps, Args, NonOptionArgs, Result, !IO),
    (
        Result = error(Msg),
        bad_cmdline([Msg], !IO)
    ;
        Result = ok(OptionTable),
        (      if lookup_bool_option(OptionTable, version, yes) then
            io.write_string(solns2dzn_version, !IO)
          else if lookup_bool_option(OptionTable, help, yes) then
            io.write_string(solns2dzn_usage, !IO)
          else
            main_3(OptionTable, NonOptionArgs, !IO)
        )
    ).

%-----------------------------------------------------------------------------%

:- pred main_3(option_table(solns2dzn_option)::in, list(string)::in,
    io::di, io::uo) is det.

main_3(OptionTable, NonOptionArgs, !IO) :-
    (
        % Work out where the input is coming from?
        (
            NonOptionArgs = [],
            InputSrc = src_stdin
        ;
            NonOptionArgs = [SrcFileName],
            InputSrc = src_file(SrcFileName)
        ),
        options_to_action(OptionTable, MaybeAction, !IO),
        (
            MaybeAction = action_ok(Action),
            open_input_stream(InputSrc, OpenResult, !IO),
            (
                OpenResult = ok(InputFile),
                read_solutions(InputFile, SolnInfo, !IO),
                close_input_stream(InputSrc, InputFile, !IO),
                (
                    Action = action_canonicalise,
                    write_canonicalised_output(OptionTable, SolnInfo, !IO)
                ;
                    Action = action_split,
                    write_split_output(OptionTable, InputSrc, SolnInfo, !IO)
                ;
                    Action = action_first_solution,
                    write_first_solution(OptionTable, SolnInfo, !IO)
                ;   
                    Action = action_last_solution,
                    write_last_solution(OptionTable, SolnInfo, !IO)
                )
            ;
                OpenResult = error(IO_Error),
                handle_io_error(IO_Error, !IO)
            )
        ;
            (
                MaybeAction = action_conflict(ConflictingOpts),
                ErrorLines = [
                  "error: only one of the following options may be specified: ",
                  "  " ++ ConflictingOpts
                ]
            ;
                MaybeAction = action_unspecified,
                ErrorLines = [
                  "error: a mode of operation must be specified."
                ]
            ),
            bad_cmdline(ErrorLines, !IO)
        )
    ;
        NonOptionArgs = [_, _ | _],
        bad_cmdline(["error: more than one file specified"], !IO)
    ).        

%-----------------------------------------------------------------------------%
%
% Modes of operation
%

:- type action
    --->    action_canonicalise
    ;       action_first_solution
    ;       action_last_solution 
    ;       action_split.

:- type maybe_action
    --->    action_ok(action)
    ;       action_unspecified
    ;       action_conflict(string).

:- pred options_to_action(option_table(solns2dzn_option)::in,
    maybe_action::out, io::di, io::uo) is det.

options_to_action(OptionTable, MaybeAction, !IO) :-
    lookup_bool_option(OptionTable, canonicalise, Canonicalise),
    lookup_bool_option(OptionTable, first_solution, FirstSoln),
    lookup_bool_option(OptionTable, last_solution, LastSoln),
    lookup_bool_option(OptionTable, split_solutions, SplitSolns),
    some [!Actions] (
        !:Actions = [],
        (
            Canonicalise = yes,
            !:Actions = [action_canonicalise | !.Actions]
        ;
            Canonicalise = no
        ),
        (
            FirstSoln = yes,
            !:Actions = [action_first_solution | !.Actions]
        ;
            FirstSoln = no
        ),
        (
            LastSoln = yes,
            !:Actions = [action_last_solution | !.Actions]
        ;
            LastSoln = no
        ),
        (
            SplitSolns = yes,
            !:Actions = [action_split | !.Actions]
        ;
            SplitSolns = no
        ),
        AllActions = !.Actions
    ),
    (
        AllActions = [],
        MaybeAction = action_unspecified
    ;
        AllActions = [Action],
        MaybeAction = action_ok(Action)
    ;
        AllActions = [_, _ | _],
        ActionStrs = list.map(action_to_option, AllActions),
        ConflictingOpts = string.join_list(", ", ActionStrs),
        MaybeAction = action_conflict(ConflictingOpts)
    ).

:- func action_to_option(action) = string.

action_to_option(action_canonicalise)   = "'--canonicalise'".
action_to_option(action_first_solution) = "'--first-solution'".
action_to_option(action_last_solution)  = "'--last-solution'".
action_to_option(action_split)          = "'--split-solutions'".         

%-----------------------------------------------------------------------------%
%
% Procedures for reading the input
%

    % Did the solver completely explore it's search tree?
    %
:- type search_completeness
    --->    search_complete_sat
    ;       search_complete_unsat
    ;       search_incomplete.

    % A single solution is a list of strings.
    %
:- type soln == list(string).

:- type soln_info
    --->    soln_info(
                si_solns    :: list(soln),
                si_complete :: search_completeness
            ).

:- pred read_solutions(io.text_input_stream::in, soln_info::out,
    io::di, io::uo) is det.

read_solutions(Src, SolnInfo, !IO) :-
    SolnInfo0 = soln_info([], search_incomplete),
    do_read_solutions(Src, [], SolnInfo0, SolnInfo, !IO).

:- pred do_read_solutions(io.text_input_stream::in, list(string)::in,
    soln_info::in, soln_info::out, io::di, io::uo) is det.

do_read_solutions(Src, CurrentPartialSoln, !SolnInfo, !IO) :-
    io.read_line_as_string(Src, ReadLineResult, !IO),
    (
        ReadLineResult = ok(Line0),
        Line = string.strip(Line0),
        ( if Line = "" then
            
            % Ignore blank lines.
            do_read_solutions(Src, CurrentPartialSoln, !SolnInfo, !IO)
          
          else if  string.first_char(Line, '%', _) then 

            % Ignore comments.
            do_read_solutions(Src, CurrentPartialSoln, !SolnInfo, !IO)

          else if Line = "----------" then

            % CurrentPartialSoln has the lines in this solution reversed.
            % Put them back around the right way before adding them to
            % the solution info structure.
            list.reverse(CurrentPartialSoln, Soln),
            Solns = [Soln | !.SolnInfo ^ si_solns],
            !SolnInfo ^ si_solns := Solns,
            do_read_solutions(Src, [], !SolnInfo, !IO)

          else if  Line = "==========" then
            
            (
                CurrentPartialSoln = []
            ;
                CurrentPartialSoln = [_ | _],
                throw(bad_input_error("incomplete solution at end of search?"))
            ),
            !SolnInfo ^ si_complete := search_complete_sat

          else if Line = "=====UNSATISFIABLE=====" then
            
            (
                CurrentPartialSoln = []
            ;
                CurrentPartialSoln = [_ | _],
                throw(bad_input_error("partial solution with unsatisfiable model?"))
            ),
            !SolnInfo ^ si_complete := search_complete_unsat

          else
            
            % If it's not any of the above then it forms part of the
            % output for an individual solution.

            do_read_solutions(Src, [Line | CurrentPartialSoln], !SolnInfo, !IO)
        )
    ;
        ReadLineResult = eof,
        (
            CurrentPartialSoln = []
        ;
            CurrentPartialSoln = [_ | _],
            throw(bad_input_error("incomplete solution at end of file?"))
        )
    ;
        ReadLineResult = error(IO_Error),
        handle_io_error(IO_Error, !IO)
    ).

%-----------------------------------------------------------------------------%

:- pred write_canonicalised_output(option_table(solns2dzn_option)::in,
    soln_info::in, io::di, io::uo) is det.

write_canonicalised_output(OptionTable, SolnInfo, !IO) :-
    lookup_string_option(OptionTable, output_to_file, OutputFile),
    ( if OutputFile = "" then
        OutputDst = dst_stdout
      else
        OutputDst = dst_file(OutputFile)
    ),
    open_output_stream(OutputDst, OpenResult, !IO),
    (
        OpenResult = ok(Dst),
        SolnInfo = soln_info(Solns, SearchComplete),
        lookup_bool_option(OptionTable, delete_duplicates, DeleteDups),
        (
            DeleteDups = yes,
            list.sort_and_remove_dups(Solns, SortedSolns)
        ;
            DeleteDups = no,
            list.sort(Solns, SortedSolns)
        ),
        list.foldl(write_soln(Dst), SortedSolns, !IO),
        (
            SearchComplete = search_complete_sat,
            io.write_string(Dst, "==========\n", !IO)
        ;
            SearchComplete = search_complete_unsat,
            io.write_string(Dst, "=====UNSATISFIABLE=====\n", !IO)
        ;
            SearchComplete = search_incomplete
        ),
        close_output_stream(OutputDst, Dst, !IO)
    ;
        OpenResult = error(IO_Error),
        handle_io_error(IO_Error, !IO)
    ).

:- pred write_soln(io.text_output_stream::in, soln::in, io::di, io::uo)
    is det.

write_soln(Dst, Soln, !IO) :-
    list.foldl(write_soln_line(Dst), Soln, !IO),
    io.write_string(Dst, "----------\n", !IO).

:- pred write_soln_line(io.text_output_stream::in, string::in,
    io::di, io::uo) is det.

write_soln_line(Dst, Line, !IO) :-
    io.format(Dst, "%s\n", [s(Line)], !IO).

%-----------------------------------------------------------------------------%

:- pred write_split_output(option_table(solns2dzn_option)::in,
    input_src::in, soln_info::in, io::di, io::uo) is det.

write_split_output(OptionTable, InputSrc, SolnInfo, !IO) :-
    SolnInfo = soln_info(Solns, _),
    lookup_string_option(OptionTable, output_base, OutputBase),
    ( if OutputBase = "" then
        % If the user didn't provide as with a base for the split file
        % names the use the input file name (if we have one), otherwise just
        % output the solutions in files with integer names.
        (
            InputSrc = src_stdin,
            MaybeBase = no
        ;
            InputSrc = src_file(FileName),
            MaybeBase = yes(FileName)
        )
      else
        MaybeBase = yes(OutputBase)
    ),
    list.foldl2(write_split_file(MaybeBase), Solns, 1, _, !IO).
  
:- pred write_split_file(maybe(string)::in, soln::in, int::in, int::out,
    io::di, io::uo) is det.

write_split_file(MaybeBase, Soln, !N, !IO) :-
    (
        MaybeBase = yes(Base),
        string.format("%s.%d", [s(Base), i(!.N)], FileName)
    ;
        MaybeBase = no,
        string.format("%d", [i(!.N)], FileName)
    ),
    io.open_output(FileName, OpenResult, !IO),
    (
        OpenResult = ok(File),
        list.foldl(write_soln_line(File), Soln, !IO),
        io.close_output(File, !IO),
        !:N = !.N + 1
    ;
        OpenResult = error(IO_Error),
        throw(IO_Error)
    ).

%-----------------------------------------------------------------------------%
%
% First and last solutions
%

:- pred write_first_solution(option_table(solns2dzn_option)::in,
    soln_info::in, io::di, io::uo) is det.

write_first_solution(OptionTable, SolnInfo, !IO) :-
    Solns = SolnInfo ^ si_solns,
    (
        Solns = []
    ;
        Solns = [_ | _],
        % read_solutions gives the list of solutions in reverse, so the
        % first solution is the last one in the list.
        FirstSoln = list.det_last(Solns),
        write_single_solution(OptionTable, FirstSoln, !IO)
    ).     

:- pred write_last_solution(option_table(solns2dzn_option)::in,
    soln_info::in, io::di, io::uo) is det.

write_last_solution(OptionTable, SolnInfo, !IO) :-
    Solns = SolnInfo ^ si_solns,
    (
        Solns = []
    ;
        % read_solutions gives the list of solutions in reverse, so the
        % last solution is the first one in the list.
        Solns = [LastSoln | _],
        write_single_solution(OptionTable, LastSoln, !IO)
    ).     

:- pred write_single_solution(option_table(solns2dzn_option)::in, soln::in,
    io::di, io::uo) is det.

write_single_solution(OptionTable, Soln, !IO) :-
    lookup_string_option(OptionTable, output_to_file, OutputFile),
    ( if OutputFile = "" then
        OutputDst = dst_stdout
      else
        OutputDst = dst_file(OutputFile)
    ),
    open_output_stream(OutputDst, OpenResult, !IO),
    (
        OpenResult = ok(Dst),
        list.foldl(write_soln_line(Dst), Soln, !IO),
        close_output_stream(OutputDst, Dst, !IO)
    ;
        OpenResult = error(IO_Error),
        handle_io_error(IO_Error, !IO)
    ).

%-----------------------------------------------------------------------------%

:- pred open_input_stream(input_src::in, io.res(io.text_input_stream)::out,
    io::di, io::uo) is det.

open_input_stream(Src, Result, !IO) :-
    (
        Src = src_stdin,
        io.stdin_stream(Stdin, !IO),
        Result = ok(Stdin)
    ;
        Src = src_file(FileName),
        io.open_input(FileName, Result, !IO)
    ).

:- pred close_input_stream(input_src::in, io.text_input_stream::in,
    io::di, io::uo) is det.

close_input_stream(Src, Stream, !IO) :-
    (
        Src = src_stdin
    ;
        Src = src_file(_),
        io.close_input(Stream, !IO)
    ).

:- pred open_output_stream(output_dst::in, io.res(io.text_output_stream)::out,
    io::di, io::uo) is det.

open_output_stream(Dst, Result, !IO) :-
    (
        Dst = dst_stdout,
        io.stdout_stream(Stdout, !IO),
        Result = ok(Stdout)
    ;
        Dst = dst_file(FileName),
        io.open_output(FileName, Result, !IO)
    ).

:- pred close_output_stream(output_dst::in, io.text_output_stream::in,
    io::di, io::uo) is det.

close_output_stream(Dst, Stream, !IO) :-
    (
        Dst = dst_stdout
    ;
        Dst = dst_file(_),
        io.close_output(Stream, !IO)
    ).

%-----------------------------------------------------------------------------%
%
% Various settings
%

:- type mode_of_operation
    --->    mode_canonicalise
            % Read the input, strip comments and blank lines, sort,
            % possibly remove duplicates and then output.

    ;       mode_split
            % Read the input, strip comments and blank lines,
            % possibly remove duplicate solutions and  then output each
            % solution to a separate file.
    .

    % Where are we getting our input from?
    %
:- type input_src
    --->    src_stdin
    ;       src_file(string).

    % Where is the output going?
    %
:- type output_dst
    --->    dst_stdout
    ;       dst_file(string).   % --output-to-file


%-----------------------------------------------------------------------------%

:- type solns2dzn_option
    --->    help
    ;       version
    ;       canonicalise
    ;       first_solution
    ;       last_solution
    ;       split_solutions
    ;       delete_duplicates
    ;       output_base
    ;       output_to_file
    .

:- pred solns2dzn_short_option(char::in, solns2dzn_option::out) is semidet.

solns2dzn_short_option('b', output_base).
solns2dzn_short_option('c', canonicalise).
solns2dzn_short_option('f', first_solution).
solns2dzn_short_option('l', last_solution).
solns2dzn_short_option('h', help).
solns2dzn_short_option('o', output_to_file).
solns2dzn_short_option('s', split_solutions).

:- pred solns2dzn_long_option(string::in, solns2dzn_option::out) is semidet.

solns2dzn_long_option("help",               help).
solns2dzn_long_option("version",            version).
solns2dzn_long_option("canonicalise",       canonicalise).
solns2dzn_long_option("delete-dups",        delete_duplicates).
solns2dzn_long_option("delete-duplicates",  delete_duplicates).
solns2dzn_long_option("first",              first_solution).
solns2dzn_long_option("first-solution",     first_solution).
solns2dzn_long_option("last",               last_solution).
solns2dzn_long_option("last-solution",      last_solution).
solns2dzn_long_option("base",               output_base).
solns2dzn_long_option("output-base",        output_base).
solns2dzn_long_option("output-to-file",     output_to_file).
solns2dzn_long_option("split-solns",        split_solutions).
solns2dzn_long_option("split-solutions",    split_solutions).

:- pred solns2dzn_option_defaults(solns2dzn_option, option_data).
:- mode solns2dzn_option_defaults(out, out) is multi.
:- mode solns2dzn_option_defaults(in, out) is det.

solns2dzn_option_defaults(help,                  bool(no)).
solns2dzn_option_defaults(version,               bool(no)).
solns2dzn_option_defaults(canonicalise,          bool(no)).
solns2dzn_option_defaults(delete_duplicates,     bool(yes)).
solns2dzn_option_defaults(first_solution,        bool(no)).
solns2dzn_option_defaults(last_solution,         bool(no)).
solns2dzn_option_defaults(output_base,           string("")).
solns2dzn_option_defaults(output_to_file,        string("")).
solns2dzn_option_defaults(split_solutions,       bool(no)).

%-----------------------------------------------------------------------------%
%
% Usage and version messages
%

    % NOTE: changes here may need to be reflected in:
    %
    %   g12/zinc/man/solns2dzn.1.in
    %
:- func solns2dzn_usage = string.

solns2dzn_usage =
    list.foldr(func(X, Xs) = X ++ "\n" ++ Xs, UsageLines, "") :-
    UsageLines = [
    "Usage: solns2dzn [<options>] [<file>]"
,   "Options:"
,   "    -h, --help"
,   "        Print this message."
,   "    --version"
,   "        Print version information."
,   ""
,   "Modes of operation:"
,   "    -c, --canonicalise"
,   "        Output a canonicalised form of the input."
,   "    -f, --first, --first-solution"
,   "        Output the first solution in a FlatZinc solution stream."
,   "    -l, --last, --last-solution"
,   "        Output the last solution in a FlatZinc solution stream."
,   "    -s, --split-solns, --split-solutions"
,   "        Output each solution to a separate file." 
,   ""
,   "Other options:"
,   "    -d-, --no-delete-dups, --no-delete-duplicates"
,   "        Do not delete duplicate solutions."
,   "    -b <base>, --base <base>, --output-base <base>"
,   "        Use the argument as the base of the files created when writing"
,   "        solutions to separate files"
,   "    -o <file>, --output-to-file <file>"
,   "        Write output to the specified file rather than to the"
,   "        the standard output.  This option is ignored when splitting"
,   "        solutions."
].

:- func solns2dzn_version = string.

solns2dzn_version = VersionMsg :-
    Version = get_solns2dzn_version,
    VersionMsg = 
        "G12 FlatZinc solution processing tool, version " ++ Version ++ "\n"
++      "Copyright (C) 2009-2012 The University of Melbourne and NICTA\n".

%-----------------------------------------------------------------------------%
%
% Error handling procedures
%

:- pred handle_io_error(io.error::in, io::di, io::uo) is det.

handle_io_error(Error, !IO) :-
    io.stderr_stream(Stderr, !IO),
    Msg = io.error_message(Error),
    io.format(Stderr, "solns2dzn: I/O error: %s\n", [s(Msg)], !IO),
    io.set_exit_status(1, !IO).

:- pred bad_cmdline(list(string)::in, io::di, io::uo) is det.

bad_cmdline(Msgs, !IO) :-
    io.stderr_stream(Stderr, !IO),
    WriteErrLine = (pred(Msg::in, !.IO::di, !:IO::uo) is det :-
        io.format(Stderr, "solns2dzn: %s\n", [s(Msg)], !IO)
    ),
    list.foldl(WriteErrLine, Msgs, !IO),
    io.write_string(Stderr, "solns2dzn: use --help for more information.\n",
        !IO),
    io.set_exit_status(1, !IO).
            
:- pred handle_bad_input_error(bad_input_error::in, io::di, io::uo) is det.

handle_bad_input_error(BadInputError, !IO) :-
    BadInputError = bad_input_error(Msg),
    io.stderr_stream(Stderr, !IO),
    io.format(Stderr, "solns2dzn: error: %s\n", [s(Msg)], !IO),
    io.set_exit_status(1, !IO).

%-----------------------------------------------------------------------------%
:- end_module solns2dzn.
%-----------------------------------------------------------------------------%
