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
% Code that is common to the various Zinc tools, including the Zinc run-time.
%
%-----------------------------------------------------------------------------%

:- module zinc_frontend.
:- interface.

:- import_module compiler_common.
:- import_module zinc_common.

:- import_module bool.
:- import_module getopt_io.
:- import_module maybe.
:- import_module list.
:- import_module io.

%-----------------------------------------------------------------------------%

    % init_frontend_globals(Verbose, VeryVerbose,  Statistics, !IO):
    % The frontend attaches a number of globals to the I/O state that are used
    % to control things like whether progress messages are printed.
    %
:- pred init_frontend_globals(bool::in, bool::in, bool::in, io::di, io::uo)
    is det.

%-----------------------------------------------------------------------------%

    % bad_cmdline(ProgName, Msg, !IO):  prints a message like this:
    %
    %   <ProgName>: <Msg>
    %   <ProgName>: use --help for more information.
    %
    % <Msg> is split over multiple lines if necesary.
    % The exit status is also set to 1.
    %
:- pred bad_cmdline(string::in, string::in, io::di, io::uo) is det.

%-----------------------------------------------------------------------------%

    % Values of this type control what debugging output is printed.
    %
:- type debug_spec.

    % new_debug_spec(PPrintBefore, PPrintAfter, PPrintIgnore, DumpBefore,
    %   DumpAfter, StopBefore, StopAfter) = DebugSpec.
    %
    % Create a new debug spec.
    %
:- func new_debug_spec(list(string), list(string), list(string), list(string),
    list(string), list(string), list(string)) = debug_spec.

:- func debug_spec_get_pprint_before(debug_spec) = list(string).
:- func debug_spec_get_pprint_after(debug_spec) = list(string).
:- func debug_spec_get_pprint_ignore_file(debug_spec) = list(string).
:- func debug_spec_get_dump_before(debug_spec) = list(string).
:- func debug_spec_get_dump_after(debug_spec) = list(string).
:- func debug_spec_get_stop_before(debug_spec) = list(string).
:- func debug_spec_get_stop_after(debug_spec) = list(string).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- pred check_stage_option(option_table(Option)::in, list(string)::in,
    Option::in, list(string)::in, list(string)::out) is det.

%-----------------------------------------------------------------------------%
    
    % Do a stage, transforming Input (of type A) to Output (of type B),
    % possibly pretty-printing and/or dumping the IR before/after.
    % MaybeInput will be 'no' if --stop-before/--stop-after has applied
    % previously and so this phase should be skipped.  MaybeOutput will be
    % 'no' if MaybeInput was 'no' or --stop-before or --stop-after applied
    % to this stage.
    %
:- pred do_stage(string::in, list(string)::in,
        string::in, lang::in, debug_spec::in,
        stage(A, B)::in(stage),
        writer2(A)::in(writer2), writer(A)::in(writer),
        writer2(B)::in(writer2), writer(B)::in(writer),
        maybe(A)::in, maybe(B)::out, io::di, io::uo) is det.
    
    % Like do_stage, but lets the stage do I/O also.
    %
:- pred do_io_stage(string, list(string), string, lang, debug_spec,
    io_stage(A, B),
    writer2(A), writer(A),
    writer2(B), writer(B),
    maybe(A), maybe(B), io, io).
:-  mode do_io_stage(in, in, in, in, in,
    in(io_stage_det),
    in(writer2), in(writer),
    in(writer2), in(writer),
    in, out, di, uo) is det.
:-  mode do_io_stage(in, in, in, in, in,
    in(io_stage_cc_multi),
    in(writer2), in(writer),
    in(writer2), in(writer),
    in, out, di, uo) is cc_multi.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module zinc_error.
:- import_module zinc_pprint.

:- import_module string.

%-----------------------------------------------------------------------------%

init_frontend_globals(Verbose, VeryVerbose, Statistics, !IO) :- 
    % 
    % The `--verbose' and `--statistics' flags are both stored in mutables
    % that are attached to the I/O state so that they can be accessed from
    % anywhere in the program with them having to passed around everywhere. 
    % XXX we should change the types of the mutables to use the more
    %     meaningful names.
    set_very_verbose_flag(VeryVerbose, !IO),
    ( if (Verbose = yes ; VeryVerbose = yes)
    then set_verbose_flag(yes, !IO)
    else true
    ),
    set_statistics_flag(Statistics, !IO).

%-----------------------------------------------------------------------------%

bad_cmdline(ProgName, MsgStr, !IO) :-
    % A minor hack: we print it as two errors messages to avoid the "use
    % --help" part being indented.
    Errs1 = [zinc_error(non_specific, [words(MsgStr)])],
    HelpStr = "use --help for more information.",
    Errs2 = [zinc_error(non_specific, [words(HelpStr)])],
    pprint_zinc_errors(pp_lang_zinc(print_coercions), ProgName, Errs1, !IO),
    pprint_zinc_errors(pp_lang_zinc(print_coercions), ProgName, Errs2, !IO),
    get_error_exit_status(ErrorExitStatus, !IO),
    io.set_exit_status(ErrorExitStatus, !IO).

%-----------------------------------------------------------------------------%

:- type debug_spec
    --->    debug_spec(
                ds_pprint_before       :: list(string),
                ds_pprint_after        :: list(string),
                ds_pprint_ignore_file  :: list(string),
                ds_dump_before         :: list(string),
                ds_dump_after          :: list(string),
                ds_stop_before         :: list(string),
                ds_stop_after          :: list(string)
            ).

new_debug_spec(PPrintBefore, PPrintAfter, PPrintIgnoreFile,
        DumpBefore, DumpAfter, StopBefore, StopAfter) = DebugSpec :-
    DebugSpec = debug_spec(PPrintBefore, PPrintAfter, PPrintIgnoreFile,
        DumpBefore, DumpAfter, StopBefore, StopAfter).

debug_spec_get_pprint_before(D) = D ^ ds_pprint_before.
debug_spec_get_pprint_after(D)  = D ^ ds_pprint_after.
debug_spec_get_pprint_ignore_file(D) = D ^ ds_pprint_ignore_file.
debug_spec_get_dump_before(D) = D ^ ds_dump_before.
debug_spec_get_dump_after(D) = D ^ ds_dump_after.
debug_spec_get_stop_before(D) = D ^ ds_stop_before.
debug_spec_get_stop_after(D) = D ^ ds_stop_after.

%-----------------------------------------------------------------------------%

check_stage_option(OptionTable, StageNames, Option, !Errors) :-
    OptionStageNames = lookup_accumulating_option(OptionTable, Option),
    IsNotStageName = (pred(S::in) is semidet :-
        not list.member(S, StageNames)
    ),
    BadOptionStageNames = list.filter(IsNotStageName, OptionStageNames),
    (
        BadOptionStageNames = []
    ;     
        BadOptionStageNames = [BadOptionStageName],
        Error = "invalid stage name: " ++ BadOptionStageName,
        !:Errors = !.Errors ++ [Error]
    ;
        BadOptionStageNames = [_, _ | _],
        Error = "invalid stage name(s): " ++ BadOptionStageNames^string,
        !:Errors = !.Errors ++ [Error]
    ).

%-----------------------------------------------------------------------------%

do_stage(ProgramName, StageNames, StageName, Lang, DebugSpec, Stage,
        PrePPrinter, PreDumper, PostPPrinter, PostDumper, MaybeInput,
        MaybeOutput, !IO) :-
    IOStage = (
        pred(LangP::in, A::in, B::out, Errs::out, Warns::out,
            IO0::di, IO0::uo) is det :-
            Stage(LangP, A, B, Errs, Warns)
    ),
    do_io_stage(ProgramName, StageNames, StageName, Lang, DebugSpec,
        IOStage, PrePPrinter, PreDumper, PostPPrinter, PostDumper, MaybeInput,
        MaybeOutput, !IO).

do_io_stage(ProgramName, StageNames, StageName, Lang, DebugSpec, Stage,
        PrePPrinter, PreDumper, PostPPrinter, PostDumper, MaybeInput,
        MaybeOutput, !IO) :-
    % Check that the stage name is present in stage_names.
    ( if list.member(StageName, StageNames) then
        true
    else
        unexpected("stage name `" ++ StageName ++ 
            "' not present in the stage names;  please add it.")
    ),

    (   MaybeInput = yes(Input),
        trace [io(!TIO)] ( verbose("Doing stage: " ++ StageName, !TIO) ),
    
        DebugSpec = debug_spec(
            PPrintBefore,
            PPrintAfter,
            PPrintIgnoredFiles,
            DumpBefore,
            DumpAfter,
            StopBefore,
            StopAfter
        ), 

        % We put '%' in front of the banner so that it's a comment.  This
        % allows the output to be fed back into the system easily.
        WriteBanner = (pred(When::in, !.IO::di, !:IO::uo) is det :-
            io.write_string("% -- " ++ When ++ " "
                ++ StageName ++ " --------------\n", !IO)),

        ( if member(StageName, PPrintBefore) then
            WriteBanner("pretty-print before", !IO),% --pprint-before
            PrePPrinter(Input, PPrintIgnoredFiles, !IO)
        else
            true
        ),
        ( if member(StageName, DumpBefore) then
            WriteBanner("dump before", !IO),        % --dump-before
            PreDumper(Input, !IO)
        else
            true
        ),
        ( if member(StageName, StopBefore) then
            MaybeOutput = no                        % --stop-before
        else
            Stage(Lang, Input, Output, Errs, Warns, !IO), % execute the stage
            maybe_report_statistics(!IO),
            % If --very-verbose is enabled then print a message to indicate
            % that we have finished the stage, since there may be a lot of
            % intervening progress information.
            trace [io(!TIO)] ( very_verbose("Finished stage: " ++ StageName, !TIO) ),

            % Stop if this stage detected errors (but warnings alone don't
            % stop us), or --stop-after was specified for this stage.
            ( if Errs = [_ | _] then
                MaybeOutput = no,
                get_error_exit_status(ErrorExitStatus, !IO),
                io.set_exit_status(ErrorExitStatus, !IO)
            else if member(StageName, StopAfter) then
                MaybeOutput = no
            else
                MaybeOutput = yes(Output)
            ),
            % Print any errors or warnings from the stage.
            Msgs = Errs ++ Warns,
            (
                Msgs = []
            ;
                Msgs = [_ | _], 
                Lang = lang_minizinc,
                PPLang = pp_lang_minizinc(print_coercions),
                pprint_zinc_errors(PPLang, ProgramName, Msgs, !IO)
            ),
            ( if list.member(StageName, PPrintAfter) then
                WriteBanner("pretty-print after", !IO), % --pprint-after
                PostPPrinter(Output, PPrintIgnoredFiles, !IO)
            else
                true
            ),
            ( if list.member(StageName, DumpAfter) then
                WriteBanner("dump after", !IO),         % --dump-after
                PostDumper(Output, !IO)
            else
                true
            )
        )
    ;
        % --stop-before/after applied to an earlier stage, or an earlier stage
        % had errors.
        MaybeInput = no,    
        trace [io(!TIO)] ( verbose("Skipping stage: " ++ StageName, !TIO) ),
        MaybeOutput = no
    ).

%-----------------------------------------------------------------------------%
:- end_module zinc_frontend.
%-----------------------------------------------------------------------------%
