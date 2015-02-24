%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2006-2007 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
% compiler_common.m
% Nicholas Nethercote <njn@csse.unimelb.edu.au>
% Mon May 26 10:54:21 EST 2008
%
% Basic things used by multiple compiler modules.
%-----------------------------------------------------------------------------%

:- module compiler_common.
:- interface.

:- import_module bool.
:- import_module io.

:- import_module zinc_common.
:- import_module zinc_error.

%-----------------------------------------------------------------------------%

    % Logging for --verbose.  Best called using trace goals.
    %
:- pred verbose(string::in, io::di, io::uo) is det.

    % Sets the --verbose flag.  Only called at startup.
    %
:- pred set_verbose_flag(bool::in, io::di, io::uo) is det.

    % Get the --verbose flag.
    %
:- pred get_verbose_flag(bool::out, io::di, io::uo) is det.

%-----------------------------------------------------------------------------%

    % Logging for --very-verbose.  Best called using trace goals.
    %
:- pred very_verbose(string::in, io::di, io::uo) is det.

    % Sets the --very-verbose flag.  Only called at startup.
    %
:- pred set_very_verbose_flag(bool::in, io::di, io::uo) is det.

    % Get the --very-verbose flag.
    %
:- pred get_very_verbose_flag(bool::out, io::di, io::uo) is det.

%-----------------------------------------------------------------------------%
%
% Exit status for errors.
%
    % Set the exit status to set if an error is encoutered.
    % By default, this is 1.
    % (This value will be used by all procedures in the frontend that set
    % the exit status if an error occurs.)
    %
:- pred set_error_exit_status(int::in, io::di, io::uo) is det.

    % Get the exit status to set if an error is encountered.
    %
:- pred get_error_exit_status(int::out, io::di, io::uo) is det.

%-----------------------------------------------------------------------------%

:- pred set_statistics_flag(bool::in, io::di, io::uo) is det.

:- pred maybe_report_statistics(io::di, io::uo) is det.

%-----------------------------------------------------------------------------%

    % Compilation stages.  'io_stage' stages are those that perform I/O, eg.
    % parsing, code generation.  'stage' stages are those that do not, ie.
    % all others.
    %
:- type    stage(A, B)  == ( pred(lang, A, B, zinc_errors, zinc_warnings)).
:- type io_stage(A, B)
    == (pred(lang, A, B, zinc_errors, zinc_warnings, io, io)).
:- inst    stage        == ( pred(in, in, out, out, out)         is det ).
:- inst io_stage_det    == ( pred(in, in, out, out, out, di, uo) is det ).
:- inst io_stage_cc_multi
                        == ( pred(in, in, out, out, out, di, uo) is cc_multi ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module list.
:- import_module string.

%-----------------------------------------------------------------------------%

:- mutable(verbosity, bool, no, ground, [untrailed, attach_to_io_state]).

set_verbose_flag(Verbose, !IO) :-
    set_verbosity(Verbose, !IO).

get_verbose_flag(Verbose, !IO) :-
    get_verbosity(Verbose, !IO).

verbose(Msg, !IO) :-
    get_verbosity(Verbose, !IO),  
    (
        Verbose = yes,
        io.stderr_stream(Stderr, !IO),
        io.write_string(Stderr, "% " ++ Msg ++ "\n", !IO)
    ;
        Verbose = no
    ).

%-----------------------------------------------------------------------------%

:- mutable(very_verbosity, bool, no, ground, [untrailed, attach_to_io_state]).

set_very_verbose_flag(VeryVerbose, !IO) :-
    set_very_verbosity(VeryVerbose, !IO).

get_very_verbose_flag(VeryVerbose, !IO) :-
    get_very_verbosity(VeryVerbose, !IO).

very_verbose(Msg, !IO) :-
    get_very_verbosity(VeryVerbose, !IO),
    (
        VeryVerbose = yes,
        io.stderr_stream(Stderr, !IO),
        io.write_string(Stderr, "% " ++ Msg ++ "\n", !IO)
    ;
        VeryVerbose = no
    ).

%-----------------------------------------------------------------------------%

:- mutable(statistics, bool, no, ground, [untrailed, attach_to_io_state]).

set_statistics_flag(Statistics, !IO) :-
    set_statistics(Statistics, !IO).

maybe_report_statistics(!IO) :-
    get_statistics(Statistics, !IO),
    (
        Statistics = yes,
        io.report_stats(!IO)
    ;
        Statistics = no
    ).

%-----------------------------------------------------------------------------%

:- mutable(error_exit_status_var, int, 1, ground,
    [untrailed, attach_to_io_state]).

set_error_exit_status(ExitStatus, !IO) :-
    set_error_exit_status_var(ExitStatus, !IO).

get_error_exit_status(ExitStatus, !IO) :-
    get_error_exit_status_var(ExitStatus, !IO).

%-----------------------------------------------------------------------------%
:- end_module compiler_common.
%-----------------------------------------------------------------------------%
