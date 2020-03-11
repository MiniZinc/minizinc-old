%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2006-2012 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Authors: Nicholas Nethercote <njn@csse.unimelb.edu.au>
%          Ralph Becket <rafe@cs.mu.oz.au>
%
% The parsing stage for the Zinc/MiniZinc/FlatZinc front-end.  It doesn't
% contain most of the actual parsing code, however;  that's in
% zinc_parser.m.
%
% Nb: 'parse.m' would be a better name for this module, but
% g12/cadmium/src/parse.m has that name, and reusing it could cause problems.
%
%-----------------------------------------------------------------------------%

:- module parse_stage.
:- interface.

%-----------------------------------------------------------------------------%

:- import_module compiler_common.
:- import_module zinc_ast.

:- import_module bool.
:- import_module list.

%-----------------------------------------------------------------------------%

:- type allow_includes
    --->    full_includes
    ;       restricted_includes
    ;       no_includes.

    % Return full_includes or restricted_includes; the argument is 'yes' if
    % includes are restricted.
    %
:- func allow_includes(bool) = allow_includes.

%-----------------------------------------------------------------------------%

:- type zinc_input
    --->    zi_model_file(string)
    ;       zi_data_file(string)
    ;       zi_cmdline(string).

:- type zinc_inputs == list(zinc_input).

:- func zinc_input_to_string(zinc_input) = string.

%-----------------------------------------------------------------------------%

:- pred parse_zinc_model(allow_includes::in, zinc_inputs::in, list(string)::in)
    : io_stage(ast, ast) `with_inst` io_stage_det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module zinc_common.
:- import_module zinc_error.
:- import_module zinc_parser.

:- import_module builtin.
:- import_module dir.
:- import_module io.
:- import_module maybe.
:- import_module pair.
:- import_module string.

%-----------------------------------------------------------------------------%
% Recursive file parsing
%-----------------------------------------------------------------------------%

% Note that here we distinguish between "file names" (eg. "stdlib.zinc"),
% "search dirs" (eg. "~/foo/bar/") and "file paths" (eg.
% "~/foo/bar/stdlib.zinc").

parse_zinc_model(AllowIncludes, Inputs, SearchDirs, Lang, !Items,
        Errs, Warns, !IO) :-
    else_unexpected(unify(!.Items, []),
        "parse_zinc_model: given non-empty AST"),
    P = parse_zinc_input(AllowIncludes, Lang, SearchDirs, no),
    list.foldl4(P, Inputs, !Items, [], _FilesParsed, [], Errs, !IO),
    Warns = [].         % This stage doesn't produce any warnings.

:- pred parse_zinc_input(allow_includes::in, lang::in, list(string)::in,
    maybe(pair(string, int))::in, zinc_input::in, items::in,
    items::out, list(string)::in, list(string)::out,
    zinc_errors::in, zinc_errors::out, io::di, io::uo) is det.

parse_zinc_input(AllowIncludes, Lang, SearchDirs, MaybeIncludeLocn, Input,
        !Items, !FilePathsRead, !Errs, !IO) :-
    (
        (
            Input = zi_model_file(FileName),
            Extra = "(model file)",
            IsDataFile = no
        ;
            Input = zi_data_file(FileName),
            Extra = "(data file)",
            IsDataFile = yes
        ),
        trace [io(!TIO)] (
            verbose("  Starting " ++ FileName ++ " " ++ Extra, !TIO)
        ),
        parse_zinc_file(AllowIncludes, Lang, SearchDirs, MaybeIncludeLocn,
            FileName, IsDataFile, !Items, !FilePathsRead, !Errs, !IO)
    ;
        Input = zi_cmdline(CmdLineData),
        trace [io(!TIO)] (
            verbose("  Parsing command line data", !TIO)
        ),
        parse_zinc_string(Lang, CmdLineData, !Items, !Errs, !IO)
    ).

:- pred parse_zinc_file(allow_includes::in, lang::in, list(string)::in,
    maybe(pair(string, int))::in, string::in, bool::in,
    items::in, items::out, list(string)::in, list(string)::out,
    zinc_errors::in, zinc_errors::out, io::di, io::uo) is det.

parse_zinc_file(AllowIncludes, Lang, SearchDirs, MaybeIncludeLocn, FileName,
        IsDataFile, !Items, !FilePathsRead, !Errs, !IO) :-
    % If the filename is absolute, we ignore the search directories and just
    % use the filename directly.  Otherwise we search for a matching file in
    % the search dirs.
    ( if path_name_is_absolute(FileName) then
        MaybeFilePath = yes(FileName)
      else
        find_file_in_search_dirs(FileName, SearchDirs, MaybeFilePath, !IO)
    ),

    (   MaybeFilePath = yes(FilePath),
        ( if member(FilePath, !.FilePathsRead) then
            % Done it already, skip
            trace [io(!TIO)] ( verbose("    Skipping " ++ FilePath ++
                " (already done)", !TIO) )
          else
            trace [io(!TIO)] ( verbose("    Reading " ++ FilePath, !TIO) ),
            get_file_text(FilePath, MaybePartialRes, !IO),
            !:FilePathsRead = [FilePath | !.FilePathsRead],
            (
                MaybePartialRes = ok(FileText),
                trace [io(!TIO)] (
                    verbose("    Parsing " ++ FilePath, !TIO)
                ),
                model(Lang, FileName, 1, IsDataFile, FileText, FileItems,
                    Includes, !Errs),
                ( if
                    AllowIncludes = no_includes
                then
                    !:Items = !.Items ++ FileItems
                else
                    parse_zinc_files_from_includes(AllowIncludes, Lang,
                        FileName, SearchDirs, Includes, ItemsFromIncludes,
                        !FilePathsRead, !Errs, !IO),
                    !:Items = !.Items ++ FileItems ++ ItemsFromIncludes
                )
            ;
                MaybePartialRes = error(_PartialFileText, IOErr),
                trace [io(!TIO)] (
                    verbose("    Could not read " ++ FilePath, !TIO)
                ),
                bad_file(FilePath, MaybeIncludeLocn, io.error_message(IOErr),
                    !Errs)
            )
        )
    ;
        MaybeFilePath = no,
        Msg = "cannot open input file: No such file",
        bad_file(FileName, MaybeIncludeLocn, Msg, !Errs)
    ).

    % This scans the items of a file and reinvokes the parser on any files
    % mentioned in include items.
:- pred parse_zinc_files_from_includes(allow_includes::in, lang::in,
    string::in, list(string)::in, list(include)::in, ast::out,
    list(string)::in, list(string)::out, zinc_errors::in, zinc_errors::out,
    io::di, io::uo) is det.

parse_zinc_files_from_includes(_, _, _, _, [], [], !FilesRead, !Errs, !IO).
parse_zinc_files_from_includes(AllowIncludes, Lang, FileName, SearchDirs,
        [Include | Includes], Items1 ++ Items2, !FilePathsRead, !Errs, !IO) :-
    % Parse the file mentioned in the include.
    Include = include(IncLineNum, IncludedFileName),
    trace [io(!TIO)] (
        verbose("    " ++ FileName ++ " includes " ++ IncludedFileName, !TIO)
    ),
    MaybeIncludeLocn = yes(FileName - IncLineNum),
    ( if
        AllowIncludes = restricted_includes,
        ( if path_name_is_absolute(IncludedFileName) then
            Msg = "cannot use absolute path in include"
        else
            P = ( pred(C::in) is semidet :- is_directory_separator(C) ),
            member("..", words_separator(P, IncludedFileName)),
            Msg = "cannot use \'..\' in include"
        )
    then
        bad_file(FileName, MaybeIncludeLocn, Msg, !Errs),
        Items1 = []
    else
        parse_zinc_input(AllowIncludes, Lang, SearchDirs, MaybeIncludeLocn,
            zi_model_file(IncludedFileName), [], Items1, !FilePathsRead,
            !Errs, !IO)
    ),
    parse_zinc_files_from_includes(AllowIncludes, Lang, FileName,
        SearchDirs, Includes, Items2, !FilePathsRead, !Errs, !IO).

:- pred parse_zinc_string(lang::in, string::in, items::in, items::out,
    zinc_errors::in, zinc_errors::out, io::di, io::uo) is det.

parse_zinc_string(Lang, CmdLineData, !Items, !Errs, !IO) :-
    model(Lang, "(command line)", 1, /*IsDataFile*/yes, CmdLineData,
        CmdLineItems, _Includes, !Errs),
    %expect(unify(Includes, []),
    !:Items = !.Items ++ CmdLineItems.

%-----------------------------------------------------------------------------%

:- pred find_file_in_search_dirs(string::in, list(string)::in,
    maybe(string)::out, io::di, io::uo) is det.

find_file_in_search_dirs(_FileName, [], no, !IO).
find_file_in_search_dirs(FileName, [Dir | Dirs], MaybeFilePath, !IO) :-
    FilePath = Dir / FileName,
    io.file_type(/*FollowSymLinks*/yes, FilePath, Res, !IO),
    ( if Res = ok(_) then
        trace [io(!TIO)]
            ( verbose("    Searching in '" ++ Dir ++ "' ... found", !TIO) ),
        MaybeFilePath = yes(FilePath)
      else
        % No match in that directory, keep looking.
        trace [io(!TIO)]
            ( verbose("    Searching in '" ++ Dir ++ "' ... failed", !TIO) ),
        find_file_in_search_dirs(FileName, Dirs, MaybeFilePath, !IO)
    ).

%-----------------------------------------------------------------------------%

    % Get the text of a file.  Returns part of the file or the empty string if
    % there's an I/O problem.
    %
:- pred get_file_text(string::in, io.maybe_partial_res(string)::out,
    io::di, io::uo) is det.

get_file_text(FilePath, MaybePartialRes, !IO) :-
    io.open_input(FilePath, OpenResult, !IO),
    (
        OpenResult = ok(InStrm),
        io.read_file_as_string(InStrm, MaybePartialRes, !IO),
        io.close_input(InStrm, !IO)
    ;
        OpenResult = error(IOErr),
        MaybePartialRes = error("", IOErr)
    ).

%-----------------------------------------------------------------------------%

:- pred bad_file(string::in, maybe(pair(string, int))::in, string::in,
    zinc_errors::in, zinc_errors::out) is det.

bad_file(FilePath, MaybeIncludeLocn, MsgStr, Errs, [Err | Errs]) :-
    (   % The bad file was included from within a Zinc source file -- give
        % the location of the include item in the error.
        MaybeIncludeLocn = yes(FileName - LineNum),
        ErrLocn = file_line(FileName, LineNum)
    ;
        % The bad file was included via the command line.
        MaybeIncludeLocn = no,
        ErrLocn = non_specific
    ),
    Err = zinc_error(ErrLocn, [words(FilePath ++ ": " ++ MsgStr)]).

%-----------------------------------------------------------------------------%

allow_includes(yes) = restricted_includes.
allow_includes(no) = full_includes.

%-----------------------------------------------------------------------------%

zinc_input_to_string(zi_model_file(F)) = F.
zinc_input_to_string(zi_data_file(F)) = F.
zinc_input_to_string(zi_cmdline(_)) = "(command line)".

%-----------------------------------------------------------------------------%
:- end_module parse_stage.
%-----------------------------------------------------------------------------%
