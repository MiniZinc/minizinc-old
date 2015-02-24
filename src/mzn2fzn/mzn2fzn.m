%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et
%-----------------------------------------------------------------------------%
% Copyright (C) 2007-2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Authors:
% Nicholas Nethercote   <njn@csse.unimelb.edu.au>
% Ralph Becket          <rafe@csse.unimelb.edua.u>
% Julien Fischer        <juliensf@csse.unimelb.edu.au>
%
% Top-level control for the MiniZinc-to-FlatZinc convertor.
%
%-----------------------------------------------------------------------------%

:- module mzn2fzn.
:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is cc_multi.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module convert_to_tmzn.
:- import_module error_util.
:- import_module errors.
:- import_module flatten.
:- import_module flatten.env.
:- import_module flatten.item.
:- import_module flatten.output.
:- import_module hr.
:- import_module hr.info.
:- import_module hr.item.
:- import_module opt.
:- import_module output_common.
:- import_module output_tfzn.
:- import_module tfzn_ast.
:- import_module tmzn_ast.
:- import_module translate.
:- import_module translate.info.
:- import_module translate.item.
:- import_module translate.opt.
:- import_module translate.vars.
:- import_module types.

:- import_module compiler_common.
:- import_module minizinc_conf.
:- import_module parse_stage.
:- import_module types_and_insts.
:- import_module zinc_ast.
:- import_module zinc_common.
:- import_module zinc_error.
:- import_module zinc_frontend.
:- import_module zinc_frontend2.
:- import_module zinc_pprint.

:- import_module bool.
:- import_module char.
:- import_module counter.
:- import_module dir.
:- import_module exception.
:- import_module getopt_io.
:- import_module list.
:- import_module map.
:- import_module maybe.
:- import_module set.
:- import_module string.
:- import_module unit.
:- import_module univ.

%-----------------------------------------------------------------------------%

main(!IO) :-
    try_io(main_2, MainResult, !IO),
    (
        MainResult = succeeded(_)
    ;
        MainResult = exception(Excp),
        ( if univ_to_type(Excp, IO_Error) then
            handle_io_error(mzn2fzn_program, IO_Error, !IO)
          else if univ_to_type(Excp, SoftwareError) then
            handle_internal_error(mzn2fzn_program, SoftwareError, !IO)
          else
            rethrow(MainResult)
        )
    ).

:- pred main_2(unit::out, io::di, io::uo) is det.

main_2(unit, !IO) :-
    io.command_line_arguments(Args, !IO),
    OptionOps = option_ops_multi(
        mzn2fzn_short_option,
        mzn2fzn_long_option,
        (pred(O::out, D::out) is multi :- mzn2fzn_option_defaults(O, D)),
        mzn2fzn_special_handler
    ),
    process_options(OptionOps, Args, NonOptionArgs, Result, !IO),
    (
        Result = error(Msg),
        bad_cmdline("mzn2fzn", Msg, !IO)
    ;
        Result = ok(OptionTable),

        % Set up the global state for the frontend.
        %
        lookup_bool_option(OptionTable, verbose, Verbose),
        lookup_bool_option(OptionTable, very_verbose, VeryVerbose),
	    lookup_bool_option(OptionTable, statistics, Statistics),
	    init_frontend_globals(Verbose, VeryVerbose, Statistics, !IO),

        % 1. Look for --version/--help, print message and stop if present.
        % 2. Look for exactly one model file.  Complain and stop if not
        %    present or more than one present.
        % 3. Check remaining options.  Complain and stop if something is
        %    wrong.  (Nb: 'process_options' above has already done a lot of
        %    checking, eg. for unknown option names.  This checking is
        %    checking for invalid combinations, option arguments, etc.)
        % 4. Compile the model.
        %
        % Nb: --version and --help go to stdout, errors go to stderr.
        %
        ( if lookup_bool_option(OptionTable, version, yes) then
            io.write_string(mzn2fzn_version, !IO)
          else if lookup_bool_option(OptionTable, help, yes) then
            io.write_string(mzn2fzn_usage, !IO)
          else
            list.filter(is_dzn, NonOptionArgs, DznArgs, NonDznArgs),
            (
                NonDznArgs = [],
                bad_cmdline("mzn2fzn", "no model file specified", !IO)
            ;
                NonDznArgs = [ModelFileName],
                check_mzn2fzn_options(OptionTable, ModelFileName,
                    Checking, FznOutputDest, OznOutputDest, [], OptionErrors),
                (
                    % Error in options found by us.
                    OptionErrors = [FirstOptionErrorMsg | _],
                    bad_cmdline("mzn2fzn", FirstOptionErrorMsg, !IO)
                ;
                    % We have a model file, we have acceptable options.
                    OptionErrors = [],

                    % Work out what directories we should search for files
                    % referred to by include items.  Report as errors any
                    % directories that don't exist.
                    %
                    setup_mzn2fzn_search_dirs(OptionTable, SearchDirs,
                        DirErrors, !IO),

                    (
                        DirErrors = [FirstDirError | _],
                        bad_cmdline("mzn2fzn", FirstDirError, !IO)
                    ;
                        DirErrors = [],
                        do_mzn2fzn_stages(FznOutputDest, OznOutputDest,
                            Checking, SearchDirs, ModelFileName, DznArgs,
                            OptionTable, !IO)
                    )
                )
            ;
                NonDznArgs = [_, _ | _],
                bad_cmdline("mzn2fzn", "more than one model file specified",
                    !IO)
            )
        )
    ).

:- pred is_dzn(string::in) is semidet.

is_dzn(FileName) :-
    string.suffix(FileName, ".dzn").

%-----------------------------------------------------------------------------%
%
% Command-line options.
%

:- type mzn2fzn_option
    % Normal options
    --->    help
    ;       version
    ;       verbose
    ;       very_verbose
    ;       data
    ;       search_dir
    ;       model_check_only
    ;       instance_check_only
    ;       flags_file
    ;       stdlib_dir
    ;       globals_dir
    ;       cmdline_data
    ;       force_standard_globals
    ;       restrict_includes

    % Optimisation options
    ;       optimise_fzn
    ;       half_reify
    ;       translate

    % Output optiopns
    ;       output_ozn
            % Should we output a .ozn file?

    ;       output_base
    ;       output_fzn_to_file
    ;       output_ozn_to_file
    ;       output_fzn_to_stdout
    ;       output_ozn_to_stdout
    ;       informal_syntax

    % Debugging options
    ;       statistics
    ;       pprint_before
    ;       pprint_after
    ;       pprint_ignore_file
    ;       dump_before
    ;       dump_after
    ;       stop_before
    ;       stop_after
    ;       ignore_stdlib
    .

    % The valid single-character options.
    %
:- pred mzn2fzn_short_option(char::in, mzn2fzn_option::out) is semidet.

mzn2fzn_short_option('d', data).
mzn2fzn_short_option('e', model_check_only).
mzn2fzn_short_option('h', help).
mzn2fzn_short_option('H', half_reify).
mzn2fzn_short_option('o', output_fzn_to_file).
mzn2fzn_short_option('v', verbose).
mzn2fzn_short_option('G', globals_dir).
mzn2fzn_short_option('I', search_dir).
mzn2fzn_short_option('i', informal_syntax).
mzn2fzn_short_option('S', statistics).
mzn2fzn_short_option('O', output_ozn).
mzn2fzn_short_option('D', cmdline_data).
mzn2fzn_short_option('V', very_verbose).

    % The valid long options.
    %
:- pred mzn2fzn_long_option(string::in, mzn2fzn_option::out) is semidet.

mzn2fzn_long_option("help",                 help).
mzn2fzn_long_option("version",              version).
mzn2fzn_long_option("verbose",              verbose).
mzn2fzn_long_option("very-verbose",         very_verbose).
mzn2fzn_long_option("data",                 data).
mzn2fzn_long_option("search-dir",           search_dir).
mzn2fzn_long_option("model-check-only",     model_check_only).
mzn2fzn_long_option("instance-check-only",  instance_check_only).
mzn2fzn_long_option("flags-file",           flags_file).
mzn2fzn_long_option("stdlib-dir",           stdlib_dir).
mzn2fzn_long_option("cmdline-data",         cmdline_data).
% The following synonyms for --stdlib-dir are for compatibility
% with zinc and cadmap.
mzn2fzn_long_option("mzn-stdlib-dir",       stdlib_dir).
mzn2fzn_long_option("minizinc-stdlib-dir",  stdlib_dir).
mzn2fzn_long_option("globals-dir",          globals_dir).
mzn2fzn_long_option("mzn-gobals-dir",       globals_dir).
mzn2fzn_long_option("minizinc-globals-dir", globals_dir).
mzn2fzn_long_option("force-standard-globals",     force_standard_globals).
mzn2fzn_long_option("std-globals",                force_standard_globals).
mzn2fzn_long_option("restrict-includes",    restrict_includes).

mzn2fzn_long_option("optimise",             optimise_fzn).
mzn2fzn_long_option("optimize",             optimise_fzn).
mzn2fzn_long_option("half-reify",           half_reify).
mzn2fzn_long_option("translate",            translate).
mzn2fzn_long_option("tr",                   translate).     % for debug

mzn2fzn_long_option("output-ozn",           output_ozn).
mzn2fzn_long_option("output-base",          output_base).
mzn2fzn_long_option("output-to-file",       output_fzn_to_file).
mzn2fzn_long_option("output-fzn-to-file",   output_fzn_to_file).
mzn2fzn_long_option("output-ozn-to-file",   output_ozn_to_file).
mzn2fzn_long_option("output-to-stdout",     output_fzn_to_stdout).
mzn2fzn_long_option("output-fzn-to-stdout", output_fzn_to_stdout).
mzn2fzn_long_option("output-ozn-to-stdout", output_ozn_to_stdout).
mzn2fzn_long_option("informal-syntax",      informal_syntax).

mzn2fzn_long_option("statistics",           statistics).
mzn2fzn_long_option("pprint-before",        pprint_before).
mzn2fzn_long_option("pprint-after",         pprint_after).
mzn2fzn_long_option("pprint-ignore-file",   pprint_ignore_file).
mzn2fzn_long_option("dump-before",          dump_before).
mzn2fzn_long_option("dump-after",           dump_after).
mzn2fzn_long_option("stop-before",          stop_before).
mzn2fzn_long_option("stop-after",           stop_after).
mzn2fzn_long_option("ignore-stdlib",        ignore_stdlib).

    % Nondeterministically returns all the options with their corresponding
    % types and default values.
    % (The second mode is used to check that we cover all options.)
    %
:- pred mzn2fzn_option_defaults(mzn2fzn_option, option_data).
:- mode mzn2fzn_option_defaults(out, out) is multi.
:- mode mzn2fzn_option_defaults(in, out) is det.

mzn2fzn_option_defaults(help,               bool(no)).
mzn2fzn_option_defaults(version,            bool(no)).
mzn2fzn_option_defaults(verbose,            bool(no)).
mzn2fzn_option_defaults(very_verbose,       bool(no)).
mzn2fzn_option_defaults(data,               accumulating([])).
mzn2fzn_option_defaults(search_dir,         accumulating([])).
mzn2fzn_option_defaults(model_check_only,   bool(no)).
mzn2fzn_option_defaults(instance_check_only,bool(no)).
mzn2fzn_option_defaults(flags_file,         file_special).
mzn2fzn_option_defaults(stdlib_dir,         string("")).
mzn2fzn_option_defaults(cmdline_data,       accumulating([])).
mzn2fzn_option_defaults(globals_dir,        accumulating([])).
mzn2fzn_option_defaults(force_standard_globals,     special).
mzn2fzn_option_defaults(restrict_includes,  bool(no)).

mzn2fzn_option_defaults(optimise_fzn,       bool(yes)).
mzn2fzn_option_defaults(half_reify,         bool(no)).
mzn2fzn_option_defaults(translate,          bool(no)).

mzn2fzn_option_defaults(output_ozn,           bool(yes)).
mzn2fzn_option_defaults(output_base,          maybe_string(no)).
mzn2fzn_option_defaults(output_fzn_to_file,   maybe_string(no)).
mzn2fzn_option_defaults(output_ozn_to_file,   maybe_string(no)).
mzn2fzn_option_defaults(output_fzn_to_stdout, bool(no)).
mzn2fzn_option_defaults(output_ozn_to_stdout, bool(no)).
mzn2fzn_option_defaults(informal_syntax,      bool(no)).

mzn2fzn_option_defaults(statistics,         bool(no)).
mzn2fzn_option_defaults(pprint_before,      accumulating([])).
mzn2fzn_option_defaults(pprint_after,       accumulating([])).
mzn2fzn_option_defaults(pprint_ignore_file, accumulating([])).
mzn2fzn_option_defaults(dump_before,        accumulating([])).
mzn2fzn_option_defaults(dump_after,         accumulating([])).
mzn2fzn_option_defaults(stop_before,        accumulating([])).
mzn2fzn_option_defaults(stop_after,         accumulating([])).
mzn2fzn_option_defaults(ignore_stdlib,      bool(no)).

:- pred mzn2fzn_special_handler(mzn2fzn_option::in, special_data::in,
    option_table(mzn2fzn_option)::in, maybe_option_table(mzn2fzn_option)::out)
    is semidet.

mzn2fzn_special_handler(force_standard_globals, none, !.OptionTable,
        ok(!:OptionTable)) :-
    map.set(globals_dir, accumulating([]), !OptionTable).

%-----------------------------------------------------------------------------%

:- pred check_mzn2fzn_options(option_table(mzn2fzn_option)::in, string::in,
    checking::out, output_destination::out, output_destination::out,
    list(string)::in, list(string)::out) is det.

check_mzn2fzn_options(OptionTable, ModelFileName, Checking, FznOutputDest,
        OznOutputDest, !Errors) :-
    % Look at the model's file extension.
    % If it is not `.mzn' then emit an error.
    ( if
        string.remove_suffix(ModelFileName, ".mzn", ModelFileNameBase),
        ModelFileNameBase \= ""     % Don't allow just ".mzn" as a name
      then
        choose_output_destination(OptionTable, ModelFileNameBase,
            FznOutputDest, OznOutputDest, !Errors)
      else
        ModelExtError = "file name must have the form `<file>.mzn'.",
        !:Errors = !.Errors ++ [ModelExtError],
        FznOutputDest = output_to_stdout, % Dummy value -- not used.
        OznOutputDest = output_to_stdout  % Dummy value -- not used.
    ),

    % Model-checking or instance-checking?
    % Default is instance-checking.
    lookup_bool_option(OptionTable, model_check_only,    Model),
    lookup_bool_option(OptionTable, instance_check_only, Instance),
    (
        Model = no,
        Checking = instance_checking
    ;
        Model = yes,
        (
            Instance = no,
            Checking = model_checking
        ;
            Instance = yes,
            Checking = instance_checking,   % dummy value -- not used
            Error = "please choose one of " ++
                "--model-check-only and --instance-check-only",
            !:Errors = !.Errors ++ [Error]
        )
    ),

    % Check that the -G option is not given an argument that specifies
    % an absolute path.
    lookup_accumulating_option(OptionTable, globals_dir, GlobalsDirs),
    ( if list.all_false(dir.path_name_is_absolute, GlobalsDirs) then
        true
      else
        PathError = "argument to option --minizinc-globals-dir" ++
            " cannot be an absolute path",
        !:Errors  = !.Errors ++ [PathError]
    ),

    % Check stage options.
    %
    StageOptions = [
        dump_before,
        dump_after,
        pprint_before,
        pprint_after,
        stop_before,
        stop_after
    ],
    foldl(check_stage_option(OptionTable, mzn2fzn_stage_names), StageOptions,
        !Errors).

:- pred choose_output_destination(option_table(mzn2fzn_option)::in, string::in,
    output_destination::out, output_destination::out,
    list(string)::in, list(string)::out) is det.

choose_output_destination(OptionTable, ModelFileNameBase, FznOutputDest,
        OznOutputDest, !Errors) :-
    ( if dir.basename(ModelFileNameBase, UnqualModelFileNameBase) then

        lookup_maybe_string_option(OptionTable, output_base,
            MaybeUserOutputBase),
        lookup_maybe_string_option(OptionTable, output_fzn_to_file,
            MaybeUserFznFile),
        lookup_maybe_string_option(OptionTable, output_ozn_to_file,
            MaybeUserOznFile),
        lookup_bool_option(OptionTable, output_fzn_to_stdout,
            FznToStdout),
        lookup_bool_option(OptionTable, output_ozn_to_stdout,
            OznToStdout),
        (
            MaybeUserOutputBase = yes(UserOutputBase),
            ( if UserOutputBase = "" then
                BadUserBaseErr = "the value of the --output-base option " ++
                    "may not be the empty string",
                !:Errors = !.Errors ++ [BadUserBaseErr],
                FznOutputDest = output_to_stdout,   % Dummy value -- not used.
                OznOutputDest = output_to_stdout    % Dummy value -- not used.
              else
                FznOutputDest = output_to_file(UserOutputBase ++ ".fzn"),
                OznOutputDest = output_to_file(UserOutputBase ++ ".ozn"),

                % Check for conflicts with other output options.
                %
                (
                    MaybeUserFznFile = yes(_),
                    add_conflicting_options_error("--output-base",
                        "--output-fzn-to-file", !Errors)
                ;
                    MaybeUserFznFile = no
                ),
                (
                    MaybeUserOznFile = yes(_),
                    add_conflicting_options_error("--output-base",
                        "output-ozn-to-file", !Errors)
                ;
                    MaybeUserOznFile = no
                ),
                (
                    FznToStdout = yes,
                    add_conflicting_options_error("--output-base",
                        "--output-fzn-to-stdout", !Errors)
                ;
                    FznToStdout = no
                ),
                (
                    OznToStdout = yes,
                    add_conflicting_options_error("--output-base",
                        "--output-ozn-to-stdout", !Errors)
                ;
                    OznToStdout = no
                )
            )
        ;
            MaybeUserOutputBase = no,

            % Determine the output destination for the generated FlatZinc.
            %
            (
                MaybeUserFznFile = yes(UserFznFile),
                ( if UserFznFile = "" then
                    BadFznFileMsg = "the value of the --output-fzn-to-file " ++
                        "option may not be the empty string",
                    !:Errors = !.Errors ++ [BadFznFileMsg],
                    FznOutputDest = output_to_stdout % Dummy value -- not used.
                  else
                    FznOutputDest = output_to_file(UserFznFile),
                    (
                        FznToStdout = yes,
                        add_conflicting_options_error("--output-fzn-to-file",
                            "--output-fzn-to-stdout", !Errors)
                    ;
                        FznToStdout = no
                    )
                )
            ;
                MaybeUserFznFile = no,
                (
                    FznToStdout = yes,
                    FznOutputDest = output_to_stdout
                ;
                    FznToStdout = no,
                    FznFileName = UnqualModelFileNameBase ++ ".fzn",
                    FznOutputDest = output_to_file(FznFileName)
                )
            ),

            % Determine the output destination for output specification.
            %
            (
                MaybeUserOznFile = yes(UserOznFile),
                ( if UserOznFile = "" then
                    BadOznFileMsg = "the value of the --output-ozn-to-file " ++
                        "option may not be the empty string",
                    !:Errors = !.Errors ++ [BadOznFileMsg],
                    OznOutputDest = output_to_stdout  % Dummy value -- not used.
                  else
                    OznOutputDest = output_to_file(UserOznFile),
                    (
                        OznToStdout = yes,
                        add_conflicting_options_error("--output-ozn-to-file",
                            "--output-ozn-to-stdout", !Errors)
                    ;
                        OznToStdout = no
                    )
                )
            ;
                MaybeUserOznFile = no,
                (
                    OznToStdout = yes,
                    OznOutputDest = output_to_stdout
                ;
                    OznToStdout = no,
                    OznFileName = UnqualModelFileNameBase ++ ".ozn",
                    OznOutputDest = output_to_file(OznFileName)
                )
            )
        )

      else
        BadDirError = "bad directory for input file",
        !:Errors = !.Errors ++ [BadDirError],
        FznOutputDest = output_to_stdout,   % Dummy value -- not used.
        OznOutputDest = output_to_stdout    % Dummy value -- not used.
    ).

    % NOTE: if you add or remove stages please update the mzn2fzn man
    % page in g12/zinc/man/mzn2fzn.1.in.
    %
:- func mzn2fzn_stage_names = list(string).

mzn2fzn_stage_names = [
    "parsing",
    "assignment-elimination",
    "top-sorting",
    "structure-checking",
    "type-inst-checking",
    "flattening",
    "formatting-output"
].

:- pred add_conflicting_options_error(string::in, string::in,
    list(string)::in, list(string)::out) is det.

add_conflicting_options_error(OptA, OptB, !Errors) :-
    Msg = "only of " ++ OptA ++ " and " ++ OptB ++ " may be specified",
    !:Errors = !.Errors ++ [Msg].

%-----------------------------------------------------------------------------%

:- pred do_mzn2fzn_stages(output_destination::in, output_destination::in,
    checking::in, list(string)::in, string::in, list(string)::in,
    option_table(mzn2fzn_option)::in, io::di, io::uo) is det.

do_mzn2fzn_stages(FznOutputDest, OznOutputDest, Checking, SearchDirs,
        ModelFileName, ArgDataFiles, OptionTable, !IO) :-
    % We mark the data files as being data files.
    lookup_accumulating_option(OptionTable, data, OptDataFiles),
    DataFileNames = ArgDataFiles ++ OptDataFiles,
    DataFileInputs = list.map((func(F) = zi_data_file(F)), DataFileNames),

    some [!Inputs] (
        % Add the standard library, if requested, to the list of items.
        % It, and the model file, are marked as not being data files.
        lookup_bool_option(OptionTable, ignore_stdlib, IgnoreStdlib),
        !:Inputs = [zi_model_file(ModelFileName) | DataFileInputs],
        (
            IgnoreStdlib = no,
            !:Inputs = [zi_model_file("stdlib.mzn") | !.Inputs]
        ;
            IgnoreStdlib = yes
        ),

        lookup_accumulating_option(OptionTable, cmdline_data, CmdLineData0),
        (
            CmdLineData0 = []
        ;
            CmdLineData0 = [_ | _],
            CmdLineData = string.append_list(CmdLineData0),
            !:Inputs = [zi_cmdline(CmdLineData) | !.Inputs]
        ),
        AllInputs = !.Inputs
    ),

    % Open the "output MiniZinc" model file if the user has specified
    % output_ozn.
    lookup_bool_option(OptionTable, output_ozn, OutputOzn),
    (
        OutputOzn = no,
        MaybeOznOutputDest = no
    ;
        OutputOzn = yes,
        MaybeOznOutputDest = yes(OznOutputDest)
    ),

    % Optimise the FlatZinc model unless requested not to.
    lookup_bool_option(OptionTable, optimise_fzn, OptFZN),
    (
        OptFZN = no,
        OptimiseFlatZinc = dont_optimise_flatzinc
    ;
        OptFZN = yes,
        OptimiseFlatZinc = optimise_flatzinc
    ),

    % Do we use the half-reification approach to flatten constraints or not?
    lookup_bool_option(OptionTable, half_reify, HalfReify0),
    lookup_bool_option(OptionTable, translate, Translate),
    (
        Translate = yes,
        HalfReify = yes
    ;
        Translate = no,
        HalfReify = HalfReify0
    ),
    (
        HalfReify = no,
        % Ignore Translate, which only selects between the hr.*.m and the
        % translate.*.m implementations of half-reification.
        Approach = old_flattening
    ;
        HalfReify = yes,
        (
            Translate = no,
            Approach = half_reification
        ;
            Translate = yes,
            Approach = translate_half_reification
        )
    ),

    trace [io(!TIO)] (
        AllInputFiles = list.map(zinc_input_to_string, AllInputs),
        verbose("Processing files: " ++ AllInputFiles ^ string, !TIO)
    ),

    DebugSpec = make_mzn2fzn_debug_spec(OptionTable),
    lookup_bool_option(OptionTable, restrict_includes, RestrictIncludes),
    AllowIncludes = allow_includes(RestrictIncludes),

    % Parsing.  Nb: the pprint-before function will print nothing, because the
    % AST is empty at that point.
    EmptyAST = [],
    do_io_stage(mzn2fzn_program, mzn2fzn_stage_names,
        "parsing", lang_minizinc, DebugSpec,
        parse_zinc_model(AllowIncludes, AllInputs, SearchDirs),
        pprint_ast(pp_lang_minizinc(print_coercions)), io.write,
        pprint_ast(pp_lang_minizinc(print_coercions)), dump_ast,
        yes(EmptyAST), MaybeItems1, !IO),

    PreConversionStageNameSuffix = "",
    do_analysis_stages(mzn2fzn_control, mzn2fzn_program, mzn2fzn_stage_names,
        lang_minizinc, Checking, PreConversionStageNameSuffix, DebugSpec,
        MaybeItems1, MaybeItemsAndSymTbl2, !IO),

    % Finished checking code.  Stop if either --model-check-only or
    % --instance-check-only is specified.

    ( if
        MaybeItemsAndSymTbl2 = yes({Items2, _SymTbl2}),
        lookup_bool_option(OptionTable, instance_check_only, no),
        lookup_bool_option(OptionTable, model_check_only,    no)
      then
        MaybeItems3 = yes(Items2)
      else
        MaybeItems3 = no
    ),

    % Open the output stream.
    lookup_bool_option(OptionTable, informal_syntax, Informal),
    (
        FznOutputDest = output_to_stdout,
        OutputStream : io.output_stream = io.stdout_stream,
        flatten_model(OutputStream, MaybeOznOutputDest, ModelFileName,
            Approach, OptimiseFlatZinc, Informal, DebugSpec, MaybeItems3, !IO)
    ;
        FznOutputDest = output_to_file(FileName),
        io.open_output(FileName, Result, !IO),
        (
            Result = ok(OutputStream),
            flatten_model(OutputStream, MaybeOznOutputDest, ModelFileName,
                Approach, OptimiseFlatZinc, Informal, DebugSpec, MaybeItems3,
                !IO),
            io.close_output(OutputStream, !IO)
        ;
            Result = error(IO_Error),
            handle_io_error(mzn2fzn_program, IO_Error, !IO)
        )
    ).

:- pred flatten_model(io.text_output_stream::in,
    maybe(output_destination)::in, string::in, approach::in,
    optimise_flatzinc::in, bool::in, debug_spec::in, maybe(sast)::in,
    io::di, io::uo) is det.

flatten_model(OutputStream, MaybeOznOutputDest, ModelFileName,
        Approach, OptimiseFlatZinc, Informal, DebugSpec, MaybeSAST, !IO) :-
    do_io_stage(mzn2fzn_program, mzn2fzn_stage_names,
        "flattening", lang_minizinc, DebugSpec,
        minizinc_ast_to_flatzinc_model(OutputStream, MaybeOznOutputDest,
            ModelFileName, Approach, OptimiseFlatZinc, Informal),
        pprint_sast(pp_lang_flatzinc(print_coercions)), dump_sast,
        pprint_ast(pp_lang_flatzinc(print_coercions)), dump_ast,
        MaybeSAST, _, !IO).

:- func maybe_filter_predfunc_decls(maybe(items)) = maybe(items).

maybe_filter_predfunc_decls(no) = no.
maybe_filter_predfunc_decls(yes(Items0)) = yes(Items) :-
    Items = filter_predfunc_decls(Items0).

:- func filter_predfunc_decls(items) = items.

filter_predfunc_decls(Items0) = Items :-
    (
        Items0 = [],
        % There must at least be a solve item so this cannot happen.
        unexpected($pred ++ ": empty AST")
    ;
        Items0 = [I | Is],
        I = item(RawItem, _),
        ( if RawItem = predfunc_item(_, _, _, _, _, _) then
            Items = filter_predfunc_decls(Is)
          else
            Items = Items0
        )
    ).

%-----------------------------------------------------------------------------%

:- type approach
    --->    old_flattening
    ;       half_reification
    ;       translate_half_reification.

:- type optimise_flatzinc
    --->    optimise_flatzinc
    ;       dont_optimise_flatzinc.

    % minizinc_ast_to_flatzinc_model(FznFileStream,
    %   MaybeOMznFileStream, OptimiseFlatZinc, Lang, Items,
    %   Errors, Warnings, !IO).
    %
    % Convert a MiniZinc model into a FlatZinc model.
    % If MaybeOMznFileName = yes(OMznFileName) then an "output only"
    % MiniZinc model will be written to OMznFileName  This file should
    % be processed with the standalone 'minizinc' application with a .ozn
    % file to produce formatted output.
    %
    % Note: this is a managerial decision which I don't favour :-)
    % It is clunky and inelegant and makes a dog's breakfast out of the code.
    %
    % If Approach = old_flattening, we use the flatten.m package to do the
    % MiniZinc to FlatZinc conversion. If Approach = half_reification, we use
    % the hr.m package. If Approach = translate_half_reification, we use
    % the translate.m package.
    %
    % If OptimiseFlatZinc = optimise_flatzinc, then we run a reasonably
    % aggressive on the FlatZinc, guaranteeing at least that all variables
    % that have constant values or are aliases of other variables will be
    % pushed into the constraints. This has the effect of removing a
    % (sometimes significant) number of temporary variables from the
    % FlatZinc output. However, this optimisation does take some time
    % on larger models, which is why it can be disabled by setting
    % OptimiseFlatZinc to dont_optimise_flatzinc.
    %
:- pred minizinc_ast_to_flatzinc_model(io.output_stream::in,
    maybe(output_destination)::in, string::in,
    approach::in, optimise_flatzinc::in, bool::in, lang::in,
    sast::in, ast::out, zinc_errors::out, zinc_warnings::out,
    io::di, io::uo) is det.

minizinc_ast_to_flatzinc_model(FznOutputStream, MaybeOznOutputDest,
        ModelFileName, Approach, OptimiseFlatZinc, Informal, _Lang, SAST, [],
        Errors, Warnings, !IO) :-
    promise_equivalent_solutions [Result, !:IO] (
        try_io(
            flatten_mzn_model(ModelFileName, SAST, Approach, OptimiseFlatZinc,
                Informal),
            Result, !IO)
    ),
    (
        Result = succeeded(Env),
        write_fzn_model(FznOutputStream, ModelFileName, Informal, Env, !IO),
        (
            MaybeOznOutputDest = no
        ;
            MaybeOznOutputDest = yes(OznOutputDest),
            write_ozn_model(OznOutputDest, Env, SAST, !IO)
        ),
        Errors = [],
        Warnings = []
    ;
        Result = exception(Exception),
        ( if Exception = univ(UserError) then
            UserError = flattening_error(SrcLocn, UserErrorMsg),
            error_at_locn(UserErrorMsg, SrcLocn, [], Errors),
            Warnings = []
          else if Exception = univ(Unsatisfiable : unsatisfiable_model) then
            Unsatisfiable = unsatisfiable_model(SrcLocn, Context),
            error_at_locn(Context, SrcLocn, [], Warnings),
            Errors = [],
            write_unsatisfiable_model(FznOutputStream, MaybeOznOutputDest, !IO)
          else
            rethrow(Result)
        )
    ).

:- pred write_unsatisfiable_model(io.output_stream::in,
    maybe(output_destination)::in, io::di, io::uo) is det.

write_unsatisfiable_model(FznOutputStream, MaybeOznFileName, !IO) :-
    % This is the unsatisfiable model.
    io.write_string(FznOutputStream,
        "constraint bool_eq(false, true);\n", !IO),
    io.write_string(FznOutputStream,
        "solve satisfy;\n", !IO),
    (
        MaybeOznFileName = no
    ;
        MaybeOznFileName = yes(OznOutputDest),
        (
            OznOutputDest = output_to_file(OznFileName),
            io.open_output(OznFileName, Result, !IO),
            (
                Result = error(IO_Error),
                throw(IO_Error)
            ;
                Result = ok(OznOutputStream)
            )
        ;
            OznOutputDest = output_to_stdout,
            OznOutputStream = io.stdout_stream
        ),
        io.write_string(OznOutputStream, "output [];\n", !IO),
        (
            OznOutputDest = output_to_file(_),
            io.close_output(OznOutputStream, !IO)
        ;
            OznOutputDest = output_to_stdout
        )
   ).

:- pred flatten_mzn_model(string::in, sast::in, approach::in,
    optimise_flatzinc::in, bool::in, env::out, io::di, io::uo) is det.

flatten_mzn_model(ModelFileName, SAST, Approach, OptimiseFlatZinc, Informal,
        FinalEnv, !IO) :-
    % This call can be used to check whether we can convert all the MiniZinc
    % models mzn2fzn is given to the typed representation. We can't, yet.
    % convert_model_to_tmzn(ModelFileName, SAST, _TMzn, !IO),

    % XXX To make the traditional_flatten_mzn_model approach work, we must
    % change flatten_mzn_model so that ALL approaches return a tfzn_ast.
    (
        Approach = old_flattening,
        traditional_flatten_mzn_model(SAST, OptimiseFlatZinc, FinalEnv)
    ;
        Approach = half_reification,
        hr_flatten_mzn_model(SAST, OptimiseFlatZinc, TmpVarCounter, Model),
        extend_model_to_env(TmpVarCounter, Model, FinalEnv)
    ;
        Approach = translate_half_reification,
        tr_flatten_mzn_model(ModelFileName, SAST, OptimiseFlatZinc, Informal,
            FinalEnv, !IO)
    ).

    % We only generate the latest version of FlatZinc.
    %
:- pred traditional_flatten_mzn_model(sast::in, optimise_flatzinc::in,
    env::out) is det.

traditional_flatten_mzn_model(SAST, OptimiseFlatZinc, FinalEnv) :-
    some [!Env] (
        !:Env = new_env,
        SAST = sast(MZItems, SolveItem, MaybeOutputItem),

        trace [io(!IO)] (
            verbose("  Flattening items ...", !IO)
        ),

        % The Zinc topsorting algorithm doesn't put predicates first, which
        % is a problem if the user has supplied alternative definitions for
        % built-ins calls to which are only generated during flattening.
        % Our first traversal of the items simply extracts predicate
        % definitions.
        trace [io(!IO)] (
            verbose("   Processing predfunc declarations ...", !IO)
        ),
        list.foldl(flatten_process_predfunc_item, MZItems, !Env),

        % Next we process variable declarations and assignment items.
        trace [io(!IO)] (
            verbose("   Processing variable declarations ...", !IO)
        ),
        list.foldl(flatten_process_var_decl_item, MZItems, !Env),

        % Now we are in a state to process the constraint items.
        trace [io(!IO)] (
            verbose("   Processing constraints ...", !IO)
        ),
        list.foldl(flatten_process_constraint_item, MZItems, !Env),

        % Now process the output item.
        trace [io(!IO)] (
            verbose("   Processing output item ...", !IO)
        ),
        (
            MaybeOutputItem = yes(OutputItem),
            flatten_process_output_item(OutputItem, !Env)
        ;
            MaybeOutputItem = no
        ),

        % And the solve goal.
        trace [io(!IO)] (
            verbose("   Processing solve item ...", !IO)
        ),
        flatten_process_solve_item(SolveItem, !Env),

        % Post-process the variables and constraints.
        trace [io(!IO)] (
            verbose("   Post-processing variables and constraints ...",
                !IO)
        ),
        flatten_post_process_vars(!Env),

        % Optimise the resulting FlatZinc unless told not to.
        (
            OptimiseFlatZinc = optimise_flatzinc,
            trace [io(!IO)] (
                verbose("   Optimising FlatZinc ...", !IO)
            ),
            get_model(!.Env, Model0),
            optimise_flatzinc(Model0, Model),
            set_model(Model, !Env)
        ;
            OptimiseFlatZinc = dont_optimise_flatzinc
        ),
        flatten_finalise_solve_item(!Env),

        % The final Env value is what we need to print the FlatZinc model.
        FinalEnv = !.Env
    ).

:- pred hr_flatten_mzn_model(sast::in, optimise_flatzinc::in,
    counter::out, model::out) is det.

hr_flatten_mzn_model(SAST, OptimiseFlatZinc, TmpVarCounter, !:Model) :-
    some [!Info] (
        init_hr_info(!:Info),
        !:Model = empty_model,

        SAST = sast(MZItems, SolveItem, MaybeOutputItem),

        trace [io(!IO)] (
            verbose("  HR Flattening items ...", !IO)
        ),

        % The Zinc topsorting algorithm doesn't put predicates first, which
        % is a problem if the user has supplied alternative definitions for
        % built-ins calls to which are only generated during flattening.
        % Our first traversal of the items simply extracts predicate
        % definitions.
        trace [io(!IO)] (
            verbose("    HR Processing predfunc declarations ...", !IO)
        ),
        list.foldl(hr_process_predfunc_item, MZItems, !Model),

        % Next we process variable declarations and assignment items.
        trace [io(!IO)] (
            verbose("    HR Processing variable declarations ...", !IO)
        ),
        list.foldl2(hr_process_var_decl_item, MZItems, !Info, !Model),

        % Now we are in a state to process the constraint items.
        trace [io(!IO)] (
            verbose("    HR Processing constraints ...", !IO)
        ),
        list.foldl2(hr_process_constraint_item, MZItems, !Info, !Model),

        % Now process the output item.
        trace [io(!IO)] (
            verbose("    HR Processing output item ...", !IO)
        ),
        (
            MaybeOutputItem = yes(OutputItem),
            hr_process_output_item(OutputItem, !Info, !Model)
        ;
            MaybeOutputItem = no
        ),

        % And the solve goal.
        trace [io(!IO)] (
            verbose("    HR Processing solve item ...", !IO)
        ),
        hr_process_solve_item(SolveItem, !Info, !Model),

        % Post-process the variables and constraints.
        trace [io(!IO)] (
            verbose("   HR Post-processing variables and constraints ...", !IO)
        ),
        hr_post_process_vars(!Info, !Model),

        % Optimise the resulting FlatZinc unless told not to.
        (
            OptimiseFlatZinc = optimise_flatzinc,
            trace [io(!IO)] (
                verbose("    HR Optimising FlatZinc ...", !IO)
            ),
            optimise_flatzinc(!Model)
        ;
            OptimiseFlatZinc = dont_optimise_flatzinc
        ),

        TmpVarCounter = hr_info_get_tmp_var_counter(!.Info)
    ).

:- pred tr_flatten_mzn_model(string::in, sast::in, optimise_flatzinc::in,
    bool::in, env::out, io::di, io::uo) is det.

tr_flatten_mzn_model(ModelFileName, SAST, OptimiseFlatZinc, Informal,
        FinalEnv, !IO) :-
    some [!Info, !TFznConstraints] (
        init_tr_info(!:Info),
        !:TFznConstraints = no_tfzn_constraints,

        trace [io(!TIO)] (
            verbose("  TR Converting SAST ...", !TIO)
        ),

        convert_model_to_tmzn(ModelFileName, SAST, TMzn, ConvertSpecs, !IO),

        TMzn = tmzn(VarDeclItems, AssignItems0, ConstraintItems0, _SolveItem,
            _MaybeOutputItem),

        trace [io(!TIO)] (
            verbose("  TR Processing variable declarations ...", !TIO)
        ),

        list.foldl2(tr_process_var_decl_item, VarDeclItems,
            [], RevImplicitAssignItems, !Info),
        list.reverse(RevImplicitAssignItems, ImplicitAssignItems),
        AssignItems = ImplicitAssignItems ++ AssignItems0,

        trace [io(!TIO)] (
            verbose("  TR Processing assignments ...", !TIO)
        ),

        list.foldl2(tr_process_assign_item, AssignItems,
            [], RevImplicitConstraintItems, !Info),
        list.reverse(RevImplicitConstraintItems, ImplicitConstraintItems),
        ConstraintItems = ImplicitConstraintItems ++ ConstraintItems0,

        trace [io(!TIO)] (
            verbose("  TR Flattening TMzn constraints ...", !TIO)
        ),

        list.foldl3(tr_process_constraint_item, ConstraintItems,
            not_seen_unsatisfiable_constraint, SeenUnsatisfiableConstraint,
            !TFznConstraints, !Info),

        % XXX Solve
        SolveItem0 = tfzn_item_solve(tfzn_sk_satisfy, set.init),

        (
            SeenUnsatisfiableConstraint = not_seen_unsatisfiable_constraint,
            tr_post_process_vars(PostProcessConstraints, !Info),
            !:TFznConstraints = !.TFznConstraints ++ PostProcessConstraints,
            tr_info_get_var_info_maps(!.Info, VarInfoMaps),
            vim_get_par_var_decls(VarInfoMaps, ParDecls0, VarDecls0),
            TFznConstraintList0 =
                tfzn_constraint_set_to_list(!.TFznConstraints),
            tr_optimise_flatzinc(ParDecls0, ParDecls, VarDecls0, VarDecls,
                SolveItem0, SolveItem, TFznConstraintList0, TFznConstraintList)
        ;
            SeenUnsatisfiableConstraint = seen_unsatisfiable_constraint,
            ParDecls = [],
            VarDecls = [],
            SolveItem = SolveItem0,

            % Throw away all the constraints we have generated,
            % and replace them with a single trivial unsatisfiable constraint.
            UnsatConstraint = tfzn_constr_bool_compare(bool_eq,
                tfzn_bool_term_const(no), tfzn_bool_term_const(yes),
                not_reified),
            UnsatConstraintItem =
                tfzn_item_constraint(UnsatConstraint, set.init),
            TFznConstraintList = [UnsatConstraintItem]
        ),

        tr_info_get_errors(!.Info, TranslateSpecs),
        Specs = ConvertSpecs ++ TranslateSpecs,
        % XXX
        set.init(ErrorOptions),
        write_error_specs(Specs, ErrorOptions, 0, _, 0, _, !IO),

        io.open_output(ModelFileName ++ ".tfzn", Res, !IO),
        ( if Res = ok(Stream) then
            % XXX PredDecls
            PredDecls = [],
            TFzn = tfzn(PredDecls, ParDecls, VarDecls,
                TFznConstraintList, SolveItem),
            Opts = output_opts(Informal, 5),
            output_tfzn(Opts, Stream, TFzn, !IO)
        else
            true
        ),

        % Until this approach works, we cheat.
        traditional_flatten_mzn_model(SAST, OptimiseFlatZinc, FinalEnv)
    ).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

    % NOTE: changes here may need to be reflected in:
    %
    %   g12/zinc/man/mzn2fzn.1.in
    %
:- func mzn2fzn_usage = string.

mzn2fzn_usage =
    list.foldr(func(X, Xs) = X ++ "\n" ++ Xs, UsageLines, "") :-
    UsageLines = [
    "Usage: mzn2fzn [<options>] <model>.mzn [<data>.dzn ...]"
,   "Options:"
,   "    -h, --help"
,   "        Print this message."
,   "    --version"
,   "        Print version information."
,   "    -v, --verbose"
,   "        Output progress information as flattening proceeds."
,   "    -V, --very-verbose"
,   "        Output detailed progress information as flattening proceeds."
,   "    -d <file>, --data <file>"
,   "        File named <file> contains data used by the model."
,   "    -D <data>, --cmdline-data <data>"
,   "        Include the given data in the model."
,   "    -I <dir>, --search-dir <dir>"
,   "        Append <dir> to list of search directories."
,   "    -e, --model-check-only"
,   "        Check the model (without requiring data) for errors, but do not"
,   "        convert to FlatZinc."
,   "    --instance-check-only"
,   "        Check the model instance (including data) for errors, but do not"
,   "        convert to FlatZinc."
,   "    --flags-file <file>"
,   "        Take options from the specified file, and handle them as if they"
,   "        were specified on the command line."
,   "    --stdlib-dir <dir>, --mzn-stdlib-dir <dir>, --minizinc-stdlib-dir <dir>"
,   "       Specify an alternative MiniZinc standard library directory."
,   "    -G <dir>, --globals-dir <dir>, --mzn-globals-dir <dir>"
,   "    --minizinc-globals-dir <dir>"
,   "       Search for included files in <stdlib>/<dir>."
,   "    --std-defs, --force-std-defs, --force-standard-definitions"
,   "       Clear the lists of search and globals directories."
,   "    --std-globals, --force-standard-globals"
,   "       Clear the list of globals directories."
,   "    --no-optimise"
,   "       Do not run the optimiser on the generated FlatZinc (this"
,   "       may speed up generation of very large models)."
,   "    --restrict-includes"
,   "       Do not allow absolute paths or \'..\' in include items."
% ,   "    --half-reify"
% ,   "       Use half-reification during flattening."
,   ""
,   "Output Options:"
,   "    -O-, --no-output-ozn"
,   "       Do not output a model output specification."
,   "    --output-base <name>"
,   "       Use the specified name as the base name for generated files."
,   "    -o <file>, --output-to-file <file>, --output-fzn-to-file <file>"
,   "       Output the generated FlatZinc to the specified file."
,   "    --output-ozn-to-file <file>"
,   "       Output the model output specification to the specified file."
,   "    --output-to-stdout, --output-fzn-to-stdout"
,   "       Output the FlatZinc to the standard output rather than to a"
,   "       file."
,   "    --output-ozn-to-stdout"
,   "       Output the model output specification to the standard output"
,   "       rather than to a file."
,   ""
,   "Debugging Options:"
,   "    -S, --statistics"
,   "        Output messages about time/space usage to stderr."
,   "    --pprint-before <name>"
,   "        Pretty-print the IR before stage <name>."
,   "    --pprint-after <name>"
,   "        Pretty-print the IR after stage <name>."
,   "    --pprint-ignore-file <file>"
,   "        Ignore items from <file> when pretty-printing."
,   "    --dump-before <name>"
,   "        Dump the full IR before stage <name>."
,   "    --dump-after <name>"
,   "        Dump IR after stage <name>."
,   "    --stop-before <name>"
,   "        Stop compilation before stage <name>."
,   "    --stop-after <name>"
,   "        Stop compilation after stage <name>."
,   "    --ignore-stdlib"
,   "        Do not automatically include stdlib.mzn in the model."
,   "        (Nb: some models will not compile correctly with this option.)"
,   ""
,   "    Valid stage names:"
    ] ++
    list.map(func(X) = "        " ++ X, mzn2fzn_stage_names).

:- func mzn2fzn_version = string.

mzn2fzn_version = VersionMsg :-
    MiniZincVersion = minizinc_major_version,
    % Attach the build date to the version string for development versions.
    % Leave it alone for numbered versions and rotds (the former don't change
    % and the latter already include the build date in their version strings.)
    ( if MiniZincVersion = "DEV" then
        Version = string.format("%s (%s)",
            [s(MiniZincVersion), s(minizinc_build_date)])
      else
        Version = string.format("%s.%s.%s", [
            s(MiniZincVersion),
            s(minizinc_minor_version),
            s(minizinc_patch_version)
        ])
    ),
    VersionMsg =
        "G12 MiniZinc to FlatZinc converter, version " ++ Version ++ "\n" ++
        "Copyright (C) 2006-2012 The University of Melbourne and NICTA\n".

%-----------------------------------------------------------------------------%

    % Return the debug spec that is implicit in the option table.
    % This assumes that we have already checked that the stage names are
    % valid.
    %
:- func make_mzn2fzn_debug_spec(option_table(mzn2fzn_option)) = debug_spec.

make_mzn2fzn_debug_spec(OptionTable) = DebugSpec :-
    lookup_accumulating_option(OptionTable, pprint_before, PPrintBefore),
    lookup_accumulating_option(OptionTable, pprint_after,  PPrintAfter),
    lookup_accumulating_option(OptionTable, pprint_ignore_file,
        PPrintIgnoredFiles),
    lookup_accumulating_option(OptionTable, dump_before,   DumpBefore),
    lookup_accumulating_option(OptionTable, dump_after,    DumpAfter),
    lookup_accumulating_option(OptionTable, stop_before,   StopBefore),
    lookup_accumulating_option(OptionTable, stop_after,    StopAfter),
    DebugSpec = new_debug_spec(PPrintBefore, PPrintAfter,
        PPrintIgnoredFiles, DumpBefore, DumpAfter, StopBefore, StopAfter).

%-----------------------------------------------------------------------------%
%
% Control.
%

:- type mzn2fzn_control
    --->    mzn2fzn_control.

:- instance frontend_control(mzn2fzn_control) where [
    % XXX maybe this should just throw an exception since it shouldn't
    %     occur?
    ( warn_unknown_fzn_annotations(_) = yes ),
    ( extra_builtin_annotation(_, _, _, _) :- false ),
    ( post_typecheck_var_decl_action(_) = no ),
    ( post_typecheck_constraint_action(_) = no ),
    ( post_typecheck_solve_action(_) = no )
].

%-----------------------------------------------------------------------------%
%
% Search directories.
%

% mzn2fzn searchs for a file referred to in an include item in the following
% directories:
%
%       (a) the current working directory.
%       (b) the directories specified with --search-dir/-I.
%       (c) the standard library directories.  (See below.)
%
% Searching for a file halts as soon as a matching file is found.  This
% occurs even if directories yet to be searched also contain a matching
% file.  This is important because it allows us to override the default
% definitions for the global constraints.
%
% The root of the standard library directories may be specified in one
% of three ways:
%
%       (a) the value of the --stdlib-dir option.
%       (b) the value of the MZN_STDLIB_DIR environment variable.
%       (c) the value of the function minizinc_conf.install_prefix/0.
%
% The above are listed in order of preference.
%
% Within the standard library directories searching for included files
% is carried out in the following order:
%
%       (a) <stdlib root>/<dir> where <dir> is the argument of the
%           --globals-dir option.
%       (b) <stdlib root>/std
%
% The --globals-dir option behaves like the --search-dir option except
% that it is relative to the root of the standard library.
%
% The above layout is designed so that FlatZinc implementations can
% install alternative sets of globals in <stdlib root>/<dir> and the
% user can easily select between them all (including just the default
% globals definitions).

:- pred setup_mzn2fzn_search_dirs(option_table(mzn2fzn_option)::in,
    list(string)::out, list(string)::out, io::di, io::uo) is det.

setup_mzn2fzn_search_dirs(OptionTable, AllSearchDirs, !:DirErrors, !IO) :-
    lookup_string_option(OptionTable, stdlib_dir, OptStdLibDir),
    ( if OptStdLibDir = "" then
        io.get_environment_var("MZN_STDLIB_DIR", MaybeEnvStdLibDir, !IO),
        (
            MaybeEnvStdLibDir = yes(EnvStdLibDir),
            verbose("MZN_STDLIB_DIR set to " ++ EnvStdLibDir, !IO),
            verbose("Stdlib root set using environment variable", !IO),

            % XXX On Windows any quotes in the value of MZN_STDLIB_DIR will
            % be escaped which breaks things.  The following environment
            % variable is a rather inelegant way of dealing with this.
            io.get_environment_var("MZN_WIN_PATH_HACK", MaybeWinPathHack, !IO),
            (
                MaybeWinPathHack = yes(_),
                verbose("Applying Windows path hack", !IO),
                string.replace_all(EnvStdLibDir, "\"", "", StdLibRoot)
            ;
                MaybeWinPathHack = no,
                StdLibRoot = EnvStdLibDir
            )
        ;
            MaybeEnvStdLibDir = no,
            StdLibRoot = install_prefix / "lib" / "minizinc",
            verbose("Stdlib root set using hardcoded path", !IO)
        )
      else
        StdLibRoot = OptStdLibDir,
        verbose("Stdlib root set using --stdlib-dir option", !IO)
    ),

    StdLibDir = StdLibRoot / "std",

    % Handle any --globals-dir options.
    %
    ExtraGlobalsDirs = lookup_accumulating_option(OptionTable, globals_dir),
    list.map_foldl2(setup_mzn2fzn_globals_dir(StdLibRoot),
        ExtraGlobalsDirs, ExtraStdSearchDirs, [], !:DirErrors, !IO),
    StdSearchDirs = ExtraStdSearchDirs ++ [StdLibDir],

    % Handle an --search-dir options.
    %
    CmdLineSearchDirs = lookup_accumulating_option(OptionTable, search_dir),
    list.foldl2(check_search_dir, CmdLineSearchDirs, !DirErrors, !IO),
    AllSearchDirs = ["."] ++ CmdLineSearchDirs ++ StdSearchDirs,
    verbose("Search directories: " ++ AllSearchDirs^string, !IO).

:- pred setup_mzn2fzn_globals_dir(string::in, string::in, string::out,
    list(string)::in, list(string)::out, io::di, io::uo) is det.

setup_mzn2fzn_globals_dir(StdLibRoot, Dir, StdSearchDir, !DirErrors, !IO) :-
    StdSearchDir = StdLibRoot / Dir,
    io.check_file_accessibility(StdSearchDir, [read], Res, !IO),
    (
        Res = ok
    ;
        Res = error(_),
        list.cons("Globals directory not found: " ++ Dir, !DirErrors)
    ).

:- pred check_search_dir(string::in, list(string)::in, list(string)::out,
    io::di, io::uo) is det.

check_search_dir(Dir, !DirErrors, !IO) :-
    io.check_file_accessibility(Dir, [read], Res, !IO),
    (
        Res = ok
    ;
        Res = error(_),
        list.cons("Search directory not found: " ++ Dir, !DirErrors)
    ).

%-----------------------------------------------------------------------------%

    % Returns a string that gives the name of this program as it will
    % appear in error messages.
    %
:- func mzn2fzn_program = string.

mzn2fzn_program = "mzn2fzn".

%-----------------------------------------------------------------------------%

:- pred handle_internal_error(string::in, software_error::in,
    io::di, io::uo) is det.

handle_internal_error(ProgName, SoftwareError, !IO) :-
    SoftwareError = software_error(Msg),
    io.stderr_stream(Stderr, !IO),
    io.format(Stderr, "%s: internal error: %s\n", [s(ProgName), s(Msg)], !IO),
    io.set_exit_status(1, !IO).

%-----------------------------------------------------------------------------%
:- end_module mzn2fzn.
%-----------------------------------------------------------------------------%
