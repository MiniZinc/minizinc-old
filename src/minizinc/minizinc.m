%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2011-2012 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Julien Fischer <juliensf@csse.unimelb.edu.au>
%
% This program is the top-level driver for the MiniZinc system.
%
%-----------------------------------------------------------------------------%

:- module minizinc.
:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is cc_multi.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module minizinc_config.

:- import_module bool.
:- import_module char.
:- import_module dir.
:- import_module exception.
:- import_module getopt_io.
:- import_module int.
:- import_module list.
:- import_module map.
:- import_module maybe.
:- import_module string.

%-----------------------------------------------------------------------------%

main(!IO) :-
    ( try [io(!IO)] (
        query_system_shell(SysShell, !IO),
        io.command_line_arguments(Args, !IO),
        OptionOps = option_ops_multi(
            short_option,
            long_option,
            (pred(O::out, D::out) is multi :- option_defaults(O, D)),
            special_handler(SysShell)
        ),
        process_options(OptionOps, Args, NonOptionArgs, Result, !IO),
        (
            Result = error(Msg),
            bad_cmdline([Msg], !IO)
        ;
            Result = ok(OptionTable),
            ( if lookup_bool_option(OptionTable, version, yes) then
                io.write_string(minizinc_version, !IO)
              else if lookup_bool_option(OptionTable, help, yes) then
                io.write_string(minizinc_usage, !IO)
              else
                list.filter(is_dzn, NonOptionArgs, DznArgs, NonDznArgs),
                (
                    NonDznArgs = [],
                    bad_cmdline(["no model file specified"], !IO)
                ;
                    NonDznArgs = [ModelFileName],
                    ( if mzn_file_base(ModelFileName, ModelFileNameBase) then
                         main_2(OptionTable, SysShell, ModelFileNameBase,
                            DznArgs, !IO)
                      else
                        bad_cmdline(["model file name must" ++
                            " have the form `<file>.mzn'."], !IO)
                    )
                ;
                    NonDznArgs = [_, _ | _],
                    bad_cmdline(["more than one model file specified."], !IO)
                )
            )
        )
    )
    then
        true
    catch IO_Error ->
        handle_io_error(IO_Error, !IO)
    catch cpviz_error ->
        % We should have already generated an error message if something
        % goes wrong when processing CP-Viz related files, so do nothing
        % here.
        true
    catch_any Other ->
        throw(Other)
    ).

    % Excpetions of this type are thrown if something goes wrong while
    % processing CP-Viz related files.
    %
:- type cpviz_error
    --->    cpviz_error.
 
:- pred is_dzn(string::in) is semidet.

is_dzn(FileName) :-
    string.suffix(FileName, ".dzn").

:- pred mzn_file_base(string::in, string::out) is semidet.

mzn_file_base(FileName, FileNameBase) :-
    string.remove_suffix(FileName, ".mzn", FileNameBase),
    FileNameBase \= "".     % Don't allow just ".mzn" as a name.

%-----------------------------------------------------------------------------%

:- pred main_2(option_table(option)::in, system_shell::in, string::in,
    list(string)::in, io::di, io::uo) is det.

main_2(OptionTable, SysShell, ModelFileNameBase, DznFiles, !IO) :-
    lookup_bool_option(OptionTable, verbose, Verbose),
    make_mzn2fzn_cmdline(OptionTable, SysShell, ModelFileNameBase, DznFiles,
        Mzn2fznCmdLine, !IO),
    (
        Verbose = yes,
        io.write_string(Mzn2fznCmdLine, !IO),
        io.nl(!IO),
        io.flush_output(!IO)
    ;
        Verbose = no
    ),
    io.call_system_return_signal(Mzn2fznCmdLine, FlattenResult, !IO),
    (
        FlattenResult = ok(SysCallResult),
        (
            SysCallResult = exited(ExitStatus),
            ( if ExitStatus = 0 then
                do_evaluation(OptionTable, SysShell, ModelFileNameBase, !IO)
              else
                io.set_exit_status(1, !IO) 
            )
        ;
            SysCallResult = signalled(SigNum),
            ( if SigNum = sigint then
                cleanup_generated_files(OptionTable, ModelFileNameBase, !IO)
              else
                Msg = "flattening killed by signal " ++ int_to_string(SigNum),
                report_error([Msg], !IO)
            )
        )
    ;
        FlattenResult = error(Error),
        Msg = io.error_message(Error),
        cleanup_generated_files(OptionTable, ModelFileNameBase, !IO),
        report_error(["could not invoke mzn2fzn: " ++ Msg], !IO)
    ).

%-----------------------------------------------------------------------------%

:- pred make_mzn2fzn_cmdline(option_table(option)::in, system_shell::in,
    string::in, list(string)::in, string::out, io::di, io::uo) is det.

make_mzn2fzn_cmdline(OptionTable, SysShell, ModelFileNameBase,
        DznFiles, CmdLine, !IO) :-
    io.get_environment_var("MZN2FZN_CMD", MaybeMzn2fznCmd, !IO),
    (
        MaybeMzn2fznCmd = yes(FlattenCmd)
    ;
        MaybeMzn2fznCmd = no,
        lookup_string_option(OptionTable, mzn2fzn_cmd, FlattenCmd)
    ),
    lookup_accumulating_option(OptionTable, globals_dir, GlobalsDirs0),
    GlobalsDirs = list.map((func(D) = "-G " ++ D), GlobalsDirs0),
    lookup_accumulating_option(OptionTable, search_dir, SearchDirs0),
    SearchDirs = list.map((func(D) = "-I" ++ quote_arg(SysShell, D)),
        SearchDirs0),
    lookup_accumulating_option(OptionTable, cmdline_data, CmdLineData0),
    CmdLineData = list.map((func(D) = "-D" ++ quote_arg(SysShell, D)),
        CmdLineData0),
    lookup_accumulating_option(OptionTable, datafile, DataFiles0),
    DataFiles = list.map((func(D) = "-d " ++ quote_arg(SysShell, D)),
        DataFiles0),
    lookup_bool_option(OptionTable, optimise_minizinc, DoOpt),
    (
        DoOpt = yes,
        MznOpt = []
    ;
        DoOpt = no,
        MznOpt = ["--no-optimise"]
    ),
    lookup_bool_option(OptionTable, restrict_includes, DoRestrict),
    (
        DoRestrict = yes,
        RestrictIncs = ["--restrict-includes"]
    ;
        DoRestrict = no,
        RestrictIncs = []
    ),
    Cmds = list.condense([
        [FlattenCmd],
        SearchDirs,
        GlobalsDirs,
        CmdLineData,
        MznOpt,
        RestrictIncs,
        DataFiles,
        [ModelFileNameBase ++ ".mzn"],
        DznFiles
    ]),
    CmdLine = string.join_list(" ", Cmds).
    
%-----------------------------------------------------------------------------%

:- pred do_evaluation(option_table(option)::in, system_shell::in, string::in,
    io::di, io::uo) is det.

do_evaluation(OptionTable, SysShell, ModelFileNameBase, !IO) :-
    lookup_bool_option(OptionTable, verbose, Verbose),
    make_fzn_cmdline(OptionTable, SysShell, ModelFileNameBase, FznCmdLine,
        !IO),
    (
        Verbose = yes,
        io.write_string(FznCmdLine, !IO),
        io.nl(!IO),
        io.flush_output(!IO)
    ;
        Verbose = no
    ),

    % XXX G12's FlatZinc interpreter ignores the -z option and requires us to
    % set an environment variable to enable CP-Viz.
    %
    lookup_bool_option(OptionTable, use_cpviz, UseCPViz),
    (
        UseCPViz = yes,
        % Clean up any CPViz generated files that happen to be lying around
        % and turn on the monitoring system.
        io.remove_file(cpviz_tree_file, _, !IO),
        io.remove_file(cpviz_viz_file, _, !IO),
        io.set_environment_var("G12_MONITOR", "cpviz", !IO)
    ;
        UseCPViz = no
    ),
    io.call_system_return_signal(FznCmdLine, EvalResult, !IO),
    (
        EvalResult = ok(SysCallResult),
        (
            SysCallResult = exited(ExitStatus),
            ( if ExitStatus = 0 then
                (
                    UseCPViz = no
                ;
                    UseCPViz = yes,
                    do_visualization(OptionTable, SysShell, ModelFileNameBase,
                        !IO)
                ),
                cleanup_generated_files(OptionTable, ModelFileNameBase, !IO)
              else
                io.set_exit_status(1, !IO)
            )
        ;
            SysCallResult = signalled(SigNum),
            ( if SigNum = sigint then
                cleanup_generated_files(OptionTable, ModelFileNameBase, !IO)
              else
                Msg = "evaluation killed by signal " ++ int_to_string(SigNum),
                report_error([Msg], !IO)
            )
        )
    ;
        EvalResult = error(Error),
        Msg = io.error_message(Error),
        cleanup_generated_files(OptionTable, ModelFileNameBase, !IO),
        report_error(["could not invoke interpreter: " ++ Msg], !IO)
    ).

%-----------------------------------------------------------------------------%

:- pred do_visualization(option_table(option)::in,
    system_shell::in, string::in, io::di, io::uo) is det.

do_visualization(OptionTable, SysShell, ModelFileNameBase, !IO) :-
    dir.make_directory(cpviz_output_dir, MkdirResult, !IO),
    (
        MkdirResult = ok,
        setup_cpviz_environment(SysShell, EnvSetupContinue, !IO),
        (
            EnvSetupContinue = yes,
            output_cpviz_config_file(!IO),
            invoke_cpviz(OptionTable, SysShell, ModelFileNameBase,
                CPVizContinue, !IO),
            (
                CPVizContinue = yes,
                output_cpviz_view_file(!IO),
                output_cpviz_control_file(!IO),
                io.format("Visualization created in %s.\n",
                    [s(cpviz_view_file)], !IO)
            ;
                CPVizContinue = no
            )
        ;
            EnvSetupContinue = no
        )
    ;
        MkdirResult = error(IO_Error),
        throw(IO_Error)
    ).

:- func cpviz_config_file = string.

cpviz_config_file = "config.xml".

:- func cpviz_tree_file = string.

cpviz_tree_file = "search.xml".

:- func cpviz_viz_file = string.

    % NOTE: the filename here must be exact since CP-Viz requires
    % that name.
    %
cpviz_viz_file = "vis.xml".

:- func cpviz_output_dir = string.

cpviz_output_dir = "viz.out".

:- func cpviz_tree_file_root = string.

cpviz_tree_file_root = "tree".

:- func cpviz_viz_file_root = string.

cpviz_viz_file_root = "viz".

:- func cpviz_idx_file = string.

cpviz_idx_file = cpviz_output_dir / "aaa.idx".

:- func cpviz_control_file = string.

cpviz_control_file = cpviz_output_dir / "control.html".

:- func cpviz_view_file = string.

cpviz_view_file = cpviz_output_dir / "aaa.html".

:- func xml_header(string) = string.

xml_header(ProgName) = "<!-- Generated by " ++ ProgName ++ "-->".

:- pred output_cpviz_config_file(io::di, io::uo) is det.

output_cpviz_config_file(!IO) :-
    io.open_output(cpviz_config_file, MaybeConfigFile, !IO),
    (
        MaybeConfigFile = ok(File),
        io.format(File, "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n",
            [], !IO),
        io.format(File, "%s\n", [s(xml_header("minizinc"))], !IO),
        io.format(File, "<configuration version=\"1.0\" directory=\"%s\">\n",
            [s(cpviz_output_dir)], !IO),
        io.format(File,
            "    <tool show=\"tree\" fileroot=\"%s\" repeat=\"all\"/>\n",
            [s(cpviz_tree_file_root)], !IO),
        io.format(File,
            "    <tool show=\"viz\" fileroot=\"%s\"/>\n",
            [s(cpviz_viz_file_root)], !IO),
        io.write_string(File, "</configuration>\n", !IO),
        io.close_output(File, !IO)
    ;
        MaybeConfigFile = error(CfgFileError),
        throw(CfgFileError)
    ).
        
:- pred invoke_cpviz(option_table(option)::in, system_shell::in,
    string::in, bool::out, io::di, io::uo) is det.

invoke_cpviz(OptionTable, _SysShell, ModelFileNameBase, Continue, !IO) :-
    io.get_environment_var("JAVA", MaybeJavaCmd, !IO),
    (
        MaybeJavaCmd = yes(Java)
    ;
        MaybeJavaCmd = no,    
        lookup_string_option(OptionTable, java_interpreter, Java)
    ),
    CPVizCmdLine = string.join_list(" ", [
        Java,
        "ie.ucc.cccc.viz.Viz",
        cpviz_config_file,
        cpviz_tree_file,
        cpviz_viz_file
    ]),
    lookup_bool_option(OptionTable, verbose, Verbose),
    (
        Verbose = yes,
        io.write_string(CPVizCmdLine, !IO),
        io.nl(!IO),
        io.flush_output(!IO)
    ;
        Verbose = no
    ),
    io.call_system_return_signal(CPVizCmdLine, CPVizResult, !IO),
    (
        CPVizResult = ok(SysCallResult),
        (
            SysCallResult = exited(ExitStatus),
            ( if ExitStatus = 0 then
                Continue = yes
              else
                io.set_exit_status(1, !IO),
                Continue = no
            )
        ;
            SysCallResult = signalled(SigNum),
            ( if SigNum = sigint then
                cleanup_generated_files(OptionTable, ModelFileNameBase, !IO)
              else
                Msg = "evaluation killed by signal "
                    ++ int_to_string(SigNum),
                report_error([Msg], !IO)
            ),
            Continue = no
        )
    ;
        CPVizResult = error(Error),
        Msg = io.error_message(Error),
        cleanup_generated_files(OptionTable, ModelFileNameBase, !IO),
        report_error(["could not invoke cpviz: " ++ Msg], !IO),
        Continue = no
    ).

:- pred setup_cpviz_environment(system_shell::in, bool::out,
    io::di, io::uo) is det.

setup_cpviz_environment(SysShell, Continue, !IO) :-
    io.get_environment_var("CPVIZ_HOME", MaybeCPVizHome, !IO),
    io.get_environment_var("CLASSPATH", MaybeClassPath, !IO),
    (
        MaybeCPVizHome = yes(CPVizHome),
        (
            MaybeClassPath = yes(ClassPath),
            (
                SysShell = system_shell_posix,
                PathSep = ":"
            ;
                SysShell = system_shell_windows,
                PathSep = ";"
            ),
            ClassPathPrime = CPVizHome ++ PathSep ++ ClassPath
        ;
            MaybeClassPath = no,
            ClassPathPrime = CPVizHome
        ),
        io.set_environment_var("CLASSPATH", ClassPathPrime, !IO),
        Continue = yes
    ;
        MaybeCPVizHome = no,
        (
            MaybeClassPath = yes(_),
            Continue = yes
        ;
            MaybeClassPath = no,
            Msg = "please set either CPVIZ_HOME or CLASSPATH to the" ++
                " Viz directory.",
            report_error([Msg], !IO),
            Continue = no
        )
    ).

:- pred output_cpviz_view_file(io::di, io::uo) is det.

output_cpviz_view_file(!IO) :-
    io.open_output(cpviz_view_file, MaybeViewFile, !IO),
    (
        MaybeViewFile = ok(ViewFile),
        io.format(ViewFile, "%s\n", [s(xml_header("minizinc"))], !IO),
        io.write_strings(ViewFile, [
            "<html>\n",
            "    <frameset rows=\"60,*\">\n",
            "         <frame name=\"control\" src=\"control.html\"/>\n",
            "         <frameset cols=\"35%,*\">\n",
            "             <frame name=\"tree\" src=\"tree0.svg\"/>\n",
            "             <frame name=\"viz\" src=\"viz0.svg\"/>\n",
            "         </frameset>\n",
            "    </frameset>\n",
            "</html>\n"
        ], !IO),
        io.close_output(ViewFile, !IO)
    ;
        MaybeViewFile = error(IO_Error),
        throw(IO_Error)
    ).

:- pred output_cpviz_control_file(io::di, io::uo) is det.

output_cpviz_control_file(!IO) :-
    io.open_output(cpviz_control_file, MaybeCtrlFile, !IO),
    (
        MaybeCtrlFile = ok(CtrlFile),
        io.write_list(CtrlFile, control_file_head, "\n", io.write_string, !IO),
        io.open_input(cpviz_idx_file, OpenIdxFileResult, !IO),
        (
            OpenIdxFileResult = ok(IdxFile),
            assign_values_to_globals(CtrlFile, IdxFile, -1, MaxTime, !IO),
            io.format(CtrlFile, "maxtime = %d\n", [i(MaxTime)], !IO),
            io.close_input(IdxFile, !IO),
            io.write_list(CtrlFile, control_file_tail, "\n", io.write_string,
                !IO),
            io.close_output(CtrlFile, !IO)
        ;
            OpenIdxFileResult = error(IO_Error),
            throw(IO_Error)
        )
    ;
        MaybeCtrlFile = error(IO_Error),
        throw(IO_Error)
    ).

%-----------------------------------------------------------------------------%

:- pred assign_values_to_globals(io.text_output_stream::in,
    io.text_input_stream::in, int::in, int::out, io::di, io::uo) is det.

assign_values_to_globals(CtrlFile, IdxFile, !Index, !IO) :-
    io.read_line_as_string(IdxFile, ReadResult, !IO),
    (
        ReadResult = ok(Line),
        Words = string.words(Line),
        ( if Words = [TreeSVG, VizSVG] then
            !:Index = !.Index + 1,
            io.format(CtrlFile, "treefiles[%d] = '%s'\n",
                [i(!.Index), s(TreeSVG)], !IO),
            io.format(CtrlFile, "vizfiles[%d] = '%s'\n",
                [i(!.Index), s(VizSVG)], !IO),
            assign_values_to_globals(CtrlFile, IdxFile, !Index, !IO)
          else  
            io.input_stream_name(IdxFile, IdxFileName, !IO),
            io.get_line_number(IdxFile, CurrLineNo, !IO),
            % The current line number will have been incremented after
            % we read the line with the error on it.
            ErrLineNo = CurrLineNo - 1,
            string.format("misformed line in index file at %s:%d",
                [s(IdxFileName), i(ErrLineNo)], Msg),
            report_error([Msg], !IO),
            throw(cpviz_error)
        )
    ;
        ReadResult = eof
    ;
        ReadResult = error(IO_Error),
        throw(IO_Error)
    ).

%-----------------------------------------------------------------------------%

:- func control_file_head = list(string).

control_file_head = [
xml_header("minizinc"),
"<html>",
"   <head>",
"       <script type=\"text/javascript\">",
"           // arrays to hold the .svg filenames",
"           var treefiles = new Array();",
"           var vizfiles = new Array();",
"           // size of each array",
"           var maxtime;"
].

:- func control_file_tail = list(string).

control_file_tail = [
"",
"            // milliseconds between animation steps",
"            var animtime = 1000;",
"",
"            // are we currently animating?",
"            var animating = 0;",
"",
"            // animation timer",
"            var animtimer;",
"",
"            // current time we are viewing",
"            var current = 0;",
"",
"            // make the tree and viz frames show the current time",
"            function setCurrent(t) {",
"                if (t == current || t < 0 || t > maxtime) return;",
"                current = t;",
"                for (var i = 0; i < parent.frames.length; i++) {",
"                    var fr = parent.frames[i];",
"                    switch (fr.name) {",
"                        case \"tree\":",
"                            fr.location = treefiles[current];",
"                            break;",
"                        case \"viz\":",
"                            fr.location = vizfiles[current];",
"                            break;",
"                        default:",
"                    }",
"                }",
"            }",
"",
"            // step forward every animtime milliseconds",
"            function animate() {",
"                setCurrent(current + 1);",
"                animtimer = setTimeout(\"animate()\", animtime);",
"            }",
"",
"            // start and stop animation",
"            function startAnimation() {",
"                if (!animating) {",
"                    animating = 1;",
"                    animate();",
"                }",
"            }",
"",
"            function stopAnimation() {",
"                clearTimeout(animtimer);",
"                animating = 0;",
"            }",
"",
"            // configure the step time",
"            function configure() {",
"               var msg = \"Set the animation step time in milliseconds\";",
"               var newtime = prompt(msg, animtime);",
"                if (newtime == null) return;",
"                newtime = newtime.match(\"[0-9]+\");",
"                if (newtime < 1) return;",
"                animtime = newtime;",
"            }",
"",
"        </script>",
"    </head>",
"    <body>",
"        <input type=\"button\" onclick=\"setCurrent(0)\" value=\"Start\"/>",
"        <input type=\"button\" onclick=\"setCurrent(current-1)\" value=\"Back\"/>",
"        <input type=\"button\" onclick=\"setCurrent(current+1)\" value=\"Forward\"/>",
"        <input type=\"button\" onclick=\"setCurrent(maxtime)\" value=\"End\"/>",
"        <input type=\"button\" onclick=\"startAnimation()\" value=\"Animate\"/>",
"        <input type=\"button\" onclick=\"stopAnimation()\" value=\"Stop\"/>",
"        <input type=\"button\" onclick=\"configure()\" value=\"Configure\"/>",
"    </body>",
"</html>"
].

%-----------------------------------------------------------------------------%

:- pred cleanup_generated_files(option_table(option)::in,
    string::in, io::di, io::uo) is det.

cleanup_generated_files(OptionTable, FileNameBase, !IO) :-
    lookup_bool_option(OptionTable, keep_files, KeepFiles),
    (
        KeepFiles = yes
    ;
        KeepFiles = no,
        io.remove_file(FileNameBase ++ ".fzn", _, !IO),
        io.remove_file(FileNameBase ++ ".ozn", _, !IO)
    ).

%-----------------------------------------------------------------------------%

:- pred make_fzn_cmdline(option_table(option)::in, system_shell::in,
    string::in, string::out, io::di, io::uo) is det.

make_fzn_cmdline(OptionTable, SysShell, ModelFileNameBase, CmdLine, !IO) :-
    io.get_environment_var("FLATZINC_CMD", MaybeEnvFznCmd, !IO),
    (
        MaybeEnvFznCmd = yes(FznCmd)
    ;
        MaybeEnvFznCmd = no,
        lookup_string_option(OptionTable, flatzinc_cmd, FznCmd)
    ), 
    lookup_bool_option(OptionTable, all_solutions, AllSolns),
    (
        AllSolns = yes,
        AllSolnsOpt = ["-a"]
    ;
        AllSolns = no,
        AllSolnsOpt = []
    ),
    lookup_bool_option(OptionTable, statistics, Statistics),
    (
        Statistics = yes,
        StatsOpt = ["-s"]
    ;
        Statistics = no,
        StatsOpt = []
    ),
    lookup_bool_option(OptionTable, use_cpviz, UseCPViz),
    (
        UseCPViz = yes,
        CPVizOpt = ["-z"]
    ;
        UseCPViz = no,
        CPVizOpt = []
    ),
    lookup_maybe_int_option(OptionTable, parallel, UseParallelism),
    (
        UseParallelism = yes(NumCores),
        ParallelOpt = ["-p " ++ int_to_string(NumCores)]
    ;
        UseParallelism = no,
        ParallelOpt = []
    ),
    lookup_int_option(OptionTable, num_solutions, NumSolns),
    ( if NumSolns = 1 then
        NumSolnsOpt = []
      else
        NumSolnsOpt = ["-n " ++ int_to_string(NumSolns)]
    ),
    lookup_string_option(OptionTable, random_seed, SeedStr),
    ( if SeedStr = "" then
        RndSeedOpt = []
      else
        RndSeedOpt = ["-r " ++ quote_arg(SysShell, SeedStr)]
    ),
    lookup_bool_option(OptionTable, canonicalize, Canonicalize),
    (
        Canonicalize = yes,
        CanCmd = ["| solns2dzn -c"]
    ;
        Canonicalize = no,
        CanCmd = []
    ),
    lookup_string_option(OptionTable, backend, Backend),
    ( if Backend = "" then
        BackendOpt = []
      else
        BackendOpt = ["-b " ++ Backend]
    ),
    lookup_bool_option(OptionTable, warn_ignored_annotations, WarnIgnAnns),
    (
        WarnIgnAnns = yes,
        WarnIgnAnnsOpt = []
    ;
        WarnIgnAnns = no,
        WarnIgnAnnsOpt = ["--no-warn-ignored-annotations"]
    ),
    lookup_maybe_string_option(OptionTable, output_to_file, MaybeOutputToFile),
    (
        MaybeOutputToFile = yes(OutputFileName),
        OutputFileOpt = ["-o " ++ quote_arg(SysShell, OutputFileName)]
    ;
        MaybeOutputToFile = no,
        OutputFileOpt = []
    ),
    lookup_bool_option(OptionTable, output_comments, OutputComments),
    (
        OutputComments = yes,
        OutputCommentsOpt = []
    ;
        OutputComments = no,
        OutputCommentsOpt = ["--no-output-comments"]
    ),
    lookup_maybe_string_option(OptionTable, solution_separator, MaybeSolnSep),
    (
        MaybeSolnSep = yes(SolnSep),
        SolnSepOpt = ["--soln-sep " ++ quote_arg(SysShell, SolnSep)]
    ;
        MaybeSolnSep = no,
        SolnSepOpt = []
    ),
    lookup_maybe_string_option(OptionTable, unsatisfiable_msg, MaybeUnsatMsg),
    (
        MaybeUnsatMsg = yes(UnsatMsg),
        UnsatMsgOpt = ["--unsatisfiable-msg " ++ quote_arg(SysShell, UnsatMsg)]
    ;
        MaybeUnsatMsg = no,
        UnsatMsgOpt = []
    ),
    lookup_maybe_string_option(OptionTable, unbounded_msg, MaybeUnbdMsg),
    (
        MaybeUnbdMsg = yes(UnbdMsg),
        UnbdMsgOpt = ["--unbounded-msg " ++ quote_arg(SysShell, UnbdMsg)]
    ;
        MaybeUnbdMsg = no,
        UnbdMsgOpt = []
    ),
    lookup_maybe_string_option(OptionTable, unknown_msg, MaybeUnkwnMsg),
    (
        MaybeUnkwnMsg = yes(UnkwnMsg),
        UnkwnMsgOpt = ["--unknown-msg " ++ quote_arg(SysShell, UnkwnMsg)]
    ;
        MaybeUnkwnMsg = no,
        UnkwnMsgOpt = []
    ),
    lookup_maybe_string_option(OptionTable, search_complete_msg,
        MaybeCompleteMsg),
    (
        MaybeCompleteMsg = yes(CompleteMsg),
        CompleteMsgOpt = ["--search-complete-msg "
            ++ quote_arg(SysShell, CompleteMsg)]
    ;
        MaybeCompleteMsg = no,
        CompleteMsgOpt = []
    ),
    lookup_int_option(OptionTable, ignore_leading_lines,
        NumIgnoreLeadLines),
    ( if NumIgnoreLeadLines > 0 then
        IgnoreLinesOpt = ["-i " ++ int_to_string(NumIgnoreLeadLines)]
       else
        IgnoreLinesOpt = []
    ),    
    lookup_accumulating_option(OptionTable, flatzinc_flags,
        MaybeUserOpts),
    Cmds = list.condense([
        [FznCmd],
        AllSolnsOpt,
        StatsOpt,
        CPVizOpt,
        BackendOpt,
        NumSolnsOpt,
        ParallelOpt,
        RndSeedOpt,
        WarnIgnAnnsOpt,
        MaybeUserOpts,
        [ModelFileNameBase ++ ".fzn"],
        CanCmd,
        ["| solns2out"],
        OutputFileOpt,
        OutputCommentsOpt,
        IgnoreLinesOpt,
        SolnSepOpt,
        UnsatMsgOpt,
        UnbdMsgOpt,
        UnkwnMsgOpt,
        CompleteMsgOpt,
        [ModelFileNameBase ++ ".ozn"]
    ]),
    CmdLine = string.join_list(" ", Cmds).

%-----------------------------------------------------------------------------%
%
% Command line options.
%

:- type option
    --->    help
    ;       version
    ;       verbose
    ;       keep_files
    ;       flags_file

    % The following option is only required for compatibility with G12's
    % test suite -- it should not be documented.
    % XXX we ought to have a standard way of controlling warning output
    %     in FlatZinc implementations.
    %
    ;       warn_ignored_annotations

    %  Flattening (mzn2fzn) options.
    %
    ;       mzn2fzn_cmd
    ;       cmdline_data
    ;       search_dir
    ;       globals_dir
    ;       datafile
    ;       force_standard_globals
    ;       optimise_minizinc
    ;       restrict_includes

    %  Evaluation (flatzinc) options.
    %
    ;       flatzinc_cmd
    ;       flatzinc_flags
    ;       flatzinc_quoted_flag
    ;       backend
    ;       canonicalize
    ;       num_solutions
    ;       all_solutions
    ;       statistics
    ;       parallel
    ;       random_seed

    % Output (solns2out) options.
    %
    ;       output_to_file
    ;       output_comments
    ;       ignore_leading_lines
    ;       solution_separator
    ;       unsatisfiable_msg
    ;       unbounded_msg
    ;       unknown_msg
    ;       search_complete_msg

    % CP-Viz options.
    ;       use_cpviz
    ;       java_interpreter.

:- pred short_option(char::in, option::out) is semidet.

short_option('a',   all_solutions).
short_option('b',   backend).
short_option('c',   canonicalize).
short_option('d',   datafile).
short_option('f',   flatzinc_cmd).
short_option('h',   help).
short_option('i',   ignore_leading_lines).
short_option('k',   keep_files).
short_option('n',   num_solutions).
short_option('o',   output_to_file).
short_option('p',   parallel).
short_option('r',   random_seed).
short_option('s',   statistics).
short_option('v',   verbose).
short_option('z',   use_cpviz).
short_option('D',   cmdline_data).
short_option('I',   search_dir).
short_option('G',   globals_dir).

:- pred long_option(string::in, option::out) is semidet.

long_option("help",                 help).
long_option("version",              version).
long_option("verbose",              verbose).
long_option("flags_file",           flags_file).
long_option("keep-files",           keep_files).

long_option("warn-ignored-annotations", warn_ignored_annotations).

long_option("mzn2fzn-cmd",          mzn2fzn_cmd).
long_option("cmdline-data",         cmdline_data). 
long_option("search-dir",           search_dir).
long_option("globals-dir",          globals_dir).
long_option("mzn-globals-dir",      globals_dir).
long_option("minizinc-globals-dir", globals_dir).
long_option("force-standard-globals", force_standard_globals).
long_option("std-globals",            force_standard_globals).
long_option("data",                 datafile).
long_option("optimise",             optimise_minizinc).
long_option("optimize",             optimise_minizinc).
long_option("restrict-includes",    restrict_includes).

long_option("fzn-cmd",              flatzinc_cmd).
long_option("flatzinc-cmd",         flatzinc_cmd).
long_option("fzn-flags",            flatzinc_flags).
long_option("flatzinc-flags",       flatzinc_flags).
long_option("flatzinc-flag",        flatzinc_quoted_flag).
long_option("fzn-flag",             flatzinc_quoted_flag).    
long_option("backend",              backend).
long_option("solver-backend",       backend).
long_option("canonicalize",         canonicalize).
long_option("num-solutions",        num_solutions).
long_option("all",                  all_solutions).
long_option("all-solns",            all_solutions).
long_option("all-solutions",        all_solutions).
long_option("statistics",           statistics). 
long_option("solver-statistics",    statistics).
long_option("parallel",             parallel).
long_option("seed",                 random_seed).
long_option("random-seed",          random_seed).

long_option("output-to-file",       output_to_file).
long_option("output-comments",      output_comments).
long_option("ignore-lines",         ignore_leading_lines).
long_option("ignore-leading-lines", ignore_leading_lines).
long_option("soln-sep",             solution_separator).
long_option("soln-separator",       solution_separator).
long_option("solution-separator",   solution_separator).
long_option("unsat-msg",            unsatisfiable_msg).
long_option("unsatisfiable-msg",    unsatisfiable_msg).
long_option("unbounded-msg",        unbounded_msg).
long_option("unknown-msg",          unknown_msg).
long_option("search-complete-msg",  search_complete_msg).

long_option("viz",                  use_cpviz).
long_option("cpviz",                use_cpviz).
long_option("use-cpviz",            use_cpviz).
long_option("java",                 java_interpreter).

:- pred option_defaults(option, option_data).
:- mode option_defaults(out, out) is multi.
:- mode option_defaults(in, out) is det.

option_defaults(help,                  bool(no)).
option_defaults(version,               bool(no)).
option_defaults(verbose,               bool(no)).
option_defaults(flags_file,            file_special).
option_defaults(keep_files,            bool(no)).

option_defaults(warn_ignored_annotations, bool(yes)).

option_defaults(mzn2fzn_cmd,           string("mzn2fzn")).
option_defaults(cmdline_data,          accumulating([])).
option_defaults(search_dir,            accumulating([])).
option_defaults(globals_dir,           accumulating([])).
option_defaults(datafile,              accumulating([])).
option_defaults(force_standard_globals, special).
option_defaults(optimise_minizinc,     bool(yes)).
option_defaults(restrict_includes,     bool(no)).

option_defaults(flatzinc_cmd,          string("flatzinc")).
option_defaults(flatzinc_flags,        accumulating([])).
option_defaults(flatzinc_quoted_flag,  string_special).
option_defaults(backend,               string("")).
option_defaults(canonicalize,          bool(no)).
option_defaults(num_solutions,         int(1)).
option_defaults(all_solutions,         bool(no)).
option_defaults(statistics,            bool(no)).
option_defaults(parallel,              maybe_int(no)).
option_defaults(random_seed,           string("")).

option_defaults(output_to_file,        maybe_string(no)).
option_defaults(output_comments,       bool(yes)).
option_defaults(ignore_leading_lines,  int(0)).
option_defaults(solution_separator,    maybe_string(no)).
option_defaults(unsatisfiable_msg,     maybe_string(no)).
option_defaults(unbounded_msg,         maybe_string(no)).
option_defaults(unknown_msg,           maybe_string(no)).
option_defaults(search_complete_msg,   maybe_string(no)).

option_defaults(use_cpviz,             bool(no)).
option_defaults(java_interpreter,      string("java")).

:- pred special_handler(system_shell::in, option::in, special_data::in,
    option_table(option)::in, maybe_option_table(option)::out)
    is semidet.

special_handler(_, force_standard_globals, none, !.OptionTable,
        ok(!:OptionTable)) :-
    map.set(globals_dir, accumulating([]), !OptionTable).

special_handler(SysShell, flatzinc_quoted_flag, string(Flag), !.OptionTable,
        ok(!:OptionTable)) :-
    lookup_accumulating_option(!.OptionTable, flatzinc_flags, Flags),
    FlagsPrime = Flags ++ [quote_arg(SysShell, Flag)],
    map.set(flatzinc_flags, accumulating(FlagsPrime), !OptionTable).  

%-----------------------------------------------------------------------------%

:- pragma foreign_decl("C", "#include <signal.h>").

:- func sigint = int.
:- pragma foreign_proc("C",
    sigint = (S::out),
    [promise_pure, will_not_call_mercury],
"
    S = SIGINT;
").

%-----------------------------------------------------------------------------%
%
% Command interpreter interface
%

    % Succeeds if the Windows API is available.
    % (This includes Cygwin and MinGW / MSYS.)
    %
:- pred have_win_api is semidet.
:- pragma foreign_proc("C",
    have_win_api,
    [promise_pure, will_not_call_mercury],
"
#if defined(MR_WIN32)
    SUCCESS_INDICATOR = MR_TRUE;
#else
    SUCCESS_INDICATOR = MR_FALSE;
#endif

").

    % Succeeds if we are on a Cygwin system, i.e. we are linked against
    % cygwin.dll.
    %
:- pred have_cygwin is semidet.
:- pragma foreign_proc("C",
    have_cygwin,
    [promise_pure, will_not_call_mercury],
"
#if defined(MR_CYGWIN)
    SUCCESS_INDICATOR = MR_TRUE;
#else
    SUCCESS_INDICATOR = MR_FALSE;
#endif

").

    % The type of shell that is invoked by a call to io.call_system/4 or
    % io.call_system_return_signal/4.
    % On POSIX systems (including Cygwin) this is (supposed to be) "sh -c".  On
    % Windows it will be cmd.exe by default (or more generally whatever the
    % value of the environment variable COMSPEC is.)
    %
    % NOTE: MinGW uses the Microsoft runtime libraries so the system shell will
    % be cmd.exe, not sh.  This is the case even when the MSYS shell is being
    % used.
    %
:- type system_shell
    --->    system_shell_posix
            % The POSIX (or a compatible) shell.

    ;       system_shell_windows.
            % The Windows command interpreter, i.e. cmd.exe.

    % Return the type of the system shell.
    % NOTE: this predicate takes the I/O state since future extensions
    % to it may need to consult the value of environment variables.
    %
:- pred query_system_shell(system_shell::out, io::di, io::uo) is det.

query_system_shell(SysShell, !IO) :-
    ( if have_win_api then
        ( if minizinc.have_cygwin then
            SysShell = system_shell_posix
          else
            SysShell = system_shell_windows
        )
      else
        SysShell = system_shell_posix
    ).

    % Quote an argument to a shell command.
    % 
:- func quote_arg(system_shell, string) = string.

quote_arg(SysShell, Arg0) = Arg :-
    (
        SysShell = system_shell_windows,
        ( ( string_contains_whitespace(Arg0) ; Arg0 = "" ) ->
            Arg = """" ++ Arg0 ++ """"
        ;
            Arg = Arg0
        )
    ;
        SysShell = system_shell_posix,
        ArgList = quote_arg_unix(string.to_char_list(Arg0)),
        (
            ArgList = [],
            Arg = """"""
        ;
            ArgList = [_ | _],
            (
                list.member(Char, ArgList),
                \+
                    ( char.is_alnum_or_underscore(Char)
                    ; Char = ('-')
                    ; Char = ('/')
                    ; Char = ('.')
                    ; Char = (',')
                    ; Char = (':')
                    )
            ->
                Arg = """" ++ string.from_char_list(ArgList) ++ """"
            ;
                Arg = string.from_char_list(ArgList)
            )
        )
    ).

:- pred string_contains_whitespace(string::in) is semidet.

string_contains_whitespace(Str) :-
    Chars = string.to_char_list(Str),
    some [Char] (
        list.member(Char, Chars),
        char.is_whitespace(Char)
    ).

:- func quote_arg_unix(list(char)) = list(char).

quote_arg_unix([]) = [].
quote_arg_unix([Char | Chars0]) = Chars :-
    Chars1 = quote_arg_unix(Chars0),
    ( quote_char_unix(Char) ->
        Chars = [('\\'), Char | Chars1]
    ;
        Chars = [Char | Chars1]
    ).

:- pred quote_char_unix(char::in) is semidet.

quote_char_unix('\\').
quote_char_unix('"').
quote_char_unix('`').
quote_char_unix('$').

%-----------------------------------------------------------------------------%

:- pred handle_io_error(io.error::in, io::di, io::uo) is det.

handle_io_error(Error, !IO) :-
    io.progname_base("minizinc", ProgName, !IO),
    io.stderr_stream(Stderr, !IO),
    Msg = io.error_message(Error),
    io.format(Stderr, "%s: I/O error: %s\n", [s(ProgName), s(Msg)], !IO),
    io.set_exit_status(1, !IO).

:- pred bad_cmdline(list(string)::in, io::di, io::uo) is det.

bad_cmdline(Msgs, !IO) :-
    io.progname_base("minizinc", ProgName, !IO),
    io.stderr_stream(Stderr, !IO),
    WriteErrLine = (pred(Msg::in, !.IO::di, !:IO::uo) is det :-
        io.format(Stderr, "%s: %s\n", [s(ProgName), s(Msg)], !IO)
    ),
    list.foldl(WriteErrLine, Msgs, !IO),
    io.format(Stderr, "%s: use --help for more information.\n",
        [s(ProgName)], !IO),
    io.set_exit_status(1, !IO).

:- pred report_error(list(string)::in, io::di, io::uo) is det.

report_error(Msgs, !IO) :-
    io.progname_base("minizinc", ProgName, !IO),
    io.stderr_stream(Stderr, !IO),
    WriteErrLine = (pred(Msg::in, !.IO::di, !:IO::uo) is det :-
        io.format(Stderr, "%s: %s\n", [s(ProgName), s(Msg)], !IO)
    ),
    list.foldl(WriteErrLine, Msgs, !IO),
    io.set_exit_status(1, !IO).

%-----------------------------------------------------------------------------%
%
% Usage and version messages
%

    % NOTE: changes here may need to be reflected in:
    %
    %   g12/zinc/man/minizinc.1.in
    %
:- func minizinc_usage = string.

minizinc_usage =
    list.foldr(func(X, Xs) = X ++ "\n" ++ Xs, UsageLines, "") :-
    UsageLines = [
    "Usage: minizinc [<options>] <model>.mzn [<data>.dzn ...]"
,   "Options:"
,   "    -h, --help"
,   "       Print this message."
,   "    --version"
,   "       Print version information."
,   "    --flags-file <file>"
,   "       Take the options from the specified file and handle them as if they"
,   "       were specified on the command line."
,   "    -k, --keep-files"
,   "       Do not delete intermediate files generated during evaluation."
,   ""
,   "Flattening Options:"
,   "    --mzn2fzn-cmd <cmd>"
,   "       Specify the command used to invoke the MiniZinc-to-FlatZinc"
,   "       converter.  The default command is: mzn2fzn."
,   "    -D <data>, --cmdline-data <data>"
,   "       Include the given data in the model."
,   "    -I <dir>, --search-dir <dir>"
,   "       Append <dir> to the list of search directories in which to search"
,   "       for included files."
,   "    -G <dir>, --globals-dir <dir>, --mzn-globals-dir <dir>"
,   "    --minizinc-globals-dir <dir>"
,   "       Search for included files in <stdlib>/<dir>."
,   "    -d <file>, --data <file>"
,   "       The specified file contains data used by the model." 
,   "    --std-globals, --force-standard-globals"
,   "       Clear the list of globals directories."
,   "    --no-optimise, --no-optimize"
,   "       Do not run the optimiser on the generated FlatZinc."
,   "       (This may speed up flattening of very large models.)"
,   "    --restrict-includes"
,   "       Do not allow absolute paths or \'..\' in include items."
,   ""      
,   ""
,   "Evaluation Options:"
,   "    -f <cmd>, --flatzinc-cmd <cmd>"
,   "       Specify the command used to invoke the FlatZinc interpreter."
,   "       The default command is: flatzinc."
,   "    --fzn-flags <options>, --flatzinc-flags <options>"
,   "       Specify option to be passed to the FlatZinc interpreter."
,   "    --fzn-flag <option>, --flatzinc-flag <option>"
,   "       As above, but for for options that are single words that need to"
,   "       be quoted when passed to the shell."
,   "    -b <backend>, --backend <backend>, --solver-backend <backend>"
,   "       Select the solver(s) and evaluation algorithm used by the FlatZinc"
,   "       interpreter."
,   "    -c, --canonicalize"
,   "       Canonicalize the FlatZinc solution stream."
,   "       Note that this option prevents incremental printing of solutions."
,   "    -n <n>, --num-solutions <n>"
,   "       An upper bound on the number of solutions to output."
,   "       The default is 1." 
,   "    -a, --all-solns, --all-solutions"
,   "       Print all solutions."
,   "    -s, --statistics, --solver-statistics"
,   "       Request that the FlatZinc interpreter emit statistical information"
,   "       gathered by solvers(s) with each solution in the form of comments."
,   "    -p <n>, --parallel <n>"
,   "       Use multiple threads and/or cores during search."
,   "       The argument <n> specifies the number of cores available."
,   "    -r <seed>, --seed <seed>, --random-seed <seed>"
,   "       Seed the interpreter's random number generator (if any) with the"
,   "       given value.  The form of the seed is implementation-dependent."
,   ""
,   "Output Options:"
,   "    -o <file>, --output-to-file <file>"
,   "       Print solutions to the specified file rather than to the standard"
,   "       output."
,   "    --no-output-comments"
,   "       Do not print comments in the FlatZinc solution stream." 
,   "    -i <n>, --ignore-lines <n>, --ignore-leading-lines <n>"
,   "       Ignore the first <n> lines in the FlatZinc solution stream."
,   "    --soln-sep <s>, --soln-separator <s>, --solution-separator <s>"
,   "        Specify the string used to separate solutions."
,   "        The default is to use the FlatZinc solution separator,"
,   "        \"----------\"."
,   "    --unsat-msg <msg>, --unsatisfiable-msg <msg>"
,   "        Specify the message to print if a model instance is"
,   "        unsatisfiable."
,   "        The default is to print \"=====UNSATISFIABLE=====\"."
,   "    --unbounded-msg <msg>"
,   "        Specify the message to print if a the objective of a"
,   "        model instance is unbounded."
,   "        The default is to print \"=====UNBOUNDED=====\"."
,   "    --unknown-msg <msg>"
,   "        Specify the message to print if search terminates without"
,   "        the entire search space having been explored and if no"
,   "        solution has been found."
,   "        The default is to print \"=====UNKNOWN=====\"."
,   "    --search-complete-msg <msg>"
,   "        Specify the message to print if search terminates having"
,   "        explored the complete search space."
,   "        The default is to print \"==========\"."
,   ""
,   "CP-Viz Options:"
,   "    -z, --viz, --cpviz, --use-cpviz"
,   "        Generate a visualization using CP-Viz."
,   "    --java <cmd>"
,   "        Specify the command used to invoke the Java interpreter."
,   "        The default is: java."
].

:- func minizinc_version = string.

minizinc_version = VersionMsg :-
    Version = get_minizinc_version,
    VersionMsg =
        "G12 MiniZinc evaluation driver, version " ++ Version ++ "\n"
++      "Copyright (C) 2011-2012 The University of Melbourne and NICTA\n".

%-----------------------------------------------------------------------------%
:- end_module minizinc.
%-----------------------------------------------------------------------------%
