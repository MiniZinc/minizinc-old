%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Julien Fischer <juliensf@csse.unimelb.edu.au>
%
% A parser for the MiniZinc / FlatZinc solution stream. 
%
%-----------------------------------------------------------------------------%

:- module read_soln.
:- interface.

:- import_module zinc_ast.

:- import_module list.
:- import_module io.

%-----------------------------------------------------------------------------%

:- type comment == string.

:- type comments == list(comment).

:- type read_soln_result
    --->    result_unknown(comments)
    ;       result_unbounded(comments)
    ;       result_unsatisfiable(comments)
    ;       result_search_complete(comments)
    ;       result_soln(list(item), comments)
    ;       result_parse_error
    ;       result_eof(comments).

%-----------------------------------------------------------------------------%

:- pred read_solution(io.text_input_stream::in,
    string::in, read_soln_result::out, io::di, io::uo) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module zinc_common.
:- import_module zinc_error.
:- import_module zinc_parser.
:- import_module zinc_pprint.

:- import_module bool.
:- import_module exception.
:- import_module int.
:- import_module maybe.
:- import_module string.

%-----------------------------------------------------------------------------%

read_solution(File, ProgName, Result, !IO) :-
    read_solution_2(File, ProgName, []/*Items*/, []/*Comments*/, Result, !IO).

:- pred read_solution_2(io.text_input_stream::in, string::in,
    list(item)::in, comments::in, read_soln_result::out, io::di, io::uo) is det.

read_solution_2(File, ProgName, !.Items, !.Comments, Result, !IO) :-
    io.input_stream_name(File, FileName, !IO),
    io.get_line_number(File, LineNumber, !IO),
    io.read_line_as_string(File, ReadResult, !IO),
    (
        ReadResult = ok(Line0),
        Line = string.strip(Line0),
        Class = classify_line(Line),
        (
            Class = line_blank,
            % Skip blank lines in the solution stream.
            read_solution_2(File, ProgName, !.Items, !.Comments, Result, !IO)
        ;
            Class = line_comment,
            !:Comments = [Line | !.Comments],
            read_solution_2(File, ProgName, !.Items, !.Comments, Result, !IO)
        ;
            Class = line_end_of_solution,
            % Put the items and comments back in their original relative order.
            list.reverse(!Items), 
            list.reverse(!Comments),
            Result = result_soln(!.Items, !.Comments)
        ;
            Class = line_unknown,
            (
                !.Items = [], 
                read_trailing_comments(File, ProgName, 
                    (func(Cs) = result_unknown(Cs)), !.Comments, Result, !IO)
            ;
                !.Items = [_ | _],
                Msg = [
                    words("error: solution assignments before"),
                    words("unknown result marker?")
                ],
                error_at_locn(Msg, src_locn(FileName, LineNumber),
                    [], Errors),
                print_errors(ProgName, Errors, !IO),
                Result = result_parse_error
            )
        ;
            Class = line_unbounded,
            (
                !.Items = [],
                read_trailing_comments(File, ProgName, 
                    (func(Cs) = result_unbounded(Cs)), !.Comments, Result, !IO)
            ;
                !.Items = [_ | _],
                Msg = [
                    words("error: solution assignments before"),
                    words("unbounded result marker?")
                ],
                error_at_locn(Msg, src_locn(FileName, LineNumber),
                    [], Errors),
                print_errors(ProgName, Errors, !IO),
                Result = result_parse_error
            )
        ;
            Class = line_unsatisfiable,
            (
                !.Items = [],
                read_trailing_comments(File, ProgName, 
                    (func(Cs) = result_unsatisfiable(Cs)), !.Comments,
                        Result, !IO)
            ;
                !.Items = [_ | _],
                Msg = [
                    words("error: solution assignments before"),
                    words("unsatisfiable result marker?")
                ],
                error_at_locn(Msg, src_locn(FileName, LineNumber),
                    [], Errors),
                print_errors(ProgName, Errors, !IO),
                Result = result_parse_error
            )
        ;
            Class = line_search_complete,
            (
                !.Items = [],
                read_trailing_comments(File, ProgName,
                    (func(Cs) = result_search_complete(Cs)), !.Comments,
                    Result, !IO)
            ;
                !.Items = [_ | _],
                Msg = [
                    words("error: missing solution separator before"),
                    words("end of search marker.")
                ],
                error_at_locn(Msg, src_locn(FileName, LineNumber),
                    [], Errors),
                print_errors(ProgName, Errors, !IO),
                Result = result_parse_error
            )
        ;
            Class = line_other,
            % Try using the Zinc parser to turn this into an assign item.
            % The FlatZinc solution stream is a subset of MiniZinc, so
            % we parse it as though it is MiniZinc.
            zinc_parser.model(lang_minizinc, FileName, LineNumber,
                no/*IsDataFile*/, Line, NewItems, Includes, [], Errs),
            (
                ( Includes = [_], IncludesDesc = "item"
                ; Includes = [_, _ | _], IncludesDesc = "items"
                ),
                IncludesMsg = [
                    words("error: include"), words(IncludesDesc),
                    words("in solution stream.")
                ],
                error_at_locn(IncludesMsg, src_locn(FileName, LineNumber),
                    [], IncludesErrs),
                print_errors(ProgName, IncludesErrs, !IO),
                Result = result_parse_error
            ;
                Includes = [],
                (
                    Errs = [],
                    (
                        NewItems = [],
                        NoItemMsg = [
                            words("error: unrecognised item"),
                            words("in solution stream.")
                        ],
                        error_at_locn(NoItemMsg, src_locn(FileName, LineNumber),
                            [], NotItemErrs),
                        print_errors(ProgName, NotItemErrs, !IO),
                        Result = result_parse_error
                    ;
                        NewItems = [Item],
                        RawItem = Item ^ raw_item,
                        (   
                            RawItem = assign_item(_, _),
                            list.cons(Item, !Items),
                            read_solution_2(File, ProgName, !.Items, !.Comments,
                                Result, !IO)
                        ;
                            ( RawItem = constraint_item(_)
                            ; RawItem = var_decl_item(_, _, _, _)
                            ; RawItem = predfunc_item(_, _, _, _, _, _)
                            ; RawItem = annotation_item(_, _)
                            ; RawItem = solve_item(_, _)
                            ; RawItem = output_item(_)
                            ),
                            BadItemMsg = [
                                words("error: illegal item"),
                                words("in solution stream.")
                            ],
                            error_at_locn(BadItemMsg,
                                src_locn(FileName, LineNumber),
                                [], BadItemErrs),
                            print_errors(ProgName, BadItemErrs, !IO),
                            Result = result_parse_error
                        )
                    ;
                        NewItems = [_, _ | _],
                        % Only one item per line is allowed in a well-formed
                        % FlatZinc stream.
                        MultiItemMsg = [
                            words("error: multiple items on a single line"),
                            words("in solution stream."), nl,
                            words(" Each item must appear on a separate line.")
                        ],
                        error_at_locn(MultiItemMsg,
                            src_locn(FileName, LineNumber),
                            [], MultiItemErrs),
                        print_errors(ProgName, MultiItemErrs, !IO),
                        Result = result_parse_error
                    )
                ;
                    Errs = [_ | _],
                    print_errors(ProgName, Errs, !IO),
                    Result = result_parse_error
                )
            )
        ) 
    ;
        ReadResult = eof,
        % Pass through any trailing comments in the solution stream. 
        list.reverse(!Comments),
        Result = result_eof(!.Comments)
    ;
        ReadResult = error(IO_Error),
        throw(IO_Error)
    ).    

:- pred read_trailing_comments(io.text_input_stream::in, string::in,
    (func(comments) = read_soln_result)::in,
    comments::in, read_soln_result::out, io::di, io::uo) is det.

read_trailing_comments(File, ProgName, MakeResult, !.Comments, Result, !IO) :-
    io.get_line_number(File, LineNumber, !IO),
    io.read_line_as_string(File, ReadLineResult, !IO),
    (
        ReadLineResult = ok(Line0),
        Line = string.strip(Line0),
        Class = classify_line(Line),
        (
            (   
                Class = line_blank
            ;
                Class = line_comment,
                list.cons(Line, !Comments)
            ),
            read_trailing_comments(File, ProgName, MakeResult, !.Comments,
                Result, !IO)
        ;
            ( Class = line_end_of_solution
            ; Class = line_unknown
            ; Class = line_unbounded
            ; Class = line_unsatisfiable
            ; Class = line_search_complete
            ; Class = line_other
            ),
            Msg = [
                words("error: misformed FlatZinc solution stream.")
            ],
            io.input_stream_name(File, FileName, !IO),
            error_at_locn(Msg, src_locn(FileName, LineNumber), [], Errors),
            print_errors(ProgName, Errors, !IO),
            Result = result_parse_error
        )
    ;
        ReadLineResult = eof,
        list.reverse(!Comments),
        Result = MakeResult(!.Comments)
    ;
        ReadLineResult = error(IO_Error),
        throw(IO_Error)
    ).


%-----------------------------------------------------------------------------%

:- type line_class
    --->    line_blank
    ;       line_comment
    ;       line_end_of_solution    
    ;       line_unknown
    ;       line_unbounded
    ;       line_unsatisfiable
    ;       line_search_complete
    ;       line_other. 

:- func classify_line(string) = line_class.

classify_line(Line) = Class :-
    ( if  Line = "" then
        Class = line_blank
      else if string.index(Line, 0, '%') then
        Class = line_comment
      else if Line = "----------" then
        Class = line_end_of_solution
      else if Line = "=====UNKNOWN=====" then
        Class = line_unknown
      else if Line = "=====UNBOUNDED=====" then
        Class = line_unbounded
      else if Line = "=====UNSATISFIABLE=====" then
        Class = line_unsatisfiable
      else if Line = "==========" then
        Class = line_search_complete
      else
        Class = line_other
    ).

%-----------------------------------------------------------------------------%

:- pred print_errors(string::in, zinc_errors::in, io::di, io::uo) is det.

print_errors(ProgName, Errors, !IO) :-
    PPLang = pp_lang_minizinc(print_coercions),
    pprint_zinc_errors(PPLang, ProgName, Errors, !IO),
    io.set_exit_status(1, !IO).

%-----------------------------------------------------------------------------%
:- end_module read_soln.
%-----------------------------------------------------------------------------%
