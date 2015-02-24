%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2006-2007 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Nicholas Nethercote <njn@csse.unimelb.edu.au>
%
% Error-handling stuff for the Zinc compiler and other related programs.
%
% This file is not called "error.m" because that name causes clashes with
% other libraries within G12.
%-----------------------------------------------------------------------------%

:- module zinc_error.
:- interface.

%-----------------------------------------------------------------------------%

:- import_module types_and_insts.
:- import_module zinc_common.

:- import_module list.

%-----------------------------------------------------------------------------%

    % Compilation errors and warnings.  The warning types are synonyms, just
    % differentiated for documentation purposes.  Note that predicates for
    % printing errors are in zinc_pprint.m.
    %
    % A note about warnings:  I (njn) hate compiler warnings.  I believe most
    % warnings indicate flaws in a language or its implementation -- if
    % something is dangerous enough to require a warning, it should be
    % disallowed, or redesigned to be less dangerous.  Furthermore, smart users
    % treat warnings as errors and always fix them, and dumb users ignore
    % warnings and get their fingers burnt.  So, although the compiler is able
    % to issue warnings, it (at the time of writing) does this extremely
    % sparingly, and in my opinion this behaviour should be preserved.
    %
:- type zinc_errors == list(zinc_error).
:- type zinc_warnings == list(zinc_warning).

:- type zinc_warning == zinc_error.
:- type zinc_error
            % We don't use 'error' as the functor because that's used in io.m,
            % and so would lead to lots of annoying ambiguity.
    --->    zinc_error(error_locn, error_msg).  % Location, error message.

:- type error_locn
    --->    file_line_column(string, int, int)  % Filename, line, column.
    ;       file_line(string, int)              % Filename, line.
            % An error that isn't specific to a source location, eg. if the
            % file named on the command line cannot be found.  Or if the
            % location is unknown.
    ;       non_specific                        
            % An error involving a builtin operator or similar;  should only
            % occur if there is a bug in the compiler(?)
    ;       builtin
    .

:- type error_msg == list(error_msg_part).
:- type error_msg_part
    --->    fixed(string)
            % The string should be printed as is.
    
    ;       words(string)
            % The string contains words separated by whitespace.  The
            % whitespace can be replaced with line breaks.

    ;       type_inst(type_inst)
            % The type-inst should be pretty printed, with quotes around it,
            % eg. "`int'".
    
    ;       type_inst_sig_args(type_insts)
            % The type-inst args should be pretty printed in parentheses, with
            % quotes around it, eg. "`(int, var float)'".
    
    ;       suffix(error_msg_part, string)
            % The part should be printed with the suffix, with no white-space
            % between them.
    
    ;       quote(string)
            % The string is printed within `' quotes.
    
    ;       nl
            % A newline should be printed.
    
    ;       src_locn(src_locn)
            % A source location.         
            
    ;       empty.
            % The empty string;  occasionally useful.

%-----------------------------------------------------------------------------%

    % error_at_locn(ErrMsg, Locn, !Errs):
    % Add an error from location Locn with the message ErrMsg to !Errs.
    %
:- pred error_at_locn(error_msg::in, src_locn::in,
    zinc_errors::in, zinc_errors::out) is det.

:- func error_compare(zinc_error::in, zinc_error::in)
    = (builtin.comparison_result::uo) is det.

    % Convert a list of strings into a list of error message pars.
    % separated by commas, with the last two elements separated by `and'.
    %
:- func list_to_parts((func(T) = error_msg_part), list(T))
    = list(error_msg_part).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

error_at_locn(ErrMsg, SrcLocn, !Errs) :-
    (   SrcLocn = src_locn(FileName, LineNum),
        ErrLocn = file_line(FileName, LineNum)
    ;
        SrcLocn = builtin,
        ErrLocn = builtin
    ;
        SrcLocn = unknown,
        ErrLocn = non_specific
    ),
    Err = zinc_error(ErrLocn, ErrMsg),
    !:Errs = [Err | !.Errs].

%-----------------------------------------------------------------------------%
    
    % Basically:
    % - Built-in errors < non-specific < file-line and file-line-column errors
    % - file-line and file-line-column errors are sorted by filename then line
    %   number, but if a file-line-column and a file-line occur on the same
    %   line, we put the file-line-column first.
error_compare(zinc_error(ErrLocn1, ErrMsg1), zinc_error(ErrLocn2, ErrMsg2)) =
        Cmp :-
    (
        ErrLocn1 = builtin,
        (
            ErrLocn2 = builtin,
            compare(Cmp, ErrMsg1, ErrMsg2)
        ;
            ( ErrLocn2 = non_specific
            ; ErrLocn2 = file_line_column(_,_,_)
            ; ErrLocn2 = file_line(_,_)
            ),
            Cmp = (<)
        )
     ;
        ErrLocn1 = non_specific,
        (
            ErrLocn2 = non_specific,
            compare(Cmp, ErrMsg1, ErrMsg2)
        ;
            ( ErrLocn2 = builtin
            ; ErrLocn2 = file_line_column(_,_,_)
            ; ErrLocn2 = file_line(_,_)
            ),
            Cmp = (<)
        )
    ;
        ErrLocn1 = file_line_column(FileName1, Line1, Col1),
        (
            ErrLocn2 = file_line_column(FileName2, Line2, Col2),
            compare(Cmp, { FileName1, Line1, Col1 }, { FileName2, Line2, Col2 })
       ;
            ErrLocn2 = file_line(FileName2, Line2),
            compare(Cmp, { FileName1, Line1, 0 }, { FileName2, Line2, 1 })
        ;
            ( ErrLocn2 = builtin
            ; ErrLocn2 = non_specific
            ),
            Cmp = (<)
        )
    ;
        ErrLocn1 = file_line(FileName1, Line1),
        (
            ErrLocn2 = file_line(FileName2, Line2),
            compare(Cmp, { FileName1, Line1 }, { FileName2, Line2 })
        ;
            ErrLocn2 = file_line_column(FileName2, Line2, _Col2),
            compare(Cmp, { FileName1, Line1, 1 }, { FileName2, Line2, 0 })
        ;
            ( ErrLocn2 = builtin
            ; ErrLocn2 = non_specific
            ),
            Cmp = (>)
        )
    ).

%-----------------------------------------------------------------------------%

list_to_parts(_, []) = [].
list_to_parts(F, [Elem]) = [F(Elem)].
list_to_parts(F, [Elem1, Elem2]) =
    [F(Elem1), words("and"), F(Elem2)].
list_to_parts(F, [Elem1, Elem2, Elem3 | Elems]) = 
    [suffix(F(Elem1), ",") | list_to_parts(F, [Elem2, Elem3 | Elems])].

%-----------------------------------------------------------------------------%
:- end_module zinc_error.
%-----------------------------------------------------------------------------%
