%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Main author: zs.
%
% This module contains code for representing and formatting error messages.
% It is based on error_util.m in the Mercury compiler, but adapted to G12.
%
% We print out error_specs in a format like this:
%
% module.mzn:10: first line of error message blah blah blah
% module.mzn:10:   second line of error message blah blah blah
% module.mzn:10:   third line of error message blah blah blah
%
% The words will be packed into lines as tightly as possible,
% with spaces between each pair of words, subject to the constraints
% that every line starts with a src_locn, followed by Indent+1 spaces
% on the first line and Indent+3 spaces on later lines, and that every
% line contains at most 80 characters (unless a long single word
% forces the line over this limit).
%
% The caller supplies the list of words to be printed in the form
% of a list of error message components. Each component may specify
% a string to printed exactly as it is, or it may specify a string
% containing a list of words, which may be broken at white space.
%
%-----------------------------------------------------------------------------%

:- module error_util.
:- interface.

:- import_module zinc_common.
:- import_module tmzn_ast.

:- import_module bool.
:- import_module io.
:- import_module list.
:- import_module maybe.
:- import_module set.

%-----------------------------------------------------------------------------%

:- type error_option
    --->    eo_halt_at_warn
    ;       eo_verbose.

:- type error_options == set(error_option).

%-----------------------------------------------------------------------------%

% Every distinct problem should generate a single error specification. This
% specification should state the severity of the problem (so that we can update
% the exit status of mzn2fzn accordingly), which phase of mzn2fzn found
% the problem (since later phases may wish to suppress some problem reports
% if some specific earlier phases found problems), and a specification
% of what to print.
%
% In most cases, the "what to print" will be a single message for a single
% src_locn. However, we may want to print messages for several src_locns.
% For example, when reporting a duplicate declaration, we want to report
% this fact in the duplicate declaration's src_locn, while printing another
% message giving the original declaration's src_locn.

:- type error_spec
    --->    error_spec(
                error_severity          :: error_severity,
                error_phase             :: error_phase,
                error_msgs              :: list(error_msg)
            ).

:- type error_severity
    --->    severity_internal_error
            % Indicates a problem in the MiniZinc translator itself.
            % Always set the exit status to indicate an error.

    ;       severity_program_error
            % Indicates a problem in the MiniZinc program being translated.
            % Always set the exit status to indicate an error.

    ;       severity_warning
            % Indicates a potential problem in the MiniZinc program being
            % translated. Only set the exit status to indicate an error
            % if --halt-at-warn is enabled.

    ;       severity_informational
            % Indicates something unusual in the MiniZinc program being
            % translated that the user may wish to know. Don't set the exit
            % status to indicate an error.

    ;       severity_conditional(
            % If the given boolean option has the given value, then the actual
            % severity is given by the third argument; if it has the other
            % value, then the actual severity is given by the fourth argument.
            % If the fourth argument is `no', then the error_spec shouldn't
            % actually print anything if cond_option doesn't have the value
            % in cond_option_value.

                cond_option             :: error_option,
                cond_option_value       :: bool,
                cond_if_match           :: error_severity,
                cond_if_no_match        :: maybe(error_severity)
            ).

:- type actual_severity
    --->    actual_severity_error
    ;       actual_severity_warning
    ;       actual_severity_informational.

:- type error_phase
    --->    phase_conversion
    ;       phase_var_decl
    ;       phase_assign
    ;       phase_constraint
    ;       phase_postprocess
    ;       phase_optimization.

% An error message may have several components that may be printed under
% different circumstances. Some components are always printed; some are
% printed only if specific options have specific values. When an error
% specification is printed, we concatenate the list of all the
% format_components that should be printed. If this yields the empty list,
% we print nothing.
%
% When we print an error message in a list of error messages, we normally
% treat the first line of the first message differently than the rest:
% we separate it from the src_locn by one space, whereas following lines
% are separate by three spaces. You can request that the first line of
% a message be treated as it were the first by setting the error_treat_as_first
% field to "treat_as_first". You can also request that the pieces in a message
% be given extra indentation by setting the error_extra_indent field
% to a nonzero value.
%
% The term simple_msg(SrcLocn, Components) is a shorthand for (and equivalent
% in every respect to) the term error_msg(yes(SrcLocn), no, 0, Components).

:- type maybe_treat_as_first
    --->    treat_as_first
    ;       do_not_treat_as_first.

:- type error_msg
    --->    simple_msg(
                simple_src_locn         :: src_locn,
                simple_components       :: list(error_msg_component)
            )
    ;       error_msg(
                error_src_locn          :: maybe(src_locn),
                error_treat_as_first    :: maybe_treat_as_first,
                error_extra_indent      :: int,
                error_components        :: list(error_msg_component)
            ).

:- type error_msg_component
    --->    always(format_components)
            % Print these components under all circumstances.

    ;       option_is_set(error_option, bool, list(error_msg_component)).
            % Print the embedded components only if the specified boolean
            % option has the specified value.

%-----------------------------------------------------------------------------%

    % make_overflow_error(Pred, Phase, SrcPos, Spec)
    %
:- pred make_overflow_error(string::in, error_phase::in, src_pos::in,
    error_spec::out) is det.

    % make_user_error(Pred, Phase, SrcPos, What, Spec)
    %
:- pred make_user_error(string::in, error_phase::in, src_pos::in, string::in,
    error_spec::out) is det.

    % make_internal_error(Pred, Phase, SrcPos, What, Spec)
    %
:- pred make_internal_error(string::in, error_phase::in, src_pos::in,
    string::in, error_spec::out) is det.

    % make_nyi_error(Pred, Phase, SrcPos, What, !Specs)
    %
:- pred make_nyi_error(string::in, error_phase::in, src_pos::in, string::in,
    error_spec::out) is det.

%-----------------------------------------------------------------------------%

    % add_user_error(Pred, Phase, SrcPos, What, !Specs)
    %
:- pred add_user_error(string::in, error_phase::in, src_pos::in, string::in,
    list(error_spec)::in, list(error_spec)::out) is det.

    % add_overflow_error(Pred, Phase, SrcPos, !Specs)
    %
:- pred add_overflow_error(string::in, error_phase::in, src_pos::in,
    list(error_spec)::in, list(error_spec)::out) is det.

    % add_internal_error(Pred, Phase, SrcPos, What, !Specs)
    %
:- pred add_internal_error(string::in, error_phase::in, src_pos::in,
    string::in, list(error_spec)::in, list(error_spec)::out) is det.

    % add_nyi_error(Pred, Phase, SrcPos, What, !Specs)
    %
:- pred add_nyi_error(string::in, error_phase::in, src_pos::in, string::in,
    list(error_spec)::in, list(error_spec)::out) is det.

%-----------------------------------------------------------------------------%

:- pred src_pos_to_locn_pieces(src_pos::in, src_locn::out,
    list(format_component)::out) is det.

%-----------------------------------------------------------------------------%

    % Return the worst of two actual severities.
    %
:- func worst_severity(actual_severity, actual_severity)
    = actual_severity.

    % Compute the actual severity of a message with the given severity
    % (if it actually prints anything).
    %
:- func actual_error_severity(error_options, error_severity)
    = maybe(actual_severity).

    % Compute the worst actual severity (if any) occurring in a list of
    % error_specs.
    %
:- func worst_severity_in_specs(error_options, list(error_spec))
    = maybe(actual_severity).

    % Return `yes' if the given list contains error_specs whose actual severity
    % is actual_severity_error.
    %
:- func contains_errors(error_options, list(error_spec)) = bool.

    % Return `yes' if the given list contains error_specs whose actual severity
    % is actual_severity_error or actual_severity_warning.
    %
:- func contains_errors_and_or_warnings(error_options, list(error_spec))
    = bool.

%-----------------------------------------------------------------------------%

:- pred sort_error_msgs(list(error_msg)::in, list(error_msg)::out) is det.

%-----------------------------------------------------------------------------%

    % write_error_spec(Spec, ErrorOptions, !NumWarnings, !NumErrors, !IO):
    % write_error_specs(Specs, ErrorOptions, !NumWarnings, !NumErrors, !IO):
    %
    % Write out the error message(s) specified by Spec or Specs, minus the
    % parts whose conditions are false. Increment !NumWarnings by the number
    % of printed warnings and !NumErrors by the number of printed errors.
    % Set the exit status to 1 if we found any errors, or if we found any
    % warnings and --halt-at-warn is set. If some error specs have verbose
    % components but they aren't being printed out, set the flag for reminding
    % the user about --verbose-errors.
    %
    % Look up option values in the supplied ErrorOptions.
    %
    % If an error spec contains only conditional messages and those conditions
    % are all false, then nothing will be printed out and the exit status
    % will not be changed.  This will happen even if the severity means
    % that something should have been printed out.
    %
:- pred write_error_spec(error_spec::in, error_options::in,
    int::in, int::out, int::in, int::out, io::di, io::uo) is det.
:- pred write_error_specs(list(error_spec)::in, error_options::in,
    int::in, int::out, int::in, int::out, io::di, io::uo) is det.

%-----------------------------------------------------------------------------%

:- type format_component
    --->    fixed(string)
            % This string should appear in the output in one piece, as it is.

    ;       quote(string)
            % Surround the string with `' quotes, then treat as fixed.

    ;       int_fixed(int)
            % Convert the integer to a string, then treat as fixed.

    ;       nth_fixed(int)
            % Convert the integer to a string, such as "first", "second",
            % "third", "4th", "5th" and then treat as fixed.

    ;       lower_case_next_if_not_first
            % If this is the first component, ignore it. If this is not
            % the first component, lower case the initial letter of the
            % next component. There is no effect if the next component
            % does not exist or does not start with an upper case letter.

    ;       prefix(string)
            % This string should appear in the output in one piece, as it is,
            % inserted directly before the next format_component, without
            % any intervening space.

    ;       suffix(string)
            % This string should appear in the output in one piece, as it is,
            % appended directly after the previous format_component, without
            % any intervening space.

    ;       words(string)
            % This string contains words separated by white space. The words
            % should appear in the output in the given order, but the white
            % space may be rearranged and line breaks may be inserted.

    ;       words_quote(string)
            % Surround the string with `' quotes, then treat as words.

    ;       nl
            % Insert a line break if there has been text output since
            % the last line break.

    ;       nl_indent_delta(int)
            % Act as nl, but also add the given integer (which should be a
            % small positive or negative integer) to the current indent level.

    ;       blank_line.
            % Create a blank line.

:- type format_components == list(format_component).

    % Wrap words() around a string.
    %
:- func string_to_words_piece(string) = format_component.

    % Convert a list of strings into a list of format_components
    % separated by commas, with the last two elements separated by `and'.
    %
:- func list_to_pieces(list(string)) = list(format_component).

    % Convert a list of lists of format_components into a list of
    % format_components separated by commas, with the last two elements
    % separated by `and'.
    %
:- func component_lists_to_pieces(list(list(format_component))) =
    list(format_component).

    % Convert a list of format_components into a list of format_components
    % separated by commas, with the last two elements separated by `and'.
    %
:- func component_list_to_pieces(list(format_component)) =
    list(format_component).

    % component_list_to_line_pieces(Lines, Final):
    %
    % Convert Lines, a list of lines (each given by a list of format_components
    % *without* a final nl) into a condensed list of format_components
    % in which adjacent lines are separated by commas and newlines.
    % What goes between the last line and the newline ending is not
    % a comma but the value of Final.
    %
:- func component_list_to_line_pieces(list(list(format_component)),
    list(format_component)) = list(format_component).

    % choose_number(List, Singular, Plural) = Form
    %
    % Choose between a singular version and a plural version of something,
    % based on the length of a list.  Chooses the plural if the list is empty.
    %
:- func choose_number(list(T), U, U) = U.

    % is_or_are(List) throws an exception if the list is empty, returns "is"
    % if the list is a singleton, and otherwise returns "are".
    %
:- func is_or_are(list(T)) = string.

%-----------------------------------------------------------------------------%

    % Put `' quotes around the given string.
    %
:- func add_quotes(string) = string.

    % Ensure that the first character of the input string is not a lower case
    % letter.
    %
:- func capitalize(string) = string.

%-----------------------------------------------------------------------------%

    % Report why the file is not able to be opened,
    % and set the exit status to be 1.
    %
:- pred unable_to_open_file(string::in, io.error::in, io::di, io::uo) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module char.
:- import_module cord.
:- import_module int.
:- import_module require.
:- import_module string.

%-----------------------------------------------------------------------------%

make_overflow_error(Pred, Phase, SrcPos, Spec) :-
    ArchSize = int.bits_per_int,
    ArchSizeStr = string.int_to_string(ArchSize),
    src_pos_to_locn_pieces(SrcPos, SrcLocn, PosPieces),
    MsgPieces = [words("the bounds on this expression"),
        words("exceed what can be represented on a"),
        fixed(ArchSizeStr), suffix("-bit"), words("machine."), nl],
    DetectedPieces = [words("(Detected by"), fixed(Pred), suffix(":)"), nl],
    Pieces = PosPieces ++ MsgPieces ++ DetectedPieces,
    Msg = simple_msg(SrcLocn, [always(Pieces)]),
    Spec = error_spec(severity_program_error, Phase, [Msg]).

make_user_error(Pred, Phase, SrcPos, What, Spec) :-
    src_pos_to_locn_pieces(SrcPos, SrcLocn, PosPieces),
    % XXX After half-reification becomes the standard translation method
    % for ordinary users (as opposed to implementors), we won't need to print
    % the predicate name.
    SorryPieces = [words("User error detected in"), words(Pred), suffix(":"),
        words(What), suffix("."), nl],
    Msg = simple_msg(SrcLocn, [always(PosPieces ++ SorryPieces)]),
    Spec = error_spec(severity_internal_error, Phase, [Msg]).

make_internal_error(Pred, Phase, SrcPos, What, Spec) :-
    src_pos_to_locn_pieces(SrcPos, SrcLocn, PosPieces),
    SorryPieces = [words("Internal error in"), words(Pred), suffix(":"),
        words(What), suffix("."), nl],
    Msg = simple_msg(SrcLocn, [always(PosPieces ++ SorryPieces)]),
    Spec = error_spec(severity_internal_error, Phase, [Msg]).

make_nyi_error(Pred, Phase, SrcPos, What, Spec) :-
    src_pos_to_locn_pieces(SrcPos, SrcLocn, PosPieces),
    SorryPieces = [words("Sorry, not yet implemented in"),
        words(Pred), suffix(":"), words(What), suffix("."), nl],
    Msg = simple_msg(SrcLocn, [always(PosPieces ++ SorryPieces)]),
    Spec = error_spec(severity_internal_error, Phase, [Msg]).

%-----------------------------------------------------------------------------%

add_overflow_error(Pred, Phase, SrcPos, !Specs) :-
    make_overflow_error(Pred, Phase, SrcPos, Spec),
    !:Specs = [Spec | !.Specs].

add_user_error(Pred, Phase, SrcPos, What, !Specs) :-
    make_user_error(Pred, Phase, SrcPos, What, Spec),
    !:Specs = [Spec | !.Specs].

add_internal_error(Pred, Phase, SrcPos, What, !Specs) :-
    make_internal_error(Pred, Phase, SrcPos, What, Spec),
    !:Specs = [Spec | !.Specs].

add_nyi_error(Pred, Phase, SrcPos, What, !Specs) :-
    make_nyi_error(Pred, Phase, SrcPos, What, Spec),
    !:Specs = [Spec | !.Specs].

%-----------------------------------------------------------------------------%

src_pos_to_locn_pieces(SrcPos, SrcLocn, Pieces) :-
    SrcPos = src_pos(NestPos, SrcLocn),
    (
        NestPos = outermost(OuterPos),
        (
            SrcLocn = src_locn(_, _),
            In = "In"
        ;
            SrcLocn = builtin,
            In = "In builtin"
        ;
            SrcLocn = unknown,
            In = "In unknown"
        ),
        (
            OuterPos = op_var_decl,
            OuterDesc = "variable declaration"
        ;
            OuterPos = op_assign(assign_explicit),
            OuterDesc = "assignment"
        ;
            OuterPos = op_assign(assign_from_var_decl),
            OuterDesc = "assignment implicit in variable initialization"
        ;
            OuterPos = op_constraint(constr_explicit),
            OuterDesc = "constraint"
        ;
            OuterPos = op_constraint(constr_from_var_decl),
            OuterDesc = "constraint implicit in variable initialization"
        ;
            OuterPos = op_constraint(constr_from_assign),
            OuterDesc = "constraint implicit in assignment"
        ;
            OuterPos = op_output,
            OuterDesc = "output item"
        ;
            OuterPos = op_solve,
            OuterDesc = "solve item"
        ;
            OuterPos = op_predfunc,
            OuterDesc = "predfunc item"
        ;
            OuterPos = op_enum,
            OuterDesc = "enum item"
        ;
            OuterPos = op_type_inst_syn,
            OuterDesc = "type_inst_syn item"
        ;
            OuterPos = op_annotation,
            OuterDesc = "annotation item"
        ),
        Pieces = [words(In), words(OuterDesc), suffix(":"), nl]
    ;
        NestPos = nest(OuterSrcPos, InnerStep),
        src_pos_to_locn_pieces(OuterSrcPos, _OuterSrcLocn, OuterPieces),
        (
            InnerStep = is_constr_expr,
            InnerPieces = []
        ;
            InnerStep = is_var_decl_init,
            InnerPieces = [words("in the initial value expression:")]
        ;
            InnerStep = is_init_index_type(N),
            InnerPieces = [words("in the"), nth_fixed(N), words("index type")]
        ;
            InnerStep = is_init_elt_type,
            InnerPieces = [words("in the element type:")]
        ;
            InnerStep = is_simple_array(N),
            InnerPieces = [words("in the"), nth_fixed(N),
                words("array element:")]
        ;
            InnerStep = is_lit_set(N),
            InnerPieces = [words("in the"), nth_fixed(N),
                words("set element:")]
        ;
            InnerStep = is_unop_arg(OpStr),
            InnerPieces = [words("in the argument of the unary operator"),
                fixed(OpStr), suffix(":")]
        ;
            InnerStep = is_binop_arg(OpStr, Which),
            (
                Which = left, WhichStr = "left"
            ;
                Which = right, WhichStr = "right"
            ),
            InnerPieces = [words("in the"), words(WhichStr),
                words("argument of the binary operator"),
                fixed(OpStr), suffix(":")]
        ;
            InnerStep = is_array_id,
            InnerPieces = [words("in the array id:")]
        ;
            InnerStep = is_index(N),
            InnerPieces = [words("in the"), nth_fixed(N),
                words("index expression:")]
        ;
            InnerStep = is_arg(PredName, N),
            InnerPieces = [words("in the"), nth_fixed(N),
                words("argument of the call to"), fixed(PredName), suffix(":")]
        ;
            InnerStep = is_compre_cond,
            InnerPieces = [words("in the comprehension condition:")]
        ;
            InnerStep = is_compre_head,
            InnerPieces = [words("in the comprehension head:")]
        ;
            InnerStep = is_compre_array(N),
            InnerPieces = [words("in the"), nth_fixed(N),
                words("generator of the comprehension:")]
        ;
            InnerStep = is_cond,
            InnerPieces = [words("in the condition:")]
        ;
            InnerStep = is_then,
            InnerPieces = [words("in the then-part:")]
        ;
            InnerStep = is_else,
            InnerPieces = [words("in the else-part:")]
        ),
        Pieces = OuterPieces ++ InnerPieces
    ).

%-----------------------------------------------------------------------------%

worst_severity(actual_severity_error, actual_severity_error) =
    actual_severity_error.
worst_severity(actual_severity_error, actual_severity_warning) =
    actual_severity_error.
worst_severity(actual_severity_error, actual_severity_informational) =
    actual_severity_error.
worst_severity(actual_severity_warning, actual_severity_error) =
    actual_severity_error.
worst_severity(actual_severity_warning, actual_severity_warning) =
    actual_severity_warning.
worst_severity(actual_severity_warning, actual_severity_informational) =
    actual_severity_warning.
worst_severity(actual_severity_informational, actual_severity_error) =
    actual_severity_error.
worst_severity(actual_severity_informational, actual_severity_warning) =
    actual_severity_warning.
worst_severity(actual_severity_informational, actual_severity_informational) =
    actual_severity_informational.

actual_error_severity(ErrorOptions, Severity) = MaybeActual :-
    (
        Severity = severity_internal_error,
        MaybeActual = yes(actual_severity_error)
    ;
        Severity = severity_program_error,
        MaybeActual = yes(actual_severity_error)
    ;
        Severity = severity_warning,
        MaybeActual = yes(actual_severity_warning)
    ;
        Severity = severity_informational,
        MaybeActual = yes(actual_severity_informational)
    ;
        Severity = severity_conditional(Option, MatchValue,
            Match, MaybeNoMatch),
        set.is_member(Option, ErrorOptions, ActualValue),
        ( ActualValue = MatchValue ->
            MaybeActual = actual_error_severity(ErrorOptions, Match)
        ;
            (
                MaybeNoMatch = no,
                MaybeActual = no
            ;
                MaybeNoMatch = yes(NoMatch),
                MaybeActual = actual_error_severity(ErrorOptions, NoMatch)
            )
        )
    ).

worst_severity_in_specs(ErrorOptions, Specs) = MaybeWorst :-
    worst_severity_in_specs_2(ErrorOptions, Specs, no, MaybeWorst).

:- pred worst_severity_in_specs_2(error_options::in, list(error_spec)::in,
    maybe(actual_severity)::in, maybe(actual_severity)::out) is det.

worst_severity_in_specs_2(_ErrorOptions, [], !MaybeWorst).
worst_severity_in_specs_2(ErrorOptions, [Spec | Specs], !MaybeWorst) :-
    Spec = error_spec(Severity, _, _),
    MaybeThis = actual_error_severity(ErrorOptions, Severity),
    (
        !.MaybeWorst = no,
        !:MaybeWorst = MaybeThis
    ;
        !.MaybeWorst = yes(_Worst),
        MaybeThis = no
    ;
        !.MaybeWorst = yes(Worst),
        MaybeThis = yes(This),
        !:MaybeWorst = yes(worst_severity(Worst, This))
    ),
    worst_severity_in_specs_2(ErrorOptions, Specs, !MaybeWorst).

contains_errors(ErrorOptions, Specs) = Errors :-
    MaybeWorstActual = worst_severity_in_specs(ErrorOptions, Specs),
    (
        MaybeWorstActual = no,
        Errors = no
    ;
        MaybeWorstActual = yes(WorstActual),
        (
            WorstActual = actual_severity_error,
            Errors = yes
        ;
            ( WorstActual = actual_severity_warning
            ; WorstActual = actual_severity_informational
            ),
            Errors = no
        )
    ).

contains_errors_and_or_warnings(ErrorOptions, Specs) = ErrorsOrWarnings :-
    MaybeWorstActual = worst_severity_in_specs(ErrorOptions, Specs),
    (
        MaybeWorstActual = no,
        ErrorsOrWarnings = no
    ;
        MaybeWorstActual = yes(WorstActual),
        (
            ( WorstActual = actual_severity_error
            ; WorstActual = actual_severity_warning
            ),
            ErrorsOrWarnings = yes
        ;
            WorstActual = actual_severity_informational,
            ErrorsOrWarnings = no
        )
    ).

%-----------------------------------------------------------------------------%

sort_error_msgs(Msgs0, Msgs) :-
    list.sort_and_remove_dups(compare_error_msgs, Msgs0, Msgs).

:- func project_msgs_src_locns(list(error_msg)) = list(src_locn).

project_msgs_src_locns([]) = [].
project_msgs_src_locns([Msg | Msgs]) = SrcLocns :-
    TailSrcLocns = project_msgs_src_locns(Msgs),
    MaybeSrcLocn = project_msg_src_locn(Msg),
    (
        MaybeSrcLocn = yes(SrcLocn),
        SrcLocns = [SrcLocn | TailSrcLocns]
    ;
        MaybeSrcLocn = no,
        SrcLocns = TailSrcLocns
    ).

:- pred compare_error_msgs(error_msg::in, error_msg::in,
    comparison_result::out) is det.

compare_error_msgs(MsgA, MsgB, Result) :-
    MaybeSrcLocnA = project_msg_src_locn(MsgA),
    MaybeSrcLocnB = project_msg_src_locn(MsgB),
    compare(SrcLocnResult, MaybeSrcLocnA, MaybeSrcLocnB),
    (
        SrcLocnResult = (=),
        compare(Result, MsgA, MsgB)
    ;
        ( SrcLocnResult = (>)
        ; SrcLocnResult = (<)
        ),
        Result = SrcLocnResult
    ).

:- func project_msg_src_locn(error_msg) = maybe(src_locn).

project_msg_src_locn(Msg) = MaybeSrcLocn :-
    (
        Msg = simple_msg(SrcLocn, _),
        MaybeSrcLocn = yes(SrcLocn)
    ;
        Msg = error_msg(yes(SrcLocn), _, _, _),
        MaybeSrcLocn = yes(SrcLocn)
    ;
        Msg = error_msg(no, _, _, __),
        MaybeSrcLocn = no
    ).

%-----------------------------------------------------------------------------%

:- pred sort_error_specs(list(error_spec)::in, list(error_spec)::out) is det.

sort_error_specs(Specs0, Specs) :-
    list.sort_and_remove_dups(compare_error_specs, Specs0, Specs).

:- pred compare_error_specs(error_spec::in, error_spec::in,
    comparison_result::out) is det.

compare_error_specs(SpecA, SpecB, Result) :-
    SpecA = error_spec(_, _, MsgsA),
    SpecB = error_spec(_, _, MsgsB),
    SrcLocnsA = project_msgs_src_locns(MsgsA),
    SrcLocnsB = project_msgs_src_locns(MsgsB),
    compare(SrcLocnResult, SrcLocnsA, SrcLocnsB),
    ( SrcLocnResult = (=) ->
        compare(Result, SpecA, SpecB)
    ;
        Result = SrcLocnResult
    ).

%-----------------------------------------------------------------------------%

write_error_spec(Spec, ErrorOptions, !NumWarnings, !NumErrors, !IO) :-
    do_write_error_spec(ErrorOptions, Spec, !NumWarnings, !NumErrors, !IO).

write_error_specs(Specs0, ErrorOptions, !NumWarnings, !NumErrors, !IO) :-
    sort_error_specs(Specs0, Specs),
    list.foldl3(do_write_error_spec(ErrorOptions), Specs,
        !NumWarnings, !NumErrors, !IO).

:- pred do_write_error_spec(error_options::in, error_spec::in,
    int::in, int::out, int::in, int::out, io::di, io::uo) is det.

do_write_error_spec(ErrorOptions, Spec, !NumWarnings, !NumErrors, !IO) :-
    Spec = error_spec(Severity, _, Msgs),
    do_write_error_msgs(Msgs, ErrorOptions, treat_as_first,
        have_not_printed_anything, PrintedSome, !IO),
    MaybeActual = actual_error_severity(ErrorOptions, Severity),
    (
        PrintedSome = have_not_printed_anything
        % XXX The following assertion is commented out because the compiler
        % can generate error specs that consist only of conditional error
        % messages whose conditions can all be false (in which case nothing
        % will be printed).  Such specs will cause the assertion to fail if
        % they have a severity that means something *should* have been
        % printed out.  Error specs like this are generated by --debug-modes.
        % expect(unify(MaybeActual, no), $module, $pred,
        %    "MaybeActual isn't no")
    ;
        PrintedSome = printed_something,
        (
            MaybeActual = yes(Actual),
            (
                Actual = actual_severity_error,
                !:NumErrors = !.NumErrors + 1,
                io.set_exit_status(1, !IO)
            ;
                Actual = actual_severity_warning,
                !:NumWarnings = !.NumWarnings + 1
            ;
                Actual = actual_severity_informational
            )
        ;
            MaybeActual = no,
            unexpected($module, $pred, "MaybeActual is no")
        )
    ).

:- type maybe_printed_something
    --->    printed_something
    ;       have_not_printed_anything.

:- type maybe_lower_next_initial
    --->    lower_next_initial
    ;       do_not_lower_next_initial.

:- pred do_write_error_msgs(list(error_msg)::in, error_options::in,
    maybe_treat_as_first::in,
    maybe_printed_something::in, maybe_printed_something::out,
    io::di, io::uo) is det.

do_write_error_msgs([], _ErrorOptions, _First, !PrintedSome, !IO).
do_write_error_msgs([Msg | Msgs], ErrorOptions, !.First, !PrintedSome, !IO) :-
    (
        Msg = simple_msg(SimpleSrcLocn, Components),
        MaybeSrcLocn = yes(SimpleSrcLocn),
        TreatAsFirst = do_not_treat_as_first,
        ExtraIndentLevel = 0
    ;
        Msg = error_msg(MaybeSrcLocn, TreatAsFirst, ExtraIndentLevel,
            Components)
    ),
    (
        TreatAsFirst = treat_as_first,
        !:First = treat_as_first
    ;
        TreatAsFirst = do_not_treat_as_first
        % Leave !:First as it is, even if it is treat_as_first.
    ),
    Indent = ExtraIndentLevel * indent_increment,
    write_msg_components(Components, MaybeSrcLocn, Indent, ErrorOptions,
        !First, !PrintedSome, !IO),
    do_write_error_msgs(Msgs, ErrorOptions, !.First, !PrintedSome, !IO).

:- pred write_msg_components(list(error_msg_component)::in,
    maybe(src_locn)::in, int::in, error_options::in,
    maybe_treat_as_first::in, maybe_treat_as_first::out,
    maybe_printed_something::in, maybe_printed_something::out,
    io::di, io::uo) is det.

write_msg_components([], _, _, _, !First, !PrintedSome, !IO).
write_msg_components([Component | Components], MaybeSrcLocn, Indent,
        ErrorOptions, !First, !PrintedSome, !IO) :-
    (
        Component = always(ComponentPieces),
        % XXX Should we make MaxWidth configurable?
        MaxWidth = 80,
        do_write_error_pieces(!.First, MaybeSrcLocn, Indent, MaxWidth,
            ComponentPieces, !IO),
        !:First = do_not_treat_as_first,
        !:PrintedSome = printed_something
    ;
        Component = option_is_set(Option, RequiredValue, EmbeddedComponents),
        set.is_member(Option, ErrorOptions, ActualValue),
        ( if ActualValue = RequiredValue then
            write_msg_components(EmbeddedComponents, MaybeSrcLocn, Indent,
                ErrorOptions, !First, !PrintedSome, !IO)
        else
            true
        )
    ),
    write_msg_components(Components, MaybeSrcLocn, Indent, ErrorOptions,
        !First, !PrintedSome, !IO).

%-----------------------------------------------------------------------------%

:- type maybe_first_in_msg
    --->    first_in_msg
    ;       not_first_in_msg.

string_to_words_piece(Str) = words(Str).

list_to_pieces([]) = [].
list_to_pieces([Elem]) = [words(Elem)].
list_to_pieces([Elem1, Elem2]) = [fixed(Elem1), words("and"), fixed(Elem2)].
list_to_pieces([Elem1, Elem2, Elem3 | Elems]) =
    [fixed(Elem1 ++ ",") | list_to_pieces([Elem2, Elem3 | Elems])].

component_lists_to_pieces([]) = [].
component_lists_to_pieces([Comps]) = Comps.
component_lists_to_pieces([Comps1, Comps2]) =
    Comps1 ++ [words("and")] ++ Comps2.
component_lists_to_pieces([Comps1, Comps2, Comps3 | Comps]) =
    Comps1 ++ [suffix(",")]
    ++ component_lists_to_pieces([Comps2, Comps3 | Comps]).

component_list_to_pieces([]) = [].
component_list_to_pieces([Comp]) = [Comp].
component_list_to_pieces([Comp1, Comp2]) = [Comp1, words("and"), Comp2].
component_list_to_pieces([Comp1, Comp2, Comp3 | Comps]) =
    [Comp1, suffix(",")]
    ++ component_list_to_pieces([Comp2, Comp3 | Comps]).

component_list_to_line_pieces([], _) = [].
component_list_to_line_pieces([Comps], Final) = Comps ++ Final ++ [nl].
component_list_to_line_pieces([Comps1, Comps2 | CompLists], Final) =
    Comps1 ++ [suffix(","), nl]
    ++ component_list_to_line_pieces([Comps2 | CompLists], Final).

choose_number([], _Singular, Plural) = Plural.
choose_number([_], Singular, _Plural) = Singular.
choose_number([_, _ | _], _Singular, Plural) = Plural.

is_or_are([]) = "" :-
    unexpected($module, $pred, "[]").
is_or_are([_]) = "is".
is_or_are([_, _ | _]) = "are".

:- pred do_write_error_pieces(maybe_treat_as_first::in,
    maybe(src_locn)::in, int::in, int::in, list(format_component)::in,
    io::di, io::uo) is det.

do_write_error_pieces(TreatAsFirst, MaybeSrcLocn, FixedIndent, MaxWidth,
        Components, !IO) :-
    % The fixed characters at the start of the line are:
    % filename
    % :
    % line number (min 3 chars)
    % :
    % space
    % indent
    (
        MaybeSrcLocn = yes(SrcLocn),
        (
            SrcLocn = src_locn(FileName, LineNumber),
            string.format("%s:%03d: ", [s(FileName), i(LineNumber)],
                SrcLocnStr)
        ;
            SrcLocn = builtin,
            SrcLocnStr = "builtin: "
        ;
            SrcLocn = unknown,
            SrcLocnStr = "unknown: "
        )
    ;
        MaybeSrcLocn = no,
        SrcLocnStr = ""
    ),
    string.count_codepoints(SrcLocnStr, SrcLocnLength),
    convert_components_to_paragraphs(Components, Paragraphs),
    FirstIndent = (TreatAsFirst = treat_as_first -> 0 ; 1),
    Remain = MaxWidth - (SrcLocnLength + FixedIndent),
    group_words(TreatAsFirst, FirstIndent, Paragraphs, Remain, Lines),
    write_lines(Lines, SrcLocnStr, FixedIndent, !IO).

:- func indent_increment = int.

indent_increment = 2.

:- pred write_lines(list(error_line)::in, string::in, int::in,
    io::di, io::uo) is det.

write_lines([], _, _, !IO).
write_lines([Line | Lines], SrcLocnStr, FixedIndent, !IO) :-
    io.write_string(SrcLocnStr, !IO),
    Line = error_line(LineIndent, LineWords),
    Indent = FixedIndent + LineIndent * indent_increment,
    string.pad_left("", ' ', Indent, IndentStr),
    io.write_string(IndentStr, !IO),
    error_util.write_line(LineWords, !IO),
    write_lines(Lines, SrcLocnStr, FixedIndent, !IO).

:- pred write_line(list(string)::in, io::di, io::uo) is det.

write_line([], !IO) :-
    io.write_char('\n', !IO).
write_line([Word | Words], !IO) :-
    io.write_string(Word, !IO),
    write_line_rest(Words, !IO),
    io.write_char('\n', !IO).

:- pred write_line_rest(list(string)::in, io::di, io::uo) is det.

write_line_rest([], !IO).
write_line_rest([Word | Words], !IO) :-
    io.write_char(' ', !IO),
    io.write_string(Word, !IO),
    write_line_rest(Words, !IO).

:- func nth_fixed_str(int) = string.

nth_fixed_str(N) =
    ( if N = 1 then
        "first"
    else if N = 2 then
        "second"
    else if N = 3 then
        "third"
    else
        int_to_string(N) ++ "th"
    ).

:- func join_string_and_tail(string, list(format_component), string) = string.

join_string_and_tail(Word, Components, TailStr) = Str :-
    ( if TailStr = "" then
        Str = Word
    else if Components = [suffix(_) | _] then
        Str = Word ++ TailStr
    else
        Str = Word ++ " " ++ TailStr
    ).

%----------------------------------------------------------------------------%

:- type paragraph
    --->    paragraph(
                % The list of words to print in the paragraph.
                % It should not be empty.
                list(string),

                % The number of blank lines to print after the paragraph.
                int,

                % The indent delta to apply for the next paragraph.
                int
            ).

:- pred convert_components_to_paragraphs(list(format_component)::in,
    list(paragraph)::out) is det.

convert_components_to_paragraphs(Components, Paras) :-
    convert_components_to_paragraphs_acc(first_in_msg, Components,
        [], cord.empty, ParasCord),
    Paras = cord.list(ParasCord).

:- type word
    --->    plain_word(string)
    ;       prefix_word(string)
    ;       suffix_word(string)
    ;       lower_next_word.

:- pred convert_components_to_paragraphs_acc(maybe_first_in_msg::in,
    list(format_component)::in, list(word)::in,
    cord(paragraph)::in, cord(paragraph)::out) is det.

convert_components_to_paragraphs_acc(_, [], RevWords0, !Paras) :-
    Strings = rev_words_to_strings(RevWords0),
    !:Paras = snoc(!.Paras, paragraph(Strings, 0, 0)).
convert_components_to_paragraphs_acc(FirstInMsg, [Component | Components],
        RevWords0, !Paras) :-
    (
        Component = words(WordsStr),
        break_into_words(WordsStr, RevWords0, RevWords1)
    ;
        Component = words_quote(WordsStr),
        break_into_words(add_quotes(WordsStr), RevWords0, RevWords1)
    ;
        Component = fixed(Word),
        RevWords1 = [plain_word(Word) | RevWords0]
    ;
        Component = quote(Word),
        RevWords1 = [plain_word(add_quotes(Word)) | RevWords0]
    ;
        Component = int_fixed(Int),
        RevWords1 = [plain_word(int_to_string(Int)) | RevWords0]
    ;
        Component = nth_fixed(Int),
        RevWords1 = [plain_word(nth_fixed_str(Int)) | RevWords0]
    ;
        Component = lower_case_next_if_not_first,
        (
            FirstInMsg = first_in_msg,
            RevWords1 = RevWords0
        ;
            FirstInMsg = not_first_in_msg,
            RevWords1 = [lower_next_word | RevWords0]
        )
    ;
        Component = prefix(Word),
        RevWords1 = [prefix_word(Word) | RevWords0]
    ;
        Component = suffix(Word),
        RevWords1 = [suffix_word(Word) | RevWords0]
    ;
        Component = nl,
        Strings = rev_words_to_strings(RevWords0),
        !:Paras = snoc(!.Paras, paragraph(Strings, 0, 0)),
        RevWords1 = []
    ;
        Component = nl_indent_delta(IndentDelta),
        Strings = rev_words_to_strings(RevWords0),
        !:Paras = snoc(!.Paras, paragraph(Strings, 0, IndentDelta)),
        RevWords1 = []
    ;
        Component = blank_line,
        Strings = rev_words_to_strings(RevWords0),
        !:Paras = snoc(!.Paras, paragraph(Strings, 1, 0)),
        RevWords1 = []
    ),
    convert_components_to_paragraphs_acc(not_first_in_msg, Components,
        RevWords1, !Paras).

:- type plain_or_prefix
    --->    plain(string)
    ;       prefix(string)
    ;       lower_next.

:- func rev_words_to_strings(list(word)) = list(string).

rev_words_to_strings(RevWords) = Strings :-
    PorPs = list.reverse(rev_words_to_rev_plain_or_prefix(RevWords)),
    Strings = join_prefixes(PorPs).

:- func rev_words_to_rev_plain_or_prefix(list(word)) = list(plain_or_prefix).

rev_words_to_rev_plain_or_prefix([]) = [].
rev_words_to_rev_plain_or_prefix([Word | Words]) = PorPs :-
    (
        Word = plain_word(String),
        PorPs = [plain(String) | rev_words_to_rev_plain_or_prefix(Words)]
    ;
        Word = lower_next_word,
        PorPs = [lower_next | rev_words_to_rev_plain_or_prefix(Words)]
    ;
        Word = prefix_word(Prefix),
        PorPs = [prefix(Prefix) | rev_words_to_rev_plain_or_prefix(Words)]
    ;
        Word = suffix_word(Suffix),
        (
            Words = [],
            PorPs = [plain(Suffix)]
        ;
            Words = [plain_word(String) | Tail],
            PorPs = [plain(String ++ Suffix)
                | rev_words_to_rev_plain_or_prefix(Tail)]
        ;
            Words = [lower_next_word | Tail],
            % Convert the lower_next_word/suffix combination into just the
            % suffix after lowercasing the suffix (which will probably have
            % no effect, since the initial character of a suffix is usually
            % not a letter).
            NewWords = [suffix_word(lower_initial(Suffix)) | Tail],
            PorPs = rev_words_to_rev_plain_or_prefix(NewWords)
        ;
            Words = [prefix_word(Prefix) | Tail],
            % Convert the prefix/suffix combination into a plain word.
            % We could convert it into a prefix, but since prefix/suffix
            % combinations shouldn't come up at all, what we do here probably
            % doesn't matter.
            PorPs = [plain(Prefix ++ Suffix)
                | rev_words_to_rev_plain_or_prefix(Tail)]
        ;
            Words = [suffix_word(MoreSuffix) | Tail],
            PorPs = rev_words_to_rev_plain_or_prefix(
                [suffix_word(MoreSuffix ++ Suffix) | Tail])
        )
    ).

:- func join_prefixes(list(plain_or_prefix)) = list(string).

join_prefixes([]) = [].
join_prefixes([Head | Tail]) = Strings :-
    TailStrings = join_prefixes(Tail),
    (
        Head = plain(String),
        Strings = [String | TailStrings]
    ;
        Head = prefix(Prefix),
        (
            TailStrings = [First | Later],
            Strings = [Prefix ++ First | Later]
        ;
            TailStrings = [],
            Strings = [Prefix | TailStrings]
        )
    ;
        Head = lower_next,
        (
            TailStrings = [],
            Strings = TailStrings
        ;
            TailStrings = [FirstTailString | LaterTailStrings],
            Strings = [lower_initial(FirstTailString) | LaterTailStrings]
        )
    ).

:- func lower_initial(string) = string.

lower_initial(Str0) = Str :-
    (
        string.first_char(Str0, First, Rest),
        char.is_upper(First)
    ->
        char.to_lower(First, LoweredFirst),
        string.first_char(Str, LoweredFirst, Rest)
    ;
        Str = Str0
    ).

:- pred break_into_words(string::in, list(word)::in, list(word)::out) is det.

break_into_words(String, Words0, Words) :-
    break_into_words_from(String, 0, Words0, Words).

:- pred break_into_words_from(string::in, int::in, list(word)::in,
    list(word)::out) is det.

break_into_words_from(String, Cur, Words0, Words) :-
    ( find_word_start(String, Cur, Start) ->
        find_word_end(String, Start, End),
        string.between(String, Start, End, WordStr),
        break_into_words_from(String, End, [plain_word(WordStr) | Words0],
            Words)
    ;
        Words = Words0
    ).

:- pred find_word_start(string::in, int::in, int::out) is semidet.

find_word_start(String, Cur, WordStart) :-
    string.unsafe_index_next(String, Cur, Next, Char),
    ( char.is_whitespace(Char) ->
        find_word_start(String, Next, WordStart)
    ;
        WordStart = Cur
    ).

:- pred find_word_end(string::in, int::in, int::out) is det.

find_word_end(String, Cur, WordEnd) :-
    ( string.unsafe_index_next(String, Cur, Next, Char) ->
        ( if char.is_whitespace(Char) then
            WordEnd = Cur
        else
            find_word_end(String, Next, WordEnd)
        )
    ;
        WordEnd = Cur
    ).

%----------------------------------------------------------------------------%

:- type error_line
    --->    error_line(
                % Indent level; multiply by indent_increment to get
                % the number of spaces of indentation.
                int,

                % The words on the line.
                list(string)
            ).

    % Groups the given words into lines. The first line can have up to Max
    % characters on it; the later lines (if any) up to Max-2 characters.
    % The given list of paragraphs must be nonempty, since we always return
    % at least one line.
    %
:- pred group_words(maybe_treat_as_first::in, int::in, list(paragraph)::in,
    int::in, list(error_line)::out) is det.

group_words(TreatAsFirst, CurIndent, Paras, Max, Lines) :-
    (
        Paras = [],
        Lines = []
    ;
        Paras = [FirstPara | LaterParas],
        FirstPara = paragraph(FirstParaWords, NumBlankLines, FirstIndentDelta),
        (
            TreatAsFirst = treat_as_first,
            RestIndent = CurIndent + 1
        ;
            TreatAsFirst = do_not_treat_as_first,
            RestIndent = CurIndent
        ),
        NextIndent = RestIndent + FirstIndentDelta,

        BlankLine = error_line(CurIndent, []),
        list.duplicate(NumBlankLines, BlankLine, BlankLines),
        (
            FirstParaWords = [],
            group_words(TreatAsFirst, NextIndent, LaterParas, Max, RestLines),
            Lines = BlankLines ++ RestLines
        ;
            FirstParaWords = [FirstWord | LaterWords],
            get_line_of_words(FirstWord, LaterWords, CurIndent, Max,
                LineWords, RestWords),
            CurLine = error_line(CurIndent, LineWords),

            group_nonfirst_line_words(RestWords, RestIndent, Max,
                ParaRestLines),
            ParaLines = [CurLine | ParaRestLines],

            group_words(do_not_treat_as_first, NextIndent, LaterParas,
                Max, RestLines),
            Lines = ParaLines ++ BlankLines ++ RestLines
        )
    ).

:- pred group_nonfirst_line_words(list(string)::in, int::in, int::in,
    list(error_line)::out) is det.

group_nonfirst_line_words(Words, Indent, Max, Lines) :-
    (
        Words = [],
        Lines = []
    ;
        Words = [FirstWord | LaterWords],
        get_line_of_words(FirstWord, LaterWords, Indent, Max,
            LineWords, RestWords),
        Line = error_line(Indent, LineWords),
        group_nonfirst_line_words(RestWords, Indent, Max, RestLines),
        Lines = [Line | RestLines]
    ).

:- pred get_line_of_words(string::in, list(string)::in, int::in, int::in,
    list(string)::out, list(string)::out) is det.

get_line_of_words(FirstWord, LaterWords, Indent, Max, Line, RestWords) :-
    string.count_codepoints(FirstWord, FirstWordLen),
    Avail = Max - Indent * indent_increment,
    get_later_words(LaterWords, FirstWordLen, Avail, [FirstWord],
        Line, RestWords).

:- pred get_later_words(list(string)::in, int::in, int::in,
    list(string)::in, list(string)::out, list(string)::out) is det.

get_later_words([], _, _, Line, Line, []).
get_later_words([Word | Words], OldLen, Avail, Line0, Line, RestWords) :-
    string.count_codepoints(Word, WordLen),
    NewLen = OldLen + 1 + WordLen,
    ( if NewLen =< Avail then
        list.append(Line0, [Word], Line1),
        get_later_words(Words, NewLen, Avail, Line1, Line, RestWords)
    else
        Line = Line0,
        RestWords = [Word | Words]
    ).

%-----------------------------------------------------------------------------%

add_quotes(Str) = "`" ++ Str ++ "'".

capitalize(Str0) = Str :-
    Chars0 = string.to_char_list(Str0),
    ( if
        Chars0 = [Char0 | TailChars],
        char.is_lower(Char0),
        Char = char.to_upper(Char0)
    then
        Chars = [Char | TailChars],
        Str = string.from_char_list(Chars)
    else
        Str = Str0
    ).

%-----------------------------------------------------------------------------%

unable_to_open_file(FileName, IOErr, !IO) :-
    io.stderr_stream(StdErr, !IO),
    io.write_string(StdErr, "Unable to open file: '", !IO),
    io.write_string(StdErr, FileName, !IO),
    io.write_string(StdErr, "' because\n", !IO),
    io.write_string(StdErr, io.error_message(IOErr), !IO),
    io.nl(StdErr, !IO),

    io.set_exit_status(1, !IO).

%-----------------------------------------------------------------------------%
:- end_module error_util.
%-----------------------------------------------------------------------------%
