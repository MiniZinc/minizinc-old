%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Ralph Becket <rafe@csse.unimelb.edu.au>
%
% Error handling for mzn2fzn.
%
%-----------------------------------------------------------------------------%

:- module errors.
:- interface.

:- import_module zinc_common.
:- import_module zinc_error.

:- import_module list.

%-----------------------------------------------------------------------------%

:- type error_context == list(list(string)).

    % We throw this error when we detect an internal error in the flattening
    % process.
:- type flattening_error
    --->    flattening_error(src_locn, list(error_msg_part)).

    % This is thrown at any point where model inconsistency is detected.
    %
:- type unsatisfiable_model
    --->    unsatisfiable_model(src_locn, list(error_msg_part)).

%-----------------------------------------------------------------------------%

:- func init_context(src_locn) = error_context.

:- pred value_out_of_range(error_context::in) is erroneous.

:- pred arg_out_of_range(error_context::in) is erroneous.

:- pred model_inconsistency_detected(error_context::in, string::in)
    is erroneous.

:- pred unsatisfiable_constraint(error_context::in) is erroneous.

:- pred minizinc_internal_error(error_context::in, string::in, string::in)
    is erroneous.

:- pred minizinc_user_error(error_context::in, string::in) is erroneous.

:- pred minizinc_overflow_error(error_context::in) is erroneous.

:- func error_context_to_error_msg(error_context) = error_msg.

%-----------------------------------------------------------------------------%

:- pred minizinc_require_match(error_context::in, T::in, list(T)::in,
    string::in, string::in) is det.

:- pred minizinc_require(error_context::in, (pred)::in((pred) is semidet),
    string::in, string::in) is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module exception.
:- import_module int.
:- import_module list.
:- import_module string.

%-----------------------------------------------------------------------------%

init_context(builtin) = [].
init_context(unknown) = [].
init_context(src_locn(FileName, LineNo)) =
    [[FileName, ":", int_to_string(LineNo), "\n"]].

value_out_of_range(Context) :-
    model_inconsistency_detected(Context, "Value is out of range.\n").

arg_out_of_range(Context) :-
    model_inconsistency_detected(Context, "Argument is out of range.\n").

model_inconsistency_detected(Context0, ErrMsg) :-
    Context = [[ErrMsg] | Context0],
    ErrorMsg = [words("warning:"), nl] ++ error_context_to_error_msg(Context),
    throw(unsatisfiable_model(unknown, ErrorMsg)).

unsatisfiable_constraint(Context) :-
    model_inconsistency_detected(Context, "Unsatisfiable constraint.\n").

minizinc_internal_error(Context, PredName, Msg) :-
    ErrorMsg = [words("internal error in " ++ PredName ++ ":"), nl] ++
        error_context_to_error_msg([[Msg] | Context]),
    throw(flattening_error(unknown, ErrorMsg)).

minizinc_user_error(Context, Msg) :-
    ErrorMsg = [words("error:"), nl] ++
        error_context_to_error_msg([[Msg] | Context]),
    throw(flattening_error(unknown, ErrorMsg)).

minizinc_overflow_error(Context) :-
    ArchSize = int.bits_per_int,
    minizinc_user_error(Context, "the bounds on this expression exceed" ++
        " what can be represented on a " ++ string.int_to_string(ArchSize) ++
        " bit machine.\n").

error_context_to_error_msg(Context) = ContextErrMsg :-
    F = ( func(Strs) = [words(string.append_list(Strs)), nl] ),
    % After the mapping, we have to remove the final, extraneous 'nl'.
    ContextErrMsgWithNl = list.condense(map(F, list.reverse(Context))),
    list.det_split_last(ContextErrMsgWithNl, ContextErrMsg, _).

%-----------------------------------------------------------------------------%

minizinc_require_match(Context, Item, List, PredName, Msg) :-
    ( if list.member(Item, List) then
        true
    else
        minizinc_internal_error(Context, PredName, Msg)
    ).

minizinc_require(Context, Test, PredName, Msg) :-
    ( if Test then
        true
    else
        minizinc_internal_error(Context, PredName, Msg)
    ).

%-----------------------------------------------------------------------------%
