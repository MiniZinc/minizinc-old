%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et
%-----------------------------------------------------------------------------%
% Copyright (C) 2006-2010 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Nicholas Nethercote <njn@csse.unimelb.edu.au>
%
% Generic things used by multiple compiler *and* runtime modules.
% Nb: things should only be in this file if they are used by both the compiler
% and runtime.
%
%-----------------------------------------------------------------------------%

:- module zinc_common.
:- interface.

%-----------------------------------------------------------------------------%

:- import_module types_and_insts.

:- import_module zinc_ast.
:- import_module zinc_error.

:- import_module bool.
:- import_module io.
:- import_module list.
:- import_module maybe.

%-----------------------------------------------------------------------------%

    % This is useful, and used with various types.
:- typeclass show(T) where [
    func T^show = string
].

%-----------------------------------------------------------------------------%

    % Which language we are dealing with.
    %
:- type lang
    --->    lang_minizinc.

:- pred is_lang(lang::in, list(lang)::in) is semidet.

    % Predicates that succeed if the given language matches that expected.
    % ('z' == Zinc, 'm' == MiniZinc, 'f' == FlatZinc).
    %
:- pred zmf(lang::in) is semidet.
:- pred zm(lang::in) is semidet.
:- pred mf(lang::in) is semidet.

:- instance show(lang).

%-----------------------------------------------------------------------------%

    % In most (but not all) cases, model_checking and model_generation behave
    % the same -- params and flat enums need not be defined, because they can
    % be defined later in a data file.
:- type checking
            % Stop after checking the model.
    --->    model_checking
            % Stop after checking the instance.
    ;       instance_checking
            % Full compilation, but instance data may be provided at run-time.
    ;       model_generation
    .

%-----------------------------------------------------------------------------%

    % A name represents a named program entity, eg. a variable, function, type,
    % record field, etc.
    %
:- type zinc_names == list(zinc_name).
:- type zinc_name  == string.

%-----------------------------------------------------------------------------%

    % In general, an id is a name and a scope-number.  We use a more compact
    % representation for ids that are in the global scope and ids that do not
    % yet have their scope set.
    %
    % Each (non-global) scope (such as a pred/func body) has its own scope
    % number. Scope numbers are intended to uniquely identify the scope;
    % in contrast to partial identifiers such as the scope nesting depth.
    % The name/scope-number pair uniquely identifies any named program entity,
    % and can be used to look it up in the symbol table.
    %
:- type ids == list(id).
:- type id
    --->    id_global(zinc_name)     % Identifier in global scope.
    ;       id_unset(zinc_name)      % Scope is unknown; prior to type checking.
    ;       id_scoped(zinc_name, int).

    % Return the name of an identifier.
    %
:- func id_name(id) = zinc_name.

    % Create a new identifier.
    % The scope is unset.
    %
:- func id_init(zinc_name) = id.

%-----------------------------------------------------------------------------%

    % A source location.
:- type src_locn
    --->    src_locn(               % From a source file.
                filename    :: string,
                line_num    :: int
            )
    ;       builtin                 % Compiler builtin.
            % An unknown location.  In principle this is never needed, but
            % sometimes propagating a src_locn/2 through from the source code
            % is difficult.
    ;       unknown
    .

:- instance show(src_locn).

%-----------------------------------------------------------------------------%

    % Some more-informative alternatives to error/1 and require/1 that
    % indicate why the program aborted -- was it something that shouldn't have
    % happened, or just something that hasn't been implemented yet?
:- pred unexpected(   string::in) is erroneous.
:- pred unimplemented(string::in) is erroneous.

    % Abort (unexpectedly) if the condition fails/succeeds.
:- pred else_unexpected((pred)::((pred) is semidet), string::in) is det.
:- pred then_unexpected((pred)::((pred) is semidet), string::in) is det.


    % handle_io_error(ProgName, Error, !IO):
    % Decode Error and write an error message to the standard error.
    % Sets the exit status to 1.
    %
:- pred handle_io_error(string::in, io.error::in, io::di, io::uo) is det.

%-----------------------------------------------------------------------------%

    % For the printing of intermediate results between stages.
:- type writer(T) == ( pred( T, io, io)        ).
:- inst writer    == ( pred(in, di, uo) is det ).

    % For the printing of intermediate results between stages, ignoring items
    % in the specified files.
:- type writer2(T) == ( pred( T, list(string), io, io)        ).
:- inst writer2    == ( pred(in, in,           di, uo) is det ).

%-----------------------------------------------------------------------------%
%
% Frontend control.
%

    % Instances of this type class are provided by the various client
    % programs that use the Zinc frontend code.  The instances are used
    % to control various aspects of the frontend, e.g. whether certain
    % types of warnings are emitted.
    %
:- typeclass frontend_control(T) where [

    % Should the implementation emit a warning about unrecognised
    % annotations in FlatZinc?
    func warn_unknown_fzn_annotations(T) = bool,

    % extra_builtin_annotation(_, Lang, Name, Sig):
    %
    % Treat the annotation with the given Name and Signature as a builtin
    % annotation for the language Lang.  This is primarily useful in allowing
    % tools that process FlatZinc to extend the builtin set of annotations,
    % since FlatZinc doesn't provide a language feature for doing that.
    %
    pred extra_builtin_annotation(T, lang, zinc_name, type_insts),
    mode extra_builtin_annotation(in, in, in, out) is semidet,
    mode extra_builtin_annotation(in, in, out, out) is nondet,

    % Post-typechecking client-specific actions:
    % The following methods allow frontend clients to hook additional
    % error checking code into the Zinc type-checker.  For example,
    % a client program may wish to emit an error message of variables
    % of a certain types are encountered.
    %
    % NOTE: these actions need to be tolerant of models that are not
    % type-correct.  Such actions are invoked after an item is type-checked,
    % but _before_ any type error messages have been emitted.  Errors, other
    % than those that an action is intended to check for, should be ignored.

    % Client specific action for variable declaration items:
    % If set, this is called after a variable declaration item is
    % type-checked.
    %
    func post_typecheck_var_decl_action(T::in)
        = (maybe(var_decl_action)::out(maybe(var_decl_action))) is det,

    % Client specific action for constraint items:
    % If set, this is called after a constraint item has is type-checked.
    %
    func post_typecheck_constraint_action(T::in)
        = (maybe(constraint_action)::out(maybe(constraint_action))) is det,

    % Client specific action for solve item:
    % If set, this is called after the solve item has been type-checked.
    %
    func post_typecheck_solve_action(T::in)
        = (maybe(solve_action)::out(maybe(solve_action))) is det
].

%-----------------------------------------------------------------------------%
%
% Types and insts for post-typechecking client-specific actions.
%

    % var_decl_action(SrcLocn, TIExpr, Name, Anns, MaybeVal, !Errors):
    % The second through to fourth argument correspond to the representation
    % of var. decl. items in the AST.
    %
:- type var_decl_action
    == pred(src_locn, ti_expr, zinc_name, exprs, var_decl_assignment,
            zinc_errors, zinc_errors).
:- inst var_decl_action == (pred(in, in, in, in, in, in, out) is det).

    % constraint_action(SrcLocn, Expr, !Errors):
    %
:- type constraint_action ==
    pred(src_locn, expr, zinc_errors, zinc_errors).
:- inst constraint_action == (pred(in, in, in, out) is det).

    % solve_action(SrcLocn, SolveKind, Anns, !Errors):
    %
:- type solve_action == pred(src_locn, solve_kind, exprs,
                             zinc_errors, zinc_errors).
:- inst solve_action == (pred(in, in, in, in, out) is det).

%-----------------------------------------------------------------------------%

    % list_to_string(P, List, Sep):  print List using P to print each list,
    % with Sep as the separator.
    %
:- func list_to_string(func(T) = string, list(T), string) = string.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module compiler_common.

:- import_module require.
:- import_module string.

%-----------------------------------------------------------------------------%

is_lang(Lang, Langs) :-
    list.member(Lang, Langs).

zmf(Lang) :- list.member(Lang, [lang_minizinc]).
zm( Lang) :- list.member(Lang, [lang_minizinc          ]).
mf( Lang) :- list.member(Lang, [      lang_minizinc]).

:- instance show(lang) where [
    lang_minizinc^show = "MiniZinc"
].

%-----------------------------------------------------------------------------%

id_name(id_global(Name)) = Name.
id_name(id_unset(Name)) = Name.
id_name(id_scoped(Name, _)) = Name.

id_init(Name) = id_unset(Name).

%-----------------------------------------------------------------------------%

:- instance show(src_locn) where [
    builtin                   ^show = "(builtin)",
    unknown                   ^show = "(unknown)",
    src_locn(FileName, LineNo)^show = FileName ++ ":" ++ LineNo^string
].

%-----------------------------------------------------------------------------%

unexpected(   Msg) :- error("Unexpected: " ++ Msg).
unimplemented(Msg) :- error("Unimplemented: " ++ Msg).

else_unexpected(P, Msg) :- ( if P then true else unexpected(Msg) ).
then_unexpected(P, Msg) :- ( if P then unexpected(Msg) else true ).

handle_io_error(ProgName, Error, !IO) :-
    io.stderr_stream(Stderr, !IO),
    Msg = io.error_message(Error),
    io.format(Stderr, "%s: I/O error: %s\n", [s(ProgName), s(Msg)], !IO),
    get_error_exit_status(ErrorExitStatus, !IO),
    io.set_exit_status(ErrorExitStatus, !IO).

%-----------------------------------------------------------------------------%

list_to_string(_ElemToString, [], _Sep) = "".
list_to_string(ElemToString, [X], _Sep) = ElemToString(X).
list_to_string(ElemToString, [X1, X2 | Xs], Sep) =
    ElemToString(X1) ++ Sep ++ list_to_string(ElemToString, [X2 | Xs], Sep).

%-----------------------------------------------------------------------------%
:- end_module zinc_common.
%-----------------------------------------------------------------------------%
