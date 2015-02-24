%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2006-2007 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Authors: Ralph Becket <rafe@cs.mu.oz.au>
%          Nicholas Nethercote <njn@csse.unimelb.edu.au>
%
% A parser for Zinc, MiniZinc, and FlatZinc.
%
% This file is not called "parser.m" because there is a Mercury library
% module with that name, and we don't want to have name clashes.
%
%-----------------------------------------------------------------------------%

:- module zinc_parser.
:- interface.

:- import_module zinc_ast.
:- import_module zinc_common.
:- import_module zinc_error.

:- import_module bool.
:- import_module list.

%-----------------------------------------------------------------------------%

    % This just parses a string as a model.  It returns a list of included
    % files but doesn't read them.
    %
    % model ::= [ item `;' ... ]
    %
:- pred model(lang::in, string::in, int::in, bool::in, string::in, items::out,
    list(include)::out, zinc_errors::in, zinc_errors::out) is det.

    % For an include item, gives its line number, and the filename being
    % included.
    %
:- type include
    --->    include(int, string).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module zinc_lexer.

:- import_module builtin.
:- import_module exception.
:- import_module maybe.
:- import_module pair.
:- import_module require.
:- import_module string.
:- import_module unit.
:- import_module univ.

%-----------------------------------------------------------------------------%

:- type parser(T)  == ( pred(T, parser_state, tokens, tokens)  ).
:- inst parser     == ( pred(out, in, in, out) is semidet ).
:- inst parser_det == ( pred(out, in, in, out) is det ).

:- type parser_state
        --->    parser_state(
                    lang        :: lang,
                    filename    :: string
                ).

%-----------------------------------------------------------------------------%
%
% Item Parsing.
%

    % A type used to temporarily hold items.  Eventually it gets replaced with
    % normal items.  Having this type means we do not have to represent
    % include items and bogus items in the AST.
    %
:- type tmp_item
    --->    tmp_normal_item(raw_item)   % normal item
    ;       tmp_include_item(string)    % include item
    ;       tmp_bogus_item              % bogus item (contains a parse error)
    .

% The basic approach to error recovery is simple.  Every parser except the
% top-level item parser throws an exception if it encounters a lexing or
% parsing error.  The parser 'item' catches any such exception, adds
% the error to !Errs, and recovers by scanning (with 'sync') forward to the
% next ';' (or EOF), which it assumes marks the start of the next parsable
% item.

    % Nb: we do all the error handling "by hand" here rather than with
    % 'semicolon_list', 'expect', etc.  That's because we're outside the try
    % block in 'item' and so we can't use any of those combinators because
    % they throw exceptions on parse errors.
    %
    % In order to ensure that we only use a constant amount of stack space here
    % we build up the list of items and includes in reverse using an
    % accumulator.  When we have finished processing items we then reverse that
    % list.
    %
model(Lang, FileName, StartLineNum, IsDataFile, FileText, Items, Includes,
        !Errs) :-
    Ts = zinc_lexer.lex_file(Lang, StartLineNum, FileName, FileText),
    S = parser_state(Lang, FileName),
    model_2(IsDataFile, !Errs, [], ItemsAndIncludes, S, Ts, _),
    reverse_and_append_items(ItemsAndIncludes, Items, Includes).

:- type items_and_includes
    --->    items_and_includes(items, list(include)).

:- type parser_acc(T) == (pred(T, T, parser_state, tokens, tokens)).
:- inst det_parser_acc == (pred(in, out, in, in, out) is det).

:- pred model_2(bool::in, zinc_errors::in, zinc_errors::out)
    : parser_acc(list(items_and_includes)) `with_inst` det_parser_acc.

model_2(IsDataFile, !Errs, !ItemsAndIncludesAcc, S, !Ts) :-
    peek_token(Tok, LineNum, !.Ts),
    ( if tmp_item(IsDataFile, !Errs, TmpItem, S, !Ts) then
        % Remove bogus items, separate include items, unpack other items.
        (   TmpItem = tmp_include_item(IncFileName),
            Items0     = [],
            Includes0  = [include(LineNum, IncFileName)]
        ;
            TmpItem = tmp_normal_item(RawItem),
            Locn = src_locn(S ^ filename, LineNum),
            Items0     = [item(RawItem, Locn)],
            Includes0  = []
        ;
            TmpItem = tmp_bogus_item,
            Items0     = [],
            Includes0  = []
        ),
        ItemsAndIncludes = items_and_includes(Items0, Includes0),
        !:ItemsAndIncludesAcc = [ItemsAndIncludes | !.ItemsAndIncludesAcc],
        ( if next_token(semicolon, _, !Ts) then
            model_2(IsDataFile, !Errs, !ItemsAndIncludesAcc, S, !Ts)
        else if next_token(eof, _, !Ts) then
            true
        else
            make_parse_error("expected `;' after previous item", Err2, S, !Ts),
            !:Errs = [Err2 | !.Errs],
            sync(yes, !Ts),
            model_2(IsDataFile, !Errs, !ItemsAndIncludesAcc, S, !Ts)
        )

    else if next_token(eof, _, !Ts) then
        true

    else if Tok = semicolon then
        make_parse_error("empty items are not allowed", Err, S, !Ts),
        !:Errs = [Err | !.Errs],
        model_2(IsDataFile, !Errs, !ItemsAndIncludesAcc, S, !Ts)

    else
        % Nb: we remind the user when the failing item is in a data file.
        % That's because data files disallow most item kinds, but if the user
        % forgets this fact, they might be confused by a plain "invalid item"
        % error on an item that would be accepted in a model file.
        (
            IsDataFile = yes,
            Extra = "(data file) "
        ;
            IsDataFile = no,
            Extra = ""
        ),
        make_parse_error("start of invalid " ++ Extra ++ "item", Err3, S, !Ts),
        !:Errs = [Err3 | !.Errs],
        sync(yes, !Ts),
        model_2(IsDataFile, !Errs, !ItemsAndIncludesAcc, S, !Ts)
    ).

:- pred reverse_and_append_items(list(items_and_includes)::in,
    items::out, list(include)::out) is det.

reverse_and_append_items(ItemsAndIncludes, Items, Includes) :-
    reverse_and_append_items_2(ItemsAndIncludes, [], Items, [], Includes).

:- pred reverse_and_append_items_2(list(items_and_includes)::in,
    items::in, items::out, list(include)::in, list(include)::out) is det.

reverse_and_append_items_2([], !Items, !Includes).
reverse_and_append_items_2([ItemsAndIncludesHead | ItemsAndIncludesTail],
        !Items, !Includes) :-
    ItemsAndIncludesHead = items_and_includes(Items0, Includes0),
    !:Items = Items0 ++ !.Items,
    !:Includes = Includes0 ++ !.Includes,
    reverse_and_append_items_2(ItemsAndIncludesTail, !Items, !Includes).

%-----------------------------------------------------------------------------%

    % See tmp_item_2 below for the 'item' grammar.
    %
:- pred tmp_item(bool::in, zinc_errors::in, zinc_errors::out)
    : parser(tmp_item) `with_inst` parser.

tmp_item(IsDataFile, !Errs, TmpItem, S, Ts, NTs) :-
    P = (pred({TmpItemP, TsP}::out) is semidet :-
        tmp_item_2(IsDataFile, TmpItemP, S, Ts, TsP)
    ),
    TryResult =
        promise_only_solution(
            ( pred(TResult::out) is cc_multi :- try(P, TResult) )
       ),
    (
        TryResult = succeeded({TmpItem, NTs})
    ;
        TryResult = exception(Exception),
        ( if univ_to_type(Exception, Err) then
            !:Errs = [Err | !.Errs],
            sync(no, Ts, NTs),
            TmpItem = tmp_bogus_item
        else if univ_to_type(Exception, software_error(Str)) then
            unexpected("item: unexpected exception: " ++ Str)
        else
            unexpected("item: unexpected exception of unknown type")
        )
    ).

%---------------------------------------------------------------------------%

    % This chews up tokens until it hits a semicolon or EOF.  It consumes the
    % the hit semicolon/EOF only if ConsumeSyncTok = yes.  Note that it never
    % throws an exception -- any lexing errors encountered by next_token will
    % be ignored, because we don't care about them at this point.
:- pred sync(bool::in, tokens::in, tokens::out) is det.

sync(ConsumeSyncTok, Ts, NTs) :-
    next_token(Tok, _, Ts, Ts1),
    ( if ( Tok = semicolon ; Tok = eof ) then
        NTs = ( if ConsumeSyncTok = yes then Ts1 else Ts )
    else
        sync(ConsumeSyncTok, Ts1, NTs)
    ).

%-----------------------------------------------------------------------------

:- pred tmp_item_2(bool::in)
    : parser(tmp_item) `with_inst` parser.

tmp_item_2(IsDataFile, RawTmpItem, S, !Ts) :-
    ( if
        zm_raw_item(IsDataFile, RawItem, S, !Ts)
    then
        RawTmpItem = tmp_normal_item(RawItem)
    else if
        IsDataFile = no,
        zm_include_item(IncFileName, S, !Ts)
    then
        RawTmpItem = tmp_include_item(IncFileName)
    else
        false
    ).

%-----------------------------------------------------------------------------%
%
% Zinc/MiniZinc Items.
%

    % zm_item ::=
    %       |  zm_type_inst_syn_item
    %       |  zm_enum_item
    %       |  zm_include_item              % handled above
    %       |  zm_var_decl_item
    %       |  zm_assign_item
    %       |  zm_constraint_item
    %       |  zm_solve_item
    %       |  zm_output_item
    %       |  zm_predicate_item
    %       |  zm_test_item
    %       |  zm_function_item
    %
:- pred zm_raw_item(bool::in)
    : parser(raw_item) `with_inst` parser.

zm_raw_item(IsDataFile, R, S, !Ts) :-
    (
        IsDataFile = yes,
        % Enums can appear in data files only if they are defined and flat.
        ( if zm_assign_item(R0, S, !Ts)
        then R = R0
        else false
        )
    ;
        IsDataFile = no,
        (    if zm_var_decl_item(     R0, S, !Ts) then R = R0
        else if zm_assign_item(       R0, S, !Ts) then R = R0
        else if zm_constraint_item(   R0, S, !Ts) then R = R0
        else if zm_solve_item(        R0, S, !Ts) then R = R0
        else if zm_output_item(       R0, S, !Ts) then R = R0
        else if zm_predicate_item(    R0, S, !Ts) then R = R0
        else if zm_test_item(         R0, S, !Ts) then R = R0
        else if zm_function_item(     R0, S, !Ts) then R = R0
        else if zm_annotation_item(   R0, S, !Ts) then R = R0
        else false
        )
    ).

%-----------------------------------------------------------------------------%

    % zm_include_item ::= `include' string_literal
    %
:- pred zm_include_item : parser(string) `with_inst` parser.

zm_include_item(IncFileName, S, !Ts) :-
    keyword("include", S, !Ts),
    ( if next_token(string(IncFileName0), _, !Ts)
    then IncFileName = IncFileName0
    else expected("string literal after `include'", S, !Ts)
    ).

%-----------------------------------------------------------------------------%

    % zm_var_decl_item ::= zm_ti_expr `:' ident annotations [ '=' expr ]
    %
:- pred zm_var_decl_item : parser(raw_item) `with_inst` parser.

zm_var_decl_item(var_decl_item(TIE, Name, AnnEs, MaybeE), S, !Ts) :-
    zm_ti_expr(TIE, S, !Ts),
    % Nb: We can't always distinguish assignments from variable declarations
    % just from the first token -- if it's an identifier, it could be either
    % (and things get more complicated if we allow the "constraint" keyword to
    % be removed on constraints).  However, if the token is definitely a
    % type-expr that cannot be used in a normal expression (eg. "int" or "set
    % of bool"), then this item must be a variable declaration, in which case
    % we use 'expect' with the colon following the type.
    %
    % We go to this effort for a common case -- forgetting the colon in a
    % variable declaration.  Eg. if we have:
    %
    %   int x = 3;
    %
    % without this effort the error message is:
    %
    %   "syntax error at `int'"
    %
    % which is not only unhelpful but misleading.  With the effort we get:
    %
    %   "syntax error at `x'; expected `:' after type in variable declaration"
    %
    ( if definitely_a_ti_expr(TIE) then
        expect_token("`:' after type in variable declaration", colon, S, !Ts)
    else
        next_token(colon, _, !Ts)
    ),
    expect("identifier after `:' in variable declaration",
        name, Name, S, !Ts),
    zm_annotations(AnnEs, S, !Ts),
    ( if next_token(op("="), _, !Ts) then
        expect("expression after `=' in variable declaration",
            zm_expr, E, S, !Ts),
        MaybeE = rhs_assignment(E)
    else
        MaybeE = no_assignment
    ).

    % This returns true if the type-expr couldn't possibly be something else
    % (such as a variable name).  It is used to improve error messages.
    %
:- pred definitely_a_ti_expr(ti_expr::in) is semidet.

definitely_a_ti_expr(ti_expr(raw_ti_expr(_VarPar, BT), _Locn)) :-
    ( BT = bte_bool
    ; BT = bte_int
    ; BT = bte_float
    ; BT = bte_string
    ; BT = bte_set_of(_)
    ; BT = bte_array_of(_,_,_)
    ; BT = bte_tuple_of(_)
    ; BT = bte_typeinst_var(_)
    ).

%-----------------------------------------------------------------------------%
%
% Assign items.
%

    % zm_assign_item ::= ident '=' expr
    %
:- pred zm_assign_item : parser(raw_item) `with_inst` parser.

zm_assign_item(assign_item(Name, Value), S, !Ts) :-
    name(Name, S, !Ts),
    next_token(op("="), _, !Ts),
    expect("expression after `=' in assignment", zm_expr, Value, S, !Ts).

%-----------------------------------------------------------------------------%
%
% Constraint items.
%

    % zm_constraint_item ::= `constraint' expr
    %
:- pred zm_constraint_item : parser(raw_item) `with_inst` parser.

zm_constraint_item(constraint_item(E), S, !Ts) :-
    keyword("constraint", S, !Ts),
    expect("expression after `constraint'", zm_expr, E, S, !Ts).

%-----------------------------------------------------------------------------%
%
% Solve items.
%

    % zm_solve_item ::= `solve' zm_annotations zm_solve_kind
    %
    % zm_solve_kind ::= `satisfy'
    %                |  `maximize' expr
    %                |  `minimize' expr
    %
:- pred zm_solve_item : parser(raw_item) `with_inst` parser.

zm_solve_item(solve_item(SolveKind, AnnEs), S, !Ts) :-
    keyword("solve", S, !Ts),
    zm_annotations(AnnEs, S, !Ts),
    zm_solve_kind(SolveKind, S, !Ts).

:- pred zm_solve_kind : parser(solve_kind) `with_inst` parser_det.

zm_solve_kind(SolveKind, S, !Ts) :-
    ( if keyword("satisfy", S, !Ts) then
        SolveKind = satisfy
      else if keyword("maximize", S, !Ts) then
        expect("expression after `solve maximize'", zm_expr, E, S, !Ts),
        SolveKind = maximize(E)
      else if keyword("minimize", S, !Ts) then
        expect("expression after `solve minimize'", zm_expr, E, S, !Ts),
        SolveKind = minimize(E)
      else
        expected("`satisfy', 'maximize' or 'minimize' after `solve'", S, !Ts)
    ).

%-----------------------------------------------------------------------------%
%
% Output items.
%

    % zm_output_item ::= `output' expr
    %
:- pred zm_output_item : parser(raw_item) `with_inst` parser.

zm_output_item(output_item(OutputE), S, !Ts) :-
    keyword("output", S, !Ts),
    expect("expression after `output'", zm_expr, OutputE, S, !Ts).

%-----------------------------------------------------------------------------%

    % zm_predicate_item ::= `predicate' ident zm_params [ '=' expr ]
    %
:- pred zm_predicate_item : parser(raw_item) `with_inst` parser.

zm_predicate_item(RawItem, S, !Ts) :-
    keyword("predicate", S, !Ts),
    zm_operation_item_tail("predicate", "predicate", pred_ret, RawItem, S,
        !Ts).

    % zm_test_item ::= `test' ident zm_params [ '=' expr ]
    %
:- pred zm_test_item : parser(raw_item) `with_inst` parser.

zm_test_item(RawItem, S, !Ts) :-
    keyword("test", S, !Ts),
    % We call tests "predicates".  See the comment above the declaration of
    % the type 'operation_kind'.
    zm_operation_item_tail("predicate", "test", test_ret, RawItem, S, !Ts).

    % zm_function_item ::= `function' zm_ti_expr : ident zm_params [ '=' expr ]
    %
:- pred zm_function_item : parser(raw_item) `with_inst` parser.

zm_function_item(RawItem, S, !Ts) :-
    keyword("function", S, !Ts),
    expect("function return type-inst after `function'",
        zm_ti_expr,  TIE, S, !Ts),
    expect_token("`:' after return type-inst in function",
        colon, S, !Ts),
    zm_operation_item_tail("function", ":", func_ret(TIE), RawItem, S, !Ts).

    % zm_operation_item_tail ::= ident zm_params zm_annotations [ '=' expr ]
    %
:- pred zm_operation_item_tail(string::in, string::in, predfunc_ret::in)
        : parser(raw_item) `with_inst` parser_det.

zm_operation_item_tail(What, NameAfter, PredFuncRet, RawItem, S, !Ts) :-
    expect(What ++ " name after `" ++ NameAfter ++ "'", name, Name, S, !Ts),
    peek_token(Tok, _, !.Ts),
    ( if ( Tok = lparen ; Tok = op("=") ; Tok = semicolon ) then
        zm_params(What, Params, S, !Ts),
        zm_annotations(AnnEs, S, !Ts),
        ( if next_token(op("="), _, !Ts) then
            expect(What ++ " body after `='", zm_expr, BodyE, S, !Ts),
            MaybeBodyE = yes(BodyE)
        else
            MaybeBodyE = no
        )
    else
        expected("list of arguments or " ++ What ++
            " body or semicolon after " ++ What ++ " name", S, !Ts)
    ),
    RawItem = raw_predfunc_init(PredFuncRet, Name, Params, AnnEs, MaybeBodyE).

    % zm_annotation_item ::= `annotation' ident zm_params
    %
:- pred zm_annotation_item : parser(raw_item) `with_inst` parser.

zm_annotation_item(annotation_item(Name, Params), S, !Ts) :-
    keyword("annotation", S, !Ts),
    expect("annotation name after `annotation'", name, Name, S, !Ts),
    zm_params("function", Params, S, !Ts).

%-----------------------------------------------------------------------------%

    % zm_params ::= [ '(' zm_ti_expr_and_id `,' ... `)' ]
    %
:- pred zm_params(string::in)
        : parser(ti_exprs_and_ids) `with_inst` parser_det.

zm_params(What, Params, S, !Ts) :-
    ( if next_token(lparen, _, !Ts) then
        expect("list of " ++ What ++ " arguments after `('",
            comma_list(zm_ti_expr_and_id(What ++ " argument")),
            Params, S, !Ts),
        expect_token("')' after " ++ What ++ " arguments",
            rparen, S, !Ts)
    else
        Params = []
    ).

%-----------------------------------------------------------------------------%

    % zm_ti_expr_and_id ::= zm_ti_expr `:' ident
    %
    % The first predicate returns a typed_id, the second one returns a
    % typed_name.

:- pred zm_ti_expr_and_id(string::in) :
    parser(ti_expr_and_id) `with_inst` parser.

zm_ti_expr_and_id(What, TIE - Id, S, !Ts) :-
    zm_ti_expr_and_name(What, TIE - Name, S, !Ts),
    Id = id_init(Name).

:- pred zm_ti_expr_and_name(string::in) : 
    parser(ti_expr_and_name) `with_inst` parser.

zm_ti_expr_and_name(What, TIE - Name, S, !Ts) :-
    zm_ti_expr(TIE, S, !Ts),
    expect_token("`:' after type-inst expression in " ++ What, colon, S, !Ts),
    expect("identifier after `:' in " ++ What, name, Name, S, !Ts).

%-----------------------------------------------------------------------------%
%
% MiniZinc Type-inst Expressions.
%

    % zm_ti_expr ::= `(' zm_ti_expr `:' ident `where' zm_expr `)'
    %             |  zm_base_ti_expr
    %
:- pred zm_ti_expr : parser(ti_expr) `with_inst` parser.

zm_ti_expr(TIE, S, !Ts) :-
    % Ordering is important:
    % - Try ones with type constraints before ranges, so the "(a:b" isn't
    %   seen as an error.
    peek_token(_, LineNum, !.Ts),
    ( if
        zm_base_ti_expr(RawTIE0, S, !Ts)
    then
        RawTIE = RawTIE0
    else
        false
    ),
    TIE = p_ti_expr_init(RawTIE, LineNum, S).

    % zm_var_par ::= `var' | `par' | empty
    %
:- pred zm_var_par : parser(var_par) `with_inst` parser_det.

zm_var_par(VarPar, S, !Ts) :-
    ( if keyword("var", S, !Ts) then
        VarPar = var
    else if keyword("par", S, !Ts) then
        VarPar = par
    else
        VarPar = par
    ).

    % zm_base_ti_expr ::= zm_var_par zm_base_ti_expr_tail
    %
:- pred zm_base_ti_expr : parser(raw_ti_expr) `with_inst` parser.

zm_base_ti_expr(raw_ti_expr(VarPar, BaseTIETail), S, !Ts) :-
    zm_var_par(VarPar, S, !Ts),
    zm_base_ti_expr_tail(BaseTIETail, S, !Ts).

    % zm_base_ti_expr_tail ::= ident
    %                       |  zm_simple_type_name
    %                       |  zm_set_ti_expr_tail
    %                       |  zm_array_ti_expr_tail
    %                       |  zm_tuple_ti_expr_tail
    %                       |  zm_record_ti_expr_tail
    %                       |  zm_ti_variable_expr_tail
    %                       |  zm_range_ti_expr_tail
    %                       |  zm_set_expr_ti_expr_tail
    %                       |  zm_op_ti_expr_tail
    %
    %
:- pred zm_base_ti_expr_tail : parser(base_ti_expr_tail) `with_inst` parser.

zm_base_ti_expr_tail(B, S, !Ts) :-
    % Ordering is important:
    % - Try ranges before idents so "m..n" doesn't have "m" swallowed as an
    %   identifer, leaving "..n" behind.
    ( if    zm_range_ti_expr_tail(   B0, S, !Ts) then B = B0
    else if ident(                   Id, S, !Ts) then B = bte_ident(Id)
    else if zm_simple_type_name(     B0, S, !Ts) then B = B0
    else if zm_set_ti_expr_tail(     B0, S, !Ts) then B = B0
    else if zm_array_ti_expr_tail(   B0, S, !Ts) then B = B0
    else if zm_tuple_ti_expr_tail(   B0, S, !Ts) then B = B0
    else if zm_ti_variable_expr_tail(B0, S, !Ts) then B = B0
    else if zm_set_expr_ti_expr_tail(B0, S, !Ts) then B = B0
    else false
    ).

%-----------------------------------------------------------------------------%

    % zm_range_ti_expr_tail ::= zm_num_expr `..' zm_num_expr
    %
:- pred zm_range_ti_expr_tail : parser(base_ti_expr_tail) `with_inst` parser.

zm_range_ti_expr_tail(BaseTIETail, S, !Ts) :-
    % Note that the 'zm_num_expr' is required here, not just 'expr' -- if
    % it were 'expr', the ".." would always be sucked into the expression
    % and this rule would never match.
    zm_num_expr(E1, S, !Ts),
    next_token(op(".."), _, !Ts),
    zm_num_expr(E2, S, !Ts),
    BaseTIETail = bte_range_expr_as_type_expr(E1, E2).

    % zm_simple_type_name ::= `bool' | `int' | `float' | `string' | `ann'
    %
:- pred zm_simple_type_name : parser(base_ti_expr_tail) `with_inst` parser.

zm_simple_type_name(BaseTIETail, S, !Ts) :-
    ( if    keyword("int",    S, !Ts) then BaseTIETail = bte_int
    else if keyword("float",  S, !Ts) then BaseTIETail = bte_float
    else if keyword("bool",   S, !Ts) then BaseTIETail = bte_bool
    else if keyword("string", S, !Ts) then BaseTIETail = bte_string
    else if keyword("ann",    S, !Ts) then BaseTIETail = bte_ann
    else false
    ).

%-----------------------------------------------------------------------------%

    % zm_ti_variable_expr_tail ::= [`any'] $[A-Za-z][A-Za-z9-0_]*
    %
:- pred zm_ti_variable_expr_tail
    : parser(base_ti_expr_tail) `with_inst` parser.

zm_ti_variable_expr_tail(BaseTIETail, S, !Ts) :-
    ( if keyword("any", S, !Ts) then IsAny = yes else IsAny = no ),
    (
        IsAny = no,
        zm_ti_variable_name(Name, S, !Ts),
        BaseTIETail = bte_typeinst_var(Name)
    ;
        IsAny = yes,
        expect("type-inst variable after `any'", zm_ti_variable_name, Name, S,
            !Ts),
        BaseTIETail = bte_any_typeinst_var(Name)
    ).

:- pred zm_ti_variable_name : parser(zinc_name) `with_inst` parser.

zm_ti_variable_name(Name, _S, !Ts) :-
    next_token(dollar_ident(Name), _, !Ts).

%-----------------------------------------------------------------------------%

    % zm_set_ti_expr_tail ::= `set' `of' zm_ti_expr
    %
:- pred zm_set_ti_expr_tail : parser(base_ti_expr_tail) `with_inst` parser.

zm_set_ti_expr_tail(bte_set_of(ElemTIE), S, !Ts) :-
    keyword("set", S, !Ts),
    expect("`of' after `set'", keyword("of"), _, S, !Ts),
    expect("type expression after `set of'", zm_ti_expr, ElemTIE, S, !Ts).

%-----------------------------------------------------------------------------%

    % zm_array_ti_expr_tail ::=
    %      `array' `[' zm_ti_expr `,' ... `]' `of' zm_ti_expr
    %    | `list' `of' zm_ti_expr
    %
:- pred zm_array_ti_expr_tail : parser(base_ti_expr_tail) `with_inst` parser.

zm_array_ti_expr_tail(bte_array_of(KeyTIEs, ValueTIE, IsListSyntax), S, !Ts) :-
    peek_token(_, LineNum, !.Ts),
    ( if keyword("array", S, !Ts) then
        expect("list of type-inst expressions in brackets after `array'",
            brackets(lsquare, comma_list(zm_ti_expr), rsquare), KeyTIEs,
            S, !Ts),
        expect("`of' after array indices", keyword("of"), _, S, !Ts),
        expect("type-inst expression after `of'", zm_ti_expr, ValueTIE, S,
            !Ts),
        IsListSyntax = no
    else if keyword("list", S, !Ts) then
        expect("`of' after `list'", keyword("of"), _, S, !Ts),
        expect("type-inst expression after `list of'",
            zm_ti_expr, ValueTIE, S, !Ts),
        KeyTIEs = [p_ti_expr_init(raw_ti_expr(par, bte_int), LineNum, S)],
        IsListSyntax = yes
    else
        false
    ).

%-----------------------------------------------------------------------------%

    % zm_tuple_ti_expr_tail ::= `tuple' `(' zm_ti_expr `,' ... `)'
    %
:- pred zm_tuple_ti_expr_tail : parser(base_ti_expr_tail) `with_inst` parser.

zm_tuple_ti_expr_tail(bte_tuple_of(TIEs), S, !Ts) :-
    keyword("tuple", S, !Ts),
    expect("list of type-inst expressions in parentheses after `tuple'",
        brackets(lparen, comma_list(zm_ti_expr), rparen), TIEs, S, !Ts).

%-----------------------------------------------------------------------------%

    % zm_set_expr_ti_expr_tail ::= '{' zm_expr ',' ... '}'
    %
:- pred zm_set_expr_ti_expr_tail : parser(base_ti_expr_tail) `with_inst` parser.

zm_set_expr_ti_expr_tail(BaseTIETail, S, !Ts) :-
    brackets(lcurly, comma_list(zm_expr), rcurly, Elems, S, !Ts),
    BaseTIETail = bte_set_expr_as_type_expr(Elems).

%-----------------------------------------------------------------------------%
% Zinc/MiniZinc Expressions
%-----------------------------------------------------------------------------%

:- type bin_op_stack_elem == pair(bin_op_attrs, expr_info).
:- type bin_op_stack      == list(bin_op_stack_elem).

:- type expr_stack == list(expr).

%-----------------------------------------------------------------------------%

    % Expressions are parsed with an operator precedence parser.
    %
    % This is a left-factored version of the grammar from the spec.  The
    % factoring groupings are: tuple_expr and parenthesized expr;
    % zm_record_access_tail and zm_tuple_access_tail;  ident and call_expr and
    % zm_enum_expr.
    %
    % zm_expr ::= zm_expr_atom zm_expr_binop_tail
    %
    % zm_expr_atom ::= zm_expr_atom_head zm_expr_atom_tail annotations
    %
    % zm_expr_binop_tail ::= [ zm_bin_op expr ]
    %
    % zm_expr_atom_head ::= zm_paren_or_tuple_expr
    %                    |  zm_ident_or_quoted_op_or_call_like_expr
    %                    |  zm_anon_var
    %                    |  zm_literal
    %                    |  zm_un_op_expr
    %                    |  zm_set_expr
    %                    |  zm_array_expr
    %                    |  zm_simple_array_literal_2d
    %                    |  zm_record_expr
    %                    |  zm_if_then_else_expr
    %                    |  zm_case_expr
    %                    |  zm_let_expr
    %                    |  zm_gen_call_expr
    %
    % zm_expr_atom_tail ::= empty
    %                   |  zm_array_access_tail           zm_expr_atom_tail
    %                   |  zm_tuple_or_record_access_tail zm_expr_atom_tail
    %
    % Integer expressions are a subset of full expressions.  We designate if
    % we're parsing full expressions or just integer expressions via an extra
    % argument.

:- pred zm_expr : parser(expr) `with_inst` parser.

zm_expr(E, S, !Ts) :-
    zm_expr2(/*IsNumE*/no, E, S, !Ts).

:- pred zm_num_expr : parser(expr) `with_inst` parser.

zm_num_expr(E, S, !Ts) :-
    zm_expr2(/*IsNumE*/yes, E, S, !Ts).

:- pred zm_expr2(bool::in) : parser(expr) `with_inst` parser.

zm_expr2(IsNumE, E, S, !Ts) :-
    zm_expr_atom(IsNumE, E0, S, !Ts),
    zm_expr_binop_tail(IsNumE, [E0], [], E, S, !Ts).

%-----------------------------------------------------------------------------%

:- pred zm_expr_atom(bool::in) : parser(expr) `with_inst` parser.

zm_expr_atom(IsNumE, E, S, !Ts) :-
    peek_token(_, LineNum, !.Ts),
    zm_expr_atom_head(IsNumE, RawE1-AnnEs1, S, !Ts),
    E1 = expr(RawE1, AnnEs1, expr_info_init(src_locn(S^filename, LineNum))),
    zm_expr_atom_tail(E1, expr(RawE2, AnnEsInner, EInfo2), S, !Ts),
    zm_annotations(AnnEsOuter, S, !Ts),
    % Concatenate any annotations from within the expressions (will only be
    % present for parenthesised expressions, eg "(x::foo)") with the ones
    % following the expression.  We must do this because we don't represent
    % parenthesised exprs differently from non-parenthesised exprs.
    E = expr(RawE2, AnnEsInner ++ AnnEsOuter, EInfo2).

:- pred zm_expr_atom_head(bool::in)
    : parser(pair(raw_expr, exprs)) `with_inst` parser.

zm_expr_atom_head(IsNumE, RawE-AnnEs, S, !Ts) :-
    % Order is important:
    % - We try 'zm_record_expr' before 'zm_paren_or_tuple_expr' so that record
    %   expressions can be parsed ok -- otherwise a fieldname can be parsed as
    %   an expression and then the ':' after the fieldname is unexpected.
    % - We try 'zm_gen_call_expr' before
    %   'zm_ident_or_quoted_op_or_call_like_expr', because they often look
    %   similar.  Eg. in "forall(i,j in S) (E)" the "forall(i,j in S)" part
    %   could be a normal call;  it's only when we reach the "(E)" that we can
    %   tell it's a gen-call.
    ( if
        zm_paren_or_tuple_expr(IsNumE, RawE0 - AnnEs0, S, !Ts)
    then
        RawE = RawE0,
        AnnEs = AnnEs0
    else
        ( if
            zm_gen_call_expr(RawE0, S, !Ts)
        then
            RawE = RawE0
        else if
            zm_ident_or_quoted_op_or_call_like_expr(IsNumE, RawE0, S, !Ts)
        then
            RawE = RawE0
        else if
            IsNumE = no,
            zm_anon_var(RawE0, S, !Ts)
        then
            RawE = RawE0
        else if
            zm_literal(IsNumE, RawE0, S, !Ts)
        then
            RawE = RawE0
        else if
            zm_un_op_expr(IsNumE, RawE0, S, !Ts)
        then
            RawE = RawE0
        else if
            IsNumE = no,
            zm_set_expr(RawE0, S, !Ts)
        then
            RawE = RawE0
        else if
            IsNumE = no,
            zm_array_expr(RawE0, S, !Ts)
        then
            RawE = RawE0
        else if
            IsNumE = no,
            zm_simple_array_literal_2d(RawE0, S, !Ts)
        then
            RawE = RawE0
        else if
            zm_if_then_else_expr(RawE0, S, !Ts)
        then
            RawE = RawE0
        else if
            zm_let_expr(RawE0, S, !Ts)
        then
            RawE = RawE0
        else
            false
        ),
        AnnEs = []
    ).

:- pred zm_expr_atom_tail(expr::in) : parser(expr) `with_inst` parser_det.

zm_expr_atom_tail(EIn, EOut, S, !Ts) :-
    ( if  zm_array_access_tail(EIn, E1, S, !Ts) then
        zm_expr_atom_tail(E1, EOut, S, !Ts)
    else
        EOut = EIn
    ).

%-----------------------------------------------------------------------------%

    % zm_annotations ::= ( '::' zm_annotation )*
    %
:- pred zm_annotations : parser(exprs) `with_inst` parser_det.

zm_annotations(AnnEs, S, !Ts) :-
    zero_or_more(andthen2("annotation after `::'", double_colon,
        zm_annotation), AnnEs, S, !Ts).

    % zm_annotation  ::= zm_expr_atom_head zm_expr_atom_tail
    %
    % Nb: annotations can themselves be annotated, but we flatten that.
    % This means that we can actually return multiple annotations from this
    % predicate.  Eg. if the annotation is "(a::b)", we return [a, b].
    %
:- pred zm_annotation : parser(expr) `with_inst` parser.

zm_annotation(Ann, S, !Ts) :-
    peek_token(_, LineNum, !.Ts),
    zm_expr_atom_head(/*IsNumE*/no, RawE1-AnnEs1, S, !Ts),
    E1 = expr(RawE1, AnnEs1, expr_info_init(src_locn(S^filename, LineNum))),
    zm_expr_atom_tail(E1, Ann, S, !Ts).

%-----------------------------------------------------------------------------%

:- pred zm_expr_binop_tail(bool::in, expr_stack::in, bin_op_stack::in)
    : parser(expr) `with_inst` parser.

zm_expr_binop_tail(IsNumE, Es0, Ops0, E, S, !Ts) :-
    Ts0 = !.Ts,
    ( if
        next_token(Tok, _, !Ts),
        Lang = S ^ lang,
        (
            Tok = op(Name),
             % Nb: the IsNumE unification is semidet
             is_bin_op(Lang, Name, Assoc, Prec, IsNumOp),
             ( if IsNumE = yes
             then IsNumOp = yes          % Semidet.
             else true
             )
        ;
            Tok = backquoted_op(Name),
            backquoted_bin_op(Lang, Assoc, Prec)
        )
    then
        peek_token(_, LineNum, !.Ts),
        EInfo = expr_info_init(src_locn(S^filename, LineNum)),
        Op = bin_op_attrs(Name, Assoc, Prec),
        push_bin_op(Op - EInfo, Es0, Es1, Ops0, Ops, S, Ts0),
        % This is nasty:  we require an expression after the bin-op, unless
        % it's an '='.  Because in that case it might actually be an
        % assignment!  Ugh.
        ( if Name = "=" then
            zm_expr_atom(IsNumE, E0, S, !Ts)
        else
            expect("expression after infix operator `" ++ Name ++ "'",
                zm_expr_atom(IsNumE), E0, S, !Ts)
        ),
        push_expr(E0, Es1, Es),
        zm_expr_binop_tail(IsNumE, Es, Ops, E, S, !Ts)
    else
        close_expr(Es0, Ops0, E)
    ).

:- pred push_bin_op(bin_op_stack_elem::in, expr_stack::in, expr_stack::out,
    bin_op_stack::in, bin_op_stack::out, parser_state::in, tokens::in)
    is semidet.

push_bin_op(Op - EInfo, Es, Es, [], [Op - EInfo], _S, _Ts).

push_bin_op(Op - EInfo, Es0, Es, Ops0 @ [Op0 - EInfo0 | Ops1], Ops, S, Ts) :-
    O = ordering(Op ^ bin_op_precedence, Op0 ^ bin_op_precedence),
    (
        % The pushed op binds tighter than the top one.
        O   = (<),
        Es  = Es0,
        Ops = [Op - EInfo | Ops0]
    ;
        % The pushed op binds as tightly as the top one.
        O = (=),
        (
            Op ^ bin_op_associativity = left,
            Es0 = [EA, EB | Es1],
            EC  = expr(raw_app_init(Op0 ^ bin_op_name, operator_app,
                    [EB, EA]), [], EInfo0),
            Es  = [EC | Es1],
            Ops = [Op - EInfo | Ops1]
        ;
            Op ^ bin_op_associativity = right,
            Es  = Es0,
            Ops = [Op - EInfo | Ops0]
        ;
            Op ^ bin_op_associativity = none,
            parse_error("non-associative operator used in an associative " ++
                "manner", S, Ts, _)
        )
    ;
        % The pushed op binds more loosely than the top one.
        O      = (>),
        Es0 = [EA, EB | Es1],
        EC  = expr(raw_app_init(Op0 ^ bin_op_name, operator_app, [EB, EA]),
            [], EInfo0),
        Es2 = [EC | Es1],
        push_bin_op(Op - EInfo, Es2, Es, Ops1, Ops, S, Ts)
    ).

:- pred push_expr(expr::in, expr_stack::in, expr_stack::out) is det.

push_expr(E, Es, [E | Es]).

:- pred close_expr(expr_stack::in, bin_op_stack::in, expr::out) is semidet.

close_expr([E], _, E).
close_expr([EA, EB | Es], [Op - EInfo | Ops], E) :-
    E0 = expr_init(raw_app_init(Op ^ bin_op_name, operator_app, [EB, EA]),
            EInfo),
    close_expr([E0 | Es], Ops, E).

%-----------------------------------------------------------------------------%

    % zm_un_op_expr ::= un_op zm_expr_atom
    %
:- pred zm_un_op_expr(bool::in) : parser(raw_expr) `with_inst` parser.

zm_un_op_expr(IsNumE, UnOpRawE, S, !Ts) :-
    Lang = S^lang,
    next_token(op(Name), _, !Ts),
    is_un_op(Lang, Name, IsNumOp),
    ( if IsNumE = yes
    then IsNumOp = yes           % Semidet.
    else true
    ),
    zm_expr_atom(IsNumE, E, S, !Ts),
    UnOpRawE = raw_app_init(Name, operator_app, [E]).

%-----------------------------------------------------------------------------%

    % zm_if_then_else_expr ::= `if' expr `then' expr
    %                          ( `elseif' expr `then' expr )*
    %                          `else' expr `endif'
:- pred zm_if_then_else_expr : parser(raw_expr) `with_inst` parser.

zm_if_then_else_expr(IfThenElseRawE, S, !Ts) :-
    keyword("if", S, !Ts),
    expect("expression after `if'",           zm_expr, IfE, S, !Ts),
    expect("`then' after `if' expression",    keyword("then"), _, S, !Ts),
    expect("expression after `then'",         zm_expr, ThenE, S, !Ts),
    zero_or_more(zm_elseif_clause, ElseifClauses, S, !Ts),
    expect("`else' after `then' expression",  keyword("else"), _, S, !Ts),
    expect("expression after `else'",         zm_expr, ElseE, S, !Ts),
    expect("`endif' after `else' expression", keyword("endif"), _, S, !Ts),
    IfThenElseRawE = nestify_elseifs(IfE, ThenE, ElseifClauses, ElseE).

:- pred zm_elseif_clause : parser(pair(expr)) `with_inst` parser.

zm_elseif_clause(ElseifE - ElsethenE, S, !Ts) :-
    keyword("elseif", S, !Ts),
    expect("expression after `elseif'",         zm_expr, ElseifE, S, !Ts),
    expect("`then' after `elseif' expression",  keyword("then"), _, S, !Ts),
    expect("expression after `then'",           zm_expr, ElsethenE, S, !Ts).

    % Converts an if-then-else with zero or more 'elseif' clauses into nested
    % if-then-elses without 'elseif' clauses.
    % Eg:
    %   if C1 then E1 elseif C2 then E2 elseif C3 then E3 else E4 endif
    % becomes:
    %   if_then_else(C1, E1 if_then_else(C2, E2, if_then_else(C3, E3, E4)))
    %
:- func nestify_elseifs(expr, expr, list(pair(expr)), expr) = raw_expr.

nestify_elseifs(IfE, ThenE, [], ElseE) =
    if_then_else(IfE, ThenE, ElseE).

nestify_elseifs(IfE, ThenE, [ElseifE - ElsethenE | Xs], ElseE) =
    if_then_else(
        IfE,
        ThenE,
        expr_init(nestify_elseifs(ElseifE, ElsethenE, Xs, ElseE),
             ElseifE^expr_info)
    ).

%-----------------------------------------------------------------------------%

    % zm_gen_call_expr ::=
    %   ident_expr_or_quoted_op_expr `(' zm_comp_tail `)' `(' zm_expr `)'
    %
:- pred zm_gen_call_expr : parser(raw_expr) `with_inst` parser.

zm_gen_call_expr(GenCallRawE, S, !Ts) :-
    % Because gen-calls can look very similar to calls, we don't know it's a
    % gen-call for sure until we either see `where' after the generators, or we
    % see the leading `(' for the body expression.  (For example, if we see
    % "f(i in S) ..." it could be a call because `in' is a binary operator.)
    % So we keep things semidet until these are satisfied.  We know it's
    % definitely not a gen-call if we see a ',' outside a possible generator,
    % eg. in "f(X in S, T)".
    %
    name_or_quoted_op(Name, S, !Ts),
    next_token(lparen, _, !Ts),
    zm_comp_tail("generator call", Generators-MaybeWhereE, S, !Ts),
    next_token(rparen, _, !Ts),

    ( if MaybeWhereE = yes(_) then
        expect_token("`(' after first part of generator call", lparen, S, !Ts)
      else if next_token(lparen, _, !Ts) then
        true
      % If what follows doesn't start with a `(' but it is an expression, it's
      % likely they forgot the parentheses.
      else if Ts0 = !.Ts, zm_expr(_, S, !Ts) then
        parse_error("parentheses required around body expression in "
            ++ "generator call",
            S, Ts0, _)
      else
        % This must be a normal call that looks a lot like a generator call,
        % eg. "foo(x in S)".
        fail
    ),
    expect("body expression after `(' in generator call",
        zm_expr, BodyE, S, !Ts),
    expect_token("`)' after body expression in generator call",
        rparen, S, !Ts),
    ArgE = expr(comprehension(simple_array_comp(BodyE), Generators,
        MaybeWhereE), [], BodyE^expr_info),
    GenCallRawE = raw_app_init(Name, gen_call_app, [ArgE]).

:- pred zm_where_expr(string::in) : parser(expr) `with_inst` parser.

zm_where_expr(What, E, S, !Ts) :-
    keyword("where", S, !Ts),
    expect("expression after `where' in " ++ What, zm_expr, E, S, !Ts).

%-----------------------------------------------------------------------------%

    % zm_paren_or_tuple_expr ::= `(' zm_expr `,' ... `)'
    %
:- pred zm_paren_or_tuple_expr(bool::in)
        : parser(pair(raw_expr, exprs)) `with_inst` parser.

zm_paren_or_tuple_expr(IsNumE, RawE-AnnEs, S, !Ts) :-
    brackets(lparen, comma_list(zm_expr), rparen, Es, S, !Ts),
    ( if Es = [E0] then
        % parentheses case
        RawE = E0^raw_expr,
        AnnEs = E0^annotations
    else
        % tuple case
        IsNumE = no,       % semidet
        RawE = lit_tuple(Es),
        AnnEs = []
    ).

%-----------------------------------------------------------------------------%

    % zm_set_literal ::= `{' [ zm_expr `,' ... ] `}'
    % zm_set_comp    ::= `{' zm_expr `|' zm_comp_tail `}'
    %
:- pred zm_set_expr : parser(raw_expr) `with_inst` parser.

zm_set_expr(RawE, S, !Ts) :-
    next_token(lcurly, _, !Ts),
    ( if next_token(rcurly, _, !Ts) then
        % empty set
        RawE = lit_set([])

    else if zm_expr(E0, S, !Ts) then
        ( if ( optional_token(comma, !Ts), next_token(rcurly, _, !Ts) ) then
            % singleton literal set expression
            RawE = lit_set([E0])
        else if next_token(comma, _, !Ts) then
            % non-singleton literal set expression
            expect("`}' or list of expressions after `,' in set expression",
                comma_list(zm_expr), Es0, S, !Ts),
            expect_token("`}' after list of expressions in set expression",
                rcurly, S, !Ts),
            RawE = lit_set([E0 | Es0])
        else if next_token(pipe, _, !Ts) then
            % set comprehension
            expect("one or more generators after `|' in set comprehension",
                zm_comp_tail("set comprehension"),
                Generators-MaybeWhereE, S, !Ts),
            expect_token("`}' at end of set comprehension",
                rcurly, S, !Ts),
            RawE = comprehension(set_comp(E0), Generators, MaybeWhereE)
        else
            expected("`}' or `,' or `|' after first expression in " ++
                "set expression", S, !Ts)
        )

    else
        expected("expression or `}' after `{' in set expression", S, !Ts)
    ).

    % zm_comp_tail ::= zm_generator `,' ... [ `where' zm_expr ]
    %
:- pred zm_comp_tail(string::in)
        : parser(pair(generators, maybe(expr))) `with_inst` parser.

zm_comp_tail(What, Generators-MaybeWhereE, S, !Ts) :-
    comma_list(zm_generator, Generators, S, !Ts),
    optional(zm_where_expr(What), MaybeWhereE, S, !Ts).

    % zm_generator ::= ident `,' ... `in' zm_expr
    %
:- pred zm_generator : parser(generator) `with_inst` parser.

zm_generator(generator(Vars, E), S, !Ts) :-
    comma_list(ident, Vars, S, !Ts),
    next_token(op("in"), _, !Ts),
    expect("expression after `in'",
        zm_expr, E, S, !Ts).

%-----------------------------------------------------------------------------%

    % zm_array_access_tail ::= `[' zm_expr `,' ... `]'
    %
:- pred zm_array_access_tail(expr::in) : parser(expr) `with_inst` parser.

zm_array_access_tail(EIn, E, S, !Ts) :-
    % We could use 'brackets' here, but doing it piece-meal gives better error
    % messages.
    next_token(lsquare, _, !Ts),
    expect("list of expressions within square brackets",
        comma_list(zm_expr), IndexEs, S, !Ts),
    expect_token("`]' after expression in array access",
        rsquare, S, !Ts),
    E = expr_init(array_access(EIn, IndexEs), EIn^expr_info).

%-----------------------------------------------------------------------------%

    % zm_simple_array_literal ::= `[' zm_expr `,' ... `]'
    % zm_simple_array_comp    ::= `[' zm_expr `|' zm_comp_tail `]'
    %
    % zm_indexed_array_literal ::= `[' zm_index_expr `,' ... `]'
    % zm_indexed_array_comp    ::= `[' zm_index_expr `|' zm_comp_tail `]'
    %
    % "[]" is parsed as a simple array.
    %
:- pred zm_array_expr : parser(raw_expr) `with_inst` parser.

zm_array_expr(RawE, S, !Ts) :-
    next_token(lsquare, _, !Ts),
    ( if next_token(rsquare, _, !Ts) then
        % Empty array... make it a simple array (rather than an indexed array).
        RawE = lit_simple_array([])

      % Simple array expression...
    else if zm_expr(E0, S, !Ts) then
        % It's a simple array.
        ( if optional_token(comma, !Ts), next_token(rsquare, _, !Ts) then
            % singleton simple array literal
            RawE = lit_simple_array([E0])
        else if next_token(comma, _, !Ts) then
            % non-singleton simple array literal
            expect("`]' or list of expressions after `,' in " ++
                   "simple array expression",
                comma_list(zm_expr), Es0, S, !Ts),
            expect_token("`]' after list of expressions in " ++
                         "simple array expression",
                rsquare, S, !Ts),
            RawE = lit_simple_array([E0 | Es0])
        else if next_token(pipe, _, !Ts) then
            % simple array comprehension
            expect("one or more generators after `|' in simple array " ++
                "comprehension", zm_comp_tail("simple array comprehension"),
                Generators-MaybeWhereS, S, !Ts),
            expect_token("`]' at end of simple array comprehension",
                rsquare, S, !Ts),
            RawE = comprehension(simple_array_comp(E0), Generators,
                MaybeWhereS)
        else
            expected("`]' or `,' or `|' after first expression in simple array"
                ++ " expression", S, !Ts)
        )

    else
        expected("expression or indexed expression after `['", S, !Ts)
    ).

    % zm_index_expr ::= zm_expr `:' zm_expr
    %
:- pred zm_index_expr : parser(index_expr) `with_inst` parser.

zm_index_expr(IndexE - E, S, !Ts) :-
    zm_expr(IndexE, S, !Ts),
    next_token(colon, _, !Ts),
    expect("expression after `:' in indexed array expression",
        zm_expr, E, S, !Ts).

    % zm_simple_array_literal_2d ::= `[|' [ (zm_expr `,' ...) `|' ... ] `|]'
    %
:- pred zm_simple_array_literal_2d : parser(raw_expr) `with_inst` parser.

zm_simple_array_literal_2d(RawE, S, !Ts) :-
    next_token(lsquarepipe, LineNum, !Ts),
    ( if next_token(rpipesquare, _, !Ts) then
        Dim1 = 0, Dim2 = 0, Es = []
    else
        pipe_list_0( comma_list(zm_expr), Ess, S, !Ts),
        Dim1 = length(Ess),
        ( if Ess = [HeadEs | _]
        then Dim2 = length(HeadEs)
        else Dim2 = 0
        ),
        list.condense(Ess, Es),
        P = (pred(P_Es::in) is semidet :- length(P_Es) = Dim2),
        ( if all_true(P, Ess) then
            true
        else
            expected("all sub-arrays of simple 2d array literal to have " ++
                "the same length", S, !Ts)
        ),
        % We put this after the sub-array length check.  That way, if the
        % sub-array length check fails, it says
        %
        %   "syntax error at `|]'; expected all sub-arrays..."
        %
        % and the `|]' seems like the best token to mention for that (better
        % than the first token after the `|]', for example).
        %
        expect_token("`|]' at end of simple 2d array literal",
            rpipesquare, S, !Ts)
    ),
    % We translate 2d array literals as calls to 'array2d'.
    EInfo = expr_info_init(src_locn(S^filename, LineNum)),
    OneE  = expr_init(lit(int(1)), EInfo),
    DimE1 = expr_init(lit(int(Dim1)), EInfo),
    DimE2 = expr_init(lit(int(Dim2)), EInfo),
    RangeE1 = expr_init(raw_app_init("..", operator_app, [OneE, DimE1]), EInfo),
    RangeE2 = expr_init(raw_app_init("..", operator_app, [OneE, DimE2]), EInfo),
    ArrE = expr_init(lit_simple_array(Es), EInfo),
    RawE = raw_app_init("array2d", array2d_literal, [RangeE1, RangeE2, ArrE]).

%-----------------------------------------------------------------------------%

    % This could be a call, a non-flat enum literal, or an annotation literal.
    %
    % zm_ident_or_quoted_op_or_call_like_expr ::=
    %   ident_or_quoted_op [ `(' zm_expr `,' ... `)' ]
    %
:- pred zm_ident_or_quoted_op_or_call_like_expr(bool::in)
        : parser(raw_expr) `with_inst` parser.

zm_ident_or_quoted_op_or_call_like_expr(_IsNumE, RawE, S, !Ts) :-
    ident_or_quoted_op(Id, S, !Ts),
    ( if
        brackets(lparen, comma_list(zm_expr), rparen, Es, S, !Ts)
    then
        % This could actually be a simple non-flat enum literal, or an
        % annotation literal but they are syntactically indistinguishable from
        % applications.  So we just always use 'app' here, and convert it to
        % 'lit_nonflat_enum_simple' or 'lit_ann' if necessary during type-inst
        % checking.
        RawE = raw_app_init(Id ^ id_name, predfunc_app, Es)

        % Handle the "foo()" case specially, since it seems reasonably likely
        % someone would try it.  They need to write "foo" instead.
    else if
        Ts0 = !.Ts,
        next_token(lparen, _, !Ts),
        next_token(rparen, _, !Ts)
    then
        parse_error("expressions with no arguments require no parentheses",
            S, Ts0, _)
    else
        RawE = ident(Id)
    ).
%-----------------------------------------------------------------------------%

    % zm_named_expr ::= ident `:' zm_expr
    %
:- pred zm_named_expr(string::in) : parser(named_expr) `with_inst` parser.

zm_named_expr(What, Name - E, S, !Ts) :-
    name(Name, S, !Ts),
    next_token(colon, _, !Ts),
    expect("expression after `:' in " ++ What, zm_expr, E, S, !Ts).

%-----------------------------------------------------------------------------%

    % zm_let_expr ::= `let' `{' zm_local_var `,' ... `}' `in' zm_expr
    %
:- pred zm_let_expr : parser(raw_expr) `with_inst` parser.

zm_let_expr(let(LetVars, E), S, !Ts) :-
    keyword("let", S, !Ts),
    expect("list of variable declarations within braces after `let'",
        brackets(lcurly, comma_list(zm_local_var_decl), rcurly),
        LetVars, S, !Ts),
    expect_token("`in' after list of local variable declarations in let " ++
        "expression", op("in"), S, !Ts),
    expect("expression after `in' in let expression",
        zm_expr, E, S, !Ts).

    % zm_local_var_decl ::= zm_ti_expr `:' ident annotations [ '=' expr ]
    %
    % This is the same as zm_var_decl_item, except the output term is
    % different, in particular, it uses an 'id' instead of a 'name'.
    %
:- pred zm_local_var_decl : parser(local_var) `with_inst` parser.

zm_local_var_decl(local_var(TIE, Id, AnnEs, MaybeInitE), S, !Ts) :-
    zm_ti_expr(TIE, S, !Ts),
    expect_token("`:' after type in local variable declaration",
        colon, S, !Ts),
    expect("identifier after `:' in local variable declaration",
        ident, Id, S, !Ts),
    zm_annotations(AnnEs, S, !Ts),
    ( if next_token(op("="), _, !Ts) then
        expect("expression after `=' in local variable declaration",
            zm_expr, InitE, S, !Ts),
        MaybeInitE = yes(InitE)
    else
        MaybeInitE = no
    ).

%-----------------------------------------------------------------------------%

:- pred zm_anon_var : parser(raw_expr) `with_inst` parser.

zm_anon_var(anon_var, _, !Ts) :-
    next_token(underscore, _, !Ts).

%-----------------------------------------------------------------------------%
% Zinc/MiniZinc Literals
%-----------------------------------------------------------------------------%

    % zm_literal ::= boolean_literal
    %             |  int_literal
    %             |  float_literal
    %             |  string_literal
    %
    % zm_boolean_literal ::= `true' | `false'
    %
    % Int, float and string literals are handled by the lexer.
    %
:- pred zm_literal(bool::in) : parser(raw_expr) `with_inst` parser.

zm_literal(IsNumE, lit(Lit), _S, !Ts) :-
    next_token(Tok, _, !Ts),
    ( if      Tok = int(Int)                      then Lit = int(Int)
      else if Tok = float(FloatStr)               then Lit = floatstr(FloatStr)
      else if IsNumE = no, Tok = keyword("false") then Lit = bool(no)
      else if IsNumE = no, Tok = keyword("true")  then Lit = bool(yes)
      else if IsNumE = no, Tok = string(String)   then Lit = string(String)
      else
        fail
    ).

%-----------------------------------------------------------------------------%
% Utility predicates.
%-----------------------------------------------------------------------------%

:- func p_ti_expr_init(raw_ti_expr, int, parser_state) = ti_expr.

p_ti_expr_init(RawTIE, LineNum, S) =
    ti_expr(RawTIE, expr_info_init(src_locn(S^filename, LineNum))).

:- func p_expr_init(raw_expr, int, parser_state) = expr.

p_expr_init(RawE, LineNum, S) =
    expr_init(RawE, expr_info_init(src_locn(S^filename, LineNum))).

%-----------------------------------------------------------------------------%

:- pred optional(parser(T)::in(parser))
        : parser(maybe(T)) `with_inst` parser_det.

optional(P, MaybeX, S, !Ts) :-
    ( if P(X, S, !Ts) then MaybeX = yes(X) else MaybeX = no ).

%-----------------------------------------------------------------------------%

:- pred zero_or_more(parser(T)::in(parser))
        : parser(list(T)) `with_inst` parser_det.

zero_or_more(P, Xs, S, !Ts) :-
    ( if P(X, S, !Ts) then
        zero_or_more(P, Xs0, S, !Ts),
        Xs = [X | Xs0]
      else
        Xs = []
    ).

%-----------------------------------------------------------------------------%

    % Parse something wrapped in brackets.
    %
:- pred brackets(token::in, parser(T)::in(parser), token::in)
    : parser(T) `with_inst` parser.

brackets(L, P, R, X, S, !Ts) :-
    next_token(L, _, !Ts),
    P(X, S, !Ts),
    expect_token("`" ++ R^show ++ "'", R, S, !Ts).

:- pred brackets_for_det_parser(token::in, parser(T)::in(parser_det),
        token::in) : parser(T) `with_inst` parser.

brackets_for_det_parser(L, P, R, X, S, !Ts) :-
    next_token(L, _, !Ts),
    P(X, S, !Ts),
    expect_token("`" ++ R^show ++ "'", R, S, !Ts).

%-----------------------------------------------------------------------------%

    % Parse a comma-separated list.
    %
:- pred comma_list(parser(T)::in(parser)) : parser(list(T)) `with_inst` parser.

comma_list(P, [X | Xs], S, !Ts) :-
    P(X, S, !Ts),
    zero_or_more(comma `andthen` P, Xs, S, !Ts),
    optional_token(comma, !Ts).

:- pred comma_list_0(parser(T)::in(parser))
        : parser(list(T)) `with_inst` parser_det.

comma_list_0(P, Xs, S, !Ts) :-
    ( if comma_list(P, Xs0, S, !Ts) then Xs = Xs0 else Xs = [] ).

:- pred pipe_list(parser(T)::in(parser))
        : parser(list(T)) `with_inst` parser.

pipe_list(P, [X | Xs], S, !Ts) :-
    P(X, S, !Ts),
    zero_or_more(pipe `andthen` P, Xs, S, !Ts),
    optional_token(pipe, !Ts).

:- pred pipe_list_0(parser(T)::in(parser))
        : parser(list(T)) `with_inst` parser_det.

pipe_list_0(P, Xs, S, !Ts) :-
    ( if pipe_list(P, Xs0, S, !Ts) then Xs = Xs0 else Xs = [] ).

    % Tok `andthen` P matches Tok, discards the result, then matches P.
    %
:- pred andthen(token::in, parser(T)::in(parser))
        : parser(T) `with_inst` parser.

andthen(Tok, P, X, S, !Ts) :-
    next_token(Tok, _, !Ts),
    P(X, S, !Ts).

    % Like 'andthen', but if Tok matches, the P must follow.
:- pred andthen2(string::in, token::in, parser(T)::in(parser))
        : parser(T) `with_inst` parser.

andthen2(What, Tok, P, X, S, !Ts) :-
    next_token(Tok, _, !Ts),
    expect(What, P, X, S, !Ts).

%-----------------------------------------------------------------------------%

    % Parse the given keyword token.
    %
:- pred keyword(string::in) : parser(unit) `with_inst` parser.

keyword(Keyword, unit, _S, !Ts) :-
    next_token(Tok, _, !Ts),
    Tok = keyword(Keyword).

:- pred keyword(string::in, parser_state::in, tokens::in, tokens::out)
        is semidet.

keyword(Keyword, S, !Ts) :-
    keyword(Keyword, _, S, !Ts).

%-----------------------------------------------------------------------------%

    % These two parse identifiers.  The first one returns an 'id', ie. a
    % (name, scope-number) pair.  The second one returns just the name.
    %
:- pred ident : parser(id) `with_inst` parser.

ident(Id, S, !Ts) :-
    name(Name, S, !Ts),
    Id = id_init(Name).

:- pred name : parser(zinc_name) `with_inst` parser.

name(Name, _S, !Ts) :-
    next_token(ident(Name), _, !Ts).

%-----------------------------------------------------------------------------%

:- pred f_varname : parser(id) `with_inst` parser.

f_varname(Id, _S, !Ts) :-
    next_token(Token, _, !Ts),
    ( Token = ident(Name)
    ; Token = underscore_ident(Name)
    ),
    Id = id_init(Name).

%-----------------------------------------------------------------------------%

    % Nb: the meaning of the 'id' type (and likewise the 'name' type) is
    % slightly different to the meaning of the 'ident' non-terminal in the
    % grammar:  the 'id' type admits quoted operator names.  The reason is that
    % once we've got through the parser, there's no point represent identifers
    % and quoted-operators any differently.
:- pred ident_or_quoted_op : parser(id)   `with_inst` parser.
:- pred name_or_quoted_op  : parser(zinc_name) `with_inst` parser.

ident_or_quoted_op(Id, S, !Ts) :-
    name_or_quoted_op(Name, S, !Ts),
    Id = id_init(Name).

name_or_quoted_op(Name, _S, !Ts) :-
    ( if next_token(ident(Name0), _, !Ts) then
        Name = Name0
      else if next_token(quoted_op(Name0), _, !Ts) then
        Name = Name0
      else
        fail
    ).

%-----------------------------------------------------------------------------%
% Reporting errors
%-----------------------------------------------------------------------------%

    % expect(ErrorMessage, P) matches P or, if that fails, throws an
    % exception with an error message identifying the problem and location.
    %
:- pred expect(string::in, parser(T)::in(parser))
    : parser(T) `with_inst` parser_det.

expect(Thing, P, X, S, !Ts) :-
    ( if P(X0, S, !Ts) then
        X = X0
      else
        expected(Thing, S, !Ts)
    ).

    % Throws a parse error if next token is not the given token.
    %
:- pred expect_token(string::in, token::in, parser_state::in, tokens::in,
        tokens::out) is det.

expect_token(Thing, Tok, S, !Ts) :-
    ( if next_token(Tok, _, !Ts) then
        true
      else
        expected(Thing, S, !Ts)
    ).

    % Throws a parse error if something unexpected happens.
    %
:- pred expected(string::in, parser_state::in, tokens::in, tokens::out)
    is erroneous.

expected(Thing, S, !Ts) :-
    parse_error("expected " ++ Thing, S, !Ts).

:- pred parse_error(string::in, parser_state::in, tokens::in, tokens::out)
    is erroneous.

parse_error(MsgStr, S, !Ts) :-
    make_parse_error(MsgStr, Err, S, !Ts),
    throw(Err).

    % Create a parse error in the standard way.
    %
:- pred make_parse_error(string::in)
    : parser(zinc_error) `with_inst` parser_det.

make_parse_error(ErrMsg0, Err, S, !Ts) :-
    % We've had a parse error.  First try to work out if it was a lex error,
    % by scanning forward to the next semicolon or EOF, and complaining if any
    % were found.  Otherwise, issue a parse error.
    ( if look_for_lex_errors({LexErrMsg, LineNum, ColNum}, S, !Ts) then
        ErrLocn = file_line_column(S^filename, LineNum, ColNum),
        ErrMsg = LexErrMsg
    else
        % Re-get the first token in the failing sequence.
        next_token(Tok, LineNum, !Ts),
        ErrLocn = file_line(S^filename, LineNum),
        % Nb: because all the parser errors are very simple, they can all be
        % handled with 'words' -- ie. have line breaks inserted anywhere within
        % them.
        ErrMsg = [
            words("syntax error at"), suffix(quote(Tok ^ show), ";"),
            words(ErrMsg0)
        ]
    ),
    Err = zinc_error(ErrLocn, ErrMsg).

:- pred look_for_lex_errors : parser({error_msg, int, int}) `with_inst` parser.

look_for_lex_errors(Out, S, !Ts) :-
    next_token(Tok, LineNum, !Ts),
    ( if Tok = error_token(ErrMsg, ColNum) then
        Out = {ErrMsg, LineNum, ColNum}
    else if ( Tok = semicolon ; Tok = eof ) then
        false
    else
        look_for_lex_errors(Out, S, !Ts)
    ).

%-----------------------------------------------------------------------------%
:- end_module zinc_parser.
%-----------------------------------------------------------------------------%
