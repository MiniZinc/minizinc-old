%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2006-2007 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Nicholas Nethercote <njn@csse.unimelb.edu.au>
%
% A lexer for Zinc, MiniZinc, and FlatZinc.
%
%-----------------------------------------------------------------------------%

:- module zinc_lexer.
:- interface.

%---------------------------------------------------------------------------%

:- import_module zinc_common.
:- import_module zinc_error.

:- import_module bool.

%-----------------------------------------------------------------------------%

:- type tokens.

:- type token
    --->    int(int)
            % [0-9]+            (decimal)
            % | 0x[0-9A-Fa-f]+  (hexadecimal)
            % | 0o[0-7]+        (octal)

    ;       float(string)
            % [0-9]+.[0-9]+                 eg. 1.1
            % | [0-9]+.[0-9]+[Ee][-+]?[0-9]+  eg. 1.1e5
            % | [0-9]+       [Ee][-+]?[0-9]+  eg.  1e5
            % (Represented as a string to avoid any inaccuracies caused by
            %  rounding.)

    ;       string(string)
            % A C-style string literal.

    ;       ident(zinc_name)
            % Alphanumeric identifier.
            % [A-Z][A-Za-z0-9_]*

    ;       quoted_op(zinc_name)
            % Excludes the quotes (eg. "+", "union")

    ;       dollar_ident(zinc_name)
            % Excludes the '$' at the start.

    ;       keyword(string)
            % Excludes alphabetic operators (eg. "and").

    ;       op(zinc_name)
            % Includes alphabetic operators (eg. "and").

    ;       backquoted_op(zinc_name)
            % Excludes the backquotes.

    ;       underscore
            % '_'   
            % Not allowed in FlatZinc.

    ;       underscore_ident(zinc_name)    
            % An identifer with 0 or more underscores as a prefix.
            % Must match -*[A-Za-z][A-Za-z0-9_]*
            % Includes the underscores.
            % Only allowed in FlatZinc.

    ;       dot                     % '.'
    ;       lparen                  % '('
    ;       rparen                  % ')'
    ;       lcurly                  % '{'
    ;       rcurly                  % '}'
    ;       lsquare                 % '['
    ;       rsquare                 % ']'
    ;       lsquarepipe             % '[|'
    ;       rpipesquare             % '|]'
    ;       pipe                    % '|'
    ;       comma                   % ','
    ;       semicolon               % ';'
    ;       colon                   % ':'
    ;       double_colon            % '::'
    ;       right_arrow             % '-->'
    ;       eof
    ;       error_token(
                error_msg,          % Lexing error message.
                int                 % Column number (Nb: the line number is
            ).                      % stored in the 'tokens' list).

%-----------------------------------------------------------------------------%

    % Lexes the given file, returning a list of tokens.
    %
:- func lex_file(lang, int, string, string) = tokens.

    % Gets the next token in the list, and its line number.
    %
:- pred next_token(token::out, int::out, tokens::in, tokens::out) is det.

    % Gets the next token in the list, and its line number, without consuming
    % them.
:- pred peek_token(token::out, int::out, tokens::in) is det.

    % Consumes the next token if it matches the given token.
:- pred optional_token(token::in, tokens::in, tokens::out) is det.

:- instance show(token).

%-----------------------------------------------------------------------------%

:- type bin_op_attrs
    --->    bin_op_attrs(
                bin_op_name             :: zinc_name,
                bin_op_associativity    :: associativity,
                bin_op_precedence       :: precedence
            ).

:- type associativity
    --->    left
    ;       right
    ;       none.

:- type precedence == int.

    % Binary operators.  The bool indicates if it's a Zinc integer operator.
:- pred is_bin_op(lang::in, zinc_name::in, associativity::out, precedence::out,
                                      bool::out) is semidet.

:- pred backquoted_bin_op(lang::in, associativity::out, precedence::out)
        is semidet.

    % Unary operators.  The bool indicates if it's a Zinc integer operator.
:- pred is_un_op(lang::in, zinc_name::in, bool::out) is semidet.

%-----------------------------------------------------------------------------
%-----------------------------------------------------------------------------

:- implementation.

:- import_module char.
:- import_module int.
:- import_module integer.
:- import_module list.
:- import_module string.
:- import_module std_util.
:- import_module unit.

%-----------------------------------------------------------------------------
% Lexing
%-----------------------------------------------------------------------------

:- type lexer0(T)   == ( pred(T,           src, int, int,      lexer_state,
                                                               lexer_state) ).
:- type lexer       == ( pred(      token, src, int, int, int, lexer_state,
                                                               lexer_state) ).
:- type op_lexer    == ( pred(bool, token, src, int, int, int, lexer_state,
                                                               lexer_state) ).

:- inst lexer0         == ( pred(    out, in, in,     out, in, out) is det ).
:- inst lexer0_semidet == ( pred(    out, in, in,     out, in, out) is semidet).
:- inst lexer          == ( pred(    out, in, in, in, out, in, out) is det ).
:- inst op_lexer       == ( pred(in, out, in, in, in, out, in, out) is det ).

    % Basic lexing state.  You might expect that we'd store the file index in
    % here too.  But we store that separately, and pass it around in a
    % separate argument pair, because it is updated for every character and it
    % makes the lexer significantly faster if we only have to
    % deconstruct/construct this state once per line instead of once per
    % character.
    %
:- type lexer_state
    --->    lexer_state(
                % These three correspond to the fields in io.posn, but
                % we don't use io.posn to avoid the (many) extra
                % (de)constructs.
                line_num    :: int,     % current line number
                line_index  :: int      % index of start of current line
            ).

    % The source file's language, file name, text and length.
    %
:- type src
    --->    src(
                lang        :: lang,
                filename    :: string,
                text        :: string,
                length      :: int
            ).

%-----------------------------------------------------------------------------%

:- pred get_char : lexer0(char) `with_inst` lexer0_semidet.

get_char(Char, Src, !I, !S) :-
    % This check is disabled because it almost halves the speed of parsing.
    %else_unexpected(!.I >= 0, "get_char: before start of string"),
    !.I < Src ^ length,         % semidet
    string.unsafe_index_next(Src ^ text, !I, Char),
    ( if Char = '\n' then
        !.S = lexer_state(LineNum0,     _LineIndex0),
        !:S = lexer_state(LineNum0 + 1, !.I)
      else
        true
    ).

:- func peek_char(src, int) = char is semidet.

peek_char(Src, I) = Char :-
    I < Src ^ length,         % semidet
    Char = unsafe_index(Src ^ text, I).

    % It's common to get a char, check it satisfies a predicate, and unget it
    % again if it fails.  This predicate does that efficiently.
    %
:- pred skip_char_if(pred(char)::pred(in) is semidet, src::in, int::in,
        int::out, lexer_state::in, lexer_state::out) is semidet.

skip_char_if(Pred, Src, !I, !S) :-
    % This check is disabled because it almost halves the speed of parsing.
    %else_unexpected(!.I >= 0, "skip_char_if: before start of string"),
    !.I < Src ^ length,     % semidet
    string.unsafe_index_next(Src ^ text, !I, Char),
    Pred(Char),                     % semidet
    ( if Char = '\n' then
        !.S = lexer_state(LineNum0,     _LineIndex0),
        !:S = lexer_state(LineNum0 + 1, !.I)
      else
        true
    ).

%-----------------------------------------------------------------------------%

    % We store tokens and line numbers in a fat list, because this list can
    % get very long and it's smaller than a list of pairs.
    %
:- type tokens
    --->    token_nil
    ;       token_cons(token, int, tokens).

lex_file(Lang, StartLineNum, FileName, FileText) = Toks :-
    Src = src(Lang, FileName, FileText, length(FileText)),
    S = lexer_state(StartLineNum, 0),
    lex_file_2(token_nil, RevToks, Src, 0, _, S, _),
    Toks = reverse_tokens(RevToks, token_nil).

    % We do the reverse-order thing to ensure that this is tail recursive,
    % because it calls itself many times.
    %
:- pred lex_file_2(tokens::in) : lexer0(tokens) `with_inst` lexer0.

lex_file_2(RevToks, NRevToks, Src, !I, !S) :-
    get_token(LineNum, Tok, Src, !I, !S),
    ( if Tok = eof then
        NRevToks = token_cons(Tok, LineNum, RevToks)
      else
        RevToks2 = token_cons(Tok, LineNum, RevToks),
        lex_file_2(RevToks2, NRevToks, Src, !I, !S)
    ).

:- func reverse_tokens(tokens, tokens) = tokens.

reverse_tokens(token_nil, Acc) = Acc.
reverse_tokens(token_cons(X, Y, Tokens), Acc) =
    reverse_tokens(Tokens, token_cons(X, Y, Acc)).

%-----------------------------------------------------------------------------%

    % We never empty the list completely -- the final EOF always remains.
    % We do this so that we always have the line number that the EOF appeared
    % on, which is necessary for reporting some errors.
    %
next_token(_,_,token_nil,_) :- unexpected($pred ++ ": empty token list").
next_token(Tok, LineNum, Toks0 @ token_cons(Tok, LineNum, Toks1), Toks) :-
    ( if Tok = eof then
        Toks = Toks0
      else
        Toks = Toks1
    ).

peek_token(_,_,token_nil) :- unexpected($pred ++ ": empty token list").
peek_token(Tok, LineNum, token_cons(Tok, LineNum, _)).

optional_token(Tok, !Ts) :- ( if next_token(Tok, _, !Ts) then true else true ).

%-----------------------------------------------------------------------------%

    % These predicates implement a DFA.  Each one consumes a single character.
    %
:- pred get_token(int::out, token::out, src::in, int::in, int::out,
            lexer_state::in, lexer_state::out) is det.

:- pred get_comment         : lexer0(unit) `with_inst` lexer0.
:- pred get_block_comment   : lexer0(unit) `with_inst` lexer0.
:- pred get_name             : lexer `with_inst` lexer.
:- pred get_underscored_name : lexer `with_inst` lexer.
:- pred get_post_zero       : lexer `with_inst` lexer.
:- pred get_post_int        : lexer `with_inst` lexer.
:- pred get_hex             : lexer `with_inst` lexer.
:- pred get_hex_2           : lexer `with_inst` lexer.
:- pred get_octal           : lexer `with_inst` lexer.
:- pred get_octal_2         : lexer `with_inst` lexer.
:- pred get_post_int_dot    : lexer `with_inst` lexer.
:- pred get_float_frac      : lexer `with_inst` lexer.
:- pred get_exponent        : lexer `with_inst` lexer.
:- pred get_exponent_2      : lexer `with_inst` lexer.
:- pred get_exponent_3      : lexer `with_inst` lexer.
:- pred get_post_lsquare    : lexer `with_inst` lexer.
:- pred get_post_pipe       : lexer `with_inst` lexer.
:- pred get_post_minus_f    : lexer `with_inst` lexer.
:- pred get_post_dot_f      : lexer `with_inst` lexer.
:- pred get_op_or_oplike(char::in)
                            : op_lexer `with_inst` op_lexer.
:- pred get_post_eq         : op_lexer `with_inst` op_lexer.
:- pred get_post_minus_zm   : op_lexer `with_inst` op_lexer.
:- pred get_post_minus_minus: op_lexer `with_inst` op_lexer.
:- pred get_post_plus       : op_lexer `with_inst` op_lexer.
:- pred get_post_lt         : op_lexer `with_inst` op_lexer.
:- pred get_post_lt_minus   : op_lexer `with_inst` op_lexer.
:- pred get_post_gt         : op_lexer `with_inst` op_lexer.
:- pred get_post_bang       : op_lexer `with_inst` op_lexer.
:- pred get_post_slash      : op_lexer `with_inst` op_lexer.
:- pred get_post_backslash  : op_lexer `with_inst` op_lexer.
:- pred get_post_dot        : op_lexer `with_inst` op_lexer.
:- pred get_string(           list(char)::in)
                            : lexer `with_inst` lexer.
:- pred get_string_escape(    list(char)::in)
                            : lexer `with_inst` lexer.
:- pred get_post_dollar     : lexer `with_inst` lexer.
:- pred get_dollar_name     : lexer `with_inst` lexer.
:- pred get_post_underscore : lexer `with_inst` lexer.
:- pred get_post_quote      : lexer `with_inst` lexer.
:- pred get_quoted_alpha_op : lexer `with_inst` lexer.
:- pred get_post_backquote  : lexer `with_inst` lexer.
:- pred get_backquoted_op   : lexer `with_inst` lexer.
:- pred get_post_colon      : lexer `with_inst` lexer.

get_token(LineNum, Tok, Src, !I, !S) :-
    I1 = !.I,
    some [!LineNum]
    ( if get_char(C, Src, !I, !S) then
        !:LineNum = !.S^line_num,
        % Ordering:
        % - must check for '0' before is_digit
        % - flatzinc: '-', '=', '.' checks must come before 'is_op_char'
        % - check for block comments must be before operators
        ( if is_whitespace(C)   then get_token(LineNum0, Tok, Src,     !I, !S),
                                     !:LineNum = LineNum0
          else if is_alpha(C)   then get_name(           Tok, Src, I1, !I, !S)
          else if C = '0'       then get_post_zero(      Tok, Src, I1, !I, !S)
          else if is_digit(C)   then get_post_int(       Tok, Src, I1, !I, !S)
          else if special(C, Tok0) then Tok = Tok0
          else if C = '['       then get_post_lsquare(   Tok, Src, I1, !I, !S)
          else if C = '|'       then get_post_pipe(      Tok, Src, I1, !I, !S)
          % Uncomment to get /* .. */ block comments in Zinc
          else if C = ('/'),
                skip_char_if(unify('*'), Src, !I, !S) then
                                   get_block_comment(  _,   Src,     !I, !S),
                                   get_token(LineNum0, Tok, Src,     !I, !S),
                                   !:LineNum = LineNum0
          else if is_op_char(C) then get_op_or_oplike(C, /*IsQuoted*/no,
                                                         Tok, Src, I1, !I, !S)
          else if C = ('%')     then get_comment(        _,   Src,     !I, !S),
                                     get_token(LineNum0, Tok, Src,     !I, !S),
                                     !:LineNum = LineNum0
          else if C = (':')     then get_post_colon(     Tok, Src, I1, !I, !S)
          else if C = '"'       then get_string(     [], Tok, Src, I1, !I, !S)
          else if C = '$'       then get_post_dollar(    Tok, Src, I1, !I, !S)
          else if C = '_'       then get_post_underscore(Tok, Src, I1, !I, !S)
          else if C = '\''      then get_post_quote(     Tok, Src, I1, !I, !S)
          else if C = '`'       then get_post_backquote( Tok, Src, I1, !I, !S)
          else
            lex_error(Tok, "invalid character `" ++ char_to_string(C) ++ "'",
                      I1, !.S)
        ),
        LineNum = !.LineNum
      else
        Tok = eof,
        LineNum = !.S^line_num
    ).

get_comment(unit, Src, !I, !S) :-
    ( if skip_char_if(isnt(unify('\n')), Src, !I, !S) then
        get_comment(_, Src, !I, !S)
      else
        true
    ).

get_block_comment(unit, Src, !I, !S) :-
    ( if get_char(C, Src, !I, !S) then
        ( if C = ('*') then
            ( if get_char(C2, Src, !I, !S) then
                ( if C2 = ('/') then
                    true
                  else
                    get_block_comment(_, Src, !I, !S)
                )
              else
                true
            )
          else
            get_block_comment(_, Src, !I, !S)
        )
      else
        true
    ).

get_name(Tok, Src, I1, !I, !S) :-
    ( if skip_char_if(is_alnum_or_underscore, Src, !I, !S) then
        get_name(Tok, Src, I1, !I, !S)
      else
        Tok = make_name(Src, I1, !.I, !.S)
    ).
                
get_underscored_name(Tok, Src, I1, !I, !S) :-
    ( if skip_char_if(unify('_'), Src, !I, !S) then
        get_underscored_name(Tok, Src, I1, !I, !S)
      else
        ( if get_char(C, Src, !I, !S) then
            ( if is_alpha(C) then
                get_underscored_name_2(Tok, Src, I1, !I, !S)
              else if is_digit(C) then
                lex_error(Tok, "first non-underscore character" ++
                    " must be a letter", I1, !.S)
              else
                lex_error(Tok,
                    "expected a letter after `_'", I1, !.S)
            )
          else
            Tok = eof
        )
    ).

:- pred get_underscored_name_2 : lexer `with_inst` lexer.

get_underscored_name_2(Tok, Src, I1, !I, !S) :-
    ( if skip_char_if(is_alnum_or_underscore, Src, !I, !S) then
        get_underscored_name_2(Tok, Src, I1, !I, !S)
      else
        % NOTE: no FlatZinc keywords begin with an underscore.
        grab_substring(Name, Src, I1, !.I),
        Tok = underscore_ident(Name)
    ).

get_post_zero(Tok, Src, I1, !I, !S) :-
    ( if get_char(C, Src, !I, !S),
         ( if      is_digit(C) then get_post_int(    Tok0, Src, I1, !I, !S)
           else if C = ('.')   then get_post_int_dot(Tok0, Src, I1, !I, !S)
           else if C = 'e'     then get_exponent(    Tok0, Src, I1, !I, !S)
           else if C = 'E'     then get_exponent(    Tok0, Src, I1, !I, !S)
           else if C = 'x'     then get_hex(         Tok0, Src, I1, !I, !S)
           else if C = 'o'     then get_octal(       Tok0, Src, I1, !I, !S)
           else                     fail
         )
      then
        Tok = Tok0
      else
        Tok = int(0)
    ).

get_post_int(Tok, Src, I1, !I, !S) :-
    ( if get_char(C, Src, !I, !S),
         ( if      is_digit(C) then get_post_int(    Tok0, Src, I1, !I, !S)
           else if C = ('.')   then get_post_int_dot(Tok0, Src, I1, !I, !S)
           else if C = 'e'     then get_exponent(    Tok0, Src, I1, !I, !S)
           else if C = 'E'     then get_exponent(    Tok0, Src, I1, !I, !S)
           else                     fail
         )
      then
        Tok = Tok0
      else
        Tok = make_int(10, Src, I1, !.I, !.S)
    ).

get_hex(Tok, Src, I1, !I, !S) :-
    ( if skip_char_if(is_hex_digit, Src, !I, !S) then
        get_hex_2(Tok, Src, I1, !I, !S)
      else
        lex_error(Tok, "expected hex digits after `0x'", I1, !.S)
    ).

get_hex_2(Tok, Src, I1, !I, !S) :-
    ( if skip_char_if(is_hex_digit, Src, !I, !S) then
        get_hex_2(Tok, Src, I1, !I, !S)
      else
        Tok = make_int(16, Src, I1, !.I, !.S)
    ).

get_octal(Tok, Src, I1, !I, !S) :-
    ( if skip_char_if(is_octal_digit, Src, !I, !S) then
        get_octal_2(Tok, Src, I1, !I, !S)
      else
        lex_error(Tok, "expected octal digits after `0o'", I1, !.S)
    ).

get_octal_2(Tok, Src, I1, !I, !S) :-
    ( if skip_char_if(is_octal_digit, Src, !I, !S) then
        get_octal_2(Tok, Src, I1, !I, !S)
      else if C = peek_char(Src, !.I), is_digit(C) then
        lex_error(Tok, "invalid digit `" ++ char_to_string(C)
            ++ "' in octal literal", I1, !.S)
      else
        Tok = make_int(8, Src, I1, !.I, !.S)
    ).

get_post_int_dot(Tok, Src, I1, !I, !S) :-
    ( if skip_char_if(is_digit, Src, !I, !S) then
        get_float_frac(Tok, Src, I1, !I, !S)
      else
        % Unget the '.'.  We don't have to worry about changing the line
        % number because the '.' cannot be a newline.
        !:I = !.I - 1,
        Tok = make_int(10, Src, I1, !.I, !.S)
    ).

get_float_frac(Tok, Src, I1, !I, !S) :-
    ( if get_char(C, Src, !I, !S),
         ( if   is_digit(C) then get_float_frac(Tok0, Src, I1, !I, !S)
           else if C = 'e'  then get_exponent(  Tok0, Src, I1, !I, !S)
           else if C = 'E'  then get_exponent(  Tok0, Src, I1, !I, !S)
           else                  fail
         )
      then
        Tok = Tok0
      else
        Tok = make_float(Src, I1, !.I, !.S)
    ).

get_exponent(Tok, Src, I1, !I, !S) :-
    ( if get_char(C, Src, !I, !S),
         ( if is_digit(C) then
             get_exponent_3(Tok0, Src, I1, !I, !S)
           else if ( C = ('+') ; C = ('-') ) then
             get_exponent_2(Tok0, Src, I1, !I, !S)
           else
             fail
         )
      then
        Tok = Tok0
      else
        lex_error(Tok, "no digits in float exponent", I1, !.S)
    ).

get_exponent_2(Tok, Src, I1, !I, !S) :-
    ( if skip_char_if(is_digit, Src, !I, !S) then
        get_exponent_3(Tok, Src, I1, !I, !S)
      else
        lex_error(Tok, "no digits in float exponent", I1, !.S)
    ).

get_exponent_3(Tok, Src, I1, !I, !S) :-
    ( if skip_char_if(is_digit, Src, !I, !S) then
        get_exponent_3(Tok, Src, I1, !I, !S)
      else
        Tok = make_float(Src, I1, !.I, !.S)
    ).

get_post_eq(IsQuoted, Tok, Src, I1, !I, !S) :-
    ( if      skip_char_if(unify(('=')), Src, !I, !S) then
        make_op("==", IsQuoted, Tok, Src, I1, !I, !S)
      else
        make_op("=",  IsQuoted, Tok, Src, I1, !I, !S)
    ).

get_post_minus_zm(IsQuoted, Tok, Src, I1, !I, !S) :-
    ( if      skip_char_if(unify(('>')), Src, !I, !S) then
        make_op("->", IsQuoted, Tok, Src, I1, !I, !S)
      else if skip_char_if(unify(('-')), Src, !I, !S) then
        get_post_minus_minus(IsQuoted, Tok, Src, I1, !I, !S)
      else
        make_op("-", IsQuoted, Tok, Src, I1, !I, !S)
    ).

get_post_minus_minus(IsQuoted, Tok, Src, I1, !I, !S) :-
    % "-->" is not an operator, so we can't make it an identifier by using
    % single quotes around it.
    ( if skip_char_if(unify(('>')), Src, !I, !S) then
        (   IsQuoted = no,
            Tok = right_arrow
        ;
            IsQuoted = yes,
            lex_error(Tok, "`-->' is not a valid operator", I1, !.S)
        )
      else
        % Unget the second '-'.  We don't have to worry about changing the
        % line number because the '-' cannot be a newline.
        !:I = !.I - 1,
        make_op("-", IsQuoted, Tok, Src, I1, !I, !S)
    ).

    % In FlatZinc, a leading '-' is lexed as part of a number.  In contrast,
    % Zinc/MiniZinc lex '-' as a unary minus, because in general it's not
    % possible to tell the difference between a binary minus and a leading
    % '-' while lexing Zinc/MiniZinc.  FlatZinc lacks binary minus, so this
    % problem doesn't arise, and it lacks unary minus, so the '-' must be
    % part of the numeric literal.
get_post_minus_f(Tok, Src, I1, !I, !S) :-
    ( if get_char(C, Src, !I, !S),
         ( if C = '0' then
             get_post_zero(Tok0, Src, I1, !I, !S)
           else if is_digit(C) then
             get_post_int(Tok0, Src, I1, !I, !S)
           else
             fail
         )
      then
        Tok = Tok0
      else
        lex_error(Tok, "expected a number after `-'", I1, !.S)
    ).

get_post_dot_f(Tok, Src, I1, !I, !S) :-
    ( if      skip_char_if(unify(('.')), Src, !I, !S) then
        Tok = op("..")
      else
        lex_error(Tok, "expected `.' after `.'", I1, !.S)
    ).

get_post_plus(IsQuoted, Tok, Src, I1, !I, !S) :-
    ( if      skip_char_if(unify(('+')), Src, !I, !S) then
        make_op("++", IsQuoted, Tok, Src, I1, !I, !S)
      else
        make_op("+",  IsQuoted, Tok, Src, I1, !I, !S)
    ).

get_post_lt(IsQuoted, Tok, Src, I1, !I, !S) :-
    ( if      skip_char_if(unify(('=')), Src, !I, !S) then
        make_op("<=", IsQuoted, Tok, Src, I1, !I, !S)
      else if skip_char_if(unify(('-')), Src, !I, !S) then
        get_post_lt_minus(     IsQuoted, Tok, Src, I1, !I, !S)
      else
        make_op("<",  IsQuoted, Tok, Src, I1, !I, !S)
    ).

get_post_lt_minus(IsQuoted, Tok, Src, I1, !I, !S) :-
    ( if skip_char_if(unify(('>')), Src, !I, !S) then
        OpStr = "<->"
      else
        OpStr = "<-"
    ),
    make_op(OpStr, IsQuoted, Tok, Src, I1, !I, !S).

get_post_gt(IsQuoted, Tok, Src, I1, !I, !S) :-
    ( if skip_char_if(unify(('=')), Src, !I, !S) then
        OpStr = ">="
      else
        OpStr = ">"
    ),
    make_op(OpStr, IsQuoted, Tok, Src, I1, !I, !S).

get_post_bang(IsQuoted, Tok, Src, I1, !I, !S) :-
    ( if skip_char_if(unify(('=')), Src, !I, !S) then
        make_op("!=", IsQuoted, Tok, Src, I1, !I, !S)
      else
        lex_error(Tok, "expected `=' after `!'", I1, !.S)
    ).

get_post_dot(IsQuoted, Tok, Src, I1, !I, !S) :-
    ( if skip_char_if(unify(('.')), Src, !I, !S) then
        make_op("..", IsQuoted, Tok, Src, I1, !I, !S)
      else
        (   IsQuoted = no,
            Tok = dot
        ;
            IsQuoted = yes,
            lex_error(Tok, "`.' is not a valid operator", I1, !.S)
        )
    ).

get_post_slash(IsQuoted, Tok, Src, I1, !I, !S) :-
    ( if skip_char_if(unify(('\\')), Src, !I, !S) then
        make_op("/\\", IsQuoted, Tok, Src, I1, !I, !S)
      else
        make_op("/", IsQuoted, Tok, Src, I1, !I, !S)
    ).

get_post_backslash(IsQuoted, Tok, Src, I1, !I, !S) :-
    ( if skip_char_if(unify(('/')), Src, !I, !S) then
        make_op("\\/", IsQuoted, Tok, Src, I1, !I, !S)
      else
        lex_error(Tok, "expected `/' after `\\'", I1, !.S)
    ).

get_post_lsquare(Tok, Src, _I1, !I, !S) :-
    ( if skip_char_if(unify(('|')), Src, !I, !S) then
        Tok = lsquarepipe
      else
        Tok = lsquare
    ).

get_post_pipe(Tok, Src, _I1, !I, !S) :-
    ( if skip_char_if(unify((']')), Src, !I, !S) then
        Tok = rpipesquare
      else
        Tok = pipe
    ).

    % It's worth noting here all the non-alpha operators, showing the common
    % prefixes, because it makes it easier to follow the operator lexing:
    %
    %   <-> <- <= <
    %   >= >
    %   -> -
    %   ++ +
    %   == =
    %   /\ /
    %   \/
    %   !=
    %   ..
    %   *
    %
get_op_or_oplike(C, IsQd, Tok, Src, I1, !I, !S) :-
    ( if      C = ('-') then get_post_minus_zm(    IsQd, Tok, Src, I1, !I, !S)
      else if C = ('=') then get_post_eq(          IsQd, Tok, Src, I1, !I, !S)
      else if C = ('+') then get_post_plus(        IsQd, Tok, Src, I1, !I, !S)
      else if C = ('<') then get_post_lt(          IsQd, Tok, Src, I1, !I, !S)
      else if C = ('>') then get_post_gt(          IsQd, Tok, Src, I1, !I, !S)
      else if C = ('!') then get_post_bang(        IsQd, Tok, Src, I1, !I, !S)
      else if C = ('.') then get_post_dot(         IsQd, Tok, Src, I1, !I, !S)
      else if C = ('/') then get_post_slash(       IsQd, Tok, Src, I1, !I, !S)
      else if C = ('\\')then get_post_backslash(   IsQd, Tok, Src, I1, !I, !S)
      else if C = ('*') then make_op(         "*", IsQd, Tok, Src, I1, !I, !S)
      else unexpected($pred ++ ": bad char")
    ).

    % We gather a list of chars (RevChars) so that we can transform escaped
    % characters as necessary along the way.
    %
get_string(RevChars, Tok, Src, I1, !I, !S) :-
    ( if get_char(C, Src, !I, !S),
         ( if      C = '"'    then
             Tok0 = make_string(RevChars)
           else if C = ('\\') then
             get_string_escape(RevChars, Tok0, Src, I1, !I, !S)
           else if C = ('\n') then
             fail
           else
             get_string([C | RevChars], Tok0, Src, I1, !I, !S)
         ) then
        Tok = Tok0
      else
        lex_error(Tok, "unterminated string literal", I1, !.S)
    ).

get_string_escape(RevChars, Tok, Src, I1, !I, !S) :-
    ( if get_char(C, Src, !I, !S) then
        ( if escape_char(C, EscC) then
            get_string( [EscC | RevChars], Tok, Src, I1, !I, !S)
          else
            lex_error(Tok, "unknown escape character `\\" ++ char_to_string(C)
                ++ "' in string literal", I1, !.S)
        )
      else
        lex_error(Tok, "unterminated string literal", I1, !.S)
    ).

get_post_dollar(Tok, Src, I1, !I, !S) :-
    ( if skip_char_if(is_alpha, Src, !I, !S) then
        get_dollar_name(Tok, Src, I1, !I, !S)
      else
        lex_error(Tok, "expected identifier after `$' in type variable",
            I1, !.S)
    ).

get_dollar_name(Tok, Src, I1, !I, !S) :-
    ( if skip_char_if(is_alnum_or_underscore, Src, !I, !S) then
        get_dollar_name(Tok, Src, I1, !I, !S)
      else
        Tok = make_dollar_name(Src, I1, !.I, !.S)
    ).

get_post_underscore(Tok, Src, I1, !I, !S) :-
    ( if C = peek_char(Src, !.I), is_alnum_or_underscore(C) then
        lex_error(Tok, "identifiers cannot begin with an underscore", I1, !.S)
      else
        Tok = underscore
    ).

get_post_quote(Tok, Src, I1, !I, !S) :-
    ( if get_char(C, Src, !I, !S),
         ( if is_op_char(C) then
             get_op_or_oplike(C, /*IsQuoted*/yes, Tok0, Src, I1, !I, !S)
           else if is_alpha(C) then
             get_quoted_alpha_op(Tok0, Src, I1, !I, !S)
           else
             fail
         )
      then
        Tok = Tok0
      else
        lex_error(Tok, "expected operator name after quote", I1, !.S)
    ).

get_quoted_alpha_op(Tok, Src, I1, !I, !S) :-
    ( if get_char(C, Src, !I, !S),
         ( if is_alpha(C) then
             get_quoted_alpha_op(Tok0, Src, I1, !I, !S)
           else if C = '\'' then
             Tok0 = make_quoted_alpha_op(Src, I1, !.I, !.S)
           else
             fail
         )
      then
        Tok = Tok0
      else
        lex_error(Tok, "expected operator name between quotes", I1, !.S)
    ).

get_post_backquote(Tok, Src, I1, !I, !S) :-
    ( if skip_char_if(is_alpha, Src, !I, !S) then
        get_backquoted_op(Tok, Src, I1, !I, !S)
      else
        lex_error(Tok, "expected alphanumeric identifier after back-quote",
            I1, !.S)
    ).

get_backquoted_op(Tok, Src, I1, !I, !S) :-
    ( if get_char(C, Src, !I, !S),
         ( if is_alnum_or_underscore(C) then
             get_backquoted_op(Tok0, Src, I1, !I, !S)
           else if C = '`' then
             Tok0 = make_backquoted_op(Src, I1, !.I, !.S)
           else
             fail
         )
      then
        Tok0 = Tok
      else
        lex_error(Tok, "unterminated back-quoted operator", I1, !.S)
    ).

get_post_colon(Tok, Src, _P0, !I, !S) :-
    ( if skip_char_if(unify((':')), Src, !I, !S) then
        Tok = double_colon
      else
        Tok = colon
    ).

%-----------------------------------------------------------------------------%
% Token builders and checkers
%-----------------------------------------------------------------------------%

:- type maker == ( func(src, int, int, lexer_state) = token ).

:- func make_name            : maker.
:- func make_int(int)        : maker.
:- func make_float           : maker.
:- func make_dollar_name     : maker.
:- func make_quoted_alpha_op : maker.
:- func make_backquoted_op   : maker.
    % This one is an op_lexer rather than a maker because it might chew up a
    % trailing single quote, if it's a quoted operator.
:- pred make_op(string::in)  : op_lexer `with_inst` op_lexer.
:- func make_string(list(char)) = token.

make_name(Src, I1, I, _S) = Tok :-
    grab_substring(Name, Src, I1, I),
    Lang = Src^lang,
    ( if is_keyword(      Name) then Tok = keyword(Name)
      else if is_op(Lang, Name) then Tok = op(Name)
      else                           Tok = ident(Name)
    ).

make_int(Base, Src, I1, I, S) = Tok :-
    grab_substring(SubS0, Src, I1, I),
    % Hack: If it's a hex or octal string, replace the 'x' or 'o' with a '0' so
    % that det_base_string_to_int/2 can handle it.  Note that this will
    % preserve any sign at the start of the integer.
    ( if Base = 8 then
        ( if string.replace(SubS0, "o", "0", SubS1) then SubS = SubS1
          else                               unexpected("no 'o' in oct int?")
        )
      else if Base = 16 then
        ( if string.replace(SubS0, "x", "0", SubS1) then SubS = SubS1
          else                               unexpected("no 'x' in hex int?")
        )
      else
        SubS = SubS0
    ),
    % If it's an integer that will definitely fit in 32-bits (judging from the
    % string length) we do a quick conversion.  If not, we do a slower
    % conversion using arbitrary-precision integers.  This is important --
    % doing the conversion with arbitrary-precision integers all the time
    % roughly halves the speed of parsing.
    ( if I - I1 =< 8 then
        Int = string.det_base_string_to_int(Base, SubS),
        Tok = check_num_suffix(int(Int), "integer literal", Src, I1, I, S)
      else
        BigInt = integer.det_from_base_string(Base, SubS),
        ( if integer(int.min_int) =< BigInt,
             integer(int.max_int) >= BigInt then
            Int = integer.int(BigInt),
            Tok = check_num_suffix(int(Int), "integer literal", Src, I1, I, S)
          else
            lex_error(Tok, "integer literal does not fit into " ++
                (int.bits_per_int:int)^string ++ " bits", I1, S)
        )
    ).

make_float(Src, I1, I, S) = Tok :-
    grab_substring(SubS, Src, I1, I),
    Tok = check_num_suffix(float(SubS), "float literal", Src, I1, I, S).

make_dollar_name(Src, I1, I, S) = Tok :-
    grab_substring(Name, Src, I1+1, I),     % +1 to skip the '$'.
    ( if is_keyword(Name) then
        lex_error(Tok, "keyword after '$'",  I1, S)
      else if is_op(Src^lang, Name) then
        lex_error(Tok, "operator after '$'", I1, S)
      else
        Tok = dollar_ident(Name)
    ).

make_quoted_alpha_op(Src, I1, I, S) = Tok :-
    grab_substring_minus_first_and_last_chars(OpStr, Src, I1, I),
    ( if is_all_alpha(OpStr), is_op(Src^lang, OpStr) then
        Tok = quoted_op(OpStr)      % Exclude the quotes.
      else
        lex_error(Tok, "unrecognised operator `" ++ OpStr ++ "'", I1, S)
    ).

make_backquoted_op(Src, I1, I, _S) = Tok :-
    grab_substring_minus_first_and_last_chars(OpStr, Src, I1, I),
    Tok = backquoted_op(OpStr). % Use the un-backquoted name as the operator.

make_op(OpStr, /*IsQuoted*/no, Tok, Src, _I1, !I, !S) :-
    Lang = Src^lang,
    else_unexpected(is_op(Lang, OpStr), $pred ++ ": not an operator"),
    Tok = op(OpStr).
make_op(OpStr, /*IsQuoted*/yes, Tok, Src, I1, !I, !S) :-
    ( if get_char(C, Src, !I, !S), C = '\'' then
        else_unexpected(is_op(Src^lang, OpStr), $pred ++ ": unknown operator"),
        Tok = quoted_op(OpStr)      % Exclude the quotes.
      else
        lex_error(Tok, "expected end-quote after `" ++ OpStr ++ "' operator",
            I1, !.S)
    ).

make_string(RevChars) = Tok :-
    string.from_rev_char_list(RevChars, String),
    Tok = string(String).

%-----------------------------------------------------------------------------%

:- pred grab_substring(string::out, src::in, int::in, int::in) is det.

grab_substring(SubS, Src, I1, I2) :-
    Len = I2 - I1,
% This check is disabled because it reduces parsing speed by about 10%.
%    else_unexpected(0 =< I1,           "before start of string"),
%    else_unexpected(I2 < Src ^ length, "past end of string"),
    unsafe_substring(Src ^ text, I1, Len, SubS).

:- pred grab_substring_minus_first_and_last_chars(string::out, src::in,
        int::in, int::in) is det.

grab_substring_minus_first_and_last_chars(SubS, Src, I1, I2) :-
    Len = I2 - I1 - 2,
% This check is disabled for consistency with 'grab_substring'.
%    else_unexpected(0 =< I1,           "before start of string"),
%    else_unexpected(I2 < Src ^ length, "past end of string"),
    unsafe_substring(Src ^ text, I1+1, Len, SubS).

%-----------------------------------------------------------------------------%

:- func check_num_suffix(token, string, src, int, int, lexer_state) = token
        is det.

check_num_suffix(Tok0, What, Src, I1, I, S) = Tok :-
    ( if
        NextC = peek_char(Src, I),
        is_alpha_or_underscore(NextC)
      then
        lex_error(Tok, "invalid suffix `" ++ char_to_string(NextC)
            ++ "' on " ++ What, I1, S)
      else
        Tok = Tok0
    ).

%-----------------------------------------------------------------------------%
% Built-in operators
%-----------------------------------------------------------------------------%

:- pred is_op(lang::in, zinc_name::in) is semidet.

is_op(Lang, Name) :-
    (   bin_only_op( Lang, Name,_,_,_)
    ;   bin_or_un_op(Lang, Name,_,_,_)
    ;   un_only_op(  Lang, Name,_)
    ).

    % Here we have the associativity/precedence for each operator, and whether
    % it is part of a numeric expression.  See builtins.m for the type-inst
    % signatures of these operators.
    %
:- pred bin_only_op(lang, zinc_name, associativity, precedence, bool).
:- mode bin_only_op(in, in,  out, out, out) is semidet.
:- mode bin_only_op(in, out, out, out, out) is nondet.

    % Binary-only operators (ie. excluding '+' and '-').
    % 5th arg indicates if it's a Zinc integer operator.
bin_only_op(Lang,   "<->",      left,   1200,   no) :- zm(Lang).

bin_only_op(Lang,   "<-",       left,   1100,   no) :- zm(Lang).
bin_only_op(Lang,   "->",       left,   1100,   no) :- zm(Lang).

bin_only_op(Lang,   "\\/",      left,   1000,   no) :- zm(Lang).
bin_only_op(Lang,   "xor",      left,   1000,   no) :- zm(Lang).

bin_only_op(Lang,   "/\\",      left,    900,   no) :- zm(Lang).

bin_only_op(Lang,   "==",       none,    800,   no) :- zm(Lang).
bin_only_op(Lang,   "=",        none,    800,   no) :- zm(Lang).
bin_only_op(Lang,   "!=",       none,    800,   no) :- zm(Lang).
bin_only_op(Lang,   "<=",       none,    800,   no) :- zm(Lang).
bin_only_op(Lang,   "<",        none,    800,   no) :- zm(Lang).
bin_only_op(Lang,   ">=",       none,    800,   no) :- zm(Lang).
bin_only_op(Lang,   ">",        none,    800,   no) :- zm(Lang).

bin_only_op(Lang,   "in",       none,    700,   no) :- zm(Lang).
bin_only_op(Lang,   "subset",   none,    700,   no) :- zm(Lang).
bin_only_op(Lang,   "superset", none,    700,   no) :- zm(Lang).

bin_only_op(Lang,   "union",    left,    600,   no) :- zm(Lang).
bin_only_op(Lang,   "diff",     left,    600,   no) :- zm(Lang).
bin_only_op(Lang,   "symdiff",  left,    600,   no) :- zm(Lang).

    % We need '..' for FlatZinc, because it's how 1..2 set literals are
    % represented internally.
bin_only_op(Lang,   "..",       none,    500,   no) :- zmf(Lang).

% '+' and '-' have precedence of 400 (see bin_or_un_op).

bin_only_op(Lang,   "*",        left,    300,   yes) :- zm(Lang).
bin_only_op(Lang,   "/",        left,    300,   yes) :- zm(Lang).
bin_only_op(Lang,   "div",      left,    300,   yes) :- zm(Lang).
bin_only_op(Lang,   "mod",      left,    300,   yes) :- zm(Lang).
bin_only_op(Lang,   "intersect",left,    300,   no)  :- zm(Lang).

bin_only_op(Lang,   "++",       right,   200,   no)  :- zm(Lang).

%-----------------------------------------------------------------------------%

    % Operators that are both unary and binary ('+' and '-').  The 'bool' arg
    % indicates if it can be used in an integer expression.
:- pred bin_or_un_op(lang, zinc_name, associativity, precedence, bool).
:- mode bin_or_un_op(in, in,  out, out, out) is semidet.
:- mode bin_or_un_op(in, out, out, out, out) is nondet.

bin_or_un_op(Lang, "+", left,    400,   yes) :- zm(Lang).
bin_or_un_op(Lang, "-", left,    400,   yes) :- zm(Lang).

%-----------------------------------------------------------------------------%

    % Unary-only operators (ie. excluding '+' and '-').
:- pred un_only_op(lang, zinc_name, bool).
:- mode un_only_op(in, in,  out) is semidet.
:- mode un_only_op(in, out, out) is semidet.

un_only_op(Lang, "not", no) :- zm(Lang).

%-----------------------------------------------------------------------------%

is_bin_op(Lang, Name, Assoc, Prec, IsNumOp) :-
    ( if bin_only_op(Lang, Name, Assoc0, Prec0, IsNumOp0) then
        Assoc   = Assoc0,
        Prec    = Prec0,
        IsNumOp = IsNumOp0
      else if bin_or_un_op(Lang, Name, Assoc0, Prec0, IsNumOp0) then
        Assoc   = Assoc0,
        Prec    = Prec0,
        IsNumOp = IsNumOp0
      else
        fail
    ).

backquoted_bin_op(Lang, left, 100) :- zm(Lang).     % eg. `foo`

is_un_op(Lang, Name, IsNumOp) :-
    ( if un_only_op(Lang, Name, IsNumOp0) then
        IsNumOp = IsNumOp0
      else if bin_or_un_op(Lang, Name, _, _, IsNumOp0) then
        IsNumOp = IsNumOp0
      else
        fail
    ).

%-----------------------------------------------------------------------------%
% Recognisers and converters, including the operator table
%-----------------------------------------------------------------------------%

:- pred escape_char(char::in, char::out) is semidet.

escape_char('a', '\a').
escape_char('b', '\b').
escape_char('r', '\r').
escape_char('f', '\f').
escape_char('t', '\t').
escape_char('n', '\n').
escape_char('v', '\v').
escape_char('\\', '\\').
escape_char('"', '"').
escape_char('\'', '\'').

    % "Special" chars are ones that are single-character tokens.  Each one must
    % not be a legitimate prefix of a longer token, even if they can appear by
    % themself (eg. `\' is not one, because '\/' is a longer token).
    %
    % Nb: you might think we should include '_' in here, since in legal
    % programs it always appears by itself.  But instead we handle it
    % separately so we can explicitly detect an identifier which illegally
    % begins with an underscore (eg. "_foo") rather than lexing it as two
    % tokens "_" and "foo".
    %
:- pred special(char::in, token::out) is semidet.

special('(', lparen).
special(')', rparen).
special(']', rsquare).      % '[' isn't special (due to '[|'), but ']' is
special('{', lcurly).
special('}', rcurly).
special(',', comma).
special(';', semicolon).

:- pred is_op_char(char::in) is semidet.

is_op_char('+').
is_op_char('-').
is_op_char('*').
is_op_char('/').
is_op_char('<').
is_op_char('>').
is_op_char('=').
is_op_char('!').
is_op_char('.').
is_op_char('\\').

    % Note that named operators (eg. 'and') are not include in this list;
    % they are covered by is_builtin_op/1.
    %
    % Note also that the keywords are the same in Zinc, MiniZinc and FlatZinc,
    % even though MiniZinc and FlatZinc don't support the features the
    % keywords involve.  Eg. FlatZinc doesn't have include items, but
    % "include" is still a keyword.
:- pred is_keyword(string::in) is semidet.

is_keyword("annotation").
is_keyword("ann").
is_keyword("any").
is_keyword("array").
is_keyword("bool").
is_keyword("case").
is_keyword("constraint").
is_keyword("else").
is_keyword("elseif").
is_keyword("endif").
is_keyword("enum").
is_keyword("false").
is_keyword("float").
is_keyword("function").
is_keyword("if").
is_keyword("include").
is_keyword("int").
is_keyword("let").
is_keyword("list").
is_keyword("maximize").
is_keyword("minimize").
is_keyword("of").
is_keyword("op").
is_keyword("output").
is_keyword("par").
is_keyword("predicate").
is_keyword("record").
is_keyword("satisfy").
is_keyword("set").
is_keyword("solve").
is_keyword("string").
is_keyword("test").
is_keyword("then").
is_keyword("true").
is_keyword("tuple").
is_keyword("type").
is_keyword("var").
is_keyword("where").

:- instance show(token) where [
    int(I)          ^show = I ^ string,
    float(F)        ^show = F ^ string,
    string(S)       ^show = S ^ string,
    ident(S)        ^show = S,
    quoted_op(S)    ^show = "'" ++ S ++ "'",
    dollar_ident(S) ^show = "$" ++ S,
    keyword(S)      ^show = S,
    op(S)           ^show = S,
    backquoted_op(S)^show = "`" ++ S ++ "`",
    underscore      ^show = "_",
    underscore_ident(S) ^ show = S,
    dot             ^show = ".",
    lparen          ^show = "(",
    rparen          ^show = ")",
    lcurly          ^show = "{",
    rcurly          ^show = "}",
    lsquare         ^show = "[",
    rsquare         ^show = "]",
    lsquarepipe     ^show = "[|",
    rpipesquare     ^show = "|]",
    pipe            ^show = "|",
    comma           ^show = ",",
    semicolon       ^show = ";",
    colon           ^show = ":",
    double_colon    ^show = "::",
    right_arrow     ^show = "-->",
    eof             ^show = "EOF",
    error_token(_,_)^show = _ :-
        unexpected("token_to_string: error_token")
].

%-----------------------------------------------------------------------------%
% Error handling
%-----------------------------------------------------------------------------%

    % Nb: all lex error messages are simple ones that can be broken up into
    % words.
    %
:- pred lex_error(token::out, string::in, int::in, lexer_state::in) is det.

lex_error(Tok, ErrStr, I, S) :-
    Tok = error_token([words(ErrStr)], I - S^line_index + 1).

%-----------------------------------------------------------------------------%
:- end_module zinc_lexer.
%-----------------------------------------------------------------------------%

