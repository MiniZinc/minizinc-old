%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2008 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Authors:	Julien Fischer        <juliensf@csse.unimelb.edu.au>
%
% This module defines a simple parser for parsing "structured" string
% annotations, like the standard FlatZinc exploration parameters.
% It is also used for parsing the values of the Zinc compiler's 
% --backend option.
% 
%-----------------------------------------------------------------------------%

:- module simple_term_parser.
:- interface.

:- import_module list.
    
%-----------------------------------------------------------------------------%
%
    % A simple term type used to represent "structured" annotations or
    % annotation parameters in FlatZinc.
    %
:- type simple_term
    --->    st_term(string, list(simple_term))
    ;       st_integer(int)
    .

    % Convert a string to an annotation term.
    % Fails if the term is not valid.
    %
:- pred string_to_simple_term(string::in, simple_term::out) is semidet.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module char.
:- import_module string.

%-----------------------------------------------------------------------------%
%
% Parser for structured annotations
%

string_to_simple_term(String, Term) :-
    tokenize_string(String, Tokens0),
    parse_term(Term, Tokens0, Tokens),
    Tokens = [].

:- pred parse_term(simple_term::out,
    list(token)::in, list(token)::out) is semidet.

parse_term(st_term(Functor, Args)) -->
    [token_word(Functor)],
    parse_arg_list(Args).

:- pred parse_arg_list(list(simple_term)::out,
    list(token)::in, list(token)::out) is semidet.

parse_arg_list(Args) -->
    ( if [token_lparen] then
        parse_args(Args),
        [token_rparen]
      else
        { Args = [] }
    ).

:- pred parse_args(list(simple_term)::out,
    list(token)::in, list(token)::out) is semidet.

parse_args([Arg | Args]) -->
    parse_arg(Arg),
    parse_args_rest(Args).

:- pred parse_args_rest(list(simple_term)::out,
    list(token)::in, list(token)::out) is semidet.

parse_args_rest(Args) -->
    ( if [token_comma] then
        parse_args(Args)
      else
        { Args = [] }
    ). 

:- pred parse_arg(simple_term::out,
    list(token)::in, list(token)::out) is semidet.

parse_arg(Term) -->
    ( if [token_integer(I)] then
        { Term = st_integer(I) }
      else
        parse_term(Term)
    ).

%-----------------------------------------------------------------------------%
%
% Lexer for structured annotations
%

:- type token
    --->    token_word(string)
    ;       token_integer(int)
    ;       token_lparen
    ;       token_rparen
    ;       token_comma
    .

:- pred tokenize_string(string::in, list(token)::out) is semidet.

tokenize_string(String, Tokens) :-
    Chars = string.to_char_list(String),
    tokenize_char_list(Chars, [], RevTokens),
    list.reverse(RevTokens, Tokens).

:- pred tokenize_char_list(list(char)::in,
    list(token)::in, list(token)::out) is semidet.

tokenize_char_list(Chars, !Tokens) :-
    (
        Chars = []
    ;
        Chars = [FirstChar | RestChars0], 
        ( char.is_whitespace(FirstChar) ->
            RestChars = RestChars0 
        ; FirstChar = '(' ->
           !:Tokens = [token_lparen | !.Tokens],
            RestChars = RestChars0
        ; FirstChar = ')' ->
           !:Tokens = [token_rparen | !.Tokens],
            RestChars = RestChars0
        ; FirstChar = (',') ->
            !:Tokens = [token_comma | !.Tokens],
            RestChars = RestChars0
        ; char.is_digit(FirstChar) ->
            get_integer(Integer, Chars, RestChars),
            !:Tokens = [token_integer(Integer) | !.Tokens]
        ; ( char.is_lower(FirstChar) ; FirstChar = '_') ->
            get_word(Word, Chars, RestChars),
            !:Tokens = [token_word(Word) | !.Tokens]
        ;
            false
        ),
        tokenize_char_list(RestChars, !Tokens)
    ).

:- pred get_integer(int::out, list(char)::in, list(char)::out) is semidet.

get_integer(Integer, !Chars) :-
    get_integer_2([], RevDigits, !Chars),
    Digits = string.from_rev_char_list(RevDigits),
    Integer = string.det_to_int(Digits). 

:- pred get_integer_2(list(char)::in, list(char)::out,
    list(char)::in, list(char)::out) is semidet.

get_integer_2(!Digits, !Chars) :-
    (
        !.Chars = [FirstChar | RestChars],
        ( char.is_digit(FirstChar) ->
            !:Digits = [FirstChar | !.Digits],
            get_integer_2(!Digits, RestChars, !:Chars)
        ; 
            true
        )
    ;
        !.Chars = []
    ).       

:- pred get_word(string::out, list(char)::in, list(char)::out) is semidet.

get_word(Word, !Chars) :-
    get_word_2([], RevWordChars, !Chars),
    Word = string.from_rev_char_list(RevWordChars).

:- pred get_word_2(list(char)::in, list(char)::out,
    list(char)::in, list(char)::out) is semidet.

get_word_2(!WordChars, !Chars) :-
    (
        !.Chars = [FirstChar | RestChars],
        ( (char.is_lower(FirstChar) ; FirstChar = '_' ; FirstChar = ('-')) ->
            !:WordChars = [FirstChar | !.WordChars],
            get_word_2(!WordChars, RestChars, !:Chars)
        ;
            true
        )
    ;
        !.Chars = []
    ).

%-----------------------------------------------------------------------------%
:- end_module simple_term_parser.
%-----------------------------------------------------------------------------%
