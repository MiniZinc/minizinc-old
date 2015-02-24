%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
% This module provides operations to compute bounds on ints and floats.
%
%-----------------------------------------------------------------------------%

:- module bounds.
:- interface.

:- import_module errors.

:- import_module maybe.

%-----------------------------------------------------------------------------%
%
% Compute the bounds on A + B, A * B, A div B, A mod B, max(A, B) and min(A, B)
% from the bounds on A and B.
%

:- pred int_plus_bounds(error_context::in, int::in, int::in, int::in, int::in,
    int::out, int::out) is det.

:- pred int_times_bounds(error_context::in, int::in, int::in, int::in, int::in,
    int::out, int::out) is det.

:- pred int_div_bounds(int::in, int::in, int::in, int::in, int::out, int::out)
    is det.

:- pred int_mod_bounds(error_context::in,
    int::in, int::in, int::in, int::in, int::out, int::out) is det.

:- pred int_min_bounds(int::in, int::in, int::in, int::in, int::out, int::out)
    is det.

:- pred int_max_bounds(int::in, int::in, int::in, int::in, int::out, int::out)
    is det.

%-----------------------------------------------------------------------------%
%
% Compute the bounds on A + B, A * B, A / B, max(A, B) and min(A, B)
% from the bounds on A and B.
%

:- pred float_plus_bounds(float::in, float::in, float::in, float::in,
    float::out, float::out) is det.

:- pred float_times_bounds(float::in, float::in, float::in, float::in,
    float::out, float::out) is det.

:- pred float_div_bounds(float::in, float::in, float::in, float::in,
    float::out, float::out) is det.

:- pred float_min_bounds(float::in, float::in, float::in, float::in,
    float::out, float::out) is det.

:- pred float_max_bounds(float::in, float::in, float::in, float::in,
    float::out, float::out) is det.

%-----------------------------------------------------------------------------%

    % int_bounded_plus/minus abort if the result is too big to be represented.
    % int_bounded_plus_maybe/minus_maybe return `no' in such cases.
:- func int_bounded_plus(error_context, int, int) = int.
:- func int_bounded_plus_maybe(int, int) = maybe(int).
:- func int_bounded_times(error_context, int, int) = int.
:- func int_bounded_times_maybe(int, int) = maybe(int).
:- func int_bounded_div(int, int) = int.
:- func int_bounded_mod(int, int) = int.

:- func float_bounded_plus(float, float) = float.
:- func float_bounded_times(float, float) = float.
:- func float_bounded_div(float, float) = float.

%-----------------------------------------------------------------------------%

:- implementation.

:- import_module types.

:- import_module float.
:- import_module int.
:- import_module list.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

int_plus_bounds(Context, LBA, UBA, LBB, UBB, LB, UB) :-
    LB = int_bounded_plus(Context, LBA, LBB),
    UB = int_bounded_plus(Context, UBA, UBB).

int_times_bounds(Context, LBA, UBA, LBB, UBB, LB, UB) :-
    Xa = int_bounded_times(Context, LBA, LBB),
    Xb = int_bounded_times(Context, LBA, UBB),
    Xc = int_bounded_times(Context, UBA, LBB),
    Xd = int_bounded_times(Context, UBA, UBB),
    LB = int.min(Xa, int.min(Xb, int.min(Xc, Xd))),
    UB = int.max(Xa, int.max(Xb, int.max(Xc, Xd))).

int_div_bounds(LBA, UBA, LBB, UBB, !:LB, !:UB) :-
    !:LB = int_plus_infinity,
    !:UB = int_minus_infinity,
    ( if LBB \= 0 then
        int.max(LBA `int_bounded_div` LBB, !UB),
        int.min(LBA `int_bounded_div` LBB, !LB),
        int.min(UBA `int_bounded_div` LBB, !LB),
        int.max(UBA `int_bounded_div` LBB, !UB)
    else
        true
    ),
    ( if UBB \= 0 then
        int.min(LBA `int_bounded_div` UBB, !LB),
        int.min(UBA `int_bounded_div` UBB, !LB),
        int.max(LBA `int_bounded_div` UBB, !UB),
        int.max(UBA `int_bounded_div` UBB, !UB)
    else
        true
    ),
    ( if LBB =< -1, -1 =< UBB then
        int.min(LBA `int_bounded_div` -1, !LB),
        int.min(UBA `int_bounded_div` -1, !LB),
        int.max(LBA `int_bounded_div` -1, !UB),
        int.max(UBA `int_bounded_div` -1, !UB)
    else
        true
    ),
    ( if LBB =< 1, 1 =< UBB then
        int.min(LBA `int_bounded_div` 1, !LB),
        int.min(UBA `int_bounded_div` 1, !LB),
        int.max(LBA `int_bounded_div` 1, !UB),
        int.max(UBA `int_bounded_div` 1, !UB)
    else
        true
    ).

int_mod_bounds(Context, LBA, UBA, LBB, UBB, LB, UB) :-
    % Find the bounds on C where C = A mod B.
    AbsUB = int_bounded_plus(Context, int.max(int.abs(LBB), int.abs(UBB)), -1),
    ( if UBA < 0 then
        %           0
        % AAAAAAAAA |
        %  CCCCCCCCC|
        %
        LB = -AbsUB,
        UB = 0
    else if LBA < 0 then
        %           0
        %       AAAA|AAAA
        %        CCC|CCC
        %
        LB = -AbsUB,
        UB =  AbsUB
    else
        %           0
        %           | AAAAAAAAA
        %           |CCCCCCCCC
        %
        LB = 0,
        UB = AbsUB
    ).

int_min_bounds(LBA, UBA, LBB, UBB, LB, UB) :-
    LB = int.min(LBA, LBB),
    UB = int.min(UBA, UBB).

int_max_bounds(LBA, UBA, LBB, UBB, LB, UB) :-
    LB = int.max(LBA, LBB),
    UB = int.max(UBA, UBB).

%-----------------------------------------------------------------------------%

float_plus_bounds(LBA, UBA, LBB, UBB, LB, UB) :-
    LB = float_bounded_plus(LBA, LBB),
    UB = float_bounded_plus(UBA, UBB).

float_times_bounds(LBA, UBA, LBB, UBB, LB, UB) :-
    Xa = float_bounded_times(LBA, LBB),
    Xb = float_bounded_times(LBA, UBB),
    Xc = float_bounded_times(UBA, LBB),
    Xd = float_bounded_times(UBA, UBB),
    LB = float.min(Xa, float.min(Xb, float.min(Xc, Xd))),
    UB = float.max(Xa, float.max(Xb, float.max(Xc, Xd))).

float_div_bounds(LBA, UBA, LBB, UBB, LB, UB) :-
    ( if UBA =< -1.0 then
        % A is definitely negative.
        ( if UBB =< -1.0 then
            % B is definitely negative.
            LB = float_bounded_div(UBA, LBB),
            UB = float_bounded_div(LBA, UBB)
        else if 1.0 =< LBB then
            % B is definitely positive.
            LB = float_bounded_div(LBA, LBB),
            UB = float_bounded_div(UBA, UBB)
        else
            % B can be positive or negative.
            LB =  LBA,
            UB = -LBA
        )
      else if 1.0 =< LBA then
        % A is definitely positive.
        ( if UBB =< -1.0 then
            % B is definitely negative.
            LB = float_bounded_div(UBA, UBB),
            UB = float_bounded_div(LBA, LBB)
        else if 1.0 =< LBB then
            % B is definitely positive.
            LB = float_bounded_div(LBA, UBB),
            UB = float_bounded_div(UBA, LBB)
        else
            % B can be positive or negative.
            LB = -UBA,
            UB =  UBA
        )
    else
        % A can be positive or negative.
        ( if UBB =< -1.0 then
            % B is definitely negative.
            LB = float_bounded_div(UBA, LBB),
            UB = float_bounded_div(float.min(LBA, -UBA), LBB)
        else if 1.0 =< LBB then
            % B is definitely positive.
            LB = float_bounded_div(LBA, LBB),
            UB = float_bounded_div(UBA, LBB)
        else
            % B can be positive or negative.
            LB = float.min(LBA, -UBA),
            UB = float.max(-LBA, UBA)
        )
    ).

float_min_bounds(LBA, UBA, LBB, UBB, LB, UB) :-
    LB = float.min(LBA, LBB),
    UB = float.min(UBA, UBB).

float_max_bounds(LBA, UBA, LBB, UBB, LB, UB) :-
    LB = float.max(LBA, LBB),
    UB = float.max(UBA, UBB).

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

int_bounded_plus(Context, X, Y) = Z :-
    Min = int.min(X, Y),
    Max = int.max(X, Y),
    ( if Max = int_plus_infinity then
        Z = int_plus_infinity
    else if Min = int_minus_infinity then
        Z = int_minus_infinity
    else if Min >= 0, int_plus_infinity - Max < Min then
        minizinc_overflow_error(Context)
    else if Max =< 0, Max < int_minus_infinity - Min then
        minizinc_overflow_error(Context)
    else
        Z = X + Y
    ).

int_bounded_plus_maybe(X, Y) = MaybeZ :-
    Min = int.min(X, Y),
    Max = int.max(X, Y),
    ( if Max = int_plus_infinity then
        Z = int_plus_infinity,
        MaybeZ = yes(Z)
    else if Min = int_minus_infinity then
        Z = int_minus_infinity,
        MaybeZ = yes(Z)
    else if Min >= 0, int_plus_infinity - Max < Min then
        MaybeZ = no
    else if Max =< 0, Max < int_minus_infinity - Min then
        MaybeZ = no
    else
        Z = X + Y,
        MaybeZ = yes(Z)
    ).

int_bounded_times(Context, X, Y) = Z :-
    Min = int.min(X, Y),
    Max = int.max(X, Y),
    ( if ( X = 0 ; Y = 0 ) then
        Z = 0
    else if Max = int_plus_infinity then
        Z = int_plus_infinity
    else if Min = int_minus_infinity then
        Z = int_minus_infinity
    else if
        MinBits = int.log2(int.abs(Min)),
        MaxBits = int.log2(int.abs(Max)),
        ArchSize = int.bits_per_int,
        MinBits + MaxBits > ArchSize
    then
        minizinc_overflow_error(Context)
    else
        Z = Min * Max
    ).

int_bounded_times_maybe(X, Y) = MaybeZ :-
    Min = int.min(X, Y),
    Max = int.max(X, Y),
    ( if ( X = 0 ; Y = 0 ) then
        Z = 0,
        MaybeZ = yes(Z)
    else if Max = int_plus_infinity then
        Z = int_plus_infinity,
        MaybeZ = yes(Z)
    else if Min = int_minus_infinity then
        Z = int_minus_infinity,
        MaybeZ = yes(Z)
    else if
        MinBits = int.log2(int.abs(Min)),
        MaxBits = int.log2(int.abs(Max)),
        ArchSize = int.bits_per_int,
        MinBits + MaxBits > ArchSize
    then
        MaybeZ = no
    else
        Z = Min * Max,
        MaybeZ = yes(Z)
    ).

int_bounded_div(X0, Y0) = Z :-
    ( if X0 < Y0 then
        X = X0, Y = Y0
    else
        X = Y0, Y = X0
    ),
    ( if ( X = 0 ; Y = 0 ) then
        Z = 0
    else if X = int_minus_infinity then
        Z = ( if 0 < Y then int_minus_infinity else int_plus_infinity )
    else if Y = int_plus_infinity then
        Z = ( if X < 0 then int_minus_infinity else int_plus_infinity )
    else
        Z = X0 / Y0
    ).

int_bounded_mod(X, Y) = Z :-
    Z = X rem Y.

%-----------------------------------------------------------------------------%

float_bounded_plus(X, Y) = Z :-
    ( if ( X = float_plus_infinity ; Y = float_plus_infinity ) then
        Z = float_plus_infinity
    else if ( X = float_minus_infinity ; Y = float_minus_infinity ) then
        Z = float_minus_infinity
    else
        Z = X + Y
    ).

float_bounded_times(X0, Y0) = Z :-
    ( if X0 < Y0 then
        X = X0, Y = Y0
    else
        X = Y0, Y = X0
    ),
    ( if ( X = 0.0 ; Y = 0.0 ) then
        Z = 0.0
    else if X = float_minus_infinity then
        Z = ( if 0.0 < Y then float_minus_infinity else float_plus_infinity )
    else if Y = float_plus_infinity then
        Z = ( if X < 0.0 then float_minus_infinity else float_plus_infinity )
    else
        Z = X * Y
    ).

float_bounded_div(X0, Y0) = Z :-
    ( if X0 < Y0 then
        X = X0, Y = Y0
    else
        X = Y0, Y = X0
    ),
    ( if ( X = 0.0 ; Y = 0.0 ) then
        Z = 0.0
    else if X = float_minus_infinity then
        Z = ( if 0.0 < Y then float_minus_infinity else float_plus_infinity )
    else if Y = float_plus_infinity then
        Z = ( if X < 0.0 then float_minus_infinity else float_plus_infinity )
    else
        Z = X0 / Y0
    ).

%-----------------------------------------------------------------------------%
:- end_module bounds.
%-----------------------------------------------------------------------------%
