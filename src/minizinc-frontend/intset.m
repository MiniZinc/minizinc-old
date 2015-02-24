%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2006-2009 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% This is mostly a copy of the ranges module from the G12 common library
% (plus some bits of the int_util module from the same spot).  The name
% has changed but it is otherwise the same.
%
% We need a copy because this is used by some parts of the system, e.g. the
% Zinc frontend library and mzn2fzn, that are not allowed to use the common
% library.
%
% This is an interim measure; in the long run this functionality will be
% probably be provided by the Mercury stdlib, or by a new library within G12
% that all of the system can use.
%
%-----------------------------------------------------------------------------%

:- module intset.
:- interface.

:- import_module array.
:- import_module list.
:- import_module set.

%-----------------------------------------------------------------------------%

    % intsets represent sets of integers.  Each contiguous block
    % of integers in the set is stored as an intset which specifies
    % the bounds of the block, and these intset are kept in a list-like
    % structure.
    %
:- type intset.

    % empty returns the empty set.
    %
:- func empty = intset.

    % singleton(N) returns the set containing only N.
    %
:- func singleton(int) = intset.

    % universe returns the largest set that can be handled by this module.
    % This is the set of integers (min_int+1)..max_int.  Note that min_int
    % cannot be represented in any set.
    %
:- func universe = intset.

    % intset(Min, Max) is the set of all integers from Min to Max inclusive.
    %
:- func intset(int, int) = intset.

    % split(D, L, H, Rest) is true iff L..H is the first intset
    % in D, and Rest is the domain D with this range removed.
    %
:- pred split(intset::in, int::out, int::out, intset::out) is semidet.

    % is_contiguous(R, L, H) <=> split(R, L, H, empty).
    % Test if the set is a contiguous set of integers and return
    % the endpoints of this set if this is the case.
    %
:- pred is_contiguous(intset::in, int::out, int::out) is semidet.

    % Add an integer to the set.
    %
:- func insert(int, intset) = intset.

    % Delete an integer from the set.
    %
:- func delete(int, intset) = intset.

    % Return the number of distinct integers which are in the intset
    % (as opposed to the number of intset).
    %
:- func size(intset) = int.

    % Returns the median value of the set.  In case of a tie, returns
    % the lower of the two options.
    %
:- func median(intset) = int.

    % least(A, N) is true iff N is the least element of A.
    %
:- pred least(intset::in, int::out) is semidet.

    % greatest(A, N) is true iff N is the greatest element of A.
    %
:- pred greatest(intset::in, int::out) is semidet.

    % next(A, N0, N) is true iff N is the least element of A greater
    % than N0.
    %
:- pred next(intset::in, int::in, int::out) is semidet.

    % Test set membership.
    %
:- pred member(int::in, intset::in) is semidet.

    % Nondeterministically produce each intset.
    %
:- pred intset_member(int::out, int::out, intset::in) is nondet.

    % Nondeterministically produce each element.
    %
:- pred nondet_member(int::out, intset::in) is nondet.

    % subset(A, B) is true iff every value in A is in B.
    %
:- pred subset(intset::in, intset::in) is semidet.

    % disjoint(A, B) is true iff A and B have no values in common.
    %
:- pred disjoint(intset::in, intset::in) is semidet.

    % union(A, B) contains all the integers in either A or B.
    %
:- func union(intset, intset) = intset.

    % intersection(A, B) contains all the integers in both A and B.
    %
:- func intersection(intset, intset) = intset.

    % difference(A, B) contains all the integers which are in A but
    % not in B.
    %
:- func difference(intset, intset) = intset.

    % restrict_min(Min, A) contains all integers in A which are greater
    % than or equal to Min.
    %
:- func restrict_min(int, intset) = intset.

    % restrict_max(Max, A) contains all integers in A which are less than
    % or equal to Max.
    %
:- func restrict_max(int, intset) = intset.

    % restrict_intset(Min, Max, A) contains all integers I in A which
    % satisfy Min =< I =< Max.
    %
:- func restrict_intset(int, int, intset) = intset.

    % prune_to_next_non_member(A0, A, N0, N):
    % N is the smallest integer larger than or equal to N0 which is not
    % in A0.  A is the set A0 restricted to values greater than N.
    %
:- pred prune_to_next_non_member(intset::in, intset::out,
    int::in, int::out) is det.

    % prune_to_prev_non_member(A0, A, N0, N):
    % N is the largest integer smaller than or equal to N0 which is not
    % in A0.  A is the set A0 restricted to values less than N.
    %
:- pred prune_to_prev_non_member(intset::in, intset::out,
    int::in, int::out) is det.

    % negate all numbers:  A in R  <=>  -A in negate(R)
    %
:- func negate(intset) = intset.

    % the sum of two intset.
    %
:- func plus(intset, intset) = intset.

    % shift a intset by const C.
    %
:- func shift(intset, int) = intset.

    % dilate a intset by const C.
    %
:- func dilation(intset, int) = intset.

    % contract a intset by const C.
    % 
:- func contraction(intset, int) = intset.

%-----------------------------------------------------------------------------%

    % Convert to a sorted list of integers.
    %
:- func to_sorted_list(intset) = list(int).

    % Convert from a list of integers.
    %
:- func from_list(list(int)) = intset.

    % Convert from a set of integers.
    %
:- func from_set(set(int)) = intset.

%-----------------------------------------------------------------------------%

    % Compare two intset:
    % A < B iff A is a strict subset of B.
    % A > B iff A is a strict superset of B.
    % A = B iff A is equal to B.
    % Otherwise A and B are incomparable.
    %
%:- func compare_intset(intset, intset) = compare_bounds_result.

%-----------------------------------------------------------------------------%

    % For each intset, call the predicate, passing it the lower and
    % upper bound and threading through an accumulator.
    %
:- pred intset_foldl(pred(int, int, T, T), intset, T, T).
:- mode intset_foldl(pred(in, in, in, out) is det,    in, in, out) is det.
:- mode intset_foldl(pred(in, in, di, uo) is det, in, di, uo) is det.
:- mode intset_foldl(pred(in, in, di, uo) is semidet, in, di, uo) is semidet.

    % As above, but with two accumulators.
    %
:- pred intset_foldl2(pred(int, int, S, S, T, T), intset, S, S, T, T).
:- mode intset_foldl2(pred(in, in, in, out, in, out) is det,
    in, in, out, in, out) is det.
:- mode intset_foldl2(pred(in, in, in, out, di, uo) is det,
    in, in, out, di, uo) is det.
:- mode intset_foldl2(pred(in, in, in, out, di, uo) is semidet,
    in, in, out, di, uo) is semidet.

    % As above, but with a ui parameter.
    %
:- pred intset_foldl_ui(pred(int, int, T, T, U), intset, T, T, U).
:- mode intset_foldl_ui(pred(in, in, in, out, ui) is det, in, in, out, ui)
    is det.
:- mode intset_foldl_ui(pred(in, in, di, uo, ui) is det, in, di, uo, ui)
    is det.

    % As above, but intervals are traversed from highest to lowest.
    %
:- pred intset_foldr(pred(int, int, T, T), intset, T, T).
:- mode intset_foldr(pred(in, in, in, out) is det, in, in, out) is det.

    % As above, but with a ui parameter.
    %
:- pred intset_foldr_ui(pred(int, int, T, T, U), intset, T, T, U).
:- mode intset_foldr_ui(pred(in, in, in, out, ui) is det, in, in, out, ui)
    is det.
:- mode intset_foldr_ui(pred(in, in, di, uo, ui) is det, in, di, uo, ui)
    is det.

%-----------------------------------------------------------------------------%
    
    % Fold left over each element in the set of integers represented by the
    % intset.
    %
:- pred intset_elems_foldl(pred(int, T, T), intset, T, T).
:- mode intset_elems_foldl(pred(in, in, out) is det, in, in, out) is det.
:- mode intset_elems_foldl(pred(in, mdi, muo) is semidet, in, mdi, muo)
    is semidet.
:- mode intset_elems_foldl(pred(in, di, uo) is semidet, in, di, uo)
    is semidet.

    % As above, but with two accumulators.
    %
:- pred intset_elems_foldl2(pred(int, T, T, U, U), intset, T, T, U, U).
:- mode intset_elems_foldl2(pred(in, in, out, in, out) is det, in, in, out,
    in, out) is det.
:- mode intset_elems_foldl2(pred(in, in, out, array_di, array_uo) is det, in,
    in, out, array_di, array_uo) is det.

%-----------------------------------------------------------------------------%
   
    % Fold right over each element in the set of integers represented by the
    % intset.
    %
:- pred intset_elems_foldr(pred(int, T, T), intset, T, T).
:- mode intset_elems_foldr(pred(in, in, out) is det, in, in, out) is det.

    % As above, but with two accumulators and a ui argument.
    %
:- pred intset_elems_foldr2_ui(pred(int, T, T, U, U, S), intset, T, T, U, U, S).
:- mode intset_elems_foldr2_ui(pred(in, in, out, in, out, ui) is det, in,
    in, out, in, out, ui) is det.
 
%-----------------------------------------------------------------------------%

    % Convert a intset list into a readable string.
    %
:- func intset.to_string(intset) = string.

    % Convert a intset list into a readble string, but do not use L..U
    % abbreviations for contiguous intset.
    %
:- func intset.to_string_no_abbr(intset) = string.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module bool.
:- import_module exception.
:- import_module int.
:- import_module string.

%-----------------------------------------------------------------------------%

    % Values of this type represent finite sets of integers.  They are
    % interpreted in the following way.
    %
    %     S[[ nil ]]                        = {}
    %     S[[ intset(L, H, Rest) ]]       = {N | L < N =< H} \/ S[[ Rest ]]
    %
    % For example, `intset(1, 4, nil)' is interpreted as {2, 3, 4}.
    %
    % The invariants on this type are:
    %
    %   1) Each intset must be non-empty (i.e., L < H).
    %   2) The intset must not overlap or abut (i.e., for any
    %      value `intset(_, H1, intset(L2, _, _)' we must have
    %      H1 < L2).
    %   3) The intset must be in sorted order.
    %
    % These invariants ensure that the representation is canonical.
    %
    % Note that it is not possible to represent a set containing min_int.
    % Attempting to create such a set will result in an exception being
    % thrown.
    %
:- type intset
    --->    nil
    ;       intset(int, int, intset).

empty = nil.

singleton(N) = intset(N - 1, N, nil).

universe = intset(min_int, max_int, nil).

intset(Min, Max) = Ranges :-
    ( if Min = min_int then
        throw("intset.intset: cannot represent min_int")
    else if Min > Max then
        Ranges = nil
    else
        Ranges = intset(Min - 1, Max, nil)
    ).

split(intset(Min1, Max, Rest), Min1 + 1, Max, Rest).

is_contiguous(Range, Min + 1, Max) :-
    Range = intset(Min, Max, nil).

insert(N, As) = intset.union(As, intset.intset(N, N)).

delete(N, As) = intset.difference(As, intset.intset(N, N)).

%-----------------------------------------------------------------------------%

size(nil) = 0.
size(intset(L, U, Rest)) = (U - L) + intset.size(Rest).

median(As) = N :-
    Size = intset.size(As),
    ( if Size > 0 then
        MiddleIndex = (Size + 1) / 2
    else
        throw("intset.median: empty set")
    ),
    N = element_index(As, MiddleIndex).

    % element_index(Intervals, I) returns the Ith largest value in the set
    % represented by Intervals (the least item in the set having index 1).
    %
:- func element_index(intset, int) = int.

element_index(nil, _) =
    throw("intset.element_index: index out of intset").
element_index(intset(L, U, Rest), I) = N :-
    N0 = L + I,
    ( if N0 =< U then
        N = N0
    else
        N = element_index(Rest, N0 - U)
    ).

%-----------------------------------------------------------------------------%

least(intset(L, _, _), L + 1).

greatest(intset(_, U0, As), U) :-
    greatest_2(U0, As, U).

:- pred greatest_2(int::in, intset::in, int::out) is det.

greatest_2(U, nil, U).
greatest_2(_, intset(_, U0, As), U) :-
    greatest_2(U0, As, U).

next(intset(L, U, As), N0, N) :-
    ( if N0 < U then
        N = int.max(L, N0) + 1
    else
        intset.next(As, N0, N)
    ).

%-----------------------------------------------------------------------------%

member(N, intset(L, U, As)) :-
    (
        N > L,
        N =< U
    ;
        intset.member(N, As)
    ).

intset_member(L, U, intset(A0, A1, As)) :-
    (
        L = A0 + 1,
        U = A1
    ;
        intset_member(L, U, As)
    ).

nondet_member(N, As) :-
    intset_member(L, U, As),
    between(L, U, N).

:- pred between(int::in, int::in, int::out) is nondet.

between(L, U, N) :-
    L =< U,
    (
        N = L
    ;
        between(L + 1, U, N)
    ).

%-----------------------------------------------------------------------------%

subset(A, B) :-
    % XXX Should implement this more efficiently.
    intset.difference(A, B) = nil.

disjoint(A, B) :-
    % XXX Should implement this more efficiently.
    intset.intersection(A, B) = nil.

%-----------------------------------------------------------------------------%

    % union(A, B) = A \/ B
    %
union(nil, Bs) = Bs.
union(As @ intset(_, _, _), nil) = As.
union(As @ intset(LA, UA, As0), Bs @ intset(LB, UB, Bs0)) = Result :-
    compare(R, LA, LB),
    (
        R = (<),
        Result = n_diff_na_b(LA, UA, As0, Bs)
    ;
        R = (=),
        Result = n_int_na_nb(LA, UA, As0, UB, Bs0)
    ;
        R = (>),
        Result = n_diff_na_b(LB, UB, Bs0, As)
    ).

    % n_union_a_nb(L, A, U, B) =
    %   {X | X > L} \ (A \/ ({Y | Y > U} \ B))
    %
    % assuming L < min(A), L < U and U < min(B).
    %
:- func n_union_a_nb(int, intset, int, intset) = intset.

n_union_a_nb(L, nil, U, Bs) = intset(L, U, Bs).
n_union_a_nb(L, As @ intset(LA, UA, As0), UB, Bs0) = Result :-
    compare(R, LA, UB),
    (
        R = (<),
        Result = intset(L, LA, diff_na_nb(UA, As0, UB, Bs0))
    ;
        R = (=),
        Result = intset(L, LA, int_na_b(UA, As0, Bs0))
    ;
        R = (>),
        Result = intset(L, UB, intset.difference(Bs0, As))
    ).

    % n_union_na_b(L, U, A, B) =
    %   {X | X > L} \ (({Y | Y > U} \ A) \/ B)
    %
    % assuming L < U, U < min(A) and L < min(B).
    %
:- func n_union_na_b(int, int, intset, intset) = intset.

n_union_na_b(L, U, As, nil) = intset(L, U, As).
n_union_na_b(L, UA, As0, Bs @ intset(LB, UB, Bs0)) = Result :-
    compare(R, UA, LB),
    (
        R = (<),
        Result = intset(L, UA, intset.difference(As0, Bs))
    ;
        R = (=),
        Result = intset(L, UA, int_a_nb(As0, UB, Bs0))
    ;
        R = (>),
        Result = intset(L, LB, diff_na_nb(UB, Bs0, UA, As0))
    ).

    % n_union_na_nb(L, UA, A, UB, B) =
    %   {X | X > L} \ (({Y | Y > UA} \ A) \/ ({Z | Z > UB} \ B))
    %
    % assuming L < UA, UA < min(A), L < UB and UB < min(B).
    %
:- func n_union_na_nb(int, int, intset, int, intset) =
    intset.

n_union_na_nb(L, UA, As0, UB, Bs0) = Result :-
    compare(R, UA, UB),
    (
        R = (<),
        Result = intset(L, UA, diff_a_nb(As0, UB, Bs0))
    ;
        R = (=),
        Result = intset(L, UA, intset.intersection(As0, Bs0))
    ;
        R = (>),
        Result = intset(L, UB, diff_a_nb(Bs0, UA, As0))
    ).

    % intersection(A, B) = A /\ B
    %
intersection(nil, _) = nil.
intersection(intset(_, _, _), nil) = nil.
intersection(As @ intset(LA, UA, As0), Bs @ intset(LB, UB, Bs0)) = Result :-
    compare(R, LA, LB),
    (
        R = (<),
        Result = diff_a_nb(Bs, UA, As0)
    ;
        R = (=),
        Result = n_union_na_nb(LA, UA, As0, UB, Bs0)
    ;
        R = (>),
        Result = diff_a_nb(As, UB, Bs0)
    ).

    % int_na_b(U, A, B) = ({X | X > U} \ A) /\ B
    %
    % assuming U < min(A).
    %
:- func int_na_b(int, intset, intset) = intset.

int_na_b(_, _, nil) = nil.
int_na_b(UA, As0, Bs @ intset(LB, UB, Bs0)) = Result :-
    compare(R, UA, LB),
    (
        R = (<),
        Result = intset.difference(Bs, As0)
    ;
        R = (=),
        Result = n_union_a_nb(UA, As0, UB, Bs0)
    ;
        R = (>),
        Result = diff_na_nb(UA, As0, UB, Bs0)
    ).

    % n_int_na_nb(L, UA, A, UB, B) =
    %   {X | X > L} (({Y | Y > UA} \ A) /\ ({Z | Z > UB} \ B))
    %
    % aasuming L < UA, UA < min(A), L < UB and UB < min(B).
    %
:- func n_int_na_nb(int, int, intset, int, intset) =
    intset.

n_int_na_nb(L, UA, As0, UB, Bs0) = Result :-
    compare(R, UA, UB),
    (
        R = (<),
        Result = n_diff_na_b(L, UB, Bs0, As0)
    ;
        R = (=),
        Result = intset(L, UA, intset.union(As0, Bs0))
    ;
        R = (>),
        Result = n_diff_na_b(L, UA, As0, Bs0)
    ).

    % int_a_nb(A, U, B) = A /\ ({X | X > U} \ B)
    %
    % assuming U < min(B).
    %
:- func int_a_nb(intset, int, intset) = intset.

int_a_nb(nil, _, _) = nil.
int_a_nb(As @ intset(LA, UA, As0), UB, Bs0) = Result :-
    compare(R, LA, UB),
    (
        R = (<),
        Result = diff_na_nb(UB, Bs0, UA, As0)
    ;
        R = (=),
        Result = n_union_na_b(LA, UA, As0, Bs0)
    ;
        R = (>),
        Result = intset.difference(As, Bs0)
    ).

    % difference(A, B) = A \ B
    %
difference(nil, _) = nil.
difference(As @ intset(_, _, _), nil) = As.
difference(As @ intset(LA, UA, As0), Bs @ intset(LB, UB, Bs0)) = Result :-
    compare(R, LA, LB),
    (
        R = (<),
        Result = n_union_na_b(LA, UA, As0, Bs)
    ;
        R = (=),
        Result = diff_na_nb(UB, Bs0, UA, As0)
    ;
        R = (>),
        Result = int_a_nb(As, UB, Bs0)
    ).

    % n_diff_na_b(L, U, A, B) = {X | X > L} \ (({Y | Y > U} \ A) \ B)
    %
    % assuming L < U, U < min(A) and L < min(B).
    %
:- func n_diff_na_b(int, int, intset, intset) = intset.

n_diff_na_b(L, U, As, nil) = intset(L, U, As).
n_diff_na_b(L, UA, As0, Bs @ intset(LB, UB, Bs0)) = Result :-
    compare(R, UA, LB),
    (
        R = (<),
        Result = intset(L, UA, intset.union(As0, Bs))
    ;
        R = (=),
        Result = n_diff_na_b(L, UB, Bs0, As0)
    ;
        R = (>),
        Result = n_int_na_nb(L, UA, As0, UB, Bs0)
    ).

    % diff_a_nb(A, U, B) = A \ ({X | X > U} \ B)
    %
    % assuming U < min(B).
    %
:- func diff_a_nb(intset, int, intset) = intset.

diff_a_nb(nil, _, _) = nil.
diff_a_nb(As @ intset(LA, UA, As0), UB, Bs0) = Result :-
    compare(R, LA, UB),
    (
        R = (<),
        Result = n_union_na_nb(LA, UA, As0, UB, Bs0)
    ;
        R = (=),
        Result = diff_a_nb(Bs0, UA, As0)
    ;
        R = (>),
        Result = intset.intersection(As, Bs0)
    ).

    % diff_na_nb(UA, A, UB, B) = ({X | X > UA} \ A) \ ({Y | Y > UB} \ B)
    %
    % assuming UA < min(A) and UB < min(B).
    %
:- func diff_na_nb(int, intset, int, intset) = intset.

diff_na_nb(UA, As0, UB, Bs0) = Result :-
    compare(R, UA, UB),
    (
        R = (<),
        Result = n_union_a_nb(UA, As0, UB, Bs0)
    ;
        R = (=),
        Result = intset.difference(Bs0, As0)
    ;
        R = (>),
        Result = int_na_b(UA, As0, Bs0)
    ).

%-----------------------------------------------------------------------------%

restrict_min(_, nil) = nil.
restrict_min(Min, As0 @ intset(L, U, As1)) = As :-
    ( if Min =< L then
        As = As0
    else if Min =< U then
        As = intset(Min - 1, U, As1)
    else
        As = restrict_min(Min, As1)
    ).

restrict_max(_, nil) = nil.
restrict_max(Max, intset(L, U, As0)) = As :-
    ( if Max =< L then
        As = nil
    else if Max =< U then
        As = intset(L, Max, nil)
    else
        As = intset(L, U, restrict_max(Max, As0))
    ).

restrict_intset(Min, Max, As) =
    intset.intersection(intset(Min - 1, Max, nil), As).

%-----------------------------------------------------------------------------%

prune_to_next_non_member(nil, nil, !N).
prune_to_next_non_member(As @ intset(LA, UA, As0), Result, !N) :-
    ( if !.N =< LA then
        Result = As
    else if !.N =< UA then
        !:N = UA + 1,
        Result = As0
    else
        prune_to_next_non_member(As0, Result, !N)
    ).

prune_to_prev_non_member(nil, nil, !N).
prune_to_prev_non_member(intset(LA, UA, As0), Result, !N) :-
    ( if !.N =< LA then
        Result = nil
    else if !.N =< UA then
        !:N = LA,
        Result = nil
    else
        prune_to_prev_non_member(As0, Result0, !N),
        Result = intset(LA, UA, Result0)
    ).


negate(As) = negate_aux(As, nil).

:- func negate_aux(intset::in, intset::in) = (intset::out) is det.

negate_aux(nil, As) = As.
negate_aux(intset(L, U, As), A) = negate_aux(As, intset(-U-1, -L-1, A)).


plus(nil, nil) = nil.
plus(nil, intset(_,_,_)) = nil.
plus(intset(_,_,_), nil) = nil.
plus(intset(La, Ha, nil), intset(L, H, nil)) = intset(La + L + 1, Ha + H, nil).
plus(intset(Lx0, Hx0, Xs0 @ intset(Lx1, Hx1, Xs1)), intset(L, H, nil)) = Result :-
    ( if Lx1 - Hx0 < H - L then
        Result = plus(intset(Lx0, Hx1, Xs1), intset(L, H, nil))
    else
        Result = intset(Lx0 + L + 1, Hx0 + H, plus(Xs0, intset(L, H, nil)))
    ).
plus(intset(Lx, Hx, Xs), intset(L, H, S @ intset(_,_,_))) = Result :-
    A = plus(intset(Lx, Hx, Xs), intset(L, H, nil)),
    B = plus(intset(Lx, Hx, Xs), S),
    Result = union(A,B).

shift(nil, _) = nil.
shift(As @ intset(L, H, As0), C) = Result :-
    ( if C = 0 then
        Result = As
    else
        Result = intset(L + C, H + C, shift(As0, C))
    ).

dilation(nil, _) = nil.
dilation(A @ intset(_,_,_) , C) = Result :-
    ( if C < 0 then
        Result = dilation(negate(A), -C)
    else if C = 0 then
        Result = intset(-1, 0, nil)
    else if C = 1 then
        Result = A
    else
        L = to_sorted_list(A),
        list.map(*(C), L) = L0,
        Result = from_list(L0)
    ).

contraction(nil, _) = nil.
contraction(A @ intset(L, H, As), C) = Result :-
    ( if C < 0 then
        Result = contraction(negate(A), -C)
    else if C = 0 then
        Result = intset(-1, 0, nil)
    else if C = 1 then
        Result = A
    else
        L0 = div_up_xp(L + 1, C) - 1,
        H0 = div_down_xp(H, C),
        Result = contraction_0(L0, H0, As, C)
    ).

:- func contraction_0(int, int, intset, int) = intset.

contraction_0(L0, H0, nil, _) = intset(L0, H0, nil).
contraction_0(L0, H0, intset(L1, H1, As), C) = Result :-
    L1N = div_up_xp(L1 + 1, C) - 1, 
    H1N = div_down_xp(H1, C),
    ( if H0 >= L1N then
        Result = contraction_0(L0, H1N, As, C)
    else
        Result = intset(L0, H0, contraction_0(L1N, H1N, As, C))
    ).


%-----------------------------------------------------------------------------%

to_sorted_list(nil) = [].
to_sorted_list(intset(L, H, Rest)) =
    to_sorted_list_2(L, H, to_sorted_list(Rest)).

:- func to_sorted_list_2(int, int, list(int)) = list(int).

to_sorted_list_2(L, H, Ints) =
    ( if   H = L
      then Ints
      else to_sorted_list_2(L, H-1, [H | Ints])
    ).

from_list(List) =
    list.foldl(intset.insert, List, intset.empty).

from_set(Set) =
    intset.from_list(set.to_sorted_list(Set)).

%-----------------------------------------------------------------------------%

%compare_intset(A, B) = O :-
%    (      if A = B        then O = cb_equal
%      else if intset.subset(A, B) then O = cb_less_than
%      else if intset.subset(B, A) then O = cb_greater_than
%      else O = cb_incomparable
%    ).

%-----------------------------------------------------------------------------%

intset_foldl(_, nil, !T).
intset_foldl(P, intset(L, U, Rest), !T) :-
    P(L + 1, U, !T),
    intset.intset_foldl(P, Rest, !T).

intset_foldl2(_, nil, !S, !T).
intset_foldl2(P, intset(L, U, Rest), !S, !T) :-
    P(L + 1, U, !S, !T),
    intset.intset_foldl2(P, Rest, !S, !T).

intset_foldl_ui(P, D, !T, U) :-
    (
        D = nil
    ;
        D = intset(L, H, Rest),
        P(L + 1, H, !T, U),
        intset.intset_foldl_ui(P, Rest, !T, U)
    ).

intset_foldr(_, nil, !T).
intset_foldr(P, intset(L, U, Rest), !T) :-
    intset.intset_foldr(P, Rest, !T),
    P(L + 1, U, !T).

intset_foldr_ui(P, D, !T, U) :-
    (
        D = nil
    ;
        D = intset(L, H, Rest),
        intset.intset_foldr_ui(P, Rest, !T, U),
        P(L + 1, H, !T, U)
    ).

%-----------------------------------------------------------------------------%

intset_elems_foldl(P, Ranges, !Acc) :-
    (
        Ranges = nil
    ;
        Ranges = intset(L, U, Rest),
        int.fold_up(P, L + 1, U, !Acc),
        intset_elems_foldl(P, Rest, !Acc)
    ).

intset_elems_foldl2(P, Ranges, !Acc1, !Acc2) :-
    (
        Ranges = nil
    ;
        Ranges = intset(L, U, Rest),
        int.fold_up2(P, L + 1, U, !Acc1, !Acc2),
        intset_elems_foldl2(P, Rest, !Acc1, !Acc2)
    ).

%-----------------------------------------------------------------------------%

intset_elems_foldr(P, D, !T) :-
    (
        D = nil
    ;
        D = intset(L, H, Rest),
        intset_elems_foldr(P, Rest, !T),
        int.fold_down(P, L + 1, H, !T) 
    ).

intset_elems_foldr2_ui(P, D, !T, !U, S) :-
    (
        D = nil
    ;
        D = intset(L, H, Rest),
        intset_elems_foldr2_ui(P, Rest, !T, !U, S),
        int_fold_down2_ui(P, L + 1, H, !T, !U, S)
    ).

:- pred int_fold_down2_ui(pred(int, T, T, U, U, S), int, int, T, T, U, U, S).
:- mode int_fold_down2_ui(pred(in, in, out, in, out, ui) is det, in, in,
    in, out, in, out, ui) is det.

int_fold_down2_ui(P, L, H, !T, !U, S) :-
    ( if L > H then
        true
    else
        P(H, !T, !U, S),
        int_fold_down2_ui(P, L, H - 1, !T, !U, S)
    ).

%-----------------------------------------------------------------------------%

to_string(L) = intset.to_string_2(L, yes).

to_string_no_abbr(L) = intset.to_string_2(L, no).

:- func intset.to_string_2(intset, bool) = string.

intset.to_string_2(Domain, UseAbbr) = Desc :-
    Pred = (pred(L::in, U::in, Seq1::in, Seq2::out) is det :-
        Str = ( if L = U
                then int_to_string(L)
                else if L + 1 = U
                then int_to_string(L) ++ ", " ++ int_to_string(U)
                else if UseAbbr = yes
                then int_to_string(L) ++ ".." ++ int_to_string(U)
                else string.join_list(", ",
                    list.map(string.int_to_string, L..U))
            ),
        Seq2 = [Str | Seq1]
    ),
    intset.intset_foldl(Pred, Domain, [], RevDescSeq),
    Desc = "{" ++ join_list(", ", list.reverse(RevDescSeq))  ++ "}".

%-----------------------------------------------------------------------------%

    % Set up the formatter for intset for debugging and printing.
    %
%:- pred init_intset(io::di, io::uo) is det.
%
%init_intset(!IO) :-
%    pretty_printer.set_default_formatter("intset", "intset", 0,
%        fmt_intset, !IO),
%    pretty_printer.set_default_formatter("intset", "intset", 0,
%        fmt_intset, !IO).

%-----------------------------------------------------------------------------%

%:- func fmt_intset(univ, list(type_desc)) = doc.
%
%fmt_intset(Univ, ArgTypes) = Doc :-
%    ( if
%        Univ = univ(Ranges),
%        ArgTypes = []
%      then
%        Doc = str(string.format("<intset%s>", [s(intset.to_string(Ranges))]))
%      else
%        Doc = str("?intset?")
%    ).

%-----------------------------------------------------------------------------%
%
% From g12.libs.int_util.
%

    % 0 < B.  Round up.
:- func div_up_xp(int::in, int::in) = (int::out) is det.

div_up_xp(A, B)   = (A > 0 -> div_up_pp(A, B) ; div_up_np(A, B)).

    % 0 < B.  Round down.
:- func div_down_xp(int::in, int::in) = (int::out) is det.

div_down_xp(A, B) = (A > 0 -> div_down_pp(A, B) ; div_down_np(A, B)).

    % 0 < A,B.    Round up.
:- func div_up_pp(int::in, int::in) = (int::out) is det.

div_up_pp(A, B)   = int.unchecked_quotient(A + B - 1, B).

    % A < 0 < B.  Round up.
:- func div_up_np(int::in, int::in) = (int::out) is det.

div_up_np(A, B)   = int.unchecked_quotient(A, B).
    
    % 0 < A,B.    Round down.
:- func div_down_pp(int::in, int::in) = (int::out) is det.

div_down_pp(A, B) = int.unchecked_quotient(A, B).

    % A < 0 < B.  Round down.
:- func div_down_np(int::in, int::in) = (int::out) is det.

div_down_np(A, B) = int.unchecked_quotient(A - B + 1, B).

%-----------------------------------------------------------------------------%
:- end_module intset.
%-----------------------------------------------------------------------------%
