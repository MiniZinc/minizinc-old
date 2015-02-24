%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2012 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
% Stuff that may be useful to both of the output_tmzn and output_tfzn modules.
%
%-----------------------------------------------------------------------------%

:- module output_common.
:- interface.

:- import_module types.

:- import_module bool.
:- import_module set.

:- type output_opts
    --->    output_opts(
                oo_informal_syntax      :: bool,
                oo_pad_length           :: int
            ).

:- func int_range_type_to_str(int_range) = string.
:- func float_range_type_to_str(float_range) = string.

:- func bool_to_str(bool) = string.
:- func int_set_to_str(set(int)) = string.
:- func float_set_to_str(set(float)) = string.

%-----------------------------------------------------------------------------%

:- implementation.

:- import_module intset.
:- import_module list.
:- import_module string.

%-----------------------------------------------------------------------------%

int_range_type_to_str(IntRange) = TypeName :-
    (
        IntRange = int_range_unbounded,
        TypeName = "int"
    ;
        IntRange = int_range_lb_ub(LB, UB),
        string.format("%d..%d", [i(LB), i(UB)], TypeName)
    ;
        IntRange = int_range_set(IntSet),
        IntStrs = list.map(string.int_to_string,
            intset.to_sorted_list(IntSet)),
        TypeName = "{" ++ string.join_list(", ", IntStrs) ++ "}"
    ).

float_range_type_to_str(FloatRange) = TypeName :-
    (
        FloatRange = float_range_unbounded,
        TypeName = "float"
    ;
        FloatRange = float_range_lb_ub(LB, UB),
        string.format("%f..%f", [f(LB), f(UB)], TypeName)
    ;
        FloatRange = float_range_set(FloatSet),
        FloatStrs = list.map(string.float_to_string,
            set.to_sorted_list(FloatSet)),
        TypeName = "{" ++ string.join_list(", ", FloatStrs) ++ "}"
    ).

%-----------------------------------------------------------------------------%

bool_to_str(no) = "false".
bool_to_str(yes) = "true".

int_set_to_str(IntSet) = Str :-
    IntStrs = list.map(string.int_to_string, set.to_sorted_list(IntSet)),
    Str = "{" ++ string.join_list(", ", IntStrs) ++ "}".

float_set_to_str(FloatSet) = Str :-
    FloatStrs = list.map(string.float_to_string, set.to_sorted_list(FloatSet)),
    Str = "{" ++ string.join_list(", ", FloatStrs) ++ "}".

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
