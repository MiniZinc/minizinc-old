%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Flattening MiniZinc to FlatZinc using the half-reification approach.
%
%-----------------------------------------------------------------------------%

:- module translate.
:- interface.

:- include_module translate.array.
:- include_module translate.bool.
:- include_module translate.float.
:- include_module translate.int.
:- include_module translate.string.

:- include_module translate.info.
:- include_module translate.item.
:- include_module translate.opt.
:- include_module translate.vars.

%-----------------------------------------------------------------------------%
:- end_module translate.
%-----------------------------------------------------------------------------%
