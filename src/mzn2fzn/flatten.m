%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2009-2011 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Ralph Becket <rafe@csse.unimelb.edu.au>
%
% Flattening MiniZinc to FlatZinc.
%
%-----------------------------------------------------------------------------%

:- module flatten.
:- interface.

:- include_module flatten.ann.
:- include_module flatten.app.
:- include_module flatten.array.
:- include_module flatten.bool.
:- include_module flatten.comp.
:- include_module flatten.env.
:- include_module flatten.expr.
:- include_module flatten.float.
:- include_module flatten.int.
:- include_module flatten.item.
:- include_module flatten.let.
:- include_module flatten.output.
:- include_module flatten.set.
:- include_module flatten.string.

%-----------------------------------------------------------------------------%
:- end_module flatten.
%-----------------------------------------------------------------------------%
