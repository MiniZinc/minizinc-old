%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2008 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%

:- module g12_zinc_frontend.
:- interface.

%-----------------------------------------------------------------------------%

:- import_module builtins.
:- import_module compiler_common.
:- import_module intset.
:- import_module parse_stage.
:- import_module simple_term_parser.
:- import_module structure_check.
:- import_module symbol_table.
:- import_module top_sort.
:- import_module type_inst_check.
:- import_module types_and_insts.
:- import_module zinc_ast.
:- import_module zinc_common.
:- import_module zinc_frontend.
:- import_module zinc_frontend2.
:- import_module zinc_pprint.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- pragma require_feature_set([]).

%-----------------------------------------------------------------------------%
:- end_module g12_zinc_frontend.
%-----------------------------------------------------------------------------%
