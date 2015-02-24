%-----------------------------------------------------------------------------%
% vim: ts=4 sw=4 et ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2012 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: zs.
%
% Optimise the FlatZinc representation of a problem.
%
%-----------------------------------------------------------------------------%

:- module translate.opt.
:- interface.

:- import_module tfzn_ast.

:- import_module list.

:- pred tr_optimise_flatzinc(
    list(tfzn_item_par_decl)::in, list(tfzn_item_par_decl)::out,
    list(tfzn_item_var_decl)::in, list(tfzn_item_var_decl)::out,
    tfzn_item_solve::in, tfzn_item_solve::out,
    list(tfzn_item_constraint)::in, list(tfzn_item_constraint)::out)
    is det.

%-----------------------------------------------------------------------------%

:- implementation.

tr_optimise_flatzinc(!ParDecls, !VarDecls, !Solve, !TFznConstraints).
    % NYI
    % We should implement here all the optimizations done by opt.m.
