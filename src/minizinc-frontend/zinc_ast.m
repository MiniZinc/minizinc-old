%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2006-2010 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Authors: Nicholas Nethercote <njn@csse.unimelb.edu.au>
%          Julien Fischer <juliensf@csse.unimelb.edu.au>
%
% Abstract Syntax Tree (AST) for Zinc and related languages.
%
%-----------------------------------------------------------------------------%

:- module zinc_ast.
:- interface.

%-----------------------------------------------------------------------------%

:- import_module types_and_insts.
:- import_module zinc_common.

:- import_module bool.
:- import_module list.
:- import_module maybe.
:- import_module pair.

%-----------------------------------------------------------------------------%
%
% AST
%

    % The unstructured AST.  This is the representation of a Zinc model
    % as initially read in by the parser or as the result of a Cadmium
    % pass.  The model may not be structurally valid, i.e. it could
    % contain multiple solve or output items.
    %
:- type ast == items.

%-----------------------------------------------------------------------------%
%
% Structured AST.
%

% The structured AST represents most of the model as a list of items, except
% the solve and output item; for those it provides constant time access.
% In addition, the structured AST provides an different representation for
% the solve item that reduces the amount of boilerplate code required by
% frontend clients.
%
% The plain AST is converted into SAST form by the structure-checking pass.

:- type sast
    --->    sast(
                sast_items      :: items,
                % All model items except the solve and output item.

                sast_solve      :: sast_solve_item,
                % The solve item (in SAST form).

                sast_output     :: maybe(item)
                % The output item, if present.
            ).

    % A SAST-specific representation of a model's solve item.
    %
:- type sast_solve_item
    --->    sast_solve_item(
                sast_solve_kind :: solve_kind,
                sast_solve_anns :: exprs,
                sast_solve_locn :: src_locn
            ).

%-----------------------------------------------------------------------------%
%
% OZN AST.
%

:- type oast_output_item
    --->    oast_output_item(
                oast_out_expr   :: expr,
                oast_out_locn   :: src_locn
            ).

:- type oast
    --->    oast(
                oast_item       :: items,
                % Variable declaration and assign items.
                % XXX are the latter necessary?

                oast_output     :: oast_output_item
            ).

%-----------------------------------------------------------------------------%
%
% Items
%

:- type items == list(item).
:- type item
    --->    item(
                raw_item        :: raw_item,
                item_src_locn   :: src_locn
            ).

    % Sort an AST by location (filenames/line numbers).
    %
:- func sort_ast_by_locn(ast) = ast.

%-----------------------------------------------------------------------------%

    % A lot of the items use a 'name' rather than an 'id' -- this is because
    % these names are known to be global, so there is no need to store the
    % scope number with them.
    %
    % Nb: include items aren't represented here.  They are processed and
    % removed during parsing.
    %
    % Nb: we put the most frequent ones first, so they will get the more
    % compact tag representation.
    %
:- type raw_item
    --->    constraint_item(
                constraint_item_expr    :: expr
            )
    ;       var_decl_item(
                var_decl_ti_expr        :: ti_expr,
                var_decl_name           :: zinc_name,
                var_decl_annotations    :: exprs,
                var_decl_maybe_value    :: var_decl_assignment
            )
    ;       assign_item(
                assign_name             :: zinc_name,
                assign_value            :: expr
            )
    ;       % New 'predfunc_item's can be constructed with 'raw_predfunc_init'.
            predfunc_item(
                % Functions have 'func_ret(ti_expr)' as their return type.
                % Predicates have 'pred_ret' (they're implicitly 'var bool').
                % Tests have 'test_ret' (they're implicitly 'par bool').
                predfunc_item_ret       :: predfunc_ret,
                predfunc_item_name      :: zinc_name,

                % Each pred/func *symbol* can be overloaded and thus represents
                % 1..N distinct preds/funcs, each with their own
                % type-signature.  Each pred/func symbol also has 0..M
                % "procedures", each of which has a different
                % type-inst-signature.
                %
                % Eg. the '+' operation symbol has four type-sigs and eight
                % procedures (where i/f are int/float, pi/vi/pf/vf are par
                % int/var int/par float/var float):
                %
                % TSigs:  [(i,i)->i, (f,f)->f, (i)->i, (f)->]
                % TISigs: [(pi,pi)->pi, (vi,vi)->vi, (pf,pf)->pf, (vf,vf)->vf)
                %          (pi)->pi, (vi)->vi, (pf)->pf, (vf)->vf)]
                %
                % The following number specifies which procedure this item
                % represents.  It indexes into the symbol's type-inst-sigs list
                % in the symbol table.  is in the symbol table.  It is
                % initially 'unset_proc_number', and is set to 1..N by
                % type-inst-checking.
                %
                predfunc_item_proc_number   :: int,

                predfunc_item_params        :: ti_exprs_and_ids,
                predfunc_item_annotations   :: exprs,
                predfunc_item_maybe_body    :: maybe(expr)
            )
    ;       annotation_item(
                annotation_item_name        :: zinc_name,
                % Nb: because the argument names are never used (because
                % annotations have no body, the names only serve as
                % documentation), we don't bother putting them in the symbol
                % table, and we don't bother ever giving them a scope_number.
                annotation_item_params      :: ti_exprs_and_ids
            )
    ;       solve_item(
                solve_item_kind         :: solve_kind,
                solve_annotations       :: exprs
            )
    ;       output_item(
                output_expr             :: expr
            )
    .


:- type var_decl_assignment
    --->    no_assignment
            % This variable declaration has no assignment.
    
    ;       rhs_assignment(expr)
            % This variable declaration has an assignment on its rhs.

    ;       separate_assignment(src_locn, expr).
            % This variable declaration has an assignment that originally
            % occurs as a separate assign item.  The src_locn gives this
            % original location.

:- type predfunc_ret
    --->    pred_ret
    ;       test_ret
    ;       func_ret(ti_expr).

:- type solve_kind
    --->    satisfy
    ;       minimize(expr)
    ;       maximize(expr).

:- type ti_exprs_and_names == list(ti_expr_and_name).
:- type ti_expr_and_name   == pair(ti_expr, zinc_name).

:- type ti_exprs_and_ids == list(ti_expr_and_id).
:- type ti_expr_and_id   == pair(ti_expr, id).

:- type local_vars ==   list(local_var).
:- type local_var
    --->    local_var(ti_expr, id, exprs, maybe(expr)).

%-----------------------------------------------------------------------------%
%
% Procedure IDs.
%

    % A proc_id uniquely identifies a procedure.
    %
:- type proc_id
    --->    proc_id(
                proc_name   :: zinc_name,   % pred/func/operator name
                proc_number :: int          % procedure number
            ).

%-----------------------------------------------------------------------------%
%
% Type-inst expressions.
%

:- type ti_exprs == list(ti_expr).
:- type ti_expr
    --->    ti_expr(
                raw_ti_expr     :: raw_ti_expr,
                ti_expr_info    :: expr_info
            ).

:- type raw_ti_expr
    --->    raw_ti_expr(
                var_par                 :: var_par,
                base_ti_expr_tail       :: base_ti_expr_tail
            ).

:- type var_par
    --->    par
    ;       var.

:- type base_ti_expr_tail
            % Nb: we put the most frequent ones first, so they will get the
            % more compact tag representation.
            %
    --->    bte_int
            % The args should be both integer exprs or both float exprs.
    ;       bte_range_expr_as_type_expr(expr, expr)   % eg. 1..n -- as a type
    ;       bte_array_of(ti_exprs, ti_expr, /*Is it a 'list of' array?*/bool)
    ;       bte_ident(id)           % Nb: can be a type name *or* a set name.
    ;       bte_bool
    ;       bte_float
    ;       bte_set_of(ti_expr)
    ;       bte_typeinst_var(zinc_name)    % The name excludes the leading '$'.
    ;       bte_any_typeinst_var(zinc_name)% The name excludes the leading '$'.
    ;       bte_tuple_of(ti_exprs)
    ;       bte_set_expr_as_type_expr(exprs)     % eg. {1,2,3} -- as a type
    ;       bte_string
    ;       bte_ann
    ;       bte_bottom
    ;       bte_error       % Only occurs by lifting 'ti_error' to a 'ti_expr'.
    .

:- type ti_expr_sigs == list(ti_expr_sig).
:- type ti_expr_sig  == pair(ti_exprs, ti_expr).

%-----------------------------------------------------------------------------%

    % Lift a type_inst to a type-inst expression.  For ti_error, the
    % raw_ti_expr of the result is raw_ti_expr(none, bte_bottom).  See the
    % comment on the definition of base_ti_expr_tail for an explanation.
    %
:- func lift_type_inst_to_ti_expr(src_locn, type_inst) = ti_expr.

%-----------------------------------------------------------------------------%
% Expressions
%-----------------------------------------------------------------------------%

    % Nb: we can represent these two:
    %
    %   e :: a :: b
    %   e :: (a :: b)
    %
    % But not this:
    %
    %   (e :: a) :: b
    %
    % So that becomes 'e :: a :: b'.  The meaning of them all is the same,
    % so that's ok.
    %
:- type exprs == list(expr).
:- type expr
    --->    expr(
                raw_expr    :: raw_expr,
                annotations :: exprs,
                expr_info   :: expr_info
            ).

    % Nb: we put the most frequent ones first, so they will get the more
    % compact tag representation.
    %
:- type raw_expr
    % Atomic expressions
            % Can be a variable name, func/pred name, quoted operator name,
            % or set type name.
    --->    ident(id)
    ;       lit(literal)
            % New 'app' exprs can be constructed with 'raw_app_init'.
    ;       app(                % May be a call or simple non-flat enum lit.
                app_id          :: id,

                % This specifies which procedure is being called.  See
                % predfunc_item above for details.  Initially
                % 'unset_proc_number', set to 1..N by type-inst-checking.
                app_proc_number :: int,

                app_kind        :: app_kind,
                app_args        :: exprs
            )
    ;       array_access(expr, exprs)
    ;       lit_set(exprs)
    ;       lit_simple_array(exprs)
    ;       lit_tuple(exprs)
    ;       lit_ann(id, exprs)
    ;       comprehension(
                comprehension_kind,
                generators,
                maybe(expr)             % maybe: where expression
            )
    ;       anon_var                    % `_'
    ;       if_then_else(expr, expr, expr)
    ;       let(local_vars, expr)
            % Introduced during type-inst-checking.
    ;       coerce(type_inst, type_inst, expr)
    .

:- func expr_init(raw_expr, expr_info) = expr.

:- func raw_predfunc_init(predfunc_ret, zinc_name, ti_exprs_and_ids, exprs,
    maybe(expr)) = raw_item.

:- func raw_app_init(zinc_name, app_kind, exprs) = raw_expr.

:- func unset_proc_number = int.

%-----------------------------------------------------------------------------%

:- type literal
    --->    bool(bool)
    ;       string(string)
    ;       int(int)
    ;       floatstr(string).   % We use a string prior to model evaluation to
                                % avoid any inaccuracies caused by rounding.
:- type comprehension_kind
    --->    set_comp(expr)
    ;       simple_array_comp(expr).

:- type generators == list(generator).
:- type generator ---> generator(list(id), expr).

:- type index_exprs == list(index_expr).
:- type index_expr  == pair(expr, expr).

:- type named_exprs == list(named_expr).
:- type named_expr  == pair(zinc_name, expr).

:- type id_exprs    == list(id_expr).
:- type id_expr     == pair(id, expr).

:- type app_kind
    --->    predfunc_app        % Normal function/predicate call expression.
    ;       gen_call_app        % Generator call expression.
    ;       operator_app        % Application of an operator.
    ;       array2d_literal     % A 2d array literal represented as a call
    .                           %   to 'array2d'.

:- type array_kind
    --->    tuple_value
    ;       record_value
    ;       set_value
    ;       list_value
    ;       array_value.

:- type array_values == index_exprs.

%-----------------------------------------------------------------------------%

:- type expr_info
    --->    expr_info(
                expr_src_locn   :: src_locn,
                expr_type_inst  :: type_inst    % ti_unknown until
            ).                                  %   type-inst-checking

:- func expr_info_init(src_locn           ) = expr_info.
:- func expr_info_init(src_locn, type_inst) = expr_info.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module require.
:- import_module string.

%-----------------------------------------------------------------------------%

expr_init(RawE, EInfo) = expr(RawE, [], EInfo).

    % ProcN is initially 'unset_proc_number'.
raw_predfunc_init(PredFuncRet, Name, Params, Anns, MaybeBodyE) =
    predfunc_item(PredFuncRet, Name, unset_proc_number, Params, Anns,
        MaybeBodyE).

    % ProcN is initially 'unset_proc_number'.
raw_app_init(Name, AppKind, Args) =
    app(id_init(Name), unset_proc_number, AppKind, Args).

%-----------------------------------------------------------------------------%

    % A number that is clearly not a valid index and stands out when debugging.
unset_proc_number = -777.

%-----------------------------------------------------------------------------%

expr_info_init(SrcLocn) = expr_info(SrcLocn, ti_unknown).

expr_info_init(SrcLocn, TI) = expr_info(SrcLocn, TI).

%-----------------------------------------------------------------------------%

sort_ast_by_locn(Items) = SortedItems :-
    sort(item_compare, Items, SortedItems).

%-----------------------------------------------------------------------------%

:- pred item_compare : comparison_pred(item) `with_inst` comparison_pred.

item_compare(Item1, Item2, Cmp) :-
    Item1 = item(RawItem1, Locn1),
    Item2 = item(RawItem2, Locn2),

    % Ordering:
    % - builtins before unknowns before src_locns
    % - ordering within builtins is arbitrary, as is ordering within unknowns
    % - for src_locn, sort by file, then line number
    (
        Locn1 = builtin,
        (   Locn2 = builtin, compare(Cmp, RawItem1, RawItem2)
        ;   Locn2 = unknown, Cmp = (<)
        ;   Locn2 = src_locn(_,_), Cmp = (<)
        )
    ;
        Locn1 = unknown,
        (   Locn2 = builtin, Cmp = (>)
        ;   Locn2 = unknown, compare(Cmp, RawItem1, RawItem2)
        ;   Locn2 = src_locn(_,_), Cmp = (<)
        )
    ;
        Locn1 = src_locn(File1, Line1),
        (   Locn2 = builtin, Cmp = (>)
        ;   Locn2 = unknown, Cmp = (>)
        ;   Locn2 = src_locn(File2, Line2),
            compare(Cmp, { File1, Line1 }, { File2, Line2 })
        )
    ).

%-----------------------------------------------------------------------------%

lift_type_inst_to_ti_expr(Locn, TI) = TIE :-
    (
        TI = ti_par_bottom,
        VarPar = par,
        BaseTIETail = bte_bottom
    ;
        TI = ti_var_bottom,
        VarPar = var,
        BaseTIETail = bte_bottom
    ;
        TI = ti_par_bool,
        VarPar = par,
        BaseTIETail = bte_bool
    ;
        TI = ti_var_bool,
        VarPar = var,
        BaseTIETail = bte_bool
    ;
        TI = ti_par_int,
        VarPar = par,
        BaseTIETail = bte_int
    ;
        TI = ti_var_int,
        VarPar = var,
        BaseTIETail = bte_int
    ;
        TI = ti_par_float,
        VarPar = par,
        BaseTIETail = bte_float
    ;
        TI = ti_var_float,
        VarPar = var,
        BaseTIETail = bte_float
    ;
        TI = ti_par_string,
        VarPar = par,
        BaseTIETail = bte_string
    ;
        TI = ti_ann,
        VarPar = par,
        BaseTIETail = bte_ann
    ;
        TI = ti_par_variable(X,_),
        VarPar = par,
        BaseTIETail = bte_typeinst_var(X)
    ;
        TI = ti_any_variable(X,_),
        VarPar = par,
        BaseTIETail = bte_any_typeinst_var(X)
    ;
        TI = ti_par_set(ElemTI),
        VarPar = par,
        BaseTIETail = bte_set_of(lift_type_inst_to_ti_expr(Locn, ElemTI))
    ;
        TI = ti_var_set(ElemTI),
        VarPar = var,
        BaseTIETail = bte_set_of(lift_type_inst_to_ti_expr(Locn, ElemTI))
    ;
        TI = ti_array(IndexTI, ElemTI),
        VarPar = par,
        BaseTIETail = bte_array_of([lift_type_inst_to_ti_expr(Locn, IndexTI)],
                                    lift_type_inst_to_ti_expr(Locn, ElemTI),
                                    no)
    ;
        TI = ti_tuple(TIs),
        VarPar = par,
        BaseTIETail = bte_tuple_of(map(lift_type_inst_to_ti_expr(Locn), TIs))
    ;
        TI = ti_error,
        VarPar = par,
        BaseTIETail = bte_error
    ;
        ( TI = ti_top
        ; TI = ti_unknown
        ),
        unexpected($pred, ": TI = " ++ TI^string)
    ),
    TIE = ti_expr(raw_ti_expr(VarPar, BaseTIETail), expr_info(Locn, TI)).

%-----------------------------------------------------------------------------%
:- end_module zinc_ast.
%-----------------------------------------------------------------------------%
