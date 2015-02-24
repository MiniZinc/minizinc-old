%-----------------------------------------------------------------------------%
% vim: ft=mercury ts=4 sw=4 et wm=0 tw=0
%-----------------------------------------------------------------------------%
% Copyright (C) 2006-2009 The University of Melbourne and NICTA.
% See the file COPYING for license information.
%-----------------------------------------------------------------------------%
%
% Author: Nicholas Nethercote <njn@csse.unimelb.edu.au>
%
% The Zinc compiler's symbol table.  Symbols are indexed by name/scope-number
% pairs.
%-----------------------------------------------------------------------------%

:- module symbol_table.
:- interface.

%-----------------------------------------------------------------------------%

:- import_module types_and_insts.
:- import_module zinc_common.

:- import_module list.

%-----------------------------------------------------------------------------%

    % The symbol table:  
    % - maps ids to symbols.
    % - holds the counter for allocating new scope numbers.
    %
:- type symbol_table.

    % Individual symbols.
    %
:- type symbols == list(symbol).
:- type symbol
    --->    sym_variable(
                type_inst       :: type_inst,
                variable_kind   :: variable_kind,
                is_defined      :: is_defined,
                % is_defn_required == yes for variables which, in a valid
                %   instance, must be defined if they are used.  It depends on
                %   the variable's type-inst expression.
               
                is_defn_required :: is_defn_required,
                % has_range_value == yes if the variable is global and is
                %   assigned a range value.  It is used to check that arrays
                %   have fixed indices (eg. x..y) in MiniZinc and FlatZinc.
                
                has_range_value :: has_range_value,
                has_implicit_index :: has_implicit_index
            )

            % Because operations (funcs/preds/ops) may be overloaded (eg. '+'),
            % a single name may have multiple signatures.
            % We currently assume that, if multiple operations have the same
            % name, they are either all defined or all undefined.
    ;       sym_operation(
                % Each type-inst sig has a number (the procedure number,
                % ProcN).  The sigs must be kept in order (according to the
                % type-inst sig, not the ProcN), from lowest to highest, so we
                % match the lowest one possible at call sites.  For example,
                % "p(par int)->par int" would be before "p(var int)->var int".
                % Therefore the procedure numbers must be recorded explicitly
                % -- the position in the list is not enough, because the
                % ordering can change as new sigs are added.
                operation_kind :: operation_kind,
                operation_info :: proc_infos
            )

            % Nb: Annotations cannot be overloaded.
    ;       sym_annotation(
                annotation_type_insts :: type_insts   % TIs  of the args
            ).

:- type is_defined
    --->    defined
    ;       undefined.

:- type is_defn_required
    --->    defn_required
    ;       defn_not_required.

:- type has_range_value
    --->    has_range_value
    ;       does_not_have_range_value.

:- type has_implicit_index
    --->    has_implicit_index
    ;       does_not_have_implicit_index.

    % Describes variables.
    %
:- type variable_kind
    --->    global_var
    ;       let_var
    ;       generator_var
    ;       pred_arg
    ;       func_arg
    ;       ann_arg.

    % Nb: we don't distinguish between predicate items and test items, because
    % its possible to overload a name to be both, in which case calling them
    % both predicates makes things easier.
    %
:- type operation_kind
    --->    predicate_operation
    ;       function_operation
    ;       operator_operation.

:- type proc_infos == list(proc_info).
:- type proc_info
        --->    proc_info(
                    int,               % ProcN
                    is_defined,        % IsDefd
                    proc_is_annotated,
                    type_inst_sig
                ).

:- type proc_is_annotated
    --->    proc_is_annotated
    ;       proc_is_not_annotated.

    % Gets the ProcInfo for the given ProcN.
    % Aborts if not present.
    %
:- func get_proc_info(int, proc_infos) = proc_info.

:- type is_usable_as_value
    --->    usable_as_value
    ;       not_usable_as_value.

:- type is_finite
    --->    is_finite
    ;       is_not_finite.

%-----------------------------------------------------------------------------%

% These operations should only be used by phases that modify the symbol table.

:- func init = symbol_table.

    % Search for a perhaps-present symbol in the symbol table.
    %
:- pred maybe_find_symbol(id::in, symbol_table::in, symbol::out, src_locn::out)
    is semidet.

    % Add a previously unseen symbol to the symbol table.  Aborts if the
    % symbol is already in the symbol table.
    %
:- pred add_unseen_symbol(id::in, symbol::in, src_locn::in,
    symbol_table::in, symbol_table::out) is det.

:- pred get_new_scope_number(int::out, symbol_table::in, symbol_table::out)
    is det.

%-----------------------------------------------------------------------------%

% These operations are used by all phases that use the symbol table.

    % Find existing symbols in the symbol table.
    % Nb: these could be modified to return the src_locn of the symbol as
    % well, like maybe_find_symbol above, but it hasn't been necessary thus
    % far.
:- func find_existing_global_symbol(zinc_name, symbol_table) = symbol.
:- func find_existing_symbol(id, symbol_table) = symbol.

    % Replace an existing symbol in the symbol table.  Aborts if the symbol is
    % not already in the symbol table.
    %
:- pred replace_existing_symbol(id::in, symbol::in, src_locn::in,
    symbol_table::in, symbol_table::out) is det.
:- pred replace_existing_global_symbol(zinc_name::in, symbol::in, src_locn::in,
    symbol_table::in, symbol_table::out) is det.

%-----------------------------------------------------------------------------%

    % Nb: there is no 'pprint_symbol_table' because it's currently not
    % needed;  the symbol table is only shown for --dump-{before,after}
    % options.
:- pred dump_symbol_table :  writer(symbol_table) `with_inst` writer.

%-----------------------------------------------------------------------------%

:- pred foldl(pred(id, symbol, src_locn, A, A)::
                pred(in, in, in, in, out) is det,
        symbol_table::in, A::in, A::out) is det.

%-----------------------------------------------------------------------------%

:- instance show(symbol).

%-----------------------------------------------------------------------------%

    % Some type operations.  You might expect these to be in
    % types_and_insts.m, but they require the symbol table as an input, and
    % this module imports types_and_insts.m, so this is a reasonable spot for
    % them.

    % Nb: ti_error is considered to be fixed.
:- pred ti_is_fixed(symbol_table::in, type_inst::in) is semidet.

    % Converts any 'var' elements in the type-inst to 'par'.
:- func parify_type_inst(symbol_table, type_inst) = type_inst is det.

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

:- implementation.

:- import_module assoc_list.
:- import_module bool.
:- import_module counter.
:- import_module io.
:- import_module map.
:- import_module pair.
:- import_module require.
:- import_module string.

%-----------------------------------------------------------------------------%

:- type symbol_table
    --->    symbol_table(
                % We store all the global symbols together because there can
                % be a lot of them (esp. for large FlatZinc files), and
                % avoiding storing and comparing all those identical
                % scope_numbers can save a non-negligible amount of time.  In
                % comparison, there are typically not that many local symbols,
                % so we bundle them all together for simplicity.
                global_symbols  :: map(zinc_name, pair(symbol, src_locn)),
                local_symbols   :: map(id,   pair(symbol, src_locn)),
                scope_ctr       :: counter  % For allocating new scope numbers.
            ).

%-----------------------------------------------------------------------------%
% Symbol table operations
%-----------------------------------------------------------------------------%

get_proc_info(_, []) = _ :- unexpected($pred ++ ": proc_info not found").
get_proc_info(ProcN0, [ProcInfo | ProcInfos]) = Out :-
    ProcInfo = proc_info(ProcN, _, _, _),
    ( if ProcN0 = ProcN then
        Out = ProcInfo
      else
        Out = get_proc_info(ProcN0, ProcInfos)
    ).

%-----------------------------------------------------------------------------%

init =
    symbol_table(    
        map.init,
        map.init,
        counter.init(1)
    ).

maybe_find_symbol(Id, SymTbl, Sym, Locn) :-
    (
        Id = id_global(Name),
        Sym-Locn = map.search(SymTbl ^ global_symbols, Name)
    ;
        ( Id = id_scoped(_, _)
        ; Id = id_unset(_)
        ),
        Sym-Locn = map.search(SymTbl ^ local_symbols, Id)
    ).

find_existing_symbol(Id, SymTbl) = Sym :-
    (
        Id = id_global(Name),
        Sym-_Locn = map.lookup(SymTbl ^ global_symbols, Name)
    ;
        ( Id = id_scoped(_, _)
        ; Id = id_unset(_)
        ),
        Sym-_Locn = map.lookup(SymTbl ^ local_symbols, Id)
    ).

find_existing_global_symbol(Name, SymTbl) =
    find_existing_symbol(id_global(Name), SymTbl).

add_unseen_symbol(Id, Sym, Locn, !SymTbl) :-
    (
        Id = id_global(Name),
        map.det_insert(Name, Sym - Locn, !.SymTbl ^ global_symbols, Temp),
        !SymTbl ^ global_symbols := Temp
    ;
        ( Id = id_scoped(_, _)
        ; Id = id_unset(_)
        ),
        map.det_insert(Id, Sym-Locn, !.SymTbl ^ local_symbols, Temp),
        !SymTbl ^ local_symbols := Temp
    ).

replace_existing_symbol(Id, Sym, Locn, !SymTbl) :-
    (
        Id = id_global(Name),
        map.det_update(Name, Sym - Locn, !.SymTbl ^ global_symbols, Temp),
        !SymTbl ^ global_symbols := Temp
    ;
        ( Id = id_scoped(_, _)
        ; Id = id_unset(_)
        ),
        map.det_update(Id, Sym - Locn, !.SymTbl ^ local_symbols, Temp),
        !SymTbl ^ local_symbols := Temp
    ).

replace_existing_global_symbol(Name, Sym, Locn, !SymTbl) :-
    replace_existing_symbol(id_global(Name), Sym, Locn, !SymTbl).

%-----------------------------------------------------------------------------%

get_new_scope_number(NewScopeN, !SymTbl) :-
    counter.allocate(NewScopeN, !.SymTbl ^ scope_ctr, Temp),
    !SymTbl ^ scope_ctr := Temp.

%-----------------------------------------------------------------------------%
%
% Symbol stuff.
%

:- instance show(symbol) where [
    sym_variable(_,VarKind,_,_,_,_)^show = VarKind^show,
    sym_operation(OpKind,_)      ^show = OpKind^show,
    sym_annotation(_)            ^show = "annotation"
].

:- instance show(variable_kind) where [
    global_var         ^show = "variable",
    let_var            ^show = "let variable",
    generator_var      ^show = "generator variable",
    pred_arg           ^show = "predicate argument",
    func_arg           ^show = "function argument",
    ann_arg            ^show = "annotation argument"
].

:- instance show(operation_kind) where [
    predicate_operation^show = "predicate",
    function_operation ^show = "function",
    operator_operation ^show = "operator"
].

%-----------------------------------------------------------------------------%
%
% Printing, etc.
%

dump_symbol_table(SymTbl, !IO) :-
    % We don't just a straight dump, because that's too difficult to read.
    SymTbl = symbol_table(GSyms, LSyms, ScopeCtr),
    map.to_sorted_assoc_list(GSyms, SortedListGSymTbl),
    F = ( func(Name-SymAndLocn) = id_global(Name)-SymAndLocn ),
    SortedAssocListGSymTbl = map(F, SortedListGSymTbl),
    SortedAssocListSymTbl = SortedAssocListGSymTbl ++ SortedAssocListLSymTbl,
    map.to_sorted_assoc_list(LSyms, SortedAssocListLSymTbl),
    io.write_string("-- symbol table: symbols --\n  ", !IO),
    io.write_list(SortedAssocListSymTbl, "\n  ", write, !IO),
    io.nl(!IO),
    io.write_string("-- symbol table: next scope number --\n  ", !IO),
    counter.allocate(NextScopeN, ScopeCtr, _),
    io.write_int(NextScopeN, !IO),
    io.nl(!IO).

%-----------------------------------------------------------------------------%

foldl(P, SymTbl, !A) :-
    PName = (
        pred(Name::in, (Sym - Locn)::in, !.PA::in, !:PA::out) is det :-
            P(id_global(Name), Sym, Locn, !PA)
    ),
    PId = (
        pred(Id::in, (Sym - Locn)::in, !.PA::in, !:PA::out) is det :-
            P(Id, Sym, Locn, !PA)
    ),
    map.foldl(PName, SymTbl^global_symbols, !A),
    map.foldl(PId,   SymTbl^local_symbols,  !A).

%-----------------------------------------------------------------------------%
%
% Properties of types and type-insts.
%

ti_is_fixed(SymTbl, TI) :- ti_is_fixed_2(SymTbl, TI) = yes.

    % Implemented using a switch so we can't forget to consider any new cases
    % added to 'type_inst'.
:- func ti_is_fixed_2(symbol_table, type_inst) = bool.

ti_is_fixed_2(_,ti_par_bottom)      = yes.
ti_is_fixed_2(_,ti_var_bottom)      = no.
ti_is_fixed_2(_,ti_par_bool)        = yes.
ti_is_fixed_2(_,ti_var_bool)        = no.
ti_is_fixed_2(_,ti_par_int)         = yes.
ti_is_fixed_2(_,ti_var_int)         = no.
ti_is_fixed_2(_,ti_par_float)       = yes.
ti_is_fixed_2(_,ti_var_float)       = no.
ti_is_fixed_2(_,ti_par_string)      = yes.
ti_is_fixed_2(_,ti_ann)             = no.  % The 'ann' type could contain vars.
ti_is_fixed_2(_,ti_par_set(_))      = yes.
ti_is_fixed_2(_,ti_var_set(_))      = no.
ti_is_fixed_2(SymTbl, ti_array(_,TI))   = ti_is_fixed_2(SymTbl, TI).
ti_is_fixed_2(SymTbl, ti_tuple(TIs))    =
    bool.and_list(map(ti_is_fixed_2(SymTbl), TIs)).
ti_is_fixed_2(_,ti_par_variable(_,_)) = yes.
ti_is_fixed_2(_,ti_any_variable(_,_)) = no.
    % Nb: the 'ti_top' case can occur if a non-flat enum containing var
    % arguments is parified, ie. because of a (type-invalid) call to 'fix'.
ti_is_fixed_2(_,ti_top)             = no.
ti_is_fixed_2(_,ti_error)           = yes.
ti_is_fixed_2(_,TI)                 = _ :-
    TI = ti_unknown,
    unexpected($file, $pred, TI^string).
            
%-----------------------------------------------------------------------------%

parify_type_inst(_,ti_par_bottom ) = ti_par_bottom.
parify_type_inst(_,ti_var_bottom ) = ti_par_bottom.
parify_type_inst(_,ti_par_bool   ) = ti_par_bool.
parify_type_inst(_,ti_var_bool   ) = ti_par_bool.
parify_type_inst(_,ti_par_int    ) = ti_par_int.
parify_type_inst(_,ti_var_int    ) = ti_par_int.
parify_type_inst(_,ti_par_float  ) = ti_par_float.
parify_type_inst(_,ti_var_float  ) = ti_par_float.
parify_type_inst(_,ti_par_string ) = ti_par_string.
parify_type_inst(_,ti_ann        ) = ti_top.
parify_type_inst(_,ti_par_set(TI)) = ti_par_set(TI).
parify_type_inst(_,ti_var_set(TI)) = ti_par_set(TI).
parify_type_inst(SymTbl, ti_array(I,V) ) = ti_array(I2, V2) :-
    I2 = parify_type_inst(SymTbl, I),
    V2 = parify_type_inst(SymTbl, V).
parify_type_inst(SymTbl, ti_tuple(TIs)) =
    ti_tuple(map(parify_type_inst(SymTbl), TIs)).
parify_type_inst(_,ti_par_variable(Tv,Sk)) = ti_par_variable(Tv,Sk).
parify_type_inst(_,ti_any_variable(Tv,Sk)) = ti_par_variable(Tv,Sk).
parify_type_inst(_,ti_top             ) = ti_top.
parify_type_inst(_,ti_error           ) = ti_error.
parify_type_inst(_,ti_unknown) = _ :-
    unexpected($file, $pred, "unknown type-inst").

%-----------------------------------------------------------------------------%
:- end_module symbol_table.
%-----------------------------------------------------------------------------%
