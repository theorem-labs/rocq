(* coqc's own commands refuse a name that holds a line break, but
   [Id.of_string_soft] accepts it. The declarations below stand for a library
   crafted to forge a line of rocqchk's output. *)

open Names

let with_line_break before after =
  Id.of_string_soft (Id.to_string before ^ "\n" ^ Id.to_string after)

let declare_axiom before after =
  let entry = Declare.ParameterEntry (Declare.parameter_entry Constr.mkSet) in
  let _ : Constant.t =
    Declare.declare_constant ~name:(with_line_break before after)
      ~kind:Decls.(IsAssumption Logical) entry
  in
  ()

let declare_block inds =
  let mie = {
    Entries.mind_entry_record = None;
    mind_entry_finite = Declarations.Finite;
    mind_entry_params = [];
    mind_entry_inds = inds;
    mind_entry_universes = Entries.Monomorphic_ind_entry;
    mind_entry_variance = None;
    mind_entry_private = None;
  } in
  let univs = UState.Monomorphic_entry Univ.ContextSet.empty, UnivNames.empty_binders in
  let _ : MutInd.t = DeclareInd.declare_mutual_inductive_with_eliminations mie univs [] in
  ()

let packet typename consname self = {
  Entries.mind_entry_typename = typename;
  mind_entry_arity = Constr.mkSet;
  mind_entry_consnames = [consname];
  mind_entry_lc = [Constr.mkRel self];
}

let declare_inductive first before after =
  let consname id = Id.of_string (Id.to_string id ^ "_c") in
  (* In a constructor's type, the last type of the block is [Rel 1]. *)
  declare_block [
    packet first (consname first) 2;
    packet (with_line_break before after) (consname before) 1;
  ]

let declare_constructor typename before after =
  declare_block [packet typename (with_line_break before after) 1]

(* A module type [name]: a functor of one parameter of the module type [ty],
   whose body is [ty]. Its parameter is made here rather than by coqc, which
   takes the library's path and a checked identifier: with [bad_path], the
   path is BadNames then [before], a line break, [after], and the identifier
   is X; otherwise the path is the library's and the identifier is [before],
   a line break, [after]. The module type is added to the kernel only. *)
let declare_bad_parameter ~bad_path name ty before after =
  let mp_ty = Nametab.locate_modtype (Libnames.qualid_of_ident ty) in
  let mbid =
    if bad_path then
      MBId.make (DirPath.make [with_line_break before after; Id.of_string "BadNames"])
        (Id.of_string "X")
    else MBId.make (Lib.library_dp ()) (with_line_break before after)
  in
  let inl : Declarations.inline = None in
  let _ : ModPath.t =
    Global.add_modtype name
      ([mbid, Declarations.MEident mp_ty, inl], Declarations.MEident mp_ty) inl
  in
  ()
