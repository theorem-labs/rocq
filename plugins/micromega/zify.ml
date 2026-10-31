(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Names
open Pp
open Lazy
module NamedDecl = Context.Named.Declaration

module ERelevance = EConstr.ERelevance

let debug_zify_flag, debug_zify = CDebug.create_full ~name:"zify" ()

(* The following [constr] are necessary for constructing the proof terms *)

let zify str =
  EConstr.of_constr
    (UnivGen.constr_of_monomorphic_global (Global.env ())
       (Rocqlib.lib_ref ("ZifyClasses." ^ str)))

(** classes *)
let rocq_InjTyp = lazy (Rocqlib.lib_ref "ZifyClasses.InjTyp")

let rocq_BinOp = lazy (Rocqlib.lib_ref "ZifyClasses.BinOp")
let rocq_UnOp = lazy (Rocqlib.lib_ref "ZifyClasses.UnOp")
let rocq_CstOp = lazy (Rocqlib.lib_ref "ZifyClasses.CstOp")
let rocq_BinRel = lazy (Rocqlib.lib_ref "ZifyClasses.BinRel")
let rocq_PropBinOp = lazy (Rocqlib.lib_ref "ZifyClasses.PropBinOp")
let rocq_PropUOp = lazy (Rocqlib.lib_ref "ZifyClasses.PropUOp")
let rocq_BinOpSpec = lazy (Rocqlib.lib_ref "ZifyClasses.BinOpSpec")
let rocq_UnOpSpec = lazy (Rocqlib.lib_ref "ZifyClasses.UnOpSpec")
let rocq_Saturate = lazy (Rocqlib.lib_ref "ZifyClasses.Saturate")

(* morphism like lemma *)

let mkapp2 = lazy (zify "mkapp2")
let mkapp = lazy (zify "mkapp")
let eq_refl = lazy (zify "eq_refl")
let eq = lazy (zify "eq")
let mkrel = lazy (zify "mkrel")
let iff_refl = lazy (zify "iff_refl")
let eq_iff = lazy (zify "eq_iff")
let rew_iff = lazy (zify "rew_iff")
let rew_iff_rev = lazy (zify "rew_iff_rev")

(* propositional logic *)

let op_and = lazy (zify "and")
let op_and_morph = lazy (zify "and_morph")
let op_or = lazy (zify "or")
let op_or_morph = lazy (zify "or_morph")
let op_impl_morph = lazy (zify "impl_morph")
let op_iff = lazy (zify "iff")
let op_iff_morph = lazy (zify "iff_morph")
let op_not = lazy (zify "not")
let op_not_morph = lazy (zify "not_morph")
let op_True = lazy (zify "True")
let op_I = lazy (zify "I")

(** [unsafe_to_constr c] returns a [Constr.t] without considering an evar_map.
    This is useful for calling Constr.hash *)
let unsafe_to_constr = EConstr.Unsafe.to_constr

let pr_constr env evd e = Printer.pr_econstr_env env evd e

let gl_pr_constr e =
  let genv = Global.env () in
  let evd = Evd.from_env genv in
  pr_constr genv evd e

let whd = Reductionops.clos_whd_flags RedFlags.all
let is_convertible env evd t1 t2 = Reductionops.(is_conv env evd t1 t2)

(** [get_type_of] performs beta reduction ;
    Is it ok for Retyping.get_type_of (Zpower_nat n q) to return (fun _ : nat => Z) q ? *)
let get_type_of env evd e =
  Tacred.cbv_beta env evd (Retyping.get_type_of env evd e)

(* arguments are dealt with in a second step *)

let rec find_option pred l =
  match l with
  | [] -> raise Not_found
  | e :: l -> ( match pred e with Some r -> r | None -> find_option pred l )

module ConstrMap = struct
  open Names.GlobRef

  type 'a t = 'a list Map.t

  let add gr e m =
    Map.update gr (function None -> Some [e] | Some l -> Some (e :: l)) m

  let empty = Map.empty

  let find evd h m =
    match Map.find (fst (EConstr.destRef evd h)) m with
    | e :: _ -> e
    | [] -> assert false

  let find_all evd h m = Map.find (fst (EConstr.destRef evd h)) m

  (** [mem c m]: [m] has an entry for the head [c], a constant, inductive type or constructor. *)
  let mem c m = Map.mem (fst (Constr.destRef c)) m

  let fold f m acc =
    Map.fold
      (fun k l acc -> List.fold_left (fun acc e -> f k e acc) acc l)
      m acc
end

module HConstr = struct
  module M = Map.Make (struct
    type t = EConstr.t

    let compare c c' = Constr.compare (unsafe_to_constr c) (unsafe_to_constr c')
  end)

  type 'a t = 'a M.t

  let add h e m = M.add h e m
  let empty = M.empty
  let find = M.find
end

(** [get_projections_from_constant (evd,c) ]
    returns an array of constr [| a1,.. an|] such that [c] is defined as
    Definition c := mk a1 .. an with mk a constructor.
    ai is therefore either a type parameter or a projection.
 *)

let get_projections_from_constant (evd, i) =
  match EConstr.kind evd (whd (Global.env ()) evd i) with
  | App (c, a) -> a
  | _ ->
    raise
      (CErrors.user_err
         Pp.(
           str "The hnf of term "
           ++ pr_constr (Global.env ()) evd i
           ++ str " should be an application i.e. (c a1 ... an)"))

(**  An instance of type, say T, is registered into a hashtable, say TableT. *)

type 'a decl =
  { decl : EConstr.t
  ; (* Registered type instance *)
    deriv : 'a (* Projections of insterest *) }

module EInjT = struct
  type t =
    { isid : bool
    ; (* S = T ->  inj = fun x -> x*)
      source : EConstr.t
    ; (* S *)
      target : EConstr.t
    ; (* T *)
      (* projections *)
      inj : EConstr.t
    ; (* S -> T *)
      pred : EConstr.t
    ; (* T -> Prop *)
      cstr : EConstr.t option (* forall x, pred (inj x) *) }

  let eq_inj evd i1 i2 =
    i1.isid = i2.isid && EConstr.eq_constr evd i1.inj i2.inj


end

(** [classify_op] classify injected operators and detect special cases. *)

type classify_op =
  | OpInj (* e.g. Z.of_nat ->  \x.x *)
  | OpSame (* e.g. Z.add -> Z.add *)
  | OpConv (* e.g. Pos.ge     == \x.y. Z.ge (Z.pos x) (Z.pos y)
                     \x.y. Z.pos (Pos.add x y) == \x.y. Z.add (Z.pos x) (Z.pos y)
                     Z.succ              == (\x.x + 1)
           *)
  | OpOther

(*let pp_classify_op = function
  | OpInj -> Pp.str "Identity"
  | OpSame -> Pp.str "Same"
  | OpConv -> Pp.str "Conv"
  | OpOther -> Pp.str "Other"
 *)

let name x =
  Context.make_annot (Name.mk_name (Names.Id.of_string x)) ERelevance.relevant

let mkconvert_unop i1 i2 op top =
  (* fun x => inj (op x) *)
  let op =
    EConstr.mkLambda
      ( name "x"
      , i1.EInjT.source
      , EConstr.mkApp (i2.EInjT.inj, [|EConstr.mkApp (op, [|EConstr.mkRel 1|])|])
      )
  in
  (* fun x => top (inj x) *)
  let top =
    EConstr.mkLambda
      ( name "x"
      , i1.EInjT.source
      , EConstr.mkApp
          (top, [|EConstr.mkApp (i1.EInjT.inj, [|EConstr.mkRel 1|])|]) )
  in
  (op, top)

let mkconvert_binop i1 i2 i3 op top =
  (* fun x y => inj (op x y) *)
  let op =
    EConstr.mkLambda
      ( name "x"
      , i1.EInjT.source
      , EConstr.mkLambda
          ( name "y"
          , i1.EInjT.source
          , EConstr.mkApp
              ( i3.EInjT.inj
              , [|EConstr.mkApp (op, [|EConstr.mkRel 2; EConstr.mkRel 1|])|] )
          ) )
  in
  (* fun x y => top (inj x) (inj y) *)
  let top =
    EConstr.mkLambda
      ( name "x"
      , i1.EInjT.source
      , EConstr.mkLambda
          ( name "y"
          , i2.EInjT.source
          , EConstr.mkApp
              ( top
              , [| EConstr.mkApp (i1.EInjT.inj, [|EConstr.mkRel 2|])
                 ; EConstr.mkApp (i2.EInjT.inj, [|EConstr.mkRel 1|]) |] ) ) )
  in
  (op, top)

let mkconvert_rel i r tr =
  let tr =
    EConstr.mkLambda
      ( name "x"
      , i.EInjT.source
      , EConstr.mkLambda
          ( name "y"
          , i.EInjT.source
          , EConstr.mkApp
              ( tr
              , [| EConstr.mkApp (i.EInjT.inj, [|EConstr.mkRel 2|])
                 ; EConstr.mkApp (i.EInjT.inj, [|EConstr.mkRel 1|]) |] ) ) )
  in
  (r, tr)

(** [classify_op mkconvert op top] takes the injection [inj] for the origin operator [op]
    and the destination operator [top] -- both [op] and [top] are closed terms *)
let classify_op mkconvert inj op top =
  let env = Global.env () in
  let evd = Evd.from_env env in
  if is_convertible env evd inj op then OpInj
  else if EConstr.eq_constr evd op top then OpSame
  else
    let op, top = mkconvert op top in
    if is_convertible env evd op top then OpConv else OpOther

(*let classify_op mkconvert tysrc op top =
  let res = classify_op mkconvert tysrc op top in
  Feedback.msg_debug
    Pp.(
      str "classify_op:" ++ gl_pr_constr op ++ str " " ++ gl_pr_constr top
      ++ str "  " ++ pp_classify_op res ++ fnl ());
  res
 *)
module EBinOpT = struct
  type t =
    { (* Op : source1 -> source2 -> source3 *)
      source1 : EConstr.t
    ; source2 : EConstr.t
    ; source3 : EConstr.t
    ; target1 : EConstr.t
    ; target2 : EConstr.t
    ; target3 : EConstr.t
    ; inj1 : EInjT.t (* InjTyp source1 target1 *)
    ; inj2 : EInjT.t (* InjTyp source2 target2 *)
    ; inj3 : EInjT.t (* InjTyp source3 target3 *)
    ; bop : EConstr.t (* BOP *)
    ; tbop : EConstr.t (* TBOP *)
    ; tbopinj : EConstr.t (* TBOpInj *)
    ; classify_binop : classify_op }
end

module ECstOpT = struct
  type t =
    { source : EConstr.t
    ; target : EConstr.t
    ; inj : EInjT.t
    ; cst : EConstr.t
    ; cstinj : EConstr.t
    ; is_construct : bool }
end

module EUnOpT = struct
  type t =
    { source1 : EConstr.t
    ; source2 : EConstr.t
    ; target1 : EConstr.t
    ; target2 : EConstr.t
    ; uop : EConstr.t
    ; inj1_t : EInjT.t
    ; inj2_t : EInjT.t
    ; tuop : EConstr.t
    ; tuopinj : EConstr.t
    ; classify_unop : classify_op
    ; is_construct : bool }
end

module EBinRelT = struct
  type t =
    { source : EConstr.t
    ; target : EConstr.t
    ; inj : EInjT.t
    ; brel : EConstr.t
    ; tbrel : EConstr.t
    ; brelinj : EConstr.t
    ; classify_rel : classify_op }
end

module EPropBinOpT = struct
  type t = {op : EConstr.t; op_iff : EConstr.t}
end

module EPropUnOpT = struct
  type t = {op : EConstr.t; op_iff : EConstr.t}
end

module ESatT = struct
  type t = {parg1 : EConstr.t; parg2 : EConstr.t; satOK : EConstr.t}
end

module ESpecT = struct
  type t = {spec : EConstr.t}
end

(* Different type of declarations *)
type decl_kind =
  | PropOp of EPropBinOpT.t decl
  | PropUnOp of EPropUnOpT.t decl
  | InjTyp of EInjT.t decl
  | BinRel of EBinRelT.t decl
  | BinOp of EBinOpT.t decl
  | UnOp of EUnOpT.t decl
  | CstOp of ECstOpT.t decl
  | Saturate of ESatT.t decl
  | UnOpSpec of ESpecT.t decl
  | BinOpSpec of ESpecT.t decl

let target_inj d =
  match d with
  | BinOp d -> Some d.deriv.EBinOpT.inj3
  | UnOp d  -> Some d.deriv.EUnOpT.inj2_t
  | CstOp d -> Some d.deriv.inj
  |  _      -> None

type term_kind = Application of EConstr.constr | OtherTerm of EConstr.constr

module type Elt = sig
  type elt

  (** name *)
  val name : string

  val gref : GlobRef.t Lazy.t
  val table : (term_kind * decl_kind) ConstrMap.t ref
  val cast : elt decl -> decl_kind
  val dest : decl_kind -> elt decl option

  (** [get_key] is the type-index used as key for the instance *)
  val get_key : int

  (** [mk_elt evd i [a0,..,an]]  returns the element of the table
        built from the type-instance i and the arguments (type indexes and projections)
        of the type-class constructor. *)
  val mk_elt : Evd.evar_map -> EConstr.t -> EConstr.t array -> elt

  (*  val arity : int*)
end

let table = Summary.ref ~name:"zify_table" ConstrMap.empty
let saturate = Summary.ref ~name:"zify_saturate" ConstrMap.empty
let specs = Summary.ref ~name:"zify_specs" ConstrMap.empty
let table_cache = ref ConstrMap.empty
let saturate_cache = ref ConstrMap.empty
let specs_cache = ref ConstrMap.empty

(* BET-84 census row 15: the three registration tables, each read whole
   under its Summary name before [init_cache] copies it. ONE value function,
   called by the record site and by the replay evaluator
   (dev/tools/census/replay_channels.py). *)
let recorded_zify_table name =
  let tbl = match name with
    | "zify_table" -> Some !table
    | "zify_saturate" -> Some !saturate
    | "zify_specs" -> Some !specs
    | _ -> None
  in
  Option.map (fun t -> Proof_recorder.digest_cached ~what:"zify_table" t) tbl

(* A key that names none of the three tables is a miss. *)
let () =
  Proof_replay.register_evaluator "zify_table" (fun key ->
      match recorded_zify_table key with
      | Some _ as v -> Proof_replay.Value v
      | None -> Proof_replay.Unknown)

let record_cache name =
  if Proof_recorder.active () then
    Proof_recorder.read ~row:"15" ~channel:"zify_table" ~key:(fun () -> name)
      ~value:(fun () -> recorded_zify_table name)

(** Each type-class gives rise to a different table.
    They only differ on how projections are extracted.  *)

module EInj = struct
  open EInjT

  type elt = EInjT.t

  let name = "EInj"
  let gref = rocq_InjTyp
  let table = table
  let cast x = InjTyp x
  let dest = function InjTyp x -> Some x | _ -> None

  let is_cstr_true evd c =
    match EConstr.kind evd c with
    | Lambda (_, _, c) -> EConstr.eq_constr_nounivs evd c (Lazy.force op_True)
    | _ -> false

  let mk_elt evd i (a : EConstr.t array) =
    let isid = EConstr.eq_constr_nounivs evd a.(0) a.(1) in
    { isid
    ; source = a.(0)
    ; target = a.(1)
    ; inj = a.(2)
    ; pred = a.(3)
    ; cstr = (if is_cstr_true evd a.(3) then None else Some a.(4)) }

  let get_key = 0
end

let get_inj evd c =
  let a = get_projections_from_constant (evd, c) in
  EInj.mk_elt evd c a

let rec decomp_type evd ty =
  match EConstr.kind_of_type evd ty with
  | EConstr.ProdType (_, t1, rst) -> t1 :: decomp_type evd rst
  | _ -> [ty]

let pp_type env evd l =
  Pp.prlist_with_sep (fun _ -> Pp.str " -> ") (pr_constr env evd) l

let check_typ evd expty op =
  let env = Global.env () in
  let ty = Retyping.get_type_of env evd op in
  let ty = decomp_type evd ty in
  if List.for_all2 (EConstr.eq_constr_nounivs evd) ty expty then ()
  else
    raise
      (CErrors.user_err
         Pp.(
           str ": Cannot register operator "
           ++ pr_constr env evd op ++ str ". It has type " ++ pp_type env evd ty
           ++ str " instead of expected type "
           ++ pp_type env evd expty))

module EBinOp = struct
  type elt = EBinOpT.t

  open EBinOpT

  let name = "BinOp"
  let gref = rocq_BinOp
  let table = table

  let mk_elt evd i a =
    let i1 = get_inj evd a.(7) in
    let i2 = get_inj evd a.(8) in
    let i3 = get_inj evd a.(9) in
    let bop = a.(6) in
    let tbop = a.(10) in
    check_typ evd EInjT.[i1.source; i2.source; i3.source] bop;
    { source1 = a.(0)
    ; source2 = a.(1)
    ; source3 = a.(2)
    ; target1 = a.(3)
    ; target2 = a.(4)
    ; target3 = a.(5)
    ; inj1 = i1
    ; inj2 = i2
    ; inj3 = i3
    ; bop
    ; tbop
    ; tbopinj = a.(11)
    ; classify_binop =
        classify_op (mkconvert_binop i1 i2 i3) i3.EInjT.inj a.(6) tbop }

  let get_key = 6
  let cast x = BinOp x
  let dest = function BinOp x -> Some x | _ -> None
end

(*let debug_term msg c =
  let genv = Global.env () in
  Feedback.msg_debug
    Pp.(str msg ++ str " " ++ pr_constr genv (Evd.from_env genv) c);
  c
 *)
module ECstOp = struct
  type elt = ECstOpT.t

  open ECstOpT

  let name = "CstOp"
  let gref = rocq_CstOp
  let table = table
  let cast x = CstOp x
  let dest = function CstOp x -> Some x | _ -> None

  let isConstruct evd c =
    match EConstr.kind evd c with
    | Construct _ | Int _ | Float _ -> true
    | _ -> false

  let mk_elt evd i a =
    { source = a.(0)
    ; target = a.(1)
    ; inj = get_inj evd a.(3)
    ; cst = a.(4)
    ; cstinj = a.(5)
    ; is_construct = isConstruct evd a.(2) }

  let get_key = 2
end

module EUnOp = struct
  type elt = EUnOpT.t

  open EUnOpT

  let name = "UnOp"
  let gref = rocq_UnOp
  let table = table
  let cast x = UnOp x
  let dest = function UnOp x -> Some x | _ -> None

  let mk_elt evd i a =
    let i1 = get_inj evd a.(5) in
    let i2 = get_inj evd a.(6) in
    let uop = a.(4) in
    check_typ evd EInjT.[i1.source; i2.source] uop;
    let tuop = a.(7) in
    { source1 = a.(0)
    ; source2 = a.(1)
    ; target1 = a.(2)
    ; target2 = a.(3)
    ; uop
    ; inj1_t = i1
    ; inj2_t = i2
    ; tuop
    ; tuopinj = a.(8)
    ; is_construct = EConstr.isConstruct evd uop
    ; classify_unop = classify_op (mkconvert_unop i1 i2) i2.EInjT.inj uop tuop
    }

  let get_key = 4
end

module EBinRel = struct
  type elt = EBinRelT.t

  open EBinRelT

  let name = "BinRel"
  let gref = rocq_BinRel
  let table = table
  let cast x = BinRel x
  let dest = function BinRel x -> Some x | _ -> None

  let mk_elt evd i a =
    let i = get_inj evd a.(3) in
    let brel = a.(2) in
    let tbrel = a.(4) in
    check_typ evd EInjT.[i.source; i.source; EConstr.mkProp] brel;
    { source = a.(0)
    ; target = a.(1)
    ; inj = get_inj evd a.(3)
    ; brel
    ; tbrel
    ; brelinj = a.(5)
    ; classify_rel = classify_op (mkconvert_rel i) i.EInjT.inj brel tbrel }

  let get_key = 2
end

module EPropBinOp = struct
  type elt = EPropBinOpT.t

  open EPropBinOpT

  let name = "PropBinOp"
  let gref = rocq_PropBinOp
  let table = table
  let cast x = PropOp x
  let dest = function PropOp x -> Some x | _ -> None
  let mk_elt evd i a = {op = a.(0); op_iff = a.(1)}
  let get_key = 0
end

module EPropUnOp = struct
  type elt = EPropUnOpT.t

  open EPropUnOpT

  let name = "PropUOp"
  let gref = rocq_PropUOp
  let table = table
  let cast x = PropUnOp x
  let dest = function PropUnOp x -> Some x | _ -> None
  let mk_elt evd i a = {op = a.(0); op_iff = a.(1)}
  let get_key = 0
end

let constr_of_term_kind = function Application c -> c | OtherTerm c -> c

let zify_register_locality =
  let open Attributes.Notations in
  Attributes.explicit_hint_locality >>= function
  | Some v ->
    let () = Locality.check_locality_nodischarge v in
    return v
  | None -> return (if Lib.sections_are_opened () then Hints.Local else Hints.SuperGlobal)

module type S = sig
  val register : Hints.hint_locality -> Libnames.qualid -> unit
  val print : unit -> unit
end

module MakeTable (E : Elt) : S = struct
  (** Given a term [c] and its arguments ai,
        we construct a HConstr.t table that is
        indexed by ai for i = E.get_key.
        The elements of the table are built using E.mk_elt c [|a0,..,an|]
     *)

  let make_elt (evd, i) =
    let a = get_projections_from_constant (evd, i) in
    E.mk_elt evd i a

  let safe_ref evd c =
    try
      fst (EConstr.destRef evd c)
    with DestKO -> CErrors.user_err Pp.(str "Add Zify "++str E.name ++ str ": the term "++
                                          gl_pr_constr c ++ str " should be a global reference")

  let register_hint evd t elt =
    match EConstr.kind evd t with
    | App (c, _) ->
       let gr = safe_ref evd c in
       E.table := ConstrMap.add gr (Application t, E.cast elt) !E.table
    | _ ->
       let gr = safe_ref evd t in
       E.table := ConstrMap.add gr (OtherTerm t, E.cast elt) !E.table

  let register_constr env evd c =
    let c = EConstr.of_constr c in
    let t = get_type_of env evd c in
    match EConstr.kind evd t with
    | App (intyp, args) when EConstr.isRefX env evd (Lazy.force E.gref) intyp ->
      let styp = args.(E.get_key) in
      let elt = {decl = c; deriv = make_elt (evd, c)} in
      register_hint evd styp elt
    | _ ->
      let env = Global.env () in
      raise
        (CErrors.user_err
           Pp.(
             str "Cannot register " ++ pr_constr env evd c
             ++ str ". It has type " ++ pr_constr env evd t
             ++ str " instead of type "
             ++ Printer.pr_global (Lazy.force E.gref)
             ++ str " X1 ... Xn"))

  let register_obj : Libobject.locality * Constr.constr -> Libobject.obj =
    let cache_constr c =
      let env = Global.env () in
      let evd = Evd.from_env env in
      register_constr env evd c
    in
    let subst_constr (subst, c) = Mod_subst.subst_mps subst c in
    (* Interface key: payload is a locality and a kernel term, no location. *)
    Libobject.declare_object
      { (Libobject.object_with_locality
           ("register-zify-" ^ E.name)
           ~cache:cache_constr ~subst:(Some subst_constr)
           ~discharge:(fun _ -> assert false))
        with Libobject.interface_key = Libobject.Key_as_is }

  (** [register c] is called from the VERNACULAR ADD [name] reference(t).
       The term [c] is interpreted and
       registered as a [superglobal_object_nodischarge].
       TODO: pre-compute [get_type_of] - [cache_constr] is using another environment.
     *)
  let register local c =
    try
      let c = UnivGen.constr_of_monomorphic_global (Global.env ()) (Nametab.locate c) in
      let _ = Lib.add_leaf (register_obj (local,c)) in
      ()
    with Not_found ->
      raise
        (CErrors.user_err Pp.(Libnames.pr_qualid c ++ str " does not exist."))

  let pp_keys () =
    let env = Global.env () in
    let evd = Evd.from_env env in
    ConstrMap.fold
      (fun _ (k, d) acc ->
        match E.dest d with
        | None -> acc
        | Some _ ->
          Pp.(pr_constr env evd (constr_of_term_kind k) ++ str " " ++ acc))
      !E.table (Pp.str "")

  let print () = Feedback.msg_info (pp_keys ())
end

module InjTable = MakeTable (EInj)

module ESat = struct
  type elt = ESatT.t

  open ESatT

  let name = "Saturate"
  let gref = rocq_Saturate
  let table = saturate
  let cast x = Saturate x
  let dest = function Saturate x -> Some x | _ -> None
  let mk_elt evd i a = {parg1 = a.(2); parg2 = a.(3); satOK = a.(5)}
  let get_key = 1
end

module EUnopSpec = struct
  open ESpecT

  type elt = ESpecT.t

  let name = "UnopSpec"
  let gref = rocq_UnOpSpec
  let table = specs
  let cast x = UnOpSpec x
  let dest = function UnOpSpec x -> Some x | _ -> None
  let mk_elt evd i a = {spec = a.(4)}
  let get_key = 2
end

module EBinOpSpec = struct
  open ESpecT

  type elt = ESpecT.t

  let name = "BinOpSpec"
  let gref = rocq_BinOpSpec
  let table = specs
  let cast x = BinOpSpec x
  let dest = function BinOpSpec x -> Some x | _ -> None
  let mk_elt evd i a = {spec = a.(5)}
  let get_key = 3
end

module BinOp = MakeTable (EBinOp)
module UnOp = MakeTable (EUnOp)
module CstOp = MakeTable (ECstOp)
module BinRel = MakeTable (EBinRel)
module PropBinOp = MakeTable (EPropBinOp)
module PropUnOp = MakeTable (EPropUnOp)
module Saturate = MakeTable (ESat)
module UnOpSpec = MakeTable (EUnopSpec)
module BinOpSpec = MakeTable (EBinOpSpec)

let init_cache () =
  record_cache "zify_table";
  record_cache "zify_saturate";
  record_cache "zify_specs";
  table_cache := !table;
  saturate_cache := !saturate;
  specs_cache := !specs

open EInjT

(** Get constr of lemma and projections in ZifyClasses. *)

(** [Effects] logs the effects of a translation, so that [TypeMemo] can replay them when it reuses
    the translation: the [CstrTable] registrations and the [Typing.checked_appvect] calls that
    thread the evar map, in order. *)
module Effects = struct
  type t =
    | Register of EConstr.t * EConstr.t
    | Checked_appvect of EConstr.t * EConstr.t array

  let log : t list ref option ref = ref None
  let add e = match !log with None -> () | Some r -> r := e :: !r

  (** [record f] runs [f ()] and returns its result with the effects it had, in order. The
      translation that [f] runs does not use the memo, so [record] is never nested. *)
  let record f =
    let r = ref [] in
    log := Some r;
    let v = Fun.protect ~finally:(fun () -> log := None) f in
    (v, List.rev !r)
end

(** Every [Typing.checked_appvect] threads the evar map, so it is logged in [Effects]. *)
module Typing = struct
  include Typing

  let checked_appvect env evd f args =
    Effects.add (Effects.Checked_appvect (f, args));
    checked_appvect env evd f args
end

(** Module [CstrTable] records terms  [x] injected into [inj x]
    together with the corresponding type constraint.
    The terms are stored by side-effect during the traversal
    of the goal. It must therefore be cleared before calling
    the main tactic.
 *)

module CstrTable = struct
  module HConstr = Hashtbl.Make (struct
    type t = EConstr.t

    let hash c = Constr.hash (unsafe_to_constr c)
    let equal c c' = Constr.equal (unsafe_to_constr c) (unsafe_to_constr c')
  end)

  let table : EConstr.t HConstr.t = HConstr.create 10

  let register evd t (i : EConstr.t) =
    HConstr.add table t i;
    Effects.add (Effects.Register (t, i))

  let get () =
    let l = HConstr.fold (fun k i acc -> (k, i) :: acc) table [] in
    HConstr.clear table; l

  (** [gen_cstr table] asserts (cstr k) for each element of the table (k,cstr).
        NB: the constraint is only asserted if it does not already exist in the context.
        With an empty table there is nothing to assert, and the hypothesis table is not built.
     *)
  let gen_cstr table =
    match table with [] -> Proofview.tclUNIT () | _ :: _ ->
    Proofview.Goal.enter (fun gl ->
        let env = Proofview.Goal.env gl in
        let evd = Proofview.Goal.sigma gl in
        (* Build the table of existing hypotheses *)
        let has_hyp =
          let hyps_table = HConstr.create 20 in
          let () = List.iter
            (fun decl -> HConstr.add hyps_table (NamedDecl.get_type decl) ())
            (EConstr.named_context env)
          in
          fun c ->
            let m = HConstr.mem hyps_table c in
            if not m then HConstr.add hyps_table c ();
            m
        in
        (* Add the constraint (cstr k) if it is not already present *)
        let gen k cstr =
          Proofview.Goal.enter (fun gl ->
              let env = Proofview.Goal.env gl in
              let term = EConstr.mkApp (cstr, [|k|]) in
              let types = get_type_of env evd term in
              if has_hyp types then Tacticals.tclIDTAC
              else
                let n =
                  Tactics.fresh_id_in_env Id.Set.empty
                    (Names.Id.of_string "cstr")
                    env
                in
                Tactics.pose_proof (Names.Name n) term)
        in
        List.fold_left
          (fun acc (k, i) -> Tacticals.tclTHEN (gen k i) acc)
          Tacticals.tclIDTAC table)
end

let eq_annot = Context.eq_annot Name.equal Sorts.relevance_equal
let eq_mind m1 m2 = MutInd.UserOrd.equal m1 m2 && MutInd.CanOrd.equal m1 m2

(** Syntactic equality of two terms: the same constructors, the same binder names and relevances,
    the same casts, the same constant and inductive names (user and canonical) and the same
    universe instances. False on the constructors that [TypeMemo.scan] and
    [ComputeMemo.check_cacheable] reject, so two terms that hold one of them are never equal, not
    even to themselves. *)
let rec exact_eq c1 c2 =
  c1 == c2
  ||
  match (Constr.kind c1, Constr.kind c2) with
  | Rel n1, Rel n2 -> Int.equal n1 n2
  | Var i1, Var i2 -> Id.equal i1 i2
  | Sort s1, Sort s2 -> Sorts.equal s1 s2
  | Cast (c1, k1, t1), Cast (c2, k2, t2) -> k1 == k2 && exact_eq c1 c2 && exact_eq t1 t2
  | Prod (n1, t1, b1), Prod (n2, t2, b2) -> eq_annot n1 n2 && exact_eq t1 t2 && exact_eq b1 b2
  | Lambda (n1, t1, b1), Lambda (n2, t2, b2) ->
    eq_annot n1 n2 && exact_eq t1 t2 && exact_eq b1 b2
  | LetIn (n1, v1, t1, b1), LetIn (n2, v2, t2, b2) ->
    eq_annot n1 n2 && exact_eq v1 v2 && exact_eq t1 t2 && exact_eq b1 b2
  | App (f1, a1), App (f2, a2) ->
    Int.equal (Array.length a1) (Array.length a2) && exact_eq f1 f2 && Array.for_all2 exact_eq a1 a2
  | Const (k1, u1), Const (k2, u2) ->
    Constant.UserOrd.equal k1 k2 && Constant.CanOrd.equal k1 k2 && UVars.Instance.equal u1 u2
  | Ind ((m1, i1), u1), Ind ((m2, i2), u2) ->
    Int.equal i1 i2 && eq_mind m1 m2 && UVars.Instance.equal u1 u2
  | Construct (((m1, i1), j1), u1), Construct (((m2, i2), j2), u2) ->
    Int.equal i1 i2 && Int.equal j1 j2 && eq_mind m1 m2 && UVars.Instance.equal u1 u2
  | Int i1, Int i2 -> Uint63.equal i1 i2
  | String s1, String s2 -> Pstring.equal s1 s2
  | _ -> false

(** [ComputeMemo.compute evd t] is [Tacred.compute (Global.env ()) evd t], memoised on [t].

    The injection reduces the term it injects, and a proof script's lia calls inject the same
    terms over and over: on speed lane R2's RtLgTopA the two call sites ([interp_prf] on a term
    built from constructors, [conv_of_term] on an operator applied to an argument) reduced
    123,406 terms, 46 of them distinct (dispatch://INFRA-217).

    Why a reused result is the reduction's. [Tacred.compute] is call by value with every flag
    ([RedFlags.all], whose transparency state is full): it reads the term and, of the environment,
    the bodies of the constants and of the section variables and the inductive declarations; only
    an opaque body stops its delta steps, and that is in the environment too. It is a reduction,
    not a conversion: it asks the universe graph nothing, and the universe instance of a constant
    it unfolds is the term's own. It reads the evar map to expand the evars of the term
    ([EConstr.kind]) and to find the body of a constant that is not in the environment: a private
    constant of [abstract], held by the evar map's side effects ([EConstr.constant_value_in],
    [Evd.lookup_constant]). So on a term with no evar, no meta and no constant outside the global
    environment it is a function of the term and the global environment. [check_cacheable] rejects
    a term with an evar, a meta, a constant outside [Global.env ()] or any constructor that
    [exact_eq] does not compare, and the memo empties itself when the global environment is no
    longer physically the one of its entries ([validate]). The result is then the one this very
    reduction returned for a term that [exact_eq] says is the same term, so the caller builds the
    proof term that stock builds; the physical sharing between the reduced terms can differ, and
    nothing downstream depends on it.

    What a hit does not repeat is the reduction's side output, which carries no value: the
    [Unfolding] lines of [Set Debug "Cbv"], and [Reductionops.reduction_effect_hook] on each
    constant. A reduction effect can only be declared from OCaml ([Reductionops.declare_reduction_effect]
    and [set_reduction_effect]; no command declares one), no plugin of the Rocq tree declares one,
    and none of the external plugins of speed lane R2's harness switch imports [Reductionops].

    [max_entries] and [max_bucket] bound what the memo keeps alive. A key beyond them is not
    stored and its term is reduced again, as without the memo. *)
module ComputeMemo : sig
  val compute : Evd.evar_map -> EConstr.t -> EConstr.t
end = struct
  exception Uncacheable

  (** Raises [Uncacheable] on a node whose reduction could read the evar map — an evar, a meta, a
      constant outside the global environment (a private constant of [abstract]) — and on the
      other constructors that [exact_eq] does not compare. *)
  let rec check_cacheable c =
    match Constr.kind c with
    | Const (kn, _) when not (Environ.mem_constant kn (Global.env ())) -> raise Uncacheable
    | Rel _ | Var _ | Sort _ | Const _ | Ind _ | Construct _ | Int _ | String _ -> ()
    | Cast (c, _, t) | Prod (_, c, t) | Lambda (_, c, t) -> check_cacheable c; check_cacheable t
    | LetIn (_, v, t, b) -> check_cacheable v; check_cacheable t; check_cacheable b
    | App (f, a) -> check_cacheable f; Array.iter check_cacheable a
    | Meta _ | Evar _ | Case _ | Fix _ | CoFix _ | Proj _ | Float _ | Array _ ->
      raise Uncacheable

  let max_entries = 4096
  let max_bucket = 4

  let table : (int, (Constr.t * Constr.t) list) Hashtbl.t = Hashtbl.create 64
  let genv = ref None
  let entries = ref 0

  let validate () =
    let e = Global.env () in
    match !genv with
    | Some e' when e' == e && !entries < max_entries -> ()
    | _ ->
      Hashtbl.reset table;
      entries := 0;
      genv := Some e

  (* BET-84: a hit skips the reads that reducing the term makes (the bodies
     of the constants it unfolds), and the recorder must see them in each
     proof that injects the term. While a proof is recorded the term is
     reduced again, as without the memo. *)
  let compute evd t =
    let c = EConstr.Unsafe.to_constr t in
    if Proof_recorder.active () then Tacred.compute (Global.env ()) evd t
    else match check_cacheable c with
    | exception Uncacheable -> Tacred.compute (Global.env ()) evd t
    | () ->
      validate ();
      let h = Constr.hash c in
      let l = match Hashtbl.find_opt table h with Some l -> l | None -> [] in
      begin match List.find_opt (fun (k, _) -> exact_eq k c) l with
      | Some (_, r) -> EConstr.of_constr r
      | None ->
        let r = Tacred.compute (Global.env ()) evd t in
        if List.length l < max_bucket then begin
          Hashtbl.replace table h ((c, EConstr.Unsafe.to_constr r) :: l);
          incr entries
        end;
        r
      end
end

type prf =
  | Term (* source is built from constructors.
             target = compute(inj source)
             inj source ==  target *)
  | Same (* target = source
             inj source == inj target *)
  | Conv of EConstr.t (* inj source == target *)
  | Prf of EConstr.t * EConstr.t

(** [eq_proof typ source target] returns (target = target : source = target) *)
let eq_proof typ source target =
  EConstr.mkCast
    ( EConstr.mkApp (force eq_refl, [|typ; target|])
    , DEFAULTcast
    , EConstr.mkApp (force eq, [|typ; source; target|]) )

let interp_prf evd inj source prf =
  let inj_source =
    if inj.EInjT.isid then source else EConstr.mkApp (inj.EInjT.inj, [|source|])
  in
  match prf with
  | Term ->
    let target = ComputeMemo.compute evd inj_source in
    (target, EConstr.mkApp (force eq_refl, [|inj.target; target|]))
  | Same ->
    (inj_source, EConstr.mkApp (force eq_refl, [|inj.target; inj_source|]))
  | Conv trm -> (trm, eq_proof inj.target inj_source trm)
  | Prf (target, prf) -> (target, prf)

let pp_prf prf =
  match prf with
  | Term -> Pp.str "Term"
  | Same -> Pp.str "Same"
  | Conv t -> Pp.(str "Conv " ++ gl_pr_constr t)
  | Prf (_, _) -> Pp.str "Prf "

let interp_prf evd inj source prf =
  let t, prf' = interp_prf evd inj source prf in
  debug_zify (fun () ->
      Pp.(
        str "interp_prf " ++ gl_pr_constr inj.EInjT.inj ++ str " "
        ++ gl_pr_constr source ++ str " = " ++ gl_pr_constr t ++ str " by "
        ++ gl_pr_constr prf' ++ str " from " ++ pp_prf prf ++ fnl ()));
  (t, prf')

let mkvar evd inj e =
  (match inj.cstr with None -> () | Some ctr -> CstrTable.register evd e ctr);
  Same

let pp_prf evd inj src prf =
  let t, prf' = interp_prf evd inj src prf in
  Pp.(
    gl_pr_constr inj.EInjT.inj ++ str " " ++ gl_pr_constr src ++ str " = "
    ++ gl_pr_constr t ++ str " by "
    ++
    match prf with
    | Term -> Pp.str "Term"
    | Same -> Pp.str "Same"
    | Conv t -> Pp.str "Conv"
    | Prf (_, p) -> Pp.str "Prf " ++ gl_pr_constr p)

let conv_of_term evd op isid arg =
  ComputeMemo.compute evd
    (if isid then arg else EConstr.mkApp (op, [|arg|]))

let app_unop env evd src unop arg prf =
  let cunop = unop.EUnOpT.classify_unop in
  let default a' prf' =
    let target = EConstr.mkApp (unop.EUnOpT.tuop, [|a'|]) in
    let evd, h = Typing.checked_appvect env evd (force mkapp)
        [| unop.source1
         ; unop.source2
         ; unop.target1
         ; unop.target2 |]
    in
    evd,
    EUnOpT.(
      Prf
        ( target
        , EConstr.mkApp
            ( h
            , [| unop.uop
               ; unop.inj1_t.EInjT.inj
               ; unop.inj2_t.EInjT.inj
               ; unop.tuop
               ; unop.tuopinj
               ; arg
               ; a'
               ; prf' |] ) ))
  in
  match prf with
  | Term -> (
    if unop.EUnOpT.is_construct then evd, Term (* Keep rebuilding *)
    else
      match cunop with
      | OpInj -> evd, Conv (conv_of_term evd unop.EUnOpT.uop false arg)
      | OpSame -> evd, Same
      | _ ->
        let a', prf = interp_prf evd unop.EUnOpT.inj1_t arg prf in
        default a' prf )
  | Same -> (
    match cunop with
    | OpSame -> evd, Same
    | OpInj -> evd, Same
    | OpConv ->
      evd,
      Conv
        (EConstr.mkApp
           ( unop.EUnOpT.tuop
           , [|EConstr.mkApp (unop.EUnOpT.inj1_t.EInjT.inj, [|arg|])|] ))
    | OpOther ->
      let a', prf' = interp_prf evd unop.EUnOpT.inj1_t arg prf in
      default a' prf' )
  | Conv a' -> (
    match cunop with
    | OpSame | OpConv -> evd, Conv (EConstr.mkApp (unop.EUnOpT.tuop, [|a'|]))
    | OpInj -> evd, Conv a'
    | _ ->
      let a', prf = interp_prf evd unop.EUnOpT.inj1_t arg prf in
      default a' prf )
  | Prf (a', prf') -> default a' prf'

let app_unop env evd src unop arg prf =
  let (evd', r) as res = app_unop env evd src unop arg prf in
  debug_zify (fun () ->
      Pp.(
        str "\napp_unop "
        ++ pp_prf evd unop.EUnOpT.inj1_t arg prf
        ++ str " => "
        ++ pp_prf evd' unop.EUnOpT.inj2_t src r));
  res

let app_binop env evd src binop arg1 prf1 arg2 prf2 =
  EBinOpT.(
    let mkApp a1 a2 = EConstr.mkApp (binop.tbop, [|a1; a2|]) in
    let to_conv inj arg = function
      | Term -> conv_of_term evd inj.EInjT.inj inj.EInjT.isid arg
      | Same ->
        if inj.EInjT.isid then arg else EConstr.mkApp (inj.EInjT.inj, [|arg|])
      | Conv t -> t
      | Prf _ -> failwith "Prf is not convertible"
    in
    let default a1 prf1 a2 prf2 =
      let res = mkApp a1 a2 in
      let evd, head = Typing.checked_appvect env evd (force mkapp2)
          [| binop.source1
           ; binop.source2
           ; binop.source3
           ; binop.target1
           ; binop.target2
           ; binop.target3 |]
      in
      let prf =
        EBinOpT.(
          EConstr.mkApp
            ( head
            , [| binop.bop
               ; binop.inj1.EInjT.inj
               ; binop.inj2.EInjT.inj
               ; binop.inj3.EInjT.inj
               ; binop.tbop
               ; binop.tbopinj
               ; arg1
               ; a1
               ; prf1
               ; arg2
               ; a2
               ; prf2 |] ))
      in
      evd, Prf (res, prf)
    in
    match (binop.EBinOpT.classify_binop, prf1, prf2) with
    | OpSame, Same, Same -> evd, Same
    | OpSame, Term, Same | OpSame, Same, Term -> evd, Same
    | OpSame, (Term | Same | Conv _), (Term | Same | Conv _) ->
      let t1 = to_conv binop.EBinOpT.inj1 arg1 prf1 in
      let t2 = to_conv binop.EBinOpT.inj1 arg2 prf2 in
      evd, Conv (mkApp t1 t2)
    | _, _, _ ->
      let a1, prf1 = interp_prf evd binop.inj1 arg1 prf1 in
      let a2, prf2 = interp_prf evd binop.inj2 arg2 prf2 in
      default a1 prf1 a2 prf2)

type typed_constr = {constr : EConstr.t; typ : EConstr.t; inj : EInjT.t}


(* [arrow] is the term (fun (x:Prop) (y : Prop) => x -> y) *)
let arrow =
  let name x =
    Context.make_annot (Name.mk_name (Names.Id.of_string x)) ERelevance.relevant
  in
  EConstr.mkLambda
    ( name "x"
    , EConstr.mkProp
    , EConstr.mkLambda
        ( name "y"
        , EConstr.mkProp
        , EConstr.mkProd
            ( Context.make_annot Names.Anonymous ERelevance.relevant
            , EConstr.mkRel 2
            , EConstr.mkRel 2 ) ) )

let is_prop env sigma term =
  let sort = Retyping.get_sort_of env sigma term in
  EConstr.ESorts.is_prop sigma sort

let is_arrow env evd a p1 p2 =
  is_prop env evd p1
  && is_prop
       (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (a, p1)) env)
       evd p2
  && (a.Context.binder_name = Names.Anonymous || EConstr.Vars.noccurn evd 1 p2)

(** [get_operator env evd e] expresses [e] as an application (c a)
     where c is the head symbol and [a] is the array of arguments.
     The function also transforms (x -> y) as (arrow x y) *)
let get_operator barrow env evd e =
  let e' = EConstr.whd_evar evd e in
  match EConstr.kind evd e' with
  | Prod (a, p1, p2) ->
    if barrow && is_arrow env evd a p1 p2 then (arrow, [|p1; p2|], false)
    else raise Not_found
  | App (c, a) -> (
    let c' = EConstr.whd_evar evd c in
    match EConstr.kind evd c' with
    | Construct _ (* e.g. Z0 , Z.pos *) | Const _ (* e.g. Z.max *) | Proj _
     |Lambda _ (* e.g projections *) | Ind _ (* e.g. eq *) ->
      (c', a, false)
    | _ -> raise Not_found )
  | Const _ -> (e', [||], false)
  | Construct _ -> (e', [||], true)
  | Int _ | Float _ -> (e', [||], true)
  | _ -> raise Not_found

let decompose_app env evd e =
  match EConstr.kind evd e with
  | Prod (a, p1, p2) when is_arrow env evd a p1 p2 -> (arrow, [|p1; p2|])
  | App (c, a) -> (c, a)
  | _ -> (EConstr.whd_evar evd e, [||])

type 'op propop = {op : 'op; op_constr : EConstr.t; op_iff : EConstr.t}

let mk_propop op c1 c2 = {op; op_constr = c1; op_iff = c2}

type prop_binop = AND | OR | IFF | IMPL
type prop_unop = NOT

type prop_op =
  | BINOP of prop_binop propop * EConstr.t * EConstr.t
  | UNOP of prop_unop propop * EConstr.t
  | OTHEROP of EConstr.t * EConstr.t array

let classify_prop env evd e =
  match EConstr.kind evd e with
  | Prod (a, p1, p2) when is_arrow env evd a p1 p2 ->
    BINOP (mk_propop IMPL arrow (force op_impl_morph), p1, p2)
  | App (c, a) -> (
    match Array.length a with
    | 1 ->
      if EConstr.eq_constr_nounivs evd (force op_not) c then
        UNOP (mk_propop NOT c (force op_not_morph), a.(0))
      else OTHEROP (c, a)
    | 2 ->
      if EConstr.eq_constr_nounivs evd (force op_and) c then
        BINOP (mk_propop AND c (force op_and_morph), a.(0), a.(1))
      else if EConstr.eq_constr_nounivs evd (force op_or) c then
        BINOP (mk_propop OR c (force op_or_morph), a.(0), a.(1))
      else if EConstr.eq_constr_nounivs evd (force op_iff) c then
        BINOP (mk_propop IFF c (force op_iff_morph), a.(0), a.(1))
      else OTHEROP (c, a)
    | _ -> OTHEROP (c, a) )
  | _ -> OTHEROP (e, [||])


let check_target_inj evd inj d =
  match inj , target_inj d with
  | None , _ -> true
  | Some _ , None -> false
  | Some i1 , Some i2 -> EInjT.eq_inj evd i1 i2


(** [match_operator env evd hd arg inj (t,d)]
     - hd is head operator of t
     - If t = OtherTerm _, then t = hd
     - If t = Application _, then
       we extract the relevant number of arguments from arg
       and check for convertibility *)
let match_operator env evd hd args inj (t, d) =
  let decomp t i =
    let n = Array.length args in
    let t' = EConstr.mkApp (hd, Array.sub args 0 (n - i)) in
    if is_convertible env evd t' t then Some (d, t) else None
  in

  if check_target_inj evd inj d
  then
  match t with
  | OtherTerm t -> Some (d, t)
  | Application t -> (
    match d with
    | CstOp _ -> decomp t 0
    | UnOp _ -> decomp t 1
    | BinOp _ -> decomp t 2
    | BinRel _ -> decomp t 2
    | PropOp _ -> decomp t 2
    | PropUnOp _ -> decomp t 1
    | _ -> None )
  else None

let pp_trans_expr env evd e res =
  debug_zify (fun () -> Pp.(str "\ntrans_expr " ++ pp_prf evd e.inj e.constr res));
  res

let rec trans_expr env evd e =
  let inj = e.inj in
  let e = e.constr in
  try
    let c, a, is_constant = get_operator false env evd e in
    if is_constant then evd, Term
    else
      let k, t =
        find_option
          (match_operator env evd c a (Some inj))
          (ConstrMap.find_all evd c !table_cache)
      in
      let n = Array.length a in
      match k with
      | CstOp {deriv = c'} ->
        ECstOpT.(if c'.is_construct then evd, Term else evd, Prf (c'.cst, c'.cstinj))
      | UnOp {deriv = unop} ->
        let evd, prf =
          trans_expr env evd
            { constr = a.(n - 1)
            ; typ = unop.EUnOpT.source1
            ; inj = unop.EUnOpT.inj1_t }
        in
        app_unop env evd e unop a.(n - 1) prf
      | BinOp {deriv = binop} ->
        let evd, prf1 =
          trans_expr env evd
            { constr = a.(n - 2)
            ; typ = binop.EBinOpT.source1
            ; inj = binop.EBinOpT.inj1 }
        in
        let evd, prf2 =
          trans_expr env evd
            { constr = a.(n - 1)
            ; typ = binop.EBinOpT.source2
            ; inj = binop.EBinOpT.inj2 }
        in
        app_binop env evd e binop a.(n - 2) prf1 a.(n - 1) prf2
      | d -> evd, mkvar evd inj e
  with Not_found | DestKO -> evd, mkvar evd inj e

let trans_expr env evd e =
  try
    let evd, prf = trans_expr env evd e in
    evd, pp_trans_expr env evd e prf
  with Not_found ->
    raise
      (CErrors.user_err
         ( Pp.str "Missing injection for type "
         ++ Printer.pr_leconstr_env env evd e.typ ))

type prfp =
  | TProof of EConstr.t * EConstr.t  (** Proof of tranformed proposition *)
  | CProof of EConstr.t  (** Transformed proposition is convertible *)
  | IProof  (** Transformed proposition is identical *)

let pp_prfp = function
  | TProof (t, prf) ->
    Pp.str "TProof " ++ gl_pr_constr t ++ Pp.str " by " ++ gl_pr_constr prf
  | CProof t -> Pp.str "CProof " ++ gl_pr_constr t
  | IProof -> Pp.str "IProof"

let trans_binrel env evd src rop a1 prf1 a2 prf2 =
  EBinRelT.(
    match (rop.classify_rel, prf1, prf2) with
    | OpSame, Same, Same -> evd, IProof
    | (OpSame | OpConv), Conv t1, Conv t2 ->
      evd, CProof (EConstr.mkApp (rop.tbrel, [|t1; t2|]))
    | (OpSame | OpConv), (Same | Term | Conv _), (Same | Term | Conv _) ->
      let a1', _ = interp_prf evd rop.inj a1 prf1 in
      let a2', _ = interp_prf evd rop.inj a2 prf2 in
      evd, CProof (EConstr.mkApp (rop.tbrel, [|a1'; a2'|]))
    | _, _, _ ->
      let a1', prf1 = interp_prf evd rop.inj a1 prf1 in
      let a2', prf2 = interp_prf evd rop.inj a2 prf2 in
      (* XXX do we need to check more of this application or check other applications?
         This one found necessary in #16803 *)
      let evd, h = Typing.checked_appvect env evd (force mkrel) [| rop.source; rop.target |] in
      evd, TProof
        ( EConstr.mkApp (rop.EBinRelT.tbrel, [|a1'; a2'|])
        , EConstr.mkApp
            ( h
            , [| rop.brel
               ; rop.EBinRelT.inj.EInjT.inj
               ; rop.EBinRelT.tbrel
               ; rop.EBinRelT.brelinj
               ; a1
               ; a1'
               ; prf1
               ; a2
               ; a2'
               ; prf2 |] ) ))

let trans_binrel env evd src rop a1 prf1 a2 prf2 =
  let evd, res = trans_binrel env evd src rop a1 prf1 a2 prf2 in
  debug_zify (fun () -> Pp.(str "\ntrans_binrel " ++ pp_prfp res));
  evd, res

let mkprf t p =
  EConstr.(
    match p with
    | IProof -> (t, mkApp (force iff_refl, [|t|]))
    | CProof t' -> (t', mkApp (force eq_iff, [|t; t'; eq_proof mkProp t t'|]))
    | TProof (t', p) -> (t', p))

let mkprf t p =
  let t', p = mkprf t p in
  debug_zify (fun () ->
      Pp.(
        str "mkprf " ++ gl_pr_constr t ++ str " <-> " ++ gl_pr_constr t'
        ++ str " by " ++ gl_pr_constr p));
  (t', p)

let trans_bin_prop op_constr op_iff t1 p1 t2 p2 =
  match (p1, p2) with
  | IProof, IProof -> IProof
  | CProof t1', IProof -> CProof (EConstr.mkApp (op_constr, [|t1'; t2|]))
  | IProof, CProof t2' -> CProof (EConstr.mkApp (op_constr, [|t1; t2'|]))
  | CProof t1', CProof t2' -> CProof (EConstr.mkApp (op_constr, [|t1'; t2'|]))
  | _, _ ->
    let t1', p1 = mkprf t1 p1 in
    let t2', p2 = mkprf t2 p2 in
    TProof
      ( EConstr.mkApp (op_constr, [|t1'; t2'|])
      , EConstr.mkApp (op_iff, [|t1; t2; t1'; t2'; p1; p2|]) )

let trans_bin_prop op_constr op_iff t1 p1 t2 p2 =
  let prf = trans_bin_prop op_constr op_iff t1 p1 t2 p2 in
  debug_zify (fun () -> pp_prfp prf);
  prf

let trans_un_prop op_constr op_iff p1 prf1 =
  match prf1 with
  | IProof -> IProof
  | CProof p1' -> CProof (EConstr.mkApp (op_constr, [|p1'|]))
  | TProof (p1', prf) ->
    TProof
      ( EConstr.mkApp (op_constr, [|p1'|])
      , EConstr.mkApp (op_iff, [|p1; p1'; prf|]) )

let rec trans_prop env evd e =
  match classify_prop env evd e with
  | BINOP ({op_constr; op_iff}, p1, p2) ->
    let evd, prf1 = trans_prop env evd p1 in
    let evd, prf2 = trans_prop env evd p2 in
    evd, trans_bin_prop op_constr op_iff p1 prf1 p2 prf2
  | UNOP ({op_constr; op_iff}, p1) ->
    let evd, prf1 = trans_prop env evd p1 in
    evd, trans_un_prop op_constr op_iff p1 prf1
  | OTHEROP (c, a) -> (
    try
      let k, t =
        find_option
          (match_operator env evd c a None)
          (ConstrMap.find_all evd c !table_cache)
      in
      let n = Array.length a in
      match k with
      | BinRel {decl = br; deriv = rop} ->
        let evd, a1 =
          trans_expr env evd
            { constr = a.(n - 2)
            ; typ = rop.EBinRelT.source
            ; inj = rop.EBinRelT.inj }
        in
        let evd, a2 =
          trans_expr env evd
            { constr = a.(n - 1)
            ; typ = rop.EBinRelT.source
            ; inj = rop.EBinRelT.inj }
        in
        trans_binrel env evd e rop a.(n - 2) a1 a.(n - 1) a2
      | _ -> evd, IProof
    with Not_found | DestKO -> evd, IProof )

let trans_check_prop env evd t =
  if is_prop env evd t then
    let evd, p = trans_prop env evd t in
    evd, Some p
  else evd, None

(** [TypeMemo] memoises [trans_check_prop] on hypothesis types and conclusions across zify calls:
    repeated lia calls on one proof context zify the same hypotheses again and again.

    An entry computed for the type [key] is reused for the type [c] in the environment [env] when
    - [c] and [key] are syntactically equal, binder names, relevances and casts included
      ([exact_eq]);
    - every variable reachable from [key] has the same declaration in [env] as in the environment of
      the computation. The variables reachable from a term are its free variables, the section
      variables that its constants, inductive types and constructors depend on
      ([Environ.vars_of_global]: a constant [mytype := a] over a section [Let a := nat] unfolds to
      [a], whose body [clearbody] removes), and, recursively, those of their declarations;
    - the global environment and zify's instance table are physically those of the computation
      ([validate] empties the memo on any change). The global environment holds the bodies of the
      global constants, the global universe graph, and the conversion strategies that [Opaque],
      [Transparent] and [Strategy] set: these change the global environment, and the
      translation's conversions ([is_convertible]) use full transparency anyway;
    - the evar map's universe graph is physically one that the entry was checked against (the
      computation's, or one that a later lookup saw with the computation's local context), or the
      evar map has physically the computation's local universe context (its levels and universe
      constraints) and side effects ([univs_ok]).
    Only evar-free and universe-free terms get entries ([scan]), and the instance terms that the
    translation converts against are closed and universe-free too ([closed_instances]). So the
    proof's own universes reach the translation only through the evar map's universe graph: the
    global graph (kept by the previous condition), plus the local universe constraints, plus the
    universes of the private constants that side effects ([abstract], schemes built on the fly)
    move into the graph without a change to the local constraints. The last condition keeps all
    three. It asks for the very same local context, not for one that relates the global levels
    alike: that test walks the whole context, which a long proof makes thousands of levels large,
    each time the context has changed, and in one agent proof it cost 23 s of checks against 2.3 s
    of translations saved. Only terms whose constants are in the global environment get
    entries ([scan]): the private constants of [abstract] and [transparent_abstract] live in the
    evar map until the end of the sentence, so a backtracked branch of one sentence can define a
    private constant whose name another branch reuses with another type or body, under the same
    global environment. The translation reads nothing else: no option (the [zify] debug flag turns
    the memo off), no [Arguments] or typeclass table (it uses zify's own instance table), and of
    the goal's context only the declarations reachable from the term. It is then a function of the
    entry's inputs, and its effects ([Effects]: the [CstrTable] registrations and the evar map
    threaded through [Typing.checked_appvect]) are had again, in order, when the entry is reused.

    A miss translates the key first, and keeps an entry only when the translation allocated at least
    [min_words] words: a cheaper translation costs no more than the memo's own work would, so it is
    not worth the dependency scan. The scan of a kept key visits at most [nodes_per_word] nodes per
    word of its translation, and at most [max_deps] variables. A key whose scan reaches either bound
    gets an [Over_cap] entry instead of a translation: the verdict that the memo does not apply to
    it, so that a later lookup in the same context runs the translation at once, without the scan.
    It is reused under the conditions above, its dependencies being the declarations that the scan
    read, except the condition on the universe graph, which the scan does not read. So a miss costs
    the translation, plus a scan of at most a fixed fraction of its work. *)
module TypeMemo : sig
  (** To call once per zify call, after [init_cache]: empties the memo when the global environment
      or zify's instance table changed. *)
  val validate : unit -> unit

  (** [memo env evd c f] is [f ()], the translation of the type [c] in [env] and [evd], or the
      result of an earlier [f] for [c] whose inputs are the same, with its effects had again. *)
  val memo :
       Environ.env
    -> Evd.evar_map
    -> Constr.t
    -> (unit -> Evd.evar_map * prfp option)
    -> Evd.evar_map * prfp option
end = struct
  exception Uncacheable

  (** [scan env step reach c] applies [reach] to the free variables of [c] and to the section
      variables that the global references of [c] depend on in [env], to those of one reference until
      [reach] returns false, and [step] to each node of [c]; it raises [Uncacheable] on evars, metas,
      universes, constants outside the global environment (private constants) and the constructors
      [exact_eq] does not compare. *)
  let rec scan env step reach c =
    step ();
    match Constr.kind c with
    | Rel _ | Int _ | String _ | Sort (Sorts.SProp | Sorts.Prop | Sorts.Set) -> ()
    | Var id -> ignore (reach id)
    | Cast (c, _, t) | Prod (_, c, t) | Lambda (_, c, t) -> scan env step reach c; scan env step reach t
    | LetIn (_, v, t, b) -> scan env step reach v; scan env step reach t; scan env step reach b
    | App (f, a) -> scan env step reach f; Array.iter (scan env step reach) a
    | Const (kn, _) when not (Environ.mem_constant kn (Global.env ())) -> raise Uncacheable
    | Const _ | Ind _ | Construct _ ->
      let gr, u = Constr.destRef c in
      if UVars.Instance.is_empty u then ignore (Id.Set.for_all reach (Environ.vars_of_global env gr))
      else raise Uncacheable
    | Sort _ | Meta _ | Evar _ | Case _ | Fix _ | CoFix _ | Proj _ | Float _ | Array _ ->
      raise Uncacheable

  (** The most variables that an entry may depend on. Without the bound, a chain of [n] local
      definitions [x_i := x_(i-1) + 1], each with a hypothesis on [x_i], costs [O(n)] per hypothesis
      and [O(n^2)] per zify call, where the translation itself costs [O(n)]. *)
  let max_deps = 64

  (** The fewest words that a translation must allocate for the memo to keep its key. A cheaper one
      (a hypothesis that zify leaves alone, such as [P x] for a predicate [P] it does not know) costs
      about what a lookup and a dependency scan would. *)
  let min_words = 2048.

  (** The nodes that the dependency scan of a key may visit per word that its translation allocated. *)
  let nodes_per_word = 0.125

  (** The dependencies of a key: [Deps l], [l] the declarations of the variables reachable from the
      key; or [Over l], the scan reached one of its bounds and [l] are the declarations that it read
      in full before that. *)
  type deps =
    | Deps of Constr.named_declaration list
    | Over of Constr.named_declaration list

  exception Bound

  (** [deps env nodes c]: the dependencies of the key [c] in [env]. The variables reachable from [c]
      are its free variables, the section variables that its constants, inductive types and
      constructors depend on ([Environ.vars_of_global]: a constant [mytype := a] over a section
      [Let a := nat] unfolds to [a], whose body [clearbody] removes), and, recursively, those of
      their declarations. The scan reads [c], then the declarations of the variables it reaches, in
      the order it reaches them. It stops at the first variable beyond [max_deps] or at the first node
      beyond [nodes], so it costs at most [nodes] nodes, whatever the context. Raises [Uncacheable] as
      [scan] does, and on a variable without a declaration, unless a bound was reached first. *)
  let deps env nodes c =
    let seen = ref Id.Set.empty and n = ref 0 and todo = ref [] and left = ref nodes and acc = ref [] in
    let step () = decr left; if !left < 0 then raise Bound in
    let reach id =
      if Id.Set.mem id !seen then true
      else if !n < max_deps then begin
        seen := Id.Set.add id !seen;
        incr n;
        todo := id :: !todo;
        true
      end
      else raise Bound
    in
    let rec close () =
      match !todo with
      | [] -> ()
      | id :: rest ->
        todo := rest;
        let d = try Environ.lookup_named id env with Not_found -> raise Uncacheable in
        scan env step reach (NamedDecl.get_type d);
        Option.iter (scan env step reach) (NamedDecl.get_value d);
        acc := d :: !acc;
        close ()
    in
    match scan env step reach c; close () with
    | () -> Deps !acc
    | exception Bound -> Over !acc

  (** What an entry holds for its key. *)
  type result =
    | Translation of
        { mutable univs : UGraph.t
              (** the evar map's universe graph ([Evd.universes]) at the computation, or at a later
                  lookup with the same local universe context and side effects *)
        ; uctx : Univ.ContextSet.t  (** the evar map's local universe context at the computation *)
        ; seff : Evd.side_effects  (** the evar map's side effects at the computation *)
        ; res : prfp option
        ; effects : Effects.t list }
    | Over_cap  (** the scan of the key reached one of its bounds: [deps] returned [Over] *)

  type entry =
    { key : Constr.t
    ; deps : Constr.named_declaration list
          (** the declarations that [deps] returned for [key], in [Deps] or [Over] *)
    ; mutable gen : int
          (** the generation ([contexts]) of a named context where [deps_ok] holds: that of the
              computation, or of a later lookup where it held *)
    ; result : result }

  type named_map = Constr.named_declaration Id.Map.t

  (** The [max_contexts] latest named contexts in which the memo was used, newest first, by their
      variable maps ([Environ.env_named_map], which [Environ.lookup_named] reads) and a generation
      number of each. An entry records the generation of a context where [deps_ok] holds for it;
      only these few maps are kept, whatever the number of entries. *)
  let max_contexts = 8

  let contexts : (int * named_map) list ref = ref []
  let last_gen = ref 0

  (** The [rebound] sets of the older contexts of [contexts] against the newest, by generation. *)
  let rebound_sets : (int * Id.Set.t) list ref = ref []

  let forget_contexts () =
    contexts := [];
    rebound_sets := []

  (** [generation map]: the generation of the context of variable map [map], which becomes the
      newest of [contexts]. *)
  let generation map =
    match !contexts with
    | (g, m) :: _ when m == map -> g
    | l ->
      let g, l =
        match List.find_opt (fun (_, m) -> m == map) l with
        | Some (g, _) -> (g, List.filter (fun (g', _) -> g' <> g) l)
        | None ->
          incr last_gen;
          (!last_gen, l)
      in
      contexts := (g, map) :: List.filteri (fun i _ -> i < max_contexts - 1) l;
      rebound_sets := [];
      g

  (** [rebound map0 map1]: the variables that [map0] binds and whose declaration in [map1] is not
      physically the same, or which [map1] does not bind. [Id.Map.symmetric_diff_fold] skips the
      subtrees that the two maps share, so its cost is that of their difference. *)
  let rebound map0 map1 =
    Id.Map.symmetric_diff_fold
      (fun id d0 _ s -> if Option.has_some d0 then Id.Set.add id s else s)
      map0 map1 Id.Set.empty

  (** [rebound_set g0 map]: the [rebound] set of the context of generation [g0] against [map], the
      newest context; [None] if [contexts] no longer holds [g0]. *)
  let rebound_set g0 map =
    match List.assoc_opt g0 !rebound_sets with
    | Some _ as s -> s
    | None -> (
      match List.assoc_opt g0 !contexts with
      | None -> None
      | Some map0 ->
        let s = rebound map0 map in
        rebound_sets := (g0, s) :: !rebound_sets;
        Some s )

  let decl_ok map d =
    match Id.Map.find_opt (NamedDecl.get_id d) map with
    | Some d' -> d == d' || NamedDecl.equal Sorts.relevance_equal exact_eq d d'
    | None -> false

  (** [deps_ok env e]: each declaration of [e.deps] is that of its variable in [env] (physically,
      or equal by [exact_eq]). It holds in the context of generation [e.gen]; so it holds at once in
      that context, and in another one it needs checking only for the variables that [rebound]
      gives against [e.gen]'s context, or for all of them if [contexts] no longer holds it. When it
      holds, [env]'s context's generation becomes [e.gen]. *)
  let deps_ok env e =
    let map = (Environ.named_context_val env).Environ.env_named_map in
    let g = generation map in
    e.gen = g
    || (match rebound_set e.gen map with
        | Some s ->
          Id.Set.is_empty s
          || List.for_all (fun d -> not (Id.Set.mem (NamedDecl.get_id d) s) || decl_ok map d) e.deps
        | None -> List.for_all (decl_ok map) e.deps)
       && begin
         e.gen <- g;
         true
       end

  let memo : (int, entry list) Hashtbl.t = Hashtbl.create 1024
  let stamp : (Environ.env * (term_kind * decl_kind) ConstrMap.t) option ref = ref None

  (** The number of entries in [memo]; [validate] empties it at [max_entries]. *)
  let entries = ref 0
  let max_entries = 100_000

  (** The most entries that [memo] keeps for one hash. [add] runs after [find] returned no entry, so
      an entry with the same key has dependencies that fail in the current environment: [add]
      replaces it, and drops the oldest entries beyond [max_bucket]. Without this bound, one type
      whose local declarations change at every call (a [pose]d body, backtracked) piles up entries
      that every lookup compares. *)
  let max_bucket = 4

  (** The memo is used only when the instance terms that the translation converts against
      ([Application] keys of the table, see [match_operator]) are closed and universe-free, as the
      memoised terms are. *)
  let usable = ref false

  let closed_instances env table =
    ConstrMap.fold
      (fun _ (k, _) ok ->
        ok
        &&
        match k with
        | OtherTerm _ -> true
        | Application t -> (
          let closed = ref true in
          let reach _ = closed := false; false in
          match scan env ignore reach (EConstr.Unsafe.to_constr t) with
          | () -> !closed
          | exception Uncacheable -> false ))
      table true

  (** To call once per zify call, after [init_cache]. *)
  let validate () =
    let genv = Global.env () in
    match !stamp with
    | Some (e, t) when e == genv && t == !table_cache && !entries < max_entries -> ()
    | _ ->
      Hashtbl.reset memo;
      entries := 0;
      forget_contexts ();
      stamp := Some (genv, !table_cache);
      usable := closed_instances genv !table_cache

  (** [univs_ok evd r]: [evd]'s universe graph is one that [r] was checked against, or [evd] has the
      computation's local universe context ([Evd.universe_context_set] returns the evar map's stored
      level set and constraint set) and side effects (whose private constants' universes are in the
      graph but not in the local context). An entry that passes on the context takes [evd]'s graph,
      so that the next lookup in this state passes on the graph. *)
  let univs_ok evd = function
    | Over_cap -> true
    | Translation t ->
      let univs = Evd.universes evd in
      t.univs == univs
      ||
      let l1, c1 = t.uctx and l2, c2 = Evd.universe_context_set evd in
      l1 == l2 && c1 == c2 && t.seff == Evd.eval_side_effects evd
      && begin t.univs <- univs; true end

  let find env evd h c =
    match Hashtbl.find_opt memo h with
    | None -> None
    | Some l -> List.find_opt (fun e -> exact_eq e.key c && univs_ok evd e.result && deps_ok env e) l

  let add h e =
    let old = Option.default [] (Hashtbl.find_opt memo h) in
    let others = List.filter (fun e' -> not (exact_eq e'.key e.key)) old in
    let l = e :: List.filteri (fun i _ -> i < max_bucket - 1) others in
    entries := !entries - List.length old + List.length l;
    Hashtbl.replace memo h l

  (** [replay_effects env evd l] has the effects [l] again: it registers the terms in [CstrTable]
      and threads [evd] through the [Typing.checked_appvect] calls. *)
  let replay_effects env evd l =
    List.fold_left
      (fun evd -> function
        | Effects.Register (t, i) -> CstrTable.HConstr.add CstrTable.table t i; evd
        | Effects.Checked_appvect (f, args) -> fst (Typing.checked_appvect env evd f args))
      evd l

  (* BET-84: a hit skips the reads the translation makes (its conversions
     and reductions), and replays only [Effects.Register] and
     [Effects.Checked_appvect]. While a proof is recorded the type is
     translated again, as without the memo. *)
  let memo env evd c f =
    if not !usable || Proof_recorder.active () then f ()
    else
      let h = Constr.hash c in
      match find env evd h c with
      | Some {result = Translation t; _} -> (replay_effects env evd t.effects, t.res)
      | Some {result = Over_cap; _} -> f ()
      | None ->
        let w = Gc.minor_words () in
        let ((_, res) as r), effects = Effects.record f in
        let words = Gc.minor_words () -. w in
        if words >= min_words then begin
          let gen = generation (Environ.named_context_val env).Environ.env_named_map in
          match deps env (int_of_float (words *. nodes_per_word)) c with
          | exception Uncacheable -> ()
          | Over deps -> add h {key = c; deps; gen; result = Over_cap}
          | Deps deps ->
            let univs = Evd.universes evd and uctx = Evd.universe_context_set evd in
            let seff = Evd.eval_side_effects evd in
            add h {key = c; deps; gen; result = Translation {univs; uctx; seff; res; effects}}
        end;
        r
end

(** [trans_check_prop], memoised by [TypeMemo], except under [Set Debug "zify"]: a memo hit would
    skip the debug output of the translation. *)
let trans_check_prop_memo env evd t =
  if CDebug.get_flag debug_zify_flag then trans_check_prop env evd t
  else
    TypeMemo.memo env evd (EConstr.Unsafe.to_constr t) (fun () -> trans_check_prop env evd t)

let get_hyp_typ = function
  | NamedDecl.LocalDef (h, _, ty) | NamedDecl.LocalAssum (h, ty) ->
    (h.Context.binder_name, EConstr.of_constr ty)

let trans_hyps env evd l =
  List.fold_left
    (fun (evd, acc) decl ->
      let h, ty = get_hyp_typ decl in
      match trans_check_prop_memo env evd ty with
      | evd, None -> evd, acc
      | evd, Some p' -> evd, (h, ty, p') :: acc)
    (evd, []) l

let trans_hyp h t0 prfp =
  debug_zify (fun () -> Pp.(str "trans_hyp: " ++ pp_prfp prfp ++ fnl ()));
  match prfp with
  | IProof -> Tacticals.tclIDTAC (* Should detect before *)
  | CProof t' ->
    Proofview.Goal.enter (fun gl ->
        let env = Proofview.Goal.env gl in
        let evd = Proofview.Goal.sigma gl in
        let t' = Reductionops.nf_betaiota env evd t' in
        Tactics.change_in_hyp ~check:true None
          (Tactics.make_change_arg t')
          (h, Locus.InHypTypeOnly))
  | TProof (t', prf) ->
    Tacticals.(
      Proofview.Goal.enter (fun gl ->
          let env = Proofview.Goal.env gl in
          let evd = Proofview.Goal.sigma gl in
          let target = Reductionops.nf_betaiota env evd t' in
          let h' = Tactics.fresh_id_in_env Id.Set.empty h env in
          let prf =
            EConstr.mkApp (force rew_iff, [|t0; target; prf; EConstr.mkVar h|])
          in
          tclTHEN
            (Tactics.pose_proof (Name.Name h') prf)
            (tclTRY
               (tclTHEN (Tactics.clear [h]) (Tactics.rename_hyp [(h', h)])))))

let trans_concl prfp =
  debug_zify (fun () -> Pp.(str "trans_concl: " ++ pp_prfp prfp ++ fnl ()));
  match prfp with
  | IProof -> Tacticals.tclIDTAC
  | CProof t ->
    Proofview.Goal.enter (fun gl ->
        let env = Proofview.Goal.env gl in
        let evd = Proofview.Goal.sigma gl in
        let t' = Reductionops.nf_betaiota env evd t in
        Tactics.change_concl t')
  | TProof (t, prf) ->
    Proofview.Goal.enter (fun gl ->
        let env = Proofview.Goal.env gl in
        let evd = Proofview.Goal.sigma gl in
        let typ = get_type_of env evd prf in
        match EConstr.kind evd typ with
        | App (c, a) when Array.length a = 2 ->
          Tactics.apply (EConstr.mkApp (Lazy.force rew_iff_rev, [|a.(0); a.(1); prf|]))
        | _ ->
          raise (CErrors.anomaly Pp.(str "zify cannot transform conclusion")))

let tclTHENOpt e tac tac' =
  match e with None -> tac' | Some e' -> Tacticals.tclTHEN (tac e') tac'


let elim_binding x t ty =
  Proofview.Goal.enter (fun gl ->
      let env = Proofview.Goal.env gl in
      let h =
        Tactics.fresh_id_in_env Id.Set.empty (Nameops.add_prefix "heq_" x) env
      in
      Tacticals.tclTHEN
        (Tactics.pose_proof (Name h) (eq_proof ty (EConstr.mkVar x) t))
        (Tacticals.tclTRY (Tactics.clear_body [x])))

let do_let tac (h : Constr.named_declaration) =
  match h with
  | Context.Named.Declaration.LocalAssum _ -> Tacticals.tclIDTAC
  | Context.Named.Declaration.LocalDef (id, t, ty) ->
    Proofview.Goal.enter (fun gl ->
        let env = Proofview.Goal.env gl in
        let evd = Proofview.Goal.sigma gl in
        try
          let x = id.Context.binder_name in
          ignore
            (let eq = Lazy.force eq in
             find_option
               (match_operator env evd eq
                  [|EConstr.of_constr ty; EConstr.mkVar x; EConstr.of_constr t|] None)
               (ConstrMap.find_all evd eq !table_cache));
          tac x (EConstr.of_constr t) (EConstr.of_constr ty)
        with Not_found -> Tacticals.tclIDTAC)

let iter_let_aux tac =
  Proofview.Goal.enter (fun gl ->
      let env = Proofview.Goal.env gl in
      let sign = Environ.named_context env in
      init_cache ();
      Tacticals.tclMAP (do_let tac) sign)

let iter_let (tac : Ltac_plugin.Tacinterp.Value.t) =
  iter_let_aux (fun (id : Names.Id.t) t ty ->
      Ltac_plugin.Tacinterp.Value.apply tac
        [ Ltac_plugin.Tacinterp.Value.of_constr (EConstr.mkVar id)
        ; Ltac_plugin.Tacinterp.Value.of_constr t
        ; Ltac_plugin.Tacinterp.Value.of_constr ty ])

let elim_let = iter_let_aux elim_binding

let zify_tac =
  Proofview.Goal.enter (fun gl ->
      Rocqlib.check_required_library ["Stdlib"; "micromega"; "ZifyClasses"];
      Rocqlib.check_required_library ["Stdlib"; "micromega"; "ZifyInst"];
      init_cache ();
      TypeMemo.validate ();
      let evd = Proofview.Goal.sigma gl in
      let env = Proofview.Goal.env gl in
      let sign = Environ.named_context env in
      let concl = Proofview.Goal.concl gl in
      let evd, concl = trans_check_prop_memo env evd concl in
      let evd, hyps = trans_hyps env evd sign in
      let l = CstrTable.get () in
      Proofview.tclTHEN (Proofview.Unsafe.tclEVARS evd)
        (tclTHENOpt concl trans_concl
           (Tacticals.tclTHEN
              (Tacticals.tclTHENLIST
                 (List.rev_map (fun (h, p, t) -> trans_hyp h p t) hyps))
              (CstrTable.gen_cstr l))))

type pscript = Set of Names.Id.t * EConstr.t | Pose of Names.Id.t * EConstr.t

type spec_env =
  { map : Names.Id.t HConstr.t
  ; spec_name : Names.Id.t
  ; term_name : Names.Id.t
  ; fresh : Nameops.Subscript.t
  ; proofs : pscript list }

let register_constr {map; spec_name; term_name; fresh; proofs} c thm =
  let tname = Nameops.add_subscript term_name fresh in
  let sname = Nameops.add_subscript spec_name fresh in
  ( EConstr.mkVar tname
  , { map = HConstr.add c tname map
    ; spec_name
    ; term_name
    ; fresh = Nameops.Subscript.succ fresh
    ; proofs = Set (tname, c) :: Pose (sname, thm) :: proofs } )

let fresh_subscript env =
  let ctx = (Environ.named_context_val env).Environ.env_named_map in
  Nameops.Subscript.succ
    (Names.Id.Map.fold
       (fun id _ s ->
         let _, s' = Nameops.get_subscript id in
         let cmp = Nameops.Subscript.compare s s' in
         if cmp = 0 then s else if cmp < 0 then s' else s)
       ctx Nameops.Subscript.zero)

let init_env sname tname s =
  { map = HConstr.empty
  ; spec_name = sname
  ; term_name = tname
  ; fresh = s
  ; proofs = [] }

let rec spec_of_term env evd (senv : spec_env) t =
  let get_name t env =
    try EConstr.mkVar (HConstr.find t senv.map) with Not_found -> t
  in
  let c, a = decompose_app env evd t in
  if a = [||] then (* The term cannot be decomposed. *)
    (get_name t senv, senv)
  else
    (* recursively analyse the sub-terms *)
    let a', senv' =
      Array.fold_right
        (fun e (l, senv) ->
          let r, senv = spec_of_term env evd senv e in
          (r :: l, senv))
        a ([], senv)
    in
    let a' = Array.of_list a' in
    let t' = EConstr.mkApp (c, a') in
    try (EConstr.mkVar (HConstr.find t' senv'.map), senv')
    with Not_found -> (
      try
        match snd (ConstrMap.find evd c !specs_cache) with
        | UnOpSpec s | BinOpSpec s ->
          let thm = EConstr.mkApp (s.deriv.ESpecT.spec, a') in
          register_constr senv' t' thm
        | _ -> (get_name t' senv', senv')
      with Not_found | DestKO -> (t', senv') )

let interp_pscript s =
  match s with
  | Set (id, c) ->
    Tacticals.tclTHEN
      (Tactics.letin_tac None (Names.Name id) c None
         {Locus.onhyps = None; Locus.concl_occs = Locus.AllOccurrences})
      (Tacticals.tclTRY (Tactics.clear_body [id]))
  | Pose (id, c) -> Tactics.pose_proof (Names.Name id) c

let rec interp_pscripts l =
  match l with
  | [] -> Tacticals.tclIDTAC
  | s :: l -> Tacticals.tclTHEN (interp_pscript s) (interp_pscripts l)

(** [may_have_spec specs c] is false when [c] has no evar and none of its applications has a head
    with an entry in [specs]. [spec_of_term] then registers nothing for [c]. *)
let may_have_spec specs c =
  let rec go c =
    (match Constr.kind c with
     | Evar _ | Meta _ -> raise Exit
     | App (f, _) when Constr.isRef f && ConstrMap.mem f specs ->
       raise Exit
     | _ -> ());
    Constr.iter go c
  in
  try go c; false with Exit -> true

let spec_of_hyps =
  Proofview.Goal.enter (fun gl ->
      let env = Proofview.Goal.env gl in
      let concl = Proofview.Goal.concl gl in
      let evd = Proofview.Goal.sigma gl in
      let terms = concl :: List.map NamedDecl.get_type (EConstr.named_context env) in
      let specs = !specs_cache in
      if not (List.exists (fun t -> may_have_spec specs (EConstr.Unsafe.to_constr t)) terms) then
        Tacticals.tclIDTAC
      else
      let s = fresh_subscript env in
      let env =
        List.fold_left
          (fun acc t -> snd (spec_of_term env evd acc t))
          (init_env (Names.Id.of_string "H") (Names.Id.of_string "z") s)
          terms
      in
      interp_pscripts (List.rev env.proofs))

let iter_specs = spec_of_hyps

let find_hyp evd t l =
  try
    Some
      (EConstr.mkVar
         (fst (List.find (fun (h, t') -> EConstr.eq_constr evd t t') l)))
  with Not_found -> None

let find_proof evd t l =
  if EConstr.eq_constr evd t (Lazy.force op_True) then Some (Lazy.force op_I)
  else
    let l = List.map (fun decl -> NamedDecl.get_id decl, NamedDecl.get_type decl) l in
    find_hyp evd t l

(** [sat_constr env evd sub taclist hyps c d]= (sub',taclist',hyps') where
    -  sub' is a fresh subscript obtained from sub
    - taclist' is obtained from taclist by posing the lemma 'd' applied to 'c'
    - hyps' is obtained from hyps'
    taclist and hyps are threaded to avoid adding duplicates
 *)
let sat_constr env evd hyps (sub, taclist, prfs) c d =
  match EConstr.kind evd c with
  | App (c, args) ->
     if Array.length args = 2 then
       let h1 =
         Tacred.cbv_beta env evd
           (EConstr.mkApp (d.ESatT.parg1, [|args.(0)|]))
       in
       let h2 =
         Tacred.cbv_beta env evd
           (EConstr.mkApp (d.ESatT.parg2, [|args.(1)|]))
       in
       let n = Nameops.add_subscript (Names.Id.of_string "__sat") sub in
       let trm =
         match (find_proof evd h1 hyps, find_proof evd h2 hyps) with
         | Some h1, Some h2 ->
            (EConstr.mkApp (d.ESatT.satOK, [|args.(0); args.(1); h1; h2|]))
         | Some h1, _ ->
            EConstr.mkApp (d.ESatT.satOK, [|args.(0); args.(1); h1|])
         | _, _ -> EConstr.mkApp (d.ESatT.satOK, [|args.(0); args.(1)|])
       in
       let rtrm = Tacred.cbv_beta env evd trm in
       let typ  = Retyping.get_type_of env evd rtrm in
       match find_hyp evd typ prfs with
       | None -> (Nameops.Subscript.succ sub, (Tactics.pose_proof (Names.Name n) rtrm :: taclist) , (n,typ)::prfs)
       | Some _ -> (sub, taclist, prfs)
     else (sub,taclist,prfs)
  | _ -> (sub,taclist,prfs)


let get_all_sat env evd c =
  List.fold_left
    (fun acc e -> match e with _, Saturate s -> s :: acc | _ -> acc)
    []
    ( try ConstrMap.find_all evd c !saturate_cache
      with DestKO | Not_found -> [] )

let saturate =
  Proofview.Goal.enter (fun gl ->
      init_cache ();
      let table = CstrTable.HConstr.create 20 in
      let concl = Proofview.Goal.concl gl in
      let env = Proofview.Goal.env gl in
      let hyps = EConstr.named_context env in
      let evd = Proofview.Goal.sigma gl in
      let rec sat t =
        match EConstr.kind evd t with
        | App (c, args) ->
          sat c;
          Array.iter sat args;
          if Array.length args = 2 then
            let ds = get_all_sat env evd c in
            if ds = [] ||  CstrTable.HConstr.mem table t
            then ()
            else List.iter (fun x ->
                     CstrTable.HConstr.add table t x.deriv) ds
          else ()
        | Prod (a, t1, t2) when a.Context.binder_name = Names.Anonymous ->
          sat t1; sat t2
        | _ -> ()
      in
      (* Collect all the potential saturation lemma *)
      sat concl;
      let () = List.iter (fun decl -> sat (NamedDecl.get_type decl)) hyps in
      if CstrTable.HConstr.length table = 0 then Tacticals.tclIDTAC else
      let s0 = fresh_subscript env in
      let (_,tacs,_) = CstrTable.HConstr.fold (fun c d acc -> sat_constr env evd hyps acc c d) table (s0,[],[]) in
      Tacticals.tclTHENLIST tacs)
