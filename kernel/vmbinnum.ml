(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Constr
open Declarations

(** {6 Routines} *)

type routine = { name : string; arity : int }

(* The index of a routine is its number [k] in [BINNUM k n], and in the table
   of kernel/byterun/rocq_binnum.c, whose [rocq_binnum_run] refuses a number
   [k] outside the table, or with another arity.

   The table is append only: a new routine goes at the end, and no routine
   is moved or removed. The number [k] is stored in the bytecode of [.vo]
   files, and the coqc of a later build runs its own routine [k] on the code
   that this build wrote, with only the arity checked. (coqchk compiles all
   code itself, so it is not affected.) *)
let routines = [|
  { name = "Pos.compare_cont"; arity = 3 };
  { name = "Pos.eqb"; arity = 2 };
  { name = "Pos.succ"; arity = 1 };
  { name = "Pos.add"; arity = 2 };
  { name = "Pos.add_carry"; arity = 2 };
  { name = "Pos.pred_double"; arity = 1 };
  { name = "Pos.mul"; arity = 2 };
  { name = "Pos.div2"; arity = 1 };
  { name = "Pos.of_succ_nat"; arity = 1 };
  { name = "Z.double"; arity = 1 };
  { name = "Z.succ_double"; arity = 1 };
  { name = "Z.pred_double"; arity = 1 };
  { name = "Z.pos_sub"; arity = 2 };
  { name = "Z.add"; arity = 2 };
  { name = "Z.mul"; arity = 2 };
  { name = "Z.compare"; arity = 2 };
  { name = "Z.leb"; arity = 2 };
  { name = "Z.ltb"; arity = 2 };
  { name = "Z.eqb"; arity = 2 };
  { name = "Z.div2"; arity = 1 };
  { name = "Z.of_nat"; arity = 1 };
  { name = "Z.pos_div_eucl"; arity = 2 };
  { name = "Nat.eqb"; arity = 2 };
  { name = "Nat.leb"; arity = 2 };
|]

let arity k = routines.(k).arity

external c_arities : unit -> int array = "rocq_binnum_arities"
external c_counters : unit -> int array = "rocq_binnum_counters"
external c_reset_counters : unit -> unit = "rocq_binnum_reset_counters"
external c_set_stats : bool -> unit = "rocq_binnum_set_stats"
external c_set_pack : bool -> unit = "rocq_binnum_set_pack"

let () =
  if not (Array.equal Int.equal (c_arities ()) (Array.map (fun r -> r.arity) routines)) then
    failwith "Vmbinnum: the routines differ from those of rocq_binnum.c"

let routine_of_name name =
  let rec find k =
    if k = Array.length routines then None
    else if String.equal routines.(k).name name then Some k
    else find (k + 1)
  in
  find 0

(** {6 Environment variables} *)

let stop fmt =
  Printf.ksprintf (fun msg ->
      let names = String.concat ", " (Array.to_list (Array.map (fun r -> r.name) routines)) in
      Printf.eprintf "%s\nThe routines are: %s; and -pack turns packing off.\n%!" msg names;
      exit 1)
    fmt

(* ROCQ_VM_BINNUM: unset, every routine is on; 0, every routine is off;
   -name1,-name2, the listed routines are off; -pack, the routines make no
   packed results (kernel/byterun/rocq_binnum.h). *)
let enabled, packing =
  let n = Array.length routines in
  match Sys.getenv_opt "ROCQ_VM_BINNUM" with
  | None -> Array.make n true, true
  | Some "0" -> Array.make n false, true
  | Some v ->
    let on = Array.make n true in
    let pack = ref true in
    let off item =
      let len = String.length item in
      let name = if len > 1 && item.[0] = '-' then Some (String.sub item 1 (len - 1)) else None in
      match name with
      | Some "pack" -> pack := false
      | _ ->
        match Option.bind name routine_of_name with
        | Some k -> on.(k) <- false
        | None ->
          stop "ROCQ_VM_BINNUM=%s: expected 0 or a comma-separated list of -name, \
                not %S." v item
    in
    List.iter off (String.split_on_char ',' v);
    on, !pack

let stats_level =
  match Sys.getenv_opt "ROCQ_VM_BINNUM_STATS" with
  | None | Some "0" -> 0
  | Some "1" -> 1
  | Some "2" -> 2
  | Some v -> stop "ROCQ_VM_BINNUM_STATS=%s: expected 0, 1 or 2." v

let () = c_set_pack packing

(** {6 Statistics} *)

(* The C routines count their calls only when the statistics are on. *)
let () = c_set_stats (stats_level > 0)

(* Recognitions of bodies at function entry, and of the constants called at
   call sites (once per compilation and constant). *)
let nbinds = ref 0
let nnear = ref 0
let nothers = ref 0
let site_binds = ref 0
let site_near = ref 0
let site_others = ref 0

(* Seconds spent recognizing, measured only when [stats_level > 0]. *)
let entry_time = ref 0.
let site_time = ref 0.

(* Printed lines, the last first; filled only when [stats_level > 0]. *)
let bind_lines = ref []
let near_lines = ref []

let reset_stats () =
  c_reset_counters ();
  nbinds := 0;
  nnear := 0;
  nothers := 0;
  site_binds := 0;
  site_near := 0;
  site_others := 0;
  entry_time := 0.;
  site_time := 0.;
  bind_lines := [];
  near_lines := []

let print_stats () =
  if stats_level > 0 then begin
    let pid = Unix.getpid () in
    let line s = Printf.eprintf "binnum[%d] %s\n" pid s in
    let c = c_counters () in
    let nr = 10 in
    Array.iteri (fun k r ->
        let b = nr * k in
        let ec = c.(b) and er = c.(b + 1) and ew = c.(b + 2) in
        let sc = c.(b + 3) and sr = c.(b + 4) and sw = c.(b + 5) in
        let args = c.(b + 6) and packed = c.(b + 7) and tail = c.(b + 8) in
        line (Printf.sprintf "routine %s: calls=%d hits=%d refusals=%d words=%d \
                              entry-calls=%d entry-refusals=%d entry-words=%d \
                              site-calls=%d site-refusals=%d site-words=%d \
                              args-chain=%d args-packed=%d args-tail=%d packed-results=%d"
                r.name (ec + sc) (ec + sc - er - sr) (er + sr) (ew + sw)
                ec er ew sc sr sw (args - packed - tail) packed tail c.(b + 9)))
      routines;
    let b = nr * Array.length routines in
    line (Printf.sprintf "packed: packing=%s switch-expansions=%d switch-nodes=%d \
                          whd-expansions=%d whd-nodes=%d"
            (if c.(b + 4) <> 0 then "on" else "off") c.(b) c.(b + 1) c.(b + 2) c.(b + 3));
    line (Printf.sprintf "recognizer: binds=%d near-misses=%d others=%d time=%.3fs"
            !nbinds !nnear !nothers !entry_time);
    line (Printf.sprintf "call-sites: binds=%d near-misses=%d others=%d time=%.3fs"
            !site_binds !site_near !site_others !site_time);
    List.iter line (List.rev !bind_lines);
    List.iter line (List.rev !near_lines);
    flush stderr
  end

let () = if stats_level > 0 then at_exit print_stats

(** {6 Inductive types} *)

(* The inductive types of a reference term are slots: [Ind ((slot_mind, i), _)]
   stands for the inductive type that the body has at that place, which must
   be the same at every place of slot [i], and must have the shape of slot
   [i]. No body names [slot_mind]: it is only compared by its slot number.
   The constants of a reference term are callees, in the same module path
   (see [callee] below). *)
let reference_mp = ModPath.MPfile (DirPath.make [Id.of_string "VmbinnumReference"])
let slot_mind = MutInd.make2 reference_mp (Id.of_string "slot")

(* The type of an argument of a constructor: the inductive type itself,
   another slot, or a parameter (numbered from 0, the first). *)
type arg = Self | Slot of int | Param of int

type shape = {
  shape_name : string;
  nparams : int;
  (* For each constructor, in order, the types of its arguments. *)
  cons : arg array array;
  (* The VM representation that the C routines assume: for each constructor,
     its tag and its number of fields; a constructor without fields is the
     immediate [Val_int tag] (kernel/indtypes.ml, the [mind_reloc_tbl]). *)
  shape_reloc : Vmvalues.reloc_table;
}

let pos_s = 0
let cmp_s = 1
let bool_s = 2
let z_s = 3
let nat_s = 4
let prod_s = 5

let shapes = [|
  (* xI : positive -> positive | xO : positive -> positive | xH : positive *)
  { shape_name = "positive"; nparams = 0; cons = [| [| Self |]; [| Self |]; [||] |];
    shape_reloc = [| (1, 1); (2, 1); (0, 0) |] };
  (* Eq | Lt | Gt *)
  { shape_name = "comparison"; nparams = 0; cons = [| [||]; [||]; [||] |];
    shape_reloc = [| (0, 0); (1, 0); (2, 0) |] };
  (* true | false *)
  { shape_name = "bool"; nparams = 0; cons = [| [||]; [||] |];
    shape_reloc = [| (0, 0); (1, 0) |] };
  (* Z0 | Zpos : positive -> Z | Zneg : positive -> Z *)
  { shape_name = "Z"; nparams = 0; cons = [| [||]; [| Slot pos_s |]; [| Slot pos_s |] |];
    shape_reloc = [| (0, 0); (1, 1); (2, 1) |] };
  (* O | S : nat -> nat *)
  { shape_name = "nat"; nparams = 0; cons = [| [||]; [| Self |] |];
    shape_reloc = [| (0, 0); (1, 1) |] };
  (* prod (A B : Type) := pair : A -> B -> prod A B *)
  { shape_name = "prod"; nparams = 2; cons = [| [| Param 0; Param 1 |] |];
    shape_reloc = [| (1, 2) |] };
|]

let same_ind a b = Ind.UserOrd.equal a b && Ind.CanOrd.equal a b

(* Why [ind] does not have the shape of slot [slot] in [env], if it does not.
   An argument of a constructor whose type is another slot binds that slot,
   if the body did not. It reads only what it has checked to be there, so a
   malformed declaration is a reason, not an exception. *)
let shape_error env slots slot ((mind, i) as ind) =
  let shape = shapes.(slot) in
  let np = shape.nparams in
  let nargs = Array.map Array.length shape.cons in
  let ncons = Array.length nargs in
  let nconst = Array.fold_left (fun n a -> if Int.equal a 0 then n + 1 else n) 0 nargs in
  let is_ind ind' t = match kind t with
    | Ind (ind'', u) -> Ind.CanOrd.equal ind' ind'' && UVars.Instance.is_empty u
    | _ -> false
  in
  (* The type [t] of argument [a] of a constructor. *)
  let arg_ok a t = function
    | Self -> Int.equal np 0 && is_ind ind t
    | Param q -> isRelN (np - q + a) t
    | Slot k ->
      match kind t with
      | Ind (ind', u) when UVars.Instance.is_empty u ->
        (match slots.(k) with
         | None -> slots.(k) <- Some ind'; true
         | Some s -> Ind.CanOrd.equal s ind')
      | _ -> false
  in
  let concl_ok n t =
    if Int.equal np 0 then is_ind ind t
    else match kind t with
      | App (f, args) ->
        is_ind ind f && Int.equal (Array.length args) np
        && Array.for_all_i (fun q a -> isRelN (np + n - q) a) 0 args
      | _ -> false
  in
  let is_assum = function
    | Context.Rel.Declaration.LocalAssum _ -> true
    | Context.Rel.Declaration.LocalDef _ -> false
  in
  let constructor_ok j (ctx, concl) =
    let decls = Array.of_list (List.rev ctx) in
    Int.equal (Array.length decls) (np + nargs.(j))
    && Array.for_all is_assum decls
    && Array.for_all_i (fun a ty ->
        arg_ok a (Context.Rel.Declaration.get_type decls.(np + a)) ty) 0 shape.cons.(j)
    && concl_ok nargs.(j) concl
  in
  if not (Environ.mem_mind mind env) then Some "it is not in the environment"
  else
    let mib = Environ.lookup_mind mind env in
    if not (Int.equal (Array.length mib.mind_packets) 1 && Int.equal i 0) then
      Some "it is in a mutual block"
    else
      let oib = mib.mind_packets.(0) in
      if (match mib.mind_finite with CoFinite -> true | Finite | BiFinite -> false)
      then Some "it is coinductive"
      else if not (Int.equal mib.mind_nparams np
                   && Int.equal (List.length mib.mind_params_ctxt) np
                   && List.for_all is_assum mib.mind_params_ctxt)
      then Some "its parameters differ"
      else if (match mib.mind_universes with Monomorphic -> false | Polymorphic _ -> true)
      then Some "it is universe polymorphic"
      else if not (Int.equal oib.mind_nrealdecls 0) then Some "it has indices"
      else if not (Sorts.relevance_equal oib.mind_relevance Sorts.Relevant) then
        Some "it is not relevant"
      else if not (Int.equal (Array.length oib.mind_consnames) ncons
                   && Int.equal (Array.length oib.mind_nf_lc) ncons
                   && Array.equal Int.equal oib.mind_consnrealargs nargs
                   && Array.equal Int.equal oib.mind_consnrealdecls nargs
                   && Array.for_all_i constructor_ok 0 oib.mind_nf_lc)
      then Some "its constructors differ"
      else if not (Int.equal oib.mind_nb_constant nconst
                   && Int.equal oib.mind_nb_args (ncons - nconst)
                   && Array.equal (fun (t, a) (t', a') -> Int.equal t t' && Int.equal a a')
                     oib.mind_reloc_tbl shape.shape_reloc)
      then Some "its VM tags differ"
      else None

(* Checks every slot that the body bound, and those that the constructors of
   these slots bind in turn. *)
let check_slots env slots =
  let checked = Array.make (Array.length slots) false in
  let rec next k =
    if k = Array.length slots then None
    else match slots.(k) with
      | Some ind when not checked.(k) -> Some (k, ind)
      | Some _ | None -> next (k + 1)
  in
  let rec loop () = match next 0 with
    | None -> None
    | Some (k, ind) ->
      checked.(k) <- true;
      match shape_error env slots k ind with
      | None -> loop ()
      | Some why ->
        Some (Printf.sprintf "the %s %s: %s" shapes.(k).shape_name
                (MutInd.to_string (fst ind)) why)
  in
  loop ()

(** {6 Reference terms} *)

(* Built from the stock bodies of Corelib (theories/Corelib/BinNums/PosDef.v
   and IntDef.v, theories/Corelib/Init/Nat.v and Datatypes.v) as the kernel
   has them. A term is written with named variables, which each binder then
   abstracts into de Bruijn indices. *)

let fresh =
  let n = ref 0 in
  fun () -> incr n; Id.of_string ("v" ^ string_of_int !n)

let anon = Context.anonR
let ind slot = mkIndU ((slot_mind, slot), UVars.Instance.empty)
let cstr slot j = mkConstructU (((slot_mind, slot), j), UVars.Instance.empty)
let app f args = mkApp (f, Array.of_list args)
let arrows doms codom = List.fold_right (fun d c -> mkProd (anon, d, c)) doms codom

let lam dom f =
  let x = fresh () in
  mkLambda (anon, dom, Vars.subst_var x (f (mkVar x)))

let lam2 d1 d2 f = lam d1 (fun x -> lam d2 (fun y -> f x y))

let letin ty def f =
  let x = fresh () in
  mkLetIn (anon, def, ty, Vars.subst_var x (f (mkVar x)))

type branch = B0 of constr | B1 of (constr -> constr) | B2 of (constr -> constr -> constr)

(* [match scrutinee return ret with ... end] on slot [slot], with one branch
   per constructor, each binding the arguments of its constructor. [ret] is
   closed. *)
let case ?(params = [||]) slot ret scrutinee branches =
  let shape = shapes.(slot) in
  let nargs = Array.map Array.length shape.cons in
  let () = assert (Int.equal (Array.length branches) (Array.length nargs)) in
  let () = assert (Int.equal (Array.length params) shape.nparams) in
  let ci = {
    ci_ind = (slot_mind, slot);
    ci_npar = shape.nparams;
    ci_cstr_ndecls = nargs;
    ci_cstr_nargs = Array.copy nargs;
    ci_pp_info = { style = RegularStyle };
  } in
  let branch j b =
    let ids = List.init nargs.(j) (fun _ -> fresh ()) in
    let body = match b, List.map mkVar ids with
      | B0 c, [] -> c
      | B1 f, [a] -> f a
      | B2 f, [a; b] -> f a b
      | (B0 _ | B1 _ | B2 _), _ -> assert false
    in
    (Array.make nargs.(j) anon, Vars.subst_vars (List.rev ids) body)
  in
  mkCase (ci, UVars.Instance.empty, params, (([| anon |], ret), Sorts.Relevant), NoInvert,
          scrutinee, Array.mapi branch branches)

(* A block of fixpoints [(recursive argument, type, body)], each body a
   function of the functions of the block; the block's function [index]. *)
let fix ~index decls =
  let fids = List.map (fun _ -> fresh ()) decls in
  let fs = Array.of_list (List.map mkVar fids) in
  let names = Array.of_list (List.map (fun _ -> anon) decls) in
  let ras = Array.of_list (List.map (fun (ra, _, _) -> ra) decls) in
  let tys = Array.of_list (List.map (fun (_, ty, _) -> ty) decls) in
  let bds = Array.of_list (List.map (fun (_, _, f) -> Vars.subst_vars (List.rev fids) (f fs)) decls) in
  mkFix ((ras, index), (names, tys, bds))

let fix1 ra ty f = fix ~index:0 [ (ra, ty, fun fs -> f fs.(0)) ]

let pos = ind pos_s
let cmp = ind cmp_s
let bool_t = ind bool_s
let z_t = ind z_s
let nat_t = ind nat_s
let prod_zz = app (ind prod_s) [z_t; z_t]
let xI p = app (cstr pos_s 1) [p]
let xO p = app (cstr pos_s 2) [p]
let xH = cstr pos_s 3
let c_eq = cstr cmp_s 1
let c_lt = cstr cmp_s 2
let c_gt = cstr cmp_s 3
let b_true = cstr bool_s 1
let b_false = cstr bool_s 2
let z0 = cstr z_s 1
let zpos p = app (cstr z_s 2) [p]
let zneg p = app (cstr z_s 3) [p]
let pair a b = app (cstr prod_s 1) [z_t; z_t; a; b]

let mpos ret s ~xi ~xo ~xh = case pos_s ret s [| B1 xi; B1 xo; B0 xh |]
let mcmp ret s ~eq ~lt ~gt = case cmp_s ret s [| B0 eq; B0 lt; B0 gt |]
let mbool ret s ~tt ~ff = case bool_s ret s [| B0 tt; B0 ff |]
let mz ret s ~zero ~zp ~zn = case z_s ret s [| B0 zero; B1 zp; B1 zn |]
let mnat ret s ~o ~sn = case nat_s ret s [| B0 o; B1 sn |]
let mprod ret s f = case ~params:[| z_t; z_t |] prod_s ret s [| B2 f |]

(* The cheap first test: the head of a body and its number of binders. *)
type signature =
  | SFun of int
  | SFix of int array * int array (* recursive arguments, binders of each body *)

let rec nlambdas c = match kind c with
  | Lambda (_, _, b) -> 1 + nlambdas b
  | _ -> 0

let signature c = match kind c with
  | Lambda _ -> Some (SFun (nlambdas c))
  | Fix ((ra, _), (_, _, bodies)) -> Some (SFix (ra, Array.map nlambdas bodies))
  | _ -> None

let same_signature s s' = match s, s' with
  | SFun n, SFun n' -> Int.equal n n'
  | SFix (ra, nl), SFix (ra', nl') -> Array.equal Int.equal ra ra' && Array.equal Int.equal nl nl'
  | (SFun _ | SFix _), _ -> false

type reference = {
  ref_name : string;
  term : constr;
  (* The routine of each function of the top-level fixpoint block, or of the
     function at index 0; [None] for a reference that is only a callee. *)
  funs : int option array;
  ref_signature : signature option;
}

(* The references, the last first, while they are defined. A reference names
   only references defined before it, so recognition follows a finite chain
   of callees whatever the environment holds. *)
let defined = ref []

(* Callees: [Const (callee_k_j)] in a reference stands for a constant whose
   body is equal to function [j] of reference [k]. *)
let callee_table : (string, int * int) Hashtbl.t = Hashtbl.create 31

let callee name j =
  let rec find k = function
    | [] -> invalid_arg ("Vmbinnum.callee " ^ name)
    | r :: l -> if String.equal r.ref_name name then k else find (k - 1) l
  in
  let k = find (List.length !defined - 1) !defined in
  let label = Printf.sprintf "callee_%d_%d" k j in
  Hashtbl.replace callee_table label (k, j);
  mkConstU (Constant.make1 (KerName.make reference_mp (Id.of_string label)), UVars.Instance.empty)

let callee_of cst =
  if ModPath.equal (Constant.modpath cst) reference_mp then
    Hashtbl.find_opt callee_table (Id.to_string (Constant.label cst))
  else None

let define name funs term =
  let rec no_var c = match kind c with
    | Var _ -> false
    | _ -> Constr.fold (fun ok c -> ok && no_var c) true c
  in
  let () = assert (Vars.closed0 term && no_var term) in
  let routine n = match routine_of_name n with Some k -> k | None -> assert false in
  defined := { ref_name = name; term; funs = Array.map (Option.map routine) funs;
               ref_signature = signature term } :: !defined

let () =
  (* fix compare_cont (r : comparison) (x y : positive) {struct y} : comparison *)
  define "Pos.compare_cont" [| Some "Pos.compare_cont" |]
    (fix1 2 (arrows [cmp; pos; pos] cmp) (fun cc ->
         lam cmp (fun r -> lam2 pos pos (fun x y ->
             let call r p q = app cc [r; p; q] in
             mpos cmp x
               ~xi:(fun p -> mpos cmp y ~xi:(fun q -> call r p q) ~xo:(fun q -> call c_gt p q) ~xh:c_gt)
               ~xo:(fun p -> mpos cmp y ~xi:(fun q -> call c_lt p q) ~xo:(fun q -> call r p q) ~xh:c_gt)
               ~xh:(mpos cmp y ~xi:(fun _ -> c_lt) ~xo:(fun _ -> c_lt) ~xh:r)))));
  (* fix eqb (p q : positive) {struct q} : bool *)
  define "Pos.eqb" [| Some "Pos.eqb" |]
    (fix1 1 (arrows [pos; pos] bool_t) (fun eqb ->
         lam2 pos pos (fun p q ->
             mpos bool_t p
               ~xi:(fun p0 -> mpos bool_t q ~xi:(fun q0 -> app eqb [p0; q0]) ~xo:(fun _ -> b_false) ~xh:b_false)
               ~xo:(fun p0 -> mpos bool_t q ~xi:(fun _ -> b_false) ~xo:(fun q0 -> app eqb [p0; q0]) ~xh:b_false)
               ~xh:(mpos bool_t q ~xi:(fun _ -> b_false) ~xo:(fun _ -> b_false) ~xh:b_true))));
  (* fix succ (x : positive) : positive *)
  define "Pos.succ" [| Some "Pos.succ" |]
    (fix1 0 (arrows [pos] pos) (fun succ ->
         lam pos (fun x -> mpos pos x ~xi:(fun p -> xO (app succ [p])) ~xo:xI ~xh:(xO xH))));
  (* fix add (x y : positive) {struct x} : positive
     with add_carry (x y : positive) {struct x} : positive *)
  define "Pos.add" [| Some "Pos.add"; Some "Pos.add_carry" |]
    (let succ = callee "Pos.succ" 0 in
     let s p = app succ [p] in
     let ty = arrows [pos; pos] pos in
     fix ~index:0 [
       (0, ty, fun fs ->
           let add p q = app fs.(0) [p; q] and addc p q = app fs.(1) [p; q] in
           lam2 pos pos (fun x y ->
               mpos pos x
                 ~xi:(fun p -> mpos pos y ~xi:(fun q -> xO (addc p q)) ~xo:(fun q -> xI (add p q)) ~xh:(xO (s p)))
                 ~xo:(fun p -> mpos pos y ~xi:(fun q -> xI (add p q)) ~xo:(fun q -> xO (add p q)) ~xh:(xI p))
                 ~xh:(mpos pos y ~xi:(fun q -> xO (s q)) ~xo:xI ~xh:(xO xH))));
       (0, ty, fun fs ->
           let add p q = app fs.(0) [p; q] and addc p q = app fs.(1) [p; q] in
           lam2 pos pos (fun x y ->
               mpos pos x
                 ~xi:(fun p -> mpos pos y ~xi:(fun q -> xI (addc p q)) ~xo:(fun q -> xO (addc p q)) ~xh:(xI (s p)))
                 ~xo:(fun p -> mpos pos y ~xi:(fun q -> xO (addc p q)) ~xo:(fun q -> xI (add p q)) ~xh:(xO (s p)))
                 ~xh:(mpos pos y ~xi:(fun q -> xI (s q)) ~xo:(fun q -> xO (s q)) ~xh:(xI xH))));
     ]);
  (* fix pred_double (x : positive) : positive *)
  define "Pos.pred_double" [| Some "Pos.pred_double" |]
    (fix1 0 (arrows [pos] pos) (fun pd ->
         lam pos (fun x -> mpos pos x ~xi:(fun p -> xI (xO p)) ~xo:(fun p -> xI (app pd [p])) ~xh:xH)));
  (* fix mul (x y : positive) {struct x} : positive *)
  define "Pos.mul" [| Some "Pos.mul" |]
    (let add = callee "Pos.add" 0 in
     fix1 0 (arrows [pos; pos] pos) (fun mul ->
         lam2 pos pos (fun x y ->
             mpos pos x ~xi:(fun p -> app add [y; xO (app mul [p; y])])
               ~xo:(fun p -> xO (app mul [p; y])) ~xh:y)));
  (* fun p : positive => ... *)
  define "Pos.div2" [| Some "Pos.div2" |]
    (lam pos (fun p -> mpos pos p ~xi:(fun p0 -> p0) ~xo:(fun p0 -> p0) ~xh:xH));
  define "Pos.div2_up" [| None |]
    (let succ = callee "Pos.succ" 0 in
     lam pos (fun p -> mpos pos p ~xi:(fun p0 -> app succ [p0]) ~xo:(fun p0 -> p0) ~xh:xH));
  (* fix of_succ_nat (n : nat) : positive *)
  define "Pos.of_succ_nat" [| Some "Pos.of_succ_nat" |]
    (let succ = callee "Pos.succ" 0 in
     fix1 0 (arrows [nat_t] pos) (fun osn ->
         lam nat_t (fun n -> mnat pos n ~o:xH ~sn:(fun x -> app succ [app osn [x]]))));
  (* compare_cont Eq *)
  define "Pos.compare" [| None |] (app (callee "Pos.compare_cont" 0) [c_eq]);
  define "CompOpp" [| None |] (lam cmp (fun r -> mcmp cmp r ~eq:c_eq ~lt:c_gt ~gt:c_lt));
  define "Z.double" [| Some "Z.double" |]
    (lam z_t (fun x -> mz z_t x ~zero:z0 ~zp:(fun p -> zpos (xO p)) ~zn:(fun p -> zneg (xO p))));
  define "Z.succ_double" [| Some "Z.succ_double" |]
    (let pd = callee "Pos.pred_double" 0 in
     lam z_t (fun x -> mz z_t x ~zero:(zpos xH) ~zp:(fun p -> zpos (xI p))
                 ~zn:(fun p -> zneg (app pd [p]))));
  define "Z.pred_double" [| Some "Z.pred_double" |]
    (let pd = callee "Pos.pred_double" 0 in
     lam z_t (fun x -> mz z_t x ~zero:(zneg xH) ~zp:(fun p -> zpos (app pd [p]))
                 ~zn:(fun p -> zneg (xI p))));
  (* fix pos_sub (x y : positive) {struct y} : Z *)
  define "Z.pos_sub" [| Some "Z.pos_sub" |]
    (let double = callee "Z.double" 0 and sd = callee "Z.succ_double" 0
     and zpd = callee "Z.pred_double" 0 and pd = callee "Pos.pred_double" 0 in
     fix1 1 (arrows [pos; pos] z_t) (fun ps ->
         lam2 pos pos (fun x y ->
             let sub p q = app ps [p; q] in
             mpos z_t x
               ~xi:(fun p -> mpos z_t y ~xi:(fun q -> app double [sub p q])
                       ~xo:(fun q -> app sd [sub p q]) ~xh:(zpos (xO p)))
               ~xo:(fun p -> mpos z_t y ~xi:(fun q -> app zpd [sub p q])
                       ~xo:(fun q -> app double [sub p q]) ~xh:(zpos (app pd [p])))
               ~xh:(mpos z_t y ~xi:(fun q -> zneg (xO q)) ~xo:(fun q -> zneg (app pd [q])) ~xh:z0))));
  define "Z.add" [| Some "Z.add" |]
    (let padd = callee "Pos.add" 0 and psub = callee "Z.pos_sub" 0 in
     lam2 z_t z_t (fun x y ->
         mz z_t x ~zero:y
           ~zp:(fun x' -> mz z_t y ~zero:x ~zp:(fun y' -> zpos (app padd [x'; y']))
                   ~zn:(fun y' -> app psub [x'; y']))
           ~zn:(fun x' -> mz z_t y ~zero:x ~zp:(fun y' -> app psub [y'; x'])
                   ~zn:(fun y' -> zneg (app padd [x'; y'])))));
  define "Z.opp" [| None |] (lam z_t (fun x -> mz z_t x ~zero:z0 ~zp:zneg ~zn:zpos));
  define "Z.sub" [| None |]
    (let zadd = callee "Z.add" 0 and zopp = callee "Z.opp" 0 in
     lam2 z_t z_t (fun m n -> app zadd [m; app zopp [n]]));
  define "Z.mul" [| Some "Z.mul" |]
    (let pmul = callee "Pos.mul" 0 in
     let m p q = app pmul [p; q] in
     lam2 z_t z_t (fun x y ->
         mz z_t x ~zero:z0
           ~zp:(fun x' -> mz z_t y ~zero:z0 ~zp:(fun y' -> zpos (m x' y')) ~zn:(fun y' -> zneg (m x' y')))
           ~zn:(fun x' -> mz z_t y ~zero:z0 ~zp:(fun y' -> zneg (m x' y')) ~zn:(fun y' -> zpos (m x' y')))));
  define "Z.compare" [| Some "Z.compare" |]
    (let pcmp = callee "Pos.compare" 0 and opp = callee "CompOpp" 0 in
     lam2 z_t z_t (fun x y ->
         mz cmp x ~zero:(mz cmp y ~zero:c_eq ~zp:(fun _ -> c_lt) ~zn:(fun _ -> c_gt))
           ~zp:(fun x' -> mz cmp y ~zero:c_gt ~zp:(fun y' -> app pcmp [x'; y']) ~zn:(fun _ -> c_gt))
           ~zn:(fun x' -> mz cmp y ~zero:c_lt ~zp:(fun _ -> c_lt)
                   ~zn:(fun y' -> app opp [app pcmp [x'; y']]))));
  define "Z.leb" [| Some "Z.leb" |]
    (let zcmp = callee "Z.compare" 0 in
     lam2 z_t z_t (fun x y -> mcmp bool_t (app zcmp [x; y]) ~eq:b_true ~lt:b_true ~gt:b_false));
  define "Z.ltb" [| Some "Z.ltb" |]
    (let zcmp = callee "Z.compare" 0 in
     lam2 z_t z_t (fun x y -> mcmp bool_t (app zcmp [x; y]) ~eq:b_false ~lt:b_true ~gt:b_false));
  define "Z.eqb" [| Some "Z.eqb" |]
    (let peqb = callee "Pos.eqb" 0 in
     lam2 z_t z_t (fun x y ->
         mz bool_t x ~zero:(mz bool_t y ~zero:b_true ~zp:(fun _ -> b_false) ~zn:(fun _ -> b_false))
           ~zp:(fun p -> mz bool_t y ~zero:b_false ~zp:(fun q -> app peqb [p; q]) ~zn:(fun _ -> b_false))
           ~zn:(fun p -> mz bool_t y ~zero:b_false ~zp:(fun _ -> b_false) ~zn:(fun q -> app peqb [p; q]))));
  define "Z.div2" [| Some "Z.div2" |]
    (let div2 = callee "Pos.div2" 0 and div2_up = callee "Pos.div2_up" 0 in
     lam z_t (fun z ->
         mz z_t z ~zero:z0
           ~zp:(fun p -> mpos z_t p ~xi:(fun _ -> zpos (app div2 [p])) ~xo:(fun _ -> zpos (app div2 [p]))
                   ~xh:z0)
           ~zn:(fun p -> zneg (app div2_up [p]))));
  define "Z.of_nat" [| Some "Z.of_nat" |]
    (let osn = callee "Pos.of_succ_nat" 0 in
     lam nat_t (fun n -> mnat z_t n ~o:z0 ~sn:(fun n0 -> zpos (app osn [n0]))));
  (* fix pos_div_eucl (a : positive) (b : Z) {struct a} : Z * Z *)
  define "Z.pos_div_eucl" [| Some "Z.pos_div_eucl" |]
    (let zadd = callee "Z.add" 0 and zmul = callee "Z.mul" 0 and zsub = callee "Z.sub" 0
     and zltb = callee "Z.ltb" 0 and zleb = callee "Z.leb" 0 in
     let two = zpos (xO xH) and one = zpos xH in
     fix1 0 (arrows [pos; z_t] prod_zz) (fun pde ->
         lam2 pos z_t (fun a b ->
             let step a' r'_of =
               mprod prod_zz (app pde [a'; b]) (fun q r ->
                   letin z_t (r'_of r) (fun r' ->
                       mbool prod_zz (app zltb [r'; b])
                         ~tt:(pair (app zmul [two; q]) r')
                         ~ff:(pair (app zadd [app zmul [two; q]; one]) (app zsub [r'; b]))))
             in
             mpos prod_zz a
               ~xi:(fun a' -> step a' (fun r -> app zadd [app zmul [two; r]; one]))
               ~xo:(fun a' -> step a' (fun r -> app zmul [two; r]))
               ~xh:(mbool prod_zz (app zleb [two; b]) ~tt:(pair z0 one) ~ff:(pair one z0)))));
  (* fix eqb (n m : nat) {struct n} : bool *)
  define "Nat.eqb" [| Some "Nat.eqb" |]
    (fix1 0 (arrows [nat_t; nat_t] bool_t) (fun eqb ->
         lam2 nat_t nat_t (fun n m ->
             mnat bool_t n ~o:(mnat bool_t m ~o:b_true ~sn:(fun _ -> b_false))
               ~sn:(fun n' -> mnat bool_t m ~o:b_false ~sn:(fun m' -> app eqb [n'; m'])))));
  (* fix leb (n m : nat) {struct n} : bool *)
  define "Nat.leb" [| Some "Nat.leb" |]
    (fix1 0 (arrows [nat_t; nat_t] bool_t) (fun leb ->
         lam2 nat_t nat_t (fun n m ->
             mnat bool_t n ~o:b_true
               ~sn:(fun n' -> mnat bool_t m ~o:b_false ~sn:(fun m' -> app leb [n'; m'])))))

let references = Array.of_list (List.rev !defined)

(** {6 Recognition} *)

(* The first node where the body differs from the reference: the path to it,
   innermost step first, the two subterms there, and why they differ. *)
exception Differ of string list * constr * constr * string

(* The body of the constant [cst], through aliases (a body that is only a
   constant). Opaque, undefined, missing and universe polymorphic constants
   have none. *)
let max_aliases = 32

let callee_body env cst =
  let rec follow cst n =
    if n > max_aliases then Error "callee: too many aliases"
    else match Environ.lookup_constant_opt cst env with
      | None -> Error "callee not in the environment"
      | Some cb ->
        match cb.const_universes, cb.const_body with
        | Polymorphic _, _ -> Error "callee is universe polymorphic"
        | Monomorphic, Def body ->
          (match kind body with
           | Const (cst', u) when UVars.Instance.is_empty u -> follow cst' (n + 1)
           | _ -> Ok body)
        | Monomorphic, (Undef _ | OpaqueDef _ | Primitive _ | Symbol _) ->
          Error "callee is not a transparent definition"
  in
  follow cst 0

(* Where the comparison is: inside a term, at the top of a body whose
   fixpoint may be any function of its block, or at the top of a callee,
   which must be function [j] of its block. *)
type top = Inner | Any_index | Index of int

(* [same env top slots path c r] checks that the body [c] is equal to the
   reference [r], node by node, except for binder names, the [ci_pp_info] of
   matches, and the inductive types, which it binds to the slots of [r]. A
   callee of [r] matches a constant whose body (read from [env]) is equal to
   the callee's reference, with the same slots. *)
let rec same env top slots path c r =
  let differ why = raise (Differ (path, c, r, why)) in
  let sub step c r = same env Inner slots (step :: path) c r in
  let relevance na na' =
    if not (Sorts.relevance_equal (Context.binder_relevance na) (Context.binder_relevance na'))
    then differ "binder relevance"
  in
  let binders nas nas' =
    if not (Int.equal (Array.length nas) (Array.length nas')) then differ "number of binders";
    Array.iter2 relevance nas nas'
  in
  let empty u = if not (UVars.Instance.is_empty u) then differ "universe instance" in
  let bind slot ind = match slots.(slot) with
    | None -> slots.(slot) <- Some ind
    | Some ind' ->
      if not (same_ind ind ind') then
        differ ("another inductive type in the place of " ^ shapes.(slot).shape_name)
  in
  match kind c, kind r with
  | Rel i, Rel j -> if not (Int.equal i j) then differ "de Bruijn index"
  | Ind (ind, u), Ind ((_, slot), _) -> empty u; bind slot ind
  | Construct ((ind, j), u), Construct (((_, slot), j'), _) ->
    empty u;
    if not (Int.equal j j') then differ "constructor";
    bind slot ind
  | Const (cst, u), Const (cst', _) ->
    empty u;
    (match callee_of cst' with
     | None -> differ "constant"
     | Some (k, j) ->
       let callee = references.(k) in
       match callee_body env cst with
       | Error why -> differ why
       | Ok body -> same env (Index j) slots (("callee " ^ callee.ref_name) :: path) body callee.term)
  | Prod (na, t, b), Prod (na', t', b') ->
    relevance na na'; sub "product domain" t t'; sub "product codomain" b b'
  | Lambda (na, t, b), Lambda (na', t', b') ->
    relevance na na'; sub "lambda domain" t t'; sub "lambda body" b b'
  | LetIn (na, v, t, b), LetIn (na', v', t', b') ->
    relevance na na'; sub "let value" v v'; sub "let type" t t'; sub "let body" b b'
  | App (f, args), App (f', args') ->
    if not (Int.equal (Array.length args) (Array.length args')) then differ "number of arguments";
    sub "function" f f';
    Array.iteri (fun i a -> sub (Printf.sprintf "argument %d" (i + 1)) a args'.(i)) args
  | Case (ci, u, pms, ((nas, p), rl), iv, s, brs),
    Case (ci', _, pms', ((nas', p'), rl'), _, s', brs') ->
    empty u;
    bind (snd ci'.ci_ind) ci.ci_ind;
    if not (Int.equal ci.ci_npar ci'.ci_npar
            && Array.equal Int.equal ci.ci_cstr_ndecls ci'.ci_cstr_ndecls
            && Array.equal Int.equal ci.ci_cstr_nargs ci'.ci_cstr_nargs)
    then differ "case info";
    if not (Int.equal (Array.length pms) (Array.length pms')) then differ "number of parameters";
    Array.iteri (fun i a -> sub (Printf.sprintf "match parameter %d" (i + 1)) a pms'.(i)) pms;
    binders nas nas';
    sub "match return clause" p p';
    if not (Sorts.relevance_equal rl rl') then differ "match relevance";
    (match iv with NoInvert -> () | CaseInvert _ -> differ "case inversion");
    sub "match scrutinee" s s';
    if not (Int.equal (Array.length brs) (Array.length brs')) then differ "number of branches";
    Array.iteri (fun j (nas, b) ->
        let (nas', b') = brs'.(j) in
        binders nas nas';
        sub (Printf.sprintf "branch %d" (j + 1)) b b')
      brs
  | Fix ((ra, i), (nas, tys, bds)), Fix ((ra', i'), (nas', tys', bds')) ->
    if not (Array.equal Int.equal ra ra') then differ "recursive arguments";
    (match top with
     | Inner -> if not (Int.equal i i') then differ "fixpoint index"
     | Any_index -> ()
     | Index j -> if not (Int.equal i j) then differ "fixpoint index");
    binders nas nas';
    if not (Int.equal (Array.length tys) (Array.length tys')
            && Int.equal (Array.length bds) (Array.length bds'))
    then differ "number of fixpoints";
    Array.iteri (fun i t -> sub (Printf.sprintf "fixpoint type %d" (i + 1)) t tys'.(i)) tys;
    Array.iteri (fun i b -> sub (Printf.sprintf "fixpoint body %d" (i + 1)) b bds'.(i)) bds
  | _ -> differ "node"

(* A failure is a near miss unless it is in a type annotation of the
   binders, or the body's first node is not even of the reference's kind. *)
let near_miss path why =
  let annotation s =
    String.equal s "lambda domain" || String.equal s "product domain"
    || String.equal s "product codomain" || CString.is_prefix "fixpoint type" s
  in
  let binder s = String.equal s "lambda body" || CString.is_prefix "fixpoint body" s in
  not (List.exists annotation path)
  && not (List.for_all binder path && List.mem_f String.equal why
            ["node"; "recursive arguments"; "number of fixpoints"; "number of binders"])

(* [Ok ()] if [body] is equal to [r] and its inductive types have the shapes
   of their slots; otherwise whether it is a near miss, why not, and, with
   [~detail:true], the lines that show the first node that differs. *)
let compare_reference ~detail env body r =
  let slots = Array.make (Array.length shapes) None in
  match same env Any_index slots [] body r.term with
  | exception Differ (path, c, r', why) ->
    let detail =
      if not detail then []
      else
        let pr label c =
          let lines = String.split_on_char '\n' (Pp.string_of_ppcmds (Constr.debug_print c)) in
          List.mapi (fun i l -> (if Int.equal i 0 then "  " ^ label ^ ": " else "    ") ^ l) lines
        in
        ("  at " ^ (match path with [] -> "the top" | _ -> String.concat " > " (List.rev path)))
        :: pr "body" c @ pr "reference" r'
    in
    Error (near_miss path why, why, detail)
  | () ->
    match check_slots env slots with
    | None -> Ok ()
    | Some why -> Error (true, why, [])

let no_binnum (_ : int) = None

let any_enabled = Array.exists (fun b -> b) enabled

(* The routines of the functions of [body]'s top-level fixpoint block (or of
   the function at index 0), if [body] is equal to a reference; otherwise the
   near misses, as (reference, why, detail). *)
let match_body ~detail env body =
  let sg = signature body in
  let candidate r =
    Array.exists (function Some k -> enabled.(k) | None -> false) r.funs
    && (match sg, r.ref_signature with
        | Some s, Some s' -> same_signature s s'
        | (Some _ | None), _ -> false)
  in
  let rec try_refs k misses =
    if k = Array.length references then Error (List.rev misses)
    else
      let r = references.(k) in
      if not (candidate r) then try_refs (k + 1) misses
      else match compare_reference ~detail env body r with
        | Error (true, why, detail) -> try_refs (k + 1) ((r, why, detail) :: misses)
        | Error (false, _, _) -> try_refs (k + 1) misses
        | Ok () ->
          Ok (Array.map (function
              | Some rk when enabled.(rk) -> Some rk
              | Some _ | None -> None) r.funs)
  in
  try_refs 0 []

let timed time f =
  if stats_level > 0 then begin
    let t0 = Unix.gettimeofday () in
    let r = f () in
    time := !time +. (Unix.gettimeofday () -. t0);
    r
  end
  else f ()

let recognize ?name env body =
  if not any_enabled then no_binnum
  else
    let name () = match name with
      | Some c -> Constant.to_string c
      | None -> "<anonymous>"
    in
    match timed entry_time (fun () -> match_body ~detail:(stats_level >= 2) env body) with
    | Error [] -> incr nothers; no_binnum
    | Error misses ->
      incr nnear;
      if stats_level > 0 then
        List.iter (fun (r, why, detail) ->
            near_lines := List.rev_append
                (Printf.sprintf "near-miss %s: %s: %s" (name ()) r.ref_name why :: detail)
                !near_lines)
          misses;
      no_binnum
    | Ok funs ->
      incr nbinds;
      if stats_level > 0 then begin
        let bound = List.map_filter (Option.map (fun rk -> routines.(rk).name))
            (Array.to_list funs) in
        bind_lines := Printf.sprintf "bind %s: %s" (name ()) (String.concat "," bound)
                      :: !bind_lines
      end;
      fun i -> if 0 <= i && i < Array.length funs then funs.(i) else None

(* At a call site of [cst]: the routine of the function that [cst] denotes,
   which is the function at the init index of a fixpoint body, and the
   function itself otherwise. As at function entry, [cst] must be a
   transparent definition with an empty universe context, and its body is
   read from [env]. Near misses are counted, not named. *)
let recognize_call env cst =
  if not any_enabled then None
  else match Environ.lookup_constant_opt cst env with
    | None -> None
    | Some cb ->
      let univs = UVars.AbstractContext.size (Declareops.universes_context cb.const_universes) in
      match cb.const_body with
      | Def body when UVars.eq_sizes (0, 0) univs ->
        let index = match kind body with Fix ((_, init), _) -> init | _ -> 0 in
        begin match timed site_time (fun () -> match_body ~detail:false env body) with
          | Error [] -> incr site_others; None
          | Error _ -> incr site_near; None
          | Ok funs ->
            incr site_binds;
            if 0 <= index && index < Array.length funs then funs.(index) else None
        end
      | Def _ | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> None
