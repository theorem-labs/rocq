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
   of kernel/byterun/rocq_binnum.c. *)
let routines = [|
  { name = "Pos.compare_cont"; arity = 3 };
  { name = "Pos.eqb"; arity = 2 };
|]

let arity k = routines.(k).arity

external c_arities : unit -> int array = "rocq_binnum_arities"
external c_counters : unit -> int array = "rocq_binnum_counters"
external c_reset_counters : unit -> unit = "rocq_binnum_reset_counters"

let () =
  if not (Array.equal Int.equal (c_arities ()) (Array.map (fun r -> r.arity) routines)) then
    failwith "Vmbinnum: the routines differ from those of rocq_binnum.c"

(** {6 Environment variables} *)

let stop fmt =
  Printf.ksprintf (fun msg ->
      let names = String.concat ", " (Array.to_list (Array.map (fun r -> r.name) routines)) in
      Printf.eprintf "%s\nThe routines are: %s.\n%!" msg names;
      exit 1)
    fmt

let routine_of_name name =
  let rec find k =
    if k = Array.length routines then None
    else if String.equal routines.(k).name name then Some k
    else find (k + 1)
  in
  find 0

(* ROCQ_VM_BINNUM: unset, every routine is on; 0, every routine is off;
   -name1,-name2, the listed routines are off. *)
let enabled = lazy (
  let n = Array.length routines in
  match Sys.getenv_opt "ROCQ_VM_BINNUM" with
  | None -> Array.make n true
  | Some "0" -> Array.make n false
  | Some v ->
    let on = Array.make n true in
    let off item =
      let len = String.length item in
      let name = if len > 1 && item.[0] = '-' then Some (String.sub item 1 (len - 1)) else None in
      match Option.bind name routine_of_name with
      | Some k -> on.(k) <- false
      | None ->
        stop "ROCQ_VM_BINNUM=%s: expected 0 or a comma-separated list of -name, \
              not %S." v item
    in
    List.iter off (String.split_on_char ',' v);
    on)

let stats_level =
  match Sys.getenv_opt "ROCQ_VM_BINNUM_STATS" with
  | None | Some "0" -> 0
  | Some "1" -> 1
  | Some "2" -> 2
  | Some v -> stop "ROCQ_VM_BINNUM_STATS=%s: expected 0, 1 or 2." v

(** {6 Statistics} *)

let nbinds = ref 0
let nnear = ref 0
let nothers = ref 0

(* Printed lines, the last first; filled only when [stats_level > 0]. *)
let bind_lines = ref []
let near_lines = ref []

let reset_stats () =
  c_reset_counters ();
  nbinds := 0;
  nnear := 0;
  nothers := 0;
  bind_lines := [];
  near_lines := []

let print_stats () =
  if stats_level > 0 then begin
    let pid = Unix.getpid () in
    let line s = Printf.eprintf "binnum[%d] %s\n" pid s in
    let c = c_counters () in
    Array.iteri (fun k r ->
        let calls = c.(3 * k) and refusals = c.(3 * k + 1) and words = c.(3 * k + 2) in
        line (Printf.sprintf "routine %s: calls=%d hits=%d refusals=%d words=%d"
                r.name calls (calls - refusals) refusals words))
      routines;
    line (Printf.sprintf "recognizer: binds=%d near-misses=%d others=%d"
            !nbinds !nnear !nothers);
    List.iter line (List.rev !bind_lines);
    List.iter line (List.rev !near_lines);
    flush stderr
  end

let () = if stats_level > 0 then at_exit print_stats

(** {6 Inductive types} *)

(* The inductive types of a reference term are slots: [Ind ((slot_mind, i), _)]
   stands for the inductive type that the body has at that place, which must
   be the same at every place of slot [i], and must have the shape of slot
   [i]. No body names [slot_mind]: it is only compared by its slot number. *)
let slot_mind =
  MutInd.make2 (ModPath.MPfile (DirPath.make [Id.of_string "VmbinnumReference"]))
    (Id.of_string "slot")

type shape = {
  shape_name : string;
  (* For each constructor, in order, its number of arguments. Each argument
     has the type itself. *)
  shape_args : int array;
  (* The VM representation that the C routines assume: for each constructor,
     its tag and its number of fields; a constructor without fields is the
     immediate [Val_int tag] (kernel/indtypes.ml, the [mind_reloc_tbl]). *)
  shape_reloc : Vmvalues.reloc_table;
}

let positive = 0
let comparison = 1
let bool = 2

let shapes = [|
  (* xI : positive -> positive | xO : positive -> positive | xH : positive *)
  { shape_name = "positive"; shape_args = [| 1; 1; 0 |];
    shape_reloc = [| (1, 1); (2, 1); (0, 0) |] };
  (* Eq | Lt | Gt *)
  { shape_name = "comparison"; shape_args = [| 0; 0; 0 |];
    shape_reloc = [| (0, 0); (1, 0); (2, 0) |] };
  (* true | false *)
  { shape_name = "bool"; shape_args = [| 0; 0 |];
    shape_reloc = [| (0, 0); (1, 0) |] };
|]

let same_ind a b = Ind.UserOrd.equal a b && Ind.CanOrd.equal a b

let is_self ind t = match kind t with
  | Ind (ind', u) -> Ind.CanOrd.equal ind ind' && UVars.Instance.is_empty u
  | _ -> false

(* Why [ind] does not have the shape of slot [slot] in [env], if it does not.
   It reads only what it has checked to be there, so a malformed declaration
   is a reason, not an exception. *)
let shape_error env slot ((mind, i) as ind) =
  let shape = shapes.(slot) in
  let ncons = Array.length shape.shape_args in
  let nconst = Array.fold_left (fun n a -> if Int.equal a 0 then n + 1 else n) 0 shape.shape_args in
  let constructor_ok (ctx, concl) nargs =
    is_self ind concl
    && Int.equal (List.length ctx) nargs
    && List.for_all (function
        | Context.Rel.Declaration.LocalAssum (_, t) -> is_self ind t
        | Context.Rel.Declaration.LocalDef _ -> false) ctx
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
      else if not (Int.equal mib.mind_nparams 0 && Int.equal mib.mind_nparams_rec 0)
           || not (List.is_empty mib.mind_params_ctxt) then Some "it has parameters"
      else if (match mib.mind_universes with Monomorphic -> false | Polymorphic _ -> true)
      then Some "it is universe polymorphic"
      else if not (Int.equal oib.mind_nrealdecls 0) then Some "it has indices"
      else if not (Sorts.relevance_equal oib.mind_relevance Sorts.Relevant) then
        Some "it is not relevant"
      else if not (Int.equal (Array.length oib.mind_consnames) ncons
                   && Int.equal (Array.length oib.mind_nf_lc) ncons
                   && Array.equal Int.equal oib.mind_consnrealargs shape.shape_args
                   && Array.equal Int.equal oib.mind_consnrealdecls shape.shape_args
                   && Array.for_all2 constructor_ok oib.mind_nf_lc shape.shape_args)
      then Some "its constructors differ"
      else if not (Int.equal oib.mind_nb_constant nconst
                   && Int.equal oib.mind_nb_args (ncons - nconst)
                   && Array.equal (fun (t, a) (t', a') -> Int.equal t t' && Int.equal a a')
                     oib.mind_reloc_tbl shape.shape_reloc)
      then Some "its VM tags differ"
      else None

(** {6 Reference terms} *)

(* Built from the stock bodies of Corelib (theories/Corelib/BinNums/PosDef.v)
   as the kernel has them. *)

let ind slot = mkIndU ((slot_mind, slot), UVars.Instance.empty)
let cstr slot j = mkConstructU (((slot_mind, slot), j), UVars.Instance.empty)
let anon = Context.anonR
let lam dom body = mkLambda (anon, dom, body)
let arrow dom codom = mkProd (anon, dom, codom)

(* [match scrutinee return ret with ... end] on slot [slot], with one branch
   per constructor, each binding the arguments of its constructor. *)
let case slot ret scrutinee branches =
  let nargs = shapes.(slot).shape_args in
  let ci = {
    ci_ind = (slot_mind, slot);
    ci_npar = 0;
    ci_cstr_ndecls = nargs;
    ci_cstr_nargs = nargs;
    ci_pp_info = { style = RegularStyle };
  } in
  let branch j body = (Array.make nargs.(j) anon, body) in
  mkCase (ci, UVars.Instance.empty, [||], (([| anon |], ret), Sorts.Relevant), NoInvert,
          scrutinee, Array.mapi branch branches)

let fix rec_arg typ body =
  mkFix (([| rec_arg |], 0), ([| anon |], [| typ |], [| body |]))

(* fix compare_cont (r : comparison) (x y : positive) {struct y} : comparison :=
     match x with
     | p~1 => match y with
              | q~1 => compare_cont r p q | q~0 => compare_cont Gt p q | 1 => Gt end
     | p~0 => match y with
              | q~1 => compare_cont Lt p q | q~0 => compare_cont r p q | 1 => Gt end
     | 1 => match y with q~1 => Lt | q~0 => Lt | 1 => r end
     end *)
let pos_compare_cont =
  let pos = ind positive and cmp = ind comparison in
  let lt = cstr comparison 2 and gt = cstr comparison 3 in
  (* In the inner branches: q is 1, p 2, y 3, x 4, r 5, compare_cont 6. *)
  let call r = mkApp (mkRel 6, [| r; mkRel 2; mkRel 1 |]) in
  fix 2 (arrow cmp (arrow pos (arrow pos cmp)))
    (lam cmp (lam pos (lam pos
      (case positive cmp (mkRel 2)
         [| case positive cmp (mkRel 2) [| call (mkRel 5); call gt; gt |];
            case positive cmp (mkRel 2) [| call lt; call (mkRel 5); gt |];
            case positive cmp (mkRel 1) [| lt; lt; mkRel 3 |] |]))))

(* fix eqb (p q : positive) {struct q} : bool :=
     match p with
     | p~1 => match q with q~1 => eqb p q | q~0 => false | 1 => false end
     | p~0 => match q with q~1 => false | q~0 => eqb p q | 1 => false end
     | 1 => match q with q~1 => false | q~0 => false | 1 => true end
     end *)
let pos_eqb =
  let pos = ind positive and b = ind bool in
  let tt = cstr bool 1 and ff = cstr bool 2 in
  (* In the inner branches: q0 is 1, p0 2, q 3, p 4, eqb 5. *)
  let call = mkApp (mkRel 5, [| mkRel 2; mkRel 1 |]) in
  fix 1 (arrow pos (arrow pos b))
    (lam pos (lam pos
      (case positive b (mkRel 2)
         [| case positive b (mkRel 2) [| call; ff; ff |];
            case positive b (mkRel 2) [| ff; call; ff |];
            case positive b (mkRel 1) [| ff; ff; tt |] |])))

type reference = {
  ref_name : string;
  term : constr;
  (* The routine of each function of the top-level fixpoint block, or of the
     function at index 0. *)
  funs : int option array;
}

let references = [|
  { ref_name = "Pos.compare_cont"; term = pos_compare_cont; funs = [| Some 0 |] };
  { ref_name = "Pos.eqb"; term = pos_eqb; funs = [| Some 1 |] };
|]

(** {6 Recognition} *)

(* The cheap first test: the head of the body and its number of binders. *)
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

let reference_signatures = Array.map (fun r -> Option.get (signature r.term)) references

(* The first node where the body differs from the reference: the path to it,
   innermost step first, the two subterms there, and why they differ. *)
exception Differ of string list * constr * constr * string

(* [same slots path c r] checks that the body [c] is equal to the reference
   [r], node by node, except for binder names, the [ci_pp_info] of matches,
   and the inductive types, which it binds to the slots of [r]. At the top,
   [~top:true] does not compare the index of a fixpoint in its block. *)
let rec same ?(top = false) slots path c r =
  let differ why = raise (Differ (path, c, r, why)) in
  let sub step c r = same slots (step :: path) c r in
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
  | Prod (na, t, b), Prod (na', t', b') ->
    relevance na na'; sub "product domain" t t'; sub "product codomain" b b'
  | Lambda (na, t, b), Lambda (na', t', b') ->
    relevance na na'; sub "lambda domain" t t'; sub "lambda body" b b'
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
    if not (top || Int.equal i i') then differ "fixpoint index";
    binders nas nas';
    if not (Int.equal (Array.length tys) (Array.length tys')
            && Int.equal (Array.length bds) (Array.length bds'))
    then differ "number of fixpoints";
    Array.iteri (fun i t -> sub (Printf.sprintf "fixpoint type %d" (i + 1)) t tys'.(i)) tys;
    Array.iteri (fun i b -> sub (Printf.sprintf "fixpoint body %d" (i + 1)) b bds'.(i)) bds
  | _ -> differ "node"

(* [Ok ()] if [body] is equal to [r] and its inductive types have the shapes
   of their slots; otherwise why not, and, with [ROCQ_VM_BINNUM_STATS=2], the
   lines that show the first node that differs. *)
let compare_reference env body r =
  let slots = Array.make (Array.length shapes) None in
  match same ~top:true slots [] body r.term with
  | exception Differ (path, c, r', why) ->
    let detail =
      if stats_level < 2 then []
      else
        let pr label c =
          let lines = String.split_on_char '\n' (Pp.string_of_ppcmds (Constr.debug_print c)) in
          List.mapi (fun i l -> (if Int.equal i 0 then "  " ^ label ^ ": " else "    ") ^ l) lines
        in
        ("  at " ^ (match path with [] -> "the top" | _ -> String.concat " > " (List.rev path)))
        :: pr "body" c @ pr "reference" r'
    in
    Error (why, detail)
  | () ->
    let check slot = function
      | None -> None
      | Some ind ->
        Option.map (fun why ->
            Printf.sprintf "the %s %s: %s" shapes.(slot).shape_name
              (MutInd.to_string (fst ind)) why)
          (shape_error env slot ind)
    in
    let errors = List.map_filter (fun x -> x) (Array.to_list (Array.mapi check slots)) in
    match errors with
    | [] -> Ok ()
    | why :: _ -> Error (why, [])

let no_binnum (_ : int) = None

let recognize ?name env body =
  let enabled = Lazy.force enabled in
  if not (Array.exists (fun b -> b) enabled) then no_binnum
  else
    let name () = match name with
      | Some c -> Constant.to_string c
      | None -> "<anonymous>"
    in
    let sg = signature body in
    let candidate k r =
      Array.exists (function Some rk -> enabled.(rk) | None -> false) r.funs
      && (match sg with
          | Some s -> same_signature s reference_signatures.(k)
          | None -> false)
    in
    let rec try_refs k misses =
      if k = Array.length references then begin
        if List.is_empty misses then incr nothers
        else begin
          incr nnear;
          if stats_level > 0 then
            List.iter (fun (r, (why, detail)) ->
                near_lines := List.rev_append
                    (Printf.sprintf "near-miss %s: %s: %s" (name ()) r.ref_name why :: detail)
                    !near_lines)
              (List.rev misses)
        end;
        no_binnum
      end
      else
        let r = references.(k) in
        if not (candidate k r) then try_refs (k + 1) misses
        else match compare_reference env body r with
          | Error e -> try_refs (k + 1) ((r, e) :: misses)
          | Ok () ->
            let funs = Array.map (function
                | Some rk when enabled.(rk) -> Some rk
                | Some _ | None -> None) r.funs
            in
            incr nbinds;
            if stats_level > 0 then begin
              let bound = List.map_filter (Option.map (fun rk -> routines.(rk).name))
                  (Array.to_list funs) in
              bind_lines := Printf.sprintf "bind %s: %s" (name ()) (String.concat "," bound)
                            :: !bind_lines
            end;
            fun i -> if 0 <= i && i < Array.length funs then funs.(i) else None
    in
    try_refs 0 []
