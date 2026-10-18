(* VM fast paths for self-contained binary-number operations.

   The checker captures a checked body for each canonical Corelib or Stdlib
   anchor once per process. The interpreter registers a closure only when its
   checked body is structurally equal to one of those reference terms; a
   closure is never selected by name. The C implementations below need no
   transparent definition other than the closure they replace, so an [Opaque]
   dependency cannot change their bytecode semantics. *)

open Declarations

type operation =
  | Pos_compare_cont
  | Pos_eqb

let enabled = Sys.getenv_opt "ROCQ_VM_FASTBIN" = Some "1"

let anchors = [
  "Corelib.BinNums.PosDef.Pos.compare_cont", Pos_compare_cont;
  "Corelib.BinNums.PosDef.Pos.eqb", Pos_eqb;
  "Stdlib.BinNums.PosDef.Pos.compare_cont", Pos_compare_cont;
  "Stdlib.BinNums.PosDef.Pos.eqb", Pos_eqb;
]

let references : (operation, Constr.t) Hashtbl.t = Hashtbl.create (List.length anchors)

let id = function
  | Pos_compare_cont -> 0
  | Pos_eqb -> 1

let arity = function
  | Pos_compare_cont -> 3
  | Pos_eqb -> 2

external register_closure : Vmvalues.values -> int -> int -> unit = "rocq_vmfast_register"

let trace = Sys.getenv_opt "ROCQ_VM_FASTBIN_TRACE" = Some "1"


let capture_reference kn = function
  | Def body ->
    let name = Names.Constant.to_string kn in
    if trace && (String.ends_with ~suffix:".compare_cont" name
                 || String.ends_with ~suffix:".Pos.eqb" name) then
      Printf.eprintf "FASTBIN candidate: %s\n%!" name;
    List.iter (fun (anchor, op) ->
        if String.equal name anchor && not (Hashtbl.mem references op) then begin
          if trace then Printf.eprintf "FASTBIN reference: %s\n%!" name;
          Hashtbl.add references op body
        end)
      anchors
  | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> ()

let operation_of_body body =
  Hashtbl.fold (fun op reference found ->
      match found with
      | Some _ -> found
      | None -> if Constr.equal body reference then Some op else None)
    references None

let register _kn body value =
  if enabled then
    match operation_of_body body with
    | Some op ->
      if trace then Printf.eprintf "FASTBIN register op=%d\n%!" (id op);
      register_closure value (id op) (arity op)
    | None -> ()
