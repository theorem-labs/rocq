(* Scratch instrumentation for the bytecode-VM lane's profile (measurement only, never shipped).

   CPU time inside the VM conversion test, split by phase with exclusive accounting: a phase entered
   inside another stops the outer one's clock until it returns, so the accounts add up. Enabled by
   ROCQ_VMSTAT=1; totals go to stderr after each library and at exit, and one VMCONV line per
   conversion gives that conversion's split.

   ROCQ_VMSTAT_CODEMAP=FILE also writes one line per bytecode block the VM links:
   "<hex address> <length in bytes> <kind> <label>", the label naming the constant the block was
   compiled from, so that perf samples of the interpreter's pc register (%r15 on x86-64) can be
   mapped back to Rocq constants. *)

let enabled = Sys.getenv_opt "ROCQ_VMSTAT" = Some "1"

type account = {
  name : string;
  mutable calls : int;
  mutable self : float;
}

let all = ref []

let make name =
  let a = { name; calls = 0; self = 0. } in
  all := a :: !all;
  a

let outside = make "outside"
let stack = ref [outside]
let last = ref 0.

let charge now =
  match !stack with
  | top :: _ -> top.self <- top.self +. (now -. !last); last := now
  | [] -> assert false

let time a f =
  if not enabled then f ()
  else begin
    charge (Sys.time ());
    a.calls <- a.calls + 1;
    stack := a :: !stack;
    let finish () =
      charge (Sys.time ());
      match !stack with
      | _ :: rest -> stack := rest
      | [] -> assert false
    in
    match f () with
    | v -> finish (); v
    | exception e -> finish (); raise e
  end

(* Vconv.conv_val and the OCaml side of readback, minus the interpreter calls it makes. *)
let vm_conv = make "conv_compare"
(* Bytecode compilation of the two terms being converted (lambda, bytegen, emit). *)
let term_compile = make "term_compile"
(* Relocation, threading (tcode_of_code) and free-variable setup of a block, excluding the
   evaluation of the constants it refers to. *)
let link = make "link_patch"
(* First evaluation of a linked constant's code (building its closure or value). *)
let interp_const = make "interp_const"
(* Evaluation of a converted term's code: where the vm_compute work happens. *)
let interp_term = make "interp_term"
(* Interpreter calls made during readback (applying closures to fresh variables, switch types and
   branches on accumulators, fixpoint types). *)
let interp_readback = make "interp_readback"
(* Import-time compilation of every constant's bytecode (Mod_checking.compile_structure). *)
let import_compile = make "import_compile"

let conversions = ref 0
let links = ref 0
let current = ref "?"

(* Constant bodies compiled at import, by canonical name: how many times each was compiled. *)
let compiled : (string, int) Hashtbl.t = Hashtbl.create 4096

let note_compiled name =
  if enabled then
    let n = match Hashtbl.find_opt compiled name with None -> 0 | Some n -> n in
    Hashtbl.replace compiled name (n + 1)

(* Constants linked (evaluated into the global table), by canonical name. *)
let linked : (string, int) Hashtbl.t = Hashtbl.create 4096

let note_linked name =
  if enabled then
    let n = match Hashtbl.find_opt linked name with None -> 0 | Some n -> n in
    Hashtbl.replace linked name (n + 1)

let codemap = lazy (Option.map open_out (Sys.getenv_opt "ROCQ_VMSTAT_CODEMAP"))

external tcode_address : Vmvalues.tcode -> nativeint = "rocq_tcode_address"

let last_code_len = ref 0

let note_code tc kind label =
  incr links;
  match Lazy.force codemap with
  | None -> ()
  | Some oc ->
    Printf.fprintf oc "%nx %d %s %s\n" (tcode_address tc) !last_code_len kind (Lazy.force label)

let conversion f =
  if not enabled then f ()
  else begin
    incr conversions;
    let before = List.map (fun a -> a.self) !all in
    let t0 = Sys.time () in
    let finish () =
      charge (Sys.time ());
      let parts =
        List.map2 (fun a b -> Printf.sprintf "%s=%.6f" a.name (a.self -. b)) !all before
        |> List.rev |> String.concat " "
      in
      Printf.eprintf "VMCONV n=%d cst=%s cpu=%.6f %s\n%!" !conversions !current (Sys.time () -. t0) parts
    in
    match f () with
    | v -> finish (); v
    | exception e -> finish (); raise e
  end

let count_dups tbl =
  let dups = Hashtbl.fold (fun _ n acc -> if n > 1 then acc + 1 else acc) tbl 0 in
  let total = Hashtbl.fold (fun _ n acc -> acc + n) tbl 0 in
  total, Hashtbl.length tbl, dups

let print tag =
  if enabled then begin
    charge (Sys.time ());
    List.iter
      (fun a -> Printf.eprintf "VMSTAT %s %s calls=%d self_cpu=%.6f\n" tag a.name a.calls a.self)
      (List.rev !all);
    let ct, cd, cdup = count_dups compiled in
    let lt, ld, ldup = count_dups linked in
    Printf.eprintf
      "VMSTAT %s counts conversions=%d blocks_linked=%d compiled=%d compiled_distinct=%d compiled_more_than_once=%d linked=%d linked_distinct=%d linked_more_than_once=%d\n%!"
      tag !conversions !links ct cd cdup lt ld ldup
  end

let report_library lib = print ("lib=" ^ lib)

let () =
  at_exit (fun () ->
      print "total";
      match Lazy.force codemap with Some oc -> close_out oc | None -> ())
