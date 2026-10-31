(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* rocq-library-label: the location-free library label of a .vo file
   (vernac/libkeyObjects.ml), recomputed from the file's content.
   - [--check FILE.vo]: one line. "label2 <64 hex>" when the digest the file
     stores for its library segment is the first 16 bytes of the label
     (layout version 2) recomputed from the file's summary and library
     segments, followed by the whole 32-byte label; "md5 <32 hex>" when it
     is the MD5 of the segment's bytes (stock's digest: a library compiled
     without -location-free-label, or with no label), followed by it;
     "other <hex>" otherwise (a label of another layout version, a tampered
     file), followed by the stored digest.
   - [--stored FILE.vo]: the digest the file stores for its library segment,
     in hex, as its dependents record it.
   - [--attempts FILE.vo]: the attempted-resolution records (Attempts), one
     line each, or "no attempts".
   - [--attempts-json FILE.vo]: the same records as one JSON document, in
     the schema documented at [Attempts.to_json] (vernac/attempts.mli).
   - [--axiom-report-json FILE.vo]: one JSON document for the keep rule's
     monotone axiom condition (schema "rocq-library-label/axiom-report",
     version 4): the library name, the label kind and the hex [--check]
     prints, the constants whose label contribution the axiom-or-opaque
     blinding erased (each with its current "axiom" or "proof" status), the
     libraries this one holds a foreign opaque reference into, and its
     [keepfacts] segment: "assumptions" (an object from each declaration's
     user name to its sorted assumption closure, empty closures left out; null
     when absent) and "opacity_queries" (each foreign constant a strategy
     command, an extraction, a Functional Scheme (its equation lemma) or a
     plugin's Global.body_of_constant told apart as an axiom or an opaque
     proof, or whose opaque body an extraction or Global.body_of_constant
     read; and each constant of this library whose opaque body one of those,
     or the walk that computes the closures, read from another library's
     table; by user name, with the library
     holding it, the opacity it saw, and "table": for a body read, the
     library whose opaque table holds the body read, else null; null when the
     file has no segment). A body read records both the holder and the table:
     for a copy a module operation did not strengthen they can differ, and the
     keep rule requires both libraries' objects byte-identical.
     "foreign_opaque_libraries" does not cover body reads: a sealed
     [Module X : T := L.F A] keeps its expression, which holds no reference,
     and a non-OCaml extraction, or the closure walk, reads the table of the
     library F's proof comes from through it. Version 4 adds "table".
     A segment that does not validate against checker/values.ml's
     description of it reads as absent ([read_keep_facts]). Version 3 drops
     version 2's "copied_from_libraries", which nothing read. Whether a
     constant copied by a module operation keeps a reference into its
     source library's opaque table depends on the operation and on where
     the constant sits: the kernel strengthens some copies to transparent
     definitions (kernel/modops.ml, [strengthen_const]) and only
     substitutes others, such as a functor application or a functor or
     module type nested at any depth. "foreign_opaque_libraries" does not
     rest on any such classification: it is computed from every constant
     of the compiled library, functor bodies, module types and
     implementations included, so it names every other library whose
     opaque table any copy references (misc/library-label-opaque-shift.sh checks
     a functor application, an [Include F A0] and an [Include] of a plain
     module, which holds none; the DI and DM cases of
     misc/library-label-functor-flip.sh show an [Include] of a functor
     application and a module declared with a module type are refused like
     the application). An [Admitted -> Qed] edit in a functor body or a
     module type moves its owner's label (label version 5).
   Three modes describe this build and take no file:
   - [--layout-version]: the label's layout version
     ([LibkeyObjects.version]), one line. A reader that keeps labels across
     builds compares them only within one layout version.
   - [--vmlibrary-format-version]: the number that names the format of the
     VM-bytecode segment this build reads and writes
     ([LibkeyObjects.vmlibrary_format_version]), one line, read by
     test-suite/misc/library-label-vmlibrary.sh against the first word of
     that segment in a library this build wrote.
   - [--vo-representation]: how this build represents what a .vo stores
     (see [vo_representation] below), read by test-suite/misc/vo-format.sh.
   Exit 0; 1 when the file cannot be read as a .vo file; 2 on a usage error;
   3 when --attempts-json meets a string that is not valid UTF-8.
   Rocq's toplevel and every one of its plugins are linked in (-linkall),
   so the object kinds registered here are the ones a library's compile
   registers; the checker's value schema is linked for
   [--vo-representation]. *)

let hex s =
  String.concat "" (List.init (String.length s) (fun i -> Printf.sprintf "%02x" (Char.code s.[i])))

let usage () =
  prerr_endline "usage: rocq-library-label (--check | --stored | --attempts | --attempts-json | --axiom-report-json) FILE.vo";
  prerr_endline "       rocq-library-label (--layout-version | --vmlibrary-format-version | --vo-representation)";
  exit 2

(* The label kind [--check] prints, and the hex it prints beside it: the full
   32-byte label for [label2], otherwise the stored digest. *)
let check_kind (l : Library.file_label) =
  match Lazy.force l.label with
  | Ok label when String.equal (Libkey.stored label) l.stored -> ("label2", hex label)
  | Ok _ | Error _ ->
    if String.equal (Lazy.force l.segment_md5) l.stored then ("md5", hex l.stored)
    else ("other", hex l.stored)

(* A JSON string: the small ASCII identifiers and dotted paths here never need
   more, but quotes, backslashes and controls are escaped so a surprising name
   cannot break the document. *)
let json_string b s =
  Buffer.add_char b '"';
  String.iter (function
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | c when Char.code c < 0x20 -> Printf.bprintf b "\\u%04x" (Char.code c)
      | c -> Buffer.add_char b c) s;
  Buffer.add_char b '"'

module Values = Coq_checklib.Values

(* The file's [keepfacts] segment, its bytes checked against their digest,
   then parsed and validated against the checker's description of it
   ([Values.v_keepfacts]) before it is unmarshalled, as rocqchk reads the
   segments it reads ([CheckLibrary.marshal_in_segment]). [coqc] writes it
   with no digest of its own ([Library.save_library_base]), so the digest the
   segment table and the segment's end store is the MD5 of its bytes, and a
   changed byte is caught here rather than read as another value. [None] when
   the file has none, or when the segment's bytes do not match that digest,
   it does not parse, or it is not the shape that description gives: the
   report then says null, which makes the keep rule rebuild, and standard
   error says why. *)
let read_keep_facts f (l : Library.file_label) : KeepFacts.t option =
  match l.Library.keep_facts_segment with
  | None -> None
  | Some seg ->
    let absent why =
      prerr_endline ("rocq-library-label: " ^ f ^ ": keepfacts segment read as absent: " ^ why);
      None in
    let bytes_digest ch =
      LargeFile.seek_in ch seg.ObjFile.pos;
      Digest.channel ch (Int64.to_int seg.ObjFile.len)
    in
    let parse ch =
      LargeFile.seek_in ch seg.ObjFile.pos;
      let v = Coq_checklib.Analyze.parse_channel ch in
      (v, Digest.input ch)
    in
    In_channel.with_open_bin f (fun ch ->
        match bytes_digest ch with
        | exception e when CErrors.noncritical e -> absent ("unreadable: " ^ Printexc.to_string e)
        | d when not (String.equal d seg.ObjFile.hash) ->
          absent "its bytes do not match its digest"
        | _ ->
          match parse ch with
          | exception e when CErrors.noncritical e -> absent ("unreadable: " ^ Printexc.to_string e)
          | (_, digest) when not (String.equal digest seg.ObjFile.hash) ->
            absent "its digest does not match the segment table"
          | (v, _) ->
            match Coq_checklib.Validate.check Values.v_keepfacts v with
            | Error why -> absent ("not the shape checker/values.ml describes: " ^ why)
            | Ok () -> Some (Obj.obj (Coq_checklib.Analyze.instantiate v) : KeepFacts.t))

let axiom_report_json file (l : Library.file_label) =
  let r = Lazy.force l.axiom_report in
  let kind, lhex = check_kind l in
  let b = Buffer.create 1024 in
  let comma = ref false in
  let field k f = (if !comma then Buffer.add_char b ','); comma := true;
    json_string b k; Buffer.add_char b ':'; f () in
  Buffer.add_char b '{';
  field "schema" (fun () -> json_string b "rocq-library-label/axiom-report");
  field "version" (fun () -> Buffer.add_string b "4");
  field "library" (fun () -> json_string b (Names.DirPath.to_string l.name));
  field "label_kind" (fun () -> json_string b kind);
  field "label" (fun () -> json_string b lhex);
  field "axiom_blind" (fun () ->
      Buffer.add_char b '[';
      List.iteri (fun i (c, status) ->
          if i > 0 then Buffer.add_char b ',';
          Buffer.add_char b '{';
          json_string b "constant"; Buffer.add_char b ':';
          json_string b (Names.Constant.to_string c);
          Buffer.add_char b ',';
          json_string b "status"; Buffer.add_char b ':';
          json_string b (match status with LibkeyObjects.Axiom -> "axiom" | LibkeyObjects.Proof -> "proof");
          Buffer.add_char b '}')
        r.LibkeyObjects.blinded;
      Buffer.add_char b ']');
  field "foreign_opaque_libraries" (fun () ->
      Buffer.add_char b '[';
      List.iteri (fun i dp ->
          if i > 0 then Buffer.add_char b ',';
          json_string b (Names.DirPath.to_string dp))
        (Names.DirPath.Set.elements r.LibkeyObjects.foreign_opaque_libraries);
      Buffer.add_char b ']');
  let strings l =
    Buffer.add_char b '[';
    List.iteri (fun i s -> if i > 0 then Buffer.add_char b ','; json_string b s) l;
    Buffer.add_char b ']' in
  (* The [keepfacts] segment: null when the file has none or it does not
     validate (the keep rule then rebuilds), or when the closure could not be
     computed. *)
  let facts = read_keep_facts file l in
  field "assumptions" (fun () ->
      match facts with
      | Some { KeepFacts.assumptions = Some a; _ } ->
        Buffer.add_char b '{';
        List.iteri (fun i (name, keys) ->
            if i > 0 then Buffer.add_char b ',';
            json_string b name; Buffer.add_char b ':'; strings keys)
          a;
        Buffer.add_char b '}'
      | _ -> Buffer.add_string b "null");
  field "opacity_queries" (fun () ->
      match facts with
      | None -> Buffer.add_string b "null"
      | Some { KeepFacts.opacity_queries = q; _ } ->
        Buffer.add_char b '[';
        List.iteri (fun i { KeepFacts.constant; library; opaque; table } ->
            let opt = function Some d -> json_string b d | None -> Buffer.add_string b "null" in
            if i > 0 then Buffer.add_char b ',';
            Buffer.add_char b '{';
            json_string b "constant"; Buffer.add_char b ':'; json_string b constant;
            Buffer.add_char b ',';
            json_string b "library"; Buffer.add_char b ':'; opt library;
            Buffer.add_char b ',';
            json_string b "opaque"; Buffer.add_char b ':';
            Buffer.add_string b (if opaque then "true" else "false");
            Buffer.add_char b ',';
            json_string b "table"; Buffer.add_char b ':'; opt table;
            Buffer.add_char b '}')
          q;
        Buffer.add_char b ']');
  Buffer.add_char b '}';
  Buffer.contents b

(* The representation of the values this build writes into a .vo
   ([--vo-representation]), in three parts:
   - the kernel part: the structure of every segment of a .vo as the
     checker describes it (checker/values.ml): per type, its constructors
     with an argument, their arity and their order, and the number of its
     constant constructors. A constructor with an argument added, removed
     or moved, or a field added to a record, changes this printing, and a
     build that reads a .vo written by a build with another printing can
     read a value as the wrong constructor. Two constant constructors
     swapped do not change it: the printing counts them. For the summary,
     library and opaques segments the description is what rocqchk
     validates a file against at load; for vmlibrary it is a description
     only, because this fork's rocqchk regenerates the bytecode and never
     reads that segment (checker/checkLibrary.ml), so nothing checks that
     description against what the kernel writes: a kernel change that
     leaves checker/values.ml as it is leaves this printing as it is;
   - the object part: the name of every object kind registered in this
     build ([Libobject.dump], with every plugin and the toplevel linked
     in), which is what the object segments of a .vo can hold. A kind
     added, removed or renamed changes this printing; a kind only this
     build has is the one difference misc/vo-format.sh lets pass;
   - the payload part ([Payload_types.payloads], printed at build time by
     checker/vo_payloads.ml from the typed trees of those same
     directories, and embedded here): the OCaml type of the value each of
     those kinds stores, with the definition of every type it reaches. A
     field added to a payload's record, a constructor renamed or moved, a
     type alias changed underneath, all change this printing. What it does
     not reach it prints rather than drops, each with a token that says
     why; the list of those tokens, and what each one means, is at the head
     of checker/vo_payloads.ml, which is the one place it is written down.
     The element type of each [Goptions] table is one of its lines
     ([table_payload]), since the functor's body names it only through its
     parameter;
   - the option part ([option_payload], from [Goptions.get_tables]): which
     of the four types of [Goptions.option_kind] each declared option
     stores, which the payload part cannot say because every option is
     registered from one reference, at the type its caller chooses.
   What no part reaches: the value behind a [Dyn] tag (a stored Ltac
   expression is pinned down to its generic arguments and no further), the
   meaning of a string, the bytecode of the vmlibrary segment among them,
   and the order of a type's constant constructors in the kernel part (the
   payload part prints them in order). A change there shows up here only
   when it moves a kernel type, a kind name or a payload type. *)

(* The schema is a graph: [Values.fix] makes cyclic values, and a node can
   be reached from several places. It is printed one node per line, [#n =
   kind(...)], with every sub-value named by its own [#n].

   Two nodes get one number when they print the same with their children's
   numbers, computed by refining a partition that starts with every node
   together. The printing then says what the schema is, not how the build
   happens to share it: [checker/values.ml] builds equal nodes in several
   places ([v_set], [v_map]), and whether those are one OCaml value is
   decided by the compiler's flags rather than by the source -- with
   [-O3 -unbox-closures], the flags of dune's release profile, flambda
   shares nodes it leaves apart without them -- so numbering by physical
   identity would fail this test on a release build alone.

   Numbers follow the order the walk first meets a class, so a changed node
   whose children all have numbers changes one line, while a node added or
   removed renumbers every class met after it: in a long diff, the first
   changed line is the change. *)
let print_schema b (v : Values.value) =
  (* The nodes, in the order the walk meets them. [Values.equal], the
     equality the checker's own walk uses (checker/validate.ml), reads a
     [Values.fix] proxy as its content, so the walk ends on a cyclic
     schema. *)
  let seen = ref [] and count = ref 0 and rev = ref [] in
  let todo = Queue.create () in
  let id v =
    match List.find_opt (fun (w, _) -> Values.equal w v) !seen with
    | Some (_, n) -> n
    | None ->
      let n = !count in
      incr count; seen := (v, n) :: !seen; rev := v :: !rev; Queue.add v todo; n
  in
  let root = id v in
  while not (Queue.is_empty todo) do
    let child v = ignore (id v) in
    match Values.kind (Queue.pop todo) with
    | Values.Any | Values.Fail _ | Values.Int | Values.Int64 | Values.Float64
    | Values.String -> ()
    | Values.Array v | Values.List v | Values.Opt v | Values.Annot (_, v) -> child v
    | Values.Tuple (_, fields) -> Array.iter child fields
    | Values.Sum (_, _, variants) -> Array.iter (Array.iter child) variants
  done;
  let nodes = Array.of_list (List.rev !rev) in
  let cls = Array.make (Array.length nodes) 0 in
  let render out v =
    let ref_ v = Printf.bprintf out "#%d" cls.(id v) in
    let refs vs = Array.iteri (fun i v -> if i > 0 then Buffer.add_char out ','; ref_ v) vs in
    let unary name v = Printf.bprintf out "%s(" name; ref_ v; Buffer.add_char out ')' in
    match Values.kind v with
    | Values.Any -> Buffer.add_string out "any"
    | Values.Fail s -> Printf.bprintf out "fail(%s)" s
    | Values.Int -> Buffer.add_string out "int"
    | Values.Int64 -> Buffer.add_string out "int64"
    | Values.Float64 -> Buffer.add_string out "float64"
    | Values.String -> Buffer.add_string out "string"
    | Values.Array v -> unary "array" v
    | Values.List v -> unary "list" v
    | Values.Opt v -> unary "opt" v
    | Values.Annot (s, v) -> Printf.bprintf out "annot(%s," s; ref_ v; Buffer.add_char out ')'
    | Values.Tuple (name, fields) ->
      Printf.bprintf out "tuple(%s,%d," name (Array.length fields); refs fields;
      Buffer.add_char out ')'
    | Values.Sum (name, nconst, variants) ->
      Printf.bprintf out "sum(%s,%d,%d," name nconst (Array.length variants);
      Array.iteri (fun i fields ->
          if i > 0 then Buffer.add_char out ';';
          Printf.bprintf out "%d:" (Array.length fields); refs fields)
        variants;
      Buffer.add_char out ')'
  in
  (* One refinement round. A node's key is its class and its printing with
     this round's classes, so a class only ever splits and the rounds end.
     The new classes are numbered in node order, the order the walk met
     them. *)
  let refine () =
    let key i =
      let out = Buffer.create 64 in
      Printf.bprintf out "%d|" cls.(i); render out nodes.(i); Buffer.contents out
    in
    let tbl = Hashtbl.create 97 and next = ref 0 in
    let fresh = Array.make (Array.length nodes) 0 in
    Array.iteri (fun i _ ->
        let k = key i in
        fresh.(i) <-
          (match Hashtbl.find_opt tbl k with
           | Some c -> c
           | None -> let c = !next in incr next; Hashtbl.add tbl k c; c))
      nodes;
    let changed = fresh <> cls in
    Array.blit fresh 0 cls 0 (Array.length cls);
    changed
  in
  while refine () do () done;
  Printf.bprintf b "root #%d\n" cls.(root);
  let printed = Hashtbl.create 97 in
  Array.iteri (fun i v ->
      if not (Hashtbl.mem printed cls.(i)) then begin
        Hashtbl.add printed cls.(i) ();
        Printf.bprintf b "  #%d = " cls.(i); render b v; Buffer.add_char b '\n'
      end)
    nodes

(* Which of the four types of [Goptions.option_kind] each declared option
   stores. The payload part cannot say: all options are registered from one
   reference ([Goptions.declare_option]), at a type its caller chooses, so
   its line is [payload_unresolved]. The option's current value carries its
   kind, and every option of this build is declared by the time this runs
   (the same initialisers that register the kinds above), so the two halves
   together pin what an object of an option kind holds. *)
let option_payloads b =
  let stored (state : Goptions.option_state) =
    match state.Goptions.opt_value with
    | Goptions.BoolValue _ -> "bool"
    | Goptions.IntValue _ -> "int option"
    | Goptions.StringValue _ -> "string"
    | Goptions.StringOptValue _ -> "string option"
  in
  List.iter (fun l -> Buffer.add_string b l; Buffer.add_char b '\n')
    (List.sort String.compare
       (Goptions.OptionMap.fold
          (fun key state acc ->
             Printf.sprintf "option_payload %s %s"
               (String.concat " " key) (stored state)
             :: acc)
          (Goptions.get_tables ()) []))

let vo_representation () =
  let b = Buffer.create 8192 in
  Buffer.add_string b "rocq-vo-representation 1\n";
  Printf.bprintf b "vo_version %ld\n" Coq_config.vo_version;
  List.iter (fun k -> Printf.bprintf b "object_kind %s\n" k)
    (List.sort String.compare (List.map snd (Libobject.dump ())));
  Buffer.add_string b Payload_types.payloads;
  option_payloads b;
  List.iter (fun (segment, v) ->
      Printf.bprintf b "segment %s " segment; print_schema b v)
    Values.vo_segments;
  Buffer.contents b

let read f =
  match Library.read_file_label f with
  | l -> l
  | exception e ->
    prerr_endline ("rocq-library-label: cannot read " ^ f ^ ": " ^ Printexc.to_string e);
    exit 1

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [mode; f] ->
    begin match mode with
    | "--check" ->
      let kind, lhex = check_kind (read f) in Printf.printf "%s %s\n" kind lhex
    | "--stored" -> print_endline (hex (read f).stored)
    | "--attempts" ->
      begin match (read f).attempts with
      | None -> print_endline "no attempts"
      | Some t -> List.iter print_endline (Attempts.describe t)
      end
    | "--attempts-json" ->
      begin match Attempts.to_json (read f).attempts with
      | Ok j -> print_endline j
      | Error what -> prerr_endline ("rocq-library-label: " ^ f ^ ": " ^ what); exit 3
      end
    | "--axiom-report-json" -> print_endline (axiom_report_json f (read f))
    | _ -> usage ()
    end
  | ["--layout-version"] -> Printf.printf "%d\n" LibkeyObjects.version
  | ["--vmlibrary-format-version"] ->
    Printf.printf "%d\n" LibkeyObjects.vmlibrary_format_version
  | ["--vo-representation"] -> print_string (vo_representation ())
  | _ -> usage ()
