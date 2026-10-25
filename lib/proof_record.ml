(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let format_version = 1

type toolchain = {
  binary : string;
  plugins : (string * string) list;
  load_order : (string * string) list;
  warnings : string;
  safe_deps : string list;
  stack_limit : string;
}

type header = {
  version : int;
  library : string;
  source : string;
  source_digest : string;
  toolchain : toolchain;
  memory_cap : string;
  rlimit_as : string;
  rlimit_data : string;
  overcommit_memory : string;
  skip_qed_typecheck : bool;
  tables_at_start : bool;
}

type toolchain_key = {
  binary : string;
  plugins : string;
  load_order : string;
  warnings : string;
  safe_deps : string;
  stack_limit : string;
}

type position = { module_path : string; section_path : string }

type ineligible = { reason : string; detail : string }

type read = { row : string; channel : string; key : string; value : string option }

type writes = {
  universe_levels : string list;
  counters : (string * int) list;
  constraints : string list;
  schemes : string list;
  constraint_sources : string list;
  warnings_raised : (string * string) list;
}

type proof = {
  name : string;
  statement : string;
  sentences : string;
  closer : string;
  toolchain_key : toolchain_key;
  position : position;
  ineligible : ineligible list;
  reads : read list;
  start_tables : read list;
  writes : writes;
  kernel_check : bool;
  wall_s : float;
  cpu_s : float;
}

type trailer = { file_wall_s : float; file_cpu_s : float; peak_rss_kb : int; proof_count : int }

type file = { header : header; proofs : proof list; trailer : trailer }

(** {6 JSON writing} *)

let replacement_char = "\xef\xbf\xbd"

let add_string b s =
  Buffer.add_char b '"';
  let n = String.length s in
  let rec loop i =
    if i < n then begin
      let c = s.[i] in
      match c with
      | '"' -> Buffer.add_string b "\\\""; loop (i + 1)
      | '\\' -> Buffer.add_string b "\\\\"; loop (i + 1)
      | '\n' -> Buffer.add_string b "\\n"; loop (i + 1)
      | '\r' -> Buffer.add_string b "\\r"; loop (i + 1)
      | '\t' -> Buffer.add_string b "\\t"; loop (i + 1)
      | '\000' .. '\031' | '\127' -> Printf.bprintf b "\\u%04x" (Char.code c); loop (i + 1)
      | '\032' .. '\126' -> Buffer.add_char b c; loop (i + 1)
      | '\128' .. '\255' ->
        let d = String.get_utf_8_uchar s i in
        let len = Uchar.utf_decode_length d in
        if Uchar.utf_decode_is_valid d then Buffer.add_substring b s i len
        else Buffer.add_string b replacement_char;
        loop (i + len)
    end
  in
  loop 0;
  Buffer.add_char b '"'

let add_float b f =
  if not (Float.is_finite f) then invalid_arg "Proof_record: a float field is not finite";
  let shortest =
    let s15 = Printf.sprintf "%.15g" f in
    if float_of_string s15 = f then s15
    else
      let s16 = Printf.sprintf "%.16g" f in
      if float_of_string s16 = f then s16 else Printf.sprintf "%.17g" f
  in
  Buffer.add_string b shortest

let add_list add b l =
  Buffer.add_char b '[';
  List.iteri (fun i x -> if i > 0 then Buffer.add_char b ','; add b x) l;
  Buffer.add_char b ']'

let add_pair add_a add_b b (x, y) =
  Buffer.add_char b '['; add_a b x; Buffer.add_char b ','; add_b b y; Buffer.add_char b ']'

let add_int b n = Buffer.add_string b (string_of_int n)
let add_bool b v = Buffer.add_string b (if v then "true" else "false")
let add_option add b = function None -> Buffer.add_string b "null" | Some x -> add b x

(** [add_object b fields] writes [{"k1":v1,...}]; each field writes its own value. *)
let add_object b fields =
  Buffer.add_char b '{';
  List.iteri (fun i (k, add_v) ->
      if i > 0 then Buffer.add_char b ',';
      add_string b k; Buffer.add_char b ':'; add_v b)
    fields;
  Buffer.add_char b '}'

let field k add v = (k, fun b -> add b v)

let add_string_pairs = add_list (add_pair add_string add_string)

let add_toolchain b (t : toolchain) =
  add_object b [
    field "binary" add_string t.binary;
    field "plugins" add_string_pairs t.plugins;
    field "load_order" add_string_pairs t.load_order;
    field "warnings" add_string t.warnings;
    field "safe_deps" (add_list add_string) t.safe_deps;
    field "stack_limit" add_string t.stack_limit;
  ]

let add_toolchain_key b (k : toolchain_key) =
  add_object b [
    field "binary" add_string k.binary;
    field "plugins" add_string k.plugins;
    field "load_order" add_string k.load_order;
    field "warnings" add_string k.warnings;
    field "safe_deps" add_string k.safe_deps;
    field "stack_limit" add_string k.stack_limit;
  ]

let add_position b p =
  add_object b [ field "module_path" add_string p.module_path; field "section_path" add_string p.section_path ]

let add_ineligible b i = add_object b [ field "reason" add_string i.reason; field "detail" add_string i.detail ]

let add_read b r =
  add_object b [
    field "row" add_string r.row;
    field "channel" add_string r.channel;
    field "key" add_string r.key;
    field "value" (add_option add_string) r.value;
  ]

let add_writes b w =
  add_object b [
    field "universe_levels" (add_list add_string) w.universe_levels;
    field "counters" (add_list (add_pair add_string add_int)) w.counters;
    field "constraints" (add_list add_string) w.constraints;
    field "schemes" (add_list add_string) w.schemes;
    field "constraint_sources" (add_list add_string) w.constraint_sources;
    field "warnings_raised" add_string_pairs w.warnings_raised;
  ]

let kind k = field "kind" add_string k

let output_header b h =
  add_object b [
    kind "header";
    field "version" add_int h.version;
    field "library" add_string h.library;
    field "source" add_string h.source;
    field "source_digest" add_string h.source_digest;
    field "toolchain" add_toolchain h.toolchain;
    field "memory_cap" add_string h.memory_cap;
    field "rlimit_as" add_string h.rlimit_as;
    field "rlimit_data" add_string h.rlimit_data;
    field "overcommit_memory" add_string h.overcommit_memory;
    field "skip_qed_typecheck" add_bool h.skip_qed_typecheck;
    field "tables_at_start" add_bool h.tables_at_start;
  ];
  Buffer.add_char b '\n'

let output_proof b p =
  add_object b [
    kind "proof";
    field "name" add_string p.name;
    field "statement" add_string p.statement;
    field "sentences" add_string p.sentences;
    field "closer" add_string p.closer;
    field "toolchain_key" add_toolchain_key p.toolchain_key;
    field "position" add_position p.position;
    field "ineligible" (add_list add_ineligible) p.ineligible;
    field "reads" (add_list add_read) p.reads;
    field "start_tables" (add_list add_read) p.start_tables;
    field "writes" add_writes p.writes;
    field "kernel_check" add_bool p.kernel_check;
    field "wall_s" add_float p.wall_s;
    field "cpu_s" add_float p.cpu_s;
  ];
  Buffer.add_char b '\n'

let output_trailer b t =
  add_object b [
    kind "trailer";
    field "file_wall_s" add_float t.file_wall_s;
    field "file_cpu_s" add_float t.file_cpu_s;
    field "peak_rss_kb" add_int t.peak_rss_kb;
    field "proof_count" add_int t.proof_count;
  ];
  Buffer.add_char b '\n'

let digest_json add v =
  let b = Buffer.create 256 in
  add b v;
  Digest.to_hex (Digest.string (Buffer.contents b))

(* The key of one toolchain record, kept for as long as the caller hands back
   the same record. Every proof asks for it, and the three digests walk three
   lists, so a compile of many proofs would otherwise pay that walk for each
   of them. The caller ({!Proof_record_env.toolchain}) returns one physical
   record while no library, no plugin and no warning flag has moved. *)
let toolchain_key_memo : (toolchain * toolchain_key) option ref = ref None

let toolchain_key (t : toolchain) : toolchain_key =
  match !toolchain_key_memo with
  | Some (t0, k) when t0 == t -> k
  | Some _ | None ->
    let k = {
      binary = t.binary;
      plugins = digest_json add_string_pairs t.plugins;
      load_order = digest_json add_string_pairs t.load_order;
      warnings = t.warnings;
      safe_deps = digest_json (add_list add_string) t.safe_deps;
      stack_limit = t.stack_limit;
    } in
    toolchain_key_memo := Some (t, k);
    k

let path_of_vo vo =
  let base = match Filename.chop_suffix_opt ~suffix:".vo" vo with Some b -> b | None -> vo in
  base ^ ".proof-record.jsonl"

(** {6 JSON reading} *)

exception Parse_error of string

type json =
  | Null
  | Bool of bool
  | Num of string
  | Str of string
  | Arr of json list
  | Obj of (string * json) list

let fail fmt = Printf.ksprintf (fun s -> raise (Parse_error s)) fmt

let add_utf_8 b code =
  if code < 0 || code > 0x10ffff || (code >= 0xd800 && code <= 0xdfff) then fail "invalid code point %x" code;
  Buffer.add_utf_8_uchar b (Uchar.of_int code)

(** Parses one JSON value that fills the whole of [s]. *)
let parse_json s =
  let n = String.length s in
  let pos = ref 0 in
  let peek () = if !pos < n then s.[!pos] else '\000' in
  let err what = fail "%s at byte %d" what !pos in
  let rec skip_ws () =
    match peek () with ' ' | '\t' | '\r' when !pos < n -> incr pos; skip_ws () | _ -> ()
  in
  let expect c = if peek () = c && !pos < n then incr pos else err (Printf.sprintf "expected '%c'" c) in
  let literal word v =
    let l = String.length word in
    if !pos + l <= n && String.sub s !pos l = word then (pos := !pos + l; v) else err "bad literal"
  in
  let hex4 () =
    if !pos + 4 > n then err "short \\u escape";
    match int_of_string_opt ("0x" ^ String.sub s !pos 4) with
    | Some v when String.for_all (function '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true | _ -> false)
                    (String.sub s !pos 4) ->
      pos := !pos + 4; v
    | _ -> err "bad \\u escape"
  in
  let parse_string () =
    expect '"';
    let b = Buffer.create 16 in
    let rec loop () =
      if !pos >= n then err "unterminated string";
      let c = s.[!pos] in
      incr pos;
      match c with
      | '"' -> ()
      | '\\' ->
        if !pos >= n then err "unterminated escape";
        let e = s.[!pos] in
        incr pos;
        (match e with
         | '"' -> Buffer.add_char b '"'
         | '\\' -> Buffer.add_char b '\\'
         | '/' -> Buffer.add_char b '/'
         | 'b' -> Buffer.add_char b '\b'
         | 'f' -> Buffer.add_char b '\012'
         | 'n' -> Buffer.add_char b '\n'
         | 'r' -> Buffer.add_char b '\r'
         | 't' -> Buffer.add_char b '\t'
         | 'u' ->
           let hi = hex4 () in
           if hi >= 0xd800 && hi <= 0xdbff then begin
             if !pos + 2 <= n && s.[!pos] = '\\' && s.[!pos + 1] = 'u' then begin
               pos := !pos + 2;
               let lo = hex4 () in
               if lo < 0xdc00 || lo > 0xdfff then err "bad surrogate pair";
               add_utf_8 b (0x10000 + ((hi - 0xd800) lsl 10) + (lo - 0xdc00))
             end else err "lone surrogate"
           end else add_utf_8 b hi
         | _ -> err "bad escape");
        loop ()
      | '\000' .. '\031' -> err "control character in string"
      | _ -> Buffer.add_char b c; loop ()
    in
    loop ();
    let r = Buffer.contents b in
    if not (String.is_valid_utf_8 r) then err "string is not UTF-8";
    r
  in
  let parse_number () =
    let start = !pos in
    while !pos < n && (match s.[!pos] with '-' | '+' | '.' | 'e' | 'E' | '0' .. '9' -> true | _ -> false) do
      incr pos
    done;
    if !pos = start then err "expected a value";
    Num (String.sub s start (!pos - start))
  in
  let rec value () =
    skip_ws ();
    let v =
      match peek () with
      | '{' ->
        incr pos; skip_ws ();
        if peek () = '}' then (incr pos; Obj [])
        else
          let rec members acc =
            skip_ws ();
            let k = parse_string () in
            skip_ws (); expect ':';
            let v = value () in
            skip_ws ();
            match peek () with
            | ',' -> incr pos; members ((k, v) :: acc)
            | '}' -> incr pos; Obj (List.rev ((k, v) :: acc))
            | _ -> err "expected ',' or '}'"
          in
          members []
      | '[' ->
        incr pos; skip_ws ();
        if peek () = ']' then (incr pos; Arr [])
        else
          let rec elements acc =
            let v = value () in
            skip_ws ();
            match peek () with
            | ',' -> incr pos; elements (v :: acc)
            | ']' -> incr pos; Arr (List.rev (v :: acc))
            | _ -> err "expected ',' or ']'"
          in
          elements []
      | '"' -> Str (parse_string ())
      | 't' -> literal "true" (Bool true)
      | 'f' -> literal "false" (Bool false)
      | 'n' -> literal "null" Null
      | _ -> parse_number ()
    in
    skip_ws ();
    v
  in
  let v = value () in
  if !pos <> n then err "trailing bytes";
  v

(** Decoding, strict: an object must have exactly the expected fields, in order. *)

let fields what expected = function
  | Obj kvs ->
    let got = List.map fst kvs in
    if got <> expected then
      fail "%s: fields [%s], expected [%s]" what (String.concat "," got) (String.concat "," expected);
    List.map snd kvs
  | _ -> fail "%s: expected an object" what

let to_str what = function Str s -> s | _ -> fail "%s: expected a string" what
let to_bool what = function Bool v -> v | _ -> fail "%s: expected a boolean" what

let to_int what = function
  | Num s when String.for_all (function '-' | '0' .. '9' -> true | _ -> false) s ->
    (match int_of_string_opt s with Some v -> v | None -> fail "%s: integer out of range" what)
  | _ -> fail "%s: expected an integer" what

let to_float what = function
  | Num s -> (match float_of_string_opt s with Some v when Float.is_finite v -> v | _ -> fail "%s: bad number" what)
  | _ -> fail "%s: expected a number" what

let to_list what f = function Arr l -> List.map f l | _ -> fail "%s: expected an array" what

let to_pair what fa fb = function Arr [ a; b ] -> (fa a, fb b) | _ -> fail "%s: expected a pair" what

let to_option f = function Null -> None | v -> Some (f v)

let to_string_pairs what = to_list what (to_pair what (to_str what) (to_str what))

let to_toolchain v : toolchain =
  match fields "toolchain" [ "binary"; "plugins"; "load_order"; "warnings"; "safe_deps"; "stack_limit" ] v with
  | [ b; p; lo; w; sd; sl ] ->
    { binary = to_str "binary" b; plugins = to_string_pairs "plugins" p; load_order = to_string_pairs "load_order" lo;
      warnings = to_str "warnings" w; safe_deps = to_list "safe_deps" (to_str "safe_deps") sd;
      stack_limit = to_str "stack_limit" sl }
  | _ -> assert false

let to_toolchain_key v : toolchain_key =
  match fields "toolchain_key" [ "binary"; "plugins"; "load_order"; "warnings"; "safe_deps"; "stack_limit" ] v with
  | [ b; p; lo; w; sd; sl ] ->
    { binary = to_str "binary" b; plugins = to_str "plugins" p; load_order = to_str "load_order" lo;
      warnings = to_str "warnings" w; safe_deps = to_str "safe_deps" sd; stack_limit = to_str "stack_limit" sl }
  | _ -> assert false

let to_position v =
  match fields "position" [ "module_path"; "section_path" ] v with
  | [ m; s ] -> { module_path = to_str "module_path" m; section_path = to_str "section_path" s }
  | _ -> assert false

let to_ineligible v =
  match fields "ineligible" [ "reason"; "detail" ] v with
  | [ r; d ] -> { reason = to_str "reason" r; detail = to_str "detail" d }
  | _ -> assert false

let to_read v =
  match fields "read" [ "row"; "channel"; "key"; "value" ] v with
  | [ r; c; k; x ] ->
    { row = to_str "row" r; channel = to_str "channel" c; key = to_str "key" k; value = to_option (to_str "value") x }
  | _ -> assert false

let to_writes v =
  match fields "writes"
          [ "universe_levels"; "counters"; "constraints"; "schemes"; "constraint_sources"; "warnings_raised" ] v with
  | [ ul; c; cs; sc; src; w ] ->
    let strs what = to_list what (to_str what) in
    { universe_levels = strs "universe_levels" ul;
      counters = to_list "counters" (to_pair "counters" (to_str "counters") (to_int "counters")) c;
      constraints = strs "constraints" cs; schemes = strs "schemes" sc;
      constraint_sources = strs "constraint_sources" src; warnings_raised = to_string_pairs "warnings_raised" w }
  | _ -> assert false

let kind_of = function
  | Obj (("kind", Str k) :: _) -> k
  | _ -> fail "a line does not start with its \"kind\" field"

let to_header v =
  (match v with
   | Obj kvs ->
     (match List.assoc_opt "version" kvs with
      | Some ver when to_int "version" ver <> format_version ->
        fail "record format version %d, this reader reads version %d" (to_int "version" ver) format_version
      | _ -> ())
   | _ -> ());
  match fields "header"
          [ "kind"; "version"; "library"; "source"; "source_digest"; "toolchain"; "memory_cap"; "rlimit_as";
            "rlimit_data"; "overcommit_memory"; "skip_qed_typecheck"; "tables_at_start" ] v with
  | [ _; ver; lib; src; sd; tc; mc; ra; rd; om; sq; ts ] ->
    { version = to_int "version" ver; library = to_str "library" lib; source = to_str "source" src;
      source_digest = to_str "source_digest" sd; toolchain = to_toolchain tc; memory_cap = to_str "memory_cap" mc;
      rlimit_as = to_str "rlimit_as" ra; rlimit_data = to_str "rlimit_data" rd;
      overcommit_memory = to_str "overcommit_memory" om; skip_qed_typecheck = to_bool "skip_qed_typecheck" sq;
      tables_at_start = to_bool "tables_at_start" ts }
  | _ -> assert false

let to_proof v =
  match fields "proof"
          [ "kind"; "name"; "statement"; "sentences"; "closer"; "toolchain_key"; "position"; "ineligible"; "reads";
            "start_tables"; "writes"; "kernel_check"; "wall_s"; "cpu_s" ] v with
  | [ _; nm; st; se; cl; tk; po; ie; rd; sts; wr; kc; ws; cs ] ->
    { name = to_str "name" nm; statement = to_str "statement" st; sentences = to_str "sentences" se;
      closer = to_str "closer" cl; toolchain_key = to_toolchain_key tk; position = to_position po;
      ineligible = to_list "ineligible" to_ineligible ie; reads = to_list "reads" to_read rd;
      start_tables = to_list "start_tables" to_read sts; writes = to_writes wr;
      kernel_check = to_bool "kernel_check" kc; wall_s = to_float "wall_s" ws; cpu_s = to_float "cpu_s" cs }
  | _ -> assert false

let to_trailer v =
  match fields "trailer" [ "kind"; "file_wall_s"; "file_cpu_s"; "peak_rss_kb"; "proof_count" ] v with
  | [ _; w; c; r; n ] ->
    { file_wall_s = to_float "file_wall_s" w; file_cpu_s = to_float "file_cpu_s" c;
      peak_rss_kb = to_int "peak_rss_kb" r; proof_count = to_int "proof_count" n }
  | _ -> assert false

let parse_string text =
  let lines = String.split_on_char '\n' text in
  let rec split_last acc = function
    | [] -> fail "the record is empty"
    | [ "" ] -> List.rev acc
    | [ _ ] -> fail "the record does not end in a newline"
    | l :: rest -> split_last (l :: acc) rest
  in
  let lines = Array.of_list (split_last [] lines) in
  let count = Array.length lines in
  let line i =
    try parse_json lines.(i) with Parse_error m -> fail "line %d: %s" (i + 1) m
  in
  let in_line i f v = try f v with Parse_error m -> fail "line %d: %s" (i + 1) m in
  if count = 0 then fail "the record has no header";
  let first = line 0 in
  if in_line 0 kind_of first <> "header" then fail "line 1 is not the header";
  let header = in_line 0 to_header first in
  if count = 1 then fail "the record has no trailer";
  let last = line (count - 1) in
  if in_line (count - 1) kind_of last <> "trailer" then fail "the last line is not the trailer";
  let trailer = in_line (count - 1) to_trailer last in
  let proofs =
    List.init (count - 2) (fun j ->
        let i = j + 1 in
        let v = line i in
        if in_line i kind_of v <> "proof" then fail "line %d: expected a proof line" (i + 1);
        in_line i to_proof v)
  in
  if trailer.proof_count <> List.length proofs then
    fail "the trailer counts %d proofs, the record has %d" trailer.proof_count (List.length proofs);
  { header; proofs; trailer }

(** {6 Structural digest} *)

exception Unhashable of string

(* Each value has a canonical encoding, a prefix code:
   'i' int64             immediate
   's' len bytes         string
   'f' bits              float
   'a' n bits...         float array
   'c' len bytes         custom block, as marshalled
   'e' len bytes         extension constructor, by name
   'l'                   a Loc.t of the [~locs] source
   'b' tag size entry... a block encoded in place, with its fields
   'd' md5               a block of at least [min_memo_size] blocks, named by
                         the md5 of its 'b' encoding
   The digest of a value is the md5 of its entry. A block whose subtree has at
   least [min_memo_size] blocks is digested once and then named by that md5,
   so the cost is linear in the number of distinct blocks and the result does
   not depend on sharing. A smaller block is encoded in place at each of its
   occurrences, which costs at most [min_memo_size] blocks and keeps the memo
   small.

   The memo lives for the whole compile, not for one call. The global state is
   persistent: the universe graph after a proof shares all but one path with
   the graph before it, so a proof's digest of it costs that path and not the
   whole graph. The price is the same assumption {!Proof_recorder.digest_cached}
   already makes, one level deeper: a value that is digested must not be
   mutated in place afterwards. {!reset_memo} empties it with the recorder.

   The encoding is built bottom-up in one buffer, from what the walk itself
   computed, so it does not depend on what the memo finds: a memo miss costs
   a walk and never changes a digest. *)

(* The memo holds its keys STRONGLY, and is emptied above [max_memo_entries].
   Weak keys were tried and measured worse on both counts: an
   [Ephemeron.K1] table cost +45% CPU and 2.4 times the peak RSS of this
   table on a registration file, because its entries are released by the
   major collection's ephemeron pass, which a fast-allocating compile
   outruns, and every lookup pays the weak-key indirection (R1M1, speed-r1
   pinned, 2026-10-25: 62.17 s and 6,235 MB against 42.75 s and 2,628 MB).
   A bound on the table is what keeps its memory, not the GC. *)
module H = Hashtbl.Make (struct
    type t = Obj.t
    let equal = ( == )
    (* The block's address. A structural hash reads only a bounded prefix of a
       block, so the many distinct blocks of a long run of equal values (a
       memory image in a statement) all share one bucket, every lookup walks
       it, and a digest costs the square of its size: a registration file of
       477 proofs took 581 times its stock CPU, with 95.6% self time in the
       bucket walk (R1M1's profile). An address separates them. A block the GC
       moves after it was added is looked for in another bucket until the
       table grows: the lookup misses and the block is walked again, which
       costs time only. *)
    let hash (o : Obj.t) = (Obj.magic o : int) lsr 3
  end)

(* [Pending alive]: the block's walk started, and [!alive] while it is still
   on the walk's stack. A stale entry, left behind by a block that moved, has
   [alive] false and means nothing. *)
type memo = Pending of bool ref | Done of Digest.t * int

let max_blocks = 1 lsl 25

let min_memo_size = 32

(* The memo of every value digested without [~locs]. A [~locs] call uses its
   own: it encodes the locations of one source as a leaf.

   It holds a block of a value it has walked for as long as the compile, so it
   keeps that block alive. Most of what the recorder digests is global state,
   which is alive anyway; a proof's own statement is not. Above
   [max_memo_entries] the memo is emptied, which costs the next digest its
   incrementality and costs no correctness: a digest is a function of the
   value, not of the memo. *)
let global_memo : memo H.t = H.create 4096

(* Measured on a registration file whose statements carry memory images: at
   2^21 the peak RSS with the flag was 2,628 MB against 1,336 MB without it
   (R1M1). Each entry also holds its block alive, and a statement's blocks
   die with the proof, so the bound is what returns that memory. *)
let max_memo_entries = 1 lsl 18

let reset_memo () = H.reset global_memo

let add_len b n = Buffer.add_int64_le b (Int64.of_int n)

let rec unforward o =
  if Obj.is_block o && Obj.tag o = Obj.forward_tag then unforward (Obj.field o 0) else o

let is_string_field o i = let f = Obj.field o i in Obj.is_block f && Obj.tag f = Obj.string_tag

(* [src] is the [Loc.InFile] source as a block of tag 0: dirpath option, file. *)
let loc_matcher = function
  | None -> fun _ -> false
  | Some (Loc.ToplevelInput) -> invalid_arg "Proof_record.digest_value: ~locs must be an InFile source"
  | Some (Loc.InFile { dirpath; file }) ->
    let same_string o s = Obj.is_block o && Obj.tag o = Obj.string_tag && (Obj.obj o : string) = s in
    let same_source o =
      Obj.is_block o && Obj.tag o = 0 && Obj.size o = 2
      && same_string (Obj.field o 1) file
      && (let d = Obj.field o 0 in
          match dirpath with
          | None -> Obj.is_int d && (Obj.obj d : int) = 0
          | Some p -> Obj.is_block d && Obj.tag d = 0 && Obj.size d = 1 && same_string (Obj.field d 0) p)
    in
    (* A Loc.t is a record of 7 fields: its source, then 6 ints. *)
    fun o ->
      Obj.tag o = 0 && Obj.size o = 7
      && (let rec ints i = i >= 7 || (Obj.is_int (Obj.field o i) && ints (i + 1)) in ints 1)
      && same_source (Obj.field o 0)

let digest_value ?locs v =
  let is_loc = loc_matcher locs in
  let memo = match locs with
    | Some _ -> H.create 1024
    | None ->
      if H.length global_memo > max_memo_entries then H.reset global_memo;
      global_memo
  in
  let blocks = ref 0 in
  (* A [`Node] is walked and may get a digest of its own. Everything else is
     encoded where it stands. *)
  let classify o =
    if Obj.is_int o then `Leaf
    else
      let t = Obj.tag o in
      if t = Obj.string_tag || t = Obj.double_tag || t = Obj.double_array_tag || t = Obj.custom_tag then `Leaf
      else if t = Obj.closure_tag || t = Obj.infix_tag then raise (Unhashable "a closure")
      else if t = Obj.lazy_tag then raise (Unhashable "an unforced lazy value")
      else if t = Obj.object_tag then
        if Obj.size o >= 1 && is_string_field o 0 then `Leaf else raise (Unhashable "an object")
      else if t = Obj.abstract_tag then raise (Unhashable "an abstract block")
      else if t >= Obj.no_scan_tag then raise (Unhashable (Printf.sprintf "a block of tag %d" t))
      else if is_loc o then `Leaf
      else `Node
  in
  let add_header b o =
    Buffer.add_char b 'b'; Buffer.add_char b (Char.chr (Obj.tag o)); add_len b (Obj.size o)
  in
  (* The entry of a [`Leaf]. *)
  let add_leaf b o =
    if Obj.is_int o then (Buffer.add_char b 'i'; Buffer.add_int64_le b (Int64.of_int (Obj.obj o : int)))
    else
      let t = Obj.tag o in
      if t = Obj.string_tag then begin
        let s : string = Obj.obj o in
        Buffer.add_char b 's'; add_len b (String.length s); Buffer.add_string b s
      end
      else if t = Obj.double_tag then (Buffer.add_char b 'f'; Buffer.add_int64_le b (Int64.bits_of_float (Obj.obj o)))
      else if t = Obj.double_array_tag then begin
        let a : float array = Obj.obj o in
        Buffer.add_char b 'a'; add_len b (Array.length a);
        Array.iter (fun x -> Buffer.add_int64_le b (Int64.bits_of_float x)) a
      end
      else if t = Obj.custom_tag then begin
        let m = try Marshal.to_string o [] with Invalid_argument _ | Failure _ ->
          raise (Unhashable "a custom block that cannot be marshalled") in
        Buffer.add_char b 'c'; add_len b (String.length m); Buffer.add_string b m
      end
      else if t = Obj.object_tag then begin
        let name : string = Obj.obj (Obj.field o 0) in
        Buffer.add_char b 'e'; add_len b (String.length name); Buffer.add_string b name
      end
      else (* a Loc.t of the [~locs] source *) Buffer.add_char b 'l'
  in
  (* One buffer for the whole walk. Each block on the stack owns the tail of
     it from its [start]: its header, then the entry of each field visited so
     far. When the block ends, its tail becomes its own entry. *)
  let buf = Buffer.create 256 in
  let stack = Stack.create () in
  (* Adds the entry of [o], a [`Node], when the memo knows it, and returns the
     size of its subtree; otherwise starts its walk and returns 0, and the walk
     adds the size when the block ends. *)
  let enter o =
    match H.find_opt memo o with
    | Some (Done (d, n)) -> Buffer.add_char buf 'd'; Buffer.add_string buf d; n
    | Some (Pending alive) when !alive -> raise (Unhashable "a cycle")
    | Some (Pending _) | None ->
      incr blocks;
      if !blocks > max_blocks then raise (Unhashable "more than 2^25 distinct blocks");
      let alive = ref true in
      H.replace memo o (Pending alive);
      let start = Buffer.length buf in
      add_header buf o;
      Stack.push (o, ref 0, ref 0, start, alive) stack;
      0
  in
  let finish o start size =
    if size < min_memo_size then H.remove memo o
    else begin
      let d = Digest.string (Buffer.sub buf start (Buffer.length buf - start)) in
      Buffer.truncate buf start;
      Buffer.add_char buf 'd'; Buffer.add_string buf d;
      H.replace memo o (Done (d, size))
    end
  in
  (* Post-order walk with an explicit stack: deep values do not overflow. Each
     frame counts the blocks of its own subtree, so that [finish] knows whether
     the block is worth a digest of its own. *)
  let root = unforward (Obj.repr v) in
  let run () =
    (match classify root with
     | `Leaf -> add_leaf buf root
     | `Node -> ignore (enter root));
    while not (Stack.is_empty stack) do
      let o, i, acc, start, alive = Stack.top stack in
      if !i < Obj.size o then begin
        let c = unforward (Obj.field o !i) in
        incr i;
        match classify c with
        | `Leaf -> add_leaf buf c
        | `Node -> acc := !acc + enter c
      end else begin
        ignore (Stack.pop stack);
        alive := false;
        let size = 1 + !acc in
        finish o start size;
        if not (Stack.is_empty stack) then
          let _, _, pacc, _, _ = Stack.top stack in pacc := !pacc + size
      end
    done;
    Digest.to_hex (Digest.string (Buffer.contents buf))
  in
  match run () with
  | d -> d
  | exception e ->
    (* The memo outlives the call, so an abandoned walk must leave none of its
       marks alive. *)
    let bt = Printexc.get_raw_backtrace () in
    Stack.iter (fun (o, _, _, _, alive) -> alive := false; H.remove memo o) stack;
    Printexc.raise_with_backtrace e bt
