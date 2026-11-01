(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* A [Require] the source text spells out in full: its [From] prefix and
   its library names, as written ({!scan_late_commands}). *)
type require_text = { rq_from : string option; rq_names : string list }

(* A late command of the source text: its word's byte offset and, for a
   [Require] the text spells out in full, that [Require]. *)
type late_command = { lc_offset : int; lc_require : require_text option }

(* What a proof has to open after to replay: the last late command that is
   late whatever is loaded, and the [Require]s after it, last first, with
   their offsets. Each of those is late only while a library it names is
   not loaded ({!Proof_replay.open_proof}). *)
type late_bound = { lb_last : int option; lb_requires : (int * require_text) list }

let no_late = { lb_last = None; lb_requires = [] }

(* A replayed proof's tactics do not run, so the process-wide caches they
   would have filled stay empty (about 120 [lazy] values hold a [lib_ref]
   answer the first time they are forced, and never ask again), and a closure
   they would have installed is not installed. A later command that rebinds
   a Rocqlib name, or loads code, then makes a later proof see what stock
   would not have seen: stock's lazy holds the old answer, replay's is forced
   after the rebinding (Claude review of c2190e74e0, P1). Which lazies are
   already forced when a proof starts is an input no read records: a proof
   whose registration found a lazy forced reads nothing, and the same proof
   in an edited file can be the one that forces it. So the hazard is decided
   by position, not per proof.

   A proof that opens after the last such command in the file meets a
   process whose state equals stock's: every proof before that command ran
   its tactics, and from there on no command rebinds a name or loads code,
   which is the state of a file with no such command at all. So those proofs
   may replay, and every proof that opens before the last such command runs
   (outcome [ineligible], channel ["rebind"]). The commands, after the
   file's first [Qed] or [Save] (no proof can be replayed before it), are:
   [Register]; [Require] (a library brings its own [Register] objects and
   plugins, which the text does not show), unless it loads nothing (below);
   [Load]; [Cd], which changes the directory that a file opened by a
   relative path is read from (a micromega certificate cache reads its
   entries again from [.lia.cache] at each lookup), so a proof before it that
   replays leaves unopened a file that stock opened there (gate review
   CF4-R2); [Declare] (ML Module,
   Module); [Import] and [Export] once an export-locality registration is
   loaded (see {!scan_late_events}); [Include]; a [Module] that is not plain
   (sealed, a functor, a module type, a definition); and an [End] that closes
   such a module (a sealed one applies its signature's objects there), or a
   plain module or a section inside which one of those commands appeared
   (Claude delta review of 7b2a60f377, P1-2 to P1-4); and [Reset] ([Reset
   Initial] too), [Back] and [BackTo], which restore an earlier state: the
   Rocqlib table and every Summary go back, while a process-wide lazy that a
   proof before them forced does not (fourth soundness review, finding 3,
   fixture late_reset_congruence). Once one of these appears, the sections
   and modules the scan keeps track of no longer follow the restored state,
   so every later [End] counts too. Decided from the source
   text, before any proof is replayed, with two runtime conditions: the one
   on [Import], and the one on [Require].

   A [Require] is not late for a proof when every library it names is
   already loaded at the proof's opening. Such a [Require] loads nothing:
   [Library.intern_library] stops at a loaded library, whose dependencies
   are loaded too, so the closure it registers is empty; no object's load
   function runs (a SuperGlobal [Register] acts at load,
   [Libobject.object_with_locality]) and no plugin loads (an ML module acts
   at load, [Mltop.inMLModule]). Its [Import] or [Export] part is a late
   word of its own, under the [Import] rule. Nothing between the decision
   and the [Require] can unload a library or resolve a name otherwise
   without being late itself: only a [Require] loads a library, and one
   that loads any is late; the [Load], the [End] and the [Reset] that could
   undo a load are late; no command changes the load path (the [Add
   LoadPath] commands were removed: doc/sphinx/changes.rst, #17394); the
   decision resolves the names with the [Require]'s own function
   ([Synterp.require_locate]), and coqc keeps the directory listings it
   read ([System.trust_file_cache]). So the dependencies of the [Require]s
   between the proof and this one add nothing to what is loaded: if one of
   them loads a library, the proof runs anyway. A [Require] the text does
   not spell out in full ({!require_sentence}), or one with a name that
   does not resolve, stays late. A [Require] that loads a library after a
   replayed proof all the same stops the compile
   ({!Proof_replay.note_require}).

   The scan reads the text with the source-token cursor below, as the
   [Require] reader does. It is meant to err toward a later position: a late
   word inside a quotation, a notation's text or an identifier ending in one
   ([x_Register]) counts too. A command a [Load]ed file builds is covered
   because [Load] counts; one a plugin adds is covered by the plugin audit
   of {!Proof_replay}, not by this scan. *)

(* {6 The source-token cursor}

   The late-command scan and the [Require] reader read the source text with
   one cursor, so that a lexer case is decided in one place (code-quality
   finding MQ-2: each had its own character loop, and five of the P1
   defects that review rounds found in the scan were lexer cases). It reads
   as Rocq's lexer reads (parsing/cLexer.ml), for what the two readers need:
   - blanks (space, newline, tab, carriage return) and comments, which nest
     and hold strings: a ["*)"] in a string does not end a comment;
   - a string, in which [""] is a quote;
   - a number, as [NumTok.Unsigned.parse] reads one: [0-9][0-9_]*, a
     fraction when a digit or [_] follows the dot, an exponent when a digit
     follows the [e] and its sign, or [0x] and hexadecimal digits with a [p]
     exponent. So in [1Register], [1_Register], [0xaRegister], [1End] or
     [1._Register] the rest is a new word (Claude delta reviews of
     7b2a60f377 and a158379eb4, P1-1);
   - a run of dots. ["."] or ["..."] followed by a blank ends a sentence;
     [".."] is one keyword and does not ([x .. y], an import filter's
     [(.. )]);
   - a word: a run of letters, digits, [_] and ['] that does not start with
     a digit. Every byte above 127 counts as a letter, so a word can be
     longer than the lexer's identifier: the scan errs toward a late word,
     and the [Require] reader refuses such a word;
   - any other byte, alone.
   An attribute is read to its matching bracket on request
   ({!skip_attribute}). *)

type token = Eof | Word | Number | Quoted | Dots | Byte

type cursor = {
  text : string;
  mutable pos : int;  (** where the next token is read from *)
  mutable line : int;  (** the line of [pos] *)
  mutable token : token;  (** the current token *)
  mutable start : int;  (** its first byte *)
  mutable token_line : int;  (** the line of [start] *)
}

let cursor text = { text; pos = 0; line = 1; token = Eof; start = 0; token_line = 1 }

let copy c = { c with pos = c.pos }

let is_letter ch = match ch with 'a'..'z' | 'A'..'Z' -> true | ch -> Char.code ch >= 128

let is_word_byte ch = is_letter ch || (match ch with '0'..'9' | '_' | '\'' -> true | _ -> false)

let is_digit ch = ch >= '0' && ch <= '9'

let is_hex_digit ch = is_digit ch || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F')

(* At a quote: past the closing quote, or to the end of the text. *)
let skip_string c =
  let text = c.text and n = String.length c.text in
  c.pos <- c.pos + 1;
  let fin = ref false in
  while not !fin && c.pos < n do
    if text.[c.pos] = '"' then
      if c.pos + 1 < n && text.[c.pos + 1] = '"' then c.pos <- c.pos + 2
      else (c.pos <- c.pos + 1; fin := true)
    else begin
      if text.[c.pos] = '\n' then c.line <- c.line + 1;
      c.pos <- c.pos + 1
    end
  done

(* At ["(*"]: past the matching ["*)"], or to the end of the text. *)
let skip_comment c =
  let text = c.text and n = String.length c.text in
  c.pos <- c.pos + 2;
  let depth = ref 1 in
  while !depth > 0 && c.pos < n do
    let ch = text.[c.pos] in
    if ch = '(' && c.pos + 1 < n && text.[c.pos + 1] = '*' then (incr depth; c.pos <- c.pos + 2)
    else if ch = '*' && c.pos + 1 < n && text.[c.pos + 1] = ')' then (decr depth; c.pos <- c.pos + 2)
    else if ch = '"' then skip_string c
    else begin
      if ch = '\n' then c.line <- c.line + 1;
      c.pos <- c.pos + 1
    end
  done

(* Past the bytes [digit] takes, and underscores. *)
let take_digits c digit =
  let n = String.length c.text in
  while c.pos < n && (digit c.text.[c.pos] || c.text.[c.pos] = '_') do c.pos <- c.pos + 1 done

(* At a digit: past the number, as [NumTok.Unsigned.parse] reads it. *)
let read_number c =
  let text = c.text and n = String.length c.text in
  let i = c.pos in
  let hex =
    text.[i] = '0' && i + 2 < n && (text.[i + 1] = 'x' || text.[i + 1] = 'X') && is_hex_digit text.[i + 2]
  in
  let digit = if hex then is_hex_digit else is_digit in
  if hex then c.pos <- i + 2;
  take_digits c digit;
  if c.pos + 1 < n && text.[c.pos] = '.' && (digit text.[c.pos + 1] || text.[c.pos + 1] = '_') then begin
    c.pos <- c.pos + 1;
    take_digits c digit
  end;
  let at_exponent =
    c.pos < n && (if hex then text.[c.pos] = 'p' || text.[c.pos] = 'P' else text.[c.pos] = 'e' || text.[c.pos] = 'E')
  in
  if at_exponent then begin
    let k = if c.pos + 1 < n && (text.[c.pos + 1] = '+' || text.[c.pos + 1] = '-') then c.pos + 2 else c.pos + 1 in
    if k < n && is_digit text.[k] then (c.pos <- k; take_digits c is_digit)
  end

(* Moves to the next token, past blanks and comments. *)
let advance c =
  let text = c.text and n = String.length c.text in
  let fin = ref false in
  while not !fin && c.pos < n do
    match text.[c.pos] with
    | ' ' | '\t' | '\r' -> c.pos <- c.pos + 1
    | '\n' -> c.line <- c.line + 1; c.pos <- c.pos + 1
    | '(' when c.pos + 1 < n && text.[c.pos + 1] = '*' -> skip_comment c
    | _ -> fin := true
  done;
  c.start <- c.pos;
  c.token_line <- c.line;
  c.token <-
    (if c.pos >= n then Eof
     else match text.[c.pos] with
       | '"' -> skip_string c; Quoted
       | '0'..'9' -> read_number c; Number
       | '.' -> while c.pos < n && text.[c.pos] = '.' do c.pos <- c.pos + 1 done; Dots
       | ch when is_word_byte ch ->
         while c.pos < n && is_word_byte text.[c.pos] do c.pos <- c.pos + 1 done; Word
       | _ -> c.pos <- c.pos + 1; Byte)

let not_eof c = match c.token with Eof -> false | _ -> true

let token_text c = String.sub c.text c.start (c.pos - c.start)

let is_word c w =
  match c.token with
  | Word -> c.pos - c.start = String.length w && CString.is_sub w c.text c.start
  | _ -> false

let is_byte c ch = match c.token with Byte -> c.text.[c.start] = ch | _ -> false

(* A run of dots that ends a sentence: ["."], or ["..."] after a tactic,
   then a blank or the end of the text. *)
let sentence_end c =
  match c.token with
  | Dots ->
    let k = c.pos - c.start in
    (k = 1 || k = 3)
    && (c.pos >= String.length c.text
        || (match c.text.[c.pos] with ' ' | '\n' | '\t' | '\r' -> true | _ -> false))
  | _ -> false

(* The dot that ends a command: ["."] then a blank. *)
let command_end c = sentence_end c && c.pos - c.start = 1

(* The current word is followed by a field: a dot, then a letter or [_]. *)
let field_follows c =
  let n = String.length c.text in
  c.pos + 1 < n && c.text.[c.pos] = '.' && (is_letter c.text.[c.pos + 1] || c.text.[c.pos + 1] = '_')

(* The current word is a field: it follows a dot that follows a word or a
   number. *)
let is_field c = c.start >= 2 && c.text.[c.start - 1] = '.' && is_word_byte c.text.[c.start - 2]

(* The current byte is ['#'] and ['['] follows it. *)
let at_attribute c = is_byte c '#' && c.pos < String.length c.text && c.text.[c.pos] = '['

(* At an attribute ({!at_attribute}): to its matching [']'], so that a [']']
   in a comment or a string inside it does not end it (Claude review of
   951eb445f9, P1-1). *)
let skip_attribute c =
  advance c;
  let depth = ref 1 in
  while !depth > 0 && not_eof c do
    advance c;
    if is_byte c '[' then incr depth else if is_byte c ']' then decr depth
  done

(* A word the [Require] reader takes as an identifier: plain ASCII, not
   [_]. *)
let ascii_ident c =
  match c.token with
  | Word ->
    let ok = ref (c.text.[c.start] <> '\'' && (c.pos - c.start > 1 || c.text.[c.start] <> '_')) in
    for i = c.start to c.pos - 1 do
      if Char.code c.text.[i] >= 128 then ok := false
    done;
    !ok
  | _ -> false

let restoring_words = [ "Reset"; "Back"; "BackTo" ]

let late_words =
  [ "Register"; "Require"; "Load"; "Cd"; "Declare"; "Import"; "Export"; "Include"; "Module" ] @ restoring_words

(* The [Require] sentence whose command word ([From] or [Require]) is the
   cursor's token, read as the grammar reads one (vernac/g_vernac.mlg):
   [From q] or nothing, [Require], [(safe)] or nothing, [Import] or
   [Export] with its import categories or nothing, one or more names each
   with an import filter or not, then the dot that ends the command. It
   gives the offset of the [Require] word, the [From] prefix and the names.
   A name is plain ASCII identifiers joined by dots with no blank around a
   dot, as the lexer joins a qualified name. Anything else gives [None], and
   the [Require] stays late: this reading can refuse a sentence Rocq
   accepts, and never takes other names from one it accepts. *)
let require_sentence c =
  let ( let* ) = Option.bind in
  let rec qualid prefix =
    if not (ascii_ident c) then None
    else begin
      let id = token_text c in
      let q = match prefix with None -> id | Some p -> p ^ "." ^ id in
      let field = field_follows c in
      advance c;
      if field then (advance c; qualid (Some q)) else Some q
    end
  in
  (* A group in parentheses, from its ['(']: the import categories, or an
     import filter. *)
  let group () =
    let rec go depth =
      match c.token with
      | Eof | Quoted -> None
      | _ when sentence_end c -> None
      | _ when is_byte c '(' -> advance c; go (depth + 1)
      | _ when is_byte c ')' -> advance c; if depth = 1 then Some () else go (depth - 1)
      | _ -> advance c; go depth
    in
    go 0
  in
  let* from =
    if is_word c "From" then (advance c; let* q = qualid None in Some (Some q))
    else if is_word c "Require" then Some None
    else None
  in
  let at_require = c.start in
  let* () = if is_word c "Require" then (advance c; Some ()) else None in
  let* () =
    if not (is_byte c '(') then Some ()
    else begin
      advance c;
      if not (is_word c "safe") then None
      else (advance c; if is_byte c ')' then (advance c; Some ()) else None)
    end
  in
  let* () =
    if is_word c "Import" || is_word c "Export" then begin
      advance c;
      if is_byte c '-' then (advance c; if is_byte c '(' then group () else None)
      else if is_byte c '(' then group ()
      else Some ()
    end
    else Some ()
  in
  let rec names acc =
    if command_end c then (if acc = [] then None else Some (List.rev acc))
    else
      let* q = qualid None in
      let* () = if is_byte c '(' then group () else Some () in
      names (q :: acc)
  in
  let* names = names [] in
  Some (at_require, { rq_from = from; rq_names = names })

(* The first late command with its line, and every late command, last
   first. With [~imports_late:false], [Import] and [Export] are not late
   words: opening a module runs only its objects' open functions, which load
   no code (an ML module acts at load: [Mltop.inMLModule]) and change a
   Rocqlib answer only through an export-locality [Register]
   ([Libobject.object_with_locality]: SuperGlobal acts at load, Export at
   open). The caller uses that scan only while no export-locality
   registration has been loaded or declared
   ({!Proof_replay.note_export_register}).

   A plain module, [Module M.] or [Module Import M.] with no binder, no
   signature and no [:=], is not late by itself, and its [End] is late only
   when a late word appeared inside it: ending it loads again only the
   objects declared in its body, and a body with no late word declares no
   Rocqlib registration and loads no code. A sealed module, a functor, a
   module type and a module definition stay late, and their [End] too.

   A [Require] that is the command word of its sentence, or follows the
   sentence's [From q], carries what it names when {!require_sentence}
   reads it. It still marks the frames it is in: the [End] of one stays
   late. *)
let scan_late_commands ?(imports_late = true) text =
  let late_words =
    if imports_late then late_words
    else List.filter (fun w -> w <> "Import" && w <> "Export") late_words
  in
  let c = cursor text in
  let closed = ref false in
  (* One frame per open [Section] or [Module]: whether its [End] can change
     what a Rocqlib name answers. A non-plain module's always can; a plain
     module's and a section's can when a late word appeared inside it, at any
     depth. Only a sentence's command word opens or closes one: [Print
     Section S.] opens nothing, [Fail End S.] closes nothing (Claude delta
     review of 2daae0ed39, P1-2). *)
  let frames : bool ref list ref = ref [] in
  (* A [Reset], [Back] or [BackTo] has appeared: the frames no longer follow
     the restored sections and modules. *)
  let restored = ref false in
  let result = ref None and commands = ref [] in
  (* The cursor at this sentence's command word when that word is [From]. *)
  let from_word = ref None in
  (* Whether the sentence after the current word holds [:=] before its end. *)
  let sentence_assigns () =
    let c = copy c in
    let rec go () =
      advance c;
      match c.token with
      | Eof -> false
      | _ when sentence_end c -> false
      | _ when is_byte c ':' && c.pos < String.length text && text.[c.pos] = '=' -> true
      | _ -> go ()
    in
    go ()
  in
  (* Whether the sentence after the current word, its command word
     [Module], is [Import] or [Export] at most, then one identifier, then the
     dot that ends it: a plain module. Anything else (a binder, a signature,
     [:=], [<:], [Type]) is not plain. *)
  let plain_module () =
    let c = copy c in
    advance c;
    if is_word c "Import" || is_word c "Export" then advance c;
    match c.token with
    | Word ->
      let first = text.[c.start] in
      (is_letter first || first = '_') && not (is_word c "Type") && (advance c; command_end c)
    | _ -> false
  in
  let found ?require w =
    if !result = None then result := Some (w, c.token_line);
    commands := { lc_offset = c.start; lc_require = require } :: !commands
  in
  (* A late word is found wherever its letters end a word and do not
     continue a longer one: in [1Register], [1_Register] and [0x1Register]
     the cursor reads a number then [Register] (P1-1), and a late word also
     counts when it follows a digit, [_] or ['] in its word. This takes an
     identifier such as [x_Register] for the word, which only costs a
     replay. *)
  let late_in run =
    List.find_opt
      (fun k ->
         let lr = String.length run and lk = String.length k in
         lr >= lk && CString.is_suffix k run
         && (lr = lk || not (is_letter run.[lr - lk - 1])))
      late_words
  in
  let prefixes =
    [ "Local"; "Global"; "Time"; "Timeout"; "Redirect"; "Instructions"; "Profile"; "Polymorphic";
      "Monomorphic"; "Cumulative"; "NonCumulative"; "Private"; "Program"; "Fail"; "Succeed" ] in
  (* A number, a string, a bullet or a brace before the command word leaves
     the sentence at its start: [Timeout 5 Register]. *)
  let at_start = ref true and under_fail = ref false and cmd_module = ref false in
  advance c;
  while not_eof c do
    (match c.token with
     | Byte when !at_start && at_attribute c -> skip_attribute c
     | Word ->
       let run = token_text c in
       let lead_letter = is_letter text.[c.start] in
       (* A component of a qualified identifier, [Module.module_contents] in
          an Ltac2 tactic or [M.Register], is part of one identifier token to
          Rocq's lexer, never a command keyword: it is followed by a field,
          or is one. It is neither a late word nor a command word. The name
          after a [Module] command keeps the rule below. *)
       let qualified = not !cmd_module && (field_follows c || is_field c) in
       if qualified then at_start := false
       else if !at_start && not !under_fail && String.equal run "Module" && plain_module () then begin
         at_start := false;
         frames := ref false :: !frames
       end
       else begin
         (match late_in run with
          | Some w ->
            List.iter (fun f -> f := true) !frames;
            if List.mem w restoring_words then restored := true;
            if !closed then begin
              (* A [Require] as the command word, or after [From q]. *)
              let require =
                if not (String.equal run "Require") then None
                else
                  let start = if !at_start then Some c else !from_word in
                  match Option.bind start (fun s -> require_sentence (copy s)) with
                  | Some (at, r) when at = c.start -> Some r
                  | _ -> None
              in
              found ?require w
            end
          | None -> ());
         if !at_start && lead_letter && List.mem run prefixes then begin
           if String.equal run "Fail" || String.equal run "Succeed" then under_fail := true
         end
         else if !at_start && not lead_letter then ()
         else if !at_start then begin
           at_start := false;
           if String.equal run "From" then from_word := Some (copy c);
           if not !under_fail then begin
             if String.equal run "Module" then cmd_module := true
             else if String.equal run "Section" then frames := ref false :: !frames
             else if String.equal run "End" then begin
               match !frames with
               | f :: rest ->
                 frames := rest;
                 if !closed && !f then found "End (of a module, or of a section that loads or imports)"
                 else if !closed && !restored then found "End (after a Reset or Back)"
               | [] -> if !closed then found "End"
             end
           end
         end
         else if !cmd_module then begin
           (* [Module Type T], [Module Export M]: the name comes later *)
           if not (List.mem run [ "Type"; "Import"; "Export" ]) then begin
             cmd_module := false;
             if not (sentence_assigns ()) then frames := ref true :: !frames
           end
         end;
         if String.equal run "Qed" || String.equal run "Save" then closed := true
       end
     | _ when sentence_end c ->
       at_start := true; under_fail := false; cmd_module := false; from_word := None
     | _ -> ());
    advance c
  done;
  !result, !commands

(* The first late command with its line, and the offset of the last one's
   word. *)
let scan_late_events ?imports_late text =
  let first, commands = scan_late_commands ?imports_late text in
  first, (match commands with c :: _ -> Some c.lc_offset | [] -> None)

let scan_late_rebind text = fst (scan_late_events text)

let late_bound commands =
  let rec go requires = function
    | { lc_offset; lc_require = Some r } :: rest -> go ((lc_offset, r) :: requires) rest
    | { lc_offset; lc_require = None } :: _ -> { lb_last = Some lc_offset; lb_requires = List.rev requires }
    | [] -> { lb_last = None; lb_requires = List.rev requires }
  in
  go [] commands

type late_events = {
  first : string * int;  (** the first late command, and its line *)
  late : late_bound;  (** [Import] and [Export] counted *)
  late_no_imports : late_bound;  (** [Import] and [Export] not counted *)
}

let late_events text =
  match scan_late_commands text with
  | Some first, (_ :: _ as commands) ->
    Some { first; late = late_bound commands;
           late_no_imports = late_bound (snd (scan_late_commands ~imports_late:false text)) }
  | _ -> None
