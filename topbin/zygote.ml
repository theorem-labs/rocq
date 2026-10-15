(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* rocq-zygote: a coqc fork server.

   Motivation (bet-failure-tasks docs/build/ROCQ-INTERNALS.md Sections 15-19):
   Require statements cost ~8% of tree-wide coqc command time, dominated by
   Library.register_library's replay of a required library's objects into
   the live Nametab/kernel environment (confirmed by direct reading:
   vernac/library.ml's libraries_table is a `Summary.ref`, but nothing in
   a straight-line batch compile (`Ccompile.compile_file`) ever unfreezes
   a summary, so across one process's lifetime it behaves exactly like a
   plain process-global ref -- `intern_library` treats an already-loaded
   dependency as terminal and skips re-registering it entirely, never even
   calling Declaremods.Interp.register_library for it). A cached-nametab-
   fragment prototype (Sections 17-19) was proven
   UNSAFE: the compile-time-interpretation and replay-time code paths
   compute different visibility levels for the same declarations.

   The safe alternative implemented here: load a common prefix of
   Require-only sentences ONCE in a "zygote" process, by literally
   interpreting that prefix through the normal, unmodified vernacular
   interpreter -- exactly as coqc itself would, via an ordinary
   Ccompile.compile_file call on a scratch file containing just that
   prefix. Then fork() once per real file. Each child inherits the
   zygote's post-prefix process state (including library/library.ml's
   now-populated libraries_table, the kernel environment, and Nametab) via
   copy-on-write, and continues with a completely normal, UNMODIFIED
   Ccompile.compile_file call on its own file, in its own process. No
   Require/registration logic is changed, reconstructed, or short-circuited
   by this file; the only new code is the fork-server loop and a
   sentence-exact prefix-match guard. Soundness rests on nothing more than:
   every child's ambient process state, at the moment it starts compiling
   its own file, is byte-for-byte what a standalone process would have
   after interpreting the same Require sentences in the same order under
   the same flags -- true by construction, since the zygote never
   processes anything file-specific before forking, and every child forks
   from that identical, shared, pre-divergence state.

   The prefix-match guard compares actual parsed VERNACULAR SENTENCES (via
   Rocq's own grammar entry, Pvernac.main_entry -- the same one coqc's own
   Vernac.load_vernac uses), not raw file bytes: two files can share an
   identical Require prefix while differing in whatever header comment
   precedes it, and the grammar entry's own token locations already start
   at the first real token, comments and whitespace skipped for free.

   Wire protocol (one line in, one line out, tab-separated, over a Unix
   domain socket):
     client -> server: "COMPILE\t<cwd>\t<coqlibs>\t<file>\t<.vo output>\t<echo:0|1>\t<stdout path>\t<stderr path>\n"
    server -> client: "MISMATCH\n"      -- either the client's <coqlibs> string didn't match this
                                            daemon's own -Q/-R flags, or chdir to <cwd> failed, or
                                            the file's own leading sentences differ from the
                                            zygote's recorded prefix, or a library the warm-up
                                            loaded has changed on disk since (the dependency-
                                            staleness guard, capture_fingerprint/fingerprint_stale
                                            below -- in the last case the daemon also exits after
                                            answering, so the next ensure_zygote call respawns and
                                            re-interprets the now-current prefix); caller must fall
                                            back to an ordinary, non-zygote compile.
                        "EXIT\t<code>\n" -- the file was compiled (or failed) under the
                                             zygote; stdout/stderr were written to the paths
                                             given in the request; caller exits with <code>.
   <file>/<.vo output> are given exactly as coq_makefile would pass them to a real `rocq
   compile` invocation (relative, matching the client's own <cwd>) -- Rocq embeds the literal
   path string it was given in every stored Loc.t, so an absolute path, or a relative path
   resolved against the wrong cwd, makes the .vo diverge from a stock compile byte-for-byte.
   The forked child chdirs to <cwd> before resolving <file>/<.vo output> (20d/21): a daemon is
   spawned lazily by whichever client wins the race, so its own post-fork cwd is NOT guaranteed
   to already equal every later client's cwd without this step.

   A second, independent mode (--rocq-zygote-dump-sentences, used by the
   offline prefix-structure analysis, not by the server) parses a file's
   leading N vernacular sentences with the same grammar entry and prints
   their exact raw text to stdout, NUL-separated, so the analysis script
   groups files by what the compiler itself will see as "the same
   sentences", not by a line-oriented guess. *)

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

(* Parse up to [max_n] leading vernacular sentences of [file] with Rocq's
   own grammar entry (no STM document needed: Procq.Entry.parse is a pure
   function of grammar state + token stream). Returns each sentence's exact
   raw source text, comments and surrounding whitespace excluded (the
   entry's own Loc.t already starts at the first real token). Stops early
   at EOF OR at the first sentence the grammar entry cannot parse under
   proof_mode=None (e.g. tactic/bullet syntax once a proof body starts) --
   callers only ever care about a leading run of plain vernacular
   (Require) sentences, so a parse hiccup past that point is treated the
   same as EOF: stop and return what was cleanly parsed so far.

   [exhaustive] (default false) changes what a parse hiccup means. This
   function never INTERPRETS a sentence between parses (unlike the real
   compile, whose Vernac loading loop parses and interprets one sentence
   at a time): if sentence k's own syntax depends on something only
   INTERPRETING an earlier sentence would establish (confirmed live: a
   `Notation` a later sentence's term syntax relies on, e.g. ListNotations'
   `[...]`, only takes effect once `Import` is actually INTERPRETED, not
   merely parsed), this function's parse of sentence k fails here even
   though the real compile sails through it. With [exhaustive:true], that
   failure raises [Truncated_before_eof] instead of silently stopping, so
   a caller that needs "this is the WHOLE prefix, not a hiccup-shortened
   one" (the self-check in zygote_run below) can refuse to trust a short
   count rather than silently serving behind it. *)
exception Truncated_before_eof

let peek_sentences ?(exhaustive = false) ~max_n file =
  let content = read_file file in
  let ic = open_in_bin file in
  Fun.protect ~finally:(fun () -> close_in ic) (fun () ->
    let pa = Procq.Parsable.make
        ~loc:Loc.(initial (InFile { dirpath = None; file }))
        (Gramlib.Stream.of_channel ic) in
    let stop acc = if exhaustive then raise Truncated_before_eof else List.rev acc in
    let rec loop n acc =
      if n <= 0 then List.rev acc
      else match Procq.Entry.parse (Pvernac.main_entry None) pa with
        | None -> List.rev acc (* true EOF: a clean stop, exhaustive or not *)
        | Some { CAst.loc = Some loc; _ } ->
          let text = String.sub content loc.Loc.bp (loc.Loc.ep - loc.Loc.bp) in
          loop (n - 1) (text :: acc)
        | Some { CAst.loc = None; _ } -> stop acc
        | exception _ -> stop acc
    in
    loop max_n [])

(* ---- Our own flags, pulled out of argv before the stock coqc-style
   parsers see it (Coqcargs.parse treats any argument it does not
   recognize as the file to compile, so our flags must never reach it). ---- *)

type zygote_args = {
  prefix_file : string option;
  socket_path : string option;
  idle_timeout : float; (* seconds; <= 0.0 means no idle timeout *)
  dump_sentences : int option; (* Some max_n: dump mode instead of serving *)
  (* The exact -Q/-R load-path flag string this daemon was launched with
     (set by the wrapper from its own ROCQ_ZYGOTE_COQLIBS, the same string
     for every file in the group by construction). Every COMPILE request
     now carries the client's own copy of that string; the server rejects
     (MISMATCH, safe fallback) any request whose string doesn't match
     byte-for-byte, so a daemon can never compile a file under load-path
     flags other than the ones its own warm-up used. *)
  coqlibs : string;
}

let parse_zygote_extra extras =
  let prefix_file = ref None in
  let socket_path = ref None in
  let idle_timeout = ref 0.0 in
  let dump_sentences = ref None in
  let coqlibs = ref "" in
  let rec go = function
    | "--rocq-zygote-prefix" :: v :: rest -> prefix_file := Some v; go rest
    | "--rocq-zygote-socket" :: v :: rest -> socket_path := Some v; go rest
    | "--rocq-zygote-idle-timeout" :: v :: rest -> idle_timeout := float_of_string v; go rest
    | "--rocq-zygote-dump-sentences" :: v :: rest -> dump_sentences := Some (int_of_string v); go rest
    | "--rocq-zygote-coqlibs" :: v :: rest -> coqlibs := v; go rest
    | x :: rest -> x :: go rest
    | [] -> []
  in
  let remaining = go extras in
  { prefix_file = !prefix_file;
    socket_path = !socket_path;
    idle_timeout = !idle_timeout;
    dump_sentences = !dump_sentences;
    coqlibs = !coqlibs },
  remaining

let zygote_specific_usage = Boot.Usage.{
  executable_name = "rocq-zygote";
  extra_args = "file...";
  extra_options = "\n\
rocq-zygote specific options (consumed before coqc's own flags):\
\n  --rocq-zygote-prefix FILE          server mode: the shared Require-only prefix, verbatim\
\n  --rocq-zygote-socket PATH          server mode: Unix socket to listen on\
\n  --rocq-zygote-idle-timeout S       server mode: exit after S idle seconds (default: never)\
\n  --rocq-zygote-coqlibs STRING       server mode: this daemon's own -Q/-R flag string, for the\
\n                                     per-request guard (see handle_connection)\
\n  --rocq-zygote-dump-sentences N     dump mode: print the file's first N sentences, NUL-separated\
\n"
}

(* Compile one file as a normal, unmodified coqc invocation would, in the
   calling process -- used both for the one-time prefix warm-up and for
   each forked child. Returns the process exit code coqc itself would use. *)
let compile_like_coqc opts stm_opts copts injections =
  try
    Topfmt.(in_phase ~phase:CompilationPhase)
      Ccompile.compile_file opts stm_opts copts injections;
    flush_all ();
    0
  with exn ->
    flush_all ();
    Topfmt.print_err_exn exn;
    flush_all ();
    CErrors.exit_code exn

(* ---- Dump-sentences mode. ---- *)

let run_dump_sentences max_n file =
  let sentences = peek_sentences ~max_n file in
  List.iter (fun s -> print_string s; print_char '\000') sentences;
  flush stdout

(* ---- The server loop, run after the one-time warm-up. ---- *)

let send_line fd s =
  let s = s ^ "\n" in
  let len = String.length s in
  let rec go off =
    if off < len then
      let n = Unix.write_substring fd s off (len - off) in
      go (off + n)
  in
  go 0

let recv_line fd =
  (* Requests are short and single-line; read until '\n' or EOF. *)
  let buf = Buffer.create 256 in
  let byte = Bytes.create 1 in
  let rec go () =
    match Unix.read fd byte 0 1 with
    | 0 -> Buffer.contents buf
    | _ ->
      if Bytes.get byte 0 = '\n' then Buffer.contents buf
      else (Buffer.add_char buf (Bytes.get byte 0); go ())
  in
  go ()

let reopen_std fd path =
  let newfd = Unix.openfile path Unix.[O_WRONLY; O_CREAT; O_TRUNC] 0o644 in
  Unix.dup2 newfd fd;
  Unix.close newfd

(* Handle exactly one already-accepted connection, in a process forked
   fresh from the warmed-up zygote. Never returns -- always exits.

   The request now carries the client's own cwd and its own copy of the
   load-path flag string (ROCQ_ZYGOTE_COQLIBS on the wrapper side, this
   daemon's ~coqlibs on the server side). Two checks before any file I/O:
   (1) the coqlibs strings must match byte-for-byte -- a daemon never
   compiles a file under -Q/-R bindings other than the ones its own
   warm-up used, which is the soundness precondition this design has
   always relied on, now actually verified per request instead of merely
   assumed from the group manifest. (2) Unix.chdir to the client's cwd,
   BEFORE resolving the (relative) file/output paths -- a forked child
   inherits the zygote's cwd at the moment it was spawned, which need not
   be the cwd of the client sending THIS request (the daemon is spawned
   lazily, once, by whichever client happened to win the race; nothing
   before this fix kept every later client's cwd in sync with that one).
   Without the chdir, a relative file/output argument is resolved against
   the wrong directory -- at best a clean ENOENT (caught below, safely
   falls back to MISMATCH), at worst a same-named file that happens to
   exist under the stale cwd too, compiled and embedding the wrong
   relative path string in its own Loc.t metadata (the divergence
   documented in 20d). The chdir runs in the forked child only, so it
   never perturbs the parent zygote's own cwd for later forks. *)
let handle_connection opts stm_opts injections ~prefix_sentences ~coqlibs conn =
  (* System.dirmap (lib/system.ml) caches each queried directory's listing
     the FIRST time `exists_in_dir_respecting_case` scans it, and reuses
     that listing for the rest of the process's life whenever
     System.trust_file_cache is true -- exactly the setting zygote_run's
     init_extra sets (copying coqc.ml's own batch-mode default) before the
     warm-up compile runs. For a stock compile this is correct: each file
     gets a brand-new process, so the cache can only ever have been
     populated no earlier than that file's own compile started, by which
     point make has already finished every prerequisite. For THIS daemon,
     the cache is populated ONCE (typically during warm-up, before any
     real target file has been compiled) and then inherited unchanged by
     every later fork's copy-on-write memory -- a sibling file's `.vo`,
     written to disk by an EARLIER fork from this same daemon after the
     cache was taken, is invisible to a LATER fork's lookups in that same
     directory. Confirmed live: a `Require` of a sibling in the same
     zygote group and the same source directory, compiled by an earlier
     fork from this daemon, failed with "Unable to locate library" under
     a real -j16 build, while the exact same file-pair rebuilt serially
     (dependency already on disk when this daemon's cache for that
     directory was first populated) succeeded immediately.

     A first version of this fix only flipped trust_file_cache to false
     here, which fixes a cache MISS (a name absent from the stale listing
     gets a real re-scan) but leaves a cache HIT trusted unconditionally:
     `exists_in_dir_respecting_case` returns true the moment the sought
     name is found in the (possibly stale) cached set, before ever
     checking the freshness flag. A directory whose cached listing
     already contains a name since deleted, or a stale entry a later
     build step replaced with different content under the same name,
     would still read as present either way. Clearing the cache outright
     instead of just the trust flag closes that gap too: the child's
     FIRST query for any given directory is then guaranteed to be a
     real, uncached scan (the map lookup below finds nothing, so the
     fallback branch always rescans), so the entry it populates is
     exactly what a brand-new process's first query would see -- present
     things are present because they were just observed, not because an
     older snapshot said so. Every later query, for the SAME directory,
     within THIS SAME CHILD, does reuse what that first query found, the
     same as a stock process would for the rest of ONE file's compile --
     not a new assumption, the same "batch mode trusts the filesystem
     not to change out from under one compile" premise trust_file_cache
     has always encoded, just no longer carried forward from a different
     file's compile in a different, earlier fork. trust_file_cache
     itself is left exactly as the parent set it (true, matching stock):
     only the cached CONTENTS are dropped, not the policy of trusting a
     freshly-populated entry for the rest of this one compile.

     The fix's effect is confined to whether a Require is DISCOVERED at
     all; it never changes what gets loaded once discovery succeeds, so
     it cannot affect any already-passing file's .vo bytes. *)
  System.reset_dir_cache ();
  (* Always move onto a fresh descriptor before we repoint fd 0/1/2 for the
     compile's own stdout/stderr -- stdin/stdout/stderr are already open in
     this process, so dup never returns one of them. set_close_on_exec is
     applied to the descriptor that survives (moved), not the one we are
     about to close: dup() does not propagate FD_CLOEXEC to the new
     descriptor, so applying it to conn before the dup was a no-op on the
     fd actually used for the rest of this request -- a native-compute
     child compiler process forked later would have inherited it open. *)
  let moved = Unix.dup conn in
  Unix.close conn;
  let conn = moved in
  Unix.set_close_on_exec conn;
  let line = recv_line conn in
  match String.split_on_char '\t' line with
  | ["COMPILE"; client_cwd; client_coqlibs; file; output; echo; stdout_path; stderr_path] ->
    if not (String.equal client_coqlibs coqlibs) then begin
      send_line conn "MISMATCH";
      Unix.close conn;
      exit 0
    end;
    let chdir_ok = try Unix.chdir client_cwd; true with Unix.Unix_error _ -> false in
    if not chdir_ok then begin
      send_line conn "MISMATCH";
      Unix.close conn;
      exit 0
    end;
    let n = Array.length prefix_sentences in
    let matches =
      try
        let actual = Array.of_list (peek_sentences ~max_n:n file) in
        Array.length actual = n &&
        Array.for_all2 String.equal actual prefix_sentences
      with _ -> false
    in
    if not matches then begin
      send_line conn "MISMATCH";
      Unix.close conn;
      exit 0
    end else begin
      reopen_std Unix.stdout stdout_path;
      reopen_std Unix.stderr stderr_path;
      (* Rocq's own CLI parser (Coqcargs.add_compile) never hands
         Ccompile.compile_file a bare filename verbatim: it first
         prepends "./" to any argument with no directory component
         (Filename.is_implicit), "needed not to break up Rocq loadpath
         stuff" per its own comment. That string becomes the embedded
         Loc.t source name (the file embeds the LITERAL string it was
         given, same principle as the cwd/coqlibs note above) -- confirmed
         live: the same file compiled via this protocol with "c1.v"
         verbatim versus "./c1.v" produces two BYTE-DIFFERENT .vo files,
         and only the "./"-prefixed one matches a stock compile byte-for-
         byte. coq_makefile always invokes `$(ROCQ) compile ... FILE.v`
         with the bare stem, so skipping this normalization here would
         make EVERY zygote-routed file diverge from stock, not just an
         edge case. Apply the identical transformation Coqcargs.add_compile
         applies, rather than passing the client's string straight through. *)
      let normalize_file f =
        if Filename.is_implicit f then Filename.concat Filename.current_dir_name f
        else f
      in
      let copts = Coqcargs.{ default with
        compile_file = Some (normalize_file file, echo = "1");
        compilation_output_name = Some output;
      } in
      let code = compile_like_coqc opts stm_opts copts injections in
      flush_all ();
      send_line conn (Printf.sprintf "EXIT\t%d" code);
      Unix.close conn;
      exit code
    end
  | _ ->
    send_line conn "MISMATCH";
    Unix.close conn;
    exit 0
let reap_finished_children () =
  try
    let continue = ref true in
    while !continue do
      match Unix.waitpid [Unix.WNOHANG] (-1) with
      | 0, _ -> continue := false
      | _, _ -> ()
    done
  with Unix.Unix_error ((Unix.ECHILD | Unix.EINTR), _, _) -> ()

(* Dependency-staleness guard: the warm-up compile (zygote_run, below)
   loads every Require'd library ONCE into this process's library table,
   and every `Declare ML Module` a required library's source carries
   loads an OCaml plugin via Dynlink -- in both cases, nothing in this
   design ever re-checks that in-memory state against disk afterward. If
   a library OR a plugin the shared prefix touches is rebuilt while this
   daemon sits warm (idle_timeout can hold it for minutes), every later
   fork would silently compile against stale in-memory state -- the same
   bug class rocq-warm's own staleness tests exist to catch (DESIGN.md
   "The .vo on disk was rebuilt under the session"), not exercised
   anywhere in this prototype before this check. The guard is a coarse
   (mtime, size) fingerprint of every loaded library's .vo AND every
   loaded plugin's .cmxs/.cmo (Library.loaded_libraries and
   Mltop.loaded_plugin_files track these as two entirely disjoint lists,
   confirmed live: `Print Libraries.`/`Print ML Modules.` after `Require
   Import Ltac2.Ltac2.` share not one entry -- Library knows nothing
   about ltac2_plugin.cmxs), taken once right after warm-up and
   re-verified before every accepted connection; residual risks:
   - a same-second edit that preserves the file's size is not detected
     (Unix.stat's mtime has only second resolution, matching rocq-warm's
     own design note that its daemon uses mtime_ns -- not available in
     OCaml's Unix.stat).
   - native-compute `.coq-native` shards are a THIRD on-disk dependency
     category this fingerprint does not cover at all:
     Library.register_native_library Dynlink-loads a library's native
     object on every Require when the native compiler is enabled, via a
     mechanism distinct from both the .vo table and the ML-plugin list
     above. A prefix compiled with native_compute enabled could go stale
     in this third category without tripping the guard. Low exposure
     today (the deployed prefixes are Require-only, built without
     native_compute), but a real blind spot if that ever changes --
     closing it needs a native-object enumeration this prototype does
     not yet have.
   On mismatch the daemon answers this one request MISMATCH (the
   existing, already-handled fallback path), then exits instead of
   forking -- the next client's ensure_zygote finds no socket and spawns
   a fresh daemon, which re-interprets the now-current prefix (and
   re-links whatever plugins it now needs). *)
type fingerprint = (string * float * int) list

let capture_fingerprint () : fingerprint =
  let stat_one path =
    try
      let st = Unix.stat path in
      Some (path, st.Unix.st_mtime, st.Unix.st_size)
    with Unix.Unix_error _ -> Some (path, nan, -1)
      (* vanished out from under us -- definitely stale *)
  in
  let libraries =
    List.filter_map (fun dir ->
      let path = Library.library_full_filename dir in
      if path = "<unavailable filename>" then None else stat_one path)
      (Library.loaded_libraries ())
  in
  let plugins = List.filter_map stat_one (Mltop.loaded_plugin_files ()) in
  libraries @ plugins

let fingerprint_stale fp =
  List.exists (fun (path, mtime, size) ->
    match (try Some (Unix.stat path) with Unix.Unix_error _ -> None) with
    | None -> true
    | Some st -> st.Unix.st_mtime <> mtime || st.Unix.st_size <> size)
    fp

let serve_forever opts stm_opts injections ~prefix_sentences ~coqlibs ~fingerprint ~socket_path ~idle_timeout =
  (try Unix.unlink socket_path with Sys_error _ | Unix.Unix_error _ -> ());
  let sock = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
  Unix.bind sock (Unix.ADDR_UNIX socket_path);
  Unix.listen sock 64;
  Printf.eprintf "rocq-zygote: warm-up complete (%d-sentence prefix), listening on %s\n%!"
    (Array.length prefix_sentences) socket_path;
  let rec loop () =
    reap_finished_children ();
    match
      if idle_timeout > 0.0 then
        (try Some (let r, _, _ = Unix.select [sock] [] [] idle_timeout in r)
         (* A signal interrupting select is not readiness, and not idleness
            either -- re-enter the loop exactly as the accept path below
            already does for the same exception, rather than treating an
            interrupted wait as if the idle timeout had elapsed. *)
         with Unix.Unix_error (Unix.EINTR, _, _) -> None)
      else Some [sock]
    with
    | None -> loop ()
    | Some [] ->
      Printf.eprintf "rocq-zygote: idle timeout, exiting\n%!";
      (try Unix.unlink socket_path with _ -> ());
      exit 0
    | Some _ ->
      (match Unix.accept sock with
       | conn, _ when fingerprint_stale fingerprint ->
         Printf.eprintf
           "rocq-zygote: a loaded library changed on disk since warm-up, refusing and exiting\n%!";
         (try send_line conn "MISMATCH" with _ -> ());
         (try Unix.close conn with _ -> ());
         (try Unix.unlink socket_path with _ -> ());
         exit 0
       | conn, _ ->
         flush_all ();
         (match Unix.fork () with
          | 0 ->
            Unix.close sock;
            handle_connection opts stm_opts injections ~prefix_sentences ~coqlibs conn
          | _pid ->
            Unix.close conn;
            loop ())
       | exception Unix.Unix_error (Unix.EINTR, _, _) -> loop ())
  in
  loop ()

let zygote_run (zargs : zygote_args) ~opts stm_opts injections =
  let prefix_file = Option.get zargs.prefix_file in
  let socket_path = Option.get zargs.socket_path in
  (* Register the normal feedback->stdout bridge once, before the warm-up;
     forked children inherit it via copy-on-write, exactly as they inherit
     every other piece of process state this design relies on. *)
  ignore (Feedback.add_feeder Coqloop.coqloop_feed);
  (* One-time warm-up: compile the shared prefix exactly as coqc would
     compile any ordinary file, in THIS (pre-fork) process. This is the
     only place the heavy Require/Nametab-registration work happens; every
     later child skips it because library/library.ml's libraries_table
     (a Summary.ref, but never unfrozen by compile_like_coqc's
     straight-line Ccompile.compile_file -- this design never touches the
     STM/interactive layer that would restore it, so it behaves as a
     plain process-global cell for every batch compile this server ever
     runs) already has these libraries loaded. *)
  let warmup_copts = Coqcargs.{ default with
    compile_file = Some (prefix_file, false);
    compilation_output_name = None;
  } in
  let code = compile_like_coqc opts stm_opts warmup_copts injections in
  if code <> 0 then begin
    Printf.eprintf "rocq-zygote: prefix warm-up failed (exit %d), refusing to serve\n%!" code;
    exit code
  end;
  (* Record the prefix as parsed sentences (the same comparison the server
     loop uses per request) ONLY NOW, after the warm-up succeeded -- not
     before, against untouched global state. peek_sentences never
     interprets a sentence between parses, so parsing it against
     pre-warm-up state stops short at any sentence whose own syntax
     depends on an EARLIER sentence having been INTERPRETED (confirmed
     live: ListNotations' `[...]` only parses once `Import` is actually
     run, not merely parsed), silently under-counting the per-request
     guard's comparison depth below the real prefix's length -- a sibling
     file could then share only that SHORTER guard-checked run, diverge
     in its own content right after it, and still inherit the REAL
     (longer) prefix's effects via fork. Parsing now, after the real
     compile has already interpreted every prefix sentence in this very
     process, means any such notation is already active, so this re-parse
     reaches exactly as far as the real compile did. ~exhaustive:true is
     the backstop for anything that can still make the two diverge: it
     turns "stopped before reaching the file's own end" into a hard
     refusal instead of a silently short count. *)
  let prefix_sentences =
    try Array.of_list (peek_sentences ~exhaustive:true ~max_n:max_int prefix_file)
    with Truncated_before_eof ->
      Printf.eprintf
        "rocq-zygote: prefix file %s has content past a sentence this \
         self-check cannot parse even after the real warm-up compile \
         succeeded on the whole file -- the per-request guard's \
         comparison length could not be trusted to cover the whole \
         prefix; refusing to serve\n%!" prefix_file;
      exit 2
  in
  if Array.length prefix_sentences = 0 then begin
    Printf.eprintf "rocq-zygote: prefix file %s has no sentences, refusing to serve\n%!" prefix_file;
    exit 2
  end;
  let fingerprint = capture_fingerprint () in
  serve_forever opts stm_opts injections ~prefix_sentences ~coqlibs:zargs.coqlibs
    ~fingerprint ~socket_path ~idle_timeout:zargs.idle_timeout

let custom_zygote
  : ((zygote_args * Coqcargs.t * Colors.color) * Stm.AsyncOpts.stm_opt, Coqargs.injection_command list) Coqtop.custom_toplevel
  = Coqtop.{
    parse_extra = (fun opts extras ->
      let zargs, extras = parse_zygote_extra extras in
      let color_mode, extras = Colors.parse_extra_colors ~emacs:opts.config.print_emacs extras in
      let stm_opts, extras = Stmargs.parse_args opts extras in
      let coqc_opts = Coqcargs.parse extras in
      ((zargs, coqc_opts, color_mode), stm_opts), []);
    usage = zygote_specific_usage;
    init_extra = (fun ((_, _, color_mode), _) injections ~opts ->
      Flags.quiet := true;
      System.trust_file_cache := true;
      Colors.init_color color_mode;
      ignore opts;
      injections);
    run = (fun ((zargs, coqc_opts, _color), stm_opts) ~opts injections ->
      match zargs.dump_sentences with
      | Some max_n ->
        let file = match coqc_opts.Coqcargs.compile_file with
          | Some (f, _) -> f
          | None -> Printf.eprintf "rocq-zygote: --rocq-zygote-dump-sentences needs a file argument\n%!"; exit 2
        in
        run_dump_sentences max_n file
      | None -> zygote_run zargs ~opts stm_opts injections);
    initial_args = Coqargs.default;
  }

let main args = Coqtop.start_coq custom_zygote args

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  main args
