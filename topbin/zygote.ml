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
   vernac/library.ml's libraries_table is a plain, process-global `ref`,
   not scoped to any STM document -- `intern_library` treats an
   already-loaded dependency as terminal and skips re-registering it
   entirely, never even calling Declaremods.Interp.register_library for
   it). A cached-nametab-fragment prototype (Sections 17-19) was proven
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
                                             zygote's recorded prefix; caller must fall back
                                             to an ordinary, non-zygote compile.
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
   same as EOF: stop and return what was cleanly parsed so far. *)
let peek_sentences ~max_n file =
  let content = read_file file in
  let ic = open_in_bin file in
  Fun.protect ~finally:(fun () -> close_in ic) (fun () ->
    let pa = Procq.Parsable.make
        ~loc:Loc.(initial (InFile { dirpath = None; file }))
        (Gramlib.Stream.of_channel ic) in
    let rec loop n acc =
      if n <= 0 then List.rev acc
      else match Procq.Entry.parse (Pvernac.main_entry None) pa with
        | None -> List.rev acc
        | Some { CAst.loc = Some loc; _ } ->
          let text = String.sub content loc.Loc.bp (loc.Loc.ep - loc.Loc.bp) in
          loop (n - 1) (text :: acc)
        | Some { CAst.loc = None; _ } -> List.rev acc
        | exception _ -> List.rev acc
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
let handle_connection opts stm_opts injections ~prefix_sentences ~coqlibs ~warm_counters conn =
  Unix.set_close_on_exec conn;
  (* Always move onto a fresh descriptor before we repoint fd 0/1/2 for the
     compile's own stdout/stderr -- stdin/stdout/stderr are already open in
     this process, so dup never returns one of them. *)
  let moved = Unix.dup conn in
  Unix.close conn;
  let conn = moved in
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
      (* Restore the universe/sort name counters to the value the warm-up
         left them at -- the value a fresh process has after the same
         Requires. new_doc (inside compile below) restores the warmed-up
         summary state (libraries kept, so no Require touches disk) but does
         NOT touch these counters, and a forked child inherits the warm-up's
         value via copy-on-write anyway; setting them explicitly makes the
         guarantee independent of fork state. The child's own file then
         numbers its universes from exactly where a fresh compile would. *)
      UnivGen.set_counters warm_counters;
      (* Resolve the file path exactly as Coqcargs.add_compile does for a stock
         `rocq compile`: an implicit (cwd-relative, no leading ./ or ../) path
         gets `./` prepended, and that literal string is what ends up in every
         stored Loc. Skipping it would embed "F.v" where a fresh compile embeds
         "./F.v" (likewise "dir/F.v" vs "./dir/F.v"). The output name is not
         embedded, so it is passed through unchanged. *)
      let file =
        if Filename.is_implicit file
        then Filename.concat Filename.current_dir_name file
        else file
      in
      let copts = Coqcargs.{ default with
        compile_file = Some (file, echo = "1");
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

let serve_forever opts stm_opts injections ~prefix_sentences ~coqlibs ~warm_counters ~socket_path ~idle_timeout =
  (try Unix.unlink socket_path with Sys_error _ | Unix.Unix_error _ -> ());
  let sock = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
  Unix.bind sock (Unix.ADDR_UNIX socket_path);
  Unix.listen sock 64;
  Printf.eprintf "rocq-zygote: warm-up complete (%d-sentence prefix), listening on %s\n%!"
    (Array.length prefix_sentences) socket_path;
  let rec loop () =
    reap_finished_children ();
    let readable =
      if idle_timeout > 0.0 then
        let r, _, _ = Unix.select [sock] [] [] idle_timeout in r
      else [sock]
    in
    match readable with
    | [] ->
      Printf.eprintf "rocq-zygote: idle timeout, exiting\n%!";
      (try Unix.unlink socket_path with _ -> ());
      exit 0
    | _ ->
      (match Unix.accept sock with
       | conn, _ ->
         flush_all ();
         (match Unix.fork () with
          | 0 ->
            Unix.close sock;
            handle_connection opts stm_opts injections ~prefix_sentences ~coqlibs ~warm_counters conn
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
  (* Record the prefix as parsed sentences (the same comparison the server
     loop uses per request), BEFORE the warm-up compile touches global
     state, from the untouched scratch file. *)
  let prefix_sentences = Array.of_list (peek_sentences ~max_n:max_int prefix_file) in
  if Array.length prefix_sentences = 0 then begin
    Printf.eprintf "rocq-zygote: prefix file %s has no sentences, refusing to serve\n%!" prefix_file;
    exit 2
  end;
  (* One-time warm-up, done ONCE in this pre-fork process. Replay exactly the
     opening of a fresh coqc compile -- new_doc (which opens a throwaway library
     and loads the prelude injections) then load the shared prefix's Requires --
     but STOP right after the Requires, before any Stm.finish / save. This is the
     only place the heavy Require/Nametab work happens, and it leaves the process
     at precisely the point a fresh compile reaches just before its file body:
     the name counters here are the values that body would start from. *)
  let long_f_dot_out = (try Filename.chop_extension prefix_file with _ -> prefix_file) ^ ".vo" in
  let check = Stm.AsyncOpts.(stm_opts.async_proofs_mode = APoff) in
  (* A fresh coqc process has allocated no global names when it reaches its
     compile's new_doc; this daemon, however, has already run its own startup
     (argument parsing, prefix peeking, feeder setup), which may have bumped the
     name counters. Zero them here so the warm-up's trajectory -- and therefore
     the post-Require snapshot below -- matches a fresh process exactly. *)
  UnivGen.set_counters (0, 0);
  (try
    Topfmt.(in_phase ~phase:CompilationPhase) (fun () ->
      let open Vernac.State in
      let doc, sid = Topfmt.(in_phase ~phase:LoadingPrelude)
          Stm.new_doc Stm.{ doc_type = VoDoc long_f_dot_out; injections } in
      let state = { doc; sid; proof = None; time = None } in
      let state = Load.load_init_vernaculars opts ~state in
      let ldir = Stm.get_ldir ~doc:state.doc in
      Dumpglob.push_output Dumpglob.NoGlob;
      let source = Loc.InFile { dirpath = Some (Names.DirPath.to_string ldir); file = prefix_file } in
      ignore (Vernac.load_vernac ~echo:false ~check ~state ~source prefix_file : Vernac.State.t))
      ()
  with exn ->
    flush_all ();
    Topfmt.print_err_exn exn;
    flush_all ();
    Printf.eprintf "rocq-zygote: prefix warm-up failed, refusing to serve\n%!";
    exit 1);
  (* Snapshot the universe/sort name counters NOW -- after the Requires, before
     any finish/save could advance them -- so each child restores exactly the
     value a fresh compile has when it starts the file body. *)
  let warm_counters = UnivGen.get_counters () in
  (* The load above left the process mid-library (the throwaway prefix's). Drop
     that library's object stacks (Lib) and reset the kernel's module-building
     state to its pristine, is_initial values -- but keep every summary the
     Requires populated (the library table, nametab) and the kernel environment /
     universes / opaque table they loaded. The result is exactly the state a
     fresh process has at its initial top level, plus the prefix's Requires
     already loaded, so each forked child's new_doc can start its own library on
     top (Safe_typing.start_library asserts is_initial) without its Requires ever
     touching disk again. *)
  Lib.Synterp.init ();
  Lib.Interp.init ();
  Global.Internal.reset_safe_env
    (Safe_typing.reset_to_initial_keeping_requires (Global.safe_env ()));
  Stm.snapshot_root_state ();
  let (uc, sc) = warm_counters in
  Printf.eprintf "rocq-zygote: warm-up loaded %d-sentence prefix, name counters (univ=%d, sort=%d)\n%!"
    (Array.length prefix_sentences) uc sc;
  serve_forever opts stm_opts injections ~prefix_sentences ~coqlibs:zargs.coqlibs
    ~warm_counters ~socket_path ~idle_timeout:zargs.idle_timeout

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
