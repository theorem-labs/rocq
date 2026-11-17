(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open System
open Names
open Environ

let () = at_exit flush_all

let fatal_error info code =
  flush_all (); Format.eprintf "@[Fatal Error: @[%a@]@]@\n%!" Pp.pp_with info; flush_all ();
  exit code

let rocq_root = Id.of_string "Corelib"
let parse_dir s =
  let len = String.length s in
  let rec decoupe_dirs dirs n =
    if n>=len then dirs else
    let pos =
      try
        String.index_from s n '.'
      with Not_found -> len
    in
    let dir = String.sub s n (pos-n) in
      decoupe_dirs (dir::dirs) (pos+1)
  in
    decoupe_dirs [] 0
let dirpath_of_string s =
  match parse_dir s with
  | [] -> CheckLibrary.default_root_prefix
  | dir -> DirPath.make (List.map Id.of_string dir)
let path_of_string s =
  if Filename.check_suffix s ".vo" then Ok (CheckLibrary.PhysicalFile s)
  else match parse_dir s with
    | [] -> Error ()
    | l::dir -> Ok (CheckLibrary.LogicalFile {dirpath=dir; basename=l})

let get_version env () =
  match env with
  | Boot.Env.Boot -> Coq_config.version
  | Env env ->
  try
    let revision = Boot.Env.(Path.to_string (revision env)) in
    let ch = open_in revision in
    let ver = input_line ch in
    let rev = input_line ch in
    let () = close_in ch in
    Printf.sprintf "%s (%s)" ver rev
  with Sys_error _ | End_of_file -> Coq_config.version

let print_header env () =
  Printf.printf "Welcome to Chicken %s\n%!" (get_version env ())

(* Adding files to Rocq loadpath *)

let add_path ~unix_path:dir ~rocq_root:rocq_dirpath =
  if exists_dir dir then
    begin
      CheckLibrary.add_load_path (dir,rocq_dirpath)
    end
  else
    Feedback.msg_warning (str "Cannot open " ++ str dir)

let convert_string d =
  try Id.of_string d
  with CErrors.UserError _ ->
    Flags.if_verbose Feedback.msg_warning
      (str "Directory " ++ str d ++ str " cannot be used as a Rocq identifier (skipped)");
    raise_notrace Exit

let add_rec_path ~unix_path ~rocq_root =
  if exists_dir unix_path then
    let dirs = all_subdirs ~unix_path in
    let prefix = DirPath.repr rocq_root in
    let convert_dirs (lp, cp) =
      try
        let path = List.rev_map convert_string cp @ prefix in
        Some (lp, Names.DirPath.make path)
      with Exit -> None
    in
    let dirs = List.map_filter convert_dirs dirs in
    List.iter CheckLibrary.add_load_path dirs;
    CheckLibrary.add_load_path (unix_path, rocq_root)
  else
    Feedback.msg_warning (str "Cannot open " ++ str unix_path)

(* By the option -R/-Q of the command line *)
let includes = ref []
(* The same roots, kept past [init_with_argv]: a -compare run puts the
   challenge directory on the load path in place of the physical directory
   of each of these roots that the challenge stands in for, under the same
   logical root ([run_compare]). *)
let user_includes = ref []
let push_include (s, alias) = includes := (s,alias) :: !includes

let set_include d p =
  let p = if String.equal p "Coq" then "Corelib" else p in
  let p = dirpath_of_string p in
  push_include (d,p)

(* Used by option -package. *)
let packages = ref []
let add_package p = packages := p :: !packages

let resolve_packages () =
  let ps = Rocq_package.resolve !packages in
  packages := [];
  List.iter (fun p -> set_include p.Rocq_package.dir p.Rocq_package.logpath) ps

(* Used by options -compare, -challenge and -compare-out
   ([rocqchk -compare CONFIG -challenge DIR -compare-out FILE]). *)
let compare_config = ref None
let compare_challenge = ref None
let compare_out = ref None

(* Used by option -sha256. *)
let sha256_printed = ref false

(* The top-level names that the installed load path serves without a -Q:
   the corelib root, and the subdirectories of every directory bound
   recursively under the empty root (user-contrib, the XDG directories and
   ROCQPATH). The working directory is bound non-recursively, so its
   subdirectories serve no library and are not names here; its own
   top-level .vo files are served under one-word names that this list does
   not hold, which is why a -compare run starts in a working directory that
   holds no .vo. A -compare run refuses a -Q that binds one of these names,
   or the empty root, which would let the solution's directory shadow a
   library that the challenge reads from the installation. Filled by
   [init_load_path] in a -compare run; empty under -boot. *)
let installed_roots = ref []

let note_installed_roots ~unix_path ~rocq_root =
  match List.rev (DirPath.repr rocq_root) with
  | id :: _ -> installed_roots := Id.to_string id :: !installed_roots
  | [] ->
    if exists_dir unix_path then
      (* a directory that cannot be listed, or one removed since the test
         above, gives no root rather than raising, as [all_subdirs] does
         through [System]'s own guarded readdir; a root that cannot be seen
         shadows nothing *)
      let entries = try Sys.readdir unix_path with Sys_error _ -> [||] in
      Array.iter (fun e ->
          if exists_dir (Filename.concat unix_path e) then
            installed_roots := e :: !installed_roots)
        entries

(* Initializes the LoadPath *)
let init_load_path rocqenv =
  (* the to_string casting won't be necessary once Boot handles
     include paths *)
  let plugins = Boot.Env.plugins rocqenv |> Boot.Path.to_string in
  let theories = Boot.Env.corelib rocqenv |> Boot.Path.to_string in
  let user_contrib = Boot.Env.user_contrib rocqenv |> Boot.Path.to_string in
  let xdg_dirs = Envars.xdg_dirs in
  let rocqpath = Envars.coqpath in
  let add_rec_path ~unix_path ~rocq_root =
    if Option.has_some !compare_config then note_installed_roots ~unix_path ~rocq_root;
    add_rec_path ~unix_path ~rocq_root
  in
  (* NOTE: These directories are searched from last to first *)
  (* first standard library *)
  add_rec_path ~unix_path:theories ~rocq_root:(Names.DirPath.make[rocq_root]);
  (* then plugins *)
  add_rec_path ~unix_path:plugins ~rocq_root:(Names.DirPath.make [rocq_root]);
  (* then user-contrib *)
  if Sys.file_exists user_contrib then
    add_rec_path ~unix_path:user_contrib ~rocq_root:CheckLibrary.default_root_prefix;
  (* then directories in XDG_DATA_DIRS and XDG_DATA_HOME *)
  List.iter (fun s -> add_rec_path ~unix_path:s ~rocq_root:CheckLibrary.default_root_prefix)
    (xdg_dirs ~warn:(fun x -> Feedback.msg_warning (str x)));
  (* then directories in ROCQPATH *)
  List.iter (fun s -> add_rec_path ~unix_path:s ~rocq_root:CheckLibrary.default_root_prefix) (rocqpath());
  (* then current directory: bound non-recursively, so it adds no installed
     root (see [installed_roots]) *)
  add_path ~unix_path:"." ~rocq_root:CheckLibrary.default_root_prefix

let init_load_path env : unit =
  NewProfile.profile "init_load_path"
    (fun () -> init_load_path env)
    ()

let impredicative_set = ref false
let set_impredicative_set () = impredicative_set := true

let boot = ref false
let set_boot () = boot := true

let coqlib = ref None
let set_coqlib v = coqlib := Some v

let indices_matter = ref false

let enable_vm = ref false

let output_context = ref false

let warn_no_bytecode =
  CWarnings.create ~name:"bytecode-compiler-disabled" ~category:CWarnings.CoreCategories.bytecode_compiler
    Pp.(fun () ->
        str "Bytecode compiler is disabled," ++ spc() ++
        str "-bytecode-compiler option ignored.")

let make_senv () =
  let senv = Safe_typing.empty_environment in
  let senv = Safe_typing.set_impredicative_set !impredicative_set senv in
  let senv = Safe_typing.set_indices_matter !indices_matter senv in
  let senv =
    if !enable_vm && not Coq_config.bytecode_compiler then begin
      warn_no_bytecode ();
      senv
    end else begin
      CheckFlags.enable_vm := !enable_vm;
      Safe_typing.set_VM !enable_vm senv
    end
  in
  let senv = Safe_typing.set_allow_sprop true senv in (* be smarter later *)
  Safe_typing.set_native_compiler false senv

let try_add_path s l = match path_of_string s with
| Ok path -> path :: l
| Error () -> CErrors.user_err (str "Invalid path " ++ qstring s)

let admit_list = ref ([] : CheckLibrary.object_file list)
let add_admit s =
  admit_list := try_add_path s !admit_list

let norec_list = ref ([] : CheckLibrary.object_file list)
let add_norec s =
  norec_list := try_add_path s !norec_list

let compile_list = ref ([] : CheckLibrary.object_file list)
let add_compile s =
  compile_list := try_add_path s !compile_list

(*s Parsing of the command line.
    We no longer use [Arg.parse], in order to use share [Usage.print_usage]
    between coqtop and coqc. *)

(* -compare also reads the admitted libraries: the config's pre-checked
   libraries are on the admit list, and one that no checked library depends
   on must be loaded too. *)
let compile_files senv =
  CheckLibrary.recheck_library ~output_context:(!output_context || !CheckFlags.axiom_free)
    ~intern_admit:(Option.has_some !compare_config) senv
    ~norec:(List.rev !norec_list)
    ~admit:(List.rev !admit_list)
    ~check:(List.rev !compile_list)

let version () =
  Printf.printf "The Rocq Proof Checker, version %s\n" Coq_config.version;
  exit 0

(* print the usage of coqtop (or coqc) on channel co *)

let print_usage_channel co command =
  output_string co command;
  output_string co "coqchk options are:\n";
  output_string co
"\
\n  -Q dir coqdir               map physical dir to logical coqdir\
\n  -R dir coqdir               synonymous for -Q\
\n  -coqlib dir                 set coqchk's standard library location\
\n  -boot                       don't initialize the library paths automatically\
\n\
\n  -admit module               load module and dependencies without checking\
\n  -norec module               check module but admit dependencies without checking\
\n\
\n  -d (d1,..,dn)               enable specified debug messages\
\n  -debug                      enable all debug messages\
\n  -profile file               output profiling info to file\
\n  -where                      print coqchk's standard library location and exit\
\n  -v, --version               print coqchk version and exit\
\n  -o, --output-context        print the list of assumptions\
\n  -axiom-free                 fail if axioms or unsafe features are used\
\n  -m, --memory                print the maximum heap size\
\n  -silent                     disable trace of constants being checked\
\n  -compare config             compare the checked solution with a challenge\
\n  -challenge dir              the challenge's directory (with -compare)\
\n  -compare-out file           write the verdict of -compare to file\
\n  -sha256 file                print the SHA-256 of file and exit\
\n\
\n  -impredicative-set          set sort Set impredicative\
\n  -indices-matter             levels of indices (and nonuniform parameters)\
\n                              contribute to the level of inductives\
\n  -bytecode-compiler (yes|no) enable the vm_compute reduction machine (default is no)\
\n\
\n  -h, --help                  print this list of options\
\n"

(* print the usage on standard error *)

let print_usage = print_usage_channel stderr

let print_usage_rocqtop () =
  print_usage "Usage: coqchk <options> modules\n\n"

let usage exitcode =
  print_usage_rocqtop ();
  flush stderr;
  exit exitcode

open Type_errors

let anomaly_string () = str "Anomaly: "
let report () = strbrk (". Please report at " ^ Coq_config.wwwbugtracker ^ ".")

let guill s = str "\"" ++ str s ++ str "\""

let explain_exn = function
  | Sys_error msg ->
      hov 0 (anomaly_string () ++ str "uncaught exception Sys_error " ++ guill msg ++ report() )
  | UserError pps ->
      hov 1 (str "User error: " ++ pps)
  | Out_of_memory ->
      hov 0 (str "Out of memory")
  | Stack_overflow ->
      hov 0 (str "Stack overflow")
  | Match_failure(filename,pos1,pos2) ->
      hov 1 (anomaly_string () ++ str "Match failure in file " ++
             guill filename ++ str " at line " ++ int pos1 ++
             str " character " ++ int pos2 ++ report ())
  | Not_found ->
      hov 0 (anomaly_string () ++ str "uncaught exception Not_found" ++ report ())
  | Failure s ->
      hov 0 (str "Failure: " ++ str s ++ report ())
  | Invalid_argument s ->
      hov 0 (anomaly_string () ++ str "uncaught exception Invalid_argument " ++ guill s ++ report ())
  | Sys.Break ->
    hov 0 (fnl () ++ str "User interrupt.")
  | UGraph.UniverseInconsistency i ->
    let msg =
      if CDebug.(get_flag misc) then
        str "." ++ spc() ++
          UGraph.explain_universe_inconsistency Sorts.raw_printer i
      else
        mt() in
    hov 0 (str "Error: Universe inconsistency" ++ msg ++ str ".")
  | QGraph.EliminationError e ->
    let msg =
      if CDebug.(get_flag misc) then
        str "." ++ spc() ++
          QGraph.explain_elimination_error Sorts.Quality.raw_printer e
      else
        mt() in
    hov 0 (str "Error: Elimination error" ++ msg ++ str ".")
  | TypeError(ctx,te) ->
      hov 0 (str "Type error: " ++
      (match te with
      | UnboundRel i -> str"UnboundRel " ++ int i
      | UnboundVar v -> str"UnboundVar" ++ str(Names.Id.to_string v)
      | NotAType _ -> str"NotAType"
      | BadAssumption _ -> str"BadAssumption"
      | ReferenceVariables _ -> str"ReferenceVariables"
      | ElimArity _ -> str"ElimArity"
      | CaseNotInductive _ -> str"CaseNotInductive"
      | CaseOnPrivateInd _ -> str"CaseOnPrivateInd"
      | WrongCaseInfo _ -> str"WrongCaseInfo"
      | NumberBranches _ -> str"NumberBranches"
      | IllFormedBranch _ -> str"IllFormedBranch"
      | IllFormedCaseParams -> str "IllFormedCaseParams"
      | BadProjType _ -> str "BadProjType"
      | Generalization _ -> str"Generalization"
      | ActualType _ -> str"ActualType"
      | IncorrectPrimitive _ -> str"IncorrectPrimitive"
      | CantApplyBadType ((n,a,b),{uj_val = hd; uj_type = hdty},args) ->
        let pp_arg i judge =
          hv 1 (str"arg " ++ int (i+1) ++ str"= " ++
                Constr.debug_print judge.uj_val ++
                str ",type= " ++ Constr.debug_print judge.uj_type) ++ fnl ()
        in
        Feedback.msg_notice (str"====== ill-typed term ====" ++ fnl () ++
                       hov 2 (str"application head= " ++ Constr.debug_print hd) ++ fnl () ++
                       hov 2 (str"head type= " ++ Constr.debug_print hdty) ++ fnl () ++
                       str"arguments:" ++ fnl () ++ hv 1 (prvecti pp_arg args));
        Feedback.msg_notice (str"====== type error ====@" ++ fnl () ++
                             Constr.debug_print b ++ fnl () ++
                             str"is not convertible with" ++ fnl () ++
                             Constr.debug_print a ++ fnl ());
        Feedback.msg_notice (str"====== universes ====" ++ fnl () ++
                             (UGraph.pr_universes Univ.Level.raw_pr
                                (UGraph.repr (Environ.universes ctx))));
        str "CantApplyBadType at argument " ++ int n
      | CantApplyNonFunctional _ -> str"CantApplyNonFunctional"
      | IllFormedRecBody _ -> str"IllFormedRecBody"
      | IllTypedRecBody _ -> str"IllTypedRecBody"
      | UnsatisfiedUnivConstraints _ -> str"UnsatisfiedUnivConstraints"
      | UnsatisfiedPConstraints _ -> str"UnsatisfiedPConstraints"
      | NotAllowedSProp -> str"NotAllowedSProp"
      | BadBinderRelevance _ -> str"BadBinderRelevance"
      | BadCaseRelevance _ -> str"BadCaseRelevance"
      | BadInvert -> str"BadInvert"
      | UndeclaredQualities _ -> str"UndeclaredQualities"
      | UndeclaredUniverses _ -> str"UndeclaredUniverse"
      | BadVariance _ -> str "BadVariance"
      | UndeclaredUsedVariables _ -> str "UndeclaredUsedVariables"
      | IllFormedConstant _ -> str "IllFormedConstant"
      | IllFormedInductive _ -> str "IllFormedInductive"
      | TooLargeArrayLiteral _ -> str "TooLargeArrayLiteral"
      ))

  | InductiveError (env,e) ->
      hov 0 (str "Error related to inductive types")
(*      let ctx = Check.get_env() in
      hov 0
        (str "Error:" ++ spc () ++ Himsg.explain_inductive_error ctx e)*)

  | CheckInductive.InductiveMismatch (mind,field) ->
    hov 0 (MutInd.print mind ++ str ": field " ++ str field ++ str " is incorrect.")

  | Mod_checking.BadConstant (cst, why) ->
    hov 0 (Constant.print cst ++ spc() ++ why)

  | Modops.ModuleTypingError _ ->
    hov 0 (str "Module typing error")

  | Assert_failure (s,b,e) ->
      hov 0 (anomaly_string () ++ str "assert failure" ++ spc () ++
               (if s = "" then mt ()
                else
                  (str "(file \"" ++ str s ++ str "\", line " ++ int b ++
                   str ", characters " ++ int e ++ str "-" ++
                   int (e+6) ++ str ")")) ++
               report ())
  | e -> CErrors.print e (* for anomalies and other uncaught exceptions *)

let profile = ref None

(* The verdict file of a -compare run is removed first, before the command
   line is parsed or anything is checked, so that a run that stops early (a
   usage error, a malformed config, a challenge file's sha256, a solution
   that fails its check) leaves no earlier run's verdict where a reader
   would take it for this run's. The file is the argument after any
   "-compare-out" token. One that cannot be removed is emptied, which no
   reader takes for a verdict. *)
let remove_stale_verdicts args =
  let rec scan = function
    | "-compare-out" :: f :: rem ->
      (try Sys.remove f with Sys_error _ ->
         try close_out (open_out_gen [Open_wronly; Open_trunc] 0 f) with Sys_error _ -> ());
      scan rem
    | _ :: rem -> scan rem
    | [] -> ()
  in
  scan args

let parse_args argv =
  let rec parse = function
    | [] -> ()
    | "-impredicative-set" :: rem ->
      set_impredicative_set (); parse rem

    | "-indices-matter" :: rem ->
      indices_matter:=true; parse rem

    | "-bytecode-compiler" :: "yes" :: rem ->
      enable_vm := true; parse rem
    | "-bytecode-compiler" :: "no" :: rem ->
      enable_vm := false; parse rem

    | "-coqlib" :: s :: rem ->
      if not (exists_dir s) then
        fatal_error (str "Directory '" ++ str s ++ str "' does not exist") 1;
      set_coqlib s;
      parse rem

    | "-boot" :: rem ->
      set_boot ();
      parse rem

    | ("-Q"|"-R") :: d :: p :: rem -> set_include d p;parse rem
    | ("-Q"|"-R") :: ([] | [_]) -> usage 1

    | "-package" :: p :: rem -> add_package p; parse rem
    | "-package" :: [] -> usage 1

    | "-d" :: s :: rem ->
      CDebug.set_flags s;
      parse rem
    | "-debug" :: rem -> CDebug.set_debug_all true; parse rem

    | "-profile" :: s :: rem ->
      profile := Some s;
      parse rem

    | "-profile" :: [] -> usage 1

    | "-where" :: _ ->
      let env = Boot.Env.init_with ~coqlib:!coqlib in
      let rocqlib = Boot.Env.coqlib env |> Boot.Path.to_string in
      print_endline rocqlib;
      exit 0

    | ("-?"|"-h"|"-H"|"-help"|"--help") :: _ -> usage 0

    | ("-v"|"--version") :: _ -> version ()
    | ("-m" | "--memory") :: rem -> Check_stat.memory_stat := true; parse rem
    | ("-o" | "--output-context") :: rem ->
        output_context := true; parse rem

    | "-axiom-free" :: rem -> CheckFlags.axiom_free := true; parse rem

    | "-admit" :: s :: rem -> add_admit s; parse rem
    | "-admit" :: [] -> usage 1

    | "-norec" :: s :: rem -> add_norec s; parse rem
    | "-norec" :: [] -> usage 1

    | "-silent" :: rem ->
        Flags.quiet := true; parse rem

    | "-compare" :: f :: rem ->
        (* Read now, so that a malformed config stops the run before any
           library is loaded. A pre-checked library loads without a check,
           through the admit list. *)
        let cfg = Check_compare.read_config f in
        List.iter add_admit (Check_compare.prechecked_libraries cfg);
        compare_config := Some cfg; parse rem
    | "-compare" :: [] -> usage 1

    | "-challenge" :: d :: rem ->
        if not (exists_dir d) then
          fatal_error (str "Directory '" ++ str d ++ str "' does not exist") 1;
        compare_challenge := Some d; parse rem
    | "-challenge" :: [] -> usage 1

    | "-compare-out" :: f :: rem -> compare_out := Some f; parse rem
    | "-compare-out" :: [] -> usage 1

    | "-sha256" :: f :: rem ->
        print_endline (Check_compare.sha256_of_file f);
        sha256_printed := true; parse rem
    | "-sha256" :: [] -> usage 1

    | s :: _ when s<>"" && s.[0]='-' ->
        fatal_error (str "Unknown option " ++ str s) 1
    | s :: rem ->  add_compile s; parse rem
  in
  let args = List.tl (Array.to_list argv) in
  remove_stale_verdicts args;
  parse args;
  (* -sha256 prints the digest a config gives, and does nothing else. *)
  if !sha256_printed then exit 0;
  begin match !compare_config, !compare_challenge, !compare_out with
  | None, None, None | Some _, Some _, Some _ -> ()
  | _ ->
    fatal_error
      (str "Options -compare, -challenge and -compare-out go together.") 1
  end;
  (* A package's directory would be a load path that the config does not
     pin and that the challenge does not stand in for. *)
  if Option.has_some !compare_config && not (List.is_empty !packages) then
    fatal_error
      (str "Option -package cannot be used with -compare: a package's directory \
            is a load path that the config does not pin.") 1

let init_profile ~file =
  let ch = open_out file in
  let fname = Filename.basename file in
  NewProfile.init { output = Format.formatter_of_out_channel ch; fname; };
  at_exit (fun () ->
      NewProfile.finish ();
      close_out ch)

(* XXX: At some point we need to either port the checker to use the
   feedback system or to remove its use completely. *)
let init_with_argv argv =
  let _fhandle = Feedback.(add_feeder (console_feedback_listener Format.err_formatter)) in
  try
    parse_args argv;
    Option.iter (fun file -> init_profile ~file) !profile;
    if CDebug.(get_flag misc) then Printexc.record_backtrace true;
    let coqenv = Boot.Env.maybe_init ~boot:!boot ~coqlib:!coqlib
        ~warn_ignored_coqlib:CWarnings.warn_ignored_coqlib
    in
    Flags.if_verbose (fun () -> print_header coqenv ()) ();
    let () = match coqenv with
      | Boot -> ()
      | Env coqenv -> init_load_path coqenv
    in
    (* the -R/-Q roots alone, taken before -package adds its roots, which
       -compare refuses *)
    user_includes := List.rev !includes;
    (* additional loadpath, given with -R/-Q options *)
    resolve_packages ();
    NewProfile.profile "add_load_paths" (fun () ->
        List.iter
          (fun (unix_path, rocq_root) -> add_rec_path ~unix_path ~rocq_root)
          (List.rev !includes))
      ();
    includes := [];
    make_senv ()
  with e ->
    fatal_error (str "Error during initialization :" ++ (explain_exn e)) (CErrors.exit_code e)

let init() = init_with_argv Sys.argv

let fatal_exn e =
  if CDebug.(get_flag misc) then Printexc.print_backtrace stderr;
  fatal_error (explain_exn e) (CErrors.exit_code e)

let run senv =
  try
    let senv = compile_files senv in
    flush_all(); senv
  with e -> fatal_exn e

(* A run that cannot complete the comparison (a challenge file whose sha256
   differs, a pre-checked library the two sides disagree on, a theorem the
   challenge does not hold) exits non-zero and writes no verdict file. A
   verdict, whatever it says, leaves the exit status at 0. [empty_senv] is
   the empty environment [init] made, which the challenge is loaded on. *)
let run_compare env empty_senv =
  match !compare_config with
  | None -> ()
  | Some cfg ->
    let dir = Option.get !compare_challenge and out = Option.get !compare_out in
    (* The challenge directory stands in for the solution's directory under
       each root that a solution library named on the command line lives
       under. A root that only a pre-checked library or another shared tree
       uses is left alone: the challenge directory does not hold it.

       Both forms that name a library to check count: the positional names
       ([compile_list], checked with their dependencies) and -norec
       ([norec_list], checked alone), each by the library name the loader
       gave it, so that a .vo file counts by its logical name. -admit names
       a library to load without checking it and never selects a solution
       library, so [admit_list] is left out: it also holds the config's
       pre-checked libraries, which are exactly the ones the challenge does
       not stand in for. *)
    let checked_names =
      List.map (fun f -> fst (CheckLibrary.try_locate_qualified_library f))
        (!compile_list @ !norec_list)
    in
    let substitutes root = List.exists (CheckLibrary.under_root ~root) checked_names in
    (* A library under one of those roots is the solution's own: the
       challenge directory holds its counterpart. Every other library the
       solution loaded is a shared one, from the installation, and the
       challenge environment loads the same ones, so that a constraint one
       of them carries is not read as a constraint the solution invented.

       This rests on every solution library being checked in this run (none
       is given with -admit): a library of the solution's own then lives
       under a root that some checked name lives under, which is a root the
       challenge stands in for; what is left is the installation's. *)
    let under_challenge_root lib =
      List.exists (fun (_, rocq_root) ->
          substitutes rocq_root && CheckLibrary.under_root ~root:rocq_root lib)
        !user_includes
    in
    (* The bound roots the challenge does not stand in for. The solution's
       build can write under one of them, so the comparator refuses a run
       that loaded a library from one unless the config pins it. *)
    let open_roots =
      List.map_filter (fun (unix_path, rocq_root) ->
          if substitutes rocq_root then None else Some (rocq_root, unix_path))
        !user_includes
    in
    (* A -Q that binds one of the installed load path's own top-level names,
       or the empty root, puts the solution's directory where a library that
       the challenge reads from the installation is looked up: the two sides
       would then read different files under one name, and the one the
       solution wrote would decide. The empty root binds every name. This is
       refused outright, because no config can make it safe, and a run needs
       only one bound root, the solution's own. *)
    List.iter (fun (unix_path, rocq_root) ->
        let head = match List.rev (DirPath.repr rocq_root) with
          | [] -> None
          | id :: _ -> Some (Id.to_string id)
        in
        match head with
        | None ->
          fatal_error
            (str ("The directory " ^ unix_path ^ " is bound to the empty root, which binds \
                   every library name the installed load path serves. A -compare run \
                   refuses it."))
            1
        | Some h when List.exists (String.equal h) !installed_roots ->
          fatal_error
            (str ("The directory " ^ unix_path ^ " is bound to " ^ DirPath.to_string rocq_root ^
                  ", a name the installed load path serves. A -compare run refuses it: the \
                   two sides would read different files under one library name."))
            1
        | Some _ -> ())
      !user_includes;
    try
      let t =
        Check_compare.prepare cfg ~dir ~out ~under_challenge_root ~open_roots
          ~bound_dirs:(List.map fst !user_includes)
          ~add_challenge_load_path:(fun () ->
              List.iter (fun (_, rocq_root) ->
                  if substitutes rocq_root then add_rec_path ~unix_path:dir ~rocq_root)
                !user_includes)
      in
      Check_compare.run t env empty_senv
    with e -> fatal_exn e

let main () =
  let empty_senv = init() in
  let senv, axioms = run empty_senv in
  let env = Safe_typing.env_of_safe_env senv in
  run_compare env empty_senv;
  Check_stat.stats env (if !output_context then Some axioms else None);
  if !CheckFlags.axiom_free && not (Mod_checking.is_axiom_free env axioms) then
    fatal_error (str "Axioms or unsafe features found (-axiom-free).") 1;
  exit 0
