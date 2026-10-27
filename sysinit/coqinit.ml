(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** GC tweaking *)

(** Rocq is a heavy user of persistent data structures and symbolic ASTs, so the
    minor heap is heavily solicited. Unfortunately, the default size is far too
    small, so we enlarge it a lot (8 times larger).

    To better handle huge memory consumers, we also augment the GC pressure
    coefficient.

    The two numbers below are measured, not estimated: a proof check allocates tens of gigabytes
    of short-lived terms (lane R2's A0IgPO allocates 10.6 Gwords) and then ends, and on that shape
    both of the collector's costs were much larger than they need to be. Measured on speed-r2 with
    the lane's four files compiled at once, against the former [32*1024*1024] words and [200]
    (per-file wall seconds, median of five interleaved runs of each arm, every range disjoint;
    dispatch://INFRA-217):

      A0IgPO 41.9 -> 35.8, RtLgTopA 41.9 -> 32.5, B0IgPO 38.3 -> 33.4, AMWrapMallocRf 33.7 -> 25.6

    The two values must be chosen together, because what the minor heap costs is cache. Four
    concurrent checks with a 256 MB minor heap each want 1 GB of this box's 480 MB last-level
    cache, so each minor collection walks memory that no cache holds and the four evict each
    other. At the former [space_overhead] a smaller minor heap alone measured slower (8 Mwords:
    A0IgPO 43.1-44.2 s against the base's 41.6-41.9); with a large [space_overhead] the minor heap
    decides the rest of the gain (measured at 3200: A0IgPO 41.5 s at 8 Mwords, 38.0 at 4, 35.8 at 2).

    [space_overhead]: the major collector marks and sweeps in proportion to the allocation, so at
    200 it spends about 1.7 s per file of this lane on a heap of about 2 GB whose garbage no later
    work reuses -- the process ends at the end of the file. 1600 keeps that work small; what it
    costs is heap: max RSS per file grows from about 2.1 GB to about 3.5 GB on the lane's heaviest
    file, which is why it is a number and not "no limit".

    1600 and not more, because a compile process that runs under an address-space ceiling must
    still answer. test-suite/misc/print-assumptions-memo-limits.sh pins one per case, and upstream's
    policy answers under it; at [space_overhead = 3200] two cases run out of memory instead.
    Smallest address space at which each answers, bisected in 10,000 KiB steps on one box
    (OCaml 4.14.2+flambda, -release), against the ceiling the test pins (dispatch://INFRA-213):

                      ceiling    upstream 32 Mwords/200    2 Mwords/3200    2 Mwords/1600
      BlockRetain64   1,000,000        890,000              1,110,000  FAIL     810,000
      AxChain3000       800,000        750,000                990,000  FAIL     580,000

    1600 therefore leaves more room under both ceilings than upstream's own policy does, and it is
    the 2 Mword minor heap that buys most of that room: at 32 Mwords and 1600 BlockRetain64 needs
    1,170,000 KiB. A heap bound cannot replace the smaller number, because [space_overhead] sets how
    far the heap grows while a major cycle runs and compaction only happens at the end of one: with
    3200, [max_overhead] 0 or 80 leaves BlockRetain64 at 1,130,000 KiB and a 1 Mword major heap
    increment makes it 1,180,000.

    What 1600 costs against 3200 is nothing that this lane can measure. On tree r316's Igraph cone
    (206 files, 16 jobs, median of 3 interleaved runs, one box): wall 515.7 s against 512.2, CPU
    1,533 s against 1,521, where upstream's policy takes 548.0 s and 1,588 s. On the heaviest file,
    AgentSubmission/Igraph/RtInitC.v: 471.6 s at 1600, 481.3 s at 3200, 581.4 s under upstream's
    policy, with a peak RSS of 14.8 GiB, 15.9 GiB and 4.0 GiB.

    Neither value changes what rocq computes. OCaml's collector decides when a value moves and when
    its memory is reused, and no result is a function of that. The places that read a GC counter at
    all are reports -- [CObj.heap_size] for -m, [NewProfile], [Mltop.print_gc] -- and zify's
    translation memo (plugins/micromega/zify.ml), which measures a translation with
    [Gc.minor_words], a count of allocation and not of collection, to decide whether to keep it;
    its hits are guarded by [exact_eq], so a different decision there changes work, not results.

    What a GC policy does change is sharing. The hash-consing tables are weak hashsets
    (clib/hashset.ml) and the kernel's bytecode and side-effect caches are ephemerons, so an entry
    whose value is unreachable dies at the next major collection: a policy that collects less keeps
    more entries, and a term built later then shares more with an earlier one. A dead entry costs a
    new representative, never a different term, and every ephemeron reader recomputes on a miss.
    Sharing changes how a term is marshalled, not what it is, so a .vo file can differ byte for byte
    from one built under another policy while holding the same terms -- the variance the lane already
    sees between two runs of one build (lever 7). The lane checks both halves: its normalising
    segment compare for the summary, library and opaques segments, and, for the vmlibrary segment
    that compare leaves out, unmarshalling both and marshalling them again with [No_sharing], which
    gives the same bytes (dispatch://INFRA-217). coqchk does not install this policy at all
    ([init_ocaml]'s only caller is toplevel/coqtop.ml) and compiles its own bytecode.
*)

let set_gc_policy () =
  Gc.set { (Gc.get ()) with
           Gc.minor_heap_size = 2*1024*1024 (* 2Mwords x 8 bytes/word = 16Mb *)
         ; Gc.space_overhead = 120
         }

let set_gc_best_fit () =
  Gc.set { (Gc.get ()) with
           Gc.allocation_policy = 2      (* best-fit *)
         ; Gc.space_overhead = 1600
         }

let init_gc () =
  try
    (* OCAMLRUNPARAM environment variable is set.
     * In that case, we let ocamlrun to use the values provided by the user.
     *)
    ignore (Sys.getenv "OCAMLRUNPARAM")

  with Not_found ->
    (* OCAMLRUNPARAM environment variable is not set.
     * In this case, we put in place our preferred configuration.
     *)
    set_gc_policy ();
    if Coq_config.caml_version_nums >= [4;10;0] then set_gc_best_fit () else ()

let init_ocaml () =
  init_gc ();
  (* Get error message (and backtrace if enabled) on Ctrl-C instead of just exiting the process *)
  Sys.catch_break true

let dirpath_of_file f =
  let ldir0 =
    try
      let lp = Loadpath.find_load_path (Filename.dirname f) in
      Loadpath.logical lp
    with Not_found -> Libnames.default_root_prefix
  in
  let f = try Filename.chop_extension (Filename.basename f) with Invalid_argument _ -> f in
  let id = Names.Id.of_string f in
  let ldir = Libnames.add_dirpath_suffix ldir0 id in
  ldir

let dirpath_of_top = function
  | Coqargs.TopPhysical f -> dirpath_of_file f
  | TopLogical dp -> Libnames.dirpath_of_string dp

let parse_arguments ~parse_extra ?(initial_args=Coqargs.default) args =
  let opts, extras = Coqargs.parse_args ~init:initial_args args in
  let customopts, extras = parse_extra opts extras in
  if not (CList.is_empty extras) then begin
    prerr_endline ("Don't know what to do with "^String.concat " " extras);
    prerr_endline "See -help for the list of supported options";
    exit 1
    end;
  opts, customopts

let print_memory_stat () =
  let open Pp in
  (* -m|--memory from the command-line *)
  Feedback.msg_notice
    (str "total heap size = " ++ int (CObj.heap_size_kb ()) ++ str " kbytes" ++ fnl ());
  (* operf-macro interface:
     https://github.com/OCamlPro/operf-macro *)
  try
    let fn = Sys.getenv "OCAML_GC_STATS" in
    let oc = open_out fn in
    Gc.print_stat oc;
    close_out oc
  with exn when CErrors.noncritical exn -> ()

let to_vo_path (x:Coqargs.vo_path) : Loadpath.vo_path = {
  implicit = x.implicit;
  unix_path = x.unix_path;
  coq_path = Libnames.dirpath_of_string x.rocq_path;
  recursive = true;
  installed = false;
  }

let boot_env usage opts =
  let open Coqargs in
  let with_err = function
    | Ok x -> x
    | Error msg -> CErrors.user_err Pp.(str msg)
  in
  let boot = opts.pre.boot in
  let coqlib = opts.config.coqlib in
  let warn_ignored_coqlib = CWarnings.warn_ignored_coqlib in
  match opts.main with
  | Run -> Boot.Env.maybe_init ~boot ~coqlib ~warn_ignored_coqlib
  | Queries qs ->
    let _ : Boot.Env.maybe_env =
      with_err
        (Boot.Env.print_queries_maybe_init ~warn_ignored_coqlib ~boot ~coqlib (Some usage) qs)
    in
    exit 0

let init_load_paths (coqenv:Boot.Env.maybe_env) opts =
  let open Coqargs in
  let (boot_ml_path, boot_vo_path), native_ml_path =
    match coqenv with
    | Boot ->
      ([],[]),opts.config.native_include_dirs
    | Env coqenv ->
      let nI = match opts.config.native_include_dirs with
        | [] -> Nativelib.default_include_dirs coqenv
        | _ :: _ as nI -> nI
      in
      Coqloadpath.init_load_path ~coqenv, nI
  in
  let () = Nativelib.include_dirs := native_ml_path in
  let ml_path = opts.pre.ml_includes @ boot_ml_path in
  List.iter Mltop.add_ml_dir (List.rev ml_path);
  List.iter Loadpath.add_vo_path boot_vo_path;
  let env_ocamlpath =
    try [Sys.getenv "OCAMLPATH"]
    with Not_found -> []
  in
  let env_ocamlpath = ml_path @ env_ocamlpath in
  let ocamlpathsep = if Sys.unix then ":" else ";" in
  let env_ocamlpath = String.concat ocamlpathsep env_ocamlpath in
  Findlib.init ~env_ocamlpath ()

let init_profile ~file =
  let ch = open_out file in
  let fname = Filename.basename file in
  NewProfile.init { output = Format.formatter_of_out_channel ch; fname; };
  at_exit (fun () ->
      NewProfile.finish ();
      close_out ch)

let init_runtime ~usage opts =
  let open Coqargs in
  Vernacextend.static_linking_done ();
  Option.iter (fun file -> init_profile ~file) opts.config.profile;
  Lib.init ();
  if opts.post.memory_stat then at_exit print_memory_stat;

  (* excluded directories *)
  List.iter System.exclude_directory opts.config.exclude_dirs;

  let coqenv = boot_env usage opts in

  (* Paths for loading stuff *)
  init_load_paths coqenv opts;

  ()

let init_document opts =
  let open Coqargs in

  (* this isn't in init_load_paths because processes (typically
     vscoqtop) are allowed to have states with differing vo paths (but
     not with differing -boot or ml paths) *)
  List.iter (fun x -> Loadpath.add_vo_path @@ to_vo_path x) opts.pre.vo_includes;

  (* Kernel configuration *)
  Global.set_impredicative_set opts.config.logic.impredicative_set;
  Global.set_indices_matter opts.config.logic.indices_matter;
  Global.set_check_universes (not opts.config.logic.type_in_type);
  Global.set_VM opts.config.enable_VM;
  Global.set_native_compiler (match opts.config.native_compiler with NativeOff -> false | NativeOn _ -> true);
  Global.set_rewrite_rules_allowed opts.config.logic.rewrite_rules;
  Opaques.skip_qed_typecheck := opts.config.skip_qed_typecheck;

  (* XXX these flags should probably be in the summary *)
  (* Native output dir *)
  Nativelib.output_dir := opts.config.native_output_dir;

  (* Default output dir *)
  System.output_directory := opts.config.output_directory;

  (* Test mode *)
  Flags.test_mode := opts.config.test_mode;

  (* beautify *)
  if opts.config.beautify then begin
    Flags.beautify := true;
    CLexer.record_comments := true;
  end;

  if opts.config.quiet then begin
    Flags.quiet := true;
  end;

  ()

let warn_require_not_found =
  CWarnings.create ~name:"compatibility-module-not-found"
    ~category:CWarnings.CoreCategories.filesystem
    Pp.(fun (prefix, lib) ->
        strbrk "Did not find compatibility module " ++ Libnames.pr_qualid lib ++
        pr_opt (fun prefix -> str "with prefix " ++ Libnames.pr_qualid prefix)
          prefix ++ str ".")

let require_file ~intern ~prefix ~lib ~export ~allow_failure =
  let mp = Libnames.qualid_of_string lib in
  let mfrom = Option.map Libnames.qualid_of_string prefix in
  let exp = Option.map (function
      | Coqargs.Import -> Vernacexpr.Import, None
      | Coqargs.Export -> Vernacexpr.Export, None)
      export
  in
  try
    Flags.silently (Vernacentries.vernac_require ~intern mfrom exp) [mp,Vernacexpr.ImportAll]
  with (Synterp.UnmappedLibrary _ | Synterp.NotFoundLibrary _) when allow_failure ->
    warn_require_not_found (mfrom, mp)

let warn_no_native_compiler =
  CWarnings.create_in Nativeconv.w_native_disabled
    Pp.(fun s -> strbrk "Native compiler is disabled," ++
                   strbrk " -native-compiler " ++ strbrk s ++
                   strbrk " option ignored.")

let warn_deprecated_native_compiler =
  CWarnings.create ~name:"deprecated-native-compiler-option" ~category:Deprecation.Version.v8_14
         (fun () ->
          Pp.strbrk "The native-compiler option is deprecated. To compile native \
          files ahead of time, use the coqnative binary instead.")

let interp_set_option (type a) opt (v:string) (k:a Goptions.option_kind) : a =
  let opt = String.concat " " opt in
  match k with
  | BoolKind -> (Coqargs.get_bool ~opt v)
  | IntKind -> (Coqargs.get_int_opt ~opt v)
  | StringKind -> v
  | StringOptKind -> Some v

let interp_set_option opt =
  { Goptions.check_and_cast = (fun v k -> interp_set_option opt v k ) }

let set_option (opt,v) =
  let open Goptions in
  match (v:Coqargs.option_command) with
  | OptionUnset -> unset_option_value_gen ~locality:OptLocal opt
  | OptionSet None -> set_bool_option_value_gen ~locality:OptLocal opt true
  | OptionSet (Some v) -> set_option_value ~locality:OptLocal (interp_set_option opt) opt v

let handle_injection ~intern = let open Coqargs in function
  | RequireInjection {lib;prefix;export;allow_failure} ->
    require_file ~intern ~lib ~prefix ~export ~allow_failure
  | OptionInjection o -> set_option o
  | WarnNoNative s -> warn_no_native_compiler s
  | WarnNativeDeprecated -> warn_deprecated_native_compiler ()

let start_library ~intern ~top injections =
  Flags.verbosely Declaremods.start_library top;
  CWarnings.override_unknown_warning[@ocaml.warning "-3"] := true;
  List.iter (handle_injection ~intern) injections;
  CWarnings.override_unknown_warning[@ocaml.warning "-3"] := false
