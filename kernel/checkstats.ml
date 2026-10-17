(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Mode flags and CPU accounting for the checker's native-conversion lever
   (BET #867 / theorem-labs/rocq sami/coqchk-native-cache). All of it is
   inert (no env var read more than once, no behavior change, no timing
   overhead beyond four [Unix.times] calls per cast) unless the harness
   opts in by setting the relevant environment variable; a build of coqchk
   that never sets any of these behaves exactly like upstream coqchk. *)

(* VM casts are decided by native conversion instead of the bytecode VM, on
   the very same pair of terms (what a NATIVEcast proof of the same goal
   would run). This is the lever under evaluation: it is what lets
   production turn native conversion on without the agent having to submit
   different proof terms. *)
let native_as_vm = Sys.getenv_opt "ROCQCHK_NATIVE_CONV" = Some "1"

(* Decide every cast (VM or NATIVEcast) BOTH ways and abort the process if
   they disagree. Used only for the measurement runs that validate this
   branch: it is strictly more expensive than either arm alone and is never
   the production configuration. Implies [native_as_vm] (a VMcast must run
   native to have a native answer to compare). *)
let debug_dual_check = Sys.getenv_opt "ROCQCHK_NATIVE_DEBUG_DUAL" = Some "1"

let native_enabled = native_as_vm || debug_dual_check

let stats_enabled = Sys.getenv_opt "ROCQCHK_NATIVE_STATS" = Some "1"

type span = {
  name : string;
  mutable calls : int;
  mutable self : float;
  mutable child : float;
}

let all = ref []

let make name =
  let a = { name; calls = 0; self = 0.; child = 0. } in
  all := a :: !all;
  a

let time a f =
  if not stats_enabled then f ()
  else begin
    let t0 = Unix.times () in
    let finish () =
      let t1 = Unix.times () in
      a.calls <- a.calls + 1;
      a.self <- a.self +. (t1.Unix.tms_utime -. t0.Unix.tms_utime) +. (t1.Unix.tms_stime -. t0.Unix.tms_stime);
      a.child <- a.child +. (t1.Unix.tms_cutime -. t0.Unix.tms_cutime) +. (t1.Unix.tms_cstime -. t0.Unix.tms_cstime)
    in
    match f () with
    | v -> finish (); v
    | exception e -> finish (); raise e
  end

let vm_conv = make "vm_conv"
let native_codegen = make "native_codegen"
let native_cache_hit = make "native_cache_hit" (* materializing an already-compiled object *)
let native_ocamlopt = make "native_ocamlopt" (* a true cache miss: child CPU is ocamlopt itself *)
let native_load_run = make "native_load_run"
let native_compare = make "native_compare"

let dual_mismatches = ref 0

let report tag =
  if stats_enabled then begin
    List.iter
      (fun a ->
        Printf.eprintf "CHECKSTATS %s %s calls=%d self_cpu=%.6f child_cpu=%.6f\n%!" tag a.name a.calls a.self
          a.child)
      (List.rev !all);
    Printf.eprintf "CHECKSTATS %s %s\n%!" tag (Nativecache.stats_line ());
    Printf.eprintf "CHECKSTATS %s dual_mismatches=%d\n%!" tag !dual_mismatches
  end

let report_library lib = report ("lib=" ^ lib)

let () = at_exit (fun () -> report "total")
