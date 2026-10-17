(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** A content-addressed, cross-process compile cache for the checker's
    native-conversion code. coqchk's native conversion ({!Nativeconv}) always
    regenerates the small OCaml source for a cast's own code and its runtime
    symbol table ({!Nativecode.mk_conv_code}: cheap, and still run on every
    hit or miss); this module caches only the expensive step, handing
    [ocamlfind opt -shared] its own previous output instead of re-running it
    when the EXACT SAME source text has already been compiled under the
    EXACT SAME toolchain.

    Safety invariant: a cache entry is addressed by a SHA-256 of the
    generated source bytes together with an "epoch" fingerprint of every
    component that can change what those bytes compile to (this coqchk
    binary, the resolved [ocamlfind]/[ocamlopt], and the kernel's native
    [.cmi] directory this build compiles against -- see {!val:epoch}). Two
    different terms can therefore never share an entry: they generate
    different source text (checked empirically: {!Nativecode.make_cenv}
    resets every name/symbol counter per call, and the traversal of a term
    is deterministic, so the same two terms checked against the same
    "already linked" state always print byte-identical source). Any change
    to the compiler, the kernel, or the generated-code shape changes the
    epoch and the old entries simply stop being looked up: entries are never
    actively invalidated, so a stale directory left over from a previous
    build is inert, not a residual trust liability. *)

(** Is a cache directory configured ([ROCQCHK_NATIVE_CACHE])? When false
    every function below is a plain pass-through with no filesystem access:
    behavior is identical to a build without this module. *)
val enabled : unit -> bool

(** [epoch_tag ~include_dirs] is the fingerprint identifying "this exact
    toolchain, compiling with these include directories". Computed once
    (memoized) from the first call; every subsequent call ignores its
    argument and returns the same tag, which is safe because
    [Nativelib.include_dirs] is set once at process start, before any
    compile happens. *)
val epoch_tag : include_dirs:string list -> string

(** [cached_object ~include_dirs source] returns the path of an
    already-compiled object for exactly this generated OCaml source under
    the current epoch, if the cache holds one. *)
val cached_object : include_dirs:string list -> string -> string option

(** [fetch_to ~include_dirs source ~dest] is [cached_object] followed by
    materializing a usable copy of the cached object at [dest] (hardlink
    when possible, else a byte copy). Returns [true] on a hit. *)
val fetch_to : include_dirs:string list -> string -> dest:string -> bool

(** [with_lock ~include_dirs source f] runs [f] while holding an exclusive,
    cross-process lock scoped to this exact source's cache key (a POSIX
    [lockf] tied to an open file descriptor, so it is released automatically
    if the holder dies or is killed -- no stale-lock cleanup is needed).
    Concurrent [-j] workers compiling the same not-yet-cached source
    therefore block on each other instead of both running [ocamlopt].
    Callers MUST re-run {!cached_object} (or {!fetch_to}) after acquiring
    the lock: another worker may have published the entry while this one
    was waiting. When the cache is disabled this is just [f ()]. *)
val with_lock : include_dirs:string list -> string -> (unit -> 'a) -> 'a

(** [publish ~include_dirs source ~compiled_file] atomically makes
    [compiled_file]'s current bytes available to {!cached_object} /
    {!fetch_to} for this exact source under the current epoch (write to a
    same-directory temp file, then [rename], so a concurrent reader never
    observes a partial file). Idempotent: publishing the same source twice
    is safe, since by the safety invariant any two publishes for the same
    key were compiled from byte-identical source under the same epoch. *)
val publish : include_dirs:string list -> string -> compiled_file:string -> unit

(** One-line summary of this process's hits / misses / lock-wait time, for
    the harness's native-conversion report. *)
val stats_line : unit -> string
