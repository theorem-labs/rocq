(** Regression test for the perf-nametab-cache masking-absolute-name bug
    (ROCQ-INTERNALS.md section 18): [nametab_mask_decl] declares a global
    [S]; [nametab_mask_section] opens and closes a [Section] that binds a
    LOCAL [S] (a section [Variable] never visible outside its own file).
    Requiring both on one [Require Import] line replays each library's own
    persisted name-table fragment in turn, then imports the first library's
    exported names -- exactly the sequence that, before the fix, let the
    section-local [S]'s stale push (never rolled back out of the exported
    fragment when its section closed) survive into the persisted .vo and
    mask the real, globally-visible [S] when it was imported here. Before
    the fix this file fails to compile with "Trying to mask the absolute
    name \"S\"!"; after the fix it compiles cleanly. *)
Require Import TestSuite.nametab_mask_decl TestSuite.nametab_mask_section.
