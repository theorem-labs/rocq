# usage-cutoff regression tests (binary-equivalence-taiga#841, D6)

Real, assertion-bearing regression tests for the usage-cutoff fork's
relaxed `.vo` loader, closing rocq#10's Major-6 / #841 finding 6: v1's own
verification scripts (`run_controls.sh`, `run_universe.sh`,
`validate_driver.sh`) printed expected output but asserted nothing, so a
regression in any of the fixes below would not fail CI. Every case here
exits non-zero when the property it checks doesn't hold.

Registered as the `usage-cutoff` subsystem in `test-suite/Makefile`
(`misc/usage-cutoff/*/run.sh`, mirroring the `tools/`/`coq-makefile/`
pattern): `make -C test-suite usage-cutoff` runs all of them, and
`make -C test-suite all` includes them. `lib.sh` (not itself a test — no
`run.sh`, so the Makefile glob skips it) holds the shared helpers every
case sources.

Four cases (5, 6, 9, 14) drive a real `coq_makefile`-generated Makefile
through `dev/usage-cutoff/cutoff_rocq.py` (the D5 driver fixes, owned by a
sibling change in this same PR) in a hermetic `mktemp -d` scratch
directory; the rest invoke `rocqc`/`rocqchk` directly. One case from
#841's own list (#10) is a Python pytest suite over the driver's own argv
parsing, not a `test-suite/` case at all — see
`dev/usage-cutoff/test_cutoff_rocq.py`. A second case (#8) needs two
separately installed Rocq toolchains and is kept as a standalone script
in `dev/usage-cutoff/` rather than wired into this Makefile subsystem — see
that script's own header.

| # | Name | Scenario | Depends on | Status |
|---|------|----------|------------|--------|
| 1 | [`two_level_false`](two_level_false/) | X declares f; A re-exports it without declaring it itself; B (requires only A) proves `b : f = 1`. f changes, A rebuilt, B.vo stale; a fresh C exploits it for a closed proof of False. | D1 (full transitive closure) | **EXPECTED TO FAIL** until commit comp_transitive_deps/Dvo_iface lands |
| 2 | [`b1_two_levels_export`](b1_two_levels_export/) | Same shape via Z/A/Bf/Cf, in both a `Require Export` and a plain-reference (`d := z`) variant — the bug doesn't need `Require Export`. | D1 | **EXPECTED TO FAIL** until commit comp_transitive_deps/Dvo_iface lands |
| 3 | [`n_levels_deep`](n_levels_deep/) | A chain of 5 (L1..L5); the bottom changes, the top (4 levels removed) must refuse reuse. Generalizes 1/2 beyond depth 2. | D1 | **EXPECTED TO FAIL** until commit comp_transitive_deps/Dvo_iface lands |
| 4 | [`coqchk_strict_rejects_what_loader_accepts`](coqchk_strict_rejects_what_loader_accepts/) | The Blocker's own Z/A/Bf tree (stale Bf.vo, fresh A/Z); `rocqchk -norec` must independently reject it via its strict, digest-only path, regardless of D1's status. | D2 (coqchk strict path) | passes now |
| 5 | [`vos_then_real_all`](vos_then_real_all/) | `make vos` must never write the cutoff stamp; a following `make real-all` must genuinely REBUILD, not reuse a stale pre-edit `.vo`. | D5 (driver flag forwarding) | passes now |
| 6 | [`rocqnative_reuse_succeeds`](rocqnative_reuse_succeeds/) | Admitted→Qed edit with native compilation on; `make` must exit 0 (inverted Major-1 repro: v1 failed here). | D3 (shared `dep_ok`, used by rocqnative) | passes now |
| 7 | [`hints_export_change_forces_rebuild`](hints_export_change_forces_rebuild/) | An exported `Hint` is removed from A; a dependent proved via `auto` must NOT be reused, and a fresh rebuild of it must genuinely fail. | D4 (exported-object digest) | passes now |
| 8 | `stale_vo_version_rejected` (in [`dev/usage-cutoff/`](../../../dev/usage-cutoff/test_stale_vo_version.sh), not here — needs two installed toolchains) | A `.vo` built by a pre-fork (narrower-tuple) compiler must be cleanly refused ("bad version number"), not crash. | vo_magic bump | passes now (run manually with `STOCK_COQC`/`ROCQC` set) |
| 9 | [`reused_target_settles`](reused_target_settles/) | After one REUSED verdict, a second `make` performs zero work (no `coqtop -require` spawned) and `make -q` reports up to date. | D5 (mtime touch-forward on reuse) | passes now |
| 10 | — (`dev/usage-cutoff/test_cutoff_rocq.py`, a sibling change's pytest suite) | `cutoff_rocq.py`'s own argv parsing: `-vos`/`-vok` never touch the stamp file. | D5 | owned by the driver-fix sibling, not duplicated here |
| 11 | [`universe_contradiction_still_caught`](universe_contradiction_still_caught/) | An agent's opaque proof adds a universe constraint contradicting one baked into a reused dependent; the loader accepts it (by design — `comp_univs` is outside the interface digest), but `rocqchk` over the merged set must still catch the inconsistency. | unaffected by D1–D5 (carried over from v1, now with a real assertion fixing m2) | passes now |
| 12 | [`unused_addition_still_reused`](unused_addition_still_reused/) | POSITIVE control: an unused declaration added to A must not force B/C to recompile — B.vo must be bit-for-bit unchanged. | D3/D4 | passes now |
| 13 | [`dvo_iface_pass_through_to_subset`](dvo_iface_pass_through_to_subset/) | An unrelated addition makes `Dvo_iface` differ, but the per-declaration subset layer must still allow reuse of a dependent that never used the addition — confirms the two layers compose. | commit 1 (`Dvo_iface`, `sami/loc-free-identity`) | **EXPECTED TO FAIL** until commit comp_transitive_deps/Dvo_iface lands (the script gates on `Dvo_iface`'s literal absence from kernel/checker/vernac sources and fails loudly with that reason) |
| 14 | [`driver_refuses_through_make`](driver_refuses_through_make/) | Routes the two_level_false shape through a real `coq_makefile` Makefile end to end; asserts the stats log shows REBUILD (never REUSED) for every file downstream of the change, and the final value reflects the post-edit world. Closes BugFinderRedTeamV2 M5/M6 (nothing else exercises "the driver asks, the kernel refuses, the driver forwards the refusal into a real rebuild"). | D1, D5 | **EXPECTED TO FAIL** until commit comp_transitive_deps/Dvo_iface lands |
| 15 | [`coqchk_tuple_roundtrip`](coqchk_tuple_roundtrip/) | A library with a non-degenerate (3-entry, mutually distinguishable) interface table and a non-empty exported-object digest; `rocqchk -norec` must accept it AND the dependents' checked values must round-trip correctly — not merely accept/reject. Closes BugFinderRedTeamV2 Blocker B1 (a same-arity, different-field-order mistake across the 5 independently-declared copies of the dependency tuple). | D1's widened tuple + Dvo_iface, consistently reflected in `checker/checkLibrary.ml`/`checker/values.ml` | **EXPECTED TO FAIL** until commit comp_transitive_deps/Dvo_iface lands |

See `gh issue view 841 -R theorem-labs/binary-equivalence-taiga` ("Regression
test list") for the authoritative wording each case implements, and
rocq#10's two review comments (`gh pr view 10 -R theorem-labs/rocq
--comments`) for the original reproductions.
