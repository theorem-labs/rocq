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

**Status below is from an actual run** (binary-equivalence-taiga#841
Review841's own finding: the previous version of this table was
aspirational, not run — exactly the anti-pattern D6 exists to prevent).
Toolchain: this worktree's own `dune build` output (`sami/841-usage-cutoff`
@ the head listed in each test's own `rocq c`/`rocqchk` banner), stdlib
built via `dune build -p rocq-runtime,coq-core,rocq-core` after temporarily
enabling `theories/{Corelib,Ltac2}/dune` from their `.disabled` twins (the
same step `.gitlab-ci.yml` runs), binaries installed into a scratch bin
directory under non-`.exe` names (`rocq`, `rocqchk`, `coqchk`, `coqc`,
`coqtop`, `coqnative`, `rocqnative`) since this worktree was never `dune
install`-ed into the opam switch. **Caveat for anyone hand-verifying a fix
here**, found while debugging test 16: `_build/default/topbin/rocq.exe` run
directly still dispatches worker subprocesses via `Findlib.package_directory
"rocq-runtime"` (`topbin/rocqshim.ml`), i.e. the *installed opam switch's*
`rocq-runtime` package, not this build tree — a stale installed switch would
silently exercise old code for anything that spawns a worker. None of the
15 original cases spawn one (no `-async-proofs on`), so this doesn't affect
the results below, but a future case that does would need a real `dune
install` into the switch to be trustworthy.

| # | Name | Scenario | Depends on | Status (actually run) |
|---|------|----------|------------|--------|
| 1 | [`two_level_false`](two_level_false/) | X declares f; A re-exports it without declaring it itself; B (requires only A) proves `b : f = 1`. f changes, A rebuilt, B.vo stale; a fresh C exploits it for a closed proof of False. | D1 (full transitive closure) | **FAILS** (expected: D1 not landed) — `C compiled against the stale B.vo ... closed proof of False with no axioms` |
| 2 | [`b1_two_levels_export`](b1_two_levels_export/) | Same shape via Z/A/Bf/Cf, in both a `Require Export` and a plain-reference (`d := z`) variant — the bug doesn't need `Require Export`. | D1 | **FAILS** (expected: D1 not landed) — same exploit, `[export]` variant |
| 3 | [`n_levels_deep`](n_levels_deep/) | A chain of 5 (L1..L5); the bottom changes, the top (4 levels removed) must refuse reuse. Generalizes 1/2 beyond depth 2. | D1 | **FAILS** (expected: D1 not landed) |
| 4 | [`coqchk_strict_rejects_what_loader_accepts`](coqchk_strict_rejects_what_loader_accepts/) | D2's own control: an edit the relaxed loader accepts must still be refused by `rocqchk -norec`'s strict, digest-only path. **Rewritten again (Review841 round 2, R3)**: the PREVIOUS rewrite's premise — "until G1 lands, no edit is accepted by the relaxed loader yet refused by coqchk" — was FALSE. Review841's own "e8" experiment found a real, present-day split that needs only D2, not G1: `A: Definition g := 0.` → `Definition g := 0.` + `Require Y.` (an unused import); B uses `g`. The `REQUIRE` leaf is Anticipate-dropped (iface/univs unchanged), but A's `comp_deps` array grows an entry for Y, which changes A's whole-library segment digest — the raw file digest `check_required_strict`'s `digest_match` compares — even though nothing the relaxed loader's subset check actually looks at changed. So the relaxed loader accepts the reuse via its subset fallback, while `rocqchk`'s strict path (digest equality only) correctly refuses it. No G1 dependency at all. The two earlier (G1-era) candidates are kept in the file's header for the record. | D2 (coqchk's strict, relaxed-branch-absent import path) | **PASSES**, confirmed non-vacuous — re-run at 619ecf0c7a: `coqc C.v` (reusing B.vo after A grows `Require Y.`) exits 0; `rocqchk -norec A -norec B` on the exact same tree gives `Fatal Error: User error: Inconsistent assumptions over module A .`, exit 129. |
| 5 | [`vos_then_real_all`](vos_then_real_all/) | `make vos` must never write the cutoff stamp; a following `make real-all` must genuinely REBUILD, not reuse a stale pre-edit `.vo`. | D5 (driver flag forwarding) | **PASSES** |
| 6 | [`rocqnative_reuse_succeeds`](rocqnative_reuse_succeeds/) | Admitted→Qed edit with native compilation on; `make` must exit 0 (inverted Major-1 repro: v1 failed here). | D3 (shared `dep_ok`, used by rocqnative) | **FAILS** (expected: G1 not landed — the Admitted→Qed edit changes `cst_kind` inside the exact-equality objects digest regardless of D3; D3 itself is sound but can't be observed to help until G1's per-declaration split lands). This build also has native compilation disabled at `./configure` time (`Warning: native compilation is globally deactivated`), so `rocqnative` isn't even exercised in this environment independent of G1. |
| 7 | [`hints_export_change_forces_rebuild`](hints_export_change_forces_rebuild/) | An exported `Hint` is removed from A; a dependent proved via `auto` must NOT be reused, and a fresh rebuild of it must genuinely fail. | D4 (exported-object digest) | **PASSES** (after fixing the fixture: both A variants now `Create HintDb hintcutoff.` so the db still exists, empty, after the hint is removed — the real failure is "Attempt to save an incomplete proof", not "No such Hint database") |
| 8 | `stale_vo_version_rejected` (in [`dev/usage-cutoff/`](../../../dev/usage-cutoff/test_stale_vo_version.sh), not here — needs two installed toolchains) | A `.vo` built by a pre-fork (narrower-tuple) compiler must be cleanly refused ("bad version number"), not crash. | vo_magic bump | not run (needs a second, pre-fork toolchain installed; not exercised by this pass) |
| 9 | [`reused_target_settles`](reused_target_settles/) | After one REUSED verdict, a second `make` performs zero work (no `coqtop -require` spawned) and `make -q` reports up to date. | D5 (mtime touch-forward on reuse) | **FAILS** (expected: G1 not landed, same Admitted→Qed `cst_kind` issue as test 6 — D5's own mtime-settling fix is independently correct but can't be observed for this edit until G1 lands) |
| 10 | — (`dev/usage-cutoff/test_cutoff_rocq.py`, a sibling change's pytest suite) | `cutoff_rocq.py`'s own argv parsing: `-vos`/`-vok` never touch the stamp file. | D5 | owned by the driver-fix sibling, not duplicated here; not run as part of this pass |
| 11 | [`universe_contradiction_still_caught`](universe_contradiction_still_caught/) | **Rewritten for G2.** Before G2, this scenario's reused dependent was accepted by the relaxed loader (by design, `comp_univs` outside both digests) and only `rocqchk` caught the inconsistency. G2 digests `(comp_univs, comp_sorts)` into `dep_ok`'s relaxed branch, so the SAME scenario is now refused already at `coqc` time; the rewrite asserts that refusal (`Compiled library B ... makes inconsistent assumptions over library A`) as the primary check, with `rocqchk`'s independent catch kept as a second confirmation. **Fixed (Review841 round 2, R4)**: the `rocqchk` grep (`-E 'universe\|inconsisten'`) was non-discriminating — it also matches rocqchk's own `[intern .../universe_contradiction_still_caught/work/B.vo` progress lines, since the TEST DIRECTORY NAME itself contains "universe"; the run that originally passed happened to also contain a genuine `Error: Universe inconsistency.`, so the pass was real, but the assertion would have passed on any rocqchk error at all. Tightened to grep for the literal `'Universe inconsistency'`. | G2 (flips the expected direction); unaffected by D1 | **PASSES**, now for the right reason — re-run at 619ecf0c7a: `rocqchk` output ends `Checking library: B` / `Fatal Error: Error: Universe inconsistency.`, and the tightened grep matches that exact line, not an `[intern ...]` progress line. |
| 12 | [`unused_addition_still_reused`](unused_addition_still_reused/) | POSITIVE control: an unused declaration added to A must not force B/C to recompile — B.vo must be bit-for-bit unchanged. | D3/D4, and (per Review841 G1) the per-declaration subset layer | **FAILS** (G1 not landed: *any* addition to A changes the exact-equality objects digest, by design until G1 splits CONSTANT/INDUCTIVE+implicits+arguments-scope into a subset-tolerant check) — previously mismarked "passes now" |
| 13 | [`dvo_iface_pass_through_to_subset`](dvo_iface_pass_through_to_subset/) | An unrelated addition makes `Dvo_iface` differ, but the per-declaration subset layer must still allow reuse of a dependent that never used the addition — confirms the two layers compose. | commit 1 (`Dvo_iface`, `sami/loc-free-identity`) | **FAILS** — precondition gate correctly fires: "Dvo_iface has not landed yet". **Fixed a false-positive in the gate itself**: the bare `grep -rq 'Dvo_iface'` now matches forward-looking *comments* the G1/G2 slice added (`kernel/safe_typing.ml`, `vernac/declaremods.ml`), which made the gate wrongly believe D1 had landed and run the real check (which then failed for G1's unrelated reason). Tightened to grep for `Dvo_iface of` (an actual constructor-definition pattern no comment uses). |
| 14 | [`driver_refuses_through_make`](driver_refuses_through_make/) | Routes the two_level_false shape through a real `coq_makefile` Makefile end to end; asserts the stats log shows REBUILD (never REUSED) for every file downstream of the change, and the final value reflects the post-edit world. Closes BugFinderRedTeamV2 M5/M6 (nothing else exercises "the driver asks, the kernel refuses, the driver forwards the refusal into a real rebuild"). | D1, D5 | **FAILS** (expected: D1 not landed) — `B.v`/`C.v` wrongly REUSED after a 2-level-down change to `f` |
| 15 | [`coqchk_tuple_roundtrip`](coqchk_tuple_roundtrip/) | A library with a non-degenerate (3-entry, mutually distinguishable) interface table and a non-empty exported-object digest; `rocqchk -norec` must accept it AND the dependents' checked values must round-trip correctly — not merely accept/reject. Closes BugFinderRedTeamV2 Blocker B1 (a same-arity, different-field-order mistake across the 5 independently-declared copies of the dependency tuple). | D1's widened tuple + Dvo_iface, consistently reflected in `checker/checkLibrary.ml`/`checker/values.ml` | **PASSES** (Review841's own finding: this one never actually needed D1 — the `rocqchk` step already passed; the old "EXPECTED TO FAIL until D1" label was wrong and the only real failure was the harness's broken value-query method, fixed here) |
| 16 | [`univ_constraint_drop_refused`](univ_constraint_drop_refused/) | **New, for G2.** Review841's own "e4": A declares `Universe u v w.`/`Constraint u < v.`; B's type (`Type@{max(v,w)} := Type@{u}`) genuinely needs the constraint (verified: a fresh rebuild of B without it fails with a real universe inconsistency). A drops the constraint; the stale B.vo must now be refused for reuse. | G2 | **PASSES** |
| 17 | [`dropped_transitive_dep_clean_refusal`](dropped_transitive_dep_clean_refusal/) | **New, for G8. Rewritten (Review841 round 2, R2 and R5).** R2: the previous precondition gate (`grep -rq 'comp_transitive_deps'`) was vacuous — that bare identifier already appears in forward-looking comments (`kernel/safe_typing.ml:1800`, `kernel/safe_typing.mli:22`, `vernac/library.ml:639`), so the gate never fired and the test passed on the *ordinary* A-digest-mismatch refusal (the old `Require Export X.` fixture), never exercising G8's own code path. R5: the reachable e6 shape needs a plain, non-Export `Require X.` in A placed AFTER another declaration (verified: placed before, an unrelated harness artifact makes A's digest differ anyway) and B referencing `X.f` directly (not via re-export). Gate tightened to grep for the real field-definition pattern `comp_transitive_deps :`. | G8 (`vernac/library.ml`'s `digest_of_dep`) needs D1 (comp_transitive_deps / the full transitive-closure field) to actually be reachable | **FAILS, correctly non-vacuously, pending D1** — re-run at 619ecf0c7a: case (a) (`Eval compute in b.`, forcing the dangling reference) crashes with the raw kernel `Anomaly "Constant X.f does not appear in the environment."`, exit 129; case (b) (`Require Import B.` without ever using `b`) is a SILENT ACCEPT, exit 0 — neither is G8's clean `user_err`, because B's own root-only `comp_deps` never recorded X at all (it was only ever a transitive dependency pulled in through A). `rocqchk -norec A -norec B` on the same tree also anomalies (exit 129, stock behaviour — `check_module` runs before `import_strict`). The test asserts exactly this current (undesirable) behavior and then calls `uc_fail` citing D1 as the blocker, so the suite's pass count honestly reflects "not fixed yet." |

See `gh issue view 841 -R theorem-labs/binary-equivalence-taiga` ("Regression
test list") and its Review841/disposition comments for the authoritative
wording each case implements, and rocq#10's two review comments (`gh pr
view 10 -R theorem-labs/rocq --comments`) for the original reproductions.

## Known gaps not covered here

G1 and G7 have no implementation yet (a design decision, not a bug fix, is
still pending for G7's name-shadowing question) — tests 6, 9, 12 and 13
above already document exactly how their absence manifests (test 4 no
longer depends on G1: Review841 round 2's "e8" found a real D2-only split,
see its row above), and no additional case was added for either: there is
nothing new to assert until an implementation lands to assert it against.

Test 17 (`dropped_transitive_dep_clean_refusal`, G8) has a separate,
independent gap: its fix is unreachable without D1 (comp_transitive_deps),
not G1/G7 — see its row above.
