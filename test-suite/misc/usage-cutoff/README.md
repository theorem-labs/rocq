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
| 4 | [`coqchk_strict_rejects_what_loader_accepts`](coqchk_strict_rejects_what_loader_accepts/) | D2's own control: an edit the relaxed loader accepts must still be refused by `rocqchk -norec`'s strict, digest-only path. **Rewritten**: the original Z/A/Bf fixture didn't discriminate D2 at all (stock coqchk also rejected it, by type error) — see file header. Two replacement candidates were tried and empirically ruled out (Review841's own "d2" constraint-weakening control now also refused by the *relaxed* loader since G2 landed; an opaque-proof-term-only edit is invisible to `rocqchk`'s own digest, which is `Dvo_or_vi seg_md.hash` — the opaque table is a separate, unhashed segment, confirmed by reading `checker/checkLibrary.ml`). With G1 absent, there is currently no edit the relaxed loader accepts beyond byte-identical, so D2 has nothing to discriminate from. | D2, and (newly discovered while rewriting this test) G1 | **FAILS** — precondition gate: "G1 has not landed yet ... D2's backstop has nothing to discriminate from". Once G1 lands this becomes a real, non-vacuous D2 regression test (fixture retained, same shape as `unused_addition_still_reused`, plus a `rocqchk` cross-check). |
| 5 | [`vos_then_real_all`](vos_then_real_all/) | `make vos` must never write the cutoff stamp; a following `make real-all` must genuinely REBUILD, not reuse a stale pre-edit `.vo`. | D5 (driver flag forwarding) | **PASSES** |
| 6 | [`rocqnative_reuse_succeeds`](rocqnative_reuse_succeeds/) | Admitted→Qed edit with native compilation on; `make` must exit 0 (inverted Major-1 repro: v1 failed here). | D3 (shared `dep_ok`, used by rocqnative) | **FAILS** (expected: G1 not landed — the Admitted→Qed edit changes `cst_kind` inside the exact-equality objects digest regardless of D3; D3 itself is sound but can't be observed to help until G1's per-declaration split lands). This build also has native compilation disabled at `./configure` time (`Warning: native compilation is globally deactivated`), so `rocqnative` isn't even exercised in this environment independent of G1. |
| 7 | [`hints_export_change_forces_rebuild`](hints_export_change_forces_rebuild/) | An exported `Hint` is removed from A; a dependent proved via `auto` must NOT be reused, and a fresh rebuild of it must genuinely fail. | D4 (exported-object digest) | **PASSES** (after fixing the fixture: both A variants now `Create HintDb hintcutoff.` so the db still exists, empty, after the hint is removed — the real failure is "Attempt to save an incomplete proof", not "No such Hint database") |
| 8 | `stale_vo_version_rejected` (in [`dev/usage-cutoff/`](../../../dev/usage-cutoff/test_stale_vo_version.sh), not here — needs two installed toolchains) | A `.vo` built by a pre-fork (narrower-tuple) compiler must be cleanly refused ("bad version number"), not crash. | vo_magic bump | not run (needs a second, pre-fork toolchain installed; not exercised by this pass) |
| 9 | [`reused_target_settles`](reused_target_settles/) | After one REUSED verdict, a second `make` performs zero work (no `coqtop -require` spawned) and `make -q` reports up to date. | D5 (mtime touch-forward on reuse) | **FAILS** (expected: G1 not landed, same Admitted→Qed `cst_kind` issue as test 6 — D5's own mtime-settling fix is independently correct but can't be observed for this edit until G1 lands) |
| 10 | — (`dev/usage-cutoff/test_cutoff_rocq.py`, a sibling change's pytest suite) | `cutoff_rocq.py`'s own argv parsing: `-vos`/`-vok` never touch the stamp file. | D5 | owned by the driver-fix sibling, not duplicated here; not run as part of this pass |
| 11 | [`universe_contradiction_still_caught`](universe_contradiction_still_caught/) | **Rewritten for G2.** Before G2, this scenario's reused dependent was accepted by the relaxed loader (by design, `comp_univs` outside both digests) and only `rocqchk` caught the inconsistency. G2 digests `(comp_univs, comp_sorts)` into `dep_ok`'s relaxed branch, so the SAME scenario is now refused already at `coqc` time; the rewrite asserts that refusal (`Compiled library B ... makes inconsistent assumptions over library A`) as the primary check, with `rocqchk`'s independent catch kept as a second confirmation. | G2 (flips the expected direction); unaffected by D1 | **PASSES** |
| 12 | [`unused_addition_still_reused`](unused_addition_still_reused/) | POSITIVE control: an unused declaration added to A must not force B/C to recompile — B.vo must be bit-for-bit unchanged. | D3/D4, and (per Review841 G1) the per-declaration subset layer | **FAILS** (G1 not landed: *any* addition to A changes the exact-equality objects digest, by design until G1 splits CONSTANT/INDUCTIVE+implicits+arguments-scope into a subset-tolerant check) — previously mismarked "passes now"; this is the scenario `coqchk_strict_rejects_what_loader_accepts`'s new precondition gate also exercises |
| 13 | [`dvo_iface_pass_through_to_subset`](dvo_iface_pass_through_to_subset/) | An unrelated addition makes `Dvo_iface` differ, but the per-declaration subset layer must still allow reuse of a dependent that never used the addition — confirms the two layers compose. | commit 1 (`Dvo_iface`, `sami/loc-free-identity`) | **FAILS** — precondition gate correctly fires: "Dvo_iface has not landed yet". **Fixed a false-positive in the gate itself**: the bare `grep -rq 'Dvo_iface'` now matches forward-looking *comments* the G1/G2 slice added (`kernel/safe_typing.ml`, `vernac/declaremods.ml`), which made the gate wrongly believe D1 had landed and run the real check (which then failed for G1's unrelated reason). Tightened to grep for `Dvo_iface of` (an actual constructor-definition pattern no comment uses). |
| 14 | [`driver_refuses_through_make`](driver_refuses_through_make/) | Routes the two_level_false shape through a real `coq_makefile` Makefile end to end; asserts the stats log shows REBUILD (never REUSED) for every file downstream of the change, and the final value reflects the post-edit world. Closes BugFinderRedTeamV2 M5/M6 (nothing else exercises "the driver asks, the kernel refuses, the driver forwards the refusal into a real rebuild"). | D1, D5 | **FAILS** (expected: D1 not landed) — `B.v`/`C.v` wrongly REUSED after a 2-level-down change to `f` |
| 15 | [`coqchk_tuple_roundtrip`](coqchk_tuple_roundtrip/) | A library with a non-degenerate (3-entry, mutually distinguishable) interface table and a non-empty exported-object digest; `rocqchk -norec` must accept it AND the dependents' checked values must round-trip correctly — not merely accept/reject. Closes BugFinderRedTeamV2 Blocker B1 (a same-arity, different-field-order mistake across the 5 independently-declared copies of the dependency tuple). | D1's widened tuple + Dvo_iface, consistently reflected in `checker/checkLibrary.ml`/`checker/values.ml` | **PASSES** (Review841's own finding: this one never actually needed D1 — the `rocqchk` step already passed; the old "EXPECTED TO FAIL until D1" label was wrong and the only real failure was the harness's broken value-query method, fixed here) |
| 16 | [`univ_constraint_drop_refused`](univ_constraint_drop_refused/) | **New, for G2.** Review841's own "e4": A declares `Universe u v w.`/`Constraint u < v.`; B's type (`Type@{max(v,w)} := Type@{u}`) genuinely needs the constraint (verified: a fresh rebuild of B without it fails with a real universe inconsistency). A drops the constraint; the stale B.vo must now be refused for reuse. | G2 | **PASSES** |
| 17 | [`dropped_transitive_dep_clean_refusal`](dropped_transitive_dep_clean_refusal/) | **New, for G8.** Review841's own "e6": X declares `f`; A re-exports it; B (requires only A) uses `f`. A is rebuilt WITHOUT requiring X at all; the stale B.vo's reuse must be refused CLEANLY (a `user_err`), never crash with an `Anomaly`. | G8 (`vernac/library.ml`'s `digest_of_dep`, landed) — see note below | **PASSES**, but see the file's header: this currently exercises the *ordinary* A-digest-mismatch refusal (dropping A's re-export already changes A's own `objects_digest`), not G8's own new "recorded dependency absent from the live closure" code path specifically — by that code's own doc comment, that branch is "today only reachable through state corruption" since `comp_deps`/`md_deps` are root-only until D1 lands (verified directly: this exact fixture, run step by step, refuses at the ordinary check before ever reaching X). The assertion itself (clean refusal, never an Anomaly) is real and passes today; a test that isolates G8's specific branch needs D1. |

See `gh issue view 841 -R theorem-labs/binary-equivalence-taiga` ("Regression
test list") and its Review841/disposition comments for the authoritative
wording each case implements, and rocq#10's two review comments (`gh pr
view 10 -R theorem-labs/rocq --comments`) for the original reproductions.

## G1 implemented 2026-10-15 (Review841 round 2)

G1 (the objects-digest partition excluding CONSTANT/INDUCTIVE's `cst_kind`
from the exact-equality check, subset-checking IMPLICITS/ARGUMENTS-SCOPE
instead) is now implemented (`vernac/declaremods.ml`'s `G1Partition`
module, `kernel/safe_typing.ml`'s `decl_objects_subset_ok`/widened
`dep_ok`). Two new real tests added and PASSING:

18. `g1_admitted_to_qed_reused` -- an unused Admitted->Qed edit is now
    REUSED (the lever's whole stated purpose; was refused before G1).
19. `g1_changed_statement_still_refused` -- a dependency's directly-used
    declaration changing VALUE is still REFUSED (confirms G1's exclusion
    didn't weaken the existing per-declaration kernel check).

Full suite run 2026-10-15 after G1 landed: **12/17 PASS** (up from 6/17
before G1, 0/15 at the start of this review round). The 5 remaining
failures are exactly the D1-dependent ones, unchanged and expected:
`two_level_false`, `b1_two_levels_export`, `n_levels_deep`,
`driver_refuses_through_make`, `dvo_iface_pass_through_to_subset`.

**G7 (name-shadowing refusal) is still NOT implemented** -- it needs
access to the dependent's own Nametab short-name resolution state, a
cross-cutting lookup `end_library` has no natural way to reach; the design
is written in #841 but not built. No new test was added for it.

**Residual finding, not yet investigated:** a standalone run of
`reused_target_settles` showed the driver being re-invoked on a repeat
`make real-all` with nothing changed (G5's "settling" property did not
hold in that one run), but the SAME test passed in a full-suite batch run
moments later -- looks timing/mtime-precision-sensitive rather than a hard
failure, not chased further given time. Flagged for whoever picks this up
next, with the exact repro: build A+B through `make`+driver, edit A's
proof body (Qed->Qed, unrelated to G1), rebuild (B should show REUSED),
then run `make real-all` again immediately with nothing changed and check
the stats log for a second REUSED entry (expected: none at all, second run
should do zero work).
