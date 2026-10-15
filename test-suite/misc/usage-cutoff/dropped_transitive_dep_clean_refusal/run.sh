#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test "dropped_transitive_dep_clean_refusal"
# (new, added for Review841's G8). Depends on: D1 (comp_transitive_deps /
# the full transitive-closure field) -- see "Precondition gate" below for
# why this scenario cannot yet be constructed on today's root-only
# comp_deps, and `vernac/library.ml`'s `digest_of_dep` fix (binary-
# equivalence-taiga#841 Review841 G8, already landed): a recorded
# dependency absent from the live closure now raises a plain, catchable
# `user_err` ("Reference to unknown module ... .") instead of the old
# `anomaly "Missing library"`.
#
# Scenario (Review841's "e6"): X declares `f`. A re-exports it
# (`Require Export X.`). B requires only A (never X directly) and uses
# `f` -- B's compiled term references the absolute kernel name `X.f`,
# bound through A's re-export at B's own compile time. A is then rebuilt
# WITHOUT requiring X at all (drops the re-export entirely); B.vo is left
# stale. A fresh compile of C (`Require Import B.`) must refuse cleanly,
# not crash with an anomaly, regardless of exactly which check catches it
# first.
#
# Precondition gate, not a guess at behavior: on TODAY's root-only
# `comp_deps` (`kernel/safe_typing.mli`'s own doc comment: "D1's full
# transitive-closure field (comp_transitive_deps) is not yet present
# here"), `digest_of_dep`'s specific "recorded dependency absent from the
# live closure" branch is -- by that same code's own doc comment in
# vernac/library.ml -- "today only reachable through state corruption
# since comp_deps/md_deps are root-only". Verified directly: building
# this exact fixture and compiling C fresh refuses at the ORDINARY
# A-digest-mismatch check (`Compiled library B ... makes inconsistent
# assumptions over library A`) before ever reaching X at all, because
# dropping A's `Require Export X` necessarily changes A's own
# `objects_digest` (the ExportObject libobject) -- already a clean
# refusal, but not evidence that G8's OWN new code path (rather than the
# pre-existing, unrelated D3/D4 check) is what caught it. A meaningful
# regression test for G8 specifically needs D1's full transitive closure
# so that B's OWN recorded dependency set actually includes X (today it
# doesn't -- B's root-only comp_deps lists only A), so this test fails
# loudly here with a precondition reason rather than fabricating a pass
# that doesn't exercise the fixed code, or silently duplicating
# "two_level_false"'s existing (ordinary-digest-mismatch) coverage under a
# new name.
. ../lib.sh

if ! grep -rq 'comp_transitive_deps' "$UC_ROOT/kernel" "$UC_ROOT/checker" "$UC_ROOT/vernac" --include='*.ml' --include='*.mli' 2>/dev/null; then
  uc_fail "D1's full transitive-closure field (comp_transitive_deps) has not landed yet (commit 1, sami/861-loc-free-identity) -- vernac/library.ml's digest_of_dep comment itself says this specific branch (a recorded dependency absent from the live closure) is only reachable through state corruption without it, since comp_deps/md_deps are root-only today. This test cannot yet construct a case where B's OWN recorded dependency set includes the dropped transitive dependency X -- see this file's header for the verified alternative (the ordinary A-digest-mismatch check refuses first, which is clean but doesn't exercise G8's new code path)."
fi

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE, requires X): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, against A-with-X): $(cat "$WORK/setup.log")"

# AFTER: A drops its Require of X entirely. Rebuild A ONLY -- B.vo (and
# its baked-in absolute reference to X.f) is left stale on disk.
cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, drops Require of X) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -eq 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v succeeded reusing B.vo after A dropped its transitive dependency on X -- the dropped dependency was not detected at all."
fi
echo "$c_out" | grep -qi 'anomaly' \
  && uc_fail "coqc C.v refused the reuse, but with an Anomaly rather than a clean user-facing error -- G8's fix did not take effect. Got: $c_out"
echo "$c_out" | grep -qi -E 'inconsistent assumptions|unknown module|reference to unknown' \
  || uc_fail "coqc C.v refused the reuse (exit $c_rc) but not with a recognizable clean refusal message -- got: $c_out"

uc_ok "A dropping its transitive dependency on X produced a clean refusal, not an Anomaly: $(echo "$c_out" | grep -im1 -E 'inconsistent assumptions|unknown module|reference to unknown')"
