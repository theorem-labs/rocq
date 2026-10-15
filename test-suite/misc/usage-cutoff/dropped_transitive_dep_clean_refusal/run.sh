#!/usr/bin/env bash
# binary-equivalence-taiga#841 D6, test "dropped_transitive_dep_clean_refusal"
# (new, added for Review841's G8). Depends on: D1 (comp_transitive_deps /
# the full transitive-closure field) -- see "Precondition gate" below.
#
# Rewritten for Review841 round 2 (issuecomment-6188182538, findings R2 and
# R5). R2: the PREVIOUS version of this test's precondition gate
# (`grep -rq 'comp_transitive_deps'`) was vacuous -- that bare identifier
# already appears in forward-looking COMMENTS at kernel/safe_typing.ml:1800,
# kernel/safe_typing.mli:22 and vernac/library.ml:639, so the gate never
# fired, and the test then passed on the ORDINARY A-digest-mismatch refusal
# (the previous fixture used `Require Export X.`, which the gate's own
# header already said doesn't exercise G8's own code path at all).
#
# R5: the reachable e6 shape needs a non-Export `Require X.` in A, placed
# AFTER another declaration (verified directly, see below -- placing the
# Require BEFORE the declaration makes A's own exported-objects digest
# differ for an unrelated reason even with the REQUIRE leaf correctly
# Anticipate-dropped, which is a harness artifact of this specific ordering,
# not the property G8 is about; placed after, the digest genuinely matches,
# reproducing the actual gap). With that ordering fixed, verified directly
# against 619ecf0c7a (see README.md's row for this test for the full run
# output):
#   (a) C.v, which forces B's `b := X.f` to be REDUCED (`Eval compute in
#       b.` -- `Check`/`Print` do NOT force it, since neither needs the
#       kernel to dereference the stored Constr's reference to X.f):
#       raw kernel `Anomaly "Constant X.f does not appear in the
#       environment."`, exit 129.
#   (b) C_unused.v, which requires B but never forces `b` at all: SILENT
#       ACCEPT, exit 0 -- the dangling reference is never detected.
#   (c) `rocqchk -norec A -norec B` on the exact same on-disk tree ALSO
#       anomalies (exit 129), because `checker/safe_checking.ml`'s
#       `check_module B` runs before `import_strict` -- this still fails
#       closed and is stock (pre-fork) behaviour, not evidence G8's own
#       code path fired either.
#
# Root cause (confirmed by reading `vernac/library.ml`'s `digest_of_dep`):
# G8's fix (a plain, catchable `user_err "Reference to unknown module"`
# instead of an anomaly) lives in the `None` branch reached when a
# RECORDED dependency is absent from the live closure -- i.e. it needs
# B's own `comp_deps`/`md_deps` to actually LIST X as a dependency. On
# today's root-only `comp_deps` (D1 absent), B's own direct `Require` list
# is only `[A]`; X is never recorded by B at all (it was only ever a
# transitive dependency, pulled in through A, with `req_root = false`,
# filtered out by `export`'s `filter_dep`). So the lookup that would hit
# G8's fixed branch is never reached -- the Anomaly instead comes from a
# DIFFERENT code path entirely (the kernel's own global-environment lookup
# of the Constr term's reference to `X.f`, deep inside `Eval compute`'s
# reduction, nowhere near `digest_of_dep`). Fixing this needs D1's full
# transitive closure, so that B's OWN recorded dependency set includes X
# and G8's `user_err` branch is what fires instead of a raw kernel lookup
# failure (case a), and so that the loader has anything to check AT ALL
# for the no-usage case (case b) -- today nothing re-examines X on B's
# behalf since B never recorded it, so nothing can ever refuse case (b)
# before D1 lands, clean error message or not.
#
# Precondition gate, not a guess at behavior: grep for a real OCaml FIELD
# DEFINITION pattern (`comp_transitive_deps :`), which only an actual
# `library_info`/`compiled_library` widening would ever write -- no
# existing comment in this tree phrases it that way (confirmed: the three
# existing comment references all use `[comp_transitive_deps]`, Coqdoc
# bracket syntax, never a bare `comp_transitive_deps :`). This is the
# same bug class R2 found in the PREVIOUS version of this gate, and the
# same fix style already used for `dvo_iface_pass_through_to_subset`'s own
# `Dvo_iface of` gate.
. ../lib.sh

if ! grep -rq 'comp_transitive_deps :' "$UC_ROOT/kernel" "$UC_ROOT/checker" "$UC_ROOT/vernac" --include='*.ml' --include='*.mli' 2>/dev/null; then
  D=$(pwd)
  WORK="$D/work"
  rm -rf "$WORK"
  mkdir -p "$WORK"
  cp "$D"/X.v "$D"/B.v "$D"/C.v "$D"/C_unused.v "$WORK"/
  cp "$D/A_before.v" "$WORK/A.v"

  build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

  build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
  build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE, requires X): $(cat "$WORK/setup.log")"
  build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, uses X.f): $(cat "$WORK/setup.log")"

  # AFTER: A drops its plain (non-Export) Require of X entirely. B.vo (and
  # its baked-in absolute reference to X.f) is left stale on disk.
  cp "$D/A_after.v" "$WORK/A.v"
  build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, drops Require of X) failed unexpectedly: $(cat "$WORK/rebuild.log")"

  # Case (a): force b := X.f to actually be reduced.
  a_out=$(build C.v 2>&1)
  a_rc=$?
  echo "$a_out" | grep -qi 'Anomaly' \
    || uc_fail "D1 has not landed, and this test expected the CURRENT (buggy) behavior for case (a) -- forcing b (Eval compute in b) was expected to crash with an Anomaly, but got (exit $a_rc): $a_out. Either the bug is already fixed (re-check the precondition gate) or this fixture no longer reproduces e6."

  # Case (b): require B but never force b at all.
  b_out=$(build C_unused.v 2>&1)
  b_rc=$?
  if [ "$b_rc" -ne 0 ]; then
    uc_fail "D1 has not landed, and this test expected the CURRENT (buggy) behavior for case (b) -- requiring B without using b was expected to be a SILENT ACCEPT (exit 0), but got (exit $b_rc): $b_out. Either the bug is already fixed in a way this fixture doesn't anticipate, or something else changed."
  fi

  uc_fail "EXPECTED TO FAIL pending D1 (comp_transitive_deps / the full transitive-closure field, binary-equivalence-taiga#841 Review841 R5): reproduced e6 exactly as observed at 619ecf0c7a -- case (a) forcing b crashes with a raw kernel Anomaly ('$(echo "$a_out" | grep -im1 Anomaly)') instead of G8's clean user_err, and case (b) (Require B without using b) is a SILENT ACCEPT (exit 0) of a dangling reference to a dropped transitive dependency, never even reaching a check. G8's own fix (vernac/library.ml's digest_of_dep user_err branch) needs B's OWN recorded dependency set to include X, which needs D1's full transitive closure; on today's root-only comp_deps, B never recorded X at all (it was only ever pulled in transitively through A), so neither case can be caught by ANY existing check. See this file's header for the full analysis."
fi

# D1 has landed: the scenario above must now be a clean refusal in BOTH
# sub-cases -- no Anomaly, no silent accept.
D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/X.v "$D"/B.v "$D"/C.v "$D"/C_unused.v "$WORK"/
cp "$D/A_before.v" "$WORK/A.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build X.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build X.v: $(cat "$WORK/setup.log")"
build A.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build A.v (BEFORE, requires X): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (BEFORE, uses X.f): $(cat "$WORK/setup.log")"

cp "$D/A_after.v" "$WORK/A.v"
build A.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD A (AFTER, drops Require of X) failed unexpectedly: $(cat "$WORK/rebuild.log")"

a_out=$(build C.v 2>&1)
a_rc=$?
if [ "$a_rc" -eq 0 ]; then
  echo "$a_out" >&2
  uc_fail "coqc C.v succeeded forcing b (Eval compute) after A dropped its transitive dependency on X -- the dropped dependency was not detected at all."
fi
echo "$a_out" | grep -qi 'anomaly' \
  && uc_fail "coqc C.v refused case (a), but with a raw Anomaly rather than a clean user-facing error -- G8's fix did not take effect. Got: $a_out"
echo "$a_out" | grep -qi -E 'inconsistent assumptions|unknown module|reference to unknown' \
  || uc_fail "coqc C.v refused case (a) (exit $a_rc) but not with a recognizable clean refusal message -- got: $a_out"

b_out=$(build C_unused.v 2>&1)
b_rc=$?
if [ "$b_rc" -eq 0 ]; then
  echo "$b_out" >&2
  uc_fail "coqc C_unused.v succeeded requiring B (without ever using b) after A dropped its transitive dependency on X -- case (b)'s silent accept is still present even though D1 landed."
fi
echo "$b_out" | grep -qi -E 'inconsistent assumptions|unknown module|reference to unknown' \
  || uc_fail "coqc C_unused.v refused case (b) (exit $b_rc) but not with a recognizable clean refusal message -- got: $b_out"

uc_ok "D1 has landed: both e6 sub-cases now produce a clean refusal -- case (a): $(echo "$a_out" | grep -im1 -E 'inconsistent assumptions|unknown module|reference to unknown'); case (b): $(echo "$b_out" | grep -im1 -E 'inconsistent assumptions|unknown module|reference to unknown')"
