#!/usr/bin/env bash
# binary-equivalence-taiga#841 round 8 (Lean round 7 review, "mt1"). A
# [Module Type]'s own abstract fields (`Parameter x` in
# `Module Type T. Parameter x : nat. End T.`) must NOT enter the G7
# cross-library shadow table: a module type is never directly
# dereferenceable (there is no `Import T.` for a module type), so its
# field names are never real shadow candidates. B requires BOTH P
# (the module type) and Q directly, using only Q's `unrelated` -- nothing
# about `x` at all. Q is rebuilt adding a REAL `Definition x := 1.`,
# colliding (by bare basename only) with P's abstract `T.x`, already part
# of B's own recorded closure. If Module Type fields fed the shadow
# table, this addition would be wrongly flagged as a NEW definition for
# an id B's closure already had a binding for (P's `x`) and refused --
# even though P's abstract `x` was never resolvable by anyone and this
# addition cannot possibly change what a fresh compile of B does.
. ../lib.sh

D=$(pwd)
WORK="$D/work"
rm -rf "$WORK"
mkdir -p "$WORK"
cp "$D"/P.v "$D"/B.v "$D"/C.v "$WORK"/
cp "$D/Q_before.v" "$WORK/Q.v"

build() { ( cd "$WORK" && uc_coqc -Q . "" "$1" ); }

build P.v >"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build P.v (Module Type T with Parameter x): $(cat "$WORK/setup.log")"
build Q.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build Q.v (BEFORE): $(cat "$WORK/setup.log")"
build B.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build B.v (requires P and Q): $(cat "$WORK/setup.log")"
build C.v >>"$WORK/setup.log" 2>&1 || uc_fail "SETUP: could not build C.v (BEFORE): $(cat "$WORK/setup.log")"
before_hash=$(uc_sha256 "$WORK/B.vo")

cp "$D/Q_after.v" "$WORK/Q.v"
build Q.v >"$WORK/rebuild.log" 2>&1 || uc_fail "REBUILD Q (AFTER, adds real x colliding with P's abstract T.x) failed unexpectedly: $(cat "$WORK/rebuild.log")"

c_out=$(build C.v 2>&1)
c_rc=$?
if [ "$c_rc" -ne 0 ]; then
  echo "$c_out" >&2
  uc_fail "coqc C.v was refused after Q added a real 'x' that only bare-basename-collides with P's abstract Module Type field T.x -- Module Type fields must be excluded from the G7 shadow table, since they are never directly dereferenceable: $c_out"
fi
after_hash=$(uc_sha256 "$WORK/B.vo")
uc_assert_eq "$after_hash" "$before_hash" \
  "B.vo's bytes changed after compiling C -- B was silently recompiled rather than genuinely reused."

uc_ok "Q's new 'x' correctly reused despite bare-basename overlap with P's abstract Module Type field (sha256 $after_hash)"
