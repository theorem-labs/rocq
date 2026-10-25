#!/usr/bin/env bash
# This fork's table of opaque proofs holds a boolean beside each proof
# (-skip-qed-typecheck: whether coqc typed it), so an entry is
# ((proof, private universes), bool), and checker/values.ml validates that
# shape. rocqchk -j N reads the table in the process that needs it
# (CheckLibrary.read_opaque_table), and at -j 1 where it interns the
# library, and both reads come out of Obj.obj: a reader that validates this
# shape but takes an entry as the shape without the boolean still compiles,
# and hands the checker a pair where it expects a proof.
#
# Libraries compiled by the release's rocq, with monomorphic and
# universe-polymorphic opaque proofs, with and without
# -skip-qed-typecheck, so that both values of the boolean and both kinds of
# private universes are in the tables, are checked at -j 1 and -j 2:
#  (a) this build accepts them at both, as the release's own rocqchk does;
#  (b) its -o output, standard output and error together, is the release's
#      rocqchk's at -j 1, but for the version in the first line, which
#      names each build (a build in a git checkout adds its revision).
#
# ROCQ_STOCK names the release's rocq, and ROCQCHK_STOCK the release's
# rocqchk. Without them, the libraries are compiled by this build's rocq,
# whose writer of the table is the release's, and (b) compares -j 2 with
# this build's -j 1.
set -eu
: "${BIN:=$(dirname "$(command -v rocq)")/}"
export PATH="$BIN:$PATH"
unset ROCQCHK_OPAQUE_AT

ROCQ=${ROCQ_STOCK:-rocq}
REF=${ROCQCHK_STOCK:-}

d=$(mktemp -d)
mkdir "$d/lib"

fail() { >&2 echo "FAILURE: $*"; exit 1; }

# Mono's proofs are monomorphic: the table stores their private universes
# as PrivateMonomorphic. Poly's are polymorphic, and p2 adds a private
# universe: PrivatePolymorphic. MonoS and PolyS are the same files compiled
# with -skip-qed-typecheck, so that the boolean of their entries is true.
# Use reads them through definitions and an opaque proof of its own.
cat > "$d/lib/Mono.v" <<'EOF'
Inductive T : Prop := I | J.
Definition U := T.
Lemma m1 : U. Proof. exact I. Qed.
Lemma m2 : forall x : T, U. Proof. intros x; exact x. Qed.
Lemma m3 : Type. Proof. exact Prop. Qed.
Definition dm := m2 m1.
EOF
cat > "$d/lib/Poly.v" <<'EOF'
Set Universe Polymorphism.
Lemma p1@{i j | i < j} (A : Type@{i}) : Type@{j}.
Proof. exact A. Qed.
Unset Strict Universe Declaration.
Lemma p2@{i j} (A : Type@{i}) : Type@{j}.
Proof.
  pose (bar := Type : Type@{j}).
  pose (foo := Type@{i} : bar).
  exact bar.
Qed.
Definition dp@{i j | i < j} := p1@{i j}.
EOF
cp "$d/lib/Mono.v" "$d/lib/MonoS.v"
cp "$d/lib/Poly.v" "$d/lib/PolyS.v"
cat > "$d/lib/Use.v" <<'EOF'
Require Mono Poly MonoS PolyS.
Definition u1 := Mono.dm.
Definition u2 := MonoS.dm.
Lemma u3 : MonoS.U. Proof. exact (MonoS.m2 MonoS.m1). Qed.
EOF
for v in Mono Poly; do
  "$ROCQ" c -q -native-compiler no -R "$d/lib" "" "$d/lib/$v.v"
  "$ROCQ" c -q -native-compiler no -skip-qed-typecheck -R "$d/lib" "" "$d/lib/${v}S.v"
done
"$ROCQ" c -q -native-compiler no -R "$d/lib" "" "$d/lib/Use.v"

# chk BIN NAME ARGS...: rocqchk -o, standard output and error together,
# pids and the version of the banner replaced. Exit code in $R.
R=0
chk() {
  local bin=$1 name=$2; shift 2
  R=0
  "$bin" -o "$@" > "$d/$name.raw" 2>&1 || R=$?
  sed -e 's/Worker process [0-9]*/Worker process PID/' \
      -e '1s/^Welcome to Chicken .*/Welcome to Chicken VERSION/' "$d/$name.raw" > "$d/$name.out"
}

ARGS=(-R "$d/lib" "" -norec Mono -norec Poly -norec MonoS -norec PolyS -norec Use)

base=j1
if [ -n "$REF" ]; then
  base=ref
  chk "$REF" ref -j 1 "${ARGS[@]}"
  [ "$R" -eq 0 ] || { cat "$d/ref.out" >&2; fail "the release's rocqchk rejects the libraries (exit code $R)"; }
fi
# Both runs are reported before the test fails, so that a failure says
# which of the two readers of the table rejects the libraries.
rejected=
for j in 1 2; do
  chk coqchk "j$j" -j $j "${ARGS[@]}"
  if [ "$R" -ne 0 ] || ! grep -q 'Modules were successfully checked' "$d/j$j.out"; then
    tail -5 "$d/j$j.out" >&2
    >&2 echo "(a) -j $j: this rocqchk rejects the libraries (exit code $R)"
    rejected="$rejected -j $j"
  fi
done
[ -z "$rejected" ] || fail "(a) this rocqchk rejects the libraries at$rejected"
for j in 1 2; do
  [ "j$j" = "$base" ] && continue
  diff -u "$d/$base.out" "$d/j$j.out" > "$d/j$j.diff" \
    || { cat "$d/j$j.diff" >&2; fail "(b) -j $j: the output differs from ${REF:-this rocqchk at -j 1}"; }
done

rm -rf "$d"
