#!/usr/bin/env bash
# Cached public opaque nodes must leave both checker output streams unchanged.
# In particular, checking a library excludes its cached nodes even when its
# statement did not change, and an admitted library needs its whole-file hash.
set -eu

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT
P=StmtCached
cat > "$d/A.v" <<'EOF'
Axiom ax : True.
Lemma proof : True. Proof. exact I. Qed.
EOF
cat > "$d/B.v" <<'EOF'
From StmtCached Require Import A.
#[bypass_check(positivity)]
Inductive bad : Set := mk : (bad -> bad) -> bad.
Lemma flagged : Set. Proof. exact bad. Qed.
Module Type S. Parameter out : True. End S.
Module M : S.
  Lemma hidden : True. Proof. exact proof. Qed.
  Definition out : True := hidden.
End M.
Lemma witness : True. Proof. exact proof. Qed.
EOF
cat > "$d/C.v" <<'EOF'
From StmtCached Require Import A B.
Lemma top : True. Proof. exact witness. Qed.
EOF
for lib in A B C; do $coqc -Q "$d" "$P" "$d/$lib.v"; done
cat > "$d/requests" <<EOF
r_proof $P.A.proof -
r_top $P.C.top -
r_flag $P.B.flagged -
r_sealed $P.B.M.out -
EOF
hashes() {
  for lib in "$@"; do
    printf '%s.%s %s\n' "$P" "$lib" "$(sha256sum "$d/$lib.vo" | cut -d' ' -f1)"
  done
}
hashes A B C > "$d/digests"
hashes A B > "$d/admit"
run() { # NAME JOBS [checker arguments]
  local name=$1 jobs=$2; shift 2
  "$BIN"rocqchk -silent -o -j "$jobs" -Q "$d" "$P" \
    -statement-report "$d/requests" "$@" > "$d/$name.out" 2> "$d/$name.err"
  grep -q '^END STATEMENT REPORT$' "$d/$name.err"
}
same() {
  diff -u "$d/$1.out" "$d/$2.out"
  diff -u "$d/$1.err" "$d/$2.err"
}
cached=(-report-nodes-in "$d/nodes" -report-nodes-admit "$d/admit")
full=(-norec "$P.A" -norec "$P.B" -norec "$P.C")
carried=(-norec "$P.C")
run full 4 "${full[@]}"
run harvest 4 "${full[@]}" -report-nodes-out "$d/nodes" -report-nodes-digests "$d/digests"
same full harvest
test -s "$d/nodes"
# Harvesting is independent of whether a statement report was requested.
"$BIN"rocqchk -silent -o -j 1 -Q "$d" "$P" "${full[@]}" > "$d/plain.out" 2> "$d/plain.err"
"$BIN"rocqchk -silent -o -j 1 -Q "$d" "$P" "${full[@]}" \
  -report-nodes-out "$d/nodes-only" -report-nodes-digests "$d/digests" \
  > "$d/saved-only.out" 2> "$d/saved-only.err"
same plain saved-only
for j in 1 4; do
  run "off$j" "$j" "${carried[@]}"
  run "on$j" "$j" "${carried[@]}" "${cached[@]}"
  same "off$j" "on$j"
  same off1 "off$j"
done
grep -q "^flag r_flag assumed-positive $P.B.bad $P.B:bad$" "$d/on4.err"
grep -q "^resolved r_sealed $P.B.M.out $P.B:M.out$" "$d/on4.err"
grep -q "^statement r_proof $P.A.proof - not-requested 0 0$" "$d/on4.err"

# The seam counts nodes the walk actually takes, not merely entries read.
counted() { # NAME JOBS [arguments]
  local name=$1 jobs=$2; shift 2
  COQ_TEST_SUITE_STATEMENT_REPORT_CACHED_NODES=1 run "$name" "$jobs" "$@"
  grep -v '^cached nodes [0-9]*$' "$d/$name.err" > "$d/$name.stripped"
}
count() { awk '$1 == "cached" && $2 == "nodes" { print $3 }' "$d/$1.err"; }
counted seamoff 1 "${carried[@]}"
counted seamon 1 "${carried[@]}" "${cached[@]}"
test "$(count seamoff)" = 0
test "$(count seamon)" -gt 0
diff -u "$d/off1.err" "$d/seamon.stripped"
diff -u "$d/off1.out" "$d/seamon.out"
counted onlyseam 1 "${carried[@]}" -report-nodes-in "$d/nodes-only" -report-nodes-admit "$d/admit"
test "$(count onlyseam)" -gt 0
diff -u "$d/off1.err" "$d/onlyseam.stripped"

# Every rejected input falls back silently, including a partial payload and
# a header written by another checker. No Marshal payload is read first.
python3 - "$d/nodes" "$d/header" "$d/truncated" "$d/badpayload" <<'PY'
import struct
import sys
raw = open(sys.argv[1], 'rb').read()
parts = raw.split(b'\n', 3)
assert len(parts) == 4
header = b'\n'.join(parts[:3]) + b'\n'
# A valid Marshal integer is not a list of library groups. Shape validation
# must fail without printing its usual diagnostic on either output stream.
bad = struct.pack('>IIIII', 0x8495a6be, 1, 0, 0, 0) + b'\x41'
open(sys.argv[4], 'wb').write(header + bad)
parts[2] = b'other checker binary'
open(sys.argv[2], 'wb').write(b'\n'.join(parts))
open(sys.argv[3], 'wb').write(raw[:-1])
PY
printf '%s.A not-a-sha256\n' "$P" > "$d/malformed"
for file in missing header truncated badpayload; do
  run "$file" 4 "${carried[@]}" -report-nodes-in "$d/$file" -report-nodes-admit "$d/admit"
  same off1 "$file"
done
run malformed 4 "${carried[@]}" -report-nodes-in "$d/nodes" -report-nodes-admit "$d/malformed"
same off1 malformed
counted malformedcount 1 "${carried[@]}" -report-nodes-in "$d/nodes" -report-nodes-admit "$d/malformed"
test "$(count malformedcount)" = 0
run missinglist 4 "${carried[@]}" -report-nodes-in "$d/nodes" -report-nodes-admit "$d/no-list"
same off1 missinglist
run writefail 4 "${full[@]}" -report-nodes-out "$d/no-directory/nodes" -report-nodes-digests "$d/digests"
same full writefail
mkdir "$d/destination"
run renamefail 4 "${full[@]}" -report-nodes-out "$d/destination" -report-nodes-digests "$d/digests"
same full renamefail
test -z "$(find "$d" -maxdepth 1 -name 'destination.*.tmp' -print)"

# A's only opaque constant is proof. Harvesting with its body unreadable
# must leave no reusable A node, even though B's nodes still can be used.
COQ_TEST_SUITE_STATEMENT_REPORT_UNREADABLE="$P.A.proof" \
  run unreadharvest 4 "${full[@]}" -report-nodes-out "$d/unreadnodes" -report-nodes-digests "$d/digests"
hashes A > "$d/only-a"
counted a_present 1 "${carried[@]}" -report-nodes-in "$d/nodes" -report-nodes-admit "$d/only-a"
counted a_absent 1 "${carried[@]}" -report-nodes-in "$d/unreadnodes" -report-nodes-admit "$d/only-a"
test "$(count a_present)" = 1
test "$(count a_absent)" = 0
for j in 1 4; do
  COQ_TEST_SUITE_STATEMENT_REPORT_UNREADABLE="$P.A.proof" run "unreadoff$j" "$j" "${carried[@]}"
  COQ_TEST_SUITE_STATEMENT_REPORT_UNREADABLE="$P.A.proof" run "unreadon$j" "$j" "${carried[@]}" \
    -report-nodes-in "$d/unreadnodes" -report-nodes-admit "$d/admit"
  same "unreadoff$j" "unreadon$j"
  grep -q "Statement report: the opaque body of $P.A.proof could not be read" "$d/unreadon$j.err"
  grep -q "^axiom r_proof $P.A.proof $P.A:proof$" "$d/unreadon$j.err"
done

# Replacing only the proof body does not change the declaration's load digest.
# First keep the OLD registration hash in LIST deliberately: condition (a)
# alone must prevent the CHECKED library from taking its old proof node.
cat > "$d/A.v" <<'EOF'
Axiom ax : True.
Lemma proof : True. Proof. exact ax. Qed.
EOF
$coqc -Q "$d" "$P" "$d/A.v"
checked=(-norec "$P.A" -norec "$P.C")
for j in 1 4; do
  run "changedoff$j" "$j" "${checked[@]}"
  run "changedon$j" "$j" "${checked[@]}" "${cached[@]}"
  same "changedoff$j" "changedon$j"
  grep -q "^axiom r_proof $P.A.ax $P.A:ax$" "$d/changedon$j.err"
done
# Now A is admitted, but its staged whole-file SHA256 differs from the
# registration's. Trusting the load digest instead would hide the axiom.
hashes A B > "$d/admit"
for j in 1 4; do
  run "staleoff$j" "$j" "${carried[@]}"
  run "staleon$j" "$j" "${carried[@]}" "${cached[@]}"
  same "staleoff$j" "staleon$j"
  grep -q "^axiom r_proof $P.A.ax $P.A:ax$" "$d/staleon$j.err"
done
hashes A > "$d/only-a"
counted stalecount 1 "${carried[@]}" -report-nodes-in "$d/nodes" -report-nodes-admit "$d/only-a"
test "$(count stalecount)" = 0
echo OK
