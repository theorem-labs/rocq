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
Module Type Empty. End Empty.
Module F (X : Empty).
  Lemma p : True. Proof. exact I. Qed.
End F.
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
Module E. End E.
Module X := A.F E.
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
r_foreign $P.B.X.p -
EOF
hashes() {
  for lib in "$@"; do
    printf '%s.%s %s\n' "$P" "$lib" "$(sha256sum "$d/$lib.vo" | cut -d' ' -f1)"
  done
}
hashes A B C > "$d/digests"
hashes A B > "$d/admit"
hashes B > "$d/foreign-admit"
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
if grep -q '^read ahead ' "$d/on4.err"; then
  echo 'read-ahead counter printed without its test variable' >&2; exit 1
fi

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
python3 - "$d/nodes" "$d/header" "$d/truncated" "$d/badpayload" "$d" <<'PY'
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

# Encode a small schema independently of OCaml's runtime object allocator.
from pathlib import Path
directory = Path(sys.argv[5])
def block(tag, *fields):
    return (tag, fields)
def linked(items):
    value = 0
    for item in reversed(items):
        value = block(0, item, value)
    return value
def encode(value):
    # Track object identity in Marshal's preorder allocation order. Keep the
    # traversal iterative so the shared-prefix depth case needs no Python
    # recursion-limit change, and never expand a shared subtree in the wire.
    body = bytearray()
    seen = {}
    pending = [value]
    objects = size32 = size64 = 0
    while pending:
        current = pending.pop()
        if isinstance(current, int):
            body.extend(bytes([0x40 + current]) if 0 <= current < 64
                        else b'\x02' + struct.pack('>i', current))
            continue
        identity = id(current)
        if identity in seen:
            distance = objects - seen[identity]
            if distance < 256:
                body.extend(b'\x04' + struct.pack('>B', distance))
            elif distance < 65536:
                body.extend(b'\x05' + struct.pack('>H', distance))
            else:
                body.extend(b'\x06' + struct.pack('>I', distance))
            continue
        if isinstance(current, str):
            seen[identity] = objects
            objects += 1
            raw = current.encode()
            body.extend(bytes([0x20 + len(raw)]) if len(raw) < 32
                        else b'\x0a' + struct.pack('>I', len(raw)))
            body.extend(raw)
            size32 += 1 + (len(raw) + 4) // 4
            size64 += 1 + (len(raw) + 8) // 8
            continue
        tag, fields = current
        if fields:
            seen[identity] = objects
            objects += 1
            size32 += 1 + len(fields)
            size64 += 1 + len(fields)
        body.extend(bytes([0x80 + (len(fields) << 4) + tag]) if tag < 16 and len(fields) < 8
                    else b'\x08' + struct.pack('>I', (len(fields) << 10) | tag))
        pending.extend(reversed(fields))
    return bytes(body), objects, size32, size64
def save(name, value):
    body, objects, size32, size64 = encode(value)
    metadata = struct.pack('>IIIII', 0x8495a6be, len(body), objects, size32, size64)
    (directory / name).write_bytes(header + metadata + body)
library, sha = (directory / 'admit').read_text().splitlines()[0].split()
path = linked(list(reversed(library.split('.'))))
constant = block(0, block(0, block(0, path), 'proof', -1))
def groups(flags):
    node = block(0, 0, 0, linked(flags), 0)
    return linked([block(0, path, sha, linked([block(0, constant, node)]))])
save('typed-control', groups([]))
# This block has the native string tag but is NOT an Analyze.String.
# Generic Obj instantiation would fabricate an unsafe runtime string.
save('native-string', groups([block(252, -1)]))

# A compact DAG must retain sharing, not merely hit a budget and discard
# everything: the ordinary proof node must still be consumed. The unknown
# entries are ignored on import, but all their shared data is decoded first.
ordinary = block(0, 0, 0, 0, 0)
known_entry = block(0, constant, ordinary)
unknown = block(0, block(0, block(0, path), 'not_declared', -1))
shared_flags = linked(['shared-flag'] * 30_000)
shared_node = block(0, 0, 0, shared_flags, 0)
shared_entry = block(0, unknown, shared_node)
distinct_entries = [block(0, unknown, block(0, 0, 0, shared_flags, 0)) for _ in range(30_000)]
dag_entries = [known_entry] + distinct_entries + [shared_entry] * 30_000
save('shared-dag', linked([block(0, path, sha, linked(dag_entries))]))

# Each key adds only 512 new edges before reaching a memoized prefix. Its
# total path height must nevertheless be checked before constructing a name.
prefix = block(0, path)
depth_entries = [known_entry]
for chunk in range(3):
    for edge in range(512):
        prefix = block(2, prefix, 'x')
    name = block(0, block(0, prefix, 'probe', -1))
    depth_entries.append(block(0, name, ordinary))
save('shared-prefix', linked([block(0, path, sha, linked(depth_entries))]))
for name, body, objects, size32, size64 in [
        ('count-bomb', b'\x40', 0x40000000, 0x40000000, 0x40000000),
        ('block-bomb', b'\x08' + struct.pack('>I', (0x100000 << 10)), 1, 1, 1),
        ('string-bomb', b'\x0a' + struct.pack('>I', 0x10000000), 1, 1, 1)]:
    (directory / name).write_bytes(header + struct.pack('>IIIII', 0x8495a6be, len(body), objects, size32, size64) + body)
with (directory / 'too-large').open('wb') as output:
    output.truncate(4_294_967_297)
(directory / 'long-list').write_text(library + ' ' + sha + '\n' + 'X' * 70_000 + ' ' + sha + '\n')
PY
printf '%s.A not-a-sha256\n' "$P" > "$d/malformed"
for file in missing header truncated badpayload; do
  run "$file" 4 "${carried[@]}" -report-nodes-in "$d/$file" -report-nodes-admit "$d/admit"
  same off1 "$file"
done

# Both the allocation bomb and FIFOs are contained externally: a broken
# reader must fail this test, not hang or exhaust the test runner's memory.
contained() {
  local name=$1; shift
  (ulimit -v 2097152
   timeout 60s "$BIN"rocqchk -silent -o -j 1 -Q "$d" "$P" \
     -statement-report "$d/requests" "${carried[@]}" "$@") > "$d/$name.out" 2> "$d/$name.err"
  grep -q '^END STATEMENT REPORT$' "$d/$name.err"
  if test "${COQ_TEST_SUITE_STATEMENT_REPORT_CACHED_NODES-}" = 1; then
    grep -v '^cached nodes [0-9]*$' "$d/$name.err" > "$d/$name.stripped"
    diff -u "$d/off1.err" "$d/$name.stripped"
    diff -u "$d/off1.out" "$d/$name.out"
  else
    same off1 "$name"
  fi
}
for file in count-bomb block-bomb string-bomb native-string too-large; do
  contained "$file" -report-nodes-in "$d/$file" -report-nodes-admit "$d/admit"
done
COQ_TEST_SUITE_STATEMENT_REPORT_CACHED_NODES=1 \
  contained shared-dag -report-nodes-in "$d/shared-dag" -report-nodes-admit "$d/admit"
test "$(count shared-dag)" = 1
COQ_TEST_SUITE_STATEMENT_REPORT_CACHED_NODES=1 \
  contained shared-prefix -report-nodes-in "$d/shared-prefix" -report-nodes-admit "$d/admit"
test "$(count shared-prefix)" = 0
mkfifo "$d/fifo"
contained fifo-cache -report-nodes-in "$d/fifo" -report-nodes-admit "$d/admit"
contained fifo-list -report-nodes-in "$d/nodes" -report-nodes-admit "$d/fifo"
contained long-list -report-nodes-in "$d/nodes" -report-nodes-admit "$d/long-list"
counted long-list-count 1 "${carried[@]}" -report-nodes-in "$d/nodes" -report-nodes-admit "$d/long-list"
test "$(count long-list-count)" = 0
hashes A > "$d/typed-admit"
counted typed-control 1 "${carried[@]}" -report-nodes-in "$d/typed-control" -report-nodes-admit "$d/typed-admit"
test "$(count typed-control)" = 1
diff -u "$d/off1.err" "$d/typed-control.stripped"
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

# Of the requested nodes owned by A, proof is the only one. Harvesting with
# its body unreadable must leave no reusable node for that request.
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
  COQ_TEST_SUITE_STATEMENT_REPORT_UNREADABLE="$P.A.proof" run "warmunread$j" "$j" "${carried[@]}" \
    -report-nodes-in "$d/nodes" -report-nodes-admit "$d/admit"
  same "unreadoff$j" "warmunread$j"
  grep -q "Statement report: the opaque body of $P.A.proof could not be read" "$d/unreadon$j.err"
  grep -q "^axiom r_proof $P.A.proof $P.A:proof$" "$d/unreadon$j.err"
done
COQ_TEST_SUITE_STATEMENT_REPORT_UNREADABLE="$P.A.proof" \
  counted warmunreadcount 1 "${carried[@]}" "${cached[@]}"
test "$(count warmunreadcount)" = 0

# Replacing only the proof body does not change the declaration's load digest.
# First keep the OLD registration hash in LIST deliberately: condition (a)
# alone must prevent the CHECKED library from taking its old proof node.
cat > "$d/A.v" <<'EOF'
Axiom ax : True.
Lemma proof : True. Proof. exact ax. Qed.
Module Type Empty. End Empty.
Module F (X : Empty).
  Lemma p : True. Proof. exact ax. Qed.
End F.
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
# B is unchanged and admitted with its genuine hash, but B.X.p's opaque
# handle reads A's replacement table. B's hash cannot authenticate that body.
foreign=(-norec "$P.A" -admit "$P.B" -admit "$P.C")
for j in 1 4; do
  run "foreignoff$j" "$j" "${foreign[@]}"
  run "foreignon$j" "$j" "${foreign[@]}" -report-nodes-in "$d/nodes" -report-nodes-admit "$d/foreign-admit"
  same "foreignoff$j" "foreignon$j"
  grep -q "^axiom r_foreign $P.A.ax $P.A:ax$" "$d/foreignon$j.err"
done
printf 'r_foreign %s.B.X.p -\n' "$P" > "$d/foreign-requests"
counted foreigncount 1 "${foreign[@]}" -statement-report "$d/foreign-requests" \
  -report-nodes-in "$d/nodes" -report-nodes-admit "$d/foreign-admit"
test "$(count foreigncount)" = 0
echo OK
