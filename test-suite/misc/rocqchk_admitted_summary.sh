#!/usr/bin/env bash
# rocqchk -o cannot see an unsafe flag inside a sealed module of a library it
# admits, because an admitted library is never walked. The summary must then
# name that library as admitted, so that its unsafe-flag sections reading
# <none> are not taken for "nothing unsafe here". When the same library is
# checked instead, the hidden fixpoint is listed and the library is not named
# as admitted.
set -eu
export PATH="$BIN:$PATH"

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

cat > "$d/Lib.v" <<'EOF'
Module Type T. Parameter tgt : 1 = 2. End T.
Module Seal : T.
  #[bypass_check(guard)] Fixpoint loop (n : nat) : False := loop n.
  Lemma tgt : 1 = 2. Proof. exfalso; exact (loop 0). Qed.
End Seal.
EOF
echo 'Require Lib. Definition use : 1 = 2 := Lib.Seal.tgt.' > "$d/Use.v"
rocq c -native-compiler no -R "$d" "" "$d/Lib.v"
rocq c -native-compiler no -R "$d" "" "$d/Use.v"

# Print one summary section: its "* <title>" line and the lines under it, up to
# the next "* " bullet. awk's index() takes the title literally, slashes and
# parentheses included.
section() { awk -v h="* $1" 'index($0, h) == 1 { p = 1; print; next } p && /^\* / { exit } p { print }' "$2"; }

rocqchk -o -silent -R "$d" "" -admit Lib Use > "$d/admitted.log" 2>&1
section 'Constants/Inductives relying on unsafe (co)fixpoints' "$d/admitted.log" \
  | grep -q 'unsafe (co)fixpoints: <none>'
section 'Libraries admitted without checking' "$d/admitted.log" | grep -qx '    Lib'

rocqchk -o -silent -R "$d" "" Use > "$d/checked.log" 2>&1
section 'Constants/Inductives relying on unsafe (co)fixpoints' "$d/checked.log" \
  | grep -qx '    Lib.Seal.loop'
if grep -q 'Libraries admitted without checking' "$d/checked.log"; then
  echo "no library is admitted, yet the summary names some"; exit 1
fi

# A global -indices-matter must not clear what is stored with an admitted
# library: -norec admits Corelib.Init.Logic without checking it again, so eq,
# which relies on indices not mattering there, must still be listed.
rocqchk -o -silent -indices-matter -norec Corelib.Init.Prelude > "$d/indices.log" 2>&1
section 'Inductives relying on indices not mattering' "$d/indices.log" \
  | grep -qx '    Corelib.Init.Logic.eq'
