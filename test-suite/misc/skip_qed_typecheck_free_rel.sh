#!/usr/bin/env bash
set -euo pipefail

export PATH="$BIN:$PATH"
workdir=$(mktemp -d)
trap 'rm -rf "$workdir"' EXIT

cat > "$workdir/free_rel.v" <<'EOF'
Require Import Ltac2.Ltac2.
Set Default Proof Mode "Classic".
Ltac2 free_rel () :=
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Rel 1)).
Lemma free_rel_is_rejected : False.
Proof.
ltac2:(free_rel ()).
Qed.
EOF

for option in "" "-skip-qed-typecheck"; do
  if rocq c -q $option "$workdir/free_rel.v" > /dev/null 2>&1; then
    echo "free relative proof unexpectedly compiled: ${option:-without option}" >&2
    exit 1
  fi
done
