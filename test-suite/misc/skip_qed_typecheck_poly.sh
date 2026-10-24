#!/usr/bin/env bash
# A universe-polymorphic Qed proof that the kernel did not type
# (-skip-qed-typecheck) must still be stored over the constant's bound
# universes, as a checked proof is, so that rocqchk accepts the library.
set -euo pipefail

export PATH="$BIN:$PATH"
workdir=$(mktemp -d)
trap 'rm -rf "$workdir"' EXIT

cat > "$workdir/poly_qed.v" <<'EOF'
Set Universe Polymorphism.

Lemma id_poly (A : Type) (x : A) : A.
Proof. exact x. Qed.

Lemma id_poly_named@{u} (A : Type@{u}) (x : A) : A.
Proof. exact (id_poly A x). Qed.
EOF

for option in "" "-skip-qed-typecheck"; do
  rm -f "$workdir"/poly_qed.{vo,vos,vok,glob}
  rocq c -q $option -R "$workdir" Top "$workdir/poly_qed.v" ||
    { echo "rocq c failed ${option:-without option}" >&2; exit 1; }
  rocqchk -silent -R "$workdir" Top -norec Top.poly_qed ||
    { echo "rocqchk rejected the library built ${option:-without option}" >&2; exit 1; }
done
