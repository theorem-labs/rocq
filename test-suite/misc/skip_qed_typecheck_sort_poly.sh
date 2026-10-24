#!/usr/bin/env bash
# A sort-polymorphic Qed proof, not typed by the kernel
# (-skip-qed-typecheck). The proof of [sort_id] mentions only the bound sort
# variable [s], in a sort and in the relevance of its binders, and no bound
# universe level. So the stored proof must use the bound sort variable, as a
# checked proof does, for rocqchk to accept the library. [sort_const] also
# mentions a bound universe.
set -euo pipefail

export PATH="$BIN:$PATH"
workdir=$(mktemp -d)
trap 'rm -rf "$workdir"' EXIT

cat > "$workdir/sort_poly.v" <<'EOF'
Set Universe Polymorphism.

Lemma sort_id@{s ; |} (A : Type@{s ; Set}) (x : A) : A.
Proof. exact x. Qed.

Lemma sort_const@{s ; u |} (A B : Type@{s ; u}) (x : A) (y : B) : A.
Proof. exact x. Qed.

Check sort_id@{Prop ; }.
EOF

for option in "" "-skip-qed-typecheck"; do
  rm -f "$workdir"/sort_poly.{vo,vos,vok,glob}
  rocq c -q $option -R "$workdir" Top "$workdir/sort_poly.v" ||
    { echo "rocq c failed ${option:-without option}" >&2; exit 1; }
  rocqchk -silent -R "$workdir" Top -norec Top.sort_poly ||
    { echo "rocqchk rejected the library built ${option:-without option}" >&2; exit 1; }
done
