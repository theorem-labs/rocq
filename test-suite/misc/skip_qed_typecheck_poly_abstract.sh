#!/usr/bin/env bash
# A universe-polymorphic Qed proof that uses [abstract], not typed by the
# kernel (-skip-qed-typecheck). The kernel still checks the abstracted
# subproof when the tactic runs; the main proof, which calls it at the
# constant's bound universes, must be stored over those bound universes, as
# for a checked proof, for rocqchk to accept the library.
set -euo pipefail

export PATH="$BIN:$PATH"
workdir=$(mktemp -d)
trap 'rm -rf "$workdir"' EXIT

cat > "$workdir/poly_abstract.v" <<'EOF'
Set Universe Polymorphism.

Inductive path@{i} {A : Type@{i}} (x : A) : A -> Type@{i} := refl : path x x.

Lemma transport@{i j} {A : Type@{i}} (P : A -> Type@{j}) (x y : A) :
  path x y -> P x -> P y.
Proof.
  intros e p.
  abstract (destruct e; exact p).
Qed.
EOF

for option in "" "-skip-qed-typecheck"; do
  rm -f "$workdir"/poly_abstract.{vo,vos,vok,glob}
  rocq c -q $option -R "$workdir" Top "$workdir/poly_abstract.v" ||
    { echo "rocq c failed ${option:-without option}" >&2; exit 1; }
  rocqchk -silent -R "$workdir" Top -norec Top.poly_abstract ||
    { echo "rocqchk rejected the library built ${option:-without option}" >&2; exit 1; }
done
