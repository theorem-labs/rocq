#!/usr/bin/env bash
# A universe-polymorphic Qed proof in a section, not typed by the kernel
# (-skip-qed-typecheck): the stored proof uses the constant's bound universes,
# and the section's own universe and variables are discharged as for a checked
# proof, so rocqchk accepts the library.
set -euo pipefail

export PATH="$BIN:$PATH"
workdir=$(mktemp -d)
trap 'rm -rf "$workdir"' EXIT

cat > "$workdir/poly_section.v" <<'EOF'
Set Universe Polymorphism.

Section Paradox.
Universe u.
Variable T : Type@{u}.
Variable M : Prop -> Prop.
Hypothesis incr : forall A B : Prop, (A -> B) -> M A -> M B.

(* [strength] has a universe of its own, for [A]. *)
Lemma strength : forall A (P : A -> Prop), M (forall x : A, P x) -> forall x : A, M (P x).
Proof.
  intros A P h x.
  eapply incr in h; eauto.
Qed.

(* [id_sec] uses only the section's universe. *)
Lemma id_sec (t : T) : T.
Proof. exact t. Qed.
End Paradox.
EOF

for option in "" "-skip-qed-typecheck"; do
  rm -f "$workdir"/poly_section.{vo,vos,vok,glob}
  rocq c -q $option -R "$workdir" Top "$workdir/poly_section.v" ||
    { echo "rocq c failed ${option:-without option}" >&2; exit 1; }
  rocqchk -silent -R "$workdir" Top -norec Top.poly_section ||
    { echo "rocqchk rejected the library built ${option:-without option}" >&2; exit 1; }
done
