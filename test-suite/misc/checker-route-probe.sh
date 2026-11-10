#!/usr/bin/env bash
# What TODAY's grade of record does with four universe shapes, and what the
# comparator does with the same four.
#
# The Checker route, as bet_grader writes it (proof_staging.TRUSTED_CHECKER_SOURCE):
# a Checker.v that Requires the trusted STATEMENT library and the agent's PROOF
# library, ascribes a module holding the agent's constant to the statement's
# module type, and ends in Print Assumptions. Compiled with coqc, then coqchk.
#
# Four cases, each a self-contained tree:
#   own-image-forged   statement over Type@{u} (the task's own) and Type@{Img.W.w};
#                      the proof puts u below w, which the statement library does not
#   img-img-forged     statement over Type@{Img.V.v} and Type@{Img.W.w}; the proof
#                      puts v below w, which the image does not entail
#   img-img-entailed   the same, where the image's own Glue already entails it
#   honest             the proof needs nothing the statement library lacks
set -u
export PATH=$BIN:$PATH
W=$(mktemp -d)
RP=$W/rocqpath
mkdir -p "$RP/Img"

cat > "$RP/Img/W.v" <<'EOF'
Monomorphic Universe w.
Monomorphic Definition Wit : Type@{w} := nat.
EOF
cat > "$RP/Img/V.v" <<'EOF'
Monomorphic Universe v.
Monomorphic Definition Vit : Type@{v} := nat.
EOF
cat > "$RP/Img/Glue.v" <<'EOF'
Require Img.V.
Require Img.W.
Monomorphic Constraint Img.V.v < Img.W.w.
EOF
(cd "$RP/Img" && ROCQPATH=$RP coqc -Q . Img W.v && ROCQPATH=$RP coqc -Q . Img V.v \
   && ROCQPATH=$RP coqc -Q . Img Glue.v) > "$W/pre.log" 2>&1 \
  || { echo "the image tree does not compile"; tail -5 "$W/pre.log"; exit 1; }
export ROCQPATH=$RP

# <case> <extra Require> <low type in Statement.v> <low type elsewhere> <witness>
one_case() {
  local name=$1 glue=$2 low=$3 lowq=$4 wit=$5
  local d=$W/$name
  mkdir -p "$d"
  {
    echo "Require Img.W."
    [ -n "$glue" ] && echo "$glue"
    echo "Monomorphic Universe u."
    echo "Monomorphic Definition su : Type@{u} := nat."
    echo "Module Type SPEC."
    echo "  Parameter thm : forall R : Prop,"
    echo "    (forall (T : Type@{Img.W.w}) (f : $low -> T),"
    echo "        (forall A B : $low,"
    echo "            (forall Q : T -> Prop, Q (f A) -> Q (f B)) ->"
    echo "            forall P : $low -> Prop, P A -> P B) -> R) -> R."
    echo "End SPEC."
  } > "$d/Statement.v"
  {
    echo "Require Top.Statement."
    echo "Definition thm : forall R : Prop,"
    echo "    (forall (T : Type@{Img.W.w}) (f : $lowq -> T),"
    echo "        (forall A B : $lowq,"
    echo "            (forall Q : T -> Prop, Q (f A) -> Q (f B)) ->"
    echo "            forall P : $lowq -> Prop, P A -> P B) -> R) -> R :="
    echo "  fun R k => k ($wit) (fun X => X) (fun A B H => H)."
  } > "$d/Proof.v"
  {
    echo "Require Top.Statement."
    echo "Require (safe) Top.Proof."
    echo "Module Checked <: Top.Statement.SPEC."
    echo "  Definition thm := Top.Proof.thm."
    echo "End Checked."
    echo "Print Assumptions Checked.thm."
  } > "$d/Checker.v"
  local rc_stmt rc_proof rc_checker rc_chk
  (cd "$d" && coqc -R . Top Statement.v) > "$d/1.log" 2>&1; rc_stmt=$?
  (cd "$d" && coqc -R . Top Proof.v) > "$d/2.log" 2>&1; rc_proof=$?
  (cd "$d" && coqc -R . Top Checker.v) > "$d/3.log" 2>&1; rc_checker=$?
  (cd "$d" && rocqchk -silent -Q . Top Top.Checker) > "$d/4.log" 2>&1; rc_chk=$?
  printf '%-18s statement=%d proof=%d CHECKER=%d coqchk=%d  %s\n' \
    "$name" "$rc_stmt" "$rc_proof" "$rc_checker" "$rc_chk" \
    "$( [ $rc_checker = 0 ] && [ $rc_chk = 0 ] && echo ACCEPTS || echo REFUSES )"
  [ $rc_proof != 0 ] && { echo "    proof: $(grep -m1 -i error "$d/2.log" | cut -c1-100)"; }
  [ $rc_checker != 0 ] && { echo "    checker: $(grep -m1 -i error "$d/3.log" | cut -c1-100)"; }
  [ $rc_chk != 0 ] && { echo "    coqchk: $(grep -m1 -i error "$d/4.log" | cut -c1-100)"; }
  return 0
}

echo "== today's Checker route =="
one_case own-image-forged  ""                  "Type@{u}"       "Type@{Top.Statement.u}" "Type@{Top.Statement.u}"
one_case img-img-forged    "Require Img.V."    "Type@{Img.V.v}" "Type@{Img.V.v}"         "Type@{Img.V.v}"
one_case img-img-entailed  "Require Img.Glue." "Type@{Img.V.v}" "Type@{Img.V.v}"         "Type@{Img.V.v}"

# The negative control: the agent's constant proves something else, so the
# module ascription in the Checker file does not typecheck. Without a row
# that the route REFUSES, the three above show only that the route runs.
d=$W/type-drift
mkdir -p "$d"
{
  echo "Module Type SPEC."
  echo "  Parameter thm : forall (A B : Prop), A -> B."
  echo "End SPEC."
} > "$d/Statement.v"
{
  echo "Definition thm : forall (A : Prop), A -> A := fun _ a => a."
} > "$d/Proof.v"
{
  echo "Require Top.Statement."
  echo "Require (safe) Top.Proof."
  echo "Module Checked <: Top.Statement.SPEC."
  echo "  Definition thm := Top.Proof.thm."
  echo "End Checked."
  echo "Print Assumptions Checked.thm."
} > "$d/Checker.v"
(cd "$d" && coqc -R . Top Statement.v) > "$d/1.log" 2>&1; rc1=$?
(cd "$d" && coqc -R . Top Proof.v) > "$d/2.log" 2>&1; rc2=$?
(cd "$d" && coqc -R . Top Checker.v) > "$d/3.log" 2>&1; rc3=$?
printf '%-18s statement=%d proof=%d CHECKER=%d  %s\n' type-drift "$rc1" "$rc2" "$rc3" \
  "$( [ $rc3 = 0 ] && echo ACCEPTS || echo REFUSES )"
[ $rc3 != 0 ] && echo "    checker: $(grep -m1 -i 'error\|Signature' "$d/3.log" | cut -c1-100)"
echo "(trees under $W)"
