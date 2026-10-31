#!/usr/bin/env bash
# The Axioms section of rocqchk -o must name an axiom that lives only inside an
# opaquely sealed implementation, whether the proof reaches it through an
# opaque or a transparent helper, under a full recursive check as well as under
# -norec. The output-coqchk tests cover -norec alone, because that harness
# always passes it.
#
# The second half pins the NAME. An axiom declared in a functor is reported
# after the applied module (App.in_f), which is also what Print Assumptions
# prints for it; the functor's own name (F.in_f) must not appear. A reader that
# joins the two accounts by name, as the BET grader does, fails closed on any
# name that only one of them prints, so where the summary cannot tell an
# assumption from a definition it reports nothing: an application inside a seal
# is named by Print Assumptions alone, and that is checked here too.
set -eu
export PATH="$BIN:$PATH"

d=$(mktemp -d)
trap 'rm -rf "$d"' EXIT

cat > "$d/Sealed.v" <<'EOF'
Module Type T. Parameter tgt : 1 = 2. End T.
Module OpaqueHelper : T.
  Axiom ax : False.
  Lemma helper : False. Proof. exact ax. Qed.
  Lemma tgt : 1 = 2. Proof. destruct helper. Qed.
End OpaqueHelper.
Module TransparentHelper : T.
  Axiom ax : False.
  Definition helper : False := ax.
  Lemma tgt : 1 = 2. Proof. destruct helper. Qed.
End TransparentHelper.
EOF
echo 'Require Sealed. Definition use : 1 = 2 := Sealed.OpaqueHelper.tgt.' > "$d/Use.v"
rocq c -native-compiler no -R "$d" "" "$d/Sealed.v"
rocq c -native-compiler no -R "$d" "" "$d/Use.v"

# Print one summary section: its "* <title>" line and the lines under it, up to
# the next "* " bullet. awk's index() takes the title literally.
section() { awk -v h="* $1" 'index($0, h) == 1 { p = 1; print; next } p && /^\* / { exit } p { print }' "$2"; }

# Recursive check: Sealed is checked as a dependency of Use.
rocqchk -o -silent -R "$d" "" Use > "$d/rec.log" 2>&1
section 'Axioms' "$d/rec.log" | grep -qx '    Sealed.OpaqueHelper.ax'
section 'Axioms' "$d/rec.log" | grep -qx '    Sealed.TransparentHelper.ax'

# -norec on the sealing library itself.
rocqchk -o -silent -R "$d" "" -norec Sealed > "$d/norec.log" 2>&1
section 'Axioms' "$d/norec.log" | grep -qx '    Sealed.OpaqueHelper.ax'
section 'Axioms' "$d/norec.log" | grep -qx '    Sealed.TransparentHelper.ax'

cat > "$d/Fun.v" <<'EOF'
Module Type S. Parameter n : nat. End S.
Module Arg. Definition n := 0. End Arg.
Module F (X : S).
  Axiom in_f : False.
  Definition use : False := in_f.
End F.
Module App := F Arg.
Definition reached : False := App.use.
Module Type T. Parameter tgt : 1 = 2. End T.
Module Seal : T.
  Module Inner := F Arg.
  Lemma tgt : 1 = 2. Proof. destruct Inner.use. Qed.
End Seal.
EOF
echo 'Require Fun. Print Assumptions Fun.reached. Print Assumptions Fun.Seal.tgt.' > "$d/Pa.v"
rocq c -native-compiler no -R "$d" "" "$d/Fun.v"
rocq c -native-compiler no -R "$d" "" "$d/Pa.v" > "$d/pa.log" 2>&1
grep -q 'Fun.App.in_f : False' "$d/pa.log"
grep -q 'Fun.Seal.Inner.in_f : False' "$d/pa.log"
if grep -q 'Fun.F.in_f' "$d/pa.log"; then
  echo "Print Assumptions named the functor, not the application"; exit 1
fi

rocqchk -o -silent -R "$d" "" Fun > "$d/fun.log" 2>&1
section 'Axioms' "$d/fun.log" | grep -qx '    Fun.App.in_f'
if section 'Axioms' "$d/fun.log" | grep -q 'Fun.F.in_f'; then
  echo "the summary named the functor, which Print Assumptions never prints"; exit 1
fi
# The application inside the seal: unreported, never reported under another
# name. Print Assumptions named it above, so a join of the two accounts fails
# closed here rather than calling an assumption nobody made.
if section 'Axioms' "$d/fun.log" | grep -q 'Fun.Seal'; then
  echo "the summary named something under Seal, which it cannot tell is assumed"; exit 1
fi
