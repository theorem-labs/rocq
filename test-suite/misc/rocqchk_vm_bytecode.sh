#!/usr/bin/env bash
# rocqchk with -bytecode-compiler yes used to take the VM bytecode of a constant
# from the vmlibrary segment of the .vo while typechecking its body from the
# library segment, with nothing tying the two together. A .vo whose vmlibrary
# disagrees with its library then let a VMcast prove False, and rocqchk accepted
# the result with no axioms reported.
#
# rocqchk now compiles the bytecode itself, from the bodies it checks, and never
# reads the vmlibrary segment at all. So:
#  - a .vo with a bogus vmlibrary is still accepted, because its declarations are
#    well typed and the bogus segment is simply ignored; but
#  - a library built against it, whose VMcast only typechecked because the
#    compiler believed the bogus bytecode, is rejected with a plain type error.
#
# No patched tool is needed to build the bogus .vo: two honest compilations that
# differ only in one constant's value produce byte-identical opaques/summary
# segments, so splicing d1's library together with d2's vmlibrary yields an
# internally consistent file whose bytecode no longer matches its body.
set -eu
export PATH="$BIN:$PATH"

d=$(mktemp -d)
mkdir "$d/d1" "$d/d2"

# poc_evil's body is (idb O true) in d1 and (idb O false) in d2; -noinit keeps
# the file self-contained so rocqchk has nothing else to load.
#
# idb is a Fixpoint, not [fun b => b], because the compiler expands a small
# function body at an application site and compiles the constant again from the
# body its library segment carries (kernel/vmsymtable.ml). A poc_evil the
# compiler compiles again would be computed from the honest body, the spliced
# bytecode would never run, and the attack this test is built on would not
# happen at all. No [Fix] is ever expanded (kernel/genlambda.ml), so with this
# idb the compiler runs the bytecode the file carries, as stock does.
cat > "$d/d1/Defs.v" <<'EOF'
Unset Elimination Schemes.
Inductive bool : Set := true | false.
Inductive nat : Set := O | S (n : nat).
Fixpoint idb (n : nat) (b : bool) : bool := match n with O => b | S m => idb m b end.
Definition poc_evil : bool := idb O true.
EOF
sed 's/idb O true/idb O false/' "$d/d1/Defs.v" > "$d/d2/Defs.v"

rocq c -noinit -R "$d/d1" "" "$d/d1/Defs.v"
rocq c -noinit -R "$d/d2" "" "$d/d2/Defs.v"

# Splice: library from d1 (body says true), vmlibrary from d2 (bytecode says
# false), keeping d1's opaques/summary and its segment order.
# misc/vo_container.py rebuilds the container, so every MD5 and every offset is
# right.
python3 - "$(dirname "$0")" "$d" <<'PY'
import sys
sys.path.insert(0, sys.argv[1])
import vo_container

d = sys.argv[2]
v1, s1 = vo_container.read(d + "/d1/Defs.vo")
v2, s2 = vo_container.read(d + "/d2/Defs.vo")
assert v1 == v2, "vo_version mismatch"
assert s1["library"] != s2["library"], "library should differ"
assert s1["vmlibrary"] != s2["vmlibrary"], "vmlibrary should differ"
s1["vmlibrary"] = s2["vmlibrary"]
vo_container.write(d + "/Defs.vo", v1, s1)
PY

# The spliced file is well typed, only its bytecode lies, and rocqchk no longer
# looks at that; accepting it is the point of the design.
if ! rocqchk -bytecode-compiler yes -R "$d" "" Defs 2> "$d/err0"; then
  >&2 echo "FAILURE: rocqchk rejected a well-typed .vo because of its vmlibrary segment"
  cat "$d/err0" >&2
  exit 1
fi

# poc_evil is (idb true), i.e. true, so [discr poc_evil] is [False]. The spliced
# vmlibrary makes the compiler's VM believe it is [false], i.e. [True], so the
# VMcast below goes through and Evil.vo holds a proof of False.
cat > "$d/Evil.v" <<'EOF'
Require Import Defs.
Inductive False : Prop := .
Inductive True : Prop := I.
Definition discr (b : bool) : Prop := match b with true => False | false => True end.
Definition oops : discr poc_evil := (I <: discr poc_evil).
Definition boom : False := oops.
EOF
rocq c -noinit -bytecode-compiler yes -R "$d" "" "$d/Evil.v"

# rocqchk computes with its own bytecode, so the VMcast simply fails to convert
# and Evil is rejected with the same type error the default checker gives.
if rocqchk -bytecode-compiler yes -R "$d" "" Evil 2> "$d/err"; then
  >&2 echo "FAILURE: rocqchk accepted a proof of False built on a bogus vmlibrary"
  cat "$d/err" >&2
  exit 1
fi
grep -q "Type error" "$d/err" || { >&2 echo "FAILURE: rejected, but not as a type error"; cat "$d/err" >&2; exit 1; }
exit 0
