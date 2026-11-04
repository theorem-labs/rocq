#!/usr/bin/env bash
# lia's fast path tells an axiom from an opaque proof, and its library label
# does not (vernac/libkeyObjects.ml), so the read is recorded in the keep
# rule's opacity log.
#
# Zcheck_oracle.fingerprint (plugins/micromega/zcheck_oracle.ml) serializes
# every constant ZTautoChecker reaches, writing "opaque" or "undef" for its
# body, and lia takes its fast path only with no opaque constant. A's `c` is
# Admitted in `adm` and a Qed proof in `qed`, and A has one label in both. B
# runs the fingerprint on a constant whose body names A.c (through a test
# plugin, since the fast path itself needs Stdlib's own Lia.zchecker), and
# must record A.c with the opacity it saw: opaque=false against `adm`,
# opaque=true against `qed`.

set -e

export PATH=$BIN:$PATH

. misc/library-label-tool.inc

mkdir -p misc/library-label-zcheck
cd misc/library-label-zcheck
rm -rf _test
umask 022
mkdir -p _test/pkg/zcpeek _test/adm _test/qed _test/b
D=_test
export TMPDIR=$(mktemp -d /tmp/zcheck-XXXXXXXXXX)
fail=0

report() { "$TOOL" --axiom-report-json "$1"; }
field() { report "$1" | sed -n "s/.*\"$2\":\(\[[^]]*\]\|{[^}]*}\|null\).*/\1/p"; }
label() { "$TOOL" --check "$1" | awk '{print $2}'; }
comp() { rocq c -q -location-free-label "$@"; }

cat > $D/pkg/zcpeek/META <<'EOF'
requires = "rocq-runtime.plugins.ltac2 rocq-runtime.plugins.micromega"
plugin(native) = "p.cmxs"
EOF
cat > $D/pkg/zcpeek/p.ml <<'EOF'
open Ltac2_plugin

(* The number of opaque constants Zcheck_oracle.fingerprint counts from [c]. *)
let () =
  Tac2externals.define
    { Tac2expr.mltac_plugin = "zcpeek"; mltac_tactic = "fingerprint" }
    Tac2externals.(Tac2ffi.constr @-> eret Tac2ffi.int)
    (fun c _env sigma ->
       match EConstr.kind sigma c with
       | Constr.Const (cst, _) ->
         let _, opaque, _ = Micromega_plugin.Zcheck_oracle.fingerprint (Global.env ()) cst in
         opaque
       | _ -> -1)
EOF
( cd $D/pkg/zcpeek && ocamlfind ocamlopt -thread -shared \
    -package rocq-runtime.plugins.ltac2,rocq-runtime.plugins.micromega -o p.cmxs p.ml > build.log 2>&1 ) ||
  { echo "FAIL cannot build the test plugin zcpeek"; cat $D/pkg/zcpeek/build.log; exit 1; }
export OCAMLPATH="$PWD/$D/pkg${OCAMLPATH:+:$OCAMLPATH}"

printf 'Lemma c : True.\nAdmitted.\n' > $D/adm/A.v
printf 'Lemma c : True.\nProof. exact I. Qed.\n' > $D/qed/A.v
comp -R $D/adm A $D/adm/A.v
comp -R $D/qed A $D/qed/A.v
check "A has one label as Admitted and as Qed ($(label $D/adm/A.vo))" \
  test "$(label $D/adm/A.vo)" = "$(label $D/qed/A.vo)"

printf '%s\n' 'Require Import Ltac2.Ltac2.' 'Declare ML Module "zcpeek".' 'Require A.' \
  'Definition uses_c := A.c.' \
  'Ltac2 @ external fingerprint : constr -> int := "zcpeek" "fingerprint".' \
  'Goal True.' '  let _ := fingerprint constr:(uses_c) in ().' '  exact I.' 'Qed.' > $D/b/B.v

for v in adm qed; do
  mkdir -p $D/b-$v; cp $D/b/B.v $D/b-$v/B.v
  comp -R $D/$v A -R $D/b-$v Bdep $D/b-$v/B.v > $D/b-$v/out 2>&1 ||
    { echo "FAIL B did not compile against A $v:"; cat $D/b-$v/out; fail=1; }
done

q_adm='[{"constant":"A.A.c","library":"A.A","opaque":false,"table":null}]'
q_qed='[{"constant":"A.A.c","library":"A.A","opaque":true,"table":null}]'
qa=$(field $D/b-adm/B.vo opacity_queries)
qq=$(field $D/b-qed/B.vo opacity_queries)
check "the fingerprint's read of the Admitted A.c is recorded (got $qa)" test "$qa" = "$q_adm"
check "the fingerprint's read of the proved A.c is recorded (got $qq)" test "$qq" = "$q_qed"

left=$(find "$TMPDIR" -mindepth 1 2>/dev/null | head -3 | tr '\n' ' ')
check "no opacity log is left in TMPDIR ($left)" test -z "$left"
rm -rf "$TMPDIR"

exit $fail
