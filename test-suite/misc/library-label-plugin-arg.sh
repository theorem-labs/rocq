#!/usr/bin/env bash
# A library whose Ltac definition stores a generic argument of a plugin
# rocq-library-label does not link (coq-hammer's sauto options, in
# Hammer.Tactics.Tactics, have this shape).
#
# coqc loaded the plugin, so it strips the argument and stores a label. The
# tool cannot recompute that label: the argument's tag is not registered in
# its process. It must say so and give its fallback reading, never stop with
# an uncaught exception (before the fix, [Genstrip.strip] asked [ArgT.repr]
# for the tag's name, which fails an assertion, and the tool exited 2 with no
# reading). Here:
# - coqc compiles the library and stores a label;
# - [--check] prints "other" (the stored digest is a label, not the MD5 of the
#   segment) and exits 0, with the reason on standard error;
# - [--axiom-report-json] and [--stored] also answer.

set -e

export PATH=$BIN:$PATH

. misc/library-label-tool.inc

mkdir -p misc/library-label-plugin-arg
cd misc/library-label-plugin-arg
rm -rf _test
mkdir -p _test/pkg/zzplug _test/lib
D=_test
fail=0

cat > $D/pkg/zzplug/META <<'EOF'
requires = "rocq-runtime.plugins.ltac"
plugin(native) = "p.cmxs"
EOF
cat > $D/pkg/zzplug/g_zz.mlg <<'EOF'
DECLARE PLUGIN "zzplug"

{
open Ltac_plugin
open Stdarg
open Procq.Prim
let pr_zz _ _ _ n = Pp.int n
}

ARGUMENT EXTEND zzopt TYPED AS int PRINTED BY { pr_zz }
| [ "zzopt" integer(n) ] -> { n }
END

TACTIC EXTEND zztac
| [ "zztac" zzopt(x) ] -> { Proofview.tclUNIT () }
END
EOF
( cd $D/pkg/zzplug && rocq pp-mlg g_zz.mlg > build.log 2>&1 &&
    ocamlfind ocamlopt -thread -shared -package rocq-runtime.plugins.ltac \
      -o p.cmxs g_zz.ml >> build.log 2>&1 ) ||
  { echo "FAIL cannot build the test plugin zzplug"; cat $D/pkg/zzplug/build.log; exit 1; }
export OCAMLPATH="$PWD/$D/pkg${OCAMLPATH:+:$OCAMLPATH}"

printf '%s\n' 'Declare ML Module "zzplug".' 'Ltac zzuse := zztac zzopt 3.' \
  'Goal True. zzuse. exact I. Qed.' > $D/lib/A.v
rocq c -q -location-free-label -R $D/lib Zz $D/lib/A.v

set +e
out=$("$TOOL" --check $D/lib/A.vo 2> $D/check.err); rc=$?
set -e
check "--check exits 0 (rc $rc, stderr: $(tr '\n' ' ' < $D/check.err))" test "$rc" = 0
check "--check gives the fallback reading 'other' (got '$out')" has "$out" '^other [0-9a-f]\{32\}$'
check "--check says why there is no label ($(tr '\n' ' ' < $D/check.err))" \
  grep -q 'no label: .*generic argument of a plugin this process did not load' $D/check.err
check "no assertion message on standard error" bash -c "! grep -q 'Unknown dynamic tag' $D/check.err"

set +e
"$TOOL" --axiom-report-json $D/lib/A.vo > $D/report.json 2> $D/report.err; rrc=$?
"$TOOL" --stored $D/lib/A.vo > $D/stored.txt 2> $D/stored.err; src=$?
set -e
check "--axiom-report-json answers (rc $rrc)" test "$rrc" = 0
check "--axiom-report-json reads the label kind 'other'" grep -q '"label_kind":"other"' $D/report.json
check "--axiom-report-json names the library" grep -q '"library":"Zz.A"' $D/report.json
check "--stored answers (rc $src)" test "$src" = 0
check "--stored is the digest --check prints" test "other $(cat $D/stored.txt)" = "$out"
set +e
"$TOOL" --attempts $D/lib/A.vo > /dev/null 2> $D/attempts.err; arc=$?
"$TOOL" --attempts-json $D/lib/A.vo > /dev/null 2> $D/attempts-json.err; ajc=$?
set -e
check "--attempts answers (rc $arc)" test "$arc" = 0
check "--attempts-json answers (rc $ajc)" test "$ajc" = 0

exit $fail
