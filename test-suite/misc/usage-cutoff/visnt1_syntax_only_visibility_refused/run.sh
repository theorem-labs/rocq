#!/usr/bin/env bash
# visnt1, reviewer files (#841 round 19, relayed by Main): Y contributes
# only the notation zz. W1 newly re-exports Y, so in a fresh B the
# notation from Y shadows B's own zz at Require Import A.
. ../round16-lib.sh
uc_round16 refused
