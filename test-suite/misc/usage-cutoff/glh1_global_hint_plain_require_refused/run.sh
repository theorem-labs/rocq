#!/usr/bin/env bash
# glh1: a #[global] hint below a plain Require is active in B, so the
# syntax snapshot must cover libraries B cannot see through Import/Export.
# It is why synplain1 cannot be fixed by snapshotting only visible libraries.
. ../round16-lib.sh
uc_round16 refused
