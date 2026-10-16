#!/usr/bin/env bash
# mtreorder1 (#841 round 21 review): accepted P3. Reordering independent
# fields of T changes T's signature-shape digest, which hashes the ordered
# field list. B never mentions T and a fresh B succeeds; refusing is sound.
. ../lt-lib.sh
uc_direct_vernac overrefused
