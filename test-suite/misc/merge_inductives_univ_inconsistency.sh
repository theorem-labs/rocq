#!/usr/bin/env bash

# A merge equates the universes of the two blocks, so a constraint that puts
# one of them strictly below the other has to be refused. What this test is
# really about is how it is refused: with the error a user can act on, and
# never with an anomaly. mi_coqc_fails fails the test on an anomaly, whatever
# the exit code.
set -eu

. misc/merge_inductives_common.bash

mi_setup misc/merge_inductives_univ_inconsistency

mi_coqc SpecN -merge-inductives
mi_coqc AgentN -merge-inductives

mi_coqc_fails Contra -merge-inductives
mi_says 'Universe inconsistency' 'a universe inconsistency'
