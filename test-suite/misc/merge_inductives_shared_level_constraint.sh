#!/usr/bin/env bash

# The two declarations are textually identical. Each library declares its own
# global universe [u] and an [Inductive b (A : Type@{u})] over it, and the one
# difference is a constraint the agent's library adds against Set, a level
# both libraries share: [Constraint Set < u].
#
# Merging would make the two universes one, and with them the two constraint
# sets, which would put [Set < SpecS.u] into a library that never asked for
# it. So the blocks must not merge, and the Checker, which needs the two
# copies of [b] to be one type, is refused by coqc. It never reaches a .vo;
# what rocqchk is asked is that refusing the merge leaves both libraries
# valid.
set -eu

. misc/merge_inductives_common.bash

mi_negative misc/merge_inductives_shared_level_constraint SpecS AgentS
