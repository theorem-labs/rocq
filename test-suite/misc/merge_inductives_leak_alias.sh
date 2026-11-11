#!/usr/bin/env bash

# merge_inductives_leak through a module alias (review finding P1-1, route 2).
# Mid is compiled WITH the option and aliases the agent's library; a reader
# without the option must still see two types, and rocqchk must accept Mid
# either way.
set -eu

. misc/merge_inductives_common.bash

mi_setup misc/merge_inductives_leak_alias

mi_coqc Spec -merge-inductives
mi_coqc Agent -merge-inductives
# Mid aliases the agent's library, whose inductive this run merged, so the
# resolver Mid would write out records the merged canonical name. Which
# copy the alias names cannot be recovered from that resolver, so writing
# the library is refused rather than guessed at -- cleanly, and with the
# name in the message.
mi_coqc_fails Mid -merge-inductives
mi_says 'cannot write this library' "the refusal to write a merged alias"
mi_says 'Spec.tree' "the name it merged into"

# Without the option there is nothing to undo and the same file compiles,
# and a reader of it still sees two types.
mi_coqc Mid
mi_rocqchk "$mi_root.Mid"
mi_coqc_fails Evil
mi_says tree "tree"
