#!/usr/bin/env bash

# A private block never merges, and merging one gives False.
#
# `Private Inductive pos := mk : nat -> pos.` means only the file that
# declared it may match on it, so a file may axiomatise a distinction away
# -- Spec's `pos_irr : forall n m, mk n = mk m` -- and stay consistent.
# Agent declares the same private type and matches on it, which is equally
# legal there. The two are two different quotients, not one type: identify
# them and Agent's match sees through Spec's axiom, which is Mid.bad :
# False (the delta review, P1, whose repro these files are).
#
# Direct.v is the control that the private discipline is what makes each
# file consistent on its own: a match on Spec.pos from outside Spec is
# refused, with the option and without it.
set -eu

. misc/merge_inductives_common.bash

mi_setup misc/merge_inductives_neg_private

mi_coqc Spec -merge-inductives
mi_coqc Agent -merge-inductives
mi_coqc Direct -merge-inductives

# The exact refusal, not just a mention of the type: the agent's function
# is applied to the spec's constructor, and the two pos types stay apart.
mi_coqc_fails Mid -merge-inductives
mi_says 'The term "Spec.mk 0" has type "Spec.pos" while it is expected to have type' \
  "the two pos types staying apart"
mi_says 'Agent.pos' "the agent's pos"

# And without the option, which is what it did before the merge existed.
mi_coqc_fails Mid
mi_says 'The term "Spec.mk 0" has type "Spec.pos" while it is expected to have type' \
  "the two pos types staying apart"
mi_says 'Agent.pos' "the agent's pos"

# Both libraries stay valid on their own: refusing the merge costs nothing.
mi_rocqchk -merge-inductives "$mi_root.Spec" "$mi_root.Agent"
