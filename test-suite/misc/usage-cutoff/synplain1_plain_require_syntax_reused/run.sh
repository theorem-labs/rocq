#!/usr/bin/env bash
# synplain1 (#841 issuecomment-6205909210; reviewer expects REUSED). Accepted
# P3: W's #[export] hint is inert under A's plain Require, but a #[global]
# hint there is active (glh1), so syntax cannot be scoped to visible
# libraries without per-object locality, which Libobject does not expose.
. ../round16-lib.sh
uc_round16 overrefused
