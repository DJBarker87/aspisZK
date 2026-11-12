#!/bin/bash
# Gate D for items 6 and 8 (crate aspis_r1_cost_probe). The body of prove_masked_with_attempt (the whole
# prover below one attempt) and the checker shell p_r1_check are kept opaque so that the LLBC stays narrow;
# p_r1_check is an opaque item in package g2 as well.
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111
export PV_SRC_DIR=${1:-src-rw}
bash $W/tools/translate.sh ${2:-i68-check_times_client} --opaque crate::prover::prove_masked_with_attempt --opaque aspis_z4b_probe::probe::z9::z9b::z9c::z9d::z9e::p_r1_check
echo done > $W/D68_${2:-i68-check_times_client}.DONE
