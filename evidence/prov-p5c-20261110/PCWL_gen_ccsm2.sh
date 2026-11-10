#!/bin/bash
# PCWL: CurrentClaimSumModel WideExact.ZERO (fresh = PCVR_E006 aspis-core emission, ON, original Aeneas, frozen 4bb3b3f; gate = compiled gate source sha 3d675744, funs view)
cd "$(dirname "$0")"
python3 -B PCWL_gen_equalities.py --module CurrentClaimSumModel --fresh-dir ../prov-p1k-20261110/PCVR_E006_emitted/raw/PCVR_core2 --fresh-ns PCVR_core2 --gate-source inputs/gate_CurrentClaimSumModel_funsview.lean --gate-types-source inputs/gate_CurrentClaimSumModel_typesview.lean --name-map inputs/ccsm_namemap2.json --only inputs/only_ccsm.json --prune-fresh --out w6.raw.lean --report w6.report.json --state-out w6.state.json | tail -1
sed -e 's/PRVFresh_CurrentClaimSumModel/PRVFresh_CurrentClaimSumModel_w6/g' -e 's/PRVEq\.CurrentClaimSumModel\./PRVEq.CurrentClaimSumModel_w6./g' w6.raw.lean | awk '!d && /^set_option maxHeartbeats 200000 in/{print "set_option maxHeartbeats 200000"; d=1} {print}' > PRVEq_CurrentClaimSumModel_w6.lean
rm -f w6.raw.lean
