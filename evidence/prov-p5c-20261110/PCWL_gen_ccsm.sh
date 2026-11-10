#!/bin/bash
# PCWL: type equivalences for CurrentClaimSumModel (fresh = PCVJ_E002 ON emission, frozen 4bb3b3f; gate = compiled gate source sha 3d675744)
cd "$(dirname "$0")"
python3 -B PCWL_gen_equalities.py --module CurrentClaimSumModel --kind types --fresh-dir ../prov-p1j-20261110/PCVJ_E002_emitted/raw/PCVJ_top --fresh-ns PCVJ_top --gate-source inputs/gate_CurrentClaimSumModel_typesview.lean --name-map inputs/ccsm_namemap.json --preamble PCWL_preamble_equivs.lean --out w3.raw.lean --report w3.report.json --state-out w3.state1.json | tail -1
sed -e 's/PRVFresh_CurrentClaimSumModel/PRVFresh_CurrentClaimSumModel_w3/g' -e 's/PRVEq\.CurrentClaimSumModel\./PRVEq.CurrentClaimSumModel_w3./g' w3.raw.lean | awk '!d && /^set_option maxHeartbeats 200000 in/{print "set_option maxHeartbeats 200000"; d=1} {print}' > PRVEq_CurrentClaimSumModel_w3.lean
rm -f w3.raw.lean
