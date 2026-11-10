#!/bin/bash
# PCWL: equality file for CurrentCompactCallerTypesV1 (fresh = PCVJ_E002 ON emission, frozen 4bb3b3f; gate = port17 dependency source = compiled gate module text)
cd "$(dirname "$0")"
python3 -B PCWL_gen_equalities.py --module CurrentCompactCallerTypesV1 --kind types --fresh-dir ../prov-p1j-20261110/PCVJ_E002_emitted/raw/PCVJ_top --fresh-ns PCVJ_top --gate-source inputs/gate_CurrentCompactCallerTypesV1.lean --preamble PCWL_preamble_equivs.lean --out w2.raw.lean --report w2.report.json --state-out w2.state1.json | tail -1
sed -e 's/PRVFresh_CurrentCompactCallerTypesV1/PRVFresh_CurrentCompactCallerTypesV1_w2/g' -e 's/PRVEq\.CurrentCompactCallerTypesV1\./PRVEq.CurrentCompactCallerTypesV1_w2./g' w2.raw.lean | awk '!d && /^set_option maxHeartbeats 200000 in/{print "set_option maxHeartbeats 200000"; d=1} {print}' > PRVEq_CurrentCompactCallerTypesV1_w2.lean
rm -f w2.raw.lean
