#!/bin/bash
# PCWL: regenerate the equality file for AspisR1AdapterReconstruct.Types (fresh = PCWE_E003 emission, gate = AD_Types); names suffixed _w1 so they cannot clash with the P4e file
cd "$(dirname "$0")"
python3 -B PCWL_gen_equalities.py --module AspisR1AdapterReconstruct.Types --fresh-dir ../prov-p4e-20261109/PCWE_E003_emitted/raw/AspisR1AdapterReconstruct --fresh-ns AspisR1AdapterReconstruct --gate-source ../prov-p4e-20261109/gatesrc/AD_Types.lean --partition ../prov-p0-20261109/PCO_PARTITION.json --out w1.raw.lean --report w1.report.json --state-out w1.state1.json | tail -1
sed -e 's/PRVFresh_AspisR1AdapterReconstruct_Types/PRVFresh_AspisR1AdapterReconstruct_Types_w1/g' -e 's/PRVEq\.AspisR1AdapterReconstruct\.Types\./PRVEq.AspisR1AdapterReconstruct.Types_w1./g' w1.raw.lean | awk '!d && /^set_option maxHeartbeats 200000 in/{print "set_option maxHeartbeats 200000"; d=1} {print}' > PRVEq_AspisR1AdapterReconstruct_Types_w1.lean
rm -f w1.raw.lean
