#!/bin/bash
# usage: bash PCWL_gen_arm.sh [STATE LEANLOG]  -- AdapterRwModel equalities, fresh = PCWL_E001 (original Aeneas, ON, frozen 4bb3b3f), gate = compiled gate source
cd "$(dirname "$0")"
EX=""; [ -n "$1" ] && EX="--state $1 --lean-log $2"
python3 -B PCWL_gen_equalities.py --module AdapterRwModel --fresh-dir PCWL_E001_emitted/raw/PCWL_ar --fresh-ns PCWL_ar --gate-source inputs/gate_AdapterRwModel.lean --gate-types-source inputs/gate_AdapterRwTypes.lean --only inputs/only_arm.json --prune-fresh $EX --out w4.raw.lean --report w4.report.json --state-out w4.state.json | tail -1
sed -e 's/PRVFresh_AdapterRwModel/PRVFresh_AdapterRwModel_w4/g' -e 's/PRVEq\.AdapterRwModel\./PRVEq.AdapterRwModel_w4./g' w4.raw.lean | awk '!d && /^set_option maxHeartbeats 200000 in/{print "set_option maxHeartbeats 200000"; d=1} {print}' > PRVEq_AdapterRwModel_w4.lean
rm -f w4.raw.lean
