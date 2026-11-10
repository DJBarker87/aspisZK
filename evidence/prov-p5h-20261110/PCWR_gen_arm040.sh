#!/bin/bash
# PCWR_ item 1: PCWL_gen_arm.sh re-run with the gate source re-pointed to lean-040 (sha c6aa4d35, the plan's source).
cd "$(dirname "$0")"
python3 -B PCWR_gen_equalities.py --module AdapterRwModel --fresh-dir PCWL_E001_emitted/raw/PCWL_ar --fresh-ns PCWL_ar --gate-source inputs/gate_AdapterRwModel_lean040.lean --gate-types-source inputs/gate_AdapterRwTypes.lean --only inputs/only_arm.json --prune-fresh --out PCWR_work/t1.raw.lean --report PCWR_work/t1.report.json --state-out PCWR_work/t1.state.json | tail -3
