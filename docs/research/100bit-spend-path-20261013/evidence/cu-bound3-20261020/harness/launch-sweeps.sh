#!/bin/bash
set -euo pipefail
H=/home/dombarker/project-offloads/codex-cx-cu-bound3-20261020
caprun() { systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 "$H/harness/sweep.py" "$H/plan-$1.json"; }
# Controls must be green before new measurements.
caprun control
python3 "$H/harness/check-controls.py" "$H"
caprun variants
caprun variants-extra
caprun targeted
caprun random
