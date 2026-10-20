#!/bin/bash
set -euo pipefail
H=/home/dombarker/project-offloads/codex-cx-cu-bound5-20261020
python3 "$H/harness/reservation.py" "$H/reservation-$1.json"
systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 "$H/harness/sweep.py" "$H/plan-$1.json"
