#!/bin/bash
set -euo pipefail
H=/home/dombarker/project-offloads/codex-cx-cu-bound5-20261020
while ! grep -q candidate-cfg-ready "$H/campaign-analysis.log"; do sleep 5; done
python3 "$H/harness/reservation.py" "$H/reservation-residuals.json"
systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 "$H/harness/capped.py" "$H/receipts/analysis-final" "time expected in per-site residual derivation, phase attribution and bound arithmetic; no compilation or proof generation" -- bash "$H/harness/analyze-final.sh"
