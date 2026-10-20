#!/bin/bash
set -euo pipefail
H=/home/dombarker/project-offloads/codex-cx-cu-bound5-20261020
# Original plan was loaded before four complete-sweep extrema were appended.
# Wait for its worker, then resume the expanded plan; completed labels skip.
while ! grep -q trace-replays-done "$H/campaign-trace.log"; do sleep 5; done
bash "$H/harness/launch_sweep.sh" trace-main > "$H/trace-extra-extrema.log" 2>&1
bash "$H/harness/audit-final.sh" > "$H/audit-final.log" 2>&1
echo candidate-cfg-ready
