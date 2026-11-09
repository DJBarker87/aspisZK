#!/bin/sh
# NPC_: NKX_launch.sh with the host directory changed to the NPC_ workspace. Same admission, disk gate and cgroup caps.
set -eu
mode=$1
ssh dombarker@100.108.41.90 "cd /home/dombarker/project-offloads/codex-cx-devnet2-20261109 && python3 /home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py $mode-reservation.json > $mode-reservation.log 2>&1 && python3 -c 'import json,shutil; assert json.load(open(\"$mode-reservation.json\"))[\"allowed\"] is True; assert shutil.disk_usage(\".\").free >= 40000000000' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 /home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/barrier.py $mode-barrier.json python3 NPC_run.py $mode > $mode-scope.log 2>&1"
