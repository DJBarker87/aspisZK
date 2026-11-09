#!/bin/bash
# usage: batch.sh MOD...   (one scope per module, sequential)
cd /Users/dominic/ZK/.worktrees/pc-prov-p3c/evidence/prov-p3c-20261109
for m in "$@"; do
  python3 gen_p3.py $m PRVEq_${m//./_}_P3.lean > gen_$m.log 2>&1
  n=$(ls -d PCVC_L[0-9][0-9][0-9]* | sed "s/PCVC_L\([0-9][0-9][0-9]\).*/\1/" | sort -n | tail -1 | sed "s/^0*//"); id=$(printf "PCVC_L%03d" $((n+1)))
  python3 PCVC_run.py $id lean PRVEq_${m//./_}_P3 > run_$m.out 2>&1
  echo "$m $id $(python3 -c "import json;r=json.load(open('$id/receipt.json'));print(r['exit_status'],round(r['wall_seconds'],1),r['peak_rss_kib'])")" >> batch_summary.txt
done
echo batchdone >> batch_summary.txt
