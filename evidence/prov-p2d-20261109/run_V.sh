#!/bin/bash
export PCUD_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p2d-20261109
cd /Users/dominic/ZK/.worktrees/pc-prov-p2d/evidence/prov-p2d-20261109
n=11
for k in V1 V2 V3 V4; do
  id=$(printf 'PCUD_L%03d' $n)
  python3 -B PCUD_mkbundle.py $k 2 >/dev/null 2>&1
  python3 -B PCUD_run.py $id lean PRVEq_bundle_${k}2 > run_$id.out 2>&1
  echo "$k $id $?" >> run_V.status
  n=$((n+1))
done
echo done >> run_V.status
