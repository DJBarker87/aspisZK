#!/bin/bash
export PCUD_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p2d-20261109
cd /Users/dominic/ZK/.worktrees/pc-prov-p2d/evidence/prov-p2d-20261109
n=6
for k in J1 J2 J3 J4 J5 J6 J7 J8; do
  id=$(printf 'PCUD_L%03d' $n)
  python3 -B PCUD_mkbundle.py $k 1 >/dev/null 2>&1
  python3 -B PCUD_run.py $id lean PRVEq_bundle_${k}1 > run_$id.out 2>&1
  echo "$k $id $?" >> run_J.status
  n=$((n+1))
done
echo done >> run_J.status
