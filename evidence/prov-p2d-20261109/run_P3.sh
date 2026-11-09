#!/bin/bash
export PCUD_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p2d-20261109
cd /Users/dominic/ZK/.worktrees/pc-prov-p2d/evidence/prov-p2d-20261109
python3 -B PCUD_mkbundle.py P3 1 >/dev/null 2>&1
python3 -B PCUD_run.py PCUD_L018 lean PRVEq_bundle_P31 > run_PCUD_L018.out 2>&1
echo "P3probe $?" >> run_P3.status
[ -f PCUD_L018/receipt.json ] || bash recover.sh PCUD_L018 >/dev/null 2>&1
xz -dc PCUD_L018/stdout.log.xz > gen/probe_P3.log
python3 -B PCUD_ingest.py 2 P3 gen/probe_P3.log > ingest_P3.out 2>&1
python3 -B PCUD_mkbundle.py P3 2 >/dev/null 2>&1
python3 -B PCUD_run.py PCUD_L019 lean PRVEq_bundle_P32 > run_PCUD_L019.out 2>&1
echo "P3verify $?" >> run_P3.status
[ -f PCUD_L019/receipt.json ] || bash recover.sh PCUD_L019 >/dev/null 2>&1
echo done >> run_P3.status
