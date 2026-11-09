#!/bin/bash
export PCQ_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p1a-20261109
cd /Users/dominic/ZK/.worktrees/pc-prov-p1a/evidence/prov-p1a-20261109
while [ $# -gt 1 ]; do
  python3 PCQ_render_spec.py $1 $2 >/dev/null || exit 3
  timeout 900 python3 PCQ_run.py $2 extract > $2.client.log 2>&1
  echo "$2 $1 rc=$?" >> chain.log
  shift 2
done
