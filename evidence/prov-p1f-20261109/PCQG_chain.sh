#!/bin/bash
# usage: bash PCQG_chain.sh RUN:SPEC[:NOTE] ...   strictly sequential, one scope at a time; commits after every 5 runs
export PCQG_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p1f-20261109
cd "$(dirname "$0")"
for x in "$@"; do
  IFS=: read run spec note <<< "$x"
  python3 -B PCQG_render_spec.py "$spec" "$run" "$note" >/dev/null || { echo "$run SPECFAIL" >> PCQG_chain.log; continue; }
  timeout 1500 python3 -B PCQG_run.py "$run" extract > "$run.client.log" 2>&1
  echo "$run $spec rc=$?" >> PCQG_chain.log
done
